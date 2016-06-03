package org.archware.sosadl.validation.typing;

import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentLinkedDeque;
import java.util.function.BinaryOperator;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.archware.sosadl.sosADL.BooleanType;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.FieldDecl;
import org.archware.sosadl.sosADL.RangeType;
import org.archware.sosadl.sosADL.SequenceType;
import org.archware.sosadl.sosADL.SosADLFactory;
import org.archware.sosadl.sosADL.TupleType;
import org.archware.sosadl.tv.typeCheckerHelper.TypeCheckerHelperFactory;
import org.archware.sosadl.tv.typeCheckerHelper.TypeVariable;
import org.archware.sosadl.validation.ErrorCollector;
import org.archware.sosadl.validation.typing.interp.InterpInZ;
import org.archware.utils.MapUtils;
import org.archware.utils.Pair;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.util.EcoreUtil;

/**
 * Implementation of type inference.
 * 
 * <p>
 * The type inference mechanism assumes the following protocol:
 * <ol>
 * <li>The subtyping constraints are first all collected during the traversal of
 * the abstract syntax tree. Such constraints are added by calling either
 * {@link #addConstraint(DataType, DataType, EObject) or
 * {@link #addConstraint(DataType, DataType, EObject, EStructuralFeature)}.</li>
 * <li>When all the constraints are issued, the {@link #solve()} method must be
 * called to invoke the solver. The algorithm repeatedly performs the following
 * tasks. At the end of each step, the solver loops back to the beginning of its
 * algorithm.
 * <ol>
 * <li>The solver first checks the constraints that do not involve type
 * variables. When any of the checked type is built using a recursive type
 * constructor, i.e., {@link SequenceType} or {@link TupleType}, new type
 * variables and constraints are issued to trigger the recursive checking. The
 * solver tries to check as many constraints as possible, and to report as many
 * error messages as possible before bailing out.</li>
 * <li>When all the constraints involve at least one type variable, the solver
 * tries to compute a lower bound and an upper bound for each type variable. To
 * do so, when several constraints provide a lower bound to a given type
 * variable, the solver replaces all these constraints with a single one with
 * the union of the lower bounds. It performs the same, replacing the set of
 * upper bounds with their intersection. After the replacement, the solver goes
 * back to the first step.</li>
 * <li>When all the constraints involve at least one type variable, and each
 * type variable is constrained by at most one lower bound and one upper bound,
 * the solver tries to infer one of the type variable. To select the type
 * variable to be substituted, the solver considers only the type variables that
 * do not depend on any non-substituted type variable. Then it prefers first a
 * type variable that has both lower and upper bounds. If no such type variable
 * exists, it selects one that has at least one bound. If no such type variable
 * exists either, it chooses a type variable with no bound.</li>
 * </ol>
 * </li>
 * <li>After the solver returns, the {@link #isSolved()} method returns
 * {@value true} if the inference problem is successfully solved. The
 * {@link #deepSubstitute(DataType)} method can then be used in order to
 * retrieve the fully substituted type for any type variable.</li>
 * </ol>
 * 
 * @author Jeremy Buisson
 */
public final class TypeInferenceSolver {
	private static final class Constraint {
		public final DataType sub;
		public final DataType sup;
		public final EObject originObject;
		public final EStructuralFeature originFeature;

		public Constraint(DataType sub, DataType sup, EObject originObject, EStructuralFeature originFeature) {
			super();
			this.sub = sub;
			this.sup = sup;
			this.originObject = originObject;
			this.originFeature = originFeature;
		}
	}

	private final ErrorCollector log;
	private final Map<String, TypeVariable> variables;
	private Map<String, Deque<Constraint>> upperBounds;
	private Map<String, Deque<Constraint>> lowerBounds;
	private Deque<Constraint> varVarConstraints;
	private Deque<Constraint> determinedConstraints;
	private final NameGenerator nameGenerator;

	/**
	 * Build a new instance of the type inference problem
	 * 
	 * @param log
	 *            collector used to report errors
	 */
	public TypeInferenceSolver(ErrorCollector log) {
		this.log = log;
		this.variables = new ConcurrentHashMap<>();
		this.upperBounds = new ConcurrentHashMap<>();
		this.lowerBounds = new ConcurrentHashMap<>();
		this.varVarConstraints = new ConcurrentLinkedDeque<>();
		this.determinedConstraints = new ConcurrentLinkedDeque<>();
		this.nameGenerator = new SequentialNameGenerator();
	}

	public Stream<TypeVariable> getVariables() {
		return variables.values().stream();
	}

	/**
	 * Record a new constraint
	 * 
	 * The new constraint states that {@value sub} is a subtype of {@value sup}.
	 * This method is equivalent to calling
	 * {@link #addConstraint(DataType, DataType, EObject, EStructuralFeature)}
	 * with a null feature.
	 * 
	 * @param sub
	 *            smallest type in the inequation
	 * @param sup
	 *            biggest type in the inequation
	 * @param origin
	 *            node in the abstract syntax tree to which the constraint is
	 *            attached, for error reports
	 */
	public void addConstraint(DataType sub, DataType sup, EObject origin) {
		addConstraint(sub, sup, origin, null);
	}

	public void addConstraint(DataType sub, DataType sup, EObject originObject, EStructuralFeature originFeature) {
		Constraint c = new Constraint(reprOrType(sub), reprOrType(sup), originObject, originFeature);
		addConstraint(c);
	}

	private void addConstraint(String n, DataType t) {
		TypeVariable v = variables.get(n);
		addConstraint(v, t, v.getConcernedObject(), v.eContainingFeature());
	}

	@SuppressWarnings("unused")
	private void addConstraint(DataType t, String n) {
		TypeVariable v = variables.get(n);
		addConstraint(t, v, v.getConcernedObject(), v.eContainingFeature());
	}

	private void addConstraint(Constraint c) {
		if (c.sub != c.sup) {
			if (isDetermined(c.sub)) {
				if (isDetermined(c.sup)) {
					determinedConstraints.add(c);
				} else {
					TypeVariable sup = (TypeVariable) c.sup;
					if (contains(c.sub, sup)) {
						log.error(nameOf(sup) + ": constraint " + typeToString(c.sub) + "<=" + typeToString(sup)
								+ " contains a cycle", c.originObject, c.originFeature);
					} else {
						multimapAdd(lowerBounds, nameOf(sup), c);
					}
				}
			} else {
				if (isDetermined(c.sup)) {
					TypeVariable sub = (TypeVariable) c.sub;
					if (contains(c.sup, sub)) {
						log.error(nameOf(sub) + ": constraint " + typeToString(sub) + "<=" + typeToString(c.sup)
								+ " contains a cycle", c.originObject, c.originFeature);
					} else {
						multimapAdd(upperBounds, nameOf(sub), c);
					}
				} else {
					varVarConstraints.add(c);
				}
			}
		}
	}

	private boolean isDetermined(DataType t) {
		return substitute(t) != null;
	}

	private DataType reprOrType(DataType t) {
		if (t instanceof TypeVariable) {
			return repr((TypeVariable) t);
		} else {
			return t;
		}
	}

	private TypeVariable repr(TypeVariable v) {
		TypeVariable n = variables.get(v.getName());
		if (n == v) {
			DataType r = v.getSubstitute();
			if (r != null && r instanceof TypeVariable) {
				TypeVariable x = repr((TypeVariable) r);
				v.setSubstitute(x);
				return x;
			} else {
				return v;
			}
		} else {
			TypeVariable r = repr(n);
			v.setSubstitute(r);
			return r;
		}
	}

	private String nameOf(DataType v) {
		return repr((TypeVariable) v).getName();
	}

	private DataType substitute(DataType t) {
		if (t != null && t instanceof TypeVariable) {
			TypeVariable r = repr((TypeVariable) t);
			return r.getSubstitute();
		} else {
			return t;
		}
	}

	public DataType deepSubstitute(DataType t) {
		if (t == null) {
			return t;
		} else if (t instanceof TypeVariable) {
			return deepSubstitute(substitute(t));
		} else if (t instanceof RangeType) {
			return t;
		} else if (t instanceof SequenceType) {
			SequenceType s = (SequenceType) t;
			DataType i = deepSubstitute(s.getType());
			return createSequenceType(i);
		} else if (t instanceof BooleanType) {
			return t;
		} else if (t instanceof TupleType) {
			TupleType tt = (TupleType) t;
			return createTupleType(
					tt.getFields().stream().map((f) -> createFieldDecl(f.getName(), deepSubstitute(f.getType())))
							.collect(Collectors.toList()));
		} else {
			return t;
		}
	}

	public static boolean containsVariable(DataType t) {
		if (t instanceof TypeVariable) {
			return true;
		} else if (t instanceof SequenceType) {
			return containsVariable(((SequenceType) t).getType());
		} else if (t instanceof TupleType) {
			return ((TupleType) t).getFields().stream().anyMatch((f) -> containsVariable(f.getType()));
		} else {
			return false;
		}
	}

	private static <K, V> void multimapAdd(Map<K, Deque<V>> mm, K k, V v) {
		mm.computeIfAbsent(k, (a) -> new ConcurrentLinkedDeque<>()).add(v);
	}

	public TypeVariable createFreshTypeVariable(BinaryOperator<Optional<DataType>> solver) {
		TypeVariable r = TypeCheckerHelperFactory.eINSTANCE.createTypeVariable();
		r.setName(nameGenerator.get());
		r.setSolver(solver);
		variables.put(r.getName(), r);
		return r;
	}

	public TypeVariable createFreshTypeVariable(BinaryOperator<Optional<DataType>> solver, EObject concernedObject,
			EStructuralFeature concernedFeature) {
		TypeVariable v = createFreshTypeVariable(solver);
		v.setConcernedObject(concernedObject);
		v.setConcernedStructuralFeature(concernedFeature);
		return v;
	}

	public TypeVariable createFreshDependency(BinaryOperator<Optional<DataType>> solver, TypeVariable dependent) {
		TypeVariable v = createFreshTypeVariable(solver, dependent.getConcernedObject(),
				dependent.getConcernedStructuralFeature());
		dependent.getDependencies().add(v);
		return v;
	}

	public boolean isSolved() {
		return variables.values().stream().allMatch(this::isDetermined);
	}

	private static class VariableSpec {
		public final String name;
		public final Optional<Constraint> lowerBound;
		public final TypeVariable variable;
		public final Optional<Constraint> upperBound;

		public VariableSpec(String name, Optional<Constraint> lowerBound, TypeVariable variable,
				Optional<Constraint> upperBound) {
			super();
			this.name = name;
			this.lowerBound = lowerBound;
			this.variable = variable;
			this.upperBound = upperBound;
		}
	}

	private static <T> Optional<T> getTheOneOf(Collection<T> c) {
		if (c.size() > 1) {
			throw new IllegalArgumentException("the collection is assumed to contain at most one value");
		} else {
			return c.stream().findAny();
		}
	}

	public void solve() {
		for (;;) {
			if (!determinedConstraints.isEmpty()) {
				// 1) check the constraints that are fully determined, if any
				Deque<Constraint> dc = determinedConstraints;
				determinedConstraints = new ConcurrentLinkedDeque<>();
				// use reduce instead of allMatch in order to ensure that all
				// the constraints are tested, and therefore report as many
				// errors as possible in a single step
				if (dc.stream().reduce(true, (b, x) -> checkDeterminedConstraint(x) && b, (a, b) -> a && b)) {
					continue;
				} else {
					return;
				}
			} else {
				Optional<Map.Entry<String, Deque<Constraint>>> cub = upperBounds.entrySet().stream()
						.filter((e) -> e.getValue().size() >= 2).findAny();
				if (cub.isPresent()) {
					// 2) merge the constraints when a single variable has
					// several (at least two) upper bounds
					Map.Entry<String, Deque<Constraint>> e = cub.get();
					Deque<Constraint> constraints = upperBounds.remove(e.getKey());
					Optional<DataType> inter = intersect(e.getKey(), constraints);
					inter.ifPresent((i) -> addConstraint(e.getKey(), i));
					if (!inter.isPresent()) {
						return;
					} else {
						continue;
					}
				} else {
					Optional<Map.Entry<String, Deque<Constraint>>> clb = lowerBounds.entrySet().stream()
							.filter((e) -> e.getValue().size() >= 2).findAny();
					if (clb.isPresent()) {
						// 3) merge the constraints when a single variable has
						// several (at least two) lower bounds
						Map.Entry<String, Deque<Constraint>> e = clb.get();
						Deque<Constraint> constraints = lowerBounds.remove(e.getKey());
						Optional<DataType> union = union(e.getKey(), constraints);
						union.ifPresent((i) -> addConstraint(e.getKey(), i));
						if (!union.isPresent()) {
							return;
						} else {
							continue;
						}
					} else {
						// each type variable has at most one lower bound and
						// one upper bound; find the variables whose
						// dependencies are determined
						Deque<VariableSpec> v = variables.entrySet().stream()
								.filter((e) -> e.getValue().getSubstitute() == null
										&& e.getValue().getDependencies().stream().allMatch(this::isDetermined))
								.map((e) -> new VariableSpec(e.getKey(),
										getTheOneOf(
												lowerBounds.getOrDefault(e.getKey(), new ConcurrentLinkedDeque<>())),
										e.getValue(),
										getTheOneOf(
												upperBounds.getOrDefault(e.getKey(), new ConcurrentLinkedDeque<>()))))
								.collect(Collectors.toCollection(ConcurrentLinkedDeque::new));
						Optional<VariableSpec> toSolve = v.stream()
								.filter((x) -> x.lowerBound.isPresent() && x.upperBound.isPresent()).findAny();
						if (!toSolve.isPresent()) {
							toSolve = v.stream().filter((x) -> x.lowerBound.isPresent() || x.upperBound.isPresent())
									.findAny();
							if (!toSolve.isPresent()) {
								toSolve = v.stream().findAny();
								if (!toSolve.isPresent()) {
									if (isSolved()) {
										return;
									} else {
										// if there is no eligible type
										// variable,
										// then don't know what to do...
										// the situation is probably due to the
										// fact
										// that there is a dependency cycle
										// between
										// type variables
										throw new IllegalArgumentException(
												"there is probably a dependency cycle between type variables");
									}
								}
							}
						}
						VariableSpec x = toSolve.get();
						Optional<DataType> solution = x.variable.getSolver().apply(x.lowerBound.map((c) -> c.sub),
								x.upperBound.map((c) -> c.sup));
						if (solution.isPresent()) {
							DataType t = solution.get();
							if (contains(t, x.variable)) {
								// the substitute is not allowed to contain the
								// substituted variable
								log.error(
										x.name + ": cannot substitute " + typeToString(x.variable) + " with "
												+ typeToString(t),
										x.variable.getConcernedObject(), x.variable.getConcernedStructuralFeature());
								return;
							} else {
								// don't remove any of the taken-into-account
								// constraints, since reSortConstraints will
								// move these constraints (after substitution)
								// to the determined set, such that the
								// correctness
								// of the solution is checked at the next
								// iteration
								doSubstitute(x.variable, t);
								reSortConstraints();
								continue;
							}
						} else {
							// if the variable-specific solver does not return a
							// inferred type, this is the indication that an
							// error has occurred... nothing else can be done in
							// such a case. just in case, issue an additional
							// error message
							log.error(x.variable.getName() + ": cannot infer the type", x.variable.getConcernedObject(),
									x.variable.getConcernedStructuralFeature());
							return;
						}
					}
				}
			}
		}
	}

	private void doSubstitute(TypeVariable a, DataType b) {
		if (a.getSubstitute() != null) {
			throw new IllegalArgumentException("the type variable should not have been substituted already");
		} else {
			a.setSubstitute(reprOrType(b));
		}
	}

	public static boolean equalsUpToSubst(DataType l, DataType r) {
		if (l == r) {
			return true;
		} else if (l instanceof BooleanType && r instanceof BooleanType) {
			return true;
		} else if (l instanceof RangeType && r instanceof RangeType) {
			RangeType rl = (RangeType) l;
			RangeType rr = (RangeType) r;
			return isEq(rl.getVmin(), rr.getVmin()) && isEq(rl.getVmax(), rr.getVmax());
		} else if (l instanceof SequenceType && r instanceof SequenceType) {
			return equalsUpToSubst(((SequenceType) l).getType(), ((SequenceType) r).getType());
		} else if (l instanceof TupleType && r instanceof TupleType) {
			Map<String, Optional<FieldDecl>> lm = getFieldMap((TupleType) l);
			Map<String, Optional<FieldDecl>> rm = getFieldMap((TupleType) r);
			return MapUtils.merge(lm, rm).entrySet().stream().anyMatch((e) -> e.getValue().a.isPresent()
					&& e.getValue().b.isPresent() && e.getValue().a.get().isPresent()
					&& e.getValue().b.get().isPresent()
					&& equalsUpToSubst(e.getValue().a.get().get().getType(), e.getValue().b.get().get().getType()));
		} else if (l instanceof TypeVariable) {
			if (r instanceof TypeVariable) {
				return ((TypeVariable) l).getName().equals(((TypeVariable) r).getName());
			} else {
				DataType ls = ((TypeVariable) l).getSubstitute();
				if (ls == null) {
					return false;
				} else {
					return equalsUpToSubst(ls, r);
				}
			}
		} else if (r instanceof TypeVariable) {
			DataType rs = ((TypeVariable) r).getSubstitute();
			if (rs == null) {
				return false;
			} else {
				return equalsUpToSubst(l, rs);
			}
		} else {
			return false;
		}
	}

	private boolean contains(DataType r, TypeVariable l) {
		if (l == r) {
			return true;
		} else if (r instanceof TypeVariable && ((TypeVariable) r).getName().equals(l.getName())) {
			return true;
		} else if (r instanceof BooleanType) {
			return false;
		} else if (r instanceof RangeType) {
			return false;
		} else if (r instanceof SequenceType) {
			return contains(((SequenceType) r).getType(), l);
		} else if (r instanceof TupleType) {
			return ((TupleType) r).getFields().stream().map(FieldDecl::getType).anyMatch((x) -> contains(r, l));
		} else {
			throw new IllegalArgumentException("unknown type");
		}
	}

	private void reSortConstraints() {
		Map<String, Deque<Constraint>> oldUpperBounds = upperBounds;
		Map<String, Deque<Constraint>> oldLowerBounds = lowerBounds;
		Deque<Constraint> oldVarVarConstraints = varVarConstraints;
		upperBounds = new ConcurrentHashMap<>();
		lowerBounds = new ConcurrentHashMap<>();
		varVarConstraints = new ConcurrentLinkedDeque<>();
		Stream<Stream<Deque<Constraint>>> s = Stream.of(oldUpperBounds.values().stream(),
				oldLowerBounds.values().stream(), Stream.of(oldVarVarConstraints));
		s.flatMap((x) -> x).flatMap(Deque::stream)
				.forEach((c) -> addConstraint(c.sub, c.sup, c.originObject, c.originFeature));
	}

	public static Optional<DataType> upperOrLowerSolver(Optional<DataType> lower, Optional<DataType> upper) {
		if (upper.isPresent()) {
			return upper;
		} else if (lower.isPresent()) {
			return lower;
		} else {
			return Optional.empty();
		}
	}

	private Optional<DataType> union(String n, Deque<Constraint> constraints) {
		TypeVariable v = variables.get(n);
		if (constraints.stream().allMatch((x) -> x.sub instanceof SequenceType)) {
			TypeVariable beta = createFreshDependency(TypeInferenceSolver::upperOrLowerSolver, v);
			constraints.stream().forEach(
					(c) -> addConstraint(((SequenceType) c.sub).getType(), beta, c.originObject, c.originFeature));
			return Optional.of(createSequenceType(beta));
		} else if (constraints.stream().allMatch((x) -> x.sub instanceof BooleanType)) {
			return Optional.of(createBooleanType());
		} else if (constraints.stream().allMatch((x) -> x.sub instanceof RangeType)) {
			Expression mi = constraints.stream().map((x) -> ((RangeType) x.sub).getVmin()).reduce(TypeInferenceSolver::min)
					.get();
			Expression ma = constraints.stream().map((x) -> ((RangeType) x.sub).getVmax()).reduce(TypeInferenceSolver::max)
					.get();
			return Optional.of(createRangeType(mi, ma));
		} else if (constraints.stream().allMatch((x) -> x.sub instanceof TupleType)) {
			return constraints.stream().map((c) -> (TupleType) c.sub).reduce((a, b) -> tupleTypeUnion(a, b, v))
					.map((x) -> (DataType) x);
		} else {
			String err = n + ": incompatible type constraints ("
					+ constraints.stream().map((c) -> c.sub).flatMap(TypeInferenceSolver::typeConstructor).distinct()
							.map((s) -> s + " <= " + typeToString(v)).collect(Collectors.joining(", "))
					+ ")";
			constraints.forEach((c) -> {
				log.error(err, c.originObject, c.originFeature);
			});
			return Optional.empty();
		}
	}

	private TupleType tupleTypeUnion(TupleType t1, TupleType t2, TypeVariable w) {
		Map<String, Optional<FieldDecl>> f2 = getFieldMap(t2);
		List<FieldDecl> fields = t1.getFields().stream().flatMap((l) -> {
			Optional<FieldDecl> r = f2.getOrDefault(l.getName(), Optional.empty());
			Optional<FieldDecl> s = r.map((y) -> {
				TypeVariable v = createFreshDependency(TypeInferenceSolver::upperOrLowerSolver, w);
				addConstraint(l.getType(), v, v.getConcernedObject(), v.getConcernedStructuralFeature());
				addConstraint(y.getType(), v, v.getConcernedObject(), v.getConcernedStructuralFeature());
				return createFieldDecl(l.getName(), v);
			});
			Optional<Stream<FieldDecl>> x = s.map(Stream::of);
			return x.orElse(Stream.empty());
		}).collect(Collectors.toList());
		return createTupleType(fields);
	}

	private static Map<String, Optional<FieldDecl>> getFieldMap(TupleType t1) {
		return t1.getFields().stream().collect(Collectors.toConcurrentMap(FieldDecl::getName, Optional::of));
	}

	private Optional<DataType> intersect(String n, Deque<Constraint> constraints) {
		TypeVariable v = variables.get(n);
		if (constraints.stream().allMatch((x) -> x.sup instanceof SequenceType)) {
			TypeVariable beta = createFreshDependency(TypeInferenceSolver::upperOrLowerSolver, v);
			constraints.stream().forEach(
					(c) -> addConstraint(beta, ((SequenceType) c.sup).getType(), c.originObject, c.originFeature));
			return Optional.of(createSequenceType(beta));
		} else if (constraints.stream().allMatch((x) -> x.sup instanceof BooleanType)) {
			return Optional.of(createBooleanType());
		} else if (constraints.stream().allMatch((x) -> x.sup instanceof RangeType)) {
			Expression mi = constraints.stream().map((x) -> ((RangeType) x.sup).getVmin()).reduce(TypeInferenceSolver::max)
					.get();
			Expression ma = constraints.stream().map((x) -> ((RangeType) x.sup).getVmax()).reduce(TypeInferenceSolver::min)
					.get();
			if (isLe(mi, ma)) {
				return Optional.of(createRangeType(mi, ma));
			} else {
				constraints.forEach((c) -> {
					log.error(n + ": the intersection of the ranges is empty", c.originObject, c.originFeature);
				});
				return Optional.empty();
			}
		} else if (constraints.stream().allMatch((x) -> x.sup instanceof TupleType)) {
			Stream<Pair<Constraint, FieldDecl>> s = constraints.stream().flatMap(TypeInferenceSolver::getFieldDecls);
			Map<String, List<Pair<Constraint, FieldDecl>>> fields = s
					.collect(Collectors.groupingBy((f) -> f.b.getName()));
			return Optional.of(createTupleType(fields.entrySet().stream().map((e) -> {
				TypeVariable b = createFreshDependency(TypeInferenceSolver::upperOrLowerSolver, v);
				e.getValue().forEach((f) -> {
					addConstraint(b, f.b.getType(), f.a.originObject, f.a.originFeature);
				});
				return createFieldDecl(e.getKey(), v);
			}).collect(Collectors.toList())));
		} else {
			String err = n + ": incompatible type constraints ("
					+ constraints.stream().map((c) -> c.sup).flatMap(TypeInferenceSolver::typeConstructor).distinct()
							.map((s) -> typeToString(v) + "<=" + s).collect(Collectors.joining(", "))
					+ ")";
			constraints.forEach((c) -> {
				log.error(err, c.originObject, c.originFeature);
			});
			return Optional.empty();
		}
	}

	private static Stream<String> typeConstructor(DataType t) {
		if (t instanceof BooleanType) {
			return Stream.of("boolean");
		} else if (t instanceof TupleType) {
			return Stream.of("tuple");
		} else if (t instanceof SequenceType) {
			return Stream.of("sequence");
		} else if (t instanceof RangeType) {
			return Stream.of("range");
		} else {
			throw new IllegalArgumentException("unknown type constructor");
		}
	}

	private static Stream<Pair<Constraint, FieldDecl>> getFieldDecls(Constraint x) {
		Stream<FieldDecl> s = ((TupleType) x.sup).getFields().stream();
		return s.map((y) -> new Pair<>(x, y));
	}

	private static Expression min(Expression l, Expression r) {
		if (InterpInZ.le(l, r)) {
			return l;
		} else {
			return r;
		}
	}

	private static Expression max(Expression l, Expression r) {
		if (InterpInZ.le(r, l)) {
			return l;
		} else {
			return r;
		}
	}

	private boolean checkDeterminedConstraint(Constraint c) {
		DataType sub = substitute(c.sub);
		DataType sup = substitute(c.sup);
		if (sub == sup) {
			return true;
		} else if (sub instanceof BooleanType && sup instanceof BooleanType) {
			return true;
		} else if (sub instanceof SequenceType && sup instanceof SequenceType) {
			addConstraint(((SequenceType) sub).getType(), ((SequenceType) sup).getType(), c.originObject,
					c.originFeature);
			return true;
		} else if (sub instanceof TupleType && sup instanceof TupleType) {
			TupleType l = (TupleType) sub;
			TupleType r = (TupleType) sup;
			Map<String, Optional<FieldDecl>> lfields = getFieldMap(l);
			// use reduce rather than allMatch in order to ensure that all the
			// fields are checked, such that all the detectable errors are
			// reported at once
			return r.getFields().stream().reduce(true, (b, rf) -> {
				Optional<FieldDecl> olf = lfields.getOrDefault(rf.getName(), Optional.empty());
				if (olf.isPresent()) {
					olf.ifPresent((lf) -> addConstraint(lf.getType(), rf.getType(), c.originObject, c.originFeature));
					return b;
				} else {
					log.error("incompatible tuple types: field `" + rf.getName() + "' is missing", c.originObject,
							c.originFeature);
					return false;
				}
			}, (a, b) -> a && b);
		} else if (sub instanceof RangeType && sup instanceof RangeType) {
			RangeType l = (RangeType) sub;
			RangeType r = (RangeType) sup;
			if (!isLe(r.getVmin(), l.getVmin()) || !isLe(l.getVmax(), r.getVmax())) {
				log.error("incompatible ranges: {" + InterpInZ.eval(l.getVmin()) + ".." + InterpInZ.eval(l.getVmax())
						+ "} is not included in {" + InterpInZ.eval(r.getVmin()) + ".." + InterpInZ.eval(r.getVmax())
						+ "}", c.originObject, c.originFeature);
				return false;
			} else {
				return true;
			}
		} else if (sub instanceof BooleanType && sup instanceof BooleanType) {
			return true;
		} else {
			log.error("type " + typeToString(sub) + " is not a subtype of " + typeToString(sup), c.originObject,
					c.originFeature);
			return false;
		}
	}

	private static boolean isLe(Expression l, Expression r) {
		return InterpInZ.le(l, r);
	}

	private static boolean isEq(Expression l, Expression r) {
		return InterpInZ.eq(l, r);
	}

	private static String typeToString(DataType t) {
		if (t instanceof BooleanType) {
			return "boolean";
		} else if (t instanceof RangeType) {
			RangeType r = (RangeType) t;
			return "integer { " + InterpInZ.eval(r.getVmin()) + " .. " + InterpInZ.eval(r.getVmax()) + " }";
		} else if (t instanceof TupleType) {
			TupleType tt = (TupleType) t;
			return "tuple { " + tt.getFields().stream().map((x) -> x.getName() + ": " + typeToString(x.getType()))
					.collect(Collectors.joining(", ")) + " }";
		} else if (t instanceof SequenceType) {
			SequenceType s = (SequenceType) t;
			return "sequence { " + typeToString(s.getType()) + " }";
		} else if (t instanceof TypeVariable) {
			return "'" + ((TypeVariable) t).getName();
		} else {
			return "unknown type";
		}
	}

	public static <T extends EObject> T copy(T x) {
		// never copy type variable in order to ensure the uniqueness of the
		// object, and therefore the uniqueness of the substitution
		if (x instanceof TypeVariable) {
			// TODO ensure that any type variable in never used in two types
			return x;
		} else {
			return EcoreUtil.copy(x);
		}
	}

	private static SequenceType createSequenceType(DataType t) {
		SequenceType ret = SosADLFactory.eINSTANCE.createSequenceType();
		ret.setType(copy(t));
		return ret;
	}

	private static BooleanType createBooleanType() {
		return SosADLFactory.eINSTANCE.createBooleanType();
	}

	private static RangeType createRangeType(Expression mi, Expression ma) {
		RangeType ret = SosADLFactory.eINSTANCE.createRangeType();
		ret.setVmin(copy(mi));
		ret.setVmax(copy(ma));
		return ret;
	}

	private static FieldDecl createFieldDecl(String name, DataType t) {
		FieldDecl ret = SosADLFactory.eINSTANCE.createFieldDecl();
		ret.setName(name);
		ret.setType(t);
		return ret;
	}

	private static TupleType createTupleType(List<FieldDecl> f) {
		TupleType ret = SosADLFactory.eINSTANCE.createTupleType();
		ret.getFields().addAll(f);
		return ret;
	}
}
