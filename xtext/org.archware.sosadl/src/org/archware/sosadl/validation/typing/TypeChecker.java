package org.archware.sosadl.validation.typing;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentLinkedDeque;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.archware.sosadl.attributed.AttributeAdapter;
import org.archware.sosadl.generator.SosADLPrettyPrinterGenerator;
import org.archware.sosadl.sosADL.ArchitectureDecl;
import org.archware.sosadl.sosADL.AssertionDecl;
import org.archware.sosadl.sosADL.BehaviorDecl;
import org.archware.sosadl.sosADL.BinaryExpression;
import org.archware.sosadl.sosADL.BooleanType;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.DataTypeDecl;
import org.archware.sosadl.sosADL.EntityBlock;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.FieldDecl;
import org.archware.sosadl.sosADL.FormalParameter;
import org.archware.sosadl.sosADL.FunctionDecl;
import org.archware.sosadl.sosADL.GateDecl;
import org.archware.sosadl.sosADL.IdentExpression;
import org.archware.sosadl.sosADL.Import;
import org.archware.sosadl.sosADL.IntegerValue;
import org.archware.sosadl.sosADL.Library;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.MethodCall;
import org.archware.sosadl.sosADL.NamedType;
import org.archware.sosadl.sosADL.RangeType;
import org.archware.sosadl.sosADL.Sequence;
import org.archware.sosadl.sosADL.SequenceType;
import org.archware.sosadl.sosADL.SoS;
import org.archware.sosadl.sosADL.SosADL;
import org.archware.sosadl.sosADL.SosADLFactory;
import org.archware.sosadl.sosADL.SosADLPackage;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.sosADL.Tuple;
import org.archware.sosadl.sosADL.TupleElement;
import org.archware.sosadl.sosADL.TupleType;
import org.archware.sosadl.sosADL.UnaryExpression;
import org.archware.sosadl.sosADL.Unit;
import org.archware.sosadl.sosADL.Valuing;
import org.archware.sosadl.tv.typeCheckerHelper.TypeVariable;
import org.archware.sosadl.validation.AccumulatingValidator;
import org.archware.sosadl.validation.typing.impl.ArchitectureEnvContent;
import org.archware.sosadl.validation.typing.impl.MediatorEnvContent;
import org.archware.sosadl.validation.typing.impl.SystemEnvContent;
import org.archware.sosadl.validation.typing.impl.TypeEnvContent;
import org.archware.sosadl.validation.typing.impl.VariableEnvContent;
import org.archware.sosadl.validation.typing.interp.InterpInZ;
import org.archware.sosadl.validation.typing.proof.*;
import org.archware.utils.DecaFunction;
import org.archware.utils.IntPair;
import org.archware.utils.ListUtils;
import org.archware.utils.MapUtils;
import org.archware.utils.OptionalUtils;
import org.archware.utils.Pair;
import org.archware.utils.PentaFunction;
import org.archware.utils.StreamUtils;
import org.archware.utils.TreDecaFunction;
import org.archware.utils.TriConsumer;
import org.archware.utils.TriFunction;
import org.eclipse.emf.common.util.ECollections;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.xtext.xbase.lib.ListExtensions;

/**
 * Implementation of the type system.
 * 
 * <p>
 * Like stated by the name of the class, a type checker for SoSADL.
 * The entry point of the type checker is the unique public method {@link #typecheck(SosADL)}.
 * This implementation also builds a proof term that can be later checked against against the type system, e.g., using some proof assistant like Coq.
 * 
 * <p>
 * The type checker is implemented following the structure of the type system.
 * Namely, each type judgment is implemented by a method that attempts to prove that judgment.
 * This method selects the appropriate typing rule, and (recursively) call the other methods to prove the premises of the rule.
 * The parameters of such a method are the input used to drive the selection of the right typing rule.
 * In most of the cases, the parameters are the (abstract syntax) subtree to type check as well as the local typing environment.
 * Each such function builds and returns the reified proof term for the judgment it has proved.
 * 
 * <p>
 * Specific cases occurs:
 * <ul>
 * <li>For some judgments, several prover may coexist depending on the context.
 *     This is typically the case of the <code>subtype</code> judgment. See, e.g.,
 *     {@link #smallestSuperType(Class, String, DataType, DataType, EObject, EStructuralFeature)} and
 *     {@link #subtype(DataType, DataType, Consumer)}.</li>
 * <li>For some judgments, the method computes synthesized attributes, which are thus returned in addition to the proof term.
 *     These methods typically return {@link Pair} objects.
 *     This is typically the case of the <code>type_expression</code> and <code>type_expression_node> judgments.
 *     See, e.g., {@link #type_expression(Environment, Expression)} or
 *     {@link #type_expression_node(Environment, Expression)}.</li>
 * </ul>
 * 
 * <p>
 * The behavior when a method fails to prove the corresponding judgments is not homogeneous.
 * Most of the methods simply return a {@literal null} proof term, possibly wrapped in a {@link Pair} object when appropriate.
 * Some methods wrap the returned proof term in an {@link Optional} object.
 * The behavior will be later homogenized.
 * 
 * <p>
 * The implementation is stateful in that, according to the inherited {@link AccumulatingValidator} class, it accumulates error messages for later reporting.
 * The type checker is thus not bound to any specific error reporting mechanism or framework.
 * 
 * <p>
 * The handling of type variables is deferred to {@link TypeInferenceSolver}. Namely, the solver is fed with subtyping constraints.
 * When all the constraints have been issued, its {@link TypeInferenceSolver#solve()} method is invoked in order to try to find a suitable solution.
 * A callback is attached to each type variable. The solver calls it whenever it has reduced the set of constraints to at most one upper bound and one lower bound.
 * The callback can freely choose any type according to the given bounds.
 * If no bound is available, the callback can either choose an arbitrary type, or issue an error.
 * The solver also honors dependencies between variables: it never tries to solve a variable that has any unsubstituted dependency.
 * This latter mechanism is used to ensure the correct ordering of type variable resolution, for instance, to handle arithmetic expression, which require strict type synthesis from the leaves to the root of the abstract syntax tree.
 *
 * <p>
 * For future evolutions, the following items should be looked at in order to improve the handling of interval types:
 * <ul>
 * <li>Kaucher arithmetic</li>
 * <li>Abstract interpretation techniques</li>
 * </ul>
 * 
 * @author Jeremy Buisson
 */
public class TypeChecker extends AccumulatingValidator {
	private TypeInferenceSolver inference = new TypeInferenceSolver(this);
	private Collection<Runnable> delayedTasks = new ConcurrentLinkedDeque<>();
	private Map<String, NumberGenerator> freshMaker = new ConcurrentHashMap<>();
	
	@Override
	public void error(String msg, EObject eo, EStructuralFeature esf) {
		System.out.println("" + eo + ": " + msg);
		if(eo == null) {
			throw new NullPointerException();
		}
		super.error(msg, eo, esf);
	}
	
	/**
	 * Performs the whole type-checking of a SoSADL specification.
	 * 
	 * @param file the SoSADL model.
	 */
	public void typecheck(SosADL file) {
		try {
			type_sosADL(file);
			solveConstraints();
		} catch(Throwable t) {
			t.printStackTrace();
			error("Bug in the type checker", file, null);
			throw t;
		}
	}
	
	/**
	 * Solves the constraints for all the accumulated type variables.
	 * 
	 * <p>
	 * This method calls the type inference solver.
	 * If successful, it then invokes the delayed task recorded for each type variable.
	 */
	private void solveConstraints() {
		inference.solve();
		if(inference.isSolved()) {
			delayedTasks.forEach((t) -> t.run());
		}
	}
	
	private Type_sosADL type_sosADL(SosADL file) {
		// type_SosADL:
		if(file.getContent() != null) {
			return saveProof(file, createType_SosADL_file(file.getImports(), file.getContent(), type_unit(Environment.empty(), file.getContent())));
		} else {
			error("The file must contains a unit", file, null);
			return null;
		}
	}

	private Type_unit type_unit(Environment gamma, Unit content) {
		// type_SoS:
		if(content instanceof SoS && ((SoS)content).getName() != null && ((SoS)content).getDecls() != null) {
			return saveProof(content, createType_SoS(gamma, ((SoS)content).getName(), ((SoS)content).getDecls(), type_entityBlock(gamma, ((SoS)content).getDecls())));
		} else
		// type_Library:
		if(content instanceof Library && ((Library)content).getName() != null && ((Library)content).getDecls() != null) {
			return saveProof(content, createType_Library(gamma, ((Library)content).getName(), ((Library)content).getDecls(), type_entityBlock(gamma, ((Library)content).getDecls())));
		} else {
			error("The unit must contain a name and a block", content, null);
			return null;
		}
	}

	private Type_entityBlock type_entityBlock(Environment gamma, EntityBlock decls) {
		saveEnvironment(decls, gamma);
		return saveProof(decls, type_entityBlock(gamma, decls, decls.getDatatypes(), decls.getFunctions(), decls.getSystems(), decls.getMediators(), decls.getArchitectures()));
	}

	private Type_entityBlock type_entityBlock(Environment gamma, EntityBlock decls, EList<DataTypeDecl> datatypes, EList<FunctionDecl> functions,
			EList<SystemDecl> systems, EList<MediatorDecl> mediators, EList<ArchitectureDecl> architectures) {
		Pair<Incrementally<DataTypeDecl,Type_datatypeDecl>,Environment> p1 = type_datatypeDecls(gamma, datatypes);
		Pair<Incrementally<FunctionDecl,Type_function>,Environment> p2 = type_functions(p1.getB(), functions);
		Pair<Incrementally<SystemDecl,Simple_increment<SystemDecl,Type_system>>,Environment> p3 = type_systems(p2.getB(), systems);
		Pair<Incrementally<MediatorDecl,Simple_increment<MediatorDecl,Type_mediator>>,Environment> p4 = type_mediators(p3.getB(), mediators);
		Pair<Incrementally<ArchitectureDecl, Simple_increment<ArchitectureDecl, Type_architecture>>, Environment> p5 = type_architectures(p4.getB(), architectures);
		return createType_EntityBlock_whole(gamma, datatypes, p1.getB(), functions, p2.getB(), systems, p3.getB(), mediators, p4.getB(), architectures, p5.getB(), p1.getA(), p2.getA(), p3.getA(), p4.getA(), p5.getA());
	}

	private Pair<Incrementally<ArchitectureDecl, Simple_increment<ArchitectureDecl, Type_architecture>>, Environment> type_architectures(Environment gamma, EList<ArchitectureDecl> architectures) {
		return proveIncrementally(gamma, architectures, (g,x) -> proveSimpleIncrement(g, x, this::type_architecture, "SosADL.SosADL.ArchitectureDecl_name", ArchitectureDecl::getName, "(fun x => Some (EArchitecture x))", (d) -> new ArchitectureEnvContent(d)));
	}

	private Pair<Incrementally<MediatorDecl, Simple_increment<MediatorDecl,Type_mediator>>, Environment> type_mediators(
			Environment gamma, EList<MediatorDecl> mediators) {
		return proveIncrementally(gamma, mediators, (g,x) -> proveSimpleIncrement(g, x, this::type_mediator, "SosADL.SosADL.MediatorDecl_name", MediatorDecl::getName, "(fun x => Some (EMediator x))", (d) -> new MediatorEnvContent(d)));
	}

	private Pair<Incrementally<SystemDecl, Simple_increment<SystemDecl,Type_system>>, Environment> type_systems(Environment gamma, EList<SystemDecl> systems) {
		return proveIncrementally(gamma, systems, (g,x) -> proveSimpleIncrement(g, x, this::type_system, "SosADL.SosADL.SystemDecl_name", SystemDecl::getName, "(fun x => Some (ESystem x))", (d) -> new SystemEnvContent(d)));
	}

	private Pair<Incrementally<FunctionDecl, Type_function>, Environment> type_functions(
			Environment gamma, EList<FunctionDecl> functions) {
		return proveIncrementally(gamma, functions, this::type_function);
	}

	private Pair<Incrementally<DataTypeDecl, Type_datatypeDecl>, Environment> type_datatypeDecls(Environment gamma,
			EList<DataTypeDecl> datatypes) {
		return proveIncrementally(gamma, datatypes, this::type_datatypeDecl);
	}

	private Pair<Type_datatypeDecl, Environment> type_datatypeDecl(Environment gamma, DataTypeDecl dataTypeDecl) {
		saveEnvironment(dataTypeDecl, gamma);
		if(dataTypeDecl.getName() != null) {
			Forall<FunctionDecl, Ex<FormalParameter, And<Equality,Equality>>> p2 =
					proveForall(dataTypeDecl.getFunctions(),
					(f) -> proveDataIsSelf(dataTypeDecl, f));
			if(dataTypeDecl.getDatatype() != null) {
				Pair<DataType, Type_datatype> p1 = type_datatype(gamma, dataTypeDecl.getDatatype());
				Pair<Incrementally<FunctionDecl, Type_function>, Environment> p3 =
						type_functions(gamma.put(dataTypeDecl.getName(),
								new TypeEnvContent(dataTypeDecl, p1.getA(), nil())),
								dataTypeDecl.getFunctions());
				return new Pair<>(saveProof(dataTypeDecl,
						createType_DataTypeDecl_def(gamma, dataTypeDecl.getName(),
								dataTypeDecl.getDatatype(), p1.getA(),
								dataTypeDecl.getFunctions(), p3.getB(),
								p1.getB(),
								p2,
						p3.getA())), p3.getB());
			} else {
				String name = generateFreshNameFor(dataTypeDecl.getName());
				Pair<Incrementally<FunctionDecl, Type_function>, Environment> p3 =
						type_functions(gamma.put(dataTypeDecl.getName(),
								new TypeEnvContent(dataTypeDecl, createNamedType(name), nil())),
								dataTypeDecl.getFunctions());
				return new Pair<>(saveProof(dataTypeDecl,
						createType_DataTypeDecl_def_None(gamma, dataTypeDecl.getName(), name,
								dataTypeDecl.getFunctions(),
								p3.getB(), createReflexivity(),
								p2,
								p3.getA())), p3.getB());
			}
		} else {
			error("The data type declaration must have a name", dataTypeDecl, null);
			return new Pair<>(null, gamma);
		}
	}

	private String generateFreshNameFor(String name) {
		int n = freshMaker.computeIfAbsent(name, (x) -> new SequentialNumberGenerator()).getAsInt();
		return name + ":" + n;
	}

	private Ex<FormalParameter, And<Equality,Equality>> proveDataIsSelf(DataTypeDecl d, FunctionDecl f) {
		if(f.getData() != null
				&& f.getData().getType() instanceof NamedType
				&& ((NamedType)f.getData().getType()).getName().equals(d.getName())) {
			return createEx_intro(f.getData(), createConj(createReflexivity(), createReflexivity()));
		} else {
			if(f.getData() != null && (!(f.getData().getType() instanceof NamedType) || !((NamedType)f.getData().getType()).getName().equals(d.getName()))) {
				error("The type of the data parameter " + f.getData().getName() + " must be `" + d.getName() + "'", f.getData().getType(), null);
			} else if(f.getData() == null) {
				error("The function must have a data parameter", f, null);
			} else {
				error("Type error", f, null);
			}
			return null;
		}
	}

	private Pair<Type_function, Environment> type_function(Environment gamma, FunctionDecl f) {
		saveEnvironment(f, gamma);
		if(f.getData() != null
				&& f.getData().getName() != null
				&& f.getData().getType() != null
				&& f.getData().getType() instanceof NamedType
				&& ((NamedType)f.getData().getType()).getName() != null
				&& gamma.get(((NamedType)f.getData().getType()).getName()) != null
				&& gamma.get(((NamedType)f.getData().getType()).getName()) instanceof TypeEnvContent
				&& f.getName() != null
				&& f.getType() != null
				&& f.getExpression() != null) {
			Optional<Pair<Pair<List<FormalParameter>,Environment>,And<Forall2<FormalParameter,FormalParameter,And<Equality,Ex<DataType,And<Equality,Ex<DataType,And<Equality,Type_datatype>>>>>>,Mutually<FormalParameter,True>>>> op3 = type_formalParameters(gamma, cons(f.getData(), f.getParameters()));
			if(op3.isPresent()) {
				Pair<DataType, Type_datatype> p2 = type_datatype(gamma, f.getType());
				if(p2.getA() != null && p2.getB() != null) {
					Pair<Pair<List<FormalParameter>, Environment>, And<Forall2<FormalParameter, FormalParameter, And<Equality, Ex<DataType, And<Equality, Ex<DataType, And<Equality, Type_datatype>>>>>>, Mutually<FormalParameter, True>>> p3 = op3.get();
					FormalParameter self2 = p3.getA().getA().get(0);
					DataType realType = ((TypeEnvContent)gamma.get(((NamedType)f.getData().getType()).getName())).getDataType();
					if(EcoreUtil.equals(self2.getType(), realType)) {
						EList<FormalParameter> params2 = cdr(p3.getA().getA());
						Environment gammap = p3.getA().getB();
						Pair<Incrementally<Valuing, Type_valuing>, Environment> p4 = type_valuings(gammap, f.getValuing());
						Environment gammav = p4.getB();
						Pair<Type_expression, DataType> p5 = type_expression(gammav, f.getExpression());
						FunctionDecl toAdd = createFunctionDecl(self2, f.getName(), params2, p2.getA(), f.getValuing(), f.getExpression());
						Environment gamma1 = gamma.put(((NamedType)f.getData().getType()).getName(),
								((TypeEnvContent)gamma.get(((NamedType)f.getData().getType()).getName())).addMethod(toAdd));
						DataType t = p5.getB();
						if(p5.getA() != null && t != null) {
							inference.addConstraint(t, p2.getA(), f, SosADLPackage.Literals.FUNCTION_DECL__EXPRESSION);
							return new Pair<>(saveProof(f,
									proofTerm(t, Type_function.class,
											(x) -> createType_FunctionDecl_Method(gamma,
													f.getData().getName(),
											((NamedType)f.getData().getType()).getName(),
											((TypeEnvContent)gamma.get(((NamedType)f.getData().getType()).getName())).getDataTypeDecl(),
											realType,
											((TypeEnvContent)gamma.get(((NamedType)f.getData().getType()).getName())).getMethods(),
											f.getName(),
											f.getParameters(),
											params2,
											gammap,
											f.getType(),
											p2.getA(),
											f.getValuing(),
											gammav,
											f.getExpression(),
											x,
											gamma1,
											createReflexivity(),
											p2.getB(),
											p3.getB(),
											p4.getA(),
											p5.getA(),
											subtype(x, p2.getA(), f, SosADLPackage.Literals.FUNCTION_DECL__EXPRESSION).orElse(null),
											createReflexivity()))),
									gamma1);
						} else {
							error("(p5.getA() != null && t != null)", f, null);
							return new Pair<>(null, gamma);
						}
					} else {
						String s1 = TypeInferenceSolver.typeToString(self2.getType());
						String s2 = TypeInferenceSolver.typeToString(realType);
						error("Inconsistent typing of the type: " + s1 + " / " + s2, f, SosADLPackage.Literals.FUNCTION_DECL__DATA);
						return new Pair<>(null, gamma);
					}
				} else {
					error("(p2.getA() != null && p2.getB() != null)", f, null);
					return new Pair<>(null, gamma);
				}
			} else {
				error("op3.isPresent()", f, null);
				return new Pair<>(null, gamma);
			}
		} else {
			if(f.getExpression() == null) {
				error("The function must contain an expression", f, SosADLPackage.Literals.FUNCTION_DECL__EXPRESSION);
			}
			if(f.getType() == null) {
				error("The function must have a return type", f, SosADLPackage.Literals.FUNCTION_DECL__TYPE);
			}
			if(f.getName() == null) {
				error("The function must have a name", f, SosADLPackage.Literals.FUNCTION_DECL__NAME);
			}
			if(f.getData() == null) {
				error("The function must have a data parameter", f, SosADLPackage.Literals.FUNCTION_DECL__DATA);
			} else {
				if(f.getData().getName() == null) {
					error("The data parameter must have a name", f.getData(), SosADLPackage.Literals.FORMAL_PARAMETER__NAME);
				}
				if(f.getData().getType() == null) {
					error("The data parameter must have a type", f.getData(), SosADLPackage.Literals.FORMAL_PARAMETER__TYPE);
				} else {
					if (!(f.getData().getType() instanceof NamedType)) {
						error("The type of the data parameter must be a named type", f.getData().getType(), null);
					} else {
						if(((NamedType)f.getData().getType()).getName() == null) {
							error("The type of the data parameter must have a name", f.getData().getType(), SosADLPackage.Literals.NAMED_TYPE__NAME);
						} else {
							if (gamma.get(((NamedType)f.getData().getType()).getName()) == null) {
								error("The type `" + ((NamedType)f.getData().getType()).getName() + "' is undefined in this context", f.getData().getType(), null);
							} else if (!(gamma.get(((NamedType)f.getData().getType()).getName()) instanceof TypeEnvContent)) {
								error("`" + ((NamedType)f.getData().getType()).getName() + "' is not a type in this context", f.getData().getType(), null);
							}
						}
					}
				}
			}
			return new Pair<>(null, gamma);
		}
	}
	
	private boolean isSubtype(DataType a, DataType b) {
		Optional<Subtype> p = new TypeChecker().subtype(a, b, null, null);
		return p.isPresent();
	}

	private Optional<Subtype> subtype(DataType a, DataType b, EObject target, EStructuralFeature targetForError) {
		return subtype(a, b, (m) -> error(m, target, targetForError));
	}
	private Optional<Subtype> subtype(DataType a, DataType b, Consumer<String> error) {
		if(EcoreUtil.equals(a, b)) {
			return Optional.of(createSubtype_refl(a));
		} else if(a instanceof RangeType && b instanceof RangeType
				&& ((RangeType)a).getVmin() != null && ((RangeType)a).getVmax() != null
				&& ((RangeType)b).getVmin() != null && ((RangeType)b).getVmax() != null
				&& isLe(((RangeType)b).getVmin(), ((RangeType)a).getVmin())
				&& isLe(((RangeType)a).getVmax(), ((RangeType)b).getVmax())) {
			return Optional.of(createSubtype_range(
					((RangeType)a).getVmin(), ((RangeType)a).getVmax(),
					((RangeType)b).getVmin(), ((RangeType)b).getVmax(),
					expression_le(((RangeType)b).getVmin(), ((RangeType)a).getVmin()),
					expression_le(((RangeType)a).getVmax(), ((RangeType)b).getVmax())));
		} else if(a instanceof TupleType && b instanceof TupleType) {
			TupleType l = (TupleType) a;
			TupleType r = (TupleType) b;
			List<Pair<Optional<FieldDecl>, FieldDecl>> fields =
					ListExtensions.map(r.getFields(),
							(f) -> new Pair<>(l.getFields().stream()
									.filter((g) -> f.getName().equals(g.getName())).findFirst(), f));
			if(fields.stream().allMatch((p) -> p.getA().isPresent())) {
				List<Pair<Pair<FieldDecl,Optional<Subtype>>,FieldDecl>> proofs =
						ListExtensions.map(fields,
								(f) -> new Pair<>(
										new Pair<>(f.getA().get(),
												subtype(f.getA().get().getType(), f.getB().getType(), error)),
										f.getB()));
				if(proofs.stream().allMatch((p) -> p.getA().getB().isPresent())) {
					Forall<FieldDecl, Ex<String, And<Equality, Ex<DataType, And<Equality, Ex<DataType, And<Equality, Subtype>>>>>>> p1 = proveForall(r.getFields(), (fr) -> {
						String n = fr.getName();
						DataType tr = fr.getType();
						Pair<FieldDecl,Optional<Subtype>> fl = rassoc(proofs, fr);
						DataType tl = fl.getA().getType();
						Subtype p = fl.getB().get();
						return createEx_intro(n, createConj(createReflexivity(),
								createEx_intro(tr, createConj(createReflexivity(),
										createEx_intro(tl, createConj(createReflexivity(), p))))));
					});
					return Optional.of(createSubtype_tuple(l.getFields(), r.getFields(), p1));
				} else {
					return Optional.empty();
				}
			} else {
				error.accept("Some fields are missing: "
				+ fields.stream().filter((p) -> !p.getA().isPresent())
				.map((p) -> p.getB().getName())
				.sorted()
				.collect(Collectors.joining(" ")));
				return Optional.empty();
			}
		} else if (a instanceof SequenceType && b instanceof SequenceType) {
			SequenceType l = (SequenceType) a;
			SequenceType r = (SequenceType) b;
			Optional<Subtype> p = subtype(l.getType(), r.getType(), error);
			return p.map((p1) -> createSubtype_sequence(l.getType(), r.getType(), p1));
		} else {
			if(a instanceof NamedType) {
				errorForNamedType(labelFor(b), "to", (NamedType)a, error);
			}
			if(b instanceof NamedType) {
				errorForNamedType(labelFor(a), "from", (NamedType)b, error);
			}
			if(a instanceof RangeType && b instanceof RangeType) {
				RangeType ra = (RangeType)a;
				RangeType rb = (RangeType)b;
				if(ra.getVmin() == null) {
					error.accept("The range type must have a lower bound");
				}
				if(ra.getVmax() == null) {
					error.accept("The range type must have an upper bound");
				}
				if(rb.getVmin() == null) {
					error.accept("The range type must have a lower bound");
				}
				if(rb.getVmax() == null) {
					error.accept("The range type must have an upper bound");
				}
				if(ra.getVmin() != null && ra.getVmax() != null
					&& rb.getVmin() != null && rb.getVmax() != null
					&& !(isLe(rb.getVmin(), ra.getVmin())
							&& isLe(ra.getVmax(), rb.getVmax()))) {
					SosADLPrettyPrinterGenerator pp = new SosADLPrettyPrinterGenerator();
					error.accept("The range [" + pp.compile(ra.getVmin()) + " = " + InterpInZ.eval(ra.getVmin()) + ".. "
					+ pp.compile(ra.getVmax()) + " = " + InterpInZ.eval(ra.getVmax())
					+ "] is not included in [" + pp.compile(rb.getVmin()) + " = " + InterpInZ.eval(rb.getVmin())
					+ " .. " + pp.compile(rb.getVmax()) + " = " + InterpInZ.eval(rb.getVmax()) + "]");
				}
			}
			if((!(a instanceof NamedType) && !(b instanceof NamedType))
					&& !(a instanceof RangeType && b instanceof RangeType)
					&& !(a instanceof TupleType && b instanceof TupleType)
					&& !(a instanceof SequenceType && b instanceof SequenceType)) {
				error.accept("Cannot convert from " + labelFor(a) + " to " + labelFor(b));
			}
			return Optional.empty();
		}
	}
	
	private static String labelFor(DataType t) {
		if(t instanceof BooleanType) {
			return "boolean";
		} else if(t instanceof RangeType) {
			RangeType r = (RangeType) t;
			return "integer { " + InterpInZ.eval(r.getVmin()) + " .. " + InterpInZ.eval(r.getVmax()) + " }";
		} else if(t instanceof NamedType) {
			return ((NamedType)t).getName();
		} else if(t instanceof TupleType) {
			TupleType tt = (TupleType) t;
			return "tuple { " + tt.getFields().stream().map((x) -> x.getName() + ": " + labelFor(x.getType())).collect(Collectors.joining(", ")) + " }";
		} else if(t instanceof SequenceType) {
			SequenceType s = (SequenceType) t;
			return "sequence { " + labelFor(s.getType()) + " }";
		} else {
			return "unknown type";
		}
	}
	
	private <T> T range_modulo_min(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Supplier<T> pos, Supplier<T> zero, Supplier<T> neg, Supplier<T> divByZero) {
		if(isLe(createIntegerValue(1), rmin)) {
			if(isLe(createIntegerValue(0), lmin)) {
				return zero.get();
			} else {
				return pos.get();
			}
		} else if(isLe(rmax, createOpposite(createIntegerValue(1)))) {
			if(isLe(createIntegerValue(0), lmin)) {
				return zero.get();
			} else {
				return neg.get();
			}
		} else {
			return divByZero.get();
		}
	}
	
	private <T> T range_modulo_max(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Supplier<T> pos, Supplier<T> zero, Supplier<T> neg, Supplier<T> divByZero) {
		if(isLe(createIntegerValue(1), rmin)) {
			if(isLe(lmax, createIntegerValue(0))) {
				return zero.get();
			} else {
				return pos.get();
			}
		} else if(isLe(rmax, createOpposite(createIntegerValue(1)))) {
			if(isLe(lmax, createIntegerValue(0))) {
				return zero.get();
			} else {
				return neg.get();
			}
		} else {
			return divByZero.get();
		}
	}
	
	private static Expression min(Expression l, Expression r) {
		if(InterpInZ.le(l, r)) {
			return l;
		} else {
			return r;
		}
	}
	
	private static Expression max(Expression l, Expression r) {
		if(InterpInZ.le(r, l)) {
			return l;
		} else {
			return r;
		}
	}
	
	private static abstract class AbstractUnaryTypeInfo<P extends Type_expression_node> extends StringBasedUnaryTypeInfo<P> {
		private final PentaFunction<Environment, Expression, DataType, Type_expression, Subtype, P> prover;
			
		public AbstractUnaryTypeInfo(String operator, PentaFunction<Environment, Expression, DataType, Type_expression, Subtype, P> prover) {
			super(operator);
			this.prover = prover;
		}

		@Override
		public P prove(Environment gamma, UnaryExpression e, Type_expression pOperand, DataType tOperand) {
			return prover.apply(gamma, e.getRight(), tOperand, pOperand, createSubtype_refl(tOperand));
		}
	}
	
	private class BooleanUnaryTypeInfo<P extends Type_expression_node> extends AbstractUnaryTypeInfo<P> {
		public BooleanUnaryTypeInfo(String operator, PentaFunction<Environment, Expression, DataType, Type_expression, Subtype, P> prover) {
			super(operator, prover);
		}
		
		@Override
		public Optional<DataType> immediateType(UnaryExpression e, DataType operand) {
			inference.addConstraint(operand, createBooleanType(), e, SosADLPackage.Literals.UNARY_EXPRESSION__RIGHT);
			return Optional.of(TypeChecker.createBooleanType());
		}
	}
	
	private class SynthetizingUnaryTypeInfo<P extends Type_expression_node> extends AbstractUnaryTypeInfo<P> {
		private final Function<DataType, Optional<DataType>> solver;
		
		public SynthetizingUnaryTypeInfo(String operator,
				PentaFunction<Environment, Expression, DataType, Type_expression, Subtype, P> prover,
				Function<DataType, Optional<DataType>> solver) {
			super(operator, prover);
			this.solver = solver;
		}
		
		@Override
		public Optional<DataType> immediateType(UnaryExpression e, DataType operand) {
			if(TypeInferenceSolver.containsVariable(operand)) {
				TypeVariable v = inference.createFreshTypeVariable((lb,ub) -> solver.apply(getSubstitute(operand)), e, null);
				TypeInferenceSolver.streamVariables(operand).forEach((x) -> inference.addDependency(v, x));
				return Optional.of(v);
			} else {
				return solver.apply(operand);
			}
		}
	}
	
	private final UnaryTypeInfo2<?> unop2Same = new SynthetizingUnaryTypeInfo<>("+",
			(g,e,t,p,s) -> createType_expression_Same(g, e, t, ((RangeType)t).getVmin(), ((RangeType)t).getVmax(), p, s),
			(t) -> Optional.ofNullable(t).filter((x) -> x instanceof RangeType));
	
	private final UnaryTypeInfo2<?> unop2Opposite = new SynthetizingUnaryTypeInfo<>("-",
			(g,e,t,p,s) -> createType_expression_Opposite(g, e, t, ((RangeType)t).getVmin(), ((RangeType)t).getVmax(), p, s),
			(t) -> Optional.ofNullable(t)
			.filter((x) -> x instanceof RangeType)
			.map((x) -> createRangeType(createOpposite(((RangeType)x).getVmax()),
					createOpposite(((RangeType)x).getVmin()))));
	
	private final UnaryTypeInfo2<?> unop2Not = new BooleanUnaryTypeInfo<>("not",
			TypeChecker::createType_expression_Not);

	private final UnaryTypeInfo2<?>[] unaryTypeInformations2 = new UnaryTypeInfo2[] {
			unop2Same,
			unop2Opposite,
			unop2Not
	};

	private static abstract class AbstractBinaryTypeInfo<P extends Type_expression_node> extends StringBasedBinaryTypeInfo<P> {
		private final DecaFunction<Environment,
		Expression, DataType, Type_expression, Subtype,
		Expression, DataType, Type_expression, Subtype,
		DataType, P> prover;
			
		public AbstractBinaryTypeInfo(String operator, DecaFunction<Environment, Expression, DataType, Type_expression, Subtype, Expression, DataType, Type_expression, Subtype, DataType, P> prover) {
			super(operator);
			this.prover = prover;
		}

		@Override
		public P prove(Environment gamma, BinaryExpression e, Type_expression pLeft, DataType tLeft, Type_expression pRight, DataType tRight, DataType r) {
			return prover.apply(gamma, e.getLeft(), tLeft, pLeft, createSubtype_refl(tLeft),
					e.getRight(), tRight, pRight, createSubtype_refl(tRight), r);
		}
	}
	
	private class SynthetizingBinaryTypeInfo<P extends Type_expression_node> extends AbstractBinaryTypeInfo<P> {
		private final TriFunction<BinaryExpression, DataType, DataType, Optional<DataType>> solver;
		
		public SynthetizingBinaryTypeInfo(String operator,
				DecaFunction<Environment, Expression, DataType, Type_expression, Subtype, Expression, DataType, Type_expression, Subtype, DataType, P> prover,
				TriFunction<BinaryExpression, DataType, DataType, Optional<DataType>> solver) {
			super(operator, prover);
			this.solver = solver;
		}
		
		@Override
		public Optional<DataType> immediateType(BinaryExpression e, DataType left, DataType right) {
			Collection<TypeVariable> vars = Stream.of(left, right)
					.flatMap(TypeInferenceSolver::streamVariables)
					.collect(Collectors.toCollection(ConcurrentLinkedDeque::new));
			if(vars.isEmpty()) {
				return solver.apply(e, left, right);
			} else {
				TypeVariable v = inference.createFreshTypeVariable((lb,ub) -> solver.apply(e, getSubstitute(left), getSubstitute(right)), e, null);
				vars.forEach((x) -> inference.addDependency(v, x));
				return Optional.of(v);
			}
		}
	}
	
	private class CmpBinaryTypeInfo<P extends Type_expression_node> extends SynthetizingBinaryTypeInfo<Type_expression_node> {
		public CmpBinaryTypeInfo(String operator, TreDecaFunction<Environment, Expression, DataType, Expression, Expression, Expression, DataType, Expression, Expression, Type_expression, Subtype, Type_expression, Subtype, Type_expression_node> constructor, TriFunction<BinaryExpression, DataType, DataType, Optional<DataType>> solver) {
			super(operator,
					(g,l,lt,lp,ls,r,rt,rp,rs,dr) -> constructor.apply(g,
							l, lt, ((RangeType)lt).getVmin(), ((RangeType)lt).getVmax(),
							r, rt, ((RangeType)rt).getVmin(), ((RangeType)rt).getVmax(),
							lp, ls, rp, rs),
					solver
					);
		}
	}

	private class BooleanBinaryTypeInfo<P extends Type_expression_node> extends AbstractBinaryTypeInfo<P> {
		public BooleanBinaryTypeInfo(String operator, DecaFunction<Environment, Expression, DataType, Type_expression, Subtype, Expression, DataType, Type_expression, Subtype, DataType, P> prover) {
			super(operator, prover);
		}

		@Override
		public Optional<DataType> immediateType(BinaryExpression e, DataType left, DataType right) {
			inference.addConstraint(left, createBooleanType(), e, SosADLPackage.Literals.BINARY_EXPRESSION__LEFT);
			inference.addConstraint(right, createBooleanType(), e, SosADLPackage.Literals.BINARY_EXPRESSION__RIGHT);
			return Optional.of(TypeChecker.createBooleanType());
		}
	}

	private static Optional<DataType> binopSolverAdd(BinaryExpression e, DataType l, DataType r) {
		if(l instanceof RangeType) {
			if(r instanceof RangeType) {
				return Optional.of(createRangeType(
						createBinaryExpression(((RangeType)l).getVmin(), "+", ((RangeType)r).getVmin()),
						createBinaryExpression(((RangeType)l).getVmax(), "+", ((RangeType)r).getVmax())));
			} else {
				return Optional.empty();
			}
		} else {
			return Optional.empty();
		}
	}
	
	private final BinaryTypeInfo2<?> binop2Add = new SynthetizingBinaryTypeInfo<>("+",
				(g, le, lt, lp, ls, re, rt, rp, rs, r) ->
					createType_expression_Add(g, le, lt, ((RangeType)lt).getVmin(), ((RangeType)lt).getVmax(),
							re, rt, ((RangeType)rt).getVmin(), ((RangeType)rt).getVmax(),
							lp, ls, rp, rs),
				TypeChecker::binopSolverAdd);

	private static Optional<DataType> binopSolverSub(BinaryExpression e, DataType l, DataType r) {
		if(l instanceof RangeType) {
			if(r instanceof RangeType) {
				return Optional.of(createRangeType(
						createBinaryExpression(((RangeType)l).getVmin(), "-", ((RangeType)r).getVmax()),
						createBinaryExpression(((RangeType)l).getVmax(), "-", ((RangeType)r).getVmin())));
			} else {
				return Optional.empty();
			}
		} else {
			return Optional.empty();
		}
	}
	
	private final BinaryTypeInfo2<?> binop2Sub = new SynthetizingBinaryTypeInfo<>("-",
			(g, le, lt, lp, ls, re, rt, rp, rs, r) ->
				createType_expression_Sub(g, le, lt, ((RangeType)lt).getVmin(), ((RangeType)lt).getVmax(),
						re, rt, ((RangeType)rt).getVmin(), ((RangeType)rt).getVmax(),
						lp, ls, rp, rs),
			TypeChecker::binopSolverSub);

	private Type_expression_node binopProverMul(Environment g, Expression le, DataType ldt, Type_expression lp,
			Subtype ls, Expression re, DataType rdt, Type_expression rp, Subtype rs, DataType rd) {
		RangeType lt = (RangeType) ldt;
		RangeType rt = (RangeType) rdt;
		RangeType r = (RangeType) rd;
		Expression c1 = createBinaryExpression(lt.getVmin(), "*", rt.getVmin());
		Expression c2 = createBinaryExpression(lt.getVmin(), "*", rt.getVmax());
		Expression c3 = createBinaryExpression(lt.getVmax(), "*", rt.getVmin());
		Expression c4 = createBinaryExpression(lt.getVmax(), "*", rt.getVmax());
		return createType_expression_Mul(g,
				le, lt, lt.getVmin(), lt.getVmax(),
				re, rt, rt.getVmin(), rt.getVmax(),
				r.getVmin(), r.getVmax(), lp, ls, rp, rs,
				expression_le(r.getVmin(), c1),
				expression_le(r.getVmin(), c2),
				expression_le(r.getVmin(), c3),
				expression_le(r.getVmin(), c4),
				expression_le(c1, r.getVmax()),
				expression_le(c2, r.getVmax()),
				expression_le(c3, r.getVmax()),
				expression_le(c4, r.getVmax()));
	}

	private static Optional<DataType> binopSolverMul(BinaryExpression e, DataType ldt, DataType rdt) {
		if(ldt instanceof RangeType) {
			if(rdt instanceof RangeType) {
				RangeType lt = (RangeType) ldt;
				RangeType rt = (RangeType) rdt;
				Expression c1 = createBinaryExpression(lt.getVmin(), "*", rt.getVmin());
				Expression c2 = createBinaryExpression(lt.getVmin(), "*", rt.getVmax());
				Expression c3 = createBinaryExpression(lt.getVmax(), "*", rt.getVmin());
				Expression c4 = createBinaryExpression(lt.getVmax(), "*", rt.getVmax());
				Expression mi = min(min(c1, c2), min(c3, c4));
				Expression ma = max(max(c1, c2), max(c3, c4));
				return Optional.of(createRangeType(mi, ma));
			} else {
				return Optional.empty();
			}
		} else {
			return Optional.empty();
		}
	}

	private final BinaryTypeInfo2<?> binop2Mul = new SynthetizingBinaryTypeInfo<>("*",
			this::binopProverMul,
			TypeChecker::binopSolverMul);

	private Type_expression_node binopProverDiv(Environment g, Expression le, DataType dlt, Type_expression lp,
			Subtype ls, Expression re, DataType drt, Type_expression rp, Subtype rs, DataType dr) {
		RangeType lt = (RangeType) dlt;
		RangeType rt = (RangeType) drt;
		RangeType r = (RangeType) dr;
		if(isLe(createIntegerValue(1), rt.getVmin())) {
			Expression c1 = createBinaryExpression(lt.getVmin(), "/", rt.getVmin());
			Expression c2 = createBinaryExpression(lt.getVmin(), "/", rt.getVmax());
			Expression c3 = createBinaryExpression(lt.getVmax(), "/", rt.getVmin());
			Expression c4 = createBinaryExpression(lt.getVmax(), "/", rt.getVmax());
			return createType_expression_Div_pos(g,
					le, lt, lt.getVmin(), lt.getVmax(),
					re, rt, rt.getVmin(), rt.getVmax(),
					r.getVmin(), r.getVmax(), lp, ls, rp, rs,
					expression_le(createIntegerValue(1), rt.getVmin()),
					expression_le(r.getVmin(), c1),
					expression_le(r.getVmin(), c2),
					expression_le(r.getVmin(), c3),
					expression_le(r.getVmin(), c4),
					expression_le(c1, r.getVmax()),
					expression_le(c2, r.getVmax()),
					expression_le(c3, r.getVmax()),
					expression_le(c4, r.getVmax()));
		} else if (isLe(rt.getVmax(), createOpposite(createIntegerValue(1)))) {
			Expression c1 = createBinaryExpression(lt.getVmin(), "/", rt.getVmin());
			Expression c2 = createBinaryExpression(lt.getVmin(), "/", rt.getVmax());
			Expression c3 = createBinaryExpression(lt.getVmax(), "/", rt.getVmin());
			Expression c4 = createBinaryExpression(lt.getVmax(), "/", rt.getVmax());
			return createType_expression_Div_neg(g,
					le, lt, lt.getVmin(), lt.getVmax(),
					re, rt, rt.getVmin(), rt.getVmax(),
					r.getVmin(), r.getVmax(), lp, ls, rp, rs,
					expression_le(rt.getVmax(), createOpposite(createIntegerValue(1))),
					expression_le(r.getVmin(), c1),
					expression_le(r.getVmin(), c2),
					expression_le(r.getVmin(), c3),
					expression_le(r.getVmin(), c4),
					expression_le(c1, r.getVmax()),
					expression_le(c2, r.getVmax()),
					expression_le(c3, r.getVmax()),
					expression_le(c4, r.getVmax()));
		} else {
			error("The divisor must be different from 0", re, null);
			return null;
		}
	}

	private Optional<DataType> binopSolverDiv(BinaryExpression e, DataType l, DataType r) {
		if(l instanceof RangeType) {
			if(r instanceof RangeType) {
				RangeType lt = (RangeType) l;
				RangeType rt = (RangeType) r;
				if(isLe(createIntegerValue(1), rt.getVmin()) || isLe(rt.getVmax(), createOpposite(createIntegerValue(1)))) {
					Expression c1 = createBinaryExpression(lt.getVmin(), "/", rt.getVmin());
					Expression c2 = createBinaryExpression(lt.getVmin(), "/", rt.getVmax());
					Expression c3 = createBinaryExpression(lt.getVmax(), "/", rt.getVmin());
					Expression c4 = createBinaryExpression(lt.getVmax(), "/", rt.getVmax());
					Expression mi = min(min(c1, c2), min(c3, c4));
					Expression ma = max(max(c1, c2), max(c3, c4));
					return Optional.of(createRangeType(mi, ma));
				} else {
					//error("The divisor must be different from 0", e.getRight(), null);
					return Optional.empty();
				}
			} else {
				return Optional.empty();
			}
		} else {
			return Optional.empty();
		}
	}

	private final BinaryTypeInfo2<?> binop2Div = new SynthetizingBinaryTypeInfo<>("/",
			this::binopProverDiv,
			this::binopSolverDiv);

	private Type_expression_node binopProverMod(Environment g, Expression le, DataType dlt, Type_expression lp,
			Subtype ls, Expression re, DataType drt, Type_expression rp, Subtype rs, DataType dr) {
		RangeType lt = (RangeType) dlt;
		RangeType rt = (RangeType) drt;
		RangeType r = (RangeType) dr;
		Range_modulo_min min = range_modulo_min(
				lt.getVmin(), lt.getVmax(),
				rt.getVmin(), rt.getVmax(),
				() -> createRange_modulo_min_pos(lt.getVmin(), lt.getVmax(),
						rt.getVmin(), rt.getVmax(),
						r.getVmin(),
						expression_le(createIntegerValue(1), rt.getVmin()),
						expression_le(r.getVmin(), createBinaryExpression(createIntegerValue(1), "-", rt.getVmax()))),
				() -> createRange_modulo_min_zero(lt.getVmin(), lt.getVmax(),
						rt.getVmin(), rt.getVmax(),
						r.getVmin(),
						expression_le(createIntegerValue(0), lt.getVmin()),
						expression_le(r.getVmin(), createIntegerValue(0))),
				() -> createRange_modulo_min_neg(lt.getVmin(), lt.getVmax(),
						rt.getVmin(), rt.getVmax(),
						r.getVmin(),
						expression_le(rt.getVmax(), createOpposite(createIntegerValue(1))),
						expression_le(r.getVmin(), createBinaryExpression(rt.getVmin(), "+", createIntegerValue(1)))),
				() -> { error("The divisor must be different from 0", re, null); return null; });
		if(min != null) {
			Range_modulo_max max = range_modulo_max(
					lt.getVmin(), lt.getVmax(),
					rt.getVmin(), rt.getVmax(),
					() -> createRange_modulo_max_pos(lt.getVmin(), lt.getVmax(),
							rt.getVmin(), rt.getVmax(),
							r.getVmax(),
							expression_le(createIntegerValue(1), rt.getVmin()),
							expression_le(createBinaryExpression(rt.getVmax(), "-", createIntegerValue(1)), r.getVmax())),
					() -> createRange_modulo_max_zero(lt.getVmin(), lt.getVmax(),
							rt.getVmin(), rt.getVmax(),
							r.getVmax(),
							expression_le(lt.getVmax(), createIntegerValue(0)),
							expression_le(createIntegerValue(0), r.getVmax())),
					() -> createRange_modulo_max_neg(lt.getVmin(), lt.getVmax(),
							rt.getVmin(), rt.getVmax(),
							r.getVmax(),
							expression_le(rt.getVmax(), createOpposite(createIntegerValue(1))),
							expression_le(createBinaryExpression(createOpposite(createIntegerValue(1)), "-", rt.getVmin()), r.getVmax())),
					() -> { error("The divisor must be different from 0", re, null); return null; });
			if(max != null) {
				return createType_expression_Mod(g,
						le, lt, lt.getVmin(), lt.getVmax(),
						re, rt, rt.getVmin(), rt.getVmax(),
						r.getVmin(), r.getVmax(),
						lp, ls, rp, rs, min, max);
			} else {
				return null;
			}
		} else {
			return null;
		}
	}

	private Optional<DataType> binopSolverMod(BinaryExpression e, DataType l, DataType r) {
		if(l instanceof RangeType) {
			if(r instanceof RangeType) {
				RangeType lt = (RangeType) l;
				RangeType rt = (RangeType) r;
				Expression min = range_modulo_min(
						lt.getVmin(), lt.getVmax(),
						rt.getVmin(), rt.getVmax(),
						() -> createBinaryExpression(createIntegerValue(1), "-", rt.getVmax()),
						() -> createIntegerValue(0),
						() -> createBinaryExpression(rt.getVmin(), "+", createIntegerValue(1)),
						() -> { error("The divisor must be different from 0", e.getRight(), null); return null; });
				if(min != null) {
					Expression max = range_modulo_max(
							lt.getVmin(), lt.getVmax(),
							rt.getVmin(), rt.getVmax(),
							() -> createBinaryExpression(rt.getVmax(), "-", createIntegerValue(1)),
							() -> createIntegerValue(0),
							() -> createBinaryExpression(createOpposite(createIntegerValue(1)), "-", rt.getVmin()),
							() -> { error("The divisor must be different from 0", e.getRight(), null); return null; });
					if(max != null) {
						return Optional.of(createRangeType(min, max));
					} else {
						error("Cannot infer the upper-bound of the range", e, null);
						return Optional.empty();
					}
				} else {
					error("Cannot infer the lower-bound of the range", e, null);
					return Optional.empty();
				}
			} else {
				error("The right-hand operator of `mod' must be a range type, found " + TypeInferenceSolver.typeToString(r), e, SosADLPackage.Literals.BINARY_EXPRESSION__RIGHT);
				return Optional.empty();
			}
		} else {
			error("The left-hand operator of `mod' must be a range type, found " + TypeInferenceSolver.typeToString(l), e, SosADLPackage.Literals.BINARY_EXPRESSION__LEFT);
			return Optional.empty();
		}
	}

	private final BinaryTypeInfo2<?> binop2Mod = new SynthetizingBinaryTypeInfo<>("mod",
			this::binopProverMod,
			this::binopSolverMod);

	private final BinaryTypeInfo2<?> binop2Implies =
			new BooleanBinaryTypeInfo<Type_expression_node>("implies",
					(g,l,lt,lp,ls,r,rt,rp,rs,t) -> TypeChecker.createType_expression_Implies(g, l, lt, r, rt, lp, ls, rp, rs));
	private final BinaryTypeInfo2<?> binop2Or =
			new BooleanBinaryTypeInfo<Type_expression_node>("or",
					(g,l,lt,lp,ls,r,rt,rp,rs,t) -> TypeChecker.createType_expression_Or(g, l, lt, r, rt, lp, ls, rp, rs));
	private final BinaryTypeInfo2<?> binop2Xor =
			new BooleanBinaryTypeInfo<Type_expression_node>("xor",
					(g,l,lt,lp,ls,r,rt,rp,rs,t) -> TypeChecker.createType_expression_Xor(g, l, lt, r, rt, lp, ls, rp, rs));
	private final BinaryTypeInfo2<?> binop2And =
			new BooleanBinaryTypeInfo<Type_expression_node>("and",
					(g,l,lt,lp,ls,r,rt,rp,rs,t) -> TypeChecker.createType_expression_And(g, l, lt, r, rt, lp, ls, rp, rs));
			
	private static Optional<DataType> binopSolverCmp(BinaryExpression e, DataType l, DataType r) {
		if(l instanceof RangeType) {
			if(r instanceof RangeType) {
				return Optional.of(createBooleanType());
			} else {
				return Optional.empty();
			}
		} else {
			return Optional.empty();
		}
	}

	private final BinaryTypeInfo2<?> binop2Equal = new CmpBinaryTypeInfo<>("=", TypeChecker::createType_expression_Equal, TypeChecker::binopSolverCmp);
	private final BinaryTypeInfo2<?> binop2Diff = new CmpBinaryTypeInfo<>("<>", TypeChecker::createType_expression_Diff, TypeChecker::binopSolverCmp);
	private final BinaryTypeInfo2<?> binop2Lt = new CmpBinaryTypeInfo<>("<", TypeChecker::createType_expression_Lt, TypeChecker::binopSolverCmp);
	private final BinaryTypeInfo2<?> binop2Le = new CmpBinaryTypeInfo<>("<=", TypeChecker::createType_expression_Le, TypeChecker::binopSolverCmp);
	private final BinaryTypeInfo2<?> binop2Gt = new CmpBinaryTypeInfo<>(">", TypeChecker::createType_expression_Gt, TypeChecker::binopSolverCmp);
	private final BinaryTypeInfo2<?> binop2Ge = new CmpBinaryTypeInfo<>(">=", TypeChecker::createType_expression_Ge, TypeChecker::binopSolverCmp);

	private final BinaryTypeInfo2<?>[] binaryTypeInformations2 = new BinaryTypeInfo2[] {
			binop2Add,
			binop2Sub,
			binop2Mul,
			binop2Div,
			binop2Mod,
			binop2Implies,
			binop2Or,
			binop2Xor,
			binop2And,
			binop2Equal,
			binop2Diff,
			binop2Lt,
			binop2Le,
			binop2Gt,
			binop2Ge
	};

	private Pair<Type_expression, DataType> type_expression(Environment gamma, Expression e) {
		saveEnvironment(e, gamma);
		Pair<Type_expression_node, DataType> p1 = type_expression_node(gamma, e);
		Type_expression_node ten = p1.getA();
		DataType t = p1.getB();
		if(ten != null && t != null) {
			saveProof(e, ten);
			saveType(e, t);
			return new Pair<>(proofTerm(t, Type_expression.class,
					(a) -> createType_expression_and_type(gamma, e, a, ten, check_datatype(a))), t);
		} else {
			return new Pair<>(null, null);
		}
	}
	
	private Check_datatype check_datatype(DataType t) {
		if(t instanceof NamedType) {
			NamedType n = (NamedType) t;
			if(n.getName() != null) {
				return createCheck_NamedType(n.getName());
			} else {
				error("The named type must have a name", t, null);
				return null;
			}
		} else if(t instanceof TupleType) {
			TupleType tt = (TupleType) t;
			if(noDuplicate(tt.getFields().stream().map(FieldDecl::getName))) {
				return createCheck_TupleType(tt.getFields(), createReflexivity(),
						proveForall(tt.getFields(), (f) -> createEx_intro(f.getType(), createConj(createReflexivity(), check_datatype(f.getType())))));
			} else {
				errorFieldClash(tt);
				return null;
			}
		} else if(t instanceof SequenceType) {
			SequenceType s = (SequenceType) t;
			if(s.getType() != null) {
				return createCheck_SequenceType(s.getType(), check_datatype(s.getType()));
			} else {
				error("The sequence type must have a base type", t, null);
				return null;
			}
		} else if(t instanceof RangeType) {
			RangeType r = (RangeType) t;
			if(r.getVmin() != null && r.getVmax() != null) {
				if(isLe(r.getVmin(), r.getVmax())) {
					return createCheck_RangeType_trivial(r.getVmin(), r.getVmax(), expression_le(r.getVmin(), r.getVmax()));
				} else {
					error("The lower bound must be smaller than or equal to the upper bound", t, null);
					return null;
				}
			} else {
				if(r.getVmin() == null) {
					error("The range type must have a lower bound", t, null);
				}
				if(r.getVmax() == null) {
					error("The range type must have an upper bound", t, null);
				}
				return null;
			}
		} else if(t instanceof BooleanType) {
			return createCheck_BooleanType();
		} else {
			error("Unknown type", t, null);
			return null;
		}
	}

	private void errorFieldClash(TupleType tt) {
		tt.getFields().stream().filter((p) -> tt.getFields().stream().map(FieldDecl::getName).filter((x) -> x.equals(p.getName())).count() >= 2)
		.forEach((f) -> error("Multiple definitions of field `" + f.getName() + "'", f, null));
	}

	private Pair<Type_expression_node, DataType> type_expression_node(Environment gamma, Expression e) {
		saveEnvironment(e, gamma);
		if(e instanceof IntegerValue) {
			return type_expression_node_IntegerValue(gamma, (IntegerValue) e);
		} else if(e instanceof UnaryExpression) {
			return type_expression_node_UnaryExpression(gamma, (UnaryExpression) e);
		} else if(e instanceof BinaryExpression) {
			return type_expression_node_BinaryExpression(gamma, (BinaryExpression) e);
		} else if (e instanceof IdentExpression) {
			return type_expression_node_IdentExpression(gamma, (IdentExpression)e);
		} else if(e instanceof MethodCall) {
			return type_expression_node_MethodCall(gamma, (MethodCall) e);
		} else if(e instanceof Tuple) {
			return type_expression_node_Tuple(gamma, (Tuple)e);
		} else if(e instanceof Sequence) {
			return type_expression_node_Sequence(gamma, (Sequence) e);
		} else if(e instanceof org.archware.sosadl.sosADL.Field) {
			return type_expression_node_Field(gamma, (org.archware.sosadl.sosADL.Field)e);
		} else {
			error("Type error", e, null);
			return new Pair<>(null, null);
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_Field(Environment gamma, org.archware.sosadl.sosADL.Field f) {
		if(f.getField() != null && f.getObject() != null) {
			Pair<Type_expression, DataType> p1 = type_expression(gamma, f.getObject());
			if(p1.getA() != null && p1.getB() != null) {
				TypeVariable v = createFreshTypeVariable(f, SosADLPackage.Literals.FIELD__FIELD,
						(lb,ub) -> chooseBetweenOrElse(lb, ub, Optional.of(createBooleanType())));
				TupleType t = createTupleType(Stream.of(createFieldDecl(f.getField(), v)));
				inference.addConstraint(p1.getB(), t, f, SosADLPackage.Literals.FIELD__FIELD);
				return new Pair<>(saveProof(f,
						proofTerm(v, Type_expression_node.class,
								(x) -> createType_expression_Field(gamma,
											f.getObject(), 
											ECollections.asEList(((TupleType)p1.getB()).getFields().stream()
													.map(this::deepSubstitute).collect(Collectors.toList())),
											f.getField(), x,
											p1.getA(),
											createReflexivity()))), v);
			} else {
				return new Pair<>(null, null);
			}
		} else {
			if(f.getField() == null) {
				error("A field name must be provided", f, SosADLPackage.Literals.FIELD__FIELD);
			}
			if(f.getObject() == null) {
				error("An object expression must be provided", f, SosADLPackage.Literals.FIELD__OBJECT);
			}
			return new Pair<>(null, null);
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_Sequence(Environment gamma, Sequence s) {
		if(s.getElements() == null) {
			error("A sequence must have a list of items", s, null);
			return new Pair<>(null, null);
		} else if(s.getElements().stream().anyMatch((x) -> x == null)) {
			error("All the items of the sequence must be present", s, SosADLPackage.Literals.SEQUENCE__ELEMENTS);
			return new Pair<>(null, null);
		} else {
			List<Pair<Expression, Pair<Type_expression, DataType>>> elts =
					s.getElements().stream().map((x) -> new Pair<>(x, type_expression(gamma, x))).collect(Collectors.toList());
			if(elts.stream().allMatch((x) -> x.getB() != null && x.getB().getA() != null && x.getB().getB() != null)) {
				TypeVariable v = createFreshTypeVariable(s, SosADLPackage.Literals.SEQUENCE__ELEMENTS,
						(lb,ub) -> chooseBetweenOrElse(lb, ub, Optional.of(createBooleanType())));
				elts.forEach((p) -> inference.addConstraint(p.getB().getB(), v, p.getA()));
				DataType t = createSequenceType(v);
				return new Pair<>(saveProof(s,
						proofTerm(t, Type_expression_node.class,
								(x) -> {
									Forall<Expression, Ex<DataType, And<Type_expression, Subtype>>> p1 =
											proveForall(elts, Pair::getA,
											(p) -> {
												DataType pbb = deepSubstitute(p.getB().getB());
												return createEx_intro(pbb,
														createConj(p.getB().getA(),
																subtype(pbb, ((SequenceType)x).getType(), p.getA(), null).orElse(null)));
											});
									return createType_expression_Sequence(gamma, s.getElements(), ((SequenceType)x).getType(), p1);
								})), t);
			} else {
				return new Pair<>(null, null);
			}
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_Tuple(Environment gamma, Tuple t) {
		if(t.getElements() == null) {
			error("A tuple must have a list of elements", t, null);
			return new Pair<>(null, null);
		} else if(t.getElements().stream().anyMatch((x) -> x == null)) {
			error("All the elements of the tuple must be present", t, SosADLPackage.Literals.TUPLE__ELEMENTS);
			return new Pair<>(null, null);
		} else {
			if(noDuplicate(t.getElements().stream().map((f) -> f.getLabel()))) {
				Collection<Pair<TupleElement, Pair<Type_expression, DataType>>> elts =
						t.getElements().stream().map((f) -> new Pair<>(f, type_expression(gamma, f.getValue())))
						.collect(Collectors.toCollection(ConcurrentLinkedQueue::new));
				if(elts.stream().allMatch((p) -> p.getB().getA() != null && p.getB().getB() != null)) {
					List<Pair<TupleElement, Pair<Type_expression, FieldDecl>>> elts2 =
							elts.stream().map((f) -> new Pair<>(f.getA(),
									new Pair<>(f.getB().getA(), createFieldDecl(f.getA().getLabel(), f.getB().getB()))))
							.collect(Collectors.toList());
					TupleType tt = createTupleType(elts2.stream().map((f) -> f.getB().getB()));
					return new Pair<>(saveProof(t,
							proofTerm(tt, Type_expression_node.class,
									(z) -> {
										Forall2<TupleElement, FieldDecl, Ex<Expression, And<Equality,Ex<DataType,And<Equality,Type_expression>>>>> p3 =
												proveForall2(elts2,
													(x) -> x.getA(),
													(x) -> getSubstitute(x.getB().getB()),
													(x) -> createEx_intro(x.getA().getValue(),
															createConj(createReflexivity(),
																	createEx_intro(getSubstitute(x.getB().getB().getType()),
																			createConj(createReflexivity(), x.getB().getA())))));
										return createType_expression_Tuple(gamma, t.getElements(),
												((TupleType)z).getFields(),
												createReflexivity(),
												proveForall2(t.getElements(), ((TupleType)z).getFields(),
														(x,y) -> createReflexivity()),
												p3);
									})),
							saveType(t, tt));
				} else {
					return new Pair<>(null, null);
				}
			} else {
				t.getElements().stream().filter((p) -> t.getElements().stream().map((x) -> x.getLabel())
						.filter((n) -> n.equals(p.getLabel())).count() >= 2)
				.forEach((f) -> error("Multiple fields named `" + f.getLabel() + "'", f, null));
				return new Pair<>(null, null);
			}
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_MethodCall(Environment gamma, MethodCall mc) {
		if (mc.getMethod() != null) {
			Pair<Type_expression, DataType> self = type_expression(gamma, mc.getObject());
			List<Pair<Expression,Pair<Type_expression, DataType>>> params = ListExtensions.map(mc.getParameters(), (p) -> new Pair<>(p, type_expression(gamma, p)));
			if(self.getA() != null && params.stream().allMatch((p) -> p.getA() != null && p.getB() != null)) {
				Stream<IntPair<TypeEnvContent>> indexedTypes = 
						StreamUtils.indexed(gamma.stream())
					.flatMap((i) -> {
						if (i.getB() instanceof TypeEnvContent) {
							return Stream.of(new IntPair<>(i.getA(), (TypeEnvContent)i.getB()));
						} else {
							return Stream.empty();
						}
					});
				Stream<IntPair<TypeEnvContent>> compatibleIndexedTypes = 
						indexedTypes
						.filter((i) -> isSubtype(self.getB(),
								createNamedType(i.getB().getDataTypeDecl().getName())));
				Optional<IntPair<Pair<TypeEnvContent,IntPair<FunctionDecl>>>> method =
						compatibleIndexedTypes
						.flatMap((i) -> StreamUtils.indexed(i.getB().getMethods().stream())
								.filter((m) -> m.getB().getName().equals(mc.getMethod()))
								.filter((m) -> params.size() == m.getB().getParameters().size())
								.filter((m) -> StreamUtils.zip(params.stream().map(Pair::getB), m.getB().getParameters().stream())
										.allMatch((p) -> isSubtype(p.getA().getB(), p.getB().getType())))
								.map((m) -> new IntPair<>(i.getA(), new Pair<>(i.getB(), m))))
						.findFirst();
				if(method.isPresent()) {
					IntPair<Pair<TypeEnvContent,IntPair<FunctionDecl>>> m = method.get();
					saveBinder(mc, m.getB().getB().getB());
					return new Pair<>(saveProof(mc,createType_expression_MethodCall(gamma, mc.getObject(), self.getB(),
								m.getB().getA().getDataTypeDecl(),
								m.getB().getA().getDataType(),
								m.getB().getB().getB().getData().getType(),
								m.getB().getA().getMethods(),
								mc.getMethod(),
								m.getB().getB().getB().getParameters(),
								m.getB().getB().getB().getType(),
								mc.getParameters(),
								self.getA(),
								createEx_intro(BigInteger.valueOf(m.getA()), createReflexivity()),
								subtype(self.getB(), m.getB().getB().getB().getData().getType(), mc, null).orElse(null),
								createEx_intro(BigInteger.valueOf(m.getB().getB().getA()),
										createConj(createReflexivity(), createConj(createReflexivity(), createConj(createReflexivity(), createReflexivity())))),
								proveForall2(m.getB().getB().getB().getParameters(),
										mc.getParameters(),
										(fp,p) -> {
											Pair<Type_expression, DataType> tp = ListUtils.assoc(params, p);
											return createEx_intro(fp.getType(),
												createConj(createReflexivity(),
														createEx_intro(tp.getB(),
																createConj(tp.getA(),
																		subtype(tp.getB(), fp.getType(), mc, null).orElse(null)))));
											}))),
							saveType(mc, m.getB().getB().getB().getType()));
				} else {
					error("No applicable method named `" + mc.getMethod() + "'", mc, SosADLPackage.Literals.METHOD_CALL__METHOD);
					return new Pair<>(null, null);
				}
			} else {
				return new Pair<>(null, null);
			}
		} else {
			error("A method name must be provided", mc, SosADLPackage.Literals.METHOD_CALL__METHOD);
			return new Pair<>(null, null);
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_IdentExpression(Environment gamma, IdentExpression e) {
		if(e.getIdent() == null) {
			error("The identifier must refer to a name", e, SosADLPackage.Literals.IDENT_EXPRESSION__IDENT);
			return new Pair<>(null, null);
		} else {
			EnvContent ec = gamma.get(e.getIdent());
			if(ec == null) {
				error("The name `" + e.getIdent() + "' is undefined in this context", e, SosADLPackage.Literals.IDENT_EXPRESSION__IDENT);
				return new Pair<>(null, null);
			} else if(!(ec instanceof VariableEnvContent)) {
				error("The name `" + e.getIdent() + "' does not refer to a variable in this context", e, SosADLPackage.Literals.IDENT_EXPRESSION__IDENT);
				return new Pair<>(null, null);
			} else {
				VariableEnvContent vec = (VariableEnvContent)ec;
				DataType t = vec.getType();
				saveBinder(e, vec.getBinder());
				return new Pair<>(saveProof(e, createType_expression_Ident(gamma, e.getIdent(), t, createReflexivity())),
						saveType(e, t));
			}
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_BinaryExpression(Environment gamma,
			BinaryExpression e) {
		if(e.getLeft() == null) {
			error("The binary operator must have a left operand", e, SosADLPackage.Literals.BINARY_EXPRESSION__LEFT);
			return new Pair<>(null, null);
		} else if(e.getOp() == null) {
			error("The binary operator must have an operator", e, SosADLPackage.Literals.BINARY_EXPRESSION__OP);
			return new Pair<>(null, null);
		} else if(e.getRight() == null) {
			error("The binary operator must have a right operand", e, SosADLPackage.Literals.BINARY_EXPRESSION__RIGHT);
			return new Pair<>(null, null);
		} else {
			Pair<Type_expression, DataType> pp1 = type_expression(gamma, e.getLeft());
			Type_expression p1 = pp1.getA();
			DataType t1 = pp1.getB();
			Pair<Type_expression, DataType> pp3 = type_expression(gamma, e.getRight());
			Type_expression p3 = pp3.getA();
			DataType t3 = pp3.getB();
			if(p1 != null && t1 != null && p3 != null && t3 != null) {
				for(BinaryTypeInfo2<?> i : binaryTypeInformations2) {
					if(i.isCandidate(e.getOp(), t1, t3)) {
						Optional<DataType> or = i.immediateType(e, t1, t3);
						if(or.isPresent()) {
							DataType r = or.get();
							return new Pair<>(
									saveProof(e, proofTerm(Type_expression_node.class,
											() -> i.prove(gamma, e, p1, getSubstitute(t1), p3, getSubstitute(t3), getSubstitute(r)),
											t1, r)),
									saveType(e, r));
						}
					}
				}
				error("Unknown unary operator with types " + TypeInferenceSolver.typeToString(t1) + " `" + e.getOp() + "' " + TypeInferenceSolver.typeToString(t3),
						e, SosADLPackage.Literals.BINARY_EXPRESSION__OP);
				return new Pair<>(null, null);
			} else {
				return new Pair<>(null, null);
			}
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_UnaryExpression(Environment gamma, UnaryExpression e) {
		if(e.getRight() == null) {
			error("The unary operator must have a right operand", e, SosADLPackage.Literals.UNARY_EXPRESSION__RIGHT);
			return new Pair<>(null, null);
		} else if(e.getOp() == null) {
			error("The unary expression must have an operator", e, SosADLPackage.Literals.UNARY_EXPRESSION__OP);
			return new Pair<>(null, null);
		} else {
			Pair<Type_expression, DataType> pp1 = type_expression(gamma, e.getRight());
			Type_expression p1 = pp1.getA();
			DataType t1 = pp1.getB();
			if(p1 != null && t1 != null) {
				for(UnaryTypeInfo2<?> i : unaryTypeInformations2) {
					if(i.isCandidate(e.getOp(), t1)) {
						Optional<DataType> or = i.immediateType(e, t1);
						if(or.isPresent()) {
							DataType r = or.get();
							return new Pair<>(
									saveProof(e, proofTerm(Type_expression_node.class,
											() -> i.prove(gamma, e, p1, getSubstitute(t1)),
											t1, r)),
									saveType(e, r));
						}
					}
				}
				error("Unknown unary operator `" + e.getOp() + "' applied to type " + TypeInferenceSolver.typeToString(t1),
						e, SosADLPackage.Literals.UNARY_EXPRESSION__OP);
				return new Pair<>(null, null);
			} else {
				return new Pair<>(null, null);
			}
		}
	}

	private Pair<Type_expression_node, DataType> type_expression_node_IntegerValue(Environment gamma, IntegerValue e) {
		DataType t = createRangeType(e, e);
		return new Pair<>(saveProof(e, createType_expression_IntegerValue(gamma, BigInteger.valueOf(((IntegerValue) e).getAbsInt()))),
				saveType(e, t));
	}
	
	private static Optional<DataType> chooseBetweenOrElse(Optional<DataType> lb, Optional<DataType> ub, Optional<DataType> other) {
		return OptionalUtils.orElse(lb, OptionalUtils.orElse(ub, other));
	}
	
	private DataType pickFromGamma(Environment gamma, DataType t) {
		if(gamma.get(((NamedType)t).getName()) != null
				&& gamma.get(((NamedType)t).getName()) instanceof TypeEnvContent
				&& ((TypeEnvContent)gamma.get(((NamedType)t).getName())).getDataTypeDecl().getName() != null
				&& ((TypeEnvContent)gamma.get(((NamedType)t).getName())).getDataTypeDecl().getName().equals(((NamedType)t).getName())) {
			return ((TypeEnvContent)gamma.get(((NamedType)t).getName())).getDataTypeDecl().getDatatype();
		} else {
			return null;
		}
	}
	
	private DataType interSubType(Environment gamma, DataType t1, DataType t2, EObject objectForError, EStructuralFeature featureForError) {
		if(t1 == null) {
			return t1;
		} else if(t2 == null) {
			return t2;
		} else if(t1 == t2) {
			return t1;
		} else if(t1 instanceof NamedType) {
			if(t2 instanceof NamedType
					&& ((NamedType)t1).getName() != null
					&& ((NamedType)t2).getName() != null
					&& ((NamedType)t1).getName().equals(((NamedType)t2).getName())) {
				return t1;
			} else {
				return interSubType(gamma, pickFromGamma(gamma, t1), t2, objectForError, featureForError);
			}
		} else if(t2 instanceof NamedType) {
			return interSubType(gamma, t1, pickFromGamma(gamma, t2), objectForError, featureForError);
		} else if(t1 instanceof BooleanType && t2 instanceof BooleanType) {
			return t1;
		} else if(t1 instanceof RangeType && t2 instanceof RangeType) {
			RangeType r1 = (RangeType) t1;
			RangeType r2 = (RangeType) t2;
			Expression mi = max(r1.getVmin(), r2.getVmin());
			Expression ma = min(r1.getVmax(), r2.getVmax());
			if(isLe(mi, ma)) {
				return createRangeType(mi, ma);
			} else {
				error("The intersection of ranges " + labelFor(r1) + " and " + labelFor(r2) + " is empty", objectForError, featureForError);
				return null;
			}
		} else if(t1 instanceof TupleType && t2 instanceof TupleType) {
			TupleType tt1 = (TupleType) t1;
			TupleType tt2 = (TupleType) t2;
			Map<String,Pair<Optional<FieldDecl>,Optional<FieldDecl>>> fields = MapUtils.merge(fieldMap(tt1.getFields()), fieldMap(tt2.getFields()));
			return createTupleType(fields.values().stream()
					.map((p) -> intersectFieldDecl(p, gamma, objectForError, featureForError))
					.flatMap(StreamUtils::toStream));
		} else if(t1 instanceof SequenceType && t2 instanceof SequenceType) {
			SequenceType s1 = (SequenceType) t1;
			SequenceType s2 = (SequenceType) t2;
			DataType t = interSubType(gamma, s1.getType(), s2.getType(), objectForError, featureForError);
			if(t != null) {
				return createSequenceType(t);
			} else {
				return null;
			}
		} else {
			error("Incompatible types: " + labelFor(t1) + " and " + labelFor(t2) , objectForError, featureForError);
			return null;
		}
	}
	
	private Optional<FieldDecl> intersectFieldDecl(Pair<Optional<FieldDecl>,Optional<FieldDecl>> p, Environment gamma, EObject objectForError, EStructuralFeature featureForError) {
		return OptionalUtils.mapOrElse(p.getA(),
				(a) -> p.getB().flatMap((b) -> intersectFieldDecl(a, b, gamma, objectForError, featureForError)),
				p.getB());
	}
	
	private Optional<FieldDecl> intersectFieldDecl(FieldDecl a, FieldDecl b, Environment gamma, EObject objectForError, EStructuralFeature featureForError) {
		return Optional.ofNullable(interSubType(gamma, a.getType(), b.getType(), objectForError, featureForError))
				.map((t) -> createFieldDecl(a.getName(), t));
	}
	
	private static Map<String,FieldDecl> fieldMap(Collection<FieldDecl> l) {
		return l.stream().collect(Collectors.toConcurrentMap(FieldDecl::getName, (x) -> x));
	}
	
	private void errorForNamedType(String label, String tofrom, NamedType t, Consumer<String> error) {
		if(t.getName() == null) {
			error.accept("The named type must have a name");
		} else {
			error.accept("The type `" + t.getName() + "' cannot be converted " + tofrom + " a " + label + " because its definition is opaque");
		}
	}

	private Pair<Incrementally<Valuing, Type_valuing>, Environment> type_valuings(Environment gamma,
			EList<Valuing> l) {
		// TODO Auto-generated method stub
		return new Pair<>(null, gamma);
	}

	private Type_system type_system(Environment gamma, SystemDecl systemDecl) {
		saveEnvironment(systemDecl, gamma);
		// type_SystemDecl:
		if(systemDecl.getName() != null && systemDecl.getBehavior() != null) {
			Optional<Pair<Pair<List<FormalParameter>, Environment>, And<Forall2<FormalParameter, FormalParameter, And<Equality, Ex<DataType, And<Equality, Ex<DataType, And<Equality, Type_datatype>>>>>>, Mutually<FormalParameter, True>>>> op1 = type_formalParameters(gamma, systemDecl.getParameters());
			if(op1.isPresent()) {
				Pair<Pair<List<FormalParameter>, Environment>, And<Forall2<FormalParameter, FormalParameter, And<Equality, Ex<DataType, And<Equality, Ex<DataType, And<Equality, Type_datatype>>>>>>, Mutually<FormalParameter, True>>> p1 = op1.get();
				EList<FormalParameter> params2 = ECollections.asEList(p1.getA().getA());
				Environment gamma1 = p1.getA().getB();
				Pair<Incrementally<DataTypeDecl,Type_datatypeDecl>,Environment> p2 = type_datatypeDecls(gamma1, systemDecl.getDatatypes());
				Pair<Incrementally<GateDecl,Simple_increment<GateDecl,Type_gate>>,Environment> p3 = type_gates(p2.getB(), systemDecl.getGates());
				return saveProof(systemDecl,
						createType_SystemDecl(gamma, systemDecl.getName(),
								systemDecl.getParameters(),
								params2,
								gamma1, systemDecl.getDatatypes(),
								p2.getB(), systemDecl.getGates(),
								p3.getB(), systemDecl.getBehavior(),
								systemDecl.getAssertion(),
								p1.getB(), p2.getA(),
								p3.getA(), type_behavior(p3.getB(), systemDecl.getBehavior()),
						proveOptionally(p3.getB(), systemDecl.getAssertion(), this::type_assertion)));
			} else {
				return null;
			}
		} else {
			if(systemDecl.getBehavior() == null) {
				error("The system must have a behavior", systemDecl, null);
			} else if(systemDecl.getName() == null) {
				error("The system must have a name", systemDecl, null);
			} else {
				error("Type error", systemDecl, null);
			}
			return null;
		}
	}

	private Pair<Incrementally<GateDecl, Simple_increment<GateDecl,Type_gate>>, Environment> type_gates(Environment gamma, EList<GateDecl> l) {
		return proveIncrementally(gamma, l, (g,x) -> proveSimpleIncrement(g, x, this::type_gate, "SosADL.SosADL.GateDecl_name", GateDecl::getName, "(fun x => None)", (y) -> null));
	}
	
	private Type_assertion type_assertion(Environment gamma, AssertionDecl a) {
		// TODO Auto-generated method stub
		return null;
	}
	
	private Type_gate type_gate(Environment gamma, GateDecl g) {
		// TODO Auto-generated method stub
		return null;
	}

	private Optional<Pair<
	Pair<List<FormalParameter>, Environment>,
	And<Forall2<FormalParameter,FormalParameter,
			And<Equality,Ex<DataType,And<Equality,Ex<DataType,And<Equality,Type_datatype>>>>>>,
		Mutually<FormalParameter, True>
	>>>
	type_formalParameters(
			Environment gamma, EList<FormalParameter> params) {
		List<Pair<FormalParameter, Pair<DataType, Type_datatype>>> l =
				ListExtensions.map(params, (p) -> new Pair<>(p, type_datatype(gamma, p.getType())));
		if(l.stream().allMatch((p) -> p.getB() != null && p.getB().getA() != null && p.getB().getB() != null)) {
			List<FormalParameter> params2 = ListExtensions.map(l, (p) -> createFormalParameter(p.getA().getName(), p.getB().getA()));
			Forall2<FormalParameter,FormalParameter,
			And<Equality,Ex<DataType,And<Equality,Ex<DataType,And<Equality,Type_datatype>>>>>> p1 =
			proveForall2(l,
					Pair::getA,
					(p) -> createFormalParameter(p.getA().getName(), p.getB().getA()),
					TypeChecker::type_formalParameter);
			Pair<Mutually<FormalParameter, True>, Environment> p2 =
					proveMutually(gamma, params2,
							(g0,p,g1) -> createI(),
							"SosADL.SosADL.FormalParameter_name", FormalParameter::getName,
							"SosADL.TypeSystem.formalParameter_to_EVariable", TypeChecker::formalParameterEnvContent);
			return Optional.of(new Pair<>(new Pair<>(params2, p2.getB()),
					createConj(p1, p2.getA())));
		} else {
			return Optional.empty();
		}
	}
	
	private static And<Equality,Ex<DataType,And<Equality,Ex<DataType,And<Equality,Type_datatype>>>>> type_formalParameter(Pair<FormalParameter, Pair<DataType, Type_datatype>> p) {
		return createConj(createReflexivity(),
				createEx_intro(p.getA().getType(),
						createConj(createReflexivity(),
								createEx_intro(p.getB().getA(),
										createConj(createReflexivity(),
												p.getB().getB())))));
	}
	
	private static EnvContent formalParameterEnvContent(FormalParameter p) {
		DataType t = p.getType();
		if(t == null) {
			return null;
		} else {
			return new VariableEnvContent(p, t);
		}
	}

	private Type_mediator type_mediator(Environment gamma, MediatorDecl mediator) {
		saveEnvironment(mediator, gamma);
		// TODO Auto-generated method stub
		return null;
	}

	private Type_architecture type_architecture(Environment gamma, ArchitectureDecl architecture) {
		saveEnvironment(architecture, gamma);
		// TODO Auto-generated method stub
		return null;
	}
	
	private Expression_le expression_le(Expression l, Expression r) {
		if(isLe(l, r)) {
			return createIn_Z(l, InterpInZ.eval(l), r, InterpInZ.eval(r), createReflexivity(), createReflexivity(), createReflexivity());
		} else {
			if(isConstExprNoError(l) && isConstExprNoError(r)) {
				error("The lower bound must be smaller than the upper bound", l, null);
				error("The upper bound must be greater than the lower bound", r, null);
			} else {
				error("Type error", l, null);
			}
			return null;
		}
	}

	private boolean isLe(Expression l, Expression r) {
		return isConstExprOrError(l) && isConstExprOrError(r) && InterpInZ.le(l, r);
	}

	private Pair<DataType,Type_datatype> type_datatype(Environment gamma, DataType type) {
		saveEnvironment(type, gamma);
		// type_NamedType:
		if(type instanceof NamedType) {
			NamedType n = (NamedType) type;
			if(n.getName() == null) {
				error("The named type must have a name", type, null);
				return new Pair<>(null, null);
			} else {
				EnvContent ec = gamma.get(n.getName());
				if(ec == null) {
					error("No type declaration named `" + gamma.get(n.getName()) + "'", type, null);
					return new Pair<>(null, null);
				} else if(ec instanceof TypeEnvContent) {
					TypeEnvContent tec = (TypeEnvContent) ec;
					saveBinder(type, tec.getDataTypeDecl());
					saveType(type, tec.getDataType());
					return new Pair<>(saveType(type, tec.getDataType()), saveProof(type,
							createType_NamedType(gamma, n.getName(), tec.getDataType(), tec.getDataTypeDecl(),
									createEx_intro(tec.getMethods(), createReflexivity()))));
				} else {
					error("`" + n.getName() + "' is not a type declaration", type, null);
					return new Pair<>(null, null);
				}
			}
		}
		// type_TupleType:
		else if(type instanceof TupleType) {
			TupleType t = (TupleType) type;
			if(noDuplicate(t.getFields().stream().map(FieldDecl::getName))) {
				List<Pair<FieldDecl,Pair<DataType,Type_datatype>>> l = ListExtensions.map(t.getFields(),
						(f) -> new Pair<>(f, type_datatype(gamma, f.getType())));
				if(l.stream().allMatch((p) -> p.getB() != null && p.getB().getA() != null && p.getB().getB() != null)) {
					List<FieldDecl> fields2 = ListExtensions.map(l, (p) -> createFieldDecl(p.getA().getName(), p.getB().getA()));
					TupleType r = createTupleType(fields2);
					return new Pair<>(saveType(type, r),
							saveProof(type,
									createType_TupleType(gamma, t.getFields(), r.getFields(), createReflexivity(),
											proveForall2(l, Pair::getA, (p) -> createFieldDecl(p.getA().getName(), p.getB().getA()),
													(p) -> createConj(createReflexivity(),
															createEx_intro(p.getA().getType(),
																	createConj(createReflexivity(),
																			createEx_intro(p.getB().getA(),
																					createConj(createReflexivity(), p.getB().getB())))))))));
				} else {
					return new Pair<>(null, null);
				}
			} else {
				errorFieldClash(t);
				return new Pair<>(null, null);
			}
		}
		// type_SequenceType:
		else if(type instanceof SequenceType) {
			SequenceType s = (SequenceType) type;
			if(s.getType() != null) {
				Pair<DataType,Type_datatype> r = type_datatype(gamma, s.getType());
				if(r != null && r.getA() != null && r.getB() != null) {
					return new Pair<>(saveType(type, createSequenceType(r.getA())),
							saveProof(type, createType_SequenceType(gamma, s.getType(), r.getA(), r.getB())));
				} else {
					return new Pair<>(null, null);
				}
			} else {
				error("The sequence type must declare a base type", type, null);
				return new Pair<>(null, null);
			}
		}
		// type_RangeType_trivial
		else if(type instanceof RangeType) {
			RangeType r = (RangeType) type;
			if(r.getVmin() != null && r.getVmax() != null) {
				if(isLe(r.getVmin(), r.getVmax())) {
					saveMin(type, InterpInZ.eval(((RangeType)type).getVmin()));
					saveMax(type, InterpInZ.eval(((RangeType)type).getVmax()));
					return new Pair<>(saveType(type, type),
							saveProof(type, createType_RangeType_trivial(gamma, r.getVmin(), r.getVmax(),
									expression_le(r.getVmin(), r.getVmax()))));
				} else {
					error("The lower bound of the range is greater than the upper bound", type, null);
					return new Pair<>(null, null);
				}
			} else {
				if(r.getVmin() == null) {
					error("The range type must have a lower bound", type, null);
				}
				if(r.getVmax() == null) {
					error("The range type must have an upper bound", type, null);
				}
				return new Pair<>(null, null);
			}
		}
		// type_BooleanType:
		else if(type instanceof BooleanType) {
			return new Pair<>(saveType(type, type),
					saveProof(type, createType_BooleanType(gamma)));
		} else {
			error("Type error", type, null);
			return new Pair<>(null, null);
		}
	}

	private boolean isConstExprOrError(Expression e) {
		return isConstExpr(e, this::error);
	}

	private boolean isConstExprNoError(Expression e) {
		return new TypeChecker().isConstExprOrError(e);
	}

	private boolean isConstExpr(Expression e, TriConsumer<String, EObject, EStructuralFeature> trigger) {
		// constexpr_IntegerValue:
		if(e instanceof IntegerValue) {
			return true;
		}
		// constexpr_Opposite:
		else if(e instanceof UnaryExpression && ((UnaryExpression)e).getOp() != null && ((UnaryExpression)e).getOp().equals("-") && ((UnaryExpression)e).getRight() != null) {
			return isConstExpr(((UnaryExpression)e).getRight(), trigger);
		}
		// constexpr_Same:
		else if(e instanceof UnaryExpression && ((UnaryExpression)e).getOp() != null && ((UnaryExpression)e).getOp().equals("+") && ((UnaryExpression)e).getRight() != null) {
			return isConstExpr(((UnaryExpression)e).getRight(), trigger);
		}
		// constexpr_Add:
		else if(e instanceof BinaryExpression && ((BinaryExpression)e).getOp() != null && ((BinaryExpression)e).getOp().equals("+") && ((BinaryExpression)e).getLeft() != null && ((BinaryExpression)e).getRight() != null) {
			return isConstExpr(((BinaryExpression)e).getLeft(), trigger) & isConstExpr(((BinaryExpression)e).getRight(), trigger);
		}
		// constexpr_Sub:
		else if(e instanceof BinaryExpression && ((BinaryExpression)e).getOp() != null && ((BinaryExpression)e).getOp().equals("-") && ((BinaryExpression)e).getLeft() != null && ((BinaryExpression)e).getRight() != null) {
			return isConstExpr(((BinaryExpression)e).getLeft(), trigger) & isConstExpr(((BinaryExpression)e).getRight(), trigger);
		}
		// constexpr_Mul:
		else if(e instanceof BinaryExpression && ((BinaryExpression)e).getOp() != null && ((BinaryExpression)e).getOp().equals("*") && ((BinaryExpression)e).getLeft() != null && ((BinaryExpression)e).getRight() != null) {
			return isConstExpr(((BinaryExpression)e).getLeft(), trigger) & isConstExpr(((BinaryExpression)e).getRight(), trigger);
		}
		// constexpr_Div:
		else if(e instanceof BinaryExpression && ((BinaryExpression)e).getOp() != null && ((BinaryExpression)e).getOp().equals("/") && ((BinaryExpression)e).getLeft() != null && ((BinaryExpression)e).getRight() != null) {
			return isConstExpr(((BinaryExpression)e).getLeft(), trigger) & isConstExpr(((BinaryExpression)e).getRight(), trigger);
		}
		// constexpr_Mod:
		else if(e instanceof BinaryExpression && ((BinaryExpression)e).getOp() != null && ((BinaryExpression)e).getOp().equals("mod") && ((BinaryExpression)e).getLeft() != null && ((BinaryExpression)e).getRight() != null) {
			return isConstExpr(((BinaryExpression)e).getLeft(), trigger) & isConstExpr(((BinaryExpression)e).getRight(), trigger);
		} else {
			return false;
		}
	}

	@SuppressWarnings("unused")
	private Constexpr_expression constexpr_expression(Expression e) {
		// constexpr_IntegerValue:
		if(e instanceof IntegerValue) {
			return saveProof(e, createConstexpr_IntegerValue(BigInteger.valueOf(((IntegerValue) e).getAbsInt())));
		}
		// constexpr_Opposite:
		else if(e instanceof UnaryExpression && ((UnaryExpression)e).getOp() != null && ((UnaryExpression)e).getOp().equals("-") && ((UnaryExpression)e).getRight() != null) {
			return saveProof(e, createConstexpr_Opposite(((UnaryExpression)e).getRight(), constexpr_expression(((UnaryExpression)e).getRight())));
		}
		// constexpr_Same:
		else if(e instanceof UnaryExpression && ((UnaryExpression)e).getOp() != null && ((UnaryExpression)e).getOp().equals("+") && ((UnaryExpression)e).getRight() != null) {
			return saveProof(e, createConstexpr_Same(((UnaryExpression)e).getRight(), constexpr_expression(((UnaryExpression)e).getRight())));
		}
		// constexpr_Add:
		else if(e instanceof BinaryExpression && ((BinaryExpression)e).getOp() != null && ((BinaryExpression)e).getOp().equals("+") && ((BinaryExpression)e).getLeft() != null && ((BinaryExpression)e).getRight() != null) {
			return saveProof(e, createConstexpr_Add(((BinaryExpression)e).getLeft(), ((BinaryExpression)e).getRight(), constexpr_expression(((BinaryExpression)e).getLeft()), constexpr_expression(((BinaryExpression)e).getRight())));
		}
		// constexpr_Sub:
		else if(e instanceof BinaryExpression && ((BinaryExpression)e).getOp() != null && ((BinaryExpression)e).getOp().equals("-") && ((BinaryExpression)e).getLeft() != null && ((BinaryExpression)e).getRight() != null) {
			return saveProof(e, createConstexpr_Sub(((BinaryExpression)e).getLeft(), ((BinaryExpression)e).getRight(), constexpr_expression(((BinaryExpression)e).getLeft()), constexpr_expression(((BinaryExpression)e).getRight())));
		}
		// constexpr_Mul:
		else if(e instanceof BinaryExpression && ((BinaryExpression)e).getOp() != null && ((BinaryExpression)e).getOp().equals("*") && ((BinaryExpression)e).getLeft() != null && ((BinaryExpression)e).getRight() != null) {
			return saveProof(e, createConstexpr_Mul(((BinaryExpression)e).getLeft(), ((BinaryExpression)e).getRight(), constexpr_expression(((BinaryExpression)e).getLeft()), constexpr_expression(((BinaryExpression)e).getRight())));
		}
		// constexpr_Div:
		else if(e instanceof BinaryExpression && ((BinaryExpression)e).getOp() != null && ((BinaryExpression)e).getOp().equals("/") && ((BinaryExpression)e).getLeft() != null && ((BinaryExpression)e).getRight() != null) {
			return saveProof(e, createConstexpr_Div(((BinaryExpression)e).getLeft(), ((BinaryExpression)e).getRight(), constexpr_expression(((BinaryExpression)e).getLeft()), constexpr_expression(((BinaryExpression)e).getRight())));
		}
		// constexpr_Mod:
		else if(e instanceof BinaryExpression && ((BinaryExpression)e).getOp() != null && ((BinaryExpression)e).getOp().equals("mod") && ((BinaryExpression)e).getLeft() != null && ((BinaryExpression)e).getRight() != null) {
			return saveProof(e, createConstexpr_Mod(((BinaryExpression)e).getLeft(), ((BinaryExpression)e).getRight(), constexpr_expression(((BinaryExpression)e).getLeft()), constexpr_expression(((BinaryExpression)e).getRight())));
		} else {
			if(e instanceof BinaryExpression && ((BinaryExpression)e).getOp() != null && ((BinaryExpression)e).getLeft() != null && ((BinaryExpression)e).getRight() != null) {
				error("Invalid binary operator for constant-integer expressions", e, SosADLPackage.Literals.BINARY_EXPRESSION__OP);
			} else if(e instanceof BinaryExpression) {
				error("Missing operator or operand", e, null);
			} else if(e instanceof UnaryExpression && ((UnaryExpression)e).getOp() != null && ((UnaryExpression)e).getRight() != null) {
				error("Invalid unary operator for constant-integer expressions", e, SosADLPackage.Literals.BINARY_EXPRESSION__OP);
			} else if(e instanceof UnaryExpression) {
				error("Missing operator or operand", e, null);
			} else {
				error("This expression is not a constant-integer expression", e, null);
			}
			return null;
		}
	}

	private Type_behavior type_behavior(Environment gamma, BehaviorDecl behaviorDecl) {
		// TODO Auto-generated method stub
		return null;
	}
	
	private static <S, T extends EObject, P extends ProofTerm> Forall<T, P> proveForall(
			List<S> l, Function<S,T> f, Function<S,P> prover) {
		if(l.isEmpty()) {
			return createForall_nil();
		} else {
			return createForall_cons(f.apply(l.get(0)), prover.apply(l.get(0)), proveForall(cdr(l), f, prover));
		}
	}

	private static <T extends EObject, P extends ProofTerm> Forall<T, P> proveForall(
			List<T> l, Function<T,P> prover) {
		return proveForall(l, (x) -> x, prover);
	}
	
	private static <T1 extends EObject, T2 extends EObject, P extends ProofTerm> Forall2<T1,T2,P> proveForall2(
			List<? extends T1> l, List<? extends T2> m, BiFunction<T1, T2, ? extends P> prover) {
		if(l.isEmpty() && m.isEmpty()) {
			return createForall2_nil();
		} else {
			return createForall2_cons(l.get(0), m.get(0), prover.apply(l.get(0), m.get(0)), proveForall2(cdr(l), cdr(m), prover));
		}
	}
	
	private static <T, T1 extends EObject, T2 extends EObject, P extends ProofTerm> Forall2<T1,T2,P> proveForall2(
			List<T> zipped, Function<T, T1> left, Function<T, T2> right, Function<T, P> prover) {
		if(zipped.isEmpty()) {
			return createForall2_nil();
		} else {
			return createForall2_cons(left.apply(zipped.get(0)),
					right.apply(zipped.get(0)),
					prover.apply(zipped.get(0)),
					proveForall2(cdr(zipped), left, right, prover));
		}
	}
	
	private static <T extends EObject, P extends ProofTerm> Pair<Incrementally<T,P>,Environment> proveIncrementally(Environment gamma, List<T> l,
			BiFunction<Environment, T, Pair<P, Environment>> prover) {
		if(l.isEmpty()) {
			return new Pair<>(createIncrementally_nil(gamma), gamma);
		} else {
			Pair<P, Environment> pi = prover.apply(gamma,  l.get(0));
			Environment gammai = pi.getB();
			Pair<Incrementally<T, P>, Environment> pn = proveIncrementally(gammai, cdr(l), prover);
			Environment gamma1 = pn.getB();
			return new Pair<>(createIncrementally_cons(gamma, l.get(0), gammai, cdr(l), gamma1, pi.getA(), pn.getA()), gamma1);
		}
	}
	
	private static <T extends EObject, P extends ProofTerm> Pair<Simple_increment<T,P>,Environment> proveSimpleIncrement(Environment gamma, T x,
			BiFunction<Environment, T, P> prover, String n, Function<T, ? extends String> name, String c, Function<T, ? extends EnvContent> content) {
		Environment gamma1 = augment_env(gamma, name.apply(x), content.apply(x));
		return new Pair<>(createSimple_increment_step(n, c, gamma, x, gamma1, createReflexivity(), prover.apply(gamma, x)), gamma1);
	}

	@SuppressWarnings("unused")
	private <T extends EObject, P extends ProofTerm> Pair<Mutually<T,P>, Environment> proveMutually(Environment gamma, List<T> l,
			TriFunction<Environment, T, Environment, P> prover, Function<T, ? extends String> name, Function<T, ? extends EnvContent> content) {
		if(noDuplicate(l.stream().map(name))) {
			Environment gamma1 = fold_right((x, g) -> augment_env(g, name.apply(x), content.apply(x)), gamma, l);
			return new Pair<>(createMutually_all(gamma, l, gamma1, createReflexivity(), createReflexivity(), proveForall(l, (x) -> prover.apply(gamma,  x,  gamma1))), gamma1);
		} else {
			l.stream().filter((p) -> l.stream().map(name).filter((n) -> n.equals(name.apply(p))).count() >= 2)
			.forEach((f) -> error("Multiple definitions of `" + name.apply(f) + "'", f, null));
			return new Pair<>(null, gamma);
		}
	}

	private <T extends EObject, P extends ProofTerm> Pair<Mutually<T,P>, Environment> proveMutually(Environment gamma, List<T> l,
			TriFunction<Environment, T, Environment, P> prover, String n, Function<T, ? extends String> name,
			String c, Function<T, ? extends EnvContent> content) {
		if(noDuplicate(l.stream().map(name))) {
			Environment gamma1 = fold_right((x, g) -> augment_env(g, name.apply(x), content.apply(x)), gamma, l);
			return new Pair<>(createMutually_all_explicit(n, c, gamma, l, gamma1, createReflexivity(), createReflexivity(), proveForall(l, (x) -> prover.apply(gamma,  x,  gamma1))), gamma1);
		} else {
			l.stream().filter((p) -> l.stream().map(name).filter((x) -> x.equals(name.apply(p))).count() >= 2)
			.forEach((f) -> error("Multiple definitions of `" + name.apply(f) + "'", f, null));
			return new Pair<>(null, gamma);
		}
	}
	
	private <T extends EObject, P extends ProofTerm> Optionally<T, P> proveOptionally(Environment gamma, T x, BiFunction<Environment,T,P> prover) {
		if(x == null) {
			return createOptionally_None(gamma);
		} else {
			return createOptionally_Some(gamma, x, prover.apply(gamma, x));
		}
	}

	public static final String ENVIRONMENT = "Environment";
	public static final String PROOF = "Proof";
	public static final String MIN = "Min";
	public static final String MAX = "Max";
	public static final String TYPE = "Type";
	public static final String BINDER = "Binder";

	public static DataType saveType(EObject eObject, DataType t) {
		AttributeAdapter.adapterOf(eObject).putAttribute(TYPE, t);
		return t;
	}
	
	public static DataType getType(EObject eObject) {
		return (DataType) AttributeAdapter.adapterOf(eObject).getAttribute(TYPE);
	}
	
	public static void saveMin(EObject eObject, Expression e) {
		saveMin(eObject, InterpInZ.eval(e));
	}
		
	public static void saveMin(EObject eObject, BigInteger i) {
		AttributeAdapter.adapterOf(eObject).putAttribute(MIN, i);
	}
	
	public static void saveMax(EObject eObject, Expression e) {
		saveMax(eObject, InterpInZ.eval(e));
	}
	
	public static void saveMax(EObject eObject, BigInteger i) {
		AttributeAdapter.adapterOf(eObject).putAttribute(MAX, i);
	}
	
	public static void saveEnvironment(EObject eObject, Environment env) {
		AttributeAdapter.adapterOf(eObject).putAttribute(ENVIRONMENT, env);
	}
	
	public static <T> T saveProof(EObject eObject, T proof) {
		if(proof == null) { System.out.println("ummm"); }
		AttributeAdapter.adapterOf(eObject).putAttribute(PROOF, proof);
		return proof;
	}

	public static Object getProof(EObject eObject) {
		return AttributeAdapter.adapterOf(eObject).getAttribute(PROOF);
	}
	
	public static void saveBinder(EObject target, EObject binder) {
		AttributeAdapter.adapterOf(target).putAttribute(BINDER, binder);
	}
	
	public static Object getBinder(EObject eObject) {
		return AttributeAdapter.adapterOf(eObject).getAttribute(BINDER);
	}
	
	private static Environment augment_env(Environment gamma, String name, EnvContent content) {
		if(name == null) {
			return gamma;
		} else if(content == null) {
			return gamma;
		} else {
			return gamma.put(name, content);
		}
	}

	private static <T> EList<T> cdr(List<T> l) {
		Iterator<T> i = l.iterator();
		EList<T> ret;
		if(i.hasNext()) {
			i.next();
			ret = ECollections.toEList(i);
		} else {
			ret = ECollections.emptyEList();
		}
		return ECollections.unmodifiableEList(ret);
	}
	
	private static <T> EList<T> cons(T v, List<T> l) {
		List<T> lv = new LinkedList<>();
		lv.add(v);
		EList<T> ret = ECollections.asEList(lv);
		ret.addAll(l);
		return ECollections.unmodifiableEList(ret);
	}
	
	private static <T> EList<T> nil() {
		return ECollections.unmodifiableEList(ECollections.emptyEList());
	}
	
	@SuppressWarnings("unused")
	private static <A,B> A fold_left(BiFunction<A,B,A> f, List<B> l, A i) {
		/*
		if(l.isEmpty()) {
			return i;
		} else {
			return fold_left(f, cdr(l), f.apply(i, l.get(0)));
		}
		*/
		A r = i;
		for(B x:l) {
			r = f.apply(r, x);
		}
		return r;
	}
	
	private static <A,B> A fold_right(BiFunction<B,A,A> f, A i, List<B> l) {
		/*
		if(l.isEmpty()) {
			return i;
		} else {
			return f.apply(l.get(0), fold_right(f, i, cdr(l)));
		}
		*/
		A r = i;
		for(int j = l.size();j > 0;) {
			--j;
			B x = l.get(j);
			r = f.apply(x, r);
		}
		return r;
	}
	
	@SuppressWarnings("unused")
	private static <A,B> B assoc(List<Pair<A,B>> l, A a) {
		for(Pair<A,B> i: l) {
			if(i.getA() == a) {
				return i.getB();
			}
		}
		return null;
	}
	
	private static <A,B> A rassoc(List<Pair<A,B>> l, B b) {
		for(Pair<A,B> i: l) {
			if(i.getB() == b) {
				return i.getA();
			}
		}
		return null;
	}
	
	private static <T> boolean noDuplicate(Stream<T> s) {
		List<T> list = s.filter((p) -> p != null).collect(Collectors.toList());
		Set<T> set = new TreeSet<>(list);
		return list.size() == set.size();
	}
	
	private static Type_sosADL createType_SosADL_file(EList<Import> i, Unit d, Type_unit p) {
		return new Type_SosADL_file(i, d, p);
	}
	
	private static Type_unit createType_SoS(Environment gamma, String n, EntityBlock e, Type_entityBlock p) {
		return new Type_SoS(gamma, n, e, p);
	}
	
	private static Type_unit createType_Library(Environment gamma, String n, EntityBlock e, Type_entityBlock p) {
		return new Type_Library(gamma, n, e, p);
	}
	
	private static Type_entityBlock createType_EntityBlock_whole(Environment gamma, List<DataTypeDecl> datatypes, Environment gamma1,
			List<FunctionDecl> funs, Environment gamma2, List<SystemDecl> systems, Environment gamma3,
			List<MediatorDecl> mediators, Environment gamma4, List<ArchitectureDecl> architectures, Environment gamma5,
			Incrementally<DataTypeDecl,Type_datatypeDecl> p1, Incrementally<FunctionDecl, Type_function> p2,
			Incrementally<SystemDecl,Simple_increment<SystemDecl,Type_system>> p3, Incrementally<MediatorDecl,Simple_increment<MediatorDecl,Type_mediator>> p4,
			Incrementally<ArchitectureDecl, Simple_increment<ArchitectureDecl, Type_architecture>> p5) {
		return new Type_EntityBlock_whole(gamma, datatypes, gamma1, funs, gamma2, systems, gamma3, mediators, gamma4, architectures, gamma5, p1, p2, p3, p4, p5);
	}
	
	private static Type_system createType_SystemDecl(Environment gamma, String name, EList<FormalParameter> params,
			EList<FormalParameter> params2, Environment gamma1, EList<DataTypeDecl> datatypes, Environment gamma2,
			EList<GateDecl> gates, Environment gamma3, BehaviorDecl bhv, AssertionDecl assrt,
			And<Forall2<FormalParameter, FormalParameter, And<Equality, Ex<DataType, And<Equality, Ex<DataType, And<Equality, Type_datatype>>>>>>, Mutually<FormalParameter, True>> p1,
			Incrementally<DataTypeDecl, Type_datatypeDecl> p2,
			Incrementally<GateDecl, Simple_increment<GateDecl, Type_gate>> p3, Type_behavior p4,
			Optionally<AssertionDecl, Type_assertion> p5) {
		return new Type_SystemDecl(gamma, name, params, params2, gamma1, datatypes, gamma2, gates, gamma3, bhv, assrt, p1, p2, p3, p4, p5);
	}
	
	private static Type_datatypeDecl createType_DataTypeDecl_def(Environment gamma, String name, DataType t, DataType t2, EList<FunctionDecl> funs, Environment gamma1, Type_datatype p1, Forall<FunctionDecl,Ex<FormalParameter, And<Equality, Equality>>> p2, Incrementally<FunctionDecl, Type_function> p3) {
		return new Type_DataTypeDecl_def(gamma, name, t, t2, funs, gamma1, p1, p2, p3);
	}
	
	private static Type_datatypeDecl createType_DataTypeDecl_def_None(Environment gamma, String name, String name2, EList<FunctionDecl> funs,
			Environment gamma1, Equality p1, Forall<FunctionDecl, Ex<FormalParameter, And<Equality, Equality>>> p2,
			Incrementally<FunctionDecl, Type_function> p3) {
		return new Type_DataTypeDecl_def_None(gamma, name, name2, funs, gamma1, p1, p2, p3);
	}

	private static Type_datatype createType_NamedType(Environment gamma, String n, DataType u, DataTypeDecl t, Ex<List<FunctionDecl>, Equality> p) {
		return new Type_NamedType(gamma, n, u, t, p);
	}
	
	private static Type_datatype createType_TupleType(Environment gamma, EList<FieldDecl> fields, EList<FieldDecl> fields2, Equality p1,
			Forall2<FieldDecl, FieldDecl, And<Equality, Ex<DataType, And<Equality, Ex<DataType, And<Equality, Type_datatype>>>>>> p2) {
		return new Type_TupleType(gamma, fields, fields2, p1, p2);
	}
	
	private static Type_datatype createType_SequenceType(Environment gamma, DataType t, DataType t2, Type_datatype p) {
		return new Type_SequenceType(gamma, t, t2, p);
	}
	
	private static Type_datatype createType_RangeType_trivial(Environment gamma, Expression min, Expression max, Expression_le p1) {
		return new Type_RangeType_trivial(gamma, min, max, p1);
	}
	
	private static Type_datatype createType_BooleanType(Environment gamma) {
		return new Type_BooleanType(gamma);
	}
	
	private static Type_function createType_FunctionDecl_Method(Environment gamma, String dataName, String dataTypeName, DataTypeDecl dataTypeDecl,
			DataType dataTypeReal, EList<FunctionDecl> dataTypeMethods, String name, EList<FormalParameter> params,
			EList<FormalParameter> params2, Environment gammap, DataType rettype, DataType rettype2,
			EList<Valuing> vals, Environment gammav, Expression retexpr, DataType tau, Environment gamma1, Equality p1,
			Type_datatype p2,
			And<Forall2<FormalParameter, FormalParameter, And<Equality, Ex<DataType, And<Equality, Ex<DataType, And<Equality, Type_datatype>>>>>>, Mutually<FormalParameter, True>> p3,
			Incrementally<Valuing, Type_valuing> p4, Type_expression p5, Subtype p6, Equality p7) {
		return new Type_FunctionDecl_Method(gamma, dataName, dataTypeName, dataTypeDecl, dataTypeReal, dataTypeMethods, name, params, params2, gammap, rettype, rettype2, vals, gammav, retexpr, tau, gamma1, p1, p2, p3, p4, p5, p6, p7);
	}
	
	private static Type_expression_node createType_expression_IntegerValue(Environment gamma, BigInteger v) {
		return new Type_expression_IntegerValue(gamma, v);
	}

	private static Type_expression createType_expression_and_type(Environment gamma, Expression e,
			DataType t, Type_expression_node p1, Check_datatype p2) {
		return new Type_expression_and_type(gamma, e, t, p1, p2);
	}

	private static Expression_le createIn_Z(Expression l, BigInteger zl, Expression r, BigInteger zr, Equality p1, Equality p2, Equality p3) {
		return new In_Z(l, zl, r, zr, p1, p2, p3);
	}
	
	private static Constexpr_expression createConstexpr_IntegerValue(BigInteger v) {
		return new Constexpr_IntegerValue(v);
	}
	
	private static Constexpr_expression createConstexpr_Opposite(Expression e, Constexpr_expression p) {
		return new Constexpr_Opposite(e, p);
	}
	
	private static Constexpr_expression createConstexpr_Same(Expression e, Constexpr_expression p) {
		return new Constexpr_Same(e, p);
	}
	
	private static Constexpr_expression createConstexpr_Add(Expression l, Expression r, Constexpr_expression p1, Constexpr_expression p2) {
		return new Constexpr_Add(l, r, p1, p2);
	}
	
	private static Constexpr_expression createConstexpr_Sub(Expression l, Expression r, Constexpr_expression p1, Constexpr_expression p2) {
		return new Constexpr_Sub(l, r, p1, p2);
	}
	
	private static Constexpr_expression createConstexpr_Mul(Expression l, Expression r, Constexpr_expression p1, Constexpr_expression p2) {
		return new Constexpr_Mul(l, r, p1, p2);
	}
	
	private static Constexpr_expression createConstexpr_Div(Expression l, Expression r, Constexpr_expression p1, Constexpr_expression p2) {
		return new Constexpr_Div(l, r, p1, p2);
	}
	
	private static Constexpr_expression createConstexpr_Mod(Expression l, Expression r, Constexpr_expression p1, Constexpr_expression p2) {
		return new Constexpr_Mod(l, r, p1, p2);
	}
	
	private static <T,P> Incrementally<T,P> createIncrementally_nil(Environment gamma) {
		return new Incrementally_nil<>(gamma);
	}
	
	private static <T,P> Incrementally<T,P> createIncrementally_cons(Environment gamma, T x, Environment gammai, List<T> l, Environment gamma1, P p1, Incrementally<T,P> p2) {
		return new Incrementally_cons<T, P>(gamma, x, gammai, l, gamma1, p1, p2);
	}
	
	private static <T, P> Simple_increment<T,P> createSimple_increment_step(String n, String c, Environment gamma, T x, Environment gamma1,
			Equality p1, P p2) {
		return new Simple_increment_step<>(n, c, gamma, x, gamma1, p1, p2);
	}
	
	private static <T,P> Mutually<T,P> createMutually_all(Environment gamma, List<T> l, Environment gamma1, Equality p1, Equality p2, Forall<T,P> p3) {
		return new Mutually_all<>(gamma, l, gamma1, p1, p2, p3);
	}

	private static <T,P> Mutually<T,P> createMutually_all_explicit(String name, String content, Environment gamma, List<T> l, Environment gamma1, Equality p1, Equality p2, Forall<T,P> p3) {
		return new Mutually_all_explicit<>(name, content, gamma, l, gamma1, p1, p2, p3);
	}
	
	private static <T,P> Optionally<T,P> createOptionally_None(Environment gamma) {
		return new Optionally_None<>(gamma);
	}
	
	private static <T,P> Optionally<T,P> createOptionally_Some(Environment gamma, T x, P p1) {
		return new Optionally_Some<>(gamma, x, p1);
	}
	
	private static <A,B> And<A,B> createConj(A a, B b) {
		return new Conj<>(a, b);
	}
	
	private static <T, P> Ex<T, P> createEx_intro(T t, P p) {
		return new Ex_intro<>(t, p);
	}
	
	private static <T, P> Forall<T,P> createForall_nil() {
		return new Forall_nil<>();
	}

	private static <T, P> Forall<T,P> createForall_cons(T t, P p1, Forall<T,P> p2) {
		return new Forall_cons<>(t, p1, p2);
	}
	
	private static <A,B,P> Forall2<A,B,P> createForall2_nil() {
		return new Forall2_nil<>();
	}
	
	private static <A,B,P> Forall2<A,B,P> createForall2_cons(A x, B y, P p1, Forall2<A,B,P> p2) {
		return new Forall2_cons<A, B, P>(x, y, p1, p2);
	}

	private static Equality createReflexivity() {
		return new Eq_refl();
	}
	
	private static True createI() {
		return new I();
	}
	
	private static RangeType createRangeType(Expression min, Expression max) {
		RangeType r = SosADLFactory.eINSTANCE.createRangeType();
		r.setVmin(copy(min));
		r.setVmax(copy(max));
		return r;
	}
	
	@SuppressWarnings("unused")
	private static RangeType createRangeType(int min, Expression max) {
		return createRangeType(createIntegerValue(min), max);
	}

	@SuppressWarnings("unused")
	private static RangeType createRangeType(Expression min, int max) {
		return createRangeType(min, createIntegerValue(max));
	}

	@SuppressWarnings("unused")
	private static RangeType createRangeType(int min, int max) {
		return createRangeType(createIntegerValue(min), createIntegerValue(max));
	}
	
	private static BooleanType createBooleanType() {
		return SosADLFactory.eINSTANCE.createBooleanType();
	}
	
	private static NamedType createNamedType(String name) {
		NamedType t = SosADLFactory.eINSTANCE.createNamedType();
		t.setName(name);
		return t;
	}
	
	private static Expression createIntegerValue(int v) {
		IntegerValue r = SosADLFactory.eINSTANCE.createIntegerValue();
		r.setAbsInt(v);
		return r;
	}
	
	private static Expression createOpposite(Expression e) {
		UnaryExpression r = SosADLFactory.eINSTANCE.createUnaryExpression();
		r.setOp("-");
		r.setRight(copy(e));
		return r;
	}
	
	private static Expression createBinaryExpression(Expression l, String o, Expression r) {
		BinaryExpression ret = SosADLFactory.eINSTANCE.createBinaryExpression();
		ret.setLeft(copy(l));
		ret.setOp(o);
		ret.setRight(copy(r));
		return ret;
	}
	
	private static TupleType createTupleType(Iterable<FieldDecl> fields) {
		return createTupleType(fields.iterator());
	}
	
	private static TupleType createTupleType(Iterator<FieldDecl> fields) {
		TupleType ret = SosADLFactory.eINSTANCE.createTupleType();
		while(fields.hasNext()) {
			ret.getFields().add(copy(fields.next()));
		}
		return ret;
	}

	private static TupleType createTupleType(Stream<FieldDecl> fields) {
		return createTupleType(fields.iterator());
	}
	
	private static SequenceType createSequenceType(DataType t) {
		SequenceType ret = SosADLFactory.eINSTANCE.createSequenceType();
		ret.setType(copy(t));
		return ret;
	}
	
	private static FieldDecl createFieldDecl(String name, DataType t) {
		FieldDecl f = SosADLFactory.eINSTANCE.createFieldDecl();
		f.setName(name);
		f.setType(copy(t));
		return f;
	}
	
	private static FormalParameter createFormalParameter(String name, DataType t) {
		FormalParameter p = SosADLFactory.eINSTANCE.createFormalParameter();
		p.setName(name);
		p.setType(copy(t));
		return p;
	}
	
	private static FunctionDecl createFunctionDecl(FormalParameter self, String name, List<FormalParameter> params, DataType ret, List<Valuing> vals, Expression b) {
		FunctionDecl f = SosADLFactory.eINSTANCE.createFunctionDecl();
		f.setData(copy(self));
		f.setName(name);
		f.getParameters().addAll(ListExtensions.map(params, TypeChecker::copy));
		f.setType(copy(ret));
		f.getValuing().addAll(ListExtensions.map(vals, TypeChecker::copy));
		f.setExpression(copy(b));
		return f;
	}

	private static Type_expression_node createType_expression_Same(Environment gamma, Expression e, DataType tau, Expression min,
			Expression max, Type_expression p1, Subtype p2) {
		return new Type_expression_Same(gamma, e, tau, min, max, p1, p2);
	}
	
	private static Type_expression_node createType_expression_Opposite(Environment gamma, Expression e, DataType tau, Expression min,
			Expression max, Type_expression p1, Subtype p2) {
		return new Type_expression_Opposite(gamma, e, tau, min, max, p1, p2);
	}
	
	private static Type_expression_node createType_expression_Not(Environment gamma, Expression e, DataType tau, Type_expression p1, Subtype p2) {
		return new Type_expression_Not(gamma, e, tau, p1, p2);
	}
	
	private static Type_expression_node createType_expression_Add(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2,
			Type_expression p3, Subtype p4) {
		return new Type_expression_Add(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
	}
	
	private static Type_expression_node createType_expression_Sub(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2,
			Type_expression p3, Subtype p4) {
		return new Type_expression_Sub(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
	}
	
	private static Type_expression_node createType_expression_Mul(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Expression min, Expression max,
			Type_expression p1, Subtype p2, Type_expression p3, Subtype p4, Expression_le p5, Expression_le p6,
			Expression_le p7, Expression_le p8, Expression_le p9, Expression_le pa, Expression_le pb,
			Expression_le pc) {
		return new Type_expression_Mul(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, min, max, p1, p2, p3, p4, p5, p6, p7, p8, p9, pa, pb, pc);
	}
	
	private static Type_expression_node createType_expression_Div_pos(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Expression min, Expression max,
			Type_expression p1, Subtype p2, Type_expression p3, Subtype p4, Expression_le p5, Expression_le p6,
			Expression_le p7, Expression_le p8, Expression_le p9, Expression_le pa, Expression_le pb,
			Expression_le pc, Expression_le pd) {
		return new Type_expression_Div_pos(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, min, max, p1, p2, p3, p4, p5, p6, p7, p8, p9, pa, pb, pc, pd);
	}
	
	private static Type_expression_node createType_expression_Div_neg(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Expression min, Expression max,
			Type_expression p1, Subtype p2, Type_expression p3, Subtype p4, Expression_le p5, Expression_le p6,
			Expression_le p7, Expression_le p8, Expression_le p9, Expression_le pa, Expression_le pb,
			Expression_le pc, Expression_le pd) {
		return new Type_expression_Div_neg(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, min, max, p1, p2, p3, p4, p5, p6, p7, p8, p9, pa, pb, pc, pd);
	}

	private static Type_expression_node createType_expression_Mod(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Expression min, Expression max,
			Type_expression p1, Subtype p2, Type_expression p3, Subtype p4, Range_modulo_min p5, Range_modulo_max p6) {
		return new Type_expression_Mod(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, min, max, p1, p2, p3, p4, p5, p6);
	}
	
	private static Type_expression_node createType_expression_Implies(Environment gamma, Expression l, DataType l__tau, Expression r, DataType r__tau,
			Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
		return new Type_expression_Implies(gamma, l, l__tau, r, r__tau, p1, p2, p3, p4);
	}
	
	private static Type_expression_node createType_expression_Or(Environment gamma, Expression l, DataType l__tau, Expression r, DataType r__tau,
			Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
		return new Type_expression_Or(gamma, l, l__tau, r, r__tau, p1, p2, p3, p4);
	}
	
	private static Type_expression_node createType_expression_Xor(Environment gamma, Expression l, DataType l__tau, Expression r, DataType r__tau,
			Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
		return new Type_expression_Xor(gamma, l, l__tau, r, r__tau, p1, p2, p3, p4);
	}
	
	private static Type_expression_node createType_expression_And(Environment gamma, Expression l, DataType l__tau, Expression r, DataType r__tau,
			Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
		return new Type_expression_And(gamma, l, l__tau, r, r__tau, p1, p2, p3, p4);
	}
	
	private static Type_expression_node createType_expression_Equal(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2,
			Type_expression p3, Subtype p4) {
		return new Type_expression_Equal(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
	}
	
	private static Type_expression_node createType_expression_Diff(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2,
			Type_expression p3, Subtype p4) {
		return new Type_expression_Diff(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
	}
	
	private static Type_expression_node createType_expression_Lt(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2,
			Type_expression p3, Subtype p4) {
		return new Type_expression_Lt(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
	}
	
	private static Type_expression_node createType_expression_Le(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2,
			Type_expression p3, Subtype p4) {
		return new Type_expression_Le(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
	}
	
	private static Type_expression_node createType_expression_Gt(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2,
			Type_expression p3, Subtype p4) {
		return new Type_expression_Gt(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
	}
	
	private static Type_expression_node createType_expression_Ge(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2,
			Type_expression p3, Subtype p4) {
		return new Type_expression_Ge(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
	}
	
	private static Type_expression_node createType_expression_Ident(Environment gamma, String x, DataType tau, Equality p) {
		return new Type_expression_Ident(gamma, x, tau, p);
	}
	
	private static Type_expression_node createType_expression_MethodCall(Environment gamma, Expression self, DataType t, DataTypeDecl typeDecl,
			DataType alpha, DataType tau, EList<FunctionDecl> methods, String name, EList<FormalParameter> formalparams, DataType ret,
			EList<Expression> params, Type_expression p1, Ex<BigInteger, Equality> p2, Subtype p4,
			Ex<BigInteger, And<Equality, And<Equality, And<Equality, Equality>>>> p5,
			Forall2<FormalParameter, Expression, Ex<DataType, And<Equality, Ex<DataType, And<Type_expression, Subtype>>>>> p6) {
		return new Type_expression_MethodCall(gamma, self, t, typeDecl, alpha, tau, methods, name, formalparams, ret, params, p1, p2, p4, p5, p6);
	}
	
	private static Type_expression_node createType_expression_Tuple(Environment gamma, EList<TupleElement> elts, EList<FieldDecl> typ, Equality p1,
			Forall2<TupleElement, FieldDecl, Equality> p2,
			Forall2<TupleElement, FieldDecl, Ex<Expression, And<Equality, Ex<DataType, And<Equality, Type_expression>>>>> p3) {
		return new Type_expression_Tuple(gamma, elts, typ, p1, p2, p3);
	}
	
	private static Type_expression_node createType_expression_Field(Environment gamma, Expression self, EList<FieldDecl> tau, String name,
			DataType tau__f, Type_expression p1, Equality p2) {
		return new Type_expression_Field(gamma, self, tau, name, tau__f, p1, p2);
	}
	
	private static Type_expression_node createType_expression_Sequence(Environment gamma, EList<Expression> elts, DataType tau,
			Forall<Expression, Ex<DataType, And<Type_expression, Subtype>>> p1) {
		return new Type_expression_Sequence(gamma, elts, tau, p1);
	}
	
	private static Range_modulo_min createRange_modulo_min_pos(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Expression min, Expression_le p1,
			Expression_le p2) {
		return new Range_modulo_min_pos(lmin, lmax, rmin, rmax, min, p1, p2);
	}
	
	private static Range_modulo_min createRange_modulo_min_zero(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Expression min, Expression_le p1,
			Expression_le p2) {
		return new Range_modulo_min_zero(lmin, lmax, rmin, rmax, min, p1, p2);
	}
	
	private static Range_modulo_min createRange_modulo_min_neg(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Expression min, Expression_le p1,
			Expression_le p2) {
		return new Range_modulo_min_neg(lmin, lmax, rmin, rmax, min, p1, p2);
	}

	private static Range_modulo_max createRange_modulo_max_pos(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Expression min, Expression_le p1,
			Expression_le p2) {
		return new Range_modulo_max_pos(lmin, lmax, rmin, rmax, min, p1, p2);
	}
	
	private static Range_modulo_max createRange_modulo_max_zero(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Expression min, Expression_le p1,
			Expression_le p2) {
		return new Range_modulo_max_zero(lmin, lmax, rmin, rmax, min, p1, p2);
	}
	
	private static Range_modulo_max createRange_modulo_max_neg(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Expression min, Expression_le p1,
			Expression_le p2) {
		return new Range_modulo_max_neg(lmin, lmax, rmin, rmax, min, p1, p2);
	}

	private static Subtype createSubtype_refl(DataType t) {
		return new Subtype_refl(t);
	}
	
	private static Subtype createSubtype_range(Expression lmi, Expression lma, Expression rmi, Expression rma,
			Expression_le p1, Expression_le p2) {
		return new Subtype_range(lmi, lma, rmi, rma, p1, p2);
	}
	
	private static Subtype createSubtype_tuple(EList<FieldDecl> l, EList<FieldDecl> r,
			Forall<FieldDecl, Ex<String, And<Equality, Ex<DataType, And<Equality, Ex<DataType, And<Equality, Subtype>>>>>>> p1) {
		return new Subtype_tuple(l, r, p1);
	}
	
	private static Subtype createSubtype_sequence(DataType l, DataType r, Subtype p1) {
		return new Subtype_sequence(l, r, p1);
	}

	private static Check_datatype createCheck_NamedType(String n) {
		return new Check_NamedType(n);
	}
	
	private static Check_datatype createCheck_TupleType(EList<FieldDecl> fields, Equality p1,
			Forall<FieldDecl, Ex<DataType, And<Equality, Check_datatype>>> p2) {
		return new Check_TupleType(fields, p1, p2);
	}
	
	private static Check_datatype createCheck_SequenceType(DataType t, Check_datatype p1) {
		return new Check_SequenceType(t, p1);
	}
	
	private static Check_datatype createCheck_RangeType_trivial(Expression min, Expression max, Expression_le p1) {
		return new Check_RangeType_trivial(min, max, p1);
	}
	
	private static Check_datatype createCheck_BooleanType() {
		return new Check_BooleanType();
	}

	private TypeVariable createFreshTypeVariable(EObject co, EStructuralFeature csf, BinaryOperator<Optional<DataType>> solver) {
		return inference.createFreshTypeVariable(solver, co, csf);
	}
	private <T extends ProofTerm> T proofTerm(DataType x, Class<T> itf, Function<DataType, T> factory) {
		return proofTerm(itf, () -> {
			DataType t = getSubstitute(x);
			return factory.apply(t);
		}, x);
	}
	
	private <T extends ProofTerm> T proofTerm(Class<T> itf, Supplier<T> factory, DataType... x) {
		if(Stream.of(x).anyMatch(TypeInferenceSolver::containsVariable)) {
			ProofTermPlaceHolder<T> ptph = ProofTermPlaceHolder.create(itf);
			delayedTasks.add(() -> {
				ptph.fillWith(factory.get());
			});
			return ptph.cast();
		} else {
			return factory.get();
		}
	}

	private DataType getSubstitute(DataType t) {
		return inference.deepSubstitute(t);
	}

	private FieldDecl getSubstitute(FieldDecl f) {
		return createFieldDecl(f.getName(), getSubstitute(f.getType()));
	}

	private static <T extends EObject> T copy(T x) {
		return TypeInferenceSolver.copy(x);
	}
	
	private DataType deepSubstitute(DataType t) {
		return getSubstitute(t);
	}
	
	private FieldDecl deepSubstitute(FieldDecl f) {
		return getSubstitute(f);
	}
}
