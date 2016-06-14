package org.archware.sosadl.validation.typing;

import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;

import org.archware.sosadl.sosADL.ArchitectureDecl;
import org.archware.sosadl.sosADL.AssertionDecl;
import org.archware.sosadl.sosADL.BehaviorDecl;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.DataTypeDecl;
import org.archware.sosadl.sosADL.EntityBlock;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.FormalParameter;
import org.archware.sosadl.sosADL.FunctionDecl;
import org.archware.sosadl.sosADL.GateDecl;
import org.archware.sosadl.sosADL.Library;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.NamedType;
import org.archware.sosadl.sosADL.SoS;
import org.archware.sosadl.sosADL.SosADL;
import org.archware.sosadl.sosADL.SosADLPackage;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.sosADL.Unit;
import org.archware.sosadl.sosADL.Valuing;
import org.archware.sosadl.validation.AccumulatingValidator;
import org.archware.sosadl.validation.typing.impl.ArchitectureEnvContent;
import org.archware.sosadl.validation.typing.impl.MediatorEnvContent;
import org.archware.sosadl.validation.typing.impl.SystemEnvContent;
import org.archware.sosadl.validation.typing.impl.TypeEnvContent;
import org.archware.sosadl.validation.typing.impl.VariableEnvContent;
import org.archware.sosadl.validation.typing.proof.And;
import org.archware.sosadl.validation.typing.proof.Equality;
import org.archware.sosadl.validation.typing.proof.Ex;
import org.archware.sosadl.validation.typing.proof.Forall;
import org.archware.sosadl.validation.typing.proof.Forall2;
import org.archware.sosadl.validation.typing.proof.Incrementally;
import org.archware.sosadl.validation.typing.proof.Mutually;
import org.archware.sosadl.validation.typing.proof.Simple_increment;
import org.archware.sosadl.validation.typing.proof.Subtype;
import org.archware.sosadl.validation.typing.proof.True;
import org.archware.sosadl.validation.typing.proof.Type_architecture;
import org.archware.sosadl.validation.typing.proof.Type_assertion;
import org.archware.sosadl.validation.typing.proof.Type_behavior;
import org.archware.sosadl.validation.typing.proof.Type_datatype;
import org.archware.sosadl.validation.typing.proof.Type_datatypeDecl;
import org.archware.sosadl.validation.typing.proof.Type_entityBlock;
import org.archware.sosadl.validation.typing.proof.Type_expression;
import org.archware.sosadl.validation.typing.proof.Type_function;
import org.archware.sosadl.validation.typing.proof.Type_gate;
import org.archware.sosadl.validation.typing.proof.Type_mediator;
import org.archware.sosadl.validation.typing.proof.Type_sosADL;
import org.archware.sosadl.validation.typing.proof.Type_system;
import org.archware.sosadl.validation.typing.proof.Type_unit;
import org.archware.sosadl.validation.typing.proof.Type_valuing;
import org.archware.utils.Pair;
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
public class TypeChecker extends TypeCheckerExpression {
	@Override
	protected Type_sosADL type_sosADL(SosADL file) {
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
				error("The type of the data parameter " + f.getData().getName() + " must be `" + d.getName() + "'", f, SosADLPackage.Literals.FUNCTION_DECL__DATA);
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
									p(Type_function.class, gamma,
											(gamma_) -> p(Type_function.class, t,
													(x) -> p(Type_function.class, gammap,
															(gammap_) -> p(Type_function.class, gammav,
																	(gammav_) -> p(Type_function.class, gamma1,
																			(gamma1_) ->
													createType_FunctionDecl_Method(gamma_,
													f.getData().getName(),
											((NamedType)f.getData().getType()).getName(),
											((TypeEnvContent)gamma_.get(((NamedType)f.getData().getType()).getName())).getDataTypeDecl(),
											realType,
											((TypeEnvContent)gamma_.get(((NamedType)f.getData().getType()).getName())).getMethods(),
											f.getName(),
											f.getParameters(),
											params2,
											gammap_,
											f.getType(),
											p2.getA(),
											f.getValuing(),
											gammav_,
											f.getExpression(),
											x,
											gamma1_,
											createReflexivity(),
											p2.getB(),
											p3.getB(),
											p4.getA(),
											p5.getA(),
											subtype(x, p2.getA(), f, SosADLPackage.Literals.FUNCTION_DECL__EXPRESSION).orElse(null),
											createReflexivity()))))))),
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
	
	private Pair<Type_valuing, Environment> type_valuing(Environment gamma, Valuing v) {
		Expression e = v.getExpression();
		String x = v.getVariable();
		if(e != null && x != null) {
			Pair<Type_expression, DataType> pt1 = type_expression(gamma, e);
			Type_expression p1 = pt1.getA();
			DataType tau__e = pt1.getB();
			if(p1 != null && tau__e != null) {
				DataType tau = v.getType();
				if(tau != null) {
					return new Pair<>(saveProof(v,
							p(Type_valuing.class, gamma,
									(gamma_) -> p(Type_valuing.class, tau,
											(tau_) -> p(Type_valuing.class, tau__e,
													(tau__e_) -> {
														Optional<Subtype> st = subtype(tau__e_, tau_,
																v, null);
														return st.map((st_) -> createType_Valuing_typed(gamma_, x, tau_, e, tau__e_, p1, st_)).orElse(null);
							})))),
							gamma.put(x, new VariableEnvContent(v, tau)));
				} else {
					return new Pair<>(saveProof(v,
							p(Type_valuing.class, gamma,
									(gamma_) -> p(Type_valuing.class, tau__e,
													(tau__e_) -> createType_Valuing_inferred(gamma_, x, e, tau__e_, p1)))),
							gamma.put(x, new VariableEnvContent(v, tau__e)));
				}
			} else {
				return new Pair<>(null, gamma);
			}
		} else {
			if(v.getExpression() == null) {
				error("The valuing must contain an expression", v, SosADLPackage.Literals.VALUING__EXPRESSION);
			}
			if(v.getVariable() == null) {
				error("The valuing must contain a variable name", v, SosADLPackage.Literals.VALUING__VARIABLE);
			}
			return new Pair<>(null, gamma);
		}
	}

	private Pair<Incrementally<Valuing, Type_valuing>, Environment> type_valuings(Environment gamma,
			EList<Valuing> l) {
		return proveIncrementally(gamma, l, this::type_valuing);
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
					this::type_formalParameter);
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
	
	private And<Equality,Ex<DataType,And<Equality,Ex<DataType,And<Equality,Type_datatype>>>>> type_formalParameter(Pair<FormalParameter, Pair<DataType, Type_datatype>> p) {
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
	
	private Type_behavior type_behavior(Environment gamma, BehaviorDecl behaviorDecl) {
		// TODO Auto-generated method stub
		return null;
	}
}
