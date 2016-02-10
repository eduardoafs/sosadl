/*
 * generated by Xtext
 */
package org.archware.sosadl.validation;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.math.BigInteger;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.archware.sosadl.attributed.AttributeAdapter;
import org.archware.sosadl.sosADL.ArchitectureDecl;
import org.archware.sosadl.sosADL.AssertionDecl;
import org.archware.sosadl.sosADL.BehaviorDecl;
import org.archware.sosadl.sosADL.BinaryExpression;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.DataTypeDecl;
import org.archware.sosadl.sosADL.EntityBlock;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.FieldDecl;
import org.archware.sosadl.sosADL.FormalParameter;
import org.archware.sosadl.sosADL.FunctionDecl;
import org.archware.sosadl.sosADL.GateDecl;
import org.archware.sosadl.sosADL.Import;
import org.archware.sosadl.sosADL.IntegerValue;
import org.archware.sosadl.sosADL.Library;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.NamedType;
import org.archware.sosadl.sosADL.RangeType;
import org.archware.sosadl.sosADL.SequenceType;
import org.archware.sosadl.sosADL.SoS;
import org.archware.sosadl.sosADL.SosADL;
import org.archware.sosadl.sosADL.SosADLPackage;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.sosADL.TupleType;
import org.archware.sosadl.sosADL.UnaryExpression;
import org.archware.sosadl.sosADL.Unit;
import org.archware.sosadl.validation.typing.Environment;
import org.archware.sosadl.validation.typing.impl.SystemEnvContent;
import org.archware.sosadl.validation.typing.impl.TypeEnvContent;
import org.archware.sosadl.validation.typing.impl.VariableEnvContent;
import org.archware.sosadl.validation.typing.interp.InterpInZ;
import org.archware.sosadl.validation.typing.proof.And;
import org.archware.sosadl.validation.typing.proof.Conj;
import org.archware.sosadl.validation.typing.proof.Constexpr_Add;
import org.archware.sosadl.validation.typing.proof.Constexpr_Div;
import org.archware.sosadl.validation.typing.proof.Constexpr_IntegerValue;
import org.archware.sosadl.validation.typing.proof.Constexpr_Mod;
import org.archware.sosadl.validation.typing.proof.Constexpr_Mul;
import org.archware.sosadl.validation.typing.proof.Constexpr_Opposite;
import org.archware.sosadl.validation.typing.proof.Constexpr_Same;
import org.archware.sosadl.validation.typing.proof.Constexpr_Sub;
import org.archware.sosadl.validation.typing.proof.Constexpr_expression;
import org.archware.sosadl.validation.typing.proof.Eluded;
import org.archware.sosadl.validation.typing.proof.Eq_refl;
import org.archware.sosadl.validation.typing.proof.Equality;
import org.archware.sosadl.validation.typing.proof.Ex;
import org.archware.sosadl.validation.typing.proof.Ex_intro;
import org.archware.sosadl.validation.typing.proof.Expression_le;
import org.archware.sosadl.validation.typing.proof.Forall;
import org.archware.sosadl.validation.typing.proof.Forall_cons;
import org.archware.sosadl.validation.typing.proof.Forall_nil;
import org.archware.sosadl.validation.typing.proof.In_Z;
import org.archware.sosadl.validation.typing.proof.Mandatory;
import org.archware.sosadl.validation.typing.proof.ProofTerm;
import org.archware.sosadl.validation.typing.proof.Type_EntityBlock;
import org.archware.sosadl.validation.typing.proof.Type_EntityBlock_datatype_None;
import org.archware.sosadl.validation.typing.proof.Type_EntityBlock_datatype_Some;
import org.archware.sosadl.validation.typing.proof.Type_EntityBlock_system;
import org.archware.sosadl.validation.typing.proof.Type_Library;
import org.archware.sosadl.validation.typing.proof.Type_NamedType;
import org.archware.sosadl.validation.typing.proof.Type_RangeType_trivial;
import org.archware.sosadl.validation.typing.proof.Type_SequenceType;
import org.archware.sosadl.validation.typing.proof.Type_SoS;
import org.archware.sosadl.validation.typing.proof.Type_SosADL;
import org.archware.sosadl.validation.typing.proof.Type_SystemDecl;
import org.archware.sosadl.validation.typing.proof.Type_SystemDecl_None;
import org.archware.sosadl.validation.typing.proof.Type_TupleType;
import org.archware.sosadl.validation.typing.proof.Type_behavior;
import org.archware.sosadl.validation.typing.proof.Type_datatype;
import org.archware.sosadl.validation.typing.proof.Type_datatypeDecl;
import org.archware.sosadl.validation.typing.proof.Type_entityBlock;
import org.archware.sosadl.validation.typing.proof.Type_sosADL;
import org.archware.sosadl.validation.typing.proof.Type_system;
import org.archware.sosadl.validation.typing.proof.Type_systemblock;
import org.archware.sosadl.validation.typing.proof.Type_unit;
import org.eclipse.emf.common.util.ECollections;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.validation.Check;
import org.eclipse.xtext.xbase.lib.StringExtensions;

/**
 * Custom validation rules. 
 *
 * see http://www.eclipse.org/Xtext/documentation.html#validation
 */
public class SosADLValidator extends AbstractSosADLValidator {
	
//  public static val INVALID_NAME = 'invalidName'
//
//	@Check
//	def checkGreetingStartsWithCapital(Greeting greeting) {
//		if (!Character.isUpperCase(greeting.name.charAt(0))) {
//			warning('Name should start with a capital', 
//					MyDslPackage.Literals.GREETING__NAME,
//					INVALID_NAME)
//		}
//	}

	@Check
	public Type_sosADL type_sosADL(SosADL file) {
		// type_SosADL:
		if(file.getContent() != null) {
			return saveProof(file, createType_SosADL(file.getImports(), file.getContent(), type_unit(Environment.empty(), file.getContent())));
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
		// type_EntityBlock_datatype_Some:
		if(datatypes.size() >= 1 && datatypes.get(0).getName() != null && datatypes.get(0).getDatatype() != null) {
			return createType_EntityBlock_datatype_Some(gamma, datatypes.get(0).getName(), datatypes.get(0).getDatatype(),
					datatypes.get(0).getFunctions(), cdr(datatypes), functions, systems, mediators, architectures,
					type_datatypeDecl(gamma, datatypes.get(0)),
					type_entityBlock(gamma.put(datatypes.get(0).getName(), new TypeEnvContent(datatypes.get(0))), decls, cdr(datatypes), functions, systems, mediators, architectures));
		} else
		// type_EntityBlock_datatype_None:
		if(datatypes.size() >= 1 && datatypes.get(0).getName() != null && datatypes.get(0).getDatatype() == null) {
			return createType_EntityBlock_datatype_None(gamma, datatypes.get(0).getName(),
					datatypes.get(0).getFunctions(), cdr(datatypes), functions, systems, mediators, architectures,
					type_datatypeDecl(gamma, datatypes.get(0)),
					type_entityBlock(gamma.put(datatypes.get(0).getName(), new TypeEnvContent(datatypes.get(0))), decls, cdr(datatypes), functions, systems, mediators, architectures));
		} else
		// type_EntityBlock_system:
		if(datatypes.isEmpty() && functions.isEmpty() && systems.size() >= 1 && systems.get(0).getName() != null) {
			return createType_EntityBlock_system(gamma, systems.get(0), systems.get(0).getName(), cdr(systems), mediators, architectures,
					type_system(gamma, systems.get(0)),
					createReflexivity(),
					type_entityBlock(gamma.put(systems.get(0).getName(),  new SystemEnvContent(systems.get(0))), decls, datatypes, functions, cdr(systems), mediators, architectures));
		} else
		// type_EntityBlock:
		if(datatypes.isEmpty() && functions.isEmpty() && systems.isEmpty() && mediators.isEmpty() && architectures.isEmpty()) {
			return createType_EntityBlock(gamma);
		} else {
			EObject x = firstOfOr(decls, datatypes, functions, systems, mediators, architectures);
			error("Badly formed entity block", x, null);
			return null;
		}
	}

	private Type_datatypeDecl type_datatypeDecl(Environment gamma, DataTypeDecl dataTypeDecl) {
		saveEnvironment(dataTypeDecl, gamma);
		// TODO Auto-generated method stub
		return null;
	}

	private Type_system type_system(Environment gamma, SystemDecl systemDecl) {
		saveEnvironment(systemDecl, gamma);
		// type_SystemDecl:
		if(systemDecl.getName() != null && systemDecl.getBehavior() != null && noDuplicate(systemDecl.getParameters().stream().map(FormalParameter::getName))) {
			return saveProof(systemDecl, createType_SystemDecl(env_add_params(systemDecl.getParameters(), gamma), systemDecl.getName(), systemDecl.getParameters(), systemDecl.getDatatypes(),
					systemDecl.getGates(), systemDecl.getBehavior(), systemDecl.getAssertion(),
					proveForall(systemDecl.getParameters(), (p) -> proveExistsAndEqType(gamma, p, FormalParameter::getType)),
					type_systemblock(gamma, systemDecl, systemDecl.getDatatypes(), systemDecl.getGates(), systemDecl.getAssertion(), systemDecl.getBehavior()), createReflexivity()));
		} else {
			if(!noDuplicate(systemDecl.getParameters().stream().map(FormalParameter::getName))) {
				EList<FormalParameter> params = systemDecl.getParameters();
				params.stream().filter((p) -> params.stream().map(FormalParameter::getName).filter((n) -> n.equals(p.getName())).count() >= 2).forEach((f) -> error("Multiple parameters named `" + f.getName() + "'", f, null));
			} else if(systemDecl.getBehavior() == null) {
				error("The system must have a behavior", systemDecl, null);
			} else if(systemDecl.getName() == null) {
				error("The system must have a name", systemDecl, null);
			} else {
				error("Type error", systemDecl, null);
			}
			return null;
		}
	}

	private <T> Ex<DataType, And<Equality,Type_datatype>> proveExistsAndEqType(Environment gamma, T t, Function<T, DataType> getter) {
		return createEx_intro(getter.apply(t), createConj(createReflexivity(), type_datatype(gamma, getter.apply(t))));
	}

	private Type_datatype type_datatype(Environment gamma, DataType type) {
		saveEnvironment(type, gamma);
		// type_NamedType:
		if(type instanceof NamedType && ((NamedType)type).getName() != null && gamma.get(((NamedType)type).getName()) != null && gamma.get(((NamedType)type).getName()) instanceof TypeEnvContent && ((TypeEnvContent)gamma.get(((NamedType)type).getName())).getDataTypeDecl() != null) {
			return saveProof(type, createType_NamedType(gamma, ((NamedType)type).getName(), ((TypeEnvContent)gamma.get(((NamedType)type).getName())).getDataTypeDecl(), createReflexivity()));
		}
		// type_TupleType:
		else if(type instanceof TupleType && noDuplicate(((TupleType)type).getFields().stream().map(FieldDecl::getName))) {
			return saveProof(type, createType_TupleType(gamma, ((TupleType)type).getFields(), createReflexivity(),
					proveForall(((TupleType)type).getFields(), (f) -> proveExistsAndEqType(gamma, f, FieldDecl::getType))));
		}
		// type_SequenceType:
		else if(type instanceof SequenceType && ((SequenceType)type).getType() != null) {
			return saveProof(type, createType_SequenceType(gamma, ((SequenceType)type).getType(), type_datatype(gamma, ((SequenceType)type).getType())));
		}
		// type_RangeType_trivial
		else if(type instanceof RangeType && ((RangeType)type).getVmin() != null && ((RangeType)type).getVmax() != null && !containsSomeNull(constexpr_expression(((RangeType)type).getVmin())) && !containsSomeNull(constexpr_expression(((RangeType)type).getVmax())) && InterpInZ.le(((RangeType)type).getVmin(), ((RangeType)type).getVmax())) {
			saveMin(type, InterpInZ.eval(((RangeType)type).getVmin()));
			saveMax(type, InterpInZ.eval(((RangeType)type).getVmax()));
			return saveProof(type, createType_RangeType_trivial(gamma, ((RangeType)type).getVmin(), ((RangeType)type).getVmax(), constexpr_expression(((RangeType)type).getVmin()), constexpr_expression(((RangeType)type).getVmax()), createIn_Z(((RangeType)type).getVmin(), InterpInZ.eval(((RangeType)type).getVmin()), ((RangeType)type).getVmax(), InterpInZ.eval(((RangeType)type).getVmax()), createReflexivity(), createReflexivity(), createReflexivity())));
		} else {
			if(type instanceof NamedType && ((NamedType)type).getName() != null && gamma.get(((NamedType)type).getName()) != null && gamma.get(((NamedType)type).getName()) instanceof TypeEnvContent && ((TypeEnvContent)gamma.get(((NamedType)type).getName())).getDataTypeDecl() == null) {
				error("No type declaration named `" + gamma.get(((NamedType)type).getName()) + "'", type, null);
			} else if(type instanceof NamedType && ((NamedType)type).getName() != null && gamma.get(((NamedType)type).getName()) != null && !(gamma.get(((NamedType)type).getName()) instanceof TypeEnvContent)) {
				error("`" + ((NamedType)type).getName() + "' is not a type declaration", type, null);
			} else if(type instanceof NamedType && ((NamedType)type).getName() != null && gamma.get(((NamedType)type).getName()) == null) {
				error("`" + ((NamedType)type).getName() + "' is undefined in this context", type, null);
			} else if(type instanceof NamedType && ((NamedType)type).getName() == null) {
				error("The named type must have a name", type, null);
			} else if(type instanceof TupleType && !noDuplicate(((TupleType)type).getFields().stream().map(FieldDecl::getName))) {
				EList<FieldDecl> fields = ((TupleType)type).getFields();
				fields.stream().filter((f) -> fields.stream().map(FieldDecl::getName).filter((n) -> n.equals(f.getName())).count() >= 2).forEach((f) -> error("Multiple fields named `" + f.getName() + "' in the tuple type", f, null));
			} else if(type instanceof SequenceType && ((SequenceType)type).getType() == null) {
				error("The sequence type must declare a base type", type, null);
			} else if(type instanceof RangeType && ((RangeType)type).getVmin() != null && ((RangeType)type).getVmax() != null && !containsSomeNull(constexpr_expression(((RangeType)type).getVmin())) && !containsSomeNull(constexpr_expression(((RangeType)type).getVmax())) && InterpInZ.gt(((RangeType)type).getVmin(), ((RangeType)type).getVmax())) {
				error("The lower bound of the range is greater than the upper bound", type, null);
			} else if(type instanceof RangeType && ((RangeType)type).getVmin() != null && ((RangeType)type).getVmax() != null) {
				if(containsSomeNull(constexpr_expression(((RangeType)type).getVmin()))) {
					error("The lower bound of the range is not a constant integer", type, SosADLPackage.Literals.RANGE_TYPE__VMIN);
				}
				if(containsSomeNull(constexpr_expression(((RangeType)type).getVmax()))) {
					error("The upper bound of the range is not a constant integer", type, SosADLPackage.Literals.RANGE_TYPE__VMIN);
				}
			} else if(type instanceof RangeType) {
				error("The range must have a lower bound and an upper bound", type, null);
			} else {
				error("Type error", type, null);
			}
			return null;
		}
	}

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

	private Type_systemblock type_systemblock(Environment gamma, SystemDecl systemDecl, EList<DataTypeDecl> dataTypeDecls, EList<GateDecl> gateDecls, AssertionDecl assertionDecl, BehaviorDecl behaviorDecl) {
		if(systemDecl.getName() != null && dataTypeDecls.isEmpty() && gateDecls.isEmpty() && assertionDecl == null && behaviorDecl != null) {
			return createType_SystemDecl_None(gamma, systemDecl.getName(), behaviorDecl, type_behavior(gamma, behaviorDecl));
		} else {
			error("Type error", systemDecl, null);
			return null;
		}
	}

	private Type_behavior type_behavior(Environment gamma, BehaviorDecl behaviorDecl) {
		// TODO Auto-generated method stub
		return null;
	}

	private <T extends EObject, P extends ProofTerm> Forall<T, P> proveForall(
			List<? extends T> l, Function<T, ? extends P> prover) {
		if(l.size() == 0) {
			return createForall_nil();
		} else {
			return createForall_cons(l.get(0), prover.apply(l.get(0)), proveForall(cdr(l), prover));
		}
	}

	public static final String ENVIRONMENT = "Environment";
	public static final String PROOF = "Proof";
	public static final String MIN = "Min";
	public static final String MAX = "Max";
	
	public static void saveMin(EObject eObject, BigInteger i) {
		AttributeAdapter.adapterOf(eObject).putAttribute(MIN, i);
	}
	
	public static void saveMax(EObject eObject, BigInteger i) {
		AttributeAdapter.adapterOf(eObject).putAttribute(MAX, i);
	}
	
	public static void saveEnvironment(EObject eObject, Environment env) {
		AttributeAdapter.adapterOf(eObject).putAttribute(ENVIRONMENT, env);
	}
	
	public static <T> T saveProof(EObject eObject, T proof) {
		AttributeAdapter.adapterOf(eObject).putAttribute(PROOF, proof);
		return proof;
	}

	public static Object getProof(EObject eObject) {
		return AttributeAdapter.adapterOf(eObject).getAttribute(PROOF);
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
	
	private static Environment env_add_params(List<FormalParameter> l, Environment gamma) {
		return fold_left((e,p) -> (p.getName() != null && p.getType() != null ? e.put(p.getName(), new VariableEnvContent(p, p.getType())) : e), l, gamma);
	}
	
	private static <A,B> A fold_left(BiFunction<A,B,A> f, List<B> l, A i) {
		if(l.isEmpty()) {
			return i;
		} else {
			return fold_left(f, cdr(l), f.apply(i, l.get(0)));
		}
	}
	
	private static <T> boolean noDuplicate(Stream<T> s) {
		List<T> list = s.collect(Collectors.toList());
		Set<T> set = new TreeSet<>(list);
		return list.size() == set.size();
	}

	private boolean containsSomeNull(Object o) {
		for(Field f : o.getClass().getDeclaredFields()) {
			if(!f.isAnnotationPresent(Eluded.class) && f.isAnnotationPresent(Mandatory.class) && ProofTerm.class.isAssignableFrom(f.getType())) {
				try {
					Method getter = o.getClass().getMethod("get" + StringExtensions.toFirstUpper(f.getName()));
					Object i = getter.invoke(o);
					if(i == null) {
						return true;
					} else if(containsSomeNull(i)) {
						return true;
					}
				} catch (NoSuchMethodException | SecurityException | IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
				}
			}
		}
		return false;
	}

	@SafeVarargs
	private static EObject firstOfOr(EObject other, EList<? extends EObject>... lists) {
		for(EList<? extends EObject> l : lists) {
			if(!l.isEmpty()) {
				return l.get(0);
			}
		}
		return other;
	}
	
	private static Type_sosADL createType_SosADL(EList<Import> i, Unit d, Type_unit p) {
		return new Type_SosADL(i, d, p);
	}
	
	private static Type_unit createType_SoS(Environment gamma, String n, EntityBlock e, Type_entityBlock p) {
		return new Type_SoS(gamma, n, e, p);
	}
	
	private static Type_unit createType_Library(Environment gamma, String n, EntityBlock e, Type_entityBlock p) {
		return new Type_Library(gamma, n, e, p);
	}
	
	private static Type_entityBlock createType_EntityBlock_datatype_Some(Environment gamma, String d_name, DataType d_def, EList<FunctionDecl> d_funs, EList<DataTypeDecl> l, EList<FunctionDecl> funs, EList<SystemDecl> systems, EList<MediatorDecl> mediators, EList<ArchitectureDecl> architectures, Type_datatypeDecl p1, Type_entityBlock p2) {
		return new Type_EntityBlock_datatype_Some(gamma, d_name, d_def, d_funs, l, funs, systems, mediators, architectures, p1, p2);
	}

	private static Type_entityBlock createType_EntityBlock_datatype_None(Environment gamma, String d_name, EList<FunctionDecl> d_funs, EList<DataTypeDecl> l, EList<FunctionDecl> funs, EList<SystemDecl> systems, EList<MediatorDecl> mediators, EList<ArchitectureDecl> architectures, Type_datatypeDecl p1, Type_entityBlock p2) {
		return new Type_EntityBlock_datatype_None(gamma, d_name, d_funs, l, funs, systems, mediators, architectures, p1, p2);
	}
	
	private static Type_entityBlock createType_EntityBlock_system(Environment gamma, SystemDecl s, String s_name,
			EList<SystemDecl> l, EList<MediatorDecl> mediators, EList<ArchitectureDecl> architectures,
			Type_system p1, Equality p2, Type_entityBlock p3) {
		return new Type_EntityBlock_system(gamma, s, s_name, l, mediators, architectures, p1, p2, p3);
	}

	private static Type_entityBlock createType_EntityBlock(Environment gamma) {
		return new Type_EntityBlock(gamma);
	}
	
	private static Type_system createType_SystemDecl(Environment gamma, String name, EList<FormalParameter> params, EList<DataTypeDecl> datatypes, EList<GateDecl> gates, BehaviorDecl bhv, AssertionDecl assrt, Forall<FormalParameter, Ex<DataType, And<Equality,Type_datatype>>> p1, Type_systemblock p2, Equality p3) {
		return new Type_SystemDecl(gamma, name, params, datatypes, gates, bhv, assrt, p1, p2, p3);
	}

	private static Type_datatype createType_NamedType(Environment gamma, String n, DataTypeDecl t, Equality p) {
		return new Type_NamedType(gamma, n, t, p);
	}
	
	private static Type_datatype createType_TupleType(Environment gamma, EList<FieldDecl> fields, Equality p1, Forall<FieldDecl, Ex<DataType, And<Equality, Type_datatype>>> p2) {
		return new Type_TupleType(gamma, fields, p1, p2);
	}
	
	private static Type_datatype createType_SequenceType(Environment gamma, DataType t, Type_datatype p) {
		return new Type_SequenceType(gamma, t, p);
	}
	
	private static Type_datatype createType_RangeType_trivial(Environment gamma, Expression min, Expression max, Constexpr_expression p1, Constexpr_expression p2, Expression_le p3) {
		return new Type_RangeType_trivial(gamma, min, max, p1, p2, p3);
	}
	
	private static Type_systemblock createType_SystemDecl_None(Environment gamma, String name, BehaviorDecl bhv, Type_behavior p) {
		return new Type_SystemDecl_None(gamma, name, bhv, p);
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

	private static Equality createReflexivity() {
		return new Eq_refl();
	}
}
