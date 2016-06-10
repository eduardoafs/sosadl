package org.archware.sosadl.validation.typing;

import java.math.BigInteger;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Stream;

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
import org.archware.sosadl.sosADL.Import;
import org.archware.sosadl.sosADL.IntegerValue;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.NamedType;
import org.archware.sosadl.sosADL.RangeType;
import org.archware.sosadl.sosADL.SequenceType;
import org.archware.sosadl.sosADL.SosADLFactory;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.sosADL.TupleElement;
import org.archware.sosadl.sosADL.TupleType;
import org.archware.sosadl.sosADL.UnaryExpression;
import org.archware.sosadl.sosADL.Unit;
import org.archware.sosadl.sosADL.Valuing;
import org.archware.sosadl.validation.typing.proof.*;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.xbase.lib.ListExtensions;

public class TypeCheckerConstructors extends TypeCheckerAnnotate {

	protected static Type_sosADL createType_SosADL_file(EList<Import> i, Unit d, Type_unit p) {
		return new Type_SosADL_file(i, d, p);
	}

	protected static Type_unit createType_SoS(Environment gamma, String n, EntityBlock e, Type_entityBlock p) {
		return new Type_SoS(gamma, n, e, p);
	}

	protected static Type_unit createType_Library(Environment gamma, String n, EntityBlock e, Type_entityBlock p) {
		return new Type_Library(gamma, n, e, p);
	}

	protected static Type_entityBlock createType_EntityBlock_whole(Environment gamma, List<DataTypeDecl> datatypes, Environment gamma1, List<FunctionDecl> funs,
			Environment gamma2, List<SystemDecl> systems, Environment gamma3, List<MediatorDecl> mediators, Environment gamma4, List<ArchitectureDecl> architectures, Environment gamma5, Incrementally<DataTypeDecl,Type_datatypeDecl> p1,
			Incrementally<FunctionDecl, Type_function> p2, Incrementally<SystemDecl,Simple_increment<SystemDecl,Type_system>> p3, Incrementally<MediatorDecl,Simple_increment<MediatorDecl,Type_mediator>> p4, Incrementally<ArchitectureDecl, Simple_increment<ArchitectureDecl, Type_architecture>> p5) {
				return new Type_EntityBlock_whole(gamma, datatypes, gamma1, funs, gamma2, systems, gamma3, mediators, gamma4, architectures, gamma5, p1, p2, p3, p4, p5);
			}

	protected static Type_system createType_SystemDecl(Environment gamma, String name, EList<FormalParameter> params, EList<FormalParameter> params2, Environment gamma1,
			EList<DataTypeDecl> datatypes, Environment gamma2, EList<GateDecl> gates, Environment gamma3, BehaviorDecl bhv, AssertionDecl assrt, And<Forall2<FormalParameter, FormalParameter, And<Equality, Ex<DataType, And<Equality, Ex<DataType, And<Equality, Type_datatype>>>>>>, Mutually<FormalParameter, True>> p1, Incrementally<DataTypeDecl, Type_datatypeDecl> p2,
			Incrementally<GateDecl, Simple_increment<GateDecl, Type_gate>> p3, Type_behavior p4, Optionally<AssertionDecl, Type_assertion> p5) {
				return new Type_SystemDecl(gamma, name, params, params2, gamma1, datatypes, gamma2, gates, gamma3, bhv, assrt, p1, p2, p3, p4, p5);
			}

	protected static Type_datatypeDecl createType_DataTypeDecl_def(Environment gamma, String name, DataType t, DataType t2,
			EList<FunctionDecl> funs, Environment gamma1, Type_datatype p1, Forall<FunctionDecl,Ex<FormalParameter, And<Equality, Equality>>> p2, Incrementally<FunctionDecl, Type_function> p3) {
				return new Type_DataTypeDecl_def(gamma, name, t, t2, funs, gamma1, p1, p2, p3);
			}

	protected static Type_datatypeDecl createType_DataTypeDecl_def_None(Environment gamma, String name, String name2, EList<FunctionDecl> funs,
			Environment gamma1, Equality p1, Forall<FunctionDecl, Ex<FormalParameter, And<Equality, Equality>>> p2, Incrementally<FunctionDecl, Type_function> p3) {
				return new Type_DataTypeDecl_def_None(gamma, name, name2, funs, gamma1, p1, p2, p3);
			}

	protected static Type_datatype createType_NamedType(Environment gamma, String n, DataType u, DataTypeDecl t, Ex<List<FunctionDecl>, Equality> p) {
		return new Type_NamedType(gamma, n, u, t, p);
	}

	protected static Type_datatype createType_TupleType(Environment gamma, EList<FieldDecl> fields, EList<FieldDecl> fields2, Equality p1, Forall2<FieldDecl, FieldDecl, And<Equality, Ex<DataType, And<Equality, Ex<DataType, And<Equality, Type_datatype>>>>>> p2) {
		return new Type_TupleType(gamma, fields, fields2, p1, p2);
	}

	protected static Type_datatype createType_SequenceType(Environment gamma, DataType t, DataType t2, Type_datatype p) {
		return new Type_SequenceType(gamma, t, t2, p);
	}

	protected static Type_datatype createType_RangeType_trivial(Environment gamma, Expression min, Expression max, Expression_le p1) {
		return new Type_RangeType_trivial(gamma, min, max, p1);
	}

	protected static Type_datatype createType_BooleanType(Environment gamma) {
		return new Type_BooleanType(gamma);
	}

	protected static Type_function createType_FunctionDecl_Method(Environment gamma, String dataName, String dataTypeName, DataTypeDecl dataTypeDecl,
			DataType dataTypeReal, EList<FunctionDecl> dataTypeMethods, String name, EList<FormalParameter> params, EList<FormalParameter> params2, Environment gammap, DataType rettype, DataType rettype2,
			EList<Valuing> vals, Environment gammav, Expression retexpr, DataType tau, Environment gamma1, Equality p1, Type_datatype p2, And<Forall2<FormalParameter, FormalParameter, And<Equality, Ex<DataType, And<Equality, Ex<DataType, And<Equality, Type_datatype>>>>>>, Mutually<FormalParameter, True>> p3,
			Incrementally<Valuing, Type_valuing> p4, Type_expression p5, Subtype p6, Equality p7) {
				return new Type_FunctionDecl_Method(gamma, dataName, dataTypeName, dataTypeDecl, dataTypeReal, dataTypeMethods, name, params, params2, gammap, rettype, rettype2, vals, gammav, retexpr, tau, gamma1, p1, p2, p3, p4, p5, p6, p7);
			}

	protected static Type_expression_node createType_expression_IntegerValue(Environment gamma, BigInteger v) {
		return new Type_expression_IntegerValue(gamma, v);
	}

	protected static Type_expression createType_expression_and_type(Environment gamma, Expression e, DataType t, Type_expression_node p1,
			Check_datatype p2) {
				return new Type_expression_and_type(gamma, e, t, p1, p2);
			}

	protected static Expression_le createIn_Z(Expression l, BigInteger zl, Expression r, BigInteger zr, Equality p1, Equality p2,
			Equality p3) {
				return new In_Z(l, zl, r, zr, p1, p2, p3);
			}

	protected static Constexpr_expression createConstexpr_IntegerValue(BigInteger v) {
		return new Constexpr_IntegerValue(v);
	}

	protected static Constexpr_expression createConstexpr_Opposite(Expression e, Constexpr_expression p) {
		return new Constexpr_Opposite(e, p);
	}

	protected static Constexpr_expression createConstexpr_Same(Expression e, Constexpr_expression p) {
		return new Constexpr_Same(e, p);
	}

	protected static Constexpr_expression createConstexpr_Add(Expression l, Expression r, Constexpr_expression p1, Constexpr_expression p2) {
		return new Constexpr_Add(l, r, p1, p2);
	}

	protected static Constexpr_expression createConstexpr_Sub(Expression l, Expression r, Constexpr_expression p1, Constexpr_expression p2) {
		return new Constexpr_Sub(l, r, p1, p2);
	}

	protected static Constexpr_expression createConstexpr_Mul(Expression l, Expression r, Constexpr_expression p1, Constexpr_expression p2) {
		return new Constexpr_Mul(l, r, p1, p2);
	}

	protected static Constexpr_expression createConstexpr_Div(Expression l, Expression r, Constexpr_expression p1, Constexpr_expression p2) {
		return new Constexpr_Div(l, r, p1, p2);
	}

	protected static Constexpr_expression createConstexpr_Mod(Expression l, Expression r, Constexpr_expression p1, Constexpr_expression p2) {
		return new Constexpr_Mod(l, r, p1, p2);
	}

	protected static <T, P> Incrementally<T,P> createIncrementally_nil(Environment gamma) {
		return new Incrementally_nil<>(gamma);
	}

	protected static <T, P> Incrementally<T,P> createIncrementally_cons(Environment gamma, T x, Environment gammai, List<T> l,
			Environment gamma1, P p1, Incrementally<T,P> p2) {
				return new Incrementally_cons<T, P>(gamma, x, gammai, l, gamma1, p1, p2);
			}

	protected static <T, P> Simple_increment<T,P> createSimple_increment_step(String n, String c, Environment gamma, T x,
			Environment gamma1, Equality p1, P p2) {
				return new Simple_increment_step<>(n, c, gamma, x, gamma1, p1, p2);
			}

	protected static <T, P> Mutually<T,P> createMutually_all(Environment gamma, List<T> l, Environment gamma1, Equality p1, Equality p2,
			Forall<T,P> p3) {
				return new Mutually_all<>(gamma, l, gamma1, p1, p2, p3);
			}

	protected static <T, P> Mutually<T,P> createMutually_all_explicit(String name, String content, Environment gamma, List<T> l,
			Environment gamma1, Equality p1, Equality p2, Forall<T,P> p3) {
				return new Mutually_all_explicit<>(name, content, gamma, l, gamma1, p1, p2, p3);
			}

	protected static <T, P> Optionally<T,P> createOptionally_None(Environment gamma) {
		return new Optionally_None<>(gamma);
	}

	protected static <T, P> Optionally<T,P> createOptionally_Some(Environment gamma, T x, P p1) {
		return new Optionally_Some<>(gamma, x, p1);
	}

	protected static <A, B> And<A,B> createConj(A a, B b) {
		return new Conj<>(a, b);
	}

	protected static <T, P> Ex<T, P> createEx_intro(T t, P p) {
		return new Ex_intro<>(t, p);
	}

	protected static <T, P> Forall<T,P> createForall_nil() {
		return new Forall_nil<>();
	}

	protected static <T, P> Forall<T,P> createForall_cons(T t, P p1, Forall<T,P> p2) {
		return new Forall_cons<>(t, p1, p2);
	}

	protected static <A, B, P> Forall2<A,B,P> createForall2_nil() {
		return new Forall2_nil<>();
	}

	protected static <A, B, P> Forall2<A,B,P> createForall2_cons(A x, B y, P p1, Forall2<A,B,P> p2) {
		return new Forall2_cons<A, B, P>(x, y, p1, p2);
	}

	protected static Equality createReflexivity() {
		return new Eq_refl();
	}

	protected static True createI() {
		return new I();
	}

	protected static RangeType createRangeType(Expression min, Expression max) {
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

	protected static BooleanType createBooleanType() {
		return SosADLFactory.eINSTANCE.createBooleanType();
	}

	protected static NamedType createNamedType(String name) {
		NamedType t = SosADLFactory.eINSTANCE.createNamedType();
		t.setName(name);
		return t;
	}

	protected static Expression createIntegerValue(int v) {
		IntegerValue r = SosADLFactory.eINSTANCE.createIntegerValue();
		r.setAbsInt(v);
		return r;
	}

	protected static Expression createOpposite(Expression e) {
		UnaryExpression r = SosADLFactory.eINSTANCE.createUnaryExpression();
		r.setOp("-");
		r.setRight(copy(e));
		return r;
	}

	protected static Expression createBinaryExpression(Expression l, String o, Expression r) {
		BinaryExpression ret = SosADLFactory.eINSTANCE.createBinaryExpression();
		ret.setLeft(copy(l));
		ret.setOp(o);
		ret.setRight(copy(r));
		return ret;
	}

	protected static TupleType createTupleType(Iterable<FieldDecl> fields) {
		return createTupleType(fields.iterator());
	}

	private static TupleType createTupleType(Iterator<FieldDecl> fields) {
		TupleType ret = SosADLFactory.eINSTANCE.createTupleType();
		while(fields.hasNext()) {
			ret.getFields().add(copy(fields.next()));
		}
		return ret;
	}

	protected static TupleType createTupleType(Stream<FieldDecl> fields) {
		return createTupleType(fields.iterator());
	}

	protected static SequenceType createSequenceType(DataType t) {
		SequenceType ret = SosADLFactory.eINSTANCE.createSequenceType();
		ret.setType(copy(t));
		return ret;
	}

	protected static FieldDecl createFieldDecl(String name, DataType t) {
		FieldDecl f = SosADLFactory.eINSTANCE.createFieldDecl();
		f.setName(name);
		f.setType(copy(t));
		return f;
	}

	protected static FormalParameter createFormalParameter(String name, DataType t) {
		FormalParameter p = SosADLFactory.eINSTANCE.createFormalParameter();
		p.setName(name);
		p.setType(copy(t));
		return p;
	}

	protected static FunctionDecl createFunctionDecl(FormalParameter self, String name, List<FormalParameter> params, DataType ret, List<Valuing> vals,
			Expression b) {
				FunctionDecl f = SosADLFactory.eINSTANCE.createFunctionDecl();
				f.setData(copy(self));
				f.setName(name);
				f.getParameters().addAll(ListExtensions.map(params, TypeCheckerConstructors::copy));
				f.setType(copy(ret));
				f.getValuing().addAll(ListExtensions.map(vals, TypeCheckerConstructors::copy));
				f.setExpression(copy(b));
				return f;
			}

	protected static Type_expression_node createType_expression_Same(Environment gamma, Expression e, DataType tau, Expression min, Expression max,
			Type_expression p1, Subtype p2) {
				return new Type_expression_Same(gamma, e, tau, min, max, p1, p2);
			}

	protected static Type_expression_node createType_expression_Opposite(Environment gamma, Expression e, DataType tau, Expression min,
			Expression max, Type_expression p1, Subtype p2) {
				return new Type_expression_Opposite(gamma, e, tau, min, max, p1, p2);
			}

	protected static Type_expression_node createType_expression_Not(Environment gamma, Expression e, DataType tau, Type_expression p1,
			Subtype p2) {
				return new Type_expression_Not(gamma, e, tau, p1, p2);
			}

	protected static Type_expression_node createType_expression_Add(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
				return new Type_expression_Add(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
			}

	protected static Type_expression_node createType_expression_Sub(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
				return new Type_expression_Sub(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
			}

	protected static Type_expression_node createType_expression_Mul(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Expression min, Expression max, Type_expression p1, Subtype p2,
			Type_expression p3, Subtype p4, Expression_le p5, Expression_le p6, Expression_le p7, Expression_le p8, Expression_le p9, Expression_le pa,
			Expression_le pb, Expression_le pc) {
				return new Type_expression_Mul(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, min, max, p1, p2, p3, p4, p5, p6, p7, p8, p9, pa, pb, pc);
			}

	protected static Type_expression_node createType_expression_Div_pos(Environment gamma, Expression l, DataType l__tau, Expression l__min,
			Expression l__max, Expression r, DataType r__tau, Expression r__min, Expression r__max, Expression min, Expression max, Type_expression p1,
			Subtype p2, Type_expression p3, Subtype p4, Expression_le p5, Expression_le p6, Expression_le p7, Expression_le p8, Expression_le p9,
			Expression_le pa, Expression_le pb, Expression_le pc, Expression_le pd) {
				return new Type_expression_Div_pos(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, min, max, p1, p2, p3, p4, p5, p6, p7, p8, p9, pa, pb, pc, pd);
			}

	protected static Type_expression_node createType_expression_Div_neg(Environment gamma, Expression l, DataType l__tau, Expression l__min,
			Expression l__max, Expression r, DataType r__tau, Expression r__min, Expression r__max, Expression min, Expression max, Type_expression p1,
			Subtype p2, Type_expression p3, Subtype p4, Expression_le p5, Expression_le p6, Expression_le p7, Expression_le p8, Expression_le p9,
			Expression_le pa, Expression_le pb, Expression_le pc, Expression_le pd) {
				return new Type_expression_Div_neg(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, min, max, p1, p2, p3, p4, p5, p6, p7, p8, p9, pa, pb, pc, pd);
			}

	protected static Type_expression_node createType_expression_Mod(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Expression min, Expression max, Type_expression p1, Subtype p2,
			Type_expression p3, Subtype p4, Range_modulo_min p5, Range_modulo_max p6) {
				return new Type_expression_Mod(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, min, max, p1, p2, p3, p4, p5, p6);
			}

	protected static Type_expression_node createType_expression_Implies(Environment gamma, Expression l, DataType l__tau, Expression r,
			DataType r__tau, Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
				return new Type_expression_Implies(gamma, l, l__tau, r, r__tau, p1, p2, p3, p4);
			}

	protected static Type_expression_node createType_expression_Or(Environment gamma, Expression l, DataType l__tau, Expression r, DataType r__tau,
			Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
				return new Type_expression_Or(gamma, l, l__tau, r, r__tau, p1, p2, p3, p4);
			}

	protected static Type_expression_node createType_expression_Xor(Environment gamma, Expression l, DataType l__tau, Expression r, DataType r__tau,
			Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
				return new Type_expression_Xor(gamma, l, l__tau, r, r__tau, p1, p2, p3, p4);
			}

	protected static Type_expression_node createType_expression_And(Environment gamma, Expression l, DataType l__tau, Expression r, DataType r__tau,
			Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
				return new Type_expression_And(gamma, l, l__tau, r, r__tau, p1, p2, p3, p4);
			}

	protected static Type_expression_node createType_expression_Equal(Environment gamma, Expression l, DataType l__tau, Expression l__min,
			Expression l__max, Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2, Type_expression p3,
			Subtype p4) {
				return new Type_expression_Equal(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
			}

	protected static Type_expression_node createType_expression_Diff(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
				return new Type_expression_Diff(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
			}

	protected static Type_expression_node createType_expression_Lt(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
				return new Type_expression_Lt(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
			}

	protected static Type_expression_node createType_expression_Le(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
				return new Type_expression_Le(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
			}

	protected static Type_expression_node createType_expression_Gt(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
				return new Type_expression_Gt(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
			}

	protected static Type_expression_node createType_expression_Ge(Environment gamma, Expression l, DataType l__tau, Expression l__min, Expression l__max,
			Expression r, DataType r__tau, Expression r__min, Expression r__max, Type_expression p1, Subtype p2, Type_expression p3, Subtype p4) {
				return new Type_expression_Ge(gamma, l, l__tau, l__min, l__max, r, r__tau, r__min, r__max, p1, p2, p3, p4);
			}

	protected static Type_expression_node createType_expression_Ident(Environment gamma, String x, DataType tau, Equality p) {
		return new Type_expression_Ident(gamma, x, tau, p);
	}

	protected static Type_expression_node createType_expression_MethodCall(Environment gamma, Expression self, DataType t, DataTypeDecl typeDecl,
			DataType alpha, DataType tau, EList<FunctionDecl> methods, String name, EList<FormalParameter> formalparams, DataType ret, EList<Expression> params, Type_expression p1,
			Ex<BigInteger, Equality> p2, Subtype p4, Ex<BigInteger, And<Equality, And<Equality, And<Equality, Equality>>>> p5, Forall2<FormalParameter, Expression, Ex<DataType, And<Equality, Ex<DataType, And<Type_expression, Subtype>>>>> p6) {
				return new Type_expression_MethodCall(gamma, self, t, typeDecl, alpha, tau, methods, name, formalparams, ret, params, p1, p2, p4, p5, p6);
			}

	protected static Type_expression_node createType_expression_Tuple(Environment gamma, EList<TupleElement> elts, EList<FieldDecl> typ, Equality p1,
			Forall2<TupleElement, FieldDecl, Equality> p2, Forall2<TupleElement, FieldDecl, Ex<Expression, And<Equality, Ex<DataType, And<Equality, Type_expression>>>>> p3) {
				return new Type_expression_Tuple(gamma, elts, typ, p1, p2, p3);
			}

	protected static Type_expression_node createType_expression_Field(Environment gamma, Expression self, EList<FieldDecl> tau, String name,
			DataType tau__f, Type_expression p1, Equality p2) {
				return new Type_expression_Field(gamma, self, tau, name, tau__f, p1, p2);
			}

	protected static Type_expression_node createType_expression_Sequence(Environment gamma, EList<Expression> elts, DataType tau, Forall<Expression, Ex<DataType, And<Type_expression, Subtype>>> p1) {
		return new Type_expression_Sequence(gamma, elts, tau, p1);
	}

	protected static Range_modulo_min createRange_modulo_min_pos(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Expression min,
			Expression_le p1, Expression_le p2) {
				return new Range_modulo_min_pos(lmin, lmax, rmin, rmax, min, p1, p2);
			}

	protected static Range_modulo_min createRange_modulo_min_zero(Expression lmin, Expression lmax, Expression rmin, Expression rmax,
			Expression min, Expression_le p1, Expression_le p2) {
				return new Range_modulo_min_zero(lmin, lmax, rmin, rmax, min, p1, p2);
			}

	protected static Range_modulo_min createRange_modulo_min_neg(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Expression min,
			Expression_le p1, Expression_le p2) {
				return new Range_modulo_min_neg(lmin, lmax, rmin, rmax, min, p1, p2);
			}

	protected static Range_modulo_max createRange_modulo_max_pos(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Expression min,
			Expression_le p1, Expression_le p2) {
				return new Range_modulo_max_pos(lmin, lmax, rmin, rmax, min, p1, p2);
			}

	protected static Range_modulo_max createRange_modulo_max_zero(Expression lmin, Expression lmax, Expression rmin, Expression rmax,
			Expression min, Expression_le p1, Expression_le p2) {
				return new Range_modulo_max_zero(lmin, lmax, rmin, rmax, min, p1, p2);
			}

	protected static Range_modulo_max createRange_modulo_max_neg(Expression lmin, Expression lmax, Expression rmin, Expression rmax, Expression min,
			Expression_le p1, Expression_le p2) {
				return new Range_modulo_max_neg(lmin, lmax, rmin, rmax, min, p1, p2);
			}

	protected static Subtype createSubtype_refl(DataType t) {
		return new Subtype_refl(t);
	}

	protected static Subtype createSubtype_range(Expression lmi, Expression lma, Expression rmi, Expression rma, Expression_le p1,
			Expression_le p2) {
				return new Subtype_range(lmi, lma, rmi, rma, p1, p2);
			}

	protected static Subtype createSubtype_tuple(EList<FieldDecl> l, EList<FieldDecl> r, Forall<FieldDecl, Ex<String, And<Equality, Ex<DataType, And<Equality, Ex<DataType, And<Equality, Subtype>>>>>>> p1) {
		return new Subtype_tuple(l, r, p1);
	}

	protected static Subtype createSubtype_sequence(DataType l, DataType r, Subtype p1) {
		return new Subtype_sequence(l, r, p1);
	}

	protected static Check_datatype createCheck_NamedType(String n) {
		return new Check_NamedType(n);
	}

	protected static Check_datatype createCheck_TupleType(EList<FieldDecl> fields, Equality p1, Forall<FieldDecl, Ex<DataType, And<Equality, Check_datatype>>> p2) {
		return new Check_TupleType(fields, p1, p2);
	}

	protected static Check_datatype createCheck_SequenceType(DataType t, Check_datatype p1) {
		return new Check_SequenceType(t, p1);
	}

	protected static Check_datatype createCheck_RangeType_trivial(Expression min, Expression max, Expression_le p1) {
		return new Check_RangeType_trivial(min, max, p1);
	}

	protected static Check_datatype createCheck_BooleanType() {
		return new Check_BooleanType();
	}

	private static <T extends EObject> T copy(T x) {
		return TypeInferenceSolver.copy(x);
	}

}