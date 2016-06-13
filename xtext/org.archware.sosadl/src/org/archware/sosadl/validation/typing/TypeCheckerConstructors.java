package org.archware.sosadl.validation.typing;

import java.util.Iterator;
import java.util.List;
import java.util.stream.Stream;

import org.archware.sosadl.sosADL.BinaryExpression;
import org.archware.sosadl.sosADL.BooleanType;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.FieldDecl;
import org.archware.sosadl.sosADL.FormalParameter;
import org.archware.sosadl.sosADL.FunctionDecl;
import org.archware.sosadl.sosADL.IntegerValue;
import org.archware.sosadl.sosADL.NamedType;
import org.archware.sosadl.sosADL.RangeType;
import org.archware.sosadl.sosADL.SequenceType;
import org.archware.sosadl.sosADL.SosADLFactory;
import org.archware.sosadl.sosADL.TupleType;
import org.archware.sosadl.sosADL.UnaryExpression;
import org.archware.sosadl.sosADL.Valuing;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.xbase.lib.ListExtensions;

public class TypeCheckerConstructors extends TypeCheckerAnnotate {

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
		while (fields.hasNext()) {
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

	protected static FunctionDecl createFunctionDecl(FormalParameter self, String name, List<FormalParameter> params,
			DataType ret, List<Valuing> vals, Expression b) {
		FunctionDecl f = SosADLFactory.eINSTANCE.createFunctionDecl();
		f.setData(copy(self));
		f.setName(name);
		f.getParameters().addAll(ListExtensions.map(params, TypeCheckerConstructors::copy));
		f.setType(copy(ret));
		f.getValuing().addAll(ListExtensions.map(vals, TypeCheckerConstructors::copy));
		f.setExpression(copy(b));
		return f;
	}

	private static <T extends EObject> T copy(T x) {
		return TypeInferenceSolver.copy(x);
	}

}