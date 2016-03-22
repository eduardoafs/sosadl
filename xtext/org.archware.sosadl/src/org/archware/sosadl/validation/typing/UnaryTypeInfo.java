package org.archware.sosadl.validation.typing;

import java.util.function.Supplier;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.UnaryExpression;
import org.archware.sosadl.validation.typing.proof.Subtype;
import org.archware.sosadl.validation.typing.proof.Type_expression;
import org.archware.sosadl.validation.typing.proof.Type_expression_node;
import org.archware.utils.Pair;
import org.archware.utils.TetraFunction;

public class UnaryTypeInfo<T extends DataType> {
	public final String operator;
	public final Class<T> clazz;
	public final String label;
	public final Supplier<T> ifNone;
	public final TetraFunction<Environment, UnaryExpression, Pair<Type_expression, DataType>, Pair<Subtype, T>, Type_expression_node> createProofTerm;
	public final TetraFunction<Environment, UnaryExpression, Pair<Type_expression, DataType>, Pair<Subtype, T>, DataType> createType;

	public UnaryTypeInfo(String operator, Class<T> clazz, String label, Supplier<T> ifNone,
			TetraFunction<Environment, UnaryExpression, Pair<Type_expression, DataType>, Pair<Subtype, T>, Type_expression_node> createProofTerm,
			TetraFunction<Environment, UnaryExpression, Pair<Type_expression, DataType>, Pair<Subtype, T>, DataType> createType) {
		super();
		this.operator = operator;
		this.clazz = clazz;
		this.label = label;
		this.ifNone = ifNone;
		this.createProofTerm = createProofTerm;
		this.createType = createType;
	}
	public String getOperator() {
		return operator;
	}
	public Class<T> getClazz() {
		return clazz;
	}
	public String getLabel() {
		return label;
	}
	public Supplier<T> getIfNone() {
		return ifNone;
	}
	public TetraFunction<Environment, UnaryExpression, Pair<Type_expression, DataType>, Pair<Subtype, T>, Type_expression_node> getCreateProofTerm() {
		return createProofTerm;
	}
	public TetraFunction<Environment, UnaryExpression, Pair<Type_expression, DataType>, Pair<Subtype, T>, DataType> getCreateType() {
		return createType;
	}

}