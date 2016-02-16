package org.archware.sosadl.validation;

import java.util.function.Supplier;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.BinaryExpression;
import org.archware.sosadl.validation.typing.Environment;
import org.archware.sosadl.validation.typing.proof.Subtype;
import org.archware.sosadl.validation.typing.proof.Type_expression;
import org.archware.sosadl.validation.typing.proof.Type_expression_node;

public class BinaryTypeInfo<L extends DataType, R extends DataType> {
	public final String operator;
	public final Class<L> lClass;
	public final String lLabel;
	public final Supplier<L> lIfNone;
	public final Class<R> rClass;
	public final String rLabel;
	public final Supplier<R> rIfNone;
	public final HexaFunction<Environment, BinaryExpression, Pair<Type_expression, DataType>, Pair<Subtype, L>, Pair<Type_expression, DataType>, Pair<Subtype, R>, Type_expression_node> createProofTerm;
	public final HexaFunction<Environment, BinaryExpression, Pair<Type_expression, DataType>, Pair<Subtype, L>, Pair<Type_expression, DataType>, Pair<Subtype, R>, DataType> createType;

	public BinaryTypeInfo(String operator, Class<L> lClass, String lLabel, Supplier<L> lIfNone, Class<R> rClass,
			String rLabel, Supplier<R> rIfNone,
			HexaFunction<Environment, BinaryExpression, Pair<Type_expression, DataType>, Pair<Subtype, L>, Pair<Type_expression, DataType>, Pair<Subtype, R>, Type_expression_node> createProofTerm,
			HexaFunction<Environment, BinaryExpression, Pair<Type_expression, DataType>, Pair<Subtype, L>, Pair<Type_expression, DataType>, Pair<Subtype, R>, DataType> createType) {
		super();
		this.operator = operator;
		this.lClass = lClass;
		this.lLabel = lLabel;
		this.lIfNone = lIfNone;
		this.rClass = rClass;
		this.rLabel = rLabel;
		this.rIfNone = rIfNone;
		this.createProofTerm = createProofTerm;
		this.createType = createType;
	}

	public String getOperator() {
		return operator;
	}

	public Class<L> getlClass() {
		return lClass;
	}

	public String getlLabel() {
		return lLabel;
	}

	public Supplier<L> getlIfNone() {
		return lIfNone;
	}

	public Class<R> getrClass() {
		return rClass;
	}

	public String getrLabel() {
		return rLabel;
	}

	public Supplier<R> getrIfNone() {
		return rIfNone;
	}

	public HexaFunction<Environment, BinaryExpression, Pair<Type_expression, DataType>, Pair<Subtype, L>, Pair<Type_expression, DataType>, Pair<Subtype, R>, Type_expression_node> getCreateProofTerm() {
		return createProofTerm;
	}

	public HexaFunction<Environment, BinaryExpression, Pair<Type_expression, DataType>, Pair<Subtype, L>, Pair<Type_expression, DataType>, Pair<Subtype, R>, DataType> getCreateType() {
		return createType;
	}

}