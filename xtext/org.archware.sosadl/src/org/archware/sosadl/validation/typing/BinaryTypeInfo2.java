package org.archware.sosadl.validation.typing;

import java.util.Optional;

import org.archware.sosadl.sosADL.BinaryExpression;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.validation.typing.proof.Type_expression;
import org.archware.sosadl.validation.typing.proof.Type_expression_node;

public interface BinaryTypeInfo2<P extends Type_expression_node> {
	boolean isCandidate(String oprator, DataType left, DataType right);

	Optional<DataType> immediateType(BinaryExpression e, DataType left, DataType right);

	P prove(Environment gamma, BinaryExpression e, Type_expression pLeft, DataType tLeft, Type_expression pRight, DataType tRight, DataType r);
}