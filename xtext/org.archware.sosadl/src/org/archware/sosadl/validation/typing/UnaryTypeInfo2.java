package org.archware.sosadl.validation.typing;

import java.util.Optional;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.UnaryExpression;
import org.archware.sosadl.validation.typing.proof.Type_expression;
import org.archware.sosadl.validation.typing.proof.Type_expression_node;

public interface UnaryTypeInfo2<P extends Type_expression_node> {
	boolean isCandidate(String oprator, DataType operand);

	Optional<DataType> immediateType(UnaryExpression e, DataType operand);

	Type_expression_node prove(Environment gamma, UnaryExpression e, Type_expression pOperand, DataType tOperand);
}