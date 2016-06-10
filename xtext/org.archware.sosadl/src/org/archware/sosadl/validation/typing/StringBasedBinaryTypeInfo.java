package org.archware.sosadl.validation.typing;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.validation.typing.proof.Type_expression_node;

public abstract class StringBasedBinaryTypeInfo<P extends Type_expression_node>
		implements BinaryTypeInfo2<P> {
	private final String operator;

	public StringBasedBinaryTypeInfo(String operator) {
		this.operator = operator;
	}

	@Override
	public boolean isCandidate(String operator, DataType left, DataType right) {
		return this.operator.equals(operator);
	}
}