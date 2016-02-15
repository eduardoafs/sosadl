package org.archware.sosadl.validation.typing.proof;

import java.math.BigInteger;

import org.archware.sosadl.validation.typing.Environment;

public class Type_expression_IntegerValue implements Type_expression {
	@Mandatory private final Environment gamma;
	
	@Mandatory private final BigInteger v;

	public Type_expression_IntegerValue(Environment gamma, BigInteger v) {
		super();
		this.gamma = gamma;
		this.v = v;
	}

	public Environment getGamma() {
		return gamma;
	}

	public BigInteger getV() {
		return v;
	}

}
