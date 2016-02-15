package org.archware.sosadl.validation.typing.proof;

import java.math.BigInteger;

import org.archware.sosadl.validation.typing.Environment;

public class Type_expression_IntegerValue implements Type_expression {
	@Mandatory private final Environment gamma;
	
	@Mandatory private final BigInteger v;
	
	@Mandatory private final Type_datatype p;

	public Type_expression_IntegerValue(Environment gamma, BigInteger v, Type_datatype p) {
		super();
		this.gamma = gamma;
		this.v = v;
		this.p = p;
	}

	public Environment getGamma() {
		return gamma;
	}

	public BigInteger getV() {
		return v;
	}

	public Type_datatype getP() {
		return p;
	}
}
