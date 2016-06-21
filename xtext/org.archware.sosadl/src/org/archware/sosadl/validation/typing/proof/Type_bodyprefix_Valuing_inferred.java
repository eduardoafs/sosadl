package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.validation.typing.Environment;

public class Type_bodyprefix_Valuing_inferred implements Type_bodyprefix {

	@Mandatory
	private final Environment gamma;

	@Mandatory
	private final String x;

	@Mandatory
	private final Expression e;

	@Mandatory
	private final DataType tau__e;

	@Mandatory
	private final Type_expression p1;

	public Type_bodyprefix_Valuing_inferred(Environment gamma, String x, Expression e, DataType tau__e,
			Type_expression p1) {
		super();
		this.gamma = gamma;
		this.x = x;
		this.e = e;
		this.tau__e = tau__e;
		this.p1 = p1;
	}

	public Environment getGamma() {
		return gamma;
	}

	public String getX() {
		return x;
	}

	public Expression getE() {
		return e;
	}

	public DataType getTau__e() {
		return tau__e;
	}

	public Type_expression getP1() {
		return p1;
	}

}
