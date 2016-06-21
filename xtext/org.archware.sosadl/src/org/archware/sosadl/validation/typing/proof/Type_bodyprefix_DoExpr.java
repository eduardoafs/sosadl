package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.validation.typing.Environment;

public class Type_bodyprefix_DoExpr implements Type_bodyprefix {
	
	@Mandatory
	private final Environment gamma;

	@Mandatory
	private final Expression e;

	@Mandatory
	private final DataType tau;

	@Mandatory
	private final Type_expression p1;

	public Type_bodyprefix_DoExpr(Environment gamma, Expression e, DataType tau, Type_expression p1) {
		super();
		this.gamma = gamma;
		this.e = e;
		this.tau = tau;
		this.p1 = p1;
	}

	public Environment getGamma() {
		return gamma;
	}

	public Expression getE() {
		return e;
	}

	public DataType getTau() {
		return tau;
	}

	public Type_expression getP1() {
		return p1;
	}

}
