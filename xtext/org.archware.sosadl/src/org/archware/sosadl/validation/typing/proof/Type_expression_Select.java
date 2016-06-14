package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.validation.typing.Environment;

public class Type_expression_Select implements Type_expression_node {
	@Mandatory
	private final Environment gamma;

	@Mandatory
	private final Expression obj;

	@Mandatory
	private final DataType tau;

	@Mandatory
	private final String x;

	@Mandatory
	private final Expression e;

	@Mandatory
	private final Type_expression p1;

	@Mandatory
	private final Type_expression p2;

	public Type_expression_Select(Environment gamma, Expression obj, DataType tau, String x, Expression e,
			Type_expression p1, Type_expression p2) {
		super();
		this.gamma = gamma;
		this.obj = obj;
		this.tau = tau;
		this.x = x;
		this.e = e;
		this.p1 = p1;
		this.p2 = p2;
	}

	public Environment getGamma() {
		return gamma;
	}

	public Expression getObj() {
		return obj;
	}

	public DataType getTau() {
		return tau;
	}

	public String getX() {
		return x;
	}

	public Expression getE() {
		return e;
	}

	public Type_expression getP1() {
		return p1;
	}

	public Type_expression getP2() {
		return p2;
	}

}
