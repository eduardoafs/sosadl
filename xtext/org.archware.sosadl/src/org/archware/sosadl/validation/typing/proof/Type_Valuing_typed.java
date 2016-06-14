package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.validation.typing.Environment;

public class Type_Valuing_typed implements Type_valuing {
	@Mandatory
	private final Environment gamma;

	@Mandatory
	private final String x;

	@Mandatory
	private final DataType tau;

	@Mandatory
	private final Expression e;

	@Mandatory
	private final DataType tau__e;

	@Mandatory
	private final Type_expression p1;

	@Mandatory
	private final Subtype p2;

	public Type_Valuing_typed(Environment gamma, String x, DataType tau, Expression e, DataType tau__e,
			Type_expression p1, Subtype p2) {
		super();
		this.gamma = gamma;
		this.x = x;
		this.tau = tau;
		this.e = e;
		this.tau__e = tau__e;
		this.p1 = p1;
		this.p2 = p2;
	}

	public Environment getGamma() {
		return gamma;
	}

	public String getX() {
		return x;
	}

	public DataType getTau() {
		return tau;
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

	public Subtype getP2() {
		return p2;
	}

}
