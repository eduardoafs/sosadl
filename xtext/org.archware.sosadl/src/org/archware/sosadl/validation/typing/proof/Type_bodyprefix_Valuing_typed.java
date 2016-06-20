package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.validation.typing.Environment;

public class Type_bodyprefix_Valuing_typed<T extends ProofTerm> implements Type_bodyprefix<T> {
	@Eluded
	private final Object r = null;

	@Mandatory
	private final Environment gamma;

	@Mandatory
	private final String x;

	@Mandatory
	private final Expression e;

	@Mandatory
	private final DataType tau;

	@Mandatory
	private final DataType tau__e;

	@Mandatory
	private final Type_expression p1;
	
	@Mandatory
	private final Subtype p2;

	@Mandatory
	private final T p3;

	public Type_bodyprefix_Valuing_typed(Environment gamma, String x, Expression e, DataType tau, DataType tau__e,
			Type_expression p1, Subtype p2, T p3) {
		super();
		this.gamma = gamma;
		this.x = x;
		this.e = e;
		this.tau = tau;
		this.tau__e = tau__e;
		this.p1 = p1;
		this.p2 = p2;
		this.p3 = p3;
	}

	public Object getR() {
		return r;
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

	public DataType getTau() {
		return tau;
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

	public T getP3() {
		return p3;
	}

}
