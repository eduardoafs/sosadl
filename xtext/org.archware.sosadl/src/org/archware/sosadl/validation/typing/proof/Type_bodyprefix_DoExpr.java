package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.validation.typing.Environment;

public class Type_bodyprefix_DoExpr<T extends ProofTerm> implements Type_bodyprefix<T> {
	@Eluded
	private final Object r = null;
	
	@Mandatory
	private final Environment gamma;

	@Mandatory
	private final Expression e;

	@Mandatory
	private final DataType tau;

	@Mandatory
	private final Type_expression p1;

	@Mandatory
	private final T p2;

	public Type_bodyprefix_DoExpr(Environment gamma, Expression e, DataType tau, Type_expression p1, T p2) {
		super();
		this.gamma = gamma;
		this.e = e;
		this.tau = tau;
		this.p1 = p1;
		this.p2 = p2;
	}
	
	public Object getR() {
		return r;
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

	public T getP2() {
		return p2;
	}

}
