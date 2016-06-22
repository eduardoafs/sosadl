package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.BehaviorStatement;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_bodyprefix_ForEach implements Type_bodyprefix {
	@Mandatory
	private final Environment gamma;

	@Mandatory
	private final String x;

	@Mandatory
	private final Expression vals;

	@Mandatory
	private final DataType tau;

	@Mandatory
	private final DataType tau__x;

	private final EList<BehaviorStatement> b;

	@Mandatory
	private final Type_expression p1;

	@Mandatory
	private final Type_nonfinalbody p2;

	@Mandatory
	private final Subtype p3;

	public Type_bodyprefix_ForEach(Environment gamma, String x, Expression vals, DataType tau, DataType tau__x,
			EList<BehaviorStatement> b, Type_expression p1, Type_nonfinalbody p2, Subtype p3) {
		super();
		this.gamma = gamma;
		this.x = x;
		this.vals = vals;
		this.tau = tau;
		this.tau__x = tau__x;
		this.b = b;
		this.p1 = p1;
		this.p2 = p2;
		this.p3 = p3;
	}

	public Environment getGamma() {
		return gamma;
	}

	public String getX() {
		return x;
	}

	public Expression getVals() {
		return vals;
	}

	public DataType getTau() {
		return tau;
	}
	
	public DataType getTau__x() {
		return tau__x;
	}

	public EList<BehaviorStatement> getB() {
		return b;
	}

	public Type_expression getP1() {
		return p1;
	}

	public Type_nonfinalbody getP2() {
		return p2;
	}
	
	public Subtype getP3() {
		return p3;
	}

}
