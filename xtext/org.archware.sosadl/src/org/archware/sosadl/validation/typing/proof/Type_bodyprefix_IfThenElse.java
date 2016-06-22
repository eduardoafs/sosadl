package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.Behavior;
import org.archware.sosadl.sosADL.BehaviorStatement;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_bodyprefix_IfThenElse implements Type_bodyprefix {

	@Mandatory
	private final Environment gamma;

	@Mandatory
	private final Expression c;

	@Mandatory
	private final Environment gammat;

	private final EList<BehaviorStatement> t;

	private final Behavior oe;

	@Mandatory
	private final Type_expression p1;

	@Mandatory
	private final Condition_true p2;

	@Mandatory
	private final Type_nonfinalbody p3;

	@Mandatory
	private final Optionally<Behavior, Ex<Environment, And<Condition_false, Type_nonfinalbody>>> p4;

	public Type_bodyprefix_IfThenElse(Environment gamma, Expression c, Environment gammat, EList<BehaviorStatement> t,
			Behavior oe, Type_expression p1, Condition_true p2, Type_nonfinalbody p3,
			Optionally<Behavior, Ex<Environment, And<Condition_false, Type_nonfinalbody>>> p4) {
		super();
		this.gamma = gamma;
		this.c = c;
		this.gammat = gammat;
		this.t = t;
		this.oe = oe;
		this.p1 = p1;
		this.p2 = p2;
		this.p3 = p3;
		this.p4 = p4;
	}

	public Environment getGamma() {
		return gamma;
	}

	public Expression getC() {
		return c;
	}

	public Environment getGammat() {
		return gammat;
	}

	public EList<BehaviorStatement> getT() {
		return t;
	}

	public Behavior getOe() {
		return oe;
	}

	public Type_expression getP1() {
		return p1;
	}

	public Condition_true getP2() {
		return p2;
	}

	public Type_nonfinalbody getP3() {
		return p3;
	}

	public Optionally<Behavior, Ex<Environment, And<Condition_false, Type_nonfinalbody>>> getP4() {
		return p4;
	}

}
