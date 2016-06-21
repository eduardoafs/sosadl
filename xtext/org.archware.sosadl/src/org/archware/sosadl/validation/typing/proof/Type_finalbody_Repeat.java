package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.BehaviorStatement;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_finalbody_Repeat implements Type_finalbody {
	@Mandatory
	private final Environment gamma;

	private final EList<BehaviorStatement> b;

	@Mandatory
	private final Type_nonfinalbody p1;

	public Type_finalbody_Repeat(Environment gamma, EList<BehaviorStatement> b, Type_nonfinalbody p1) {
		super();
		this.gamma = gamma;
		this.b = b;
		this.p1 = p1;
	}

	public Environment getGamma() {
		return gamma;
	}

	public EList<BehaviorStatement> getB() {
		return b;
	}

	public Type_nonfinalbody getP1() {
		return p1;
	}

}
