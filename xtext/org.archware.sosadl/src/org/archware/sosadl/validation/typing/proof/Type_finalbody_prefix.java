package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.BehaviorStatement;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_finalbody_prefix implements Type_finalbody {
	@Mandatory
	private final Environment gamma;

	@Mandatory
	private final BehaviorStatement s;

	@Mandatory
	private final Environment gamma1;

	private final EList<BehaviorStatement> l;

	@Mandatory
	private final Type_bodyprefix p1;

	@Mandatory
	private final Type_finalbody p2;

	public Type_finalbody_prefix(Environment gamma, BehaviorStatement s, Environment gamma1, EList<BehaviorStatement> l,
			Type_bodyprefix p1, Type_finalbody p2) {
		super();
		this.gamma = gamma;
		this.s = s;
		this.gamma1 = gamma1;
		this.l = l;
		this.p1 = p1;
		this.p2 = p2;
	}

	public Environment getGamma() {
		return gamma;
	}

	public BehaviorStatement getS() {
		return s;
	}

	public Environment getGamma1() {
		return gamma1;
	}

	public EList<BehaviorStatement> getL() {
		return l;
	}

	public Type_bodyprefix getP1() {
		return p1;
	}

	public Type_finalbody getP2() {
		return p2;
	}

}
