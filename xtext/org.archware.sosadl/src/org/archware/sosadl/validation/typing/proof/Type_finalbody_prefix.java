package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.BehaviorStatement;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_finalbody_prefix implements Type_finalbody {
	@Mandatory
	private final Environment gamma;
	
	@Mandatory
	private final BehaviorStatement s;
	
	private final EList<BehaviorStatement> l;
	
	@Mandatory private final Type_bodyprefix<Type_finalbody> p1;

	public Type_finalbody_prefix(Environment gamma, BehaviorStatement s, EList<BehaviorStatement> l,
			Type_bodyprefix<Type_finalbody> p1) {
		super();
		this.gamma = gamma;
		this.s = s;
		this.l = l;
		this.p1 = p1;
	}

	public Environment getGamma() {
		return gamma;
	}

	public BehaviorStatement getS() {
		return s;
	}

	public EList<BehaviorStatement> getL() {
		return l;
	}

	public Type_bodyprefix<Type_finalbody> getP1() {
		return p1;
	}

}
