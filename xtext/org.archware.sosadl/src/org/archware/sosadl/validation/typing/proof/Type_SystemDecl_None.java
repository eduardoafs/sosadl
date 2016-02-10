package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.BehaviorDecl;
import org.archware.sosadl.validation.typing.Environment;

public class Type_SystemDecl_None implements Type_systemblock {
	@Mandatory private final Environment gamma;
	
	@Mandatory private final String name;
	
	@Mandatory private final BehaviorDecl bhv;
	
	@Mandatory private final Type_behavior p;

	public Type_SystemDecl_None(Environment gamma, String name, BehaviorDecl bhv, Type_behavior p) {
		super();
		this.gamma = gamma;
		this.name = name;
		this.bhv = bhv;
		this.p = p;
	}

	public Environment getGamma() {
		return gamma;
	}

	public String getName() {
		return name;
	}

	public BehaviorDecl getBhv() {
		return bhv;
	}

	public Type_behavior getP() {
		return p;
	}

}
