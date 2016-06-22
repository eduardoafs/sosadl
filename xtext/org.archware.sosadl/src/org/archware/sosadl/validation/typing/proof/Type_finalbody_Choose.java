package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.Behavior;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_finalbody_Choose implements Type_finalbody {
	@Mandatory
	private final Environment gamma;

	private final EList<Behavior> branches;

	@Mandatory
	private final Forall<Behavior, Type_finalbody> p1;

	public Type_finalbody_Choose(Environment gamma, EList<Behavior> branches, Forall<Behavior, Type_finalbody> p1) {
		super();
		this.gamma = gamma;
		this.branches = branches;
		this.p1 = p1;
	}

	public Environment getGamma() {
		return gamma;
	}

	public EList<Behavior> getBranches() {
		return branches;
	}

	public Forall<Behavior, Type_finalbody> getP1() {
		return p1;
	}

}
