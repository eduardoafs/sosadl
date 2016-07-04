package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.Protocol;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_finalprotocol_Choose implements Type_finalprotocol {
	@Mandatory
	private final Environment gamma;

	private final EList<Protocol> branches;

	@Mandatory
	private final Forall<Protocol, Type_finalprotocol> p1;

	public Type_finalprotocol_Choose(Environment gamma, EList<Protocol> branches,
			Forall<Protocol, Type_finalprotocol> p1) {
		super();
		this.gamma = gamma;
		this.branches = branches;
		this.p1 = p1;
	}

	public Environment getGamma() {
		return gamma;
	}

	public EList<Protocol> getBranches() {
		return branches;
	}

	public Forall<Protocol, Type_finalprotocol> getP1() {
		return p1;
	}

}
