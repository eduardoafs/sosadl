package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.validation.typing.Environment;

public class Type_finalbody_Done implements Type_finalbody {
	@Mandatory
	private final Environment gamma;

	public Type_finalbody_Done(Environment gamma) {
		super();
		this.gamma = gamma;
	}

	public Environment getGamma() {
		return gamma;
	}

}
