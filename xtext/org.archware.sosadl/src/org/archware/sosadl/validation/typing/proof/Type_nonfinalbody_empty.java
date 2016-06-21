package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.validation.typing.Environment;

public class Type_nonfinalbody_empty implements Type_nonfinalbody {
	@Mandatory
	private final Environment gamma;

	public Type_nonfinalbody_empty(Environment gamma) {
		super();
		this.gamma = gamma;
	}

	public Environment getGamma() {
		return gamma;
	}

}
