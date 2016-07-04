package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.validation.typing.Environment;

public class Type_finalprotocol_Done implements Type_finalprotocol {
	@Mandatory
	private final Environment gamma;

	public Type_finalprotocol_Done(Environment gamma) {
		super();
		this.gamma = gamma;
	}

	public Environment getGamma() {
		return gamma;
	}

}
