package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.validation.typing.Environment;

public class Type_nonfinalprotocol_empty implements Type_nonfinalprotocol {
	@Mandatory
	private final Environment gamma;

	public Type_nonfinalprotocol_empty(Environment gamma) {
		super();
		this.gamma = gamma;
	}

	public Environment getGamma() {
		return gamma;
	}

}
