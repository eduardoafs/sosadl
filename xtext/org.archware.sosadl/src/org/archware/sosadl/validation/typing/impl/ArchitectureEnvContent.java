package org.archware.sosadl.validation.typing.impl;

import org.archware.sosadl.sosADL.ArchitectureDecl;
import org.archware.sosadl.validation.typing.EnvContent;
import org.archware.sosadl.validation.typing.proof.CoqConstructor;
import org.archware.sosadl.validation.typing.proof.Mandatory;

@CoqConstructor("EArchitecture")
public class ArchitectureEnvContent implements EnvContent {
	@Mandatory
	private final ArchitectureDecl architectureDecl;

	public ArchitectureEnvContent(ArchitectureDecl dtd) {
		this.architectureDecl = dtd;
	}

	public ArchitectureDecl getMediatorDecl() {
		return this.architectureDecl;
	}
}
