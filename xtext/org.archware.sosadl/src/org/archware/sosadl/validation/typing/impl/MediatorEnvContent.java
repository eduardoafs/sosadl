package org.archware.sosadl.validation.typing.impl;

import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.validation.typing.EnvContent;
import org.archware.sosadl.validation.typing.proof.CoqConstructor;
import org.archware.sosadl.validation.typing.proof.Mandatory;

@CoqConstructor("EMediator")
public class MediatorEnvContent implements EnvContent {
	@Mandatory
	private final MediatorDecl mediatorDecl;

	public MediatorEnvContent(MediatorDecl dtd) {
		this.mediatorDecl = dtd;
	}

	public MediatorDecl getMediatorDecl() {
		return this.mediatorDecl;
	}
}
