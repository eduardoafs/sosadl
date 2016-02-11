package org.archware.sosadl.validation.typing.impl;

import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.validation.typing.EnvContent;

public class MediatorEnvContent implements EnvContent {
	private final MediatorDecl mediatorDecl;
	
	public MediatorEnvContent(MediatorDecl dtd) {
		this.mediatorDecl = dtd;
	}
	
	public MediatorDecl getMediatorDecl() {
		return this.mediatorDecl;
	}
}
