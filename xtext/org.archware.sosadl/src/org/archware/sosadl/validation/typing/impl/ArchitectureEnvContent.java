package org.archware.sosadl.validation.typing.impl;

import org.archware.sosadl.sosADL.ArchitectureDecl;
import org.archware.sosadl.validation.typing.EnvContent;

public class ArchitectureEnvContent implements EnvContent {
	private final ArchitectureDecl architectureDecl;
	
	public ArchitectureEnvContent(ArchitectureDecl dtd) {
		this.architectureDecl = dtd;
	}
	
	public ArchitectureDecl getMediatorDecl() {
		return this.architectureDecl;
	}
}
