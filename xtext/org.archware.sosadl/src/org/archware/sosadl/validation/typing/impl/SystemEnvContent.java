package org.archware.sosadl.validation.typing.impl;

import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.validation.typing.EnvContent;

public class SystemEnvContent implements EnvContent {
	private final SystemDecl systemDecl;
	
	public SystemEnvContent(SystemDecl dtd) {
		this.systemDecl = dtd;
	}
	
	public SystemDecl getSystemDecl() {
		return this.systemDecl;
	}
}
