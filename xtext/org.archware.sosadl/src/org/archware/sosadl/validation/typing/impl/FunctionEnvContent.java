package org.archware.sosadl.validation.typing.impl;

import org.archware.sosadl.sosADL.FunctionDecl;
import org.archware.sosadl.validation.typing.EnvContent;

public class FunctionEnvContent implements EnvContent {
	private final FunctionDecl function;

	public FunctionEnvContent(FunctionDecl function) {
		super();
		this.function = function;
	}

	public FunctionDecl getFunction() {
		return function;
	}

}
