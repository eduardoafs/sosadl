package org.archware.sosadl.validation.typing.impl;

import org.archware.sosadl.sosADL.FunctionDecl;
import org.archware.sosadl.validation.typing.EnvContent;
import org.eclipse.emf.ecore.EObject;

public class FunctionEnvContent implements EnvContent {
	private final EObject binder;

	private final FunctionDecl function;
	
	public FunctionEnvContent(EObject binder, FunctionDecl function) {
		super();
		this.binder = binder;
		this.function = function;
	}
	
	public EObject getBinder() {
		return binder;
	}

	public FunctionDecl getFunction() {
		return function;
	}

}
