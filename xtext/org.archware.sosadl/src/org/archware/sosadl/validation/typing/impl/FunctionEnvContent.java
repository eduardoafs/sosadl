package org.archware.sosadl.validation.typing.impl;

import org.archware.sosadl.sosADL.FunctionDecl;
import org.archware.sosadl.validation.typing.EnvContent;
import org.archware.sosadl.validation.typing.proof.CoqConstructor;
import org.archware.sosadl.validation.typing.proof.CoqTransient;
import org.archware.sosadl.validation.typing.proof.Mandatory;
import org.eclipse.emf.ecore.EObject;

@CoqConstructor("EFunction")
public class FunctionEnvContent implements EnvContent {
	@CoqTransient
	private final EObject binder;

	@Mandatory
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
