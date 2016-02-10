package org.archware.sosadl.validation.typing.impl;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.validation.typing.EnvContent;
import org.eclipse.emf.ecore.EObject;

public class VariableEnvContent implements EnvContent {
	private final EObject binder;
	
	private final DataType type;

	public VariableEnvContent(EObject binder, DataType type) {
		super();
		this.binder = binder;
		this.type = type;
	}

	public EObject getBinder() {
		return binder;
	}

	public DataType getType() {
		return type;
	}

}
