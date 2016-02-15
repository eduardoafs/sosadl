package org.archware.sosadl.validation.typing.impl;

import org.archware.sosadl.sosADL.DataTypeDecl;
import org.archware.sosadl.sosADL.FunctionDecl;
import org.archware.sosadl.validation.typing.EnvContent;
import org.eclipse.emf.common.util.EList;

public class TypeEnvContent implements EnvContent {
	private final DataTypeDecl dataTypeDecl;
	
	private final EList<FunctionDecl> methods;
	
	public TypeEnvContent(DataTypeDecl dtd, EList<FunctionDecl> methods) {
		this.dataTypeDecl = dtd;
		this.methods = methods;
	}
	
	public DataTypeDecl getDataTypeDecl() {
		return this.dataTypeDecl;
	}

	public EList<FunctionDecl> getMethods() {
		return this.methods;
	}
}
