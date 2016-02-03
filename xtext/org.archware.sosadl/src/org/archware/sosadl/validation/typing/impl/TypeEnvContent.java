package org.archware.sosadl.validation.typing.impl;

import org.archware.sosadl.sosADL.DataTypeDecl;
import org.archware.sosadl.validation.typing.EnvContent;

public class TypeEnvContent implements EnvContent {
	private final DataTypeDecl dataTypeDecl;
	
	public TypeEnvContent(DataTypeDecl dtd) {
		this.dataTypeDecl = dtd;
	}
	
	public DataTypeDecl getDataTypeDecl() {
		return this.dataTypeDecl;
	}
}
