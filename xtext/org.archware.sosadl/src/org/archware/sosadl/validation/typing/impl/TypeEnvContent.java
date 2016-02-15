package org.archware.sosadl.validation.typing.impl;

import java.util.LinkedList;
import java.util.List;

import org.archware.sosadl.sosADL.DataTypeDecl;
import org.archware.sosadl.sosADL.FunctionDecl;
import org.archware.sosadl.validation.typing.EnvContent;
import org.eclipse.emf.common.util.ECollections;
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

	public EnvContent addMethod(FunctionDecl f) {
		return new TypeEnvContent(dataTypeDecl, cons(f, methods));
	}

	private static <T> EList<T> cons(T v, List<T> l) {
		List<T> lv = new LinkedList<>();
		lv.add(v);
		EList<T> ret = ECollections.asEList(lv);
		ret.addAll(l);
		return ECollections.unmodifiableEList(ret);
	}
}
