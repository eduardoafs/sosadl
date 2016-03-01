package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.FunctionDecl;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Subtype_unfold_right implements Subtype {
	@Mandatory private final Environment gamma;
	
	@Mandatory private final DataType l;
	
	@Mandatory private final String r;
	
	@Mandatory private final DataType def;

	private final EList<FunctionDecl> funs;

	private final EList<FunctionDecl> methods;
	
	@Mandatory private final Equality p1;
	
	@Mandatory private final Subtype p2;

	public Subtype_unfold_right(Environment gamma, DataType l, String r, DataType def, EList<FunctionDecl> funs,
			EList<FunctionDecl> methods, Equality p1, Subtype p2) {
		super();
		this.gamma = gamma;
		this.l = l;
		this.def = def;
		this.funs = funs;
		this.methods = methods;
		this.r = r;
		this.p1 = p1;
		this.p2 = p2;
	}

	public Environment getGamma() {
		return gamma;
	}

	public DataType getL() {
		return l;
	}

	public String getR() {
		return r;
	}

	public DataType getDef() {
		return def;
	}

	public EList<FunctionDecl> getFuns() {
		return funs;
	}

	public EList<FunctionDecl> getMethods() {
		return methods;
	}

	public Equality getP1() {
		return p1;
	}

	public Subtype getP2() {
		return p2;
	}

}
