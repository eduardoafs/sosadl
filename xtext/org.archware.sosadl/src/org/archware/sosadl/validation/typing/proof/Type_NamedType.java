package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.DataTypeDecl;
import org.archware.sosadl.validation.typing.Environment;

public class Type_NamedType implements Type_datatype {
	@Mandatory private final Environment gamma;
	
	@Mandatory private final String n;
	
	@Mandatory private final DataTypeDecl t;
	
	@Mandatory private final Equality p;

	public Type_NamedType(Environment gamma, String n, DataTypeDecl t, Equality p) {
		super();
		this.gamma = gamma;
		this.n = n;
		this.t = t;
		this.p = p;
	}

	public Environment getGamma() {
		return gamma;
	}

	public String getN() {
		return n;
	}

	public DataTypeDecl getT() {
		return t;
	}

	public Equality getP() {
		return p;
	}

}
