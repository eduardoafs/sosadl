package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.EntityBlock;

@CoqType("unit (AST.Library (Some n) (Some e)) well typed")
public class Type_Library implements Type_unit {
	@Mandatory
	private final String n;
	
	@Mandatory
	private final EntityBlock e;
	
	@CoqType("entity e well typed in empty")
	private final Type_entityBlock p;

	public Type_Library(String n, EntityBlock e, Type_entityBlock p) {
		super();
		this.n = n;
		this.e = e;
		this.p = p;
	}

	public String getN() {
		return n;
	}

	public EntityBlock getE() {
		return e;
	}

	public Type_entityBlock getP() {
		return p;
	}

}
