package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.validation.typing.Environment;

@CoqType("entity (AST.EntityBlock nil nil nil nil nil) well typed in gamma")
public class Type_EntityBlock implements Type_entityBlock {
	@Mandatory
	private final Environment gamma;

	public Type_EntityBlock(Environment gamma) {
		super();
		this.gamma = gamma;
	}

	public Environment getGamma() {
		return gamma;
	}

}
