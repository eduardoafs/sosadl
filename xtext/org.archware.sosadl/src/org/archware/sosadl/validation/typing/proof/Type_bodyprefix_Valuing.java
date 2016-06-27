package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.Valuing;
import org.archware.sosadl.validation.typing.Environment;

public class Type_bodyprefix_Valuing implements Type_bodyprefix {

	@Mandatory
	private final Environment gamma;

	@Mandatory
	private final Valuing v;

	@Mandatory
	private final Environment gamma1;

	@Mandatory
	private final Type_valuing p1;

	public Type_bodyprefix_Valuing(Environment gamma, Valuing v, Environment gamma1, Type_valuing p1) {
		super();
		this.gamma = gamma;
		this.v = v;
		this.gamma1 = gamma1;
		this.p1 = p1;
	}

	public Environment getGamma() {
		return gamma;
	}

	public Valuing getV() {
		return v;
	}

	public Environment getGamma1() {
		return gamma1;
	}

	public Type_valuing getP1() {
		return p1;
	}

}
