package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.validation.typing.Environment;

public class Subtype_refl implements Subtype {
	@Mandatory private final Environment gamma;
	
	@Mandatory private final DataType t;

	public Subtype_refl(Environment gamma, DataType t) {
		super();
		this.gamma = gamma;
		this.t = t;
	}

	public Environment getGamma() {
		return gamma;
	}

	public DataType getT() {
		return t;
	}

}
