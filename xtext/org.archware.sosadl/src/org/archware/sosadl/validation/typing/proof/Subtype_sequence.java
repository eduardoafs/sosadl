package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.validation.typing.Environment;

public class Subtype_sequence implements Subtype {
	@Mandatory private final Environment gamma;

	@Mandatory private final DataType l;

	@Mandatory private final DataType r;

	@Mandatory private final Subtype p1;

	public Subtype_sequence(Environment gamma, DataType l, DataType r, Subtype p1) {
		super();
		this.gamma = gamma;
		this.l = l;
		this.r = r;
		this.p1 = p1;
	}

	public Environment getGamma() {
		return gamma;
	}

	public DataType getL() {
		return l;
	}

	public DataType getR() {
		return r;
	}

	public Subtype getP1() {
		return p1;
	}

}
