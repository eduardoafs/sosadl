package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.validation.typing.Environment;

public class Type_SequenceType implements Type_datatype {
	@Mandatory private final Environment gamma;
	
	@Mandatory private final DataType t;
	
	@Mandatory private final Type_datatype p;

	public Type_SequenceType(Environment gamma, DataType t, Type_datatype p) {
		super();
		this.gamma = gamma;
		this.t = t;
		this.p = p;
	}

	public Environment getGamma() {
		return gamma;
	}

	public DataType getT() {
		return t;
	}

	public Type_datatype getP() {
		return p;
	}

}
