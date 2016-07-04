package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.ProtocolStatement;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_finalprotocol_Repeat implements Type_finalprotocol {
	@Mandatory
	private final Environment gamma;

	private final EList<ProtocolStatement> b;

	@Mandatory
	private final Type_nonfinalprotocol p1;

	public Type_finalprotocol_Repeat(Environment gamma, EList<ProtocolStatement> b, Type_nonfinalprotocol p1) {
		super();
		this.gamma = gamma;
		this.b = b;
		this.p1 = p1;
	}

	public Environment getGamma() {
		return gamma;
	}

	public EList<ProtocolStatement> getB() {
		return b;
	}

	public Type_nonfinalprotocol getP1() {
		return p1;
	}

}
