package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.ProtocolStatement;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_finalprotocol_prefix implements Type_finalprotocol {
	@Mandatory
	private final Environment gamma;

	@Mandatory
	private final ProtocolStatement s;

	@Mandatory
	private final Environment gamma1;

	private final EList<ProtocolStatement> l;

	@Mandatory
	private final Type_bodyprotocol p1;

	@Mandatory
	private final Type_finalprotocol p2;

	public Type_finalprotocol_prefix(Environment gamma, ProtocolStatement s, Environment gamma1,
			EList<ProtocolStatement> l, Type_bodyprotocol p1, Type_finalprotocol p2) {
		super();
		this.gamma = gamma;
		this.s = s;
		this.gamma1 = gamma1;
		this.l = l;
		this.p1 = p1;
		this.p2 = p2;
	}

	public Environment getGamma() {
		return gamma;
	}

	public ProtocolStatement getS() {
		return s;
	}

	public Environment getGamma1() {
		return gamma1;
	}

	public EList<ProtocolStatement> getL() {
		return l;
	}

	public Type_bodyprotocol getP1() {
		return p1;
	}

	public Type_finalprotocol getP2() {
		return p2;
	}

}
