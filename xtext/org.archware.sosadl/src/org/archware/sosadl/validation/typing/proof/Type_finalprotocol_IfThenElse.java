package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.ProtocolStatement;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_finalprotocol_IfThenElse implements Type_finalprotocol {
	@Mandatory
	private final Environment gamma;

	@Mandatory
	private final Expression c;

	@Mandatory
	private final Environment gammat;

	private final EList<ProtocolStatement> t;

	@Mandatory
	private final Environment gammae;

	private final EList<ProtocolStatement> e;

	@Mandatory
	private final Type_expression p1;

	@Mandatory
	private final Condition_true p2;

	@Mandatory
	private final Type_finalprotocol p3;

	@Mandatory
	private final Condition_false p4;

	@Mandatory
	private final Type_finalprotocol p5;

	public Type_finalprotocol_IfThenElse(Environment gamma, Expression c, Environment gammat,
			EList<ProtocolStatement> t, Environment gammae, EList<ProtocolStatement> e, Type_expression p1,
			Condition_true p2, Type_finalprotocol p3, Condition_false p4, Type_finalprotocol p5) {
		super();
		this.gamma = gamma;
		this.c = c;
		this.gammat = gammat;
		this.t = t;
		this.gammae = gammae;
		this.e = e;
		this.p1 = p1;
		this.p2 = p2;
		this.p3 = p3;
		this.p4 = p4;
		this.p5 = p5;
	}

	public Environment getGamma() {
		return gamma;
	}

	public Expression getC() {
		return c;
	}

	public Environment getGammat() {
		return gammat;
	}

	public EList<ProtocolStatement> getT() {
		return t;
	}

	public Environment getGammae() {
		return gammae;
	}

	public EList<ProtocolStatement> getE() {
		return e;
	}

	public Type_expression getP1() {
		return p1;
	}

	public Condition_true getP2() {
		return p2;
	}

	public Type_finalprotocol getP3() {
		return p3;
	}

	public Condition_false getP4() {
		return p4;
	}

	public Type_finalprotocol getP5() {
		return p5;
	}

}
