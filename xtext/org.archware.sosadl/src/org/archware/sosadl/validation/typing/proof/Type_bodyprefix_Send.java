package org.archware.sosadl.validation.typing.proof;

import java.math.BigInteger;

import org.archware.sosadl.sosADL.Connection;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.ModeType;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_bodyprefix_Send implements Type_bodyprefix {

	@Mandatory
	private final Environment gamma;

	@Mandatory
	private final String gd;

	private final EList<Connection> endpoints;

	@Mandatory
	private final boolean is_env;

	@Mandatory
	private final String conn;

	@Mandatory
	private final ModeType mode;

	@Mandatory
	private final DataType conn__tau;

	@Mandatory
	private final Expression e;

	@Mandatory
	private final DataType tau__e;

	@Mandatory
	private final Equality p1;

	@Mandatory
	private final Ex<BigInteger, Equality> p2;

	@Mandatory
	private final Mode_send p3;

	@Mandatory
	private final Type_expression p4;

	@Mandatory
	private final Subtype p5;

	public Type_bodyprefix_Send(Environment gamma, String gd, EList<Connection> endpoints, boolean is_env, String conn,
			ModeType mode, DataType conn__tau, Expression e, DataType tau__e, Equality p1, Ex<BigInteger, Equality> p2,
			Mode_send p3, Type_expression p4, Subtype p5) {
		super();
		this.gamma = gamma;
		this.gd = gd;
		this.endpoints = endpoints;
		this.is_env = is_env;
		this.conn = conn;
		this.mode = mode;
		this.conn__tau = conn__tau;
		this.e = e;
		this.tau__e = tau__e;
		this.p1 = p1;
		this.p2 = p2;
		this.p3 = p3;
		this.p4 = p4;
		this.p5 = p5;
	}

	public Environment getGamma() {
		return gamma;
	}

	public String getGd() {
		return gd;
	}

	public EList<Connection> getEndpoints() {
		return endpoints;
	}

	public boolean isIs_env() {
		return is_env;
	}

	public String getConn() {
		return conn;
	}

	public ModeType getMode() {
		return mode;
	}

	public DataType getConn__tau() {
		return conn__tau;
	}

	public Expression getE() {
		return e;
	}

	public DataType getTau__e() {
		return tau__e;
	}

	public Equality getP1() {
		return p1;
	}

	public Ex<BigInteger, Equality> getP2() {
		return p2;
	}

	public Mode_send getP3() {
		return p3;
	}

	public Type_expression getP4() {
		return p4;
	}

	public Subtype getP5() {
		return p5;
	}

}
