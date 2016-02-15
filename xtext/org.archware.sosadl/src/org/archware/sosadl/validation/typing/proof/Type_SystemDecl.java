package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.AssertionDecl;
import org.archware.sosadl.sosADL.BehaviorDecl;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.DataTypeDecl;
import org.archware.sosadl.sosADL.FormalParameter;
import org.archware.sosadl.sosADL.GateDecl;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_SystemDecl implements Type_system {
	@Mandatory private final Environment gamma;
	
	@Mandatory private final String name;
	
	private final EList<FormalParameter> params;
	
	@Mandatory private final Environment gamma1;
	
	private final EList<DataTypeDecl> datatypes;
	
	@Mandatory private final Environment gamma2;
	
	private final EList<GateDecl> gates;
	
	@Mandatory private final Environment gamma3;

	@Mandatory private final BehaviorDecl bhv;
	
	private final AssertionDecl assrt;
	
	@Mandatory private final Mutually<FormalParameter, Ex<DataType, And<Equality,Type_datatype>>> p1;
	
	@Mandatory private final Incrementally<DataTypeDecl,Type_datatypeDecl> p2;

	@Mandatory private final Incrementally<GateDecl, Simple_increment<GateDecl, Type_gate>> p3;
	
	@Mandatory private final Type_behavior p4;
	
	@Mandatory private final Optionally<AssertionDecl, Type_assertion> p5;

	public Type_SystemDecl(Environment gamma, String name, EList<FormalParameter> params, Environment gamma1,
			EList<DataTypeDecl> datatypes, Environment gamma2, EList<GateDecl> gates, Environment gamma3,
			BehaviorDecl bhv, AssertionDecl assrt,
			Mutually<FormalParameter, Ex<DataType, And<Equality, Type_datatype>>> p1,
			Incrementally<DataTypeDecl,Type_datatypeDecl> p2, Incrementally<GateDecl,Simple_increment<GateDecl,Type_gate>> p3, Type_behavior p4,
			Optionally<AssertionDecl, Type_assertion> p5) {
		super();
		this.gamma = gamma;
		this.name = name;
		this.params = params;
		this.gamma1 = gamma1;
		this.datatypes = datatypes;
		this.gamma2 = gamma2;
		this.gates = gates;
		this.gamma3 = gamma3;
		this.bhv = bhv;
		this.assrt = assrt;
		this.p1 = p1;
		this.p2 = p2;
		this.p3 = p3;
		this.p4 = p4;
		this.p5 = p5;
	}

	public Environment getGamma() {
		return gamma;
	}

	public String getName() {
		return name;
	}

	public EList<FormalParameter> getParams() {
		return params;
	}

	public Environment getGamma1() {
		return gamma1;
	}

	public EList<DataTypeDecl> getDatatypes() {
		return datatypes;
	}

	public Environment getGamma2() {
		return gamma2;
	}

	public EList<GateDecl> getGates() {
		return gates;
	}

	public Environment getGamma3() {
		return gamma3;
	}

	public BehaviorDecl getBhv() {
		return bhv;
	}

	public AssertionDecl getAssrt() {
		return assrt;
	}

	public Mutually<FormalParameter, Ex<DataType, And<Equality, Type_datatype>>> getP1() {
		return p1;
	}

	public Incrementally<DataTypeDecl,Type_datatypeDecl> getP2() {
		return p2;
	}

	public Incrementally<GateDecl,Simple_increment<GateDecl,Type_gate>> getP3() {
		return p3;
	}

	public Type_behavior getP4() {
		return p4;
	}

	public Optionally<AssertionDecl, Type_assertion> getP5() {
		return p5;
	}
}
