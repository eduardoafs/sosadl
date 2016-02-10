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
	
	private final EList<DataTypeDecl> datatypes;
	
	private final EList<GateDecl> gates;

	@Mandatory private final BehaviorDecl bhv;
	
	private final AssertionDecl assrt;
	
	@Mandatory private final Forall<FormalParameter, Ex<DataType, And<Equality,Type_datatype>>> p1;
	
	@Mandatory private final Type_systemblock p2;
	
	@Mandatory private final Equality p3;

	public Type_SystemDecl(Environment gamma, String name, EList<FormalParameter> params, EList<DataTypeDecl> datatypes,
			EList<GateDecl> gates, BehaviorDecl bhv, AssertionDecl assrt,
			Forall<FormalParameter, Ex<DataType, And<Equality, Type_datatype>>> p1, Type_systemblock p2, Equality p3) {
		super();
		this.gamma = gamma;
		this.name = name;
		this.params = params;
		this.datatypes = datatypes;
		this.gates = gates;
		this.bhv = bhv;
		this.assrt = assrt;
		this.p1 = p1;
		this.p2 = p2;
		this.p3 = p3;
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

	public EList<DataTypeDecl> getDatatypes() {
		return datatypes;
	}

	public EList<GateDecl> getGates() {
		return gates;
	}

	public BehaviorDecl getBhv() {
		return bhv;
	}

	public AssertionDecl getAssrt() {
		return assrt;
	}

	public Forall<FormalParameter, Ex<DataType, And<Equality, Type_datatype>>> getP1() {
		return p1;
	}

	public Type_systemblock getP2() {
		return p2;
	}

	public Equality getP3() {
		return p3;
	}
}
