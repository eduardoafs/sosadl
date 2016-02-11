package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.AssertionDecl;
import org.archware.sosadl.sosADL.BehaviorDecl;
import org.archware.sosadl.sosADL.DataType;
import org.archware.sosadl.sosADL.DataTypeDecl;
import org.archware.sosadl.sosADL.FunctionDecl;
import org.archware.sosadl.sosADL.GateDecl;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

public class Type_SystemDecl_datatype_Some implements Type_systemblock {
	@Mandatory private final Environment gamma;
	
	@Mandatory private final String name;
	
	@Mandatory private final String d_name;
	
	@Mandatory private final DataType d_def;
	
	private final EList<FunctionDecl> d_funs;
	
	private final EList<DataTypeDecl> l;
	
	private final EList<GateDecl> gates;
	
	@Mandatory private final BehaviorDecl bhv;
	
	private final AssertionDecl assrt;
	
	@Mandatory private final Type_datatypeDecl p1;
	
	@Mandatory private final Type_systemblock p2;

	public Type_SystemDecl_datatype_Some(Environment gamma, String name, String d_name, DataType d_def,
			EList<FunctionDecl> d_funs, EList<DataTypeDecl> l, EList<GateDecl> gates, BehaviorDecl bhv,
			AssertionDecl assrt, Type_datatypeDecl p1, Type_systemblock p2) {
		super();
		this.gamma = gamma;
		this.name = name;
		this.d_name = d_name;
		this.d_def = d_def;
		this.d_funs = d_funs;
		this.l = l;
		this.gates = gates;
		this.bhv = bhv;
		this.assrt = assrt;
		this.p1 = p1;
		this.p2 = p2;
	}

	public Environment getGamma() {
		return gamma;
	}

	public String getName() {
		return name;
	}

	public String getD_name() {
		return d_name;
	}

	public DataType getD_def() {
		return d_def;
	}

	public EList<FunctionDecl> getD_funs() {
		return d_funs;
	}

	public EList<DataTypeDecl> getL() {
		return l;
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

	public Type_datatypeDecl getP1() {
		return p1;
	}

	public Type_systemblock getP2() {
		return p2;
	}

}
