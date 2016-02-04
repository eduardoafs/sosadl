package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.ArchitectureDecl;
import org.archware.sosadl.sosADL.DataTypeDecl;
import org.archware.sosadl.sosADL.FunctionDecl;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

@CoqType("entity (AST.EntityBlock ((AST.DataTypeDecl (Some d_name) None d_funs)::l) funs systems mediators architectures well typed in Gamma")
public class Type_EntityBlock_datatype_None implements Type_entityBlock {
	@Mandatory private final Environment Gamma;
	
	@Mandatory private final String d_name;
	
	private final EList<FunctionDecl> d_funs;
	
	private final EList<DataTypeDecl> l;
	
	private final EList<FunctionDecl> funs;
	
	private final EList<SystemDecl> systems;
	
	private final EList<MediatorDecl> mediators;
	
	private final EList<ArchitectureDecl> architectures;
	
	@Mandatory
	@CoqType("typedecl (AST.DataTypeDeck (Some d_name) None d_funs) well typed in Gamma")
	private final Type_datatypeDecl p1;
	
	@Mandatory
	@CoqType("entity (AST.EntityBlock l funs systems mediators architectures) well typed in Gamma[d_name <- EType (AST.DataTypeDeck (Some d_name) (Some d_def) d_funs)]")
	private final Type_entityBlock p2;

	public Type_EntityBlock_datatype_None(Environment gamma, String d_name, EList<FunctionDecl> d_funs,
			EList<DataTypeDecl> l, EList<FunctionDecl> funs, EList<SystemDecl> systems, EList<MediatorDecl> mediators,
			EList<ArchitectureDecl> architectures, Type_datatypeDecl p1, Type_entityBlock p2) {
		super();
		Gamma = gamma;
		this.d_name = d_name;
		this.d_funs = d_funs;
		this.l = l;
		this.funs = funs;
		this.systems = systems;
		this.mediators = mediators;
		this.architectures = architectures;
		this.p1 = p1;
		this.p2 = p2;
	}

	public Environment getGamma() {
		return Gamma;
	}

	public String getD_name() {
		return d_name;
	}

	public EList<FunctionDecl> getD_funs() {
		return d_funs;
	}

	public EList<DataTypeDecl> getL() {
		return l;
	}

	public EList<FunctionDecl> getFuns() {
		return funs;
	}

	public EList<SystemDecl> getSystems() {
		return systems;
	}

	public EList<MediatorDecl> getMediators() {
		return mediators;
	}

	public EList<ArchitectureDecl> getArchitectures() {
		return architectures;
	}

	public Type_datatypeDecl getP1() {
		return p1;
	}

	public Type_entityBlock getP2() {
		return p2;
	}

}
