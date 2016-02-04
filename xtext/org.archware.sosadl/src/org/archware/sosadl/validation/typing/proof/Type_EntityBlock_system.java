package org.archware.sosadl.validation.typing.proof;

import org.archware.sosadl.sosADL.ArchitectureDecl;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.validation.typing.Environment;
import org.eclipse.emf.common.util.EList;

@CoqType("entity (AST.EntityBlock nil nil (s::l) mediators architectures) well typed in gamma")
public class Type_EntityBlock_system implements Type_entityBlock {
	@Mandatory private final Environment gamma;
	
	@Mandatory private final SystemDecl s;
	
	@Mandatory private final String s_name;
	
	private final EList<SystemDecl> l;
	
	private final EList<MediatorDecl> mediators;
	
	private final EList<ArchitectureDecl> architectures;
	
	@Mandatory
	@CoqType("system s well typed in gamma")
	private final Type_system p1;
	
	@Mandatory
	@CoqType("AST.SystemDeck_name s = Some s_name")
	private final Equality p2;
	
	@Mandatory
	@CoqType("entity (AST.EntityBlock nil nil l mediators architectures) well typed in gamma[s_name <- ESystem]")
	private final Type_entityBlock p3;

	public Type_EntityBlock_system(Environment gamma, SystemDecl s, String s_name, EList<SystemDecl> l,
			EList<MediatorDecl> mediators, EList<ArchitectureDecl> architectures, Type_system p1, Equality p2,
			Type_entityBlock p3) {
		super();
		this.gamma = gamma;
		this.s = s;
		this.s_name = s_name;
		this.l = l;
		this.mediators = mediators;
		this.architectures = architectures;
		this.p1 = p1;
		this.p2 = p2;
		this.p3 = p3;
	}

	public Environment getGamma() {
		return gamma;
	}

	public SystemDecl getS() {
		return s;
	}

	public String getS_name() {
		return s_name;
	}

	public EList<SystemDecl> getL() {
		return l;
	}

	public EList<MediatorDecl> getMediators() {
		return mediators;
	}

	public EList<ArchitectureDecl> getArchitectures() {
		return architectures;
	}

	public Type_system getP1() {
		return p1;
	}

	public Equality getP2() {
		return p2;
	}

	public Type_entityBlock getP3() {
		return p3;
	}

}
