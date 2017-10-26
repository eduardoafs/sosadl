package org.archware.sosadl.design.tools;

import java.util.Collection;
import java.util.Map;

import org.archware.sosadl.sosADL.ArchBehaviorDecl;
import org.archware.sosadl.sosADL.BinaryExpression;
import org.archware.sosadl.sosADL.ComplexName;
import org.archware.sosadl.sosADL.DutyDecl;
import org.archware.sosadl.sosADL.GateDecl;
import org.archware.sosadl.sosADL.Multiplicity;
import org.archware.sosadl.sosADL.SosADLFactory;
import org.archware.sosadl.sosADL.Unify;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.sirius.business.api.action.AbstractExternalJavaAction;

import org.eclipse.sirius.diagram.DNode;

public class CreateUnify extends AbstractExternalJavaAction {

	@Override
	public boolean canExecute(Collection<? extends EObject> arg0) {
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	public void execute(Collection<? extends EObject> arg0, Map<String, Object> arg1) {
		DNode view = (DNode) getOptionalParameter(arg1, "view", EObject.class);
		EObject constituent = ((DNode) view.eContainer()).getTarget();
		
		Unify newU = SosADLFactory.eINSTANCE.createUnify();
		newU.setMultLeft(Multiplicity.MULTIPLICITY_ALL);
		newU.setMultRight(Multiplicity.MULTIPLICITY_ALL);
		
		EObject source = getOptionalParameter(arg1, "source", EObject.class);
		EObject target = getOptionalParameter(arg1, "target", EObject.class);
		
		// If source is a gate, target is a duty
		if (source instanceof GateDecl) {
			ComplexName sourceName = SosADLFactory.eINSTANCE.createComplexName();
			sourceName.getName().add(((GateDecl) source).getName());
			newU.setConnLeft(sourceName);
			
			ComplexName targetName = SosADLFactory.eINSTANCE.createComplexName();
			targetName.getName().add(((DutyDecl) target).getName());
		} else { // source is a Duty, target is a Gate
			ComplexName sourceName = SosADLFactory.eINSTANCE.createComplexName();
			sourceName.getName().add(((DutyDecl) source).getName());
			newU.setConnLeft(sourceName);
			
			ComplexName targetName = SosADLFactory.eINSTANCE.createComplexName();
			targetName.getName().add(((GateDecl) target).getName());
		}
		
		ArchBehaviorDecl arch = (ArchBehaviorDecl) constituent.eContainer();
		
		// Create new binary expression
		BinaryExpression exp = SosADLFactory.eINSTANCE.createBinaryExpression();
		exp.setLeft(newU);
		if (arch.getBindings()!=null) {
			exp.setOp("and");
			exp.setRight(arch.getBindings());
		}
		
		arch.setBindings(exp);
	}

}
