package org.archware.sosadl.design.tools;

import java.util.Collection;
import java.util.Map;

import org.archware.sosadl.sosADL.ArchBehaviorDecl;
import org.archware.sosadl.sosADL.Constituent;
import org.archware.sosadl.sosADL.SystemDecl;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.sirius.business.api.action.AbstractExternalJavaAction;

public class DeleteConstituent extends AbstractExternalJavaAction{

	@Override
	public boolean canExecute(Collection<? extends EObject> arg0) {
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	public void execute(Collection<? extends EObject> arg0, Map<String, Object> arg1) {
		Object o = arg0.toArray()[0];
		if (!(o instanceof Constituent)) {
			// DO NOTHING
			return;
		}
		ArchBehaviorDecl beha = (ArchBehaviorDecl) ((Constituent)o).eContainer();
		beha.getConstituents().remove(o);
	}

}
