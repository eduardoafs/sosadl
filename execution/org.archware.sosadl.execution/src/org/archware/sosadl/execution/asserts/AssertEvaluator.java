package org.archware.sosadl.execution.asserts;

import org.archware.sosadl.execution.context.Context;
import org.archware.sosadl.sosADL.ComplexName;
import org.archware.sosadl.sosADL.Connection;
import org.archware.sosadl.sosADL.DutyDecl;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.ModeType;
import org.archware.sosadl.sosADL.SosADLFactory;
import org.archware.sosadl.sosADL.SystemDecl;

public class AssertEvaluator {

	public static boolean canExecute(MediatorDecl o, Context context) {
		// TODO check the asserts, by now, just check if the inputs are all available
		//List<ComplexName> inputs = new ArrayList<ComplexName>();
		// identify all input connections for the given mediator
		for (DutyDecl d : o.getDuties()) {
			for (Connection c : d.getConnections()) {
				ModeType t = c.getMode();
				if (t == ModeType.MODE_TYPE_IN || t == ModeType.MODE_TYPE_INOUT) {
					ComplexName cName = SosADLFactory.eINSTANCE.createComplexName();
					cName.getName().add(d.getName());
					cName.getName().add(c.getName());
					// inputs.add(cName); // [update: this list is no longer necessary]
					
					// if the context for this input is null, then return false (optimization)
					if (context.getValue(cName)==null) return false;
				}
			}
		}
		// check if the values are not null [update: this is now done in the previous loop]
		/*for (ComplexName connections : inputs) {
			if (context.getValue(connections)==null) return false; // if any value is null, return false
		}*/
		return true;
	}

	public static boolean canExecute(SystemDecl o, Context context) {
		// TODO Auto-generated method stub
		return false;
	}
}
