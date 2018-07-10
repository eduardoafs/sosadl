package org.archware.sosadl.execution.context;

import java.util.ArrayList;
import java.util.List;

import org.archware.sosadl.execution.events.EventStorage;
import org.archware.sosadl.execution.events.InternalEvent;
import org.archware.sosadl.sosADL.ComplexName;
import org.archware.sosadl.utility.ModelUtils;
import org.eclipse.emf.ecore.EObject;

public class VariableObserver<T> {
	private VariableValue target;
	private List<T> stakeholders;
	
	public VariableObserver(VariableValue variableValue) {
		stakeholders = new ArrayList<T>();
		target = variableValue;
	}

	public void add(T c) {
		if (!stakeholders.contains(c)) stakeholders.add(c);
	}

	public void notifyAllExcept(Object sender) {
		InternalEvent event = target.getValue()==null? InternalEvent.VALUE_CONSUMPTION : InternalEvent.VALUE_TRANSMISSION;
		for (T c : stakeholders) {
			//if (!ModelUtils.areComplexNameEqual(c, sender)) {
			if (c.equals(sender)) {
				EventStorage.getInstance().addEvent(event, sender, target);
			}
		}
	}

}
