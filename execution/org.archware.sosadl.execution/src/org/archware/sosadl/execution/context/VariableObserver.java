package org.archware.sosadl.execution.context;

import java.util.ArrayList;
import java.util.List;

import org.archware.sosadl.execution.events.EventStorage;
import org.archware.sosadl.execution.events.InternalEvent;
import org.archware.sosadl.sosADL.ComplexName;
import org.archware.sosadl.utility.ModelUtils;

public class VariableObserver {
	private VariableValue target;
	private List<ComplexName> stakeholders;
	
	public VariableObserver(VariableValue variableValue) {
		stakeholders = new ArrayList<ComplexName>();
		target = variableValue;
	}

	public void add(ComplexName c) {
		if (!stakeholders.contains(c)) stakeholders.add(c);
	}

	public void notifyAllExcept(ComplexName sender) {
		InternalEvent event = target.getValue()==null? InternalEvent.VALUE_CONSUMPTION : InternalEvent.VALUE_TRANSMISSION;
		for (ComplexName c : stakeholders) {
			if (!ModelUtils.areComplexNameEqual(c, sender)) {
				EventStorage.getInstance().addEvent(event, sender, target);
			}
		}
	}

}
