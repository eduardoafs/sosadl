package org.archware.sosadl.execution.context;

import org.archware.sosadl.sosADL.ComplexName;

public class VariableValue {
	private Object value;
	private VariableObserver observers;
	
	public void setValue(ComplexName sender, Object newValue) {
		this.value = newValue;
		if (sender!=null) {
			observers.notifyAllExcept(sender);
		}
	}
	
	public VariableValue() {
		this.value = null;
		observers = new VariableObserver(this);
	}
	
	public Object getValue() {
		return value;
	}

	public void addObserver(ComplexName c) {
		observers.add(c);
	}
}
