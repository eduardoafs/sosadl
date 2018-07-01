package org.archware.sosadl.execution.context;

public class VariableValue {
	private Object value;
	
	public void setValue(Object newValue) {
		ValueObserver.getObserver().notify(this);
		this.value = newValue;
	}
	
	public VariableValue() {
		this.value = null;
	}
	
	public Object getValue() {
		return value;
	}
}
