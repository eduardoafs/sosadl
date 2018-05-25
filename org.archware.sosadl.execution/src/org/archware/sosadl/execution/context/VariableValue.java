package org.archware.sosadl.execution.context;

public class VariableValue {
	private Object value;
	
	public void setValue(Object newValue) {
		this.value = newValue;
	}
	
	public VariableValue() {
		this.value = null;
	}
}
