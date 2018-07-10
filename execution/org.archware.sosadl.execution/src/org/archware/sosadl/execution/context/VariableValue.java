package org.archware.sosadl.execution.context;

public class VariableValue {
	private Object value;
	private VariableObserver<?> observers;
	
	public void setValue(Object sender, Object newValue) {
		this.value = newValue;
		if (sender!=null) {
			observers.notifyAllExcept(sender);
		}
	}
	
	public VariableValue() {
		this.value = null;
		observers = new VariableObserver<Object>(this);
	}
	
	public Object getValue() {
		return value;
	}
}
