package org.archware.sosadl.execution.external;

import org.archware.sosadl.execution.context.Context;

public abstract class ConstituentSimulator {
	private String id;
	public ConstituentSimulator(String id) {
		this.id = id;
	}
	
	public abstract boolean canRun(Context context);
	public abstract void run(Context context);
	
	public String getId() {
		return id;
	}
}
