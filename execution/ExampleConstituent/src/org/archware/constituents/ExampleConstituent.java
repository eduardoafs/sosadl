package org.archware.constituents;
import org.archware.sosadl.execution.context.Context;
import org.archware.sosadl.execution.external.ConstituentSimulator;

public class ExampleConstituent extends ConstituentSimulator {

	public ExampleConstituent() {
		super("");
		System.out.println("Example Constituent Initialized");
	}
	
	public ExampleConstituent(String id) {
		super(id);
	}
	
	@Override
	public boolean canRun(Context context) {
		// TODO Auto-generated method stub
	
		return true;
	}

	@Override
	public void run(Context context) {
		System.out.println("Running example constituent");
	}

}
