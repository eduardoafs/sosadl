package org.archware.sosadl.execution.context;

import java.util.HashMap;

import org.archware.sosadl.sosADL.ComplexName;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.SosADLFactory;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.sosADL.Unify;

public class Context {
	private HashMap<ComplexName, VariableValue> context;
	
	public Context() {
		context = new HashMap<ComplexName, VariableValue>();
	}
	
	public void changeValue(ComplexName c, Object newValue) {
		VariableValue var = context.get(c);
		if (var == null) {
			var = new VariableValue();
			context.put(c, var);
		}
		var.setValue(newValue);
	}

	public void unify(Unify f) {
		ComplexName left = f.getConnLeft();
		ComplexName right = f.getConnRight();
		
		VariableValue v = null;
		
		if (context.containsKey(left)) {
			v = context.get(left);
		}
		if (v==null && context.containsKey(right)) {
			v = context.get(right);
		}
		if (v==null) {
			v = new VariableValue();
		}
		
		context.put(left,v);
		context.put(right,v);
	}

	public Context subContext(MediatorDecl o) {
		Context c = new Context();
		for (ComplexName name : this.context.keySet()) {
			String mediatorName = o.getName();
			
			if (name.getName().get(0).equals(mediatorName)) {
				ComplexName internalName = SosADLFactory.eINSTANCE.createComplexName();
				Boolean control = false;
				for (String s : name.getName()) {
					if (control) internalName.getName().add(s);
					control = true;
				}
				VariableValue originalValue = context.get(name);
				c.changeValue(internalName, originalValue);
			}
			
		}
		return c;
	}

	public Context subContext(SystemDecl o) {
		// TODO Auto-generated method stub
		return null;
	}

	
}
