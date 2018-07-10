package org.archware.sosadl.execution.context;

import java.util.HashMap;

import org.archware.sosadl.sosADL.ComplexName;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.sosADL.Unify;
import org.archware.sosadl.utility.ModelUtils;

public class Context {
	private HashMap<String, VariableValue> context;
	
	//private QualifiedNameTree<VariableValue> context;
	public Context() {
		context = new HashMap<String, VariableValue>();
		//context = new QualifiedNameTree<VariableValue>();
	}

	public void changeValue(ComplexName c, Object newValue) {
		/*//Connection target = (Connection) ModelUtils.resolve(c);
		VariableValue var = this.getValue(c);
		if (var == null) {
			var = new VariableValue();
			context.put(ModelUtils.printName(c), var);
			translator.put(ModelUtils.printName(c), c);
			var.addObserver(c);
		}
		var.setValue(c, newValue);*/
		changeValue(ModelUtils.printName(c), newValue);
	}
	
	public void changeValue(String c, Object newValue) {
		VariableValue var = this.getValue(c);
		if (var == null) {
			var = new VariableValue();
			context.put(c, var);
			//var.addObserver(c);
		}
		var.setValue(c, newValue);
	}

	public VariableValue getValue(ComplexName name) {
		//Connection target = (Connection) ModelUtils.resolve(name);
		//for (ComplexName c : context.keySet()) {
		//	if (ModelUtils.areComplexNameEqual(c, name)) return context.get(c);
		//}
		//return null;
		return getValue(ModelUtils.printName(name));
	}
	
	public VariableValue getValue(String complexName) {
		return context.get(complexName);
	}


	public void unify(Unify f) {
		ComplexName left = f.getConnLeft();
		ComplexName right = f.getConnRight();

		VariableValue v = new VariableValue();

		if (this.contains(left)) {
			v = context.get(ModelUtils.printName(left));
		} else if (this.contains(right)) {
			v = context.get(ModelUtils.printName(right));
		}
		v.setValue(null, null);
		System.out.println("Unified " + ModelUtils.printName(left) + " and " + ModelUtils.printName(right));
		String leftName = ModelUtils.printName(left);
		String rightName = ModelUtils.printName(right); 
		context.put(leftName, v);
		context.put(rightName, v);
	}

	private boolean contains(ComplexName left) {
		/*for (ComplexName c : context.keySet()) {
			if (left.getName().size() == c.getName().size()) {
				int size = left.getName().size();
				List<String> leftName = left.getName();
				List<String> cName = c.getName();
				for (int i=0; i<size;i++) {
					if (leftName.get(i).equals(cName.get(i))) { 
						if (i==size-1) return true;
					}
				}
			}
		}
		return false;*/
		return context.containsKey(ModelUtils.printName(left));
	}

	public Context subContext(MediatorDecl o) {
		/*Context newContext = new Context();
		for (ComplexName n : this.context.keySet()) {
			if (!n.getName().isEmpty() && n.getName().get(0).equals(o.getName())) {
				if (n.getName().get(0).equals(o.getName())) {
					ComplexName newName = SosADLFactory.eINSTANCE.createComplexName();

					for (int i = 1; i < n.getName().size(); i++) {
						newName.getName().add(n.getName().get(i));
					}
					newContext.context.put(newName, this.context.get(n));
				} else {
					// do nothing
				}
			}
		}
		return newContext;*/
		return subContext(o.getName());
	}

	public Context subContext(SystemDecl o) {
		/*Context newContext = new Context();
		for (ComplexName n : this.context.keySet()) {
			if (!n.getName().isEmpty() && n.getName().get(0).equals(o.getName())) {
				ComplexName newName = SosADLFactory.eINSTANCE.createComplexName();

				for (int i = 1; i < n.getName().size(); i++) {
					newName.getName().add(n.getName().get(i));
				}
				newContext.context.put(newName, this.context.get(n));
			} else {
				// do nothing
			}
		}
		return newContext;*/
		return subContext(o.getName());
	}
	
	private Context subContext(String key) {
		Context newContext = new Context();
		for (String s : context.keySet()) {
			if (s.startsWith(key+".")) {
				String newKey = s.replace(key+".", "");
				newContext.context.put(newKey, this.context.get(s));
			}
		}
		
		return newContext;
	}

	public String toString() {
		String s = "";
		for (String n : context.keySet()) {
			s += (s.isEmpty()? "" : "\n") +n + " value=" + context.get(n).getValue();
		}
		return s;
	}

}
