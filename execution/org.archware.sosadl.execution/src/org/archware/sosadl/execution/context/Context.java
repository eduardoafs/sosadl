package org.archware.sosadl.execution.context;

import java.util.HashMap;
import java.util.List;

import org.archware.sosadl.sosADL.ComplexName;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.SosADLFactory;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.sosADL.Unify;
import org.archware.sosadl.utility.ModelUtils;

public class Context {
	private HashMap<ComplexName, VariableValue> context;
	//private QualifiedNameTree<VariableValue> context;
	public Context() {
		context = new HashMap<ComplexName, VariableValue>();
		//context = new QualifiedNameTree<VariableValue>();
	}

	public void changeValue(ComplexName c, Object newValue) {
		//Connection target = (Connection) ModelUtils.resolve(c);
		VariableValue var = this.getValue(c);
		if (var == null) {
			var = new VariableValue();
			context.put(c, var);
			var.addObserver(c);
		}
		var.setValue(c, newValue);
	}

	public VariableValue getValue(ComplexName name) {
		//Connection target = (Connection) ModelUtils.resolve(name);
		for (ComplexName c : context.keySet()) {
			if (ModelUtils.areComplexNameEqual(c, name)) return context.get(c);
		}
		return null;
	}

	public void unify(Unify f) {
		ComplexName left = f.getConnLeft();
		ComplexName right = f.getConnRight();

		VariableValue v = new VariableValue();

		if (this.contains(left)) {
			v = context.get(left);
		} else if (this.contains(right)) {
			v = context.get(right);
		}
		v.setValue(null, null);
		System.out.println("Unified " + ModelUtils.printName(left) + " and " + ModelUtils.printName(right));
		context.put(left, v);
		context.put(right, v);
	}

	private boolean contains(ComplexName left) {
		for (ComplexName c : context.keySet()) {
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
		return false;
	}

	public Context subContext(MediatorDecl o) {
		Context newContext = new Context();
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
		return newContext;
	}

	public Context subContext(SystemDecl o) {
		Context newContext = new Context();
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
		return newContext;
	}

	public String toString() {
		String s = "";
		for (ComplexName n : context.keySet()) {
			s += (s.isEmpty()? "" : "\n") +ModelUtils.printName(n) + " value=" + context.get(n).getValue();
		}
		return s;
	}

}
