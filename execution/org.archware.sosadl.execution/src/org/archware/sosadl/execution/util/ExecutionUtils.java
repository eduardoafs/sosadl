package org.archware.sosadl.execution.util;

import java.util.ArrayList;
import java.util.List;

import org.archware.sosadl.sosADL.BinaryExpression;
import org.archware.sosadl.sosADL.Unify;

public class ExecutionUtils {
	public static List<Unify> extractUnifies(BinaryExpression bindings) {
		List<Unify> unifies = new ArrayList<Unify>();
		if (bindings.getLeft() instanceof Unify)
			unifies.add((Unify) bindings.getLeft());
		else if (bindings.getLeft() instanceof BinaryExpression)
			unifies.addAll(extractUnifies((BinaryExpression) bindings.getLeft()));
		if (bindings.getRight() instanceof Unify)
			unifies.add((Unify) bindings.getRight());
		else if (bindings.getRight() instanceof BinaryExpression)
			unifies.addAll(extractUnifies((BinaryExpression) bindings.getRight()));
		return unifies;
	}
}
