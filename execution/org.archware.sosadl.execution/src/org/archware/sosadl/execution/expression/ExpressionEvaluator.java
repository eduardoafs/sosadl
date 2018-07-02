package org.archware.sosadl.execution.expression;

import org.archware.sosadl.execution.context.Context;
import org.archware.sosadl.sosADL.BinaryExpression;
import org.archware.sosadl.sosADL.Expression;

public abstract class ExpressionEvaluator {

	public static Object evaluate(Expression exp, Context context) {
		return false;
	}

	public abstract Object evaluate(BinaryExpression exp, Context context);
}
