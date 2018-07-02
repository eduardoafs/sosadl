package org.archware.sosadl.execution.expression;

import org.archware.sosadl.execution.context.Context;
import org.archware.sosadl.sosADL.BinaryExpression;
import org.archware.sosadl.sosADL.Expression;

public abstract class BinaryExpressionEvaluator extends ExpressionEvaluator {
	public Object evaluate(BinaryExpression exp, Context context) {
		String op = exp.getOp();
		Expression left = exp.getLeft();
		Expression right = exp.getRight();

		if (op == null || op.isEmpty())
			return evaluate(left, context);

		Object valueLeft = evaluate(left, context);
		if (op.equals("implies")) {
			if (valueLeft instanceof Boolean && (Boolean) valueLeft)
				return evaluate(right, context);
			else
				return true;
		}
		if (op.equals("or")) {
			if (valueLeft instanceof Boolean && (Boolean) valueLeft)
				return true;
			else
				return evaluate(right, context);
		}
		if (op.equals("xor")) {
			if (valueLeft instanceof Boolean) {
				Object valueRight = evaluate(right, context);
				if (valueRight instanceof Boolean) {
					return ((Boolean)valueLeft && !(Boolean)valueRight) || (!(Boolean)valueLeft && (Boolean)valueRight);
				}
			} else return false;
		}
		if (op.equals("and")) {
			if (valueLeft instanceof Boolean && (Boolean) valueLeft)
				return evaluate(right, context);
			else
				return false;
		}
		if (op.equals("=")) {
			Object valueRight = evaluate(right, context);
			return valueLeft.equals(valueRight);
		}
		if (op.equals("<>")) {
			Object valueRight = evaluate(right, context);
			return !valueLeft.equals(valueRight);
		}
		if (op.equals("<")) {
			Object valueRight = evaluate(right, context);
			return ValueComparator.compare(valueLeft, valueRight) < 0;
		}
		if (op.equals("<=")) {
			Object valueRight = evaluate(right, context);
			return ValueComparator.compare(valueLeft, valueRight) <= 0;
		}
		if (op.equals(">")) {
			Object valueRight = evaluate(right, context);
			return ValueComparator.compare(valueLeft, valueRight) > 0;
		}
		if (op.equals(">=")) {
			Object valueRight = evaluate(right, context);
			return ValueComparator.compare(valueLeft, valueRight) >= 0;
		}

		if (op.equals("+")) {
			Object valueRight = evaluate(right, context);
			return ArithmeticEvaluator.sum(valueLeft, valueRight);
		}
		if (op.equals("-")) {
			Object valueRight = evaluate(right, context);
			return ArithmeticEvaluator.sub(valueLeft, valueRight);
		}
		if (op.equals("*")) {
			Object valueRight = evaluate(right, context);
			return ArithmeticEvaluator.mul(valueLeft, valueRight);
		}
		if (op.equals("/")) {
			Object valueRight = evaluate(right, context);
			return ArithmeticEvaluator.div(valueLeft, valueRight);
		}
		if (op.equals("mod")) {
			Object valueRight = evaluate(right, context);
			return ArithmeticEvaluator.mod(valueLeft, valueRight);
		}
		if (op.equals("div")) {
			Object valueRight = evaluate(right, context);
			return ArithmeticEvaluator.div(valueLeft, valueRight);
		}

		return null;
	}

}
