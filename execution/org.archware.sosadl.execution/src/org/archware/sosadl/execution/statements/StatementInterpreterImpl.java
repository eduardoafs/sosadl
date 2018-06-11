package org.archware.sosadl.execution.statements;

import org.archware.sosadl.execution.context.Context;
import org.archware.sosadl.execution.expression.ExpressionEvaluator;
import org.archware.sosadl.sosADL.Action;
import org.archware.sosadl.sosADL.AssertBehavior;
import org.archware.sosadl.sosADL.ChooseBehavior;
import org.archware.sosadl.sosADL.DoExprBehavior;
import org.archware.sosadl.sosADL.DoneBehavior;
import org.archware.sosadl.sosADL.Expression;
import org.archware.sosadl.sosADL.ForEachBehavior;
import org.archware.sosadl.sosADL.IfThenElseBehavior;
import org.archware.sosadl.sosADL.RecursiveCall;
import org.archware.sosadl.sosADL.RepeatBehavior;
import org.archware.sosadl.sosADL.UnobservableBehavior;
import org.archware.sosadl.sosADL.ValuingBehavior;

public class StatementInterpreterImpl extends StatementInterpreter {

	@Override
	public void execute(ValuingBehavior s, Context context) throws StatementException {
		// TODO Auto-generated method stub
	}

	@Override
	public void execute(AssertBehavior s, Context context) throws StatementException {
		// TODO Auto-generated method stub
	}

	@Override
	public void execute(Action s, Context context) throws StatementException {
		// TODO Auto-generated method stub
	}

	@Override
	public void execute(RepeatBehavior s, Context context) throws StatementException {
		try {
			while (true) executeAll(s.getRepeated(), context);
		} catch (DoneStatementException exp) {
			// do nothing
		}
	}

	@Override
	public void execute(IfThenElseBehavior s, Context context) throws StatementException {
		Expression exp = s.getCondition();
		Object value = ExpressionEvaluator.evaluate(exp, context);
		if (value instanceof Boolean && (Boolean) value)
			executeAll(s.getIfTrue(), context);
		else executeAll(s.getIfFalse(), context);
	}


	@Override
	public void execute(ChooseBehavior s, Context context) throws StatementException {
		// TODO Auto-generated method stub
	}

	@Override
	public void execute(ForEachBehavior s, Context context) throws StatementException {
		// TODO Auto-generated method stub
	}

	@Override
	public void execute(DoExprBehavior s, Context context) throws StatementException {
		ExpressionEvaluator.evaluate(s.getExpression(), context);
	}

	@Override
	public void execute(DoneBehavior s, Context context) throws StatementException {
		throw new DoneStatementException();
	}

	@Override
	public void execute(RecursiveCall s, Context context) throws StatementException {
		// TODO Auto-generated method stub
	}

	@Override
	public void execute(UnobservableBehavior s, Context context) throws StatementException {
		// do nothing
	}

}
