package org.archware.sosadl.execution.statements;

import org.archware.sosadl.execution.context.Context;
import org.archware.sosadl.sosADL.Action;
import org.archware.sosadl.sosADL.AssertBehavior;
import org.archware.sosadl.sosADL.BehaviorStatement;
import org.archware.sosadl.sosADL.ChooseBehavior;
import org.archware.sosadl.sosADL.DoExprBehavior;
import org.archware.sosadl.sosADL.DoneBehavior;
import org.archware.sosadl.sosADL.ForEachBehavior;
import org.archware.sosadl.sosADL.IfThenElseBehavior;
import org.archware.sosadl.sosADL.RecursiveCall;
import org.archware.sosadl.sosADL.RepeatBehavior;
import org.archware.sosadl.sosADL.UnobservableBehavior;
import org.archware.sosadl.sosADL.ValuingBehavior;

public abstract class StatementInterpreter {
	public Object execute(BehaviorStatement s, Context context) throws StatementException {
		if (s instanceof ValuingBehavior) return execute((ValuingBehavior) s, context);
		else if (s instanceof AssertBehavior) return execute((AssertBehavior) s, context);
		else if (s instanceof Action) return execute((Action) s, context);
		else if (s instanceof RepeatBehavior) return execute((RepeatBehavior) s, context);
		else if (s instanceof IfThenElseBehavior) return execute((IfThenElseBehavior) s, context);
		else if (s instanceof ChooseBehavior) return execute((ChooseBehavior) s, context);
		else if (s instanceof ForEachBehavior) return execute((ForEachBehavior) s, context);
		else if (s instanceof DoExprBehavior) return execute((DoExprBehavior) s, context);
		else if (s instanceof DoneBehavior) return execute((DoneBehavior) s, context);
		else if (s instanceof RecursiveCall) return execute((RecursiveCall) s, context);
		else if (s instanceof UnobservableBehavior) return execute((UnobservableBehavior) s, context);
		else throw new StatementException("Invalid kind of statement: "+s.getClass().getCanonicalName());
	}
	public abstract Object execute(ValuingBehavior s, Context context) throws StatementException;
	public abstract Object execute(AssertBehavior s, Context context) throws StatementException;
	public abstract Object execute(Action s, Context context) throws StatementException;
	public abstract Object execute(RepeatBehavior s, Context context) throws StatementException;
	public abstract Object execute(IfThenElseBehavior s, Context context) throws StatementException;
	public abstract Object execute(ChooseBehavior s, Context context) throws StatementException;
	public abstract Object execute(ForEachBehavior s, Context context) throws StatementException;
	public abstract Object execute(DoExprBehavior s, Context context) throws StatementException;
	public abstract Object execute(DoneBehavior s, Context context) throws StatementException;
	public abstract Object execute(RecursiveCall s, Context context) throws StatementException;
	public abstract Object execute(UnobservableBehavior s, Context context) throws StatementException;
}
