package org.archware.sosadl.execution.statements;

import org.archware.sosadl.execution.context.Context;
import org.archware.sosadl.sosADL.Action;
import org.archware.sosadl.sosADL.AssertBehavior;
import org.archware.sosadl.sosADL.Behavior;
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
	public void executeAll(Behavior behavior, Context context) throws StatementException {
		for (BehaviorStatement s : behavior.getStatements()) {
			execute(s, context);
		}
	}
	
	public void execute(BehaviorStatement s, Context context) throws StatementException {
		if (s instanceof ValuingBehavior) execute((ValuingBehavior) s, context);
		else if (s instanceof AssertBehavior) execute((AssertBehavior) s, context);
		else if (s instanceof Action) execute((Action) s, context);
		else if (s instanceof RepeatBehavior) execute((RepeatBehavior) s, context);
		else if (s instanceof IfThenElseBehavior) execute((IfThenElseBehavior) s, context);
		else if (s instanceof ChooseBehavior) execute((ChooseBehavior) s, context);
		else if (s instanceof ForEachBehavior) execute((ForEachBehavior) s, context);
		else if (s instanceof DoExprBehavior) execute((DoExprBehavior) s, context);
		else if (s instanceof DoneBehavior) execute((DoneBehavior) s, context);
		else if (s instanceof RecursiveCall) execute((RecursiveCall) s, context);
		else if (s instanceof UnobservableBehavior) execute((UnobservableBehavior) s, context);
		else throw new StatementException("Invalid kind of statement: "+s.getClass().getCanonicalName());
	}
	public abstract void execute(ValuingBehavior s, Context context) throws StatementException;
	public abstract void execute(AssertBehavior s, Context context) throws StatementException;
	public abstract void execute(Action s, Context context) throws StatementException;
	public abstract void execute(RepeatBehavior s, Context context) throws StatementException;
	public abstract void execute(IfThenElseBehavior s, Context context) throws StatementException;
	public abstract void execute(ChooseBehavior s, Context context) throws StatementException;
	public abstract void execute(ForEachBehavior s, Context context) throws StatementException;
	public abstract void execute(DoExprBehavior s, Context context) throws StatementException;
	public abstract void execute(DoneBehavior s, Context context) throws StatementException;
	public abstract void execute(RecursiveCall s, Context context) throws StatementException;
	public abstract void execute(UnobservableBehavior s, Context context) throws StatementException;
}
