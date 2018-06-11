package org.archware.sosadl.execution;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.archware.sosadl.execution.asserts.AssertEvaluator;
import org.archware.sosadl.execution.context.Context;
import org.archware.sosadl.execution.input.InputFile;
import org.archware.sosadl.execution.input.InputLine;
import org.archware.sosadl.execution.statements.StatementException;
import org.archware.sosadl.execution.statements.StatementInterpreter;
import org.archware.sosadl.execution.statements.StatementInterpreterImpl;
import org.archware.sosadl.execution.util.ExecutionUtils;
import org.archware.sosadl.sosADL.ArchitectureDecl;
import org.archware.sosadl.sosADL.BehaviorStatement;
import org.archware.sosadl.sosADL.BinaryExpression;
import org.archware.sosadl.sosADL.Connection;
import org.archware.sosadl.sosADL.Constituent;
import org.archware.sosadl.sosADL.EntityBlock;
import org.archware.sosadl.sosADL.GateDecl;
import org.archware.sosadl.sosADL.IdentExpression;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.SoS;
import org.archware.sosadl.sosADL.SosADL;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.sosADL.Unify;
import org.archware.sosadl.sosADL.Unit;
import org.archware.sosadl.utility.ModelUtils;
import events.ConnectionRef;
import events.Event;

public class Simulator {
	private ArchitectureDecl model;
	private List<List> eventList;
	private StatementInterpreter st;
	private InputFile file;
	private Iterator inputIt;

	public ArchitectureDecl getModel() {
		return model;
	}

	public InputFile getFile() {
		return file;
	}

	int time = 1;
	private Context defaultContext;
	private InputLine currentInputLine;

	public Simulator(SosADL model) {
		st = new StatementInterpreterImpl();
		Unit unit = model.getContent();
		try {
			if (unit instanceof SoS) {
				EntityBlock entity = ((SoS) unit).getDecls();
				if (entity.getArchitectures().isEmpty())
					throw new Exception("No architecture found in model");
				this.model = entity.getArchitectures().get(0);
			} else {
				throw new Exception("Unable to execute model");
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
		}
	}

	public Simulator(SosADL model, String configFilePath) throws IOException {
		st = new StatementInterpreterImpl();
		Unit unit = model.getContent();
		try {
			if (unit instanceof SoS) {
				EntityBlock entity = ((SoS) unit).getDecls();
				if (entity.getArchitectures().isEmpty())
					throw new Exception("No architecture found in model");
				this.model = entity.getArchitectures().get(0);
			} else {
				throw new Exception("Unable to execute model");
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
		}
		this.setInputFile(configFilePath);
	}

	public void setInputFile(String filePath) throws IOException {
		File f = new File(filePath);
		this.file = InputFile.init(f);
	}

	public void init() {
		System.out.println("Initializing simulator...");
		eventList = new ArrayList<List>();
		time = 1;
		inputIt = file.getLines().iterator();
		if (inputIt.hasNext())
			currentInputLine = (InputLine) inputIt.next();
		else
			currentInputLine = null;

		// initialize default context
		defaultContext = new Context();

		// calculate unified connections
		BinaryExpression bindings = (BinaryExpression) model.getBehavior().getBindings();
		for (Unify f : ExecutionUtils.extractUnifies(bindings)) {
			defaultContext.unify(f); // unifies variable values
		}

		// list of events with create node and create links
		// TODO
		System.out.println("Simulator initialized.");
	}

	public List<Event> step() {
		System.out.println("Running step " + time + ".");
		// first of all, check if next value injection is in this step
		if (currentInputLine != null && currentInputLine.getNumber() == time) {
			// inject value
			defaultContext.changeValue(currentInputLine.getName(), currentInputLine.getValue());

			// update currentInputLine
			if (inputIt.hasNext())
				currentInputLine = (InputLine) inputIt.next();
			else
				currentInputLine = null;
		}

		List<Event> stepEvents = new ArrayList<Event>();
		// do something

		// try to execute components' behavior
		for (Constituent c : model.getBehavior().getConstituents()) { // TODO error-proof loop
			Object o = ModelUtils.resolve((IdentExpression) c.getValue());
			// pass with default context
			if (o instanceof SystemDecl) {
				execute((SystemDecl) o, defaultContext);
			} else if (o instanceof MediatorDecl) {
				execute((MediatorDecl) o, defaultContext);
			}
		}

		System.out.println("Current context:");
		System.out.println(defaultContext);
		eventList.add(stepEvents);
		System.out.println("Finished step " + time + ".");
		time++;
		return stepEvents;
	}

	private void execute(SystemDecl o, Context context) {
		Context context2 = context.subContext(o);
		/*
		 * System.out.println("Internal context for system "+o.getName()+":");
		 * System.out.println(context2);
		 */
		/*for (BehaviorStatement b : o.getBehavior().getBody().getStatements()) {
			try {
				st.execute(b, context2);
			} catch (StatementException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}*/
		if (AssertEvaluator.canExecute(o, context)) {
			try {
				st.executeAll(o.getBehavior().getBody(), context2);
			} catch (StatementException e) {
				e.printStackTrace();
			}
		}
	}

	private void execute(MediatorDecl o, Context context) {
		Context context2 = context.subContext(o);
		/* System.out.println("Trying to execute mediator "+o.getName()); */
		/*
		 * for (BehaviorStatement b : o.getBehavior().getBody().getStatements()) { try {
		 * st.execute(b, context2); } catch (StatementException e) { // TODO
		 * Auto-generated catch block e.printStackTrace(); } }
		 */
		if (AssertEvaluator.canExecute(o, context)) {
			try {
				st.executeAll(o.getBehavior().getBody(), context2);
			} catch (StatementException e) {
				e.printStackTrace();
			}
		}
	}

	public void restart() {

	}

	private ConnectionRef ackOf(Connection n) {
		return new ConnectionRef(n.getName(), "ack");
	}

	private ConnectionRef reqOf(Connection n) {
		return new ConnectionRef(n.getName(), "req");
	}

	public void runCompleteSimulation() {
		while (time <= file.getMaxIt()) {
			this.step();
		}
	}

}
