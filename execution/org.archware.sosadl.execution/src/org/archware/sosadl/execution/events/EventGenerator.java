package org.archware.sosadl.execution.events;
import org.eclipse.emf.ecore.EObject;

public class EventGenerator {
	public static ExecutionEvent fromInternal(InternalEvent type, Object sender, Object... params) {
		switch (type) {
		case CONSTITUENT_EXECUTION: break;
		case MEDIATOR_EXECUTION: break;
		case NEW_CONNECTION: break;
		case NEW_NODE: break;
		case VALUE_CONSUMPTION: break;
		case VALUE_TRANSMISSION: break;
		}
		return null;
	}
}
