package org.archware.sosadl.execution.events;
import org.eclipse.emf.ecore.EObject;

import events.Event;

public class EventGenerator {
	public static Event fromInternal(InternalEvent type, EObject sender, Object... params) {
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
