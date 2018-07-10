package org.archware.sosadl.execution.events;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.emf.ecore.EObject;


public class EventStorage {
	private List<ExecutionEvent> events;
	
	private static EventStorage instance;
	
	private EventStorage() {
		events = new ArrayList<ExecutionEvent>();
	}
	
	public static EventStorage getInstance() {
		if (instance==null) instance = new EventStorage();
		return instance;
	}
	
	public void addEvent(InternalEvent type, Object sender, Object... params) {
		events.add(EventGenerator.fromInternal(type, sender, params));
	}
	
	public List<ExecutionEvent> popEvents() {
		List<ExecutionEvent> oldList = events;
		events = new ArrayList<ExecutionEvent>();
		
		return oldList;
	}
}
