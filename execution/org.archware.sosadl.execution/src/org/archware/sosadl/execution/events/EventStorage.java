package org.archware.sosadl.execution.events;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.emf.ecore.EObject;

import events.Event;


public class EventStorage {
	private List<Event> events;
	
	private static EventStorage instance;
	
	private EventStorage() {
		events = new ArrayList<Event>();
	}
	
	public static EventStorage getInstance() {
		if (instance==null) instance = new EventStorage();
		return instance;
	}
	
	public void addEvent(InternalEvent type, EObject sender, Object... params) {
		events.add(EventGenerator.fromInternal(type, sender, params));
	}
	
	public List<Event> popEvents() {
		List<Event> oldList = events;
		events = new ArrayList<Event>();
		
		return oldList;
	}
}
