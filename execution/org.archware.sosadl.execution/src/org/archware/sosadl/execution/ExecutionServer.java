package org.archware.sosadl.execution;

import java.io.EOFException;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.SocketException;
import java.util.ArrayList;

import org.archware.sosadl.execution.events.EventStorage;

import events.Event;
import requests.Request;
import responses.Events;
import responses.Init;
import responses.TraceStart;

public class ExecutionServer {
	static Simulator simu;
	static boolean end = false;
	/** stores several events together before sending them */
	static Events events;
	/** number of events to send simultaneously */
	static int eventsSize = 50;
	/** port to listen on */
	static int port = 4242;

	public void start() {
		try {
			ServerSocket ss = new ServerSocket(port);
			System.out.println("Listening on localhost:" + port);
			while (!end) {
				Socket client = ss.accept();
				System.out.println("New client connected.");
				ObjectInputStream ois = new ObjectInputStream(client.getInputStream());
				ObjectOutputStream oos = new ObjectOutputStream(client.getOutputStream());
				Request r = Request.INIT;
				System.out.println("Wating for requests from client.");
				while (r != Request.END) {
					try {
						r = (Request) ois.readObject();
						switch (r) {
						case INIT:
							System.out.println("Received INIT request");
							//simu = new Simulator(3, 2); // TODO FIXME
							oos.writeObject(new Init());
							System.out.println("Answered INIT");
							break;
						case NEW_STATE:
							System.out.println("Received NEW_STATE request");
							oos.writeObject(events);
							System.out.println("Sent Events");
							fillEvents();
							break;
						case NEW_TRACE:
							System.out.println("Received NEW_TRACE request");
							simu.restart();
							oos.writeObject(new TraceStart());
							System.out.println("Sent TRACE_START msg");
							fillEvents();
							break;
						case END:
							System.out.println("Received END request");
							end = true;
							break;
						default:
							System.err.println("Unknown request" + r);
							break;

						}
					} catch (ClassNotFoundException e) {
						System.err.println("Unable to undestand request from the client: " + e.getMessage());
					} catch (EOFException e) {
						System.err.println("client closed connection unexepectedly");
						r = Request.END;
					} catch (SocketException e) {
						System.err.println("connection problem - aborting session");
						r = Request.END;
					}
				}
				client.close();
			}
			ss.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

	private void fillEvents() {
		ArrayList<Event> evs = new ArrayList<Event>();
		for (int i = 0; i < eventsSize; i++) {
			evs.addAll(EventStorage.getInstance().popEvents());
		}
		events = new Events(evs);
	}
}
