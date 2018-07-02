package org.archware.sosadl.execution.external;

import java.io.File;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.HashMap;

public class ConstituentPluginLoader {
	private HashMap<String, ConstituentSimulator> simulators;
	private ClassLoader loader;

	public ConstituentPluginLoader(String directory) {
		File pluginsDir = new File(System.getProperty("user.dir") + directory);
		System.out.println("Searching for plugins in folder: " + pluginsDir.getAbsolutePath());
		loader = getClass().getClassLoader();
		simulators = new HashMap<String, ConstituentSimulator>();

		for (File jar : pluginsDir.listFiles()) {
			try {
				System.out.println("Jar found: " + jar.getAbsolutePath());
				loader = URLClassLoader.newInstance(new URL[] { jar.toURL() }, loader);
			} catch (MalformedURLException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}

	public void loadConstituent(String constituent, String classpath) throws ClassNotFoundException {
		// File pluginsDir = new File(System.getProperty("user.dir") + directory);
		// System.out.println("Working directory: " + pluginsDir.getAbsolutePath());
		try {
			Class<?> clazz = Class.forName(classpath, true, loader);
			Class<?> newClass = clazz.asSubclass(ConstituentSimulator.class);
			// Apparently its bad to use Class.newInstance, so we use
			// newClass.getConstructor() instead
			Constructor<?> constructor;
			constructor = newClass.getConstructor();
			simulators.put(constituent, (ConstituentSimulator) constructor.newInstance());
			System.out.println("Loaded external simulator: "+constituent+" ("+classpath+")");
		} catch (NoSuchMethodException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (SecurityException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InstantiationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InvocationTargetException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public boolean checkSimulator(String constituent) {
		return simulators.containsKey(constituent);
	}

	public ConstituentSimulator getSimulator(String constituent) {
		return simulators.get(constituent);
	}

	public HashMap<String, ConstituentSimulator> getPlugins() {
		return simulators;
	}

}