package org.archware.sosadl.execution.input;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.archware.sosadl.execution.external.ConstituentPluginLoader;
import org.archware.sosadl.execution.external.ConstituentSimulator;
import org.archware.sosadl.sosADL.Constituent;
import org.archware.sosadl.sosADL.IdentExpression;
import org.archware.sosadl.utility.ModelUtils;

public class SimConfiguration {
	//private InputFile file;
	private ConstituentPluginLoader plugins;
	private HashMap<String, String> params;
	private String configFileName;
	private List<DataInject> inject;
	private HashMap<String, String> pluginPaths;
	
	public SimConfiguration(String filePath) throws IOException {
		params = new HashMap<String, String>();
		pluginPaths = new HashMap<String, String>();
		configFileName = filePath;
		inject = new ArrayList<DataInject>();
		
		File f = new File(filePath);
		BufferedReader br = new BufferedReader(new FileReader(f));
		String line;

		int currentState = -1;
		// first line is setup
		int lineNumber=1;
		while ((line=br.readLine())!=null) {
			lineNumber++;
			if (line.startsWith("#") || line.isEmpty()) continue;
			if (line.startsWith("[")) currentState = -1; // reset of states
			
			switch (currentState) {
			case 0: // init of configuration file
				String[] param = line.split("=");
				// add new parameters here
				params.put(param[0], param[1]);
				if (param[0].equals("pluginsDir")) {
					plugins = new ConstituentPluginLoader(param[1]);
				}
				break;
			case 1: // external behavior simulators
				String[] param1 = line.split("=");
				String constituent = param1[0];
				String path = param1[1];
				if (plugins==null) {
					System.out.println("No plugin directory specified, ignoring line "+lineNumber);
					continue;
				}
				try {
					plugins.loadConstituent(constituent, path);
				} catch (ClassNotFoundException e) {
					System.out.println("Unable to find class "+path);
					//e.printStackTrace();
				}
				break; 
			case 2: // data injection
				inject.add(DataInject.fromString(line));
				break;
			default: // transition state
				if (line.startsWith("[")) {
					String zone = line.replace("[", "").replace("]","").replace(" ", "");
					if (zone.equals("config")) currentState = 0;
					else if (zone.equals("simulators")) currentState = 1;
					else if (zone.equals("data")) currentState = 2;
					else throw new IOException("Unknown entry at line "+lineNumber);
				} else throw new IOException("Unknown entry at line "+lineNumber);
			}
		}
		br.close();
	}
	
	public boolean externalSimulatorExists(Constituent s) {
		return pluginPaths.containsKey(s.getName());
	}
	
	public ConstituentSimulator getExternalSimulator(Constituent s) {
		return plugins.getSimulator(pluginPaths.get(s.getName()));
	}
	
	public int getNumIterations() {
		try {
			return Integer.parseInt(params.get("iterations"));
		} catch(Exception e) {
			System.out.println("Unknown number of iterations, check config file: "+configFileName);
			return 0;
		}
	}
	
	public List<DataInject> getInjectionData() {
		return inject;
	}

	public HashMap<String, ?> getExternalSimulators() {
		return plugins.getPlugins();
	}
	
}
