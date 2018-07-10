package org.archware.sosadl.execution.ui;

import java.io.IOException;

import org.archware.sosadl.SosADLStandaloneSetup;
import org.archware.sosadl.execution.Simulator;
import org.archware.sosadl.execution.input.DataInject;
import org.archware.sosadl.sosADL.SosADL;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.internal.resources.File;
import org.eclipse.core.runtime.IPath;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.ui.ISources;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.resource.XtextResourceSet;

import com.google.inject.Injector;

public class ExecuteModel extends AbstractHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		TreeSelection tree = (TreeSelection) HandlerUtil.getVariable(event, ISources.ACTIVE_CURRENT_SELECTION_NAME);
		File file = (File) tree.getFirstElement();

		System.out.println("Executing "+file.getName()+"...");
		Injector injector = (new SosADLStandaloneSetup()).createInjectorAndDoEMFRegistration();

		XtextResourceSet resSet = injector.getInstance(XtextResourceSet.class);
		resSet.addLoadOption(XtextResource.OPTION_RESOLVE_ALL, Boolean.TRUE);

		IPath path = file.getFullPath();
		System.out.println(path);
		Resource resource = resSet.getResource(URI.createFileURI(path.toString()), true);
		SosADL model = (SosADL) resource.getContents().get(0);

		System.out.println("Setting up simulator...");
		Simulator sim = new Simulator(model);

		String confFile = null;
		// try to find the configuration file, look for the path
		java.io.File f = new java.io.File(file.getRawLocation().toString().replace(".sos", ".sosconf"));
		//System.out.println(file.getRawLocation().toString());
		if (f.exists()) {
			System.out.println("Configuration file automatically detected!");
			confFile = f.getAbsolutePath();
		}
		// otherwise, ask the user
		else {
			FileDialog dialog = new FileDialog(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), SWT.OPEN);
			dialog.setFilterExtensions(new String[] { "*.sosconf" });
			//dialog.setFilterPath("c:\\temp");
			confFile = dialog.open();
		}
		
		System.out.println("Configuration file: "+confFile+".\nSetting up configuration");
		try {
			sim.setup(confFile);
		} catch (IOException e) {
			System.out.println(e.getMessage());
			System.out.println("Unable to find configuration file, aborting...");
			return null;
		}
		
		// test
		System.out.println("Simulator ready");
		System.out.println("Architecture name: "+sim.getModel().getName());
		System.out.println("[Configuration]");
		System.out.println("# iterations: "+sim.getConfig().getNumIterations());
		System.out.println("External simulators:");
		for (String s : sim.getConfig().getExternalSimulators().keySet()) {
			System.out.println("# "+s+ "("+sim.getConfig().getExternalSimulators().get(s)+")");
		}
		System.out.println("Data injection:");
		for (DataInject i : sim.getConfig().getInjectionData()) {
			System.out.println("# "+i);
		}
		
	
		sim.init();
		System.out.println("Starting iteractions...");
		Thread thread = new Thread() {
			@Override
			public void run() {
				sim.runCompleteSimulation();
				System.out.println("Finished");
			}
		};
		thread.start();
		return null;
	}
}
