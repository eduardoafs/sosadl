package org.archware.sosadl.execution.ui;

import java.io.IOException;

import org.archware.sosadl.SosADLStandaloneSetup;
import org.archware.sosadl.execution.Simulator;
import org.archware.sosadl.execution.input.InputLine;
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

		System.out.println(file.getName());
		XtextResource res;
		Injector injector = (new SosADLStandaloneSetup()).createInjectorAndDoEMFRegistration();

		XtextResourceSet resSet = injector.getInstance(XtextResourceSet.class);
		resSet.addLoadOption(XtextResource.OPTION_RESOLVE_ALL, Boolean.TRUE);

		IPath path = file.getFullPath();
		System.out.println(path);
		Resource resource = resSet.getResource(URI.createFileURI(path.toString()), true);
		SosADL model = (SosADL) resource.getContents().get(0);

		System.out.println("Setting up simulator...");
		Simulator sim = new Simulator(model);

		FileDialog dialog = new FileDialog(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), SWT.OPEN);
		dialog.setFilterExtensions(new String[] { "*.sosconf" });
		//dialog.setFilterPath("c:\\temp");
		String confFile = dialog.open();

		try {
			sim.setInputFile(confFile);
		} catch (IOException e) {
			System.out.println(e.getMessage());
			System.out.println("Unable to find configuration file, aborting...");
			return null;
		}
		
		// test
		System.out.println("Simulator ready");
		System.out.println("Architecture name: "+sim.getModel().getName());
		System.out.println("Config file:");
		for (InputLine i : sim.getFile().getLines()) {
			System.out.println(i);
		}
		
		sim.init();
		System.out.println("Starting iteractions...");
		sim.runCompleteSimulation();
		System.out.println("Finished");
		return null;
	}
}
