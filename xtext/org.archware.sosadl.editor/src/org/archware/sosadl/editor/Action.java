package org.archware.sosadl.editor;

import java.util.Iterator;
import java.util.List;

import org.archware.sosadl.sosADL.ArchBehaviorDecl;
import org.archware.sosadl.sosADL.Constituent;
import org.archware.sosadl.sosADL.IdentExpression;
import org.archware.sosadl.sosADL.impl.SoSImpl;
import org.archware.sosadl.sosADL.impl.SosADLImpl;
import org.archware.sosadl.validation.TypeInformation;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.xmi.impl.XMIResourceFactoryImpl;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.util.CancelIndicator;
import org.eclipse.xtext.validation.CheckMode;
import org.eclipse.xtext.validation.IResourceValidator;
import org.eclipse.xtext.validation.Issue;

public class Action implements IObjectActionDelegate {

	public Action() {
		// TODO Auto-generated constructor stub
	}

	private ISelection currentSelection;

	@Override
	public void run(IAction action) {
		IStructuredSelection iss = (IStructuredSelection) currentSelection;
		for (Iterator<?> iterator = iss.iterator(); iterator.hasNext();) {
			try {
				loadModel((IFile) iterator.next());
			} catch (Exception e) {
				throw new RuntimeException(e);
			}
		}
	}

	

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		this.currentSelection = selection;
	}

	@Override
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		// TODO Auto-generated method stub
		
	}
	
	private void loadModel(IFile file) {
        ResourceSet resourceSet = new ResourceSetImpl();
        URI fileURIModelSource = URI.createFileURI(file.getFullPath().toString());

        XtextResource resource = (XtextResource) resourceSet.getResource(fileURIModelSource, true);
        IResourceValidator validator = resource.getResourceServiceProvider().get(IResourceValidator.class);
        List<Issue> issues = validator.validate(resource, CheckMode.ALL, CancelIndicator.NullImpl);
        
        System.out.println(resource.getContents());
        EObject obj = resource.getContents().get(0);
        SoSImpl s = (SoSImpl) ((SosADLImpl) obj).getContent();
        TreeIterator<EObject> tree = s.eAllContents();
        EObject c;
        while (tree.hasNext()) {
        	c = tree.next();
            //System.out.println("Teste: "+c.getName());
        	if (c instanceof ArchBehaviorDecl) {
                System.out.println("Found! "+c.getClass().getName());
                for (Constituent co : ((ArchBehaviorDecl) c).getConstituents()) {
                	System.out.println("Constituent: "+co.getName());
                	System.out.println("Expr: "+co.getValue().getClass().getName());
                	System.out.println("Evaluating...");
                	EObject sys = TypeInformation.resolve((IdentExpression)co.getValue());
                	System.out.println(sys);
                }
        	}
        }
	}

}
