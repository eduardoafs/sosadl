package org.archware.sosadl.utility;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.archware.sosadl.sosADL.ArchBehaviorDecl;
import org.archware.sosadl.sosADL.ArchitectureDecl;
import org.archware.sosadl.sosADL.ComplexName;
import org.archware.sosadl.sosADL.Connection;
import org.archware.sosadl.sosADL.Constituent;
import org.archware.sosadl.sosADL.DutyDecl;
import org.archware.sosadl.sosADL.EntityBlock;
import org.archware.sosadl.sosADL.GateDecl;
import org.archware.sosadl.sosADL.IdentExpression;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.SosADL;
import org.archware.sosadl.sosADL.SosADLFactory;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.sosADL.Unit;
import org.archware.sosadl.validation.TypeInformation;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.util.CancelIndicator;
import org.eclipse.xtext.validation.CheckMode;
import org.eclipse.xtext.validation.IResourceValidator;
import org.eclipse.xtext.validation.Issue;

public class ModelUtils {
	static List<XtextResource> validatedResources = new ArrayList<XtextResource>();
	/**
	 * Goes up the the tree model until find an instance of class
	 * @param n
	 * @param class1
	 * @return
	 */
	static public EObject upUntilFind(EObject n, Class<? extends EObject> class1) {
		EObject obj = n;
		while((!class1.isAssignableFrom(obj.getClass())) && obj.getClass()!=SosADL.class) {
			obj = obj.eContainer();
		}
		return obj;
	}
	
	public static SosADL getModel(EObject o) {
		return (SosADL) EcoreUtil.getRootContainer(o);
	}

	@SuppressWarnings("all")
	public static EObject resolve(IdentExpression e) {
		XtextResource resource = (XtextResource) e.eResource();
		// check if resource was already validated -- significant performance update
		if (!validatedResources.contains(resource)) {
			// Therefore I will validate it manually
			System.out.println("Validating resource...");
			IResourceValidator validator = resource.getResourceServiceProvider().get(IResourceValidator.class);
			List<Issue> issues = validator.validate(resource, CheckMode.ALL, CancelIndicator.NullImpl);
			validatedResources.add(resource);
		}

		EObject o = TypeInformation.resolve(e);

		return o;
	}

	public static EObject resolve(ComplexName n) {
		// remake
		Iterator it =  n.getName().iterator();
		
		SosADL model = getModel(n);
		Iterator<EObject> t = model.eContents().iterator();
		EObject next;
		
		while (it.hasNext()) {
			
		}
		/*
		String relevantName = n.getName().get(n.getName().size() - 1);

		SosADL model = getModel(n);

		TreeIterator<EObject> t = model.eAllContents();
		EObject obj = model;
		// Scan all contents of the model, trying to find the gate
		while (t.hasNext()) {
			obj = t.next();
			if (obj instanceof DutyDecl) {
				if (((DutyDecl) obj).getName().equals(relevantName))
					return obj;
			} else if (obj instanceof GateDecl) {
				if (((GateDecl) obj).getName().equals(relevantName))
					return obj;
			} else if (obj instanceof Connection) {
				if (((Connection) obj).getName().equals(relevantName)) {
					int nameSize = n.getName().size();
					if (nameSize>1) {
						EObject container = obj.eContainer(); 
						String cName = container instanceof GateDecl? ((GateDecl)container).getName() : ((DutyDecl)container).getName();
						if (cName.equals(n.getName().get(nameSize-2))) {
							// Also, need to check the first part of the name
							if (nameSize>2) { // need to include this information
								EObject cContainer = container.eContainer();
								EObject s = resolve((IdentExpression)findConstituent(n).getValue());
								
								// cContainer must be equal to s
								if (cContainer.equals(s)) return obj;
								else continue;
							} else 
							// resolve the name of constituent
							// check if resolution is equal to container.eContainer()
							
							return obj;
						}
					}
				}
			} else if (obj instanceof SystemDecl) {
				if (((SystemDecl) obj).getName().equals(relevantName))
					return (SystemDecl) obj;
			} else if (obj instanceof MediatorDecl) {
				if (((MediatorDecl) obj).getName().equals(relevantName))
					return (MediatorDecl) obj;
			}
		}*/
		return null;
	}

	/**
	 * TODO implement me
	 * Finds a constituent at n.getName().get(0)
	 * @param n
	 * @return
	 */
	public static Constituent findConstituent(ComplexName n) {
		// ComplexNames are contained in Unify, Unifies are contained in ArchBehaviorDecl
		ArchBehaviorDecl e = (ArchBehaviorDecl) ModelUtils.upUntilFind(n, ArchBehaviorDecl.class);
		for (Constituent c : e.getConstituents()) {
			if (c.getName().equals(n.getName().get(0))) return c;
		}
		return null;
	}

	/**
	 * TODO implement me
	 * Better complex name resolver
	 * @param n
	 * @return
	 */
	public static EObject resolve2(ComplexName n) {
		EObject obj = null;
		// TODO implement me
		//SosADL model = getModel(n);
		//TreeIterator<EObject> t = model.eAllContents();

		for (int i = 0; i < n.getName().size(); i++) {

		}
		return obj;
	}
	
	public static String printName(ComplexName name) {
		String s = "";
		for (String p : name.getName()) {
			s = s + (s.isEmpty()? "" : ".") + p;
		}
		return s;
	}

	public static boolean areComplexNameEqual(ComplexName n1, ComplexName n2) {
		List ln1 = n1.getName();
		List ln2 = n2.getName();
		int size = ln1.size();
		if (ln2.size()!=size) return false;
		for (int index=0; index<size;index++) {
			if (!ln1.get(index).equals(ln2.get(index))) return false;
		}
		return true;
	}

	public static ComplexName createComplexName(String complexName) {
		ComplexName c = SosADLFactory.eINSTANCE.createComplexName();
		String[] s = complexName.split("."); 
		for (int i=0; i<s.length;i++) 
			c.getName().add(s[i]);
		return c;
	}

}
