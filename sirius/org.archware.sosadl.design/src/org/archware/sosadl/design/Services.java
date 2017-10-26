package org.archware.sosadl.design;

import java.util.List;

import org.archware.sosadl.sosADL.ComplexName;
import org.archware.sosadl.sosADL.Constituent;
import org.archware.sosadl.sosADL.DutyDecl;
import org.archware.sosadl.sosADL.EntityBlock;
import org.archware.sosadl.sosADL.GateDecl;
import org.archware.sosadl.sosADL.IdentExpression;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.SosADL;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.sosADL.Unify;
import org.archware.sosadl.validation.TypeInformation;
import org.eclipse.emf.common.util.BasicEList;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.util.CancelIndicator;
import org.eclipse.xtext.validation.CheckMode;
import org.eclipse.xtext.validation.IResourceValidator;
import org.eclipse.xtext.validation.Issue;

/**
 * The services class used by VSM.
 */
public class Services {
	
	/**
	 * See
	 * http://help.eclipse.org/neon/index.jsp?topic=%2Forg.eclipse.sirius.doc%
	 * 2Fdoc%2Findex.html&cp=24 for documentation on how to write service
	 * methods.
	 */

	/**
	 * TODO optimize this, read comments inside
	 * @param c constituent
	 * @return list of gates
	 */
	@SuppressWarnings("all")
	public EList<GateDecl> allGates(Constituent c) {
		// For some unknown reason, Xtext is not validating this resource
		XtextResource resource = (XtextResource) c.eResource();
		IResourceValidator validator = resource.getResourceServiceProvider().get(IResourceValidator.class);
		// Therefore I will validate it manually
        List<Issue> issues = validator.validate(resource, CheckMode.ALL, CancelIndicator.NullImpl);
        
		EObject e = TypeInformation.resolve((IdentExpression) c.getValue());
		
		if (e instanceof SystemDecl) {
			return ((SystemDecl) e).getGates();
		} else return null;
	}
	
	/**
	 * TODO optimize this, read comments inside
	 * @param c constituent
	 * @return list of duties
	 */
	@SuppressWarnings("all")
	public EList<DutyDecl> allDuties(Constituent c) {
		// For some unknown reason, Xtext is not validating this resource
		XtextResource resource = (XtextResource) c.eResource();
		IResourceValidator validator = resource.getResourceServiceProvider().get(IResourceValidator.class);
		// Therefore I will validate it manually
        List<Issue> issues = validator.validate(resource, CheckMode.ALL, CancelIndicator.NullImpl);
        
		EObject e = TypeInformation.resolve((IdentExpression) c.getValue());
		
		if (e instanceof MediatorDecl) {
			return ((MediatorDecl) e).getDuties();
		} else return null;
	}

	public GateDecl firstGate(Unify u) {
		return findGate(u.getConnLeft());
	}
	public GateDecl secondGate(Unify u) {
		return findGate(u.getConnRight());
	}

	public DutyDecl firstDuty(Unify u) {
		return findDuty(u.getConnLeft());
	}
	public DutyDecl secondDuty(Unify u) {
		return findDuty(u.getConnRight());
	}

	/**
	 * TODO
	 * resolves a complex name, returning a gate
	 * @param n
	 * @return
	 */
	private GateDecl findGate(ComplexName n) {
		String relevantName = n.getName().get(n.getName().size()-1);
		
		SosADL model = getModel(n);
		
		TreeIterator<EObject> t = model.eAllContents();
		EObject obj;
		// Scan all contents of the model, trying to find the gate
		while (t.hasNext()) {
			obj = t.next();
			if (obj instanceof GateDecl) {
				if (((GateDecl) obj).getName().equals(relevantName)) {
					return (GateDecl) obj;
				}
			}
		}
		return null;
	}
	
	/**
	 * TODO
	 * resolves a complex name, returning a duty
	 * @param n
	 * @return
	 */
	private DutyDecl findDuty(ComplexName n) {
		String relevantName = n.getName().get(n.getName().size()-1);
		
		SosADL model = getModel(n);
		
		TreeIterator<EObject> t = model.eAllContents();
		EObject obj;
		// Scan all contents of the model, trying to find the gate
		while (t.hasNext()) {
			obj = t.next();
			if (obj instanceof DutyDecl) {
				if (((DutyDecl) obj).getName().equals(relevantName)) {
					return (DutyDecl) obj;
				}
			}
		}
		return null;
	}
	
	/**
	 * 
	 * @param e
	 * @return
	 */
	public EList<EObject> availableConstituent(EObject e) {
		EList<EObject> constituents = new BasicEList<EObject>();
		
		SosADL find = getModel(e);

		// Now find is a SosADL
		EntityBlock entity = find.getContent().getDecls();
		
		// Add all systems and mediators
		constituents.addAll(entity.getSystems());
		constituents.addAll(entity.getMediators());
		
		// TODO resolve imports
		/*for (Import i : ((SosADL)find).getImports()) {
			String libName = i.getImportedLibrary();
		}*/
		
		return constituents;
	}
	
	private SosADL getModel(EObject o) {
		return (SosADL) EcoreUtil.getRootContainer(o);
	}
	
}
