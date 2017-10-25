package org.archware.sosadl.design;

import java.util.List;

import org.archware.sosadl.sosADL.Constituent;
import org.archware.sosadl.sosADL.DutyDecl;
import org.archware.sosadl.sosADL.GateDecl;
import org.archware.sosadl.sosADL.IdentExpression;
import org.archware.sosadl.sosADL.MediatorDecl;
import org.archware.sosadl.sosADL.SystemDecl;
import org.archware.sosadl.validation.TypeInformation;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;
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

}
