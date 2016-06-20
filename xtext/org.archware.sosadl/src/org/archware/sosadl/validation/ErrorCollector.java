package org.archware.sosadl.validation;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;

/**
 * The interface of objects that can be used to report errors.
 * 
 * @author Jeremy Buisson
 */
public interface ErrorCollector {

	/**
	 * Report an error.
	 * 
	 * @param message
	 *            an error message
	 * @param target
	 *            the object in the abstract syntax tree at which the error is
	 *            reported
	 * @param feature
	 *            out-edge of {@value target} at which the error is reported
	 */
	void error(String message, EObject target, EStructuralFeature feature);

	void error(String message, EObject target, EStructuralFeature feature, int index);
}
