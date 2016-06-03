package org.archware.sosadl.validation;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;

public interface ErrorCollector {

	void error(String message, EObject target, EStructuralFeature feature);

}
