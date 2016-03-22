package org.archware.sosadl.validation;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;

public class ValidationError {
	public final String message;
	
	public final EObject target;
	
	public final EStructuralFeature feature;

	public ValidationError(String message, EObject target, EStructuralFeature feature) {
		super();
		this.message = message;
		this.target = target;
		this.feature = feature;
	}

	public String getMessage() {
		return message;
	}

	public EObject getTarget() {
		return target;
	}

	public EStructuralFeature getFeature() {
		return feature;
	}
}
