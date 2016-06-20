package org.archware.sosadl.validation;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;

public class ValidationError {
	public final String message;
	
	public final EObject target;
	
	public final EStructuralFeature feature;
	
	public final int index;

	public ValidationError(String message, EObject target, EStructuralFeature feature, int index) {
		super();
		this.message = message;
		this.target = target;
		this.feature = feature;
		this.index = index;
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
	
	public int getIndex() {
		return index;
	}
}
