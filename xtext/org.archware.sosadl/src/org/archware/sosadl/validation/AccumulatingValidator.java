package org.archware.sosadl.validation;

import java.util.LinkedList;
import java.util.List;
import java.util.function.Consumer;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;

public class AccumulatingValidator {
	private final List<ValidationError> errors = new LinkedList<>();

	public void consumeErrors(Consumer<ValidationError> c) {
		errors.stream().forEach(c);
	}
	
	protected void error(String message, EObject target, EStructuralFeature feature) {
		errors.add(new ValidationError(message, target, feature));
	}
}
