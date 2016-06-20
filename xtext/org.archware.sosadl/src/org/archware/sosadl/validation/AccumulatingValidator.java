package org.archware.sosadl.validation;

import java.util.LinkedList;
import java.util.List;
import java.util.function.Consumer;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.xtext.validation.ValidationMessageAcceptor;

public class AccumulatingValidator implements ErrorCollector {
	private final List<ValidationError> errors = new LinkedList<>();

	public void consumeErrors(Consumer<ValidationError> c) {
		errors.stream().forEach(c);
	}

	@Override
	public void error(String message, EObject target, EStructuralFeature feature) {
		error(message, target, feature, ValidationMessageAcceptor.INSIGNIFICANT_INDEX);
	}

	@Override
	public void error(String message, EObject target, EStructuralFeature feature, int index) {
		if (target == null) {
			throw new NullPointerException();
		}
		errors.add(new ValidationError(message, target, feature, index));
	}
}
