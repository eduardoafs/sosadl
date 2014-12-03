package org.archware.tools.mm.handlers;

import java.util.Collection;
import java.util.stream.Collectors;

import org.eclipse.emf.ecore.EClassifier;

public class MmTypeNotSupported extends MmNotSupportedException {
	private static final long serialVersionUID = 935291648040299721L;

	private Collection<EClassifier> badTypes;

	public MmTypeNotSupported(Collection<EClassifier> badTypes) {
		this.badTypes = badTypes;
	}

	@Override
	public String getMessage() {
		return badTypes.stream().map(EClassifier::getName).sorted().distinct()
				.collect(Collectors.joining(", ", "[", "]"));
	}
}
