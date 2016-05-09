package org.archware.sosadl.validation.typing.proof;

import java.lang.reflect.Field;
import java.util.Optional;

import org.archware.sosadl.validation.typing.proof.fields.FieldDescriptor;

public class ProofTermPlaceHolder implements ProofTerm {
	private Optional<ProofTerm> proxy;
	
	public ProofTermPlaceHolder() {
		this.proxy = Optional.empty();
	}
	
	public void fillWith(ProofTerm p) {
		this.proxy = Optional.of(p);
	}

	@Override
	public String getConstructorName() {
		return this.proxy.get().getConstructorName();
	}

	@Override
	public FieldDescriptor[] getDeclaredFields() {
		return this.proxy.get().getDeclaredFields();
	}

	@Override
	public FieldDescriptor describeField(Field f) {
		return this.proxy.get().describeField(f);
	}
}
