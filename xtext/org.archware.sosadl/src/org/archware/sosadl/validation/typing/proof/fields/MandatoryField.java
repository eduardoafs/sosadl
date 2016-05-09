package org.archware.sosadl.validation.typing.proof.fields;

import java.util.Optional;
import java.util.function.Function;

public interface MandatoryField extends FieldDescriptor {
	Optional<CharSequence> get(Function<Object, CharSequence> process);
}
