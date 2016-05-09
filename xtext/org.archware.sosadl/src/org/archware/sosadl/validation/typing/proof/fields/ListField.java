package org.archware.sosadl.validation.typing.proof.fields;

import java.util.List;
import java.util.Optional;
import java.util.function.Function;

public interface ListField extends FieldDescriptor {
	List<Optional<CharSequence>> get(Function<Object, CharSequence> process);
}
