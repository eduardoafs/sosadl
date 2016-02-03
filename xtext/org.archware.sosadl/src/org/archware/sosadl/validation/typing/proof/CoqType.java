package org.archware.sosadl.validation.typing.proof;

import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

@Target({ElementType.FIELD, ElementType.TYPE})
public @interface CoqType {
	String value();
}
