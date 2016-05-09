package org.archware.sosadl.validation.typing.proof;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Stream;

import org.archware.sosadl.validation.typing.proof.fields.EludedField;
import org.archware.sosadl.validation.typing.proof.fields.FieldDescriptor;
import org.archware.sosadl.validation.typing.proof.fields.ListField;
import org.archware.sosadl.validation.typing.proof.fields.MandatoryField;
import org.archware.sosadl.validation.typing.proof.fields.OptionalField;
import org.eclipse.xtext.xbase.lib.ListExtensions;
import org.eclipse.xtext.xbase.lib.StringExtensions;

public interface ProofTerm {
	default String getConstructorName() {
		Class<?> c = this.getClass();
		CoqConstructor cc = c.getAnnotation(CoqConstructor.class);
		if (cc != null) {
			return cc.value();
		} else {
			return StringExtensions.toFirstLower(c.getSimpleName());
		}
	}

	default FieldDescriptor[] getDeclaredFields() {
		Class<?> c = this.getClass();
		FieldDescriptor[] f = Stream.of(c.getDeclaredFields()).map(this::describeField)
				.toArray((s) -> new FieldDescriptor[s]);
		return f;
	}

	default FieldDescriptor describeField(Field f) {
		if (f.isAnnotationPresent(Eluded.class)) {
			return new EludedField() {
				@Override
				public Field getField() {
					return f;
				}
			};
		} else {
			try {
				Method getter = f.getDeclaringClass().getMethod("get" + StringExtensions.toFirstUpper(f.getName()));
				Object content = getter.invoke(this);
				if (List.class.isAssignableFrom(f.getType())) {
					if (f.isAnnotationPresent(CoqLiteral.class)) {
						return new ListField() {
							@Override
							public List<Optional<CharSequence>> get(Function<Object, CharSequence> process) {
								return ListExtensions.map((List<?>) content,
										(x) -> Optional.ofNullable((CharSequence) x));
							}

							@Override
							public Field getField() {
								return f;
							}
						};
					} else {
						return new ListField() {
							@Override
							public List<Optional<CharSequence>> get(Function<Object, CharSequence> process) {
								return ListExtensions.map((List<?>) content,
										(x) -> Optional.ofNullable(x).map(process));
							}

							@Override
							public Field getField() {
								return f;
							}
						};
					}
				} else {
					if (f.isAnnotationPresent(CoqLiteral.class) && CharSequence.class.isAssignableFrom(f.getType())) {
						Optional<CharSequence> c = Optional.ofNullable((CharSequence) content);
						if (f.isAnnotationPresent(Mandatory.class)) {
							return new MandatoryField() {
								@Override
								public Optional<CharSequence> get(Function<Object, CharSequence> process) {
									return c;
								}

								@Override
								public Field getField() {
									return f;
								}
							};
						} else {
							return new OptionalField() {
								@Override
								public Optional<CharSequence> get(Function<Object, CharSequence> process) {
									return c;
								}

								@Override
								public Field getField() {
									return f;
								}
							};
						}
					} else {
						Optional<?> c = Optional.ofNullable(content);
						if (f.isAnnotationPresent(Mandatory.class)) {
							return new MandatoryField() {
								@Override
								public Optional<CharSequence> get(Function<Object, CharSequence> process) {
									return c.map(process);
								}

								@Override
								public Field getField() {
									return f;
								}
							};
						} else {
							return new OptionalField() {
								@Override
								public Optional<CharSequence> get(Function<Object, CharSequence> process) {
									return c.map(process);
								}

								@Override
								public Field getField() {
									return f;
								}
							};
						}
					}
				}
			} catch (NoSuchMethodException | SecurityException | IllegalAccessException | IllegalArgumentException
					| InvocationTargetException e) {
				String msg = "field: " + f.toGenericString();
				throw new IllegalArgumentException(msg, e);
			}
		}
	}
}
