package org.archware.sosadl.validation.typing;

import org.archware.sosadl.validation.typing.impl.EnvironmentImpl;

public interface Environment {
	public EnvContent get(String name);
	public Environment put(String name, EnvContent info);
	
	public static Environment empty() {
		return new EnvironmentImpl();
	}
}
