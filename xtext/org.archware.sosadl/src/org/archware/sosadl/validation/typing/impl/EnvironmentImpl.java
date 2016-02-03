package org.archware.sosadl.validation.typing.impl;

import org.archware.sosadl.validation.typing.EnvContent;
import org.archware.sosadl.validation.typing.Environment;

public class EnvironmentImpl implements Environment {
	@Override
	public EnvContent get(String name) {
		return null;
	}

	@Override
	public Environment put(String name, EnvContent info) {
		return new CellEnvironmentImpl(this, name, info);
	}

}
