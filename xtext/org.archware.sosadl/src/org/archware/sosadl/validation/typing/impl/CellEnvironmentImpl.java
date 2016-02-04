package org.archware.sosadl.validation.typing.impl;

import org.archware.sosadl.validation.typing.EnvContent;
import org.archware.sosadl.validation.typing.Environment;

public class CellEnvironmentImpl extends EnvironmentImpl implements Environment {
	private final Environment parent;
	private final String name;
	private final EnvContent info;

	public CellEnvironmentImpl(Environment parent, String name, EnvContent info) {
		this.parent = parent;
		this.name = name;
		this.info = info;
	}

	@Override
	public EnvContent get(String name) {
		if(name.equals(this.name)){
			return info;
		} else {
			return parent.get(name);
		}
	}

	public String getName() {
		return name;
	}
	
	public EnvContent getInfo() {
		return info;
	}
	
	public Environment getParent() {
		return parent;
	}
}
