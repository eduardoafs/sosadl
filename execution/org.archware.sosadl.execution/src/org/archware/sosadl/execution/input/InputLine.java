package org.archware.sosadl.execution.input;

import java.util.Scanner;
import java.util.regex.MatchResult;

import org.archware.sosadl.sosADL.ComplexName;
import org.archware.sosadl.sosADL.SosADLFactory;

public class InputLine {
	private int it;
	private ComplexName name;
	private String value;

	public InputLine(int it, ComplexName id, String value) {
		this.it = it;
		this.name = id;
		this.value = value;
	}

	public static InputLine fromString(String line) {
		Scanner sc = new Scanner(line);
		MatchResult result = null;
		try {
			sc.findInLine("(\\d*)\\s(\\S*)\\s(.*)");
			result = sc.match();
			sc.close();
		} catch (Exception e) {
			return null;
		}

		int it = Integer.parseInt(result.group(1));
		String complexName = result.group(2);
		String value = result.group(3);

		ComplexName name = SosADLFactory.eINSTANCE.createComplexName();
		// initialize complex name
		String[] names = complexName.split("\\.");
		for (String s : names) {
			name.getName().add(s);
		}
		return new InputLine(it, name, value);
	}

	public String toString() {
		return "Step " + it + ", name: " + printName() + ", value: " + value;
	}

	public String printName() {
		String s = "";
		for (String p : this.name.getName()) {
			s = s + ">" + p;
		}
		return s;
	}

	public int getNumber() {
		return it;
	}

	public ComplexName getName() {
		return name;
	}

	public Object getValue() {
		return value;
	}
}
