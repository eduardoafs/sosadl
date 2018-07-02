package org.archware.sosadl.execution.input;

import java.util.Scanner;
import java.util.regex.MatchResult;

import org.archware.sosadl.sosADL.ComplexName;
import org.archware.sosadl.utility.ModelUtils;

public class DataInject {
	private int it;
	private ComplexName name;
	private String value;

	public DataInject(int it, ComplexName id, String value) {
		this.it = it;
		this.name = id;
		this.value = value;
	}

	public static DataInject fromString(String line) {
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

		// initialize complex name
		ComplexName name = ModelUtils.createComplexName(complexName);
		DataInject newD = new DataInject(it, name, value);
		//System.out.println("New DataInject: "+newD);
		return newD;
	}

	public String toString() {
		return "Step " + it + ", name: " + ModelUtils.printName(name) + ", value: " + value;
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
