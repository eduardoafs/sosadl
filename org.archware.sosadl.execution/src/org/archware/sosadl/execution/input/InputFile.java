package org.archware.sosadl.execution.input;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;
import java.util.regex.MatchResult;

public class InputFile {
	private File file;
	private List<InputLine> lines;
	private int maxIt;

	public InputFile() {
		this.lines = new ArrayList<InputLine>();
	}
	
	public static InputFile init(File file) throws IOException {
		BufferedReader br = new BufferedReader(new FileReader(file));
		String line;
		InputFile newFile = new InputFile();
		newFile.file = file;
		
		// first line is setup
		String setupLine = br.readLine();
		while(setupLine.startsWith("#") || setupLine.isEmpty()) {
			setupLine = br.readLine();
		}
		Scanner sc = new Scanner(setupLine);
		sc.findInLine("(\\d*)");
		MatchResult result = sc.match();
		sc.close();
		int maxIt = Integer.parseInt(result.group(1));
		newFile.maxIt = maxIt;
		
		// then the controller lines
		while ((line=br.readLine())!=null) {
			 if (line.startsWith("#") || line.isEmpty()) continue; // ignore comment and empty lines
			 InputLine newLine = InputLine.fromString(line);
			 if (newLine!=null) newFile.lines.add(newLine);
		 }
		 //newFile.it = newFile.lines.iterator();
		br.close();
		return newFile;
	}
	
	
	public List<InputLine> getLines() {
		return lines;
	}
	
	public int getMaxIt() {
		return this.maxIt;
	}
	
	public File getFile() {
		return this.file;
	}
}
