package org.archware.sosadl.generator;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

public class HierarchicalStringBuilder extends StringBuilderAppender implements CharSequence, Appendable {
	private List<StringBuilderAppender> store = new LinkedList<>();
	
	private static class CharSequenceAppender extends StringBuilderAppender {
		private final CharSequence s;
		
		public CharSequenceAppender(CharSequence s) {
			this.s = s;
		}

		@Override
		public void appendTo(StringBuilder sb) {
			sb.append(s);
		}
	}
	
	private static class CharSubsequenceAppender extends StringBuilderAppender {
		private final CharSequence s;
		private final int start;
		private final int end;

		public CharSubsequenceAppender(CharSequence s, int start, int end) {
			super();
			this.s = s;
			this.start = start;
			this.end = end;
		}

		@Override
		public void appendTo(StringBuilder sb) {
			sb.append(s, start, end);
		}
	}
	
	private static class CharAppender extends StringBuilderAppender {
		private final char c;

		public CharAppender(char c) {
			super();
			this.c = c;
		}

		@Override
		public void appendTo(StringBuilder sb) {
			sb.append(c);
		}
	}
	
	private static final int FACTOR = 16;
	
	private transient String cache = null;

	@Override
	public int length() {
		return toString().length();
	}

	@Override
	public char charAt(int index) {
		return toString().charAt(index);
	}

	@Override
	public CharSequence subSequence(int start, int end) {
		return toString().subSequence(start, end);
	}
	
	@Override
	public String toString() {
		if(cache == null) {
			StringBuilder sb = new StringBuilder(store.size() * FACTOR);
			appendTo(sb);
			cache = sb.toString();
		}
		return cache;
	}
	
	@Override
	public void appendTo(StringBuilder sb) {
		for(StringBuilderAppender s: store) {
			((StringBuilderAppender) s).appendTo(sb);
		}
	}

	@Override
	public Appendable append(CharSequence csq) throws IOException {
		if(csq instanceof StringBuilderAppender) {
			store.add((StringBuilderAppender) csq);
		} else {
			store.add(new CharSequenceAppender(csq));
		}
		return this;
	}

	@Override
	public Appendable append(CharSequence csq, int start, int end) throws IOException {
		store.add(new CharSubsequenceAppender(csq, start, end));
		return this;
	}

	@Override
	public Appendable append(char c) throws IOException {
		store.add(new CharAppender(c));
		return this;
	}
}
