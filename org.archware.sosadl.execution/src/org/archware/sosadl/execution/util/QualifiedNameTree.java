package org.archware.sosadl.execution.util;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.archware.sosadl.sosADL.ComplexName;

public class QualifiedNameTree<T> {
	private QualifiedNameNode<T> root;
	
	public QualifiedNameTree() {
		root = new QualifiedNameNode<T>(null,null);
	}
	
	public void push(ComplexName key, T value) {
		QualifiedNameNode entry = root;
		Iterator t = key.getName().iterator();
		while (t.hasNext()) {
			String cur = (String) t.next();
			// search in the children for the current key
			entry = entry.getChildrenByKey(cur);
		}
		entry.value = value;
	}
	
	public T get(ComplexName key) {
		QualifiedNameNode needle = root;
		Iterator t=  key.getName().iterator();
		while (t.hasNext()) {
			String cur = (String) t.next();
			needle = needle.getChildrenByKey(cur);
		}
		return (T) needle.value;
	}
	
	private class QualifiedNameNode<T> {
		public QualifiedNameNode(String key, T value) {
			this.key = key;
			this.value = value;
			children = new ArrayList<QualifiedNameNode>();
		}
		
		public QualifiedNameNode getChildrenByKey(String cur) {
			for (QualifiedNameNode t : children) {
				if (t.key.equals(cur)) return t;
			}
			// if not found, create new
			QualifiedNameNode newT = new QualifiedNameNode(cur, null);
			this.children.add(newT); // add to the children
			return newT;
		}

		public String key;
		public T value;
		public List<QualifiedNameNode> children;
	}
}
