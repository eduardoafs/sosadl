package org.archware.tools.mm.generators

import java.util.List
import org.eclipse.emf.ecore.EEnum
import java.util.Map
import org.eclipse.emf.ecore.EClassifier
import org.eclipse.emf.ecore.EClass
import java.util.Set
import java.util.TreeMap
import java.util.Collection
import java.util.TreeSet
import org.eclipse.emf.ecore.EcorePackage

class MyAbstractGenerator {
	protected val List<EEnum> enums
	protected val Map<String, EClassifier> namedClassifiers
	protected val Map<String, EClass> namedClasses
	protected val Map<String, Set<String>> cases
	protected val Map<String, Set<String>> revertedCases

	new(Collection<EClassifier> classifiers, List<EEnum> enums, Map<String, EClass> namedClasses,
		Map<String, Set<String>> cases) {
		this.enums = enums.immutableCopy
		this.namedClasses = namedClasses.immutableCopy
		this.cases = cases.immutableCopy

		val nc = new TreeMap
		classifiers.forEach[c|nc.put(c.name, c)]
		namedClassifiers = nc.immutableCopy

		val rc = new TreeMap
		cases.forEach[k, v|v.forEach[c|rc.put(c, new TreeSet)]]
		cases.forEach[k, v|v.forEach[c|rc.get(c).add(k)]]
		revertedCases = rc.immutableCopy
	}

	def static generateBaseType(EClassifier f) {
		switch f {
			case EcorePackage.Literals.EBOOLEAN:
				return "bool"
			case EcorePackage.Literals.EINT:
				return "Z"
			case EcorePackage.Literals.ESTRING:
				return "string"
			default:
				if (f instanceof EEnum) {
					return f.name
				} else {
					return '''t_«f.name»'''
				}
		}
	}

	def ctorName(String t, String ctor) {
		if (revertedCases.get(ctor).size >= 2) {
			return '''«t»_«ctor»'''
		} else {
			return ctor
		}
	}

}
