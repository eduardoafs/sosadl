package org.archware.tools.mm.generators

import java.util.Collection
import java.util.List
import java.util.Map
import java.util.Set
import org.eclipse.emf.ecore.EClass
import org.eclipse.emf.ecore.EClassifier
import org.eclipse.emf.ecore.EEnum
import org.eclipse.emf.ecore.EEnumLiteral
import org.eclipse.emf.ecore.EStructuralFeature

class CoqGenerator extends MyAbstractGenerator {
	new(Collection<EClassifier> classifiers, List<EEnum> enums, Map<String, EClass> namedClasses, Map<String,Set<String>> cases) {
		super(classifiers, enums, namedClasses, cases)
	}
	
	def generate() '''
		Require Import List.
		Require Import String.
		Require Import BinInt.
		
		(**
		 * Type of the abstract syntax tree
		
		_This module has been automatically generated_.
		 *)
		
		«enums.map[generateEnum].join(lineSeparator)»

		«cases.entrySet.map[generateCaseType].join("Inductive ", lineWithSpace, ".", [x|x])»
		
		«cases.filter[t, ctors | ctors.size == 1].entrySet.map[generateAccessors].join(lineSeparator)»
		
	'''

	def generateEnum(EEnum e) '''
		Inductive «e.name»: Set :=
		«e.ELiterals.map[l|generateLiteralIn(l, e)].join("", lineSeparator, ".", [x|x])»
	'''

	def static generateLiteralIn(EEnumLiteral l, EEnum e) '''| «l.name»: «e.name»'''
	
	def generateCaseType(Map.Entry<String, Set<String>> type) '''
		t_«type.key»: Set :=
		«type.value.map[c | generateConstructor(type.key, c)].join(lineSeparator)»
	'''
	
	def generateConstructor(String t, String ctor) '''
		| «ctorName(t, ctor)»:«namedClasses.get(ctor).EAllStructuralFeatures.map[generateConstructorParameterType].join(" ", " -> ", " -> ", [x|x])» t_«t»'''

	def generateAccessors(Map.Entry<String, Set<String>> type) {
		return type.value.filter[c | !namedClasses.get(c).EAllStructuralFeatures.empty].map[c | generateAccessorsOf(type.key, c)].join(lineSeparator)
	}
	
	def generateAccessorsOf(String t, String ctor) {
		val features = namedClasses.get(ctor).EAllStructuralFeatures.map[name]
		return features.map[f | generateAccessor(t, ctor, f, features)].join(lineSeparator)
	}
	
	def generateAccessor(String t, String ctor, String field, List<String> features) '''
		Definition «ctorName(t, ctor)»_«field» x :=
			match x with
			| «ctorName(t, ctor)» «features.map[f | fieldIf(field, f, "y")].join(" ")» => y
			end.
	'''
	
	def static fieldIf(String a, String b, String name) {
		if (a.equals(b)) {
			return name
		} else {
			return "_"
		}
	}

	def static generateConstructorParameterType(EStructuralFeature f) {
		if (f.many) {
			return '''list «f.EType.generateBaseType»'''
		} else if (f.required) {
			return f.EType.generateBaseType
		} else {
			return '''option «f.EType.generateBaseType»'''
		}
	}
	
	def static lineSeparator() '''

	'''
	
	def static lineWithSpace() '''

		with '''
}
