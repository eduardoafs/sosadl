package org.archware.tools.mm.generators

import java.util.Collection
import org.eclipse.emf.ecore.EClassifier
import java.util.List
import org.eclipse.emf.ecore.EEnum
import java.util.Set
import java.util.Map
import org.eclipse.emf.ecore.EClass
import org.eclipse.emf.codegen.ecore.genmodel.GenPackage
import org.eclipse.emf.codegen.ecore.genmodel.GenEnum
import org.eclipse.emf.codegen.ecore.genmodel.GenEnumLiteral
import org.eclipse.emf.codegen.ecore.genmodel.GenClass
import java.util.TreeMap
import org.eclipse.emf.codegen.ecore.genmodel.GenFeature

class XtendGeneratorGenerator extends MyAbstractGenerator {
	val GenPackage genPackage;
	val Map<String, GenClass> genClasses;

	new(Collection<EClassifier> classifiers, List<EEnum> enums, Map<String, EClass> namedClasses,
		Map<String, Set<String>> cases, GenPackage genPackage) {
		super(classifiers, enums, namedClasses, cases)
		this.genPackage = genPackage
		val Map<String, GenClass> gc = new TreeMap
		genPackage.genClasses.forEach[c | gc.put(c.ecoreClass.name, c)]
		this.genClasses = gc.immutableCopy
	}

	def generate() '''
		// Automatically generated
		package «genPackage.qualifiedPackageName».generator
		
		import java.util.List
		import javax.annotation.Generated
		import org.eclipse.xtext.xbase.lib.Functions.Function1
		
		«genPackage.genEnums.map[c|'''import «c.qualifiedName»'''].join(lineSeparator())»
		
		«cases.values.flatten.toSet.map[c|'''import «genClasses.get(c).qualifiedInterfaceName»'''].join(lineSeparator())»
		
		@Generated(value = "«genPackage.getEcorePackage.name»")
		class CoqGenerator {
		
			def <T> _generateO(T t, Function1<? super T, ? extends CharSequence> gen) {
				if (t == null) {
					return "None"
				} else {
					return «"'''"»(Some «"«"»gen.apply(t)»)«"'''"»
				}
			}

			def <T> _generateL(List<T> l, Function1<? super T, ? extends CharSequence> gen) «"'''"»[«"«"»l.map(gen).join("; ")»]«"'''"»

			def generatebool(boolean b) {
				if (b) {
					return "true"
				} else {
					return "false"
				}
			}

			def generateZ(int i) {
				return Integer.toString(i)
			}

			def generatestring(String i) «"'''"»"«"«"»i»"«"'''"»
		
			«genPackage.genEnums.map[generateForEnum].join(lineSeparator())»
		
			«cases.entrySet.map[generateForType].join(lineSeparator())»
		}
	'''

	def generateForEnum(GenEnum e) '''
		def generate«e.name»(«e.name» n) {
			switch (n) {
				«e.genEnumLiterals.map[generateEnumCase].join(lineSeparator())»
			}
		}
	'''

	def generateEnumCase(GenEnumLiteral l) '''
		case «l.enumLiteralInstanceConstantName»: {
			return «"'''"»«l.ecoreEnumLiteral.name»«"'''"»
		}
	'''

	def generateForType(Map.Entry<String, Set<String>> typ) {
		if (typ.value.size == 1) {
			return generateForConstructor(typ.key, typ.value.get(0))
		} else {
			return '''«typ.value.map[c|generateForDispatchConstructor(typ.key, c)].join(lineSeparator())»'''
		}
	}

	def generateForConstructor(String typ, String c) '''
		def «generateMethod(typ, c)»
	'''

	def generateForDispatchConstructor(String typ, String c) '''
		def dispatch «generateMethod(typ, c)»
	'''
	
	def generateMethod(String typ, String c) '''CharSequence generate«namedClasses.get(typ).generateBaseType»(«c» n) «"'''"»«generateText(typ, c)»«"'''"»'''
	
	def generateText(String typ, String c) {
		val gc = genClasses.get(c)
		val gf = gc.allGenFeatures
		
		if(gf.empty) {
			return ctorName(typ, c)
		} else {
			return '''(«ctorName(typ, c)» «gf.map[generateParam].join(" ")»)'''
		}
	}
	
	def generateParam(GenFeature f) {
		val ef = f.ecoreFeature
		val bt = ef.EType.generateBaseType
		if(ef.many) {
			return '''«"«"»_generateL(n.«f.getAccessor»(), [generate«bt»])»'''
		} else if(ef.required) {
			return '''«"«"»generate«bt»(n.«f.getAccessor»())»'''
		} else {
			return '''«"«"»_generateO(n.«f.getAccessor»(), [generate«bt»])»'''			
		}
	}

	def static lineSeparator() '''

	'''
}
