/*
 * generated by Xtext
 */
package org.archware.sosadl.generator

import java.lang.reflect.Field
import org.archware.sosadl.sosADL.ActionSuite
import org.archware.sosadl.sosADL.ArchBehaviorDecl
import org.archware.sosadl.sosADL.ArchitectureDecl
import org.archware.sosadl.sosADL.Assert
import org.archware.sosadl.sosADL.AssertionDecl
import org.archware.sosadl.sosADL.Behavior
import org.archware.sosadl.sosADL.BehaviorDecl
import org.archware.sosadl.sosADL.BehaviorStatement
import org.archware.sosadl.sosADL.Binding
import org.archware.sosadl.sosADL.ComplexName
import org.archware.sosadl.sosADL.Connection
import org.archware.sosadl.sosADL.Constituent
import org.archware.sosadl.sosADL.ConstructedValue
import org.archware.sosadl.sosADL.DataType
import org.archware.sosadl.sosADL.DataTypeDecl
import org.archware.sosadl.sosADL.DutyDecl
import org.archware.sosadl.sosADL.ElementInConstituent
import org.archware.sosadl.sosADL.EntityBlock
import org.archware.sosadl.sosADL.Expression
import org.archware.sosadl.sosADL.FieldDecl
import org.archware.sosadl.sosADL.FormalParameter
import org.archware.sosadl.sosADL.FunctionDecl
import org.archware.sosadl.sosADL.GateDecl
import org.archware.sosadl.sosADL.Import
import org.archware.sosadl.sosADL.MediatorDecl
import org.archware.sosadl.sosADL.Multiplicity
import org.archware.sosadl.sosADL.Protocol
import org.archware.sosadl.sosADL.ProtocolActionSuite
import org.archware.sosadl.sosADL.ProtocolDecl
import org.archware.sosadl.sosADL.ProtocolStatement
import org.archware.sosadl.sosADL.Quantifier
import org.archware.sosadl.sosADL.SosADL
import org.archware.sosadl.sosADL.SystemDecl
import org.archware.sosadl.sosADL.TupleElement
import org.archware.sosadl.sosADL.Unit
import org.archware.sosadl.sosADL.Valuing
import org.archware.sosadl.sosADL.generator.CoqGenerator
import org.archware.sosadl.validation.SosADLValidator
import org.archware.sosadl.validation.typing.Environment
import org.archware.sosadl.validation.typing.impl.CellEnvironmentImpl
import org.archware.sosadl.validation.typing.impl.SystemEnvContent
import org.archware.sosadl.validation.typing.impl.TypeEnvContent
import org.archware.sosadl.validation.typing.proof.CoqConstructor
import org.archware.sosadl.validation.typing.proof.Eluded
import org.archware.sosadl.validation.typing.proof.Mandatory
import org.archware.sosadl.validation.typing.proof.ProofTerm
import org.eclipse.emf.common.util.EList
import org.eclipse.emf.ecore.resource.Resource
import org.eclipse.xtext.generator.IFileSystemAccess
import org.eclipse.xtext.generator.IGenerator
import java.math.BigInteger
import org.archware.sosadl.validation.typing.impl.VariableEnvContent
import org.archware.sosadl.validation.typing.EnvContent
import org.archware.sosadl.validation.typing.proof.CoqLiteral
import org.archware.sosadl.validation.typing.impl.EnvironmentImpl

/**
 * Generates code from your model files on save.
 * 
 * see http://www.eclipse.org/Xtext/documentation.html#TutorialCodeGeneration
 */
class TypingProofGenerator implements IGenerator {
	var coqGenerator = new CoqGenerator

	override void doGenerate(Resource resource, IFileSystemAccess fsa) {

		for (e : resource.allContents.toIterable.filter(SosADL)) {
	        var String resourceFilename = e.eResource.URI.trimFileExtension.lastSegment
			fsa.generateFile(resourceFilename+"_typing.v", e.generate)
		}
	}
	
	def generate(SosADL s) '''
	Require Import SosADL.Environment.
	Require Import SosADL.TypeSystem.
	Require Import SosADL.SosADL.
	Require Import SosADL.Interpretation.
	Require Import String.
	Require Import List.
	Require Import BinInt.
	
	Import ListNotations.
	
	Local Open Scope list_scope.
	Local Open Scope string_scope.
	Local Open Scope Z_scope.
	
	Axiom admitted: forall (A: Prop), A.
	
	Definition well_typed: SoSADL («coqGenerator.generatet_SosADL(s)») well typed :=
	«generateProofOf(s)».
	'''
	
	def generateProofOf(SosADL s) {
		generateProof(SosADLValidator.getProof(s) as ProofTerm)
	}
	
	def CharSequence generateProof(ProofTerm p) {
		var clazz = p.class
		return '''(«clazz.ctorName»
		    «FOR i : clazz.declaredFields»
      			«processField(p, clazz, i)»
    		«ENDFOR»)'''
	}
	
	def processField(ProofTerm p, Class<?> clazz, Field f) {
		if(f.isAnnotationPresent(Eluded)) {
			return '''_'''
		} else {
			var mandatory = f.isAnnotationPresent(Mandatory)
			var literal = f.isAnnotationPresent(CoqLiteral)
			var content = getByGetter(p, clazz, f)
			return processAny(mandatory, literal, content)
		}
	}
	
	def CharSequence processAny(boolean mandatory, boolean literal, Object content) {
		if(mandatory && content == null) {
			return '''(admitted _)'''
		} else if(content instanceof EList<?>) {
			return coqGenerator._generateL(content as EList<?>, [x | processAny(true, literal, x)])
		} else {
			var genfun = [Object x | generatorFunction(x) as CharSequence]
			if(literal) {
				genfun = [Object x | x as CharSequence ]
			}
			if(mandatory) {
				return genfun.apply(content)
			} else {
				return coqGenerator._generateO(content, genfun)
			}
		}
	}
	
	def dispatch generatorFunction(Integer content) { return coqGenerator.generateZ(content) }
	def dispatch generatorFunction(BigInteger content) { return content.toString }
	def dispatch generatorFunction(String content) { return coqGenerator.generatestring(content) }
	def dispatch generatorFunction(Boolean content) { return coqGenerator.generatebool(content) }
	def dispatch generatorFunction(Quantifier content) { return coqGenerator.generateQuantifier(content) }
	def dispatch generatorFunction(Multiplicity content) { return coqGenerator.generateMultiplicity(content) }
	def dispatch generatorFunction(ActionSuite content) { return coqGenerator.generatet_ActionSuite(content) }
	def dispatch generatorFunction(ArchBehaviorDecl content) { return coqGenerator.generatet_ArchBehaviorDecl(content) }
	def dispatch generatorFunction(ArchitectureDecl content) { return coqGenerator.generatet_ArchitectureDecl(content) }
	def dispatch generatorFunction(Assert content) { return coqGenerator.generatet_Assert(content) }
	def dispatch generatorFunction(AssertionDecl content) { return coqGenerator.generatet_AssertionDecl(content) }
	def dispatch generatorFunction(Behavior content) { return coqGenerator.generatet_Behavior(content) }
	def dispatch generatorFunction(BehaviorDecl content) { return coqGenerator.generatet_BehaviorDecl(content) }
	def dispatch generatorFunction(BehaviorStatement content) { return coqGenerator.generatet_BehaviorStatement(content) }
	def dispatch generatorFunction(Binding content) { return coqGenerator.generatet_Binding(content) }
	def dispatch generatorFunction(ComplexName content) { return coqGenerator.generatet_ComplexName(content) }
	def dispatch generatorFunction(Connection content) { return coqGenerator.generatet_Connection(content) }
	def dispatch generatorFunction(Constituent content) { return coqGenerator.generatet_Constituent(content) }
	def dispatch generatorFunction(ConstructedValue content) { return coqGenerator.generatet_ConstructedValue(content) }
	def dispatch generatorFunction(DataType content) { return coqGenerator.generatet_DataType(content) }
	def dispatch generatorFunction(DataTypeDecl content) { return coqGenerator.generatet_DataTypeDecl(content) }
	def dispatch generatorFunction(DutyDecl content) { return coqGenerator.generatet_DutyDecl(content) }
	def dispatch generatorFunction(ElementInConstituent content) { return coqGenerator.generatet_ElementInConstituent(content) }
	def dispatch generatorFunction(EntityBlock content) { return coqGenerator.generatet_EntityBlock(content) }
	def dispatch generatorFunction(Expression content) { return coqGenerator.generatet_Expression(content) }
	def dispatch generatorFunction(FieldDecl content) { return coqGenerator.generatet_FieldDecl(content) }
	def dispatch generatorFunction(FormalParameter content) { return coqGenerator.generatet_FormalParameter(content) }
	def dispatch generatorFunction(FunctionDecl content) { return coqGenerator.generatet_FunctionDecl(content) }
	def dispatch generatorFunction(GateDecl content) { return coqGenerator.generatet_GateDecl(content) }
	def dispatch generatorFunction(Import content) { return coqGenerator.generatet_Import(content) }
	def dispatch generatorFunction(MediatorDecl content) { return coqGenerator.generatet_MediatorDecl(content) }
	def dispatch generatorFunction(Protocol content) { return coqGenerator.generatet_Protocol(content) }
	def dispatch generatorFunction(ProtocolActionSuite content) { return coqGenerator.generatet_ProtocolActionSuite(content) }
	def dispatch generatorFunction(ProtocolDecl content) { return coqGenerator.generatet_ProtocolDecl(content) }
	def dispatch generatorFunction(ProtocolStatement content) { return coqGenerator.generatet_ProtocolStatement(content) }
	def dispatch generatorFunction(SosADL content) { return coqGenerator.generatet_SosADL(content) }
	def dispatch generatorFunction(SystemDecl content) { return coqGenerator.generatet_SystemDecl(content) }
	def dispatch generatorFunction(TupleElement content) { return coqGenerator.generatet_TupleElement(content) }
	def dispatch generatorFunction(Unit content) { return coqGenerator.generatet_Unit(content) }
	def dispatch generatorFunction(Valuing content) { return coqGenerator.generatet_Valuing(content) }
	def dispatch generatorFunction(ProofTerm content) { return generateProof(content) }
	def dispatch generatorFunction(Environment content) { return '''(«generateEnvironment(content)»)''' }
	def dispatch generatorFunction(EnvContent content) { return generateEnvContent(content) }
	
	def dispatch CharSequence generateEnvironment(CellEnvironmentImpl env) '''{| key := "«env.name»"; value := «env.info.generateEnvContent» |} :: «env.parent.generateEnvironment»'''
	def dispatch generateEnvironment(EnvironmentImpl env) '''[]'''
	def dispatch generateEnvironment(Environment env) { throw new UnsupportedOperationException }
	
	def dispatch generateEnvContent(SystemEnvContent c) '''(ESystem «coqGenerator.generatet_SystemDecl(c.systemDecl)»)'''
	def dispatch generateEnvContent(TypeEnvContent c) '''(EType «coqGenerator.generatet_DataTypeDecl(c.dataTypeDecl)» «coqGenerator._generateL(c.methods, [ f | coqGenerator.generatet_FunctionDecl(f)])»)'''
	def dispatch generateEnvContent(VariableEnvContent c) '''(EVariable «coqGenerator.generatet_DataType(c.type)»)'''
	
	static def ctorName(Class<?> clazz) {
		if(clazz.isAnnotationPresent(CoqConstructor)) {
			return clazz.getAnnotation(CoqConstructor).value
		} else {
			return clazz.simpleName.toFirstLower
		}
	}
	
	static def getGetterFor(Class<?> clazz, Field f) {
		var getterName = "get" + f.name.toFirstUpper
		return clazz.getMethod(getterName)
	}
	
	static def getByGetter(Object o, Class<?> clazz, Field f) {
		var getter = getGetterFor(clazz, f)
		return getter.invoke(o)
	}
}