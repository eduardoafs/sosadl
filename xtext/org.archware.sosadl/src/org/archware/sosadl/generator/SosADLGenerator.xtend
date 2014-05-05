/*
 * generated by Xtext
 */
package org.archware.sosadl.generator

import org.eclipse.emf.ecore.resource.Resource
import org.eclipse.xtext.generator.IGenerator
import org.eclipse.xtext.generator.IFileSystemAccess
import org.archware.sosadl.sosADL.*
import org.eclipse.xtext.naming.IQualifiedNameProvider
import com.google.inject.Inject
import org.archware.sosadl.SosADLStandaloneSetup
import org.eclipse.xtext.resource.XtextResourceSet
import org.eclipse.emf.common.util.URI
import org.eclipse.xtext.util.StringInputStream
import org.archware.sosadl.SosADLComparator
import org.eclipse.xtext.parser.IParser
import java.io.StringReader

/**
 * Generates code from your model files on save.
 * 
 * see http://www.eclipse.org/Xtext/documentation.html#TutorialCodeGeneration
 */
class SosADLGenerator implements IGenerator {

	@Inject extension IQualifiedNameProvider

	override void doGenerate(Resource resource, IFileSystemAccess fsa) {

		//		fsa.generateFile('greetings.txt', 'People to greet: ' + 
		//			resource.allContents
		//				.filter(typeof(Greeting))
		//				.map[name]
		//				.join(', '))
		for (e : resource.allContents.toIterable.filter(SosADL)) {
			//System.out.println("e ='"+e+"'")
			//System.out.println("e fullname='"+e.fullyQualifiedName+"'")
			val c = e.compile
			// System.out.println(c)
			check_roundtrip(resource.URI, e, c.toString())
		}
	}
	
	private def do_parse(CharSequence c) {
		val injector = new SosADLStandaloneSetup().createInjectorAndDoEMFRegistration
		val parser = injector.getInstance(IParser)
		val result = parser.parse(new StringReader(c.toString()))
		if(result.hasSyntaxErrors) {
			result.getSyntaxErrors.forEach[e | System.out.println(e.toString())]
		} else {
			result.getRootASTElement as SosADL
		}
	}
	
	private def check_roundtrip(URI uri, SosADL e, String c) {
		val p1 = do_parse(c)
		val e1 = p1.compile.toString()
		val p2 = do_parse(e1)
		val e2 = p2.compile.toString()
		System.out.println("roundtrip test for " + uri.toString() + ": " + SosADLComparator.compare(e, p1) + " / " + SosADLComparator.compare(e, p2) + " / " + e1.equals(e2))		
	}

/* switch equivalent aux IF en cascade (sauf les espaces):
    	«switch s.content {
			NewNamedLibrary:(s.content as NewNamedLibrary).compile
			NewSoS:(s.content as NewSoS).compile
		}»
 */
	def compile(SosADL s)'''
    «FOR i : s.imports»
      «i.compile»
    «ENDFOR»

    «IF s.content instanceof Library»
      «(s.content as Library).compile»
    «ELSEIF s.content instanceof SoS»
      «(s.content as SoS).compile »
    «ENDIF»
	'''

	def compile(Import i)'''
	with «i.importName»
	'''

	def compile(Library l)'''
    
    library «l.libraryName» is {
      «l.decls.compile»
    }
	'''

	def compile(SoS s)'''
      sos «s.sosName» is {
        «s.decls.compile»
      }
	'''

	def compile(EntityBlock e)'''
    «FOR d : e.datatypes»
      «d.compile»
    «ENDFOR»
    «FOR f : e.functions»
      «f.compile»
    «ENDFOR»
    
    «FOR s : e.systems»
      «s.compile»
    «ENDFOR»
    «FOR m : e.mediators»
      «m.compile»
    «ENDFOR»
    «FOR a : e.architectures»
      «a.compile»
    «ENDFOR»
	'''

	def compile(SystemDecl s)'''
      system «s.systemName» («s.params.map[compile].join(", ")») is {
        «FOR d : s.datatypes»
          «d.compile»
        «ENDFOR»
        «FOR g : s.gates»
          «g.compile»
        «ENDFOR»
      
        «s.behavior.compile»
      }«IF s.assertionDecl != null» guarantee {
        «s.assertionDecl.compile»
      }
      «ENDIF»
	'''

	def compile(ArchitectureDecl a)'''
      architecture «a.architectureName» («a.params.map[compile].join(", ")») is {
        «FOR d : a.datatypes»
          «d.compile»
        «ENDFOR»
        «FOR g : a.gates»
          «g.compile»
        «ENDFOR»
        
        «a.archBehavior.compile»
      }«IF a.assertionDecl != null» guarantee {
        «a.assertionDecl.compile»
      }
      «ENDIF»
	'''

    def compile(MediatorDecl m)'''
      mediator «m.mediatorName» («m.params.map[compile].join(", ")») is {
        «FOR d : m.datatypes»
          «d.compile»
        «ENDFOR»
        «FOR d : m.duties»
          «d.compile»
        «ENDFOR»
        
        «m.behavior.compile»
      }
	'''
	
	def compile(GateDecl g)'''
      
      gate «g.gateName» is {
        «FOR c : g.connections»
        «c.compile»
        «ENDFOR»
      } guarantee {
        «g.protocolDecl.compile»
      }
	'''
	
	def compile(DutyDecl d)'''
      
      duty «d.dutyName» is {
        «FOR c : d.connections»
        «c.compile»
        «ENDFOR»
      } require {
        «d.assertion.compile»
      } assume {
        «d.assumedProtocol.compile»
      }
      '''
	
	def compile(Connection c)'''«IF c.envConnection»environment «ENDIF»connection «c.name» is «c.mode»{«c.valueType.compile»}'''
	
	def compile(AssertionDecl a)'''
      property «a.assertionName» is {
        «IF ! a.valuing.isEmpty»
        «FOR v:a.valuing»
        «v.compile»
        «ENDFOR»
        within
        «ENDIF»
        «a.assertionExpr.compile»
      }
    '''
    
    def compile(ProtocolDecl p)'''
      protocol «p.protocolName» is «p.protocolBody.compile»
    '''
    
    def CharSequence compile(Protocol p)'''
    {
      «FOR s : p.statements»
      «s.compile»
      «ENDFOR»
    }
	'''
	
	def compile(ProtocolStatement p)'''
    «IF p instanceof Valuing»
      «(p as Valuing).compile»
    «ELSEIF p instanceof Assert»
      «(p as Assert).compile»
    «ELSEIF p instanceof ProtocolAction»
      «(p as ProtocolAction).compile»
    «ELSEIF p instanceof AnyAction»
      «(p as AnyAction).compile»
    «ELSEIF p instanceof RepeatProtocol»
      «(p as RepeatProtocol).compile»
    «ELSEIF p instanceof IfThenElseProtocol»
      «(p as IfThenElseProtocol).compile»
    «ELSEIF p instanceof ChooseProtocol»
      «(p as ChooseProtocol).compile»
    «ELSEIF p instanceof ForEachProtocol»
      «(p as ForEachProtocol).compile»
    «ELSEIF p instanceof DoExpr»
      «(p as DoExpr).compile»
    «ELSEIF p instanceof Done»
      «(p as Done).compile»
    «ENDIF»
	'''
	
	def compile(IfThenElseProtocol i)'''
    if «i.cond.compile» then {
      «i.ifTrueProtocol.compile»
    }«IF i.ifFalseProtocol != null» else {
      «i.ifFalseProtocol.compile»
    }
    «ENDIF»
	'''
	
	def compile(ChooseProtocol c)'''
    choose «c.choiceProtocol.map[compile].join("or ")»
	'''
	
	def compile(ForEachProtocol f)'''
    foreach «f.name» in «f.setOfValues.compile» «f.foreachProtocol.compile»
	'''
	
	def compile(DoExpr d)'''
    do «d.expr.compile»
	'''
	
	def compile(RepeatProtocol r)'''
    repeat «r.repeatedProtocol.compile»
	''' 
	
	def compile(Done d)'''done'''
	    
    def compile(ProtocolAction p)'''
    via «p.complexName.compile»«
    IF p.suite instanceof SendProtocolAction»«
      (p.suite as SendProtocolAction).compile»«
    ELSEIF p.suite instanceof ReceiveAnyProtocolAction»«
      (p.suite as ReceiveAnyProtocolAction).compile»«
    ELSEIF p.suite instanceof ReceiveProtocolAction»«
      (p.suite as ReceiveProtocolAction).compile»«
    ENDIF»
    '''
    
    def compile(SendProtocolAction s)''' send «s.sendExpression.compile»'''
    
    def compile(ReceiveAnyProtocolAction r)''' receive any'''
    
    def compile(ReceiveProtocolAction r)''' receive «r.receivedValue.compile»'''
    
    def compile(AnyAction a)'''anyaction'''
    
    def compile(BehaviorDecl b)'''
    behavior «b.behaviorName» («b.paramExpr.map[compile].join(", ")») is «b.behaviorBody.compile»
    '''

	def CharSequence compile(Behavior b)'''
    {
      «FOR s : b.statements»
      «s.compile»
      «ENDFOR»
    } 
    '''
    
    def compile(BehaviorStatement b)'''
    «IF b instanceof Valuing»
      «(b as Valuing).compile»
    «ELSEIF b instanceof Assert»
      «(b as Assert).compile»
    «ELSEIF b instanceof Action»
      «(b as Action).compile»
    «ELSEIF b instanceof RepeatBehavior»
      «(b as RepeatBehavior).compile»
    «ELSEIF b instanceof IfThenElseBehavior»
      «(b as IfThenElseBehavior).compile»
    «ELSEIF b instanceof ChooseBehavior»
      «(b as ChooseBehavior).compile»
    «ELSEIF b instanceof ForEachBehavior»
      «(b as ForEachBehavior).compile»
    «ELSEIF b instanceof DoExpr»
      «(b as DoExpr).compile»
    «ELSEIF b instanceof Done»
      «(b as Done).compile»
    «ELSEIF b instanceof RecursiveCall»
      «(b as RecursiveCall).compile»
    «ENDIF»
    '''

	def compile(RepeatBehavior f)'''
    repeat «f.repeatedBehavior.compile»
    '''
	
	def compile(IfThenElseBehavior i)'''
    if «i.cond.compile» then «i.ifTrueBehavior.compile»«
    IF i.ifFalseBehavior != null»
    else «i.ifFalseBehavior.compile»
    «ENDIF»
	'''
	
	def compile(ChooseBehavior c)'''
    choose «c.choiceBehavior.map[compile].join("or ")»
	'''
	
	def compile(ForEachBehavior f)'''
    foreach «f.name» in «f.setOfValues.compile» «f.foreachBehavior.compile»
	'''
	
	def compile(RecursiveCall r)'''
    behavior («r.paramExpr.map[compile].join(", ")»)
	'''
	
    def compile(Assert a)'''
    «IF a instanceof TellAssertion»
       «(a as TellAssertion).compile»
    «ELSEIF a instanceof AskAssertion»
       «(a as AskAssertion).compile»
    «ENDIF»
    '''
    
    def compile(TellAssertion a)'''
    assert «a.assertName» is {«a.assertExpression.compile»}
    '''
    
    def compile(AskAssertion a)'''
    ask «a.assertName» is {«a.assertExpression.compile»}
    '''

	def compile(AssertExpression a)'''«
	IF a instanceof Valuing»«
	  (a as Valuing).compile»«
	ELSEIF a instanceof BooleanExpression»«
	  (a as BooleanExpression).compile»«
	ENDIF»'''

	def compile(Action a)'''
    via «a.complexName.compile»«
    IF a.suite instanceof SendAction»«(a.suite as SendAction).compile»«
    ELSEIF a.suite instanceof ReceiveAction»«(a.suite as ReceiveAction).compile»«
    ENDIF»'''
	
	def compile(SendAction s)''' send «s.sendExpression.compile»'''
    
    def compile(ReceiveAction r)''' receive «r.receivedValue.compile»'''
        
	def compile(ArchBehaviorDecl a)'''
    behavior «a.behaviorName» («a.paramExpr.map[compile].join(", ")») is compose {
      «a.constituentList.compile»
    } binding {
      «a.bindings.compile»
    }
	''' 
	
	def compile(ConstituentList l)'''
    «FOR c:l.constituent»
      «c.compile»
    «ENDFOR»
	'''
	def compile(Constituent c)'''«c.constituentName» is «c.constituentValue.compile»'''

    def compile(Binding b)'''«
    IF b instanceof Relay»«
      (b as Relay).compile»«
    ELSEIF b instanceof Unify»«
      (b as Unify).compile»«
    ELSEIF b instanceof Quantify»«
      (b as Quantify).compile»«
    ENDIF»
    '''
    
    def compile(Relay r)'''
    relay «r.gate.compile» to «r.connection.compile»
    '''

	def compile(Unify u)'''
    unify «u.multLeft»{«u.connLeft.compile»} to «u.multRight»{«u.connRight.compile»}
	'''

	def compile(Quantify q)'''
    «q.quantifier» {
      «q.elementInConstituent.map[compile].join(", ")»
      suchthat
      «q.bindings.compile»
    }
	'''
	
	def compile(ElementInConstituent e)'''«e.element» in «e.constituent»'''
	
	def compile(DataTypeDecl d)'''
    datatype «d.datatypeName»«IF d.datatype != null» is «d.datatype.compile»«ENDIF»«IF !d.function.empty» { 
      «FOR f : d.function»
      «f.compile»
      «ENDFOR»
    }
    «ENDIF»
	'''
	
	def CharSequence compile(DataType d)'''«
	IF d instanceof BaseType»«
      (d as BaseType).compile»«
    ELSEIF d instanceof ConstructedType»«
      (d as ConstructedType).compile»«
    ELSEIF d instanceof TypeName»«
      (d as TypeName).compile»«
    ENDIF»'''
	
	def compile(FunctionDecl f)'''
      function («f.dataName»:«f.dataTypeName»)::«f.functionName»(«f.params.map[compile].join(", ")»):«f.returnType.compile» is {
        «FOR v:f.valuing»
        «v.compile»
        «ENDFOR»
        return «f.returnExpression.compile»
      }
	'''

	def compile(ParamType p)'''«p.name»:«p.type.compile»'''

	def compile(BaseType t)'''integer'''

	def compile(ConstructedType t)'''«
	  IF t instanceof TupleType»«
        (t as TupleType).compile»«
      ELSEIF t instanceof SequenceType»«
        (t as SequenceType).compile»«
      ELSEIF t instanceof RangeType»integer{«(t as RangeType).vmin.compile»..«(t as RangeType).vmax.compile»}«
      ELSEIF t instanceof ConnectionType»«
        (t as ConnectionType).mode.compile»{«(t as ConnectionType).typeOfConnection»}«
      ENDIF»'''
	
	def compile(TupleType t)'''tuple{«t.field.map[compile].join(", ")»}'''
	
	def compile(SequenceType s)'''sequence{«s.typeOfSequence.compile»}'''
	
	def compile(LabelledType l)'''«l.label.toString»:«l.type.compile»'''

	def compile(ModeType m)'''«m.literal»'''
	
	def compile(TypeName t)'''«t.typeName»'''

    def compile(ComplexName c)'''«IF c.complexName != null»«c.complexName.join("::")»«ENDIF»'''
    
	def compile(Valuing v)'''
      value «v.valueName»«IF v.valueType != null» is «v.valueType.compile»«ENDIF» = «v.expression.compile»
	'''
	
	def compile(IntegerValue i)'''«i.absInt»'''
	
	def compile(Any a)'''any'''
	
	def compile(ConstructedValue c)'''«
      IF c instanceof Tuple»«
        (c as Tuple).compile»«
      ELSEIF c instanceof Sequence»«
        (c as Sequence).compile»«
      ENDIF»'''
	
	def compile(Tuple t)'''tuple{«t.tupleElement.map[compile].join(", ")»}'''
	
	def compile(TupleElement t)'''«t.elementLabel»=«t.elementValue.compile»'''
	
	def compile(Sequence s)'''sequence{«s.paramExpr.map[compile].join(", ")»}'''

    def compile(BindingExpression b)'''«(b as Expression).compile»'''

    def compile(BooleanExpression b)'''«(b as Expression).compile»'''
    
    /*
     * La compilation de la règle initiale Expression était illisible : la faute à la grammaire abstraite !
     * En effet, presque toutes les règles de la grammaire concrète pour Expression
     * se traduisaient dans l'unique classe Expression...
     * Remède :
     * - CallExpression ne retourne plus Expression
     * - CallFunction est supprimé dans CallExpression
     * - la suite d'expressions derrière les :: est reportée dans une règle CallExpressionSuite
     */
    def CharSequence compile(Expression e)'''«
	IF e instanceof BinaryExpression»(«(e as BinaryExpression).left.compile») «(e as BinaryExpression).op» («(e as BinaryExpression).right.compile»)«
	ELSEIF e instanceof UnaryExpression» «(e as UnaryExpression).op» («(e as UnaryExpression).right.compile»)«
	ELSEIF e instanceof Binding»«(e as Binding).compile»«
	ELSEIF e instanceof CallExpression»«(e as CallExpression).compile»«
	ELSEIF e instanceof IdentExpression»«(e as IdentExpression).ident.name»«
	ELSEIF e instanceof UnobservableValue»unobservable«
	ELSEIF e instanceof Any»any«
    ELSEIF e instanceof Tuple»«(e as Tuple).compile»«
    ELSEIF e instanceof Sequence»«(e as Sequence).compile»«
    ELSEIF e instanceof IntegerValue»«(e as IntegerValue).compile»«
    ELSEIF e instanceof CallExpression»«(e as CallExpression).compile»«
    ELSEIF e instanceof Field»«(e as Field).object.compile»::«(e as Field).fieldName»«
    ELSEIF e instanceof Select»«(e as Select).compile»«
    ELSEIF e instanceof Map»«(e as Map).compile»«
    ELSEIF e instanceof MethodCall»«(e as MethodCall).compile»«
	ENDIF»'''
	
	def compile(CallExpression e)'''«
	e.functionName.name»(«e.params.map[compile].join(", ")»)'''
	
	def compile(Select e)'''«
	e.object.compile»::select{«e.selectName» suchthat «e.selectExpr.compile»}'''

	def compile(Map e)'''«
	e.object.compile»::map{«e.mapName» to «e.mapExpr.compile»}'''

	def compile(MethodCall e)'''«
	e.object.compile»::«e.methodName»(«e.params.map[compile].join(", ")»)'''
	
    def compile(UnaryExpression u)'''«u.op» «u.right.compile»'''
    
    def compile(Ident i)'''«i.name»'''
    
    def CharSequence compile(Assertion a)'''«
	IF a instanceof BinaryAssertion»(«(a as BinaryAssertion).left.compile») «(a as BinaryAssertion).op» («(a as BinaryAssertion).right.compile»)«
	ELSEIF a instanceof UnaryAssertion» «(a as UnaryAssertion).op» («(a as UnaryAssertion).right.compile»)«
	ELSEIF a instanceof Expression»«(a as Expression).compile»«
	ELSEIF a instanceof Always»«(a as Always).compile»«
	ELSEIF a instanceof Anynext»«(a as Anynext).compile»«
	ELSEIF a instanceof Action»«(a as Action).compile»«
	ENDIF»'''
	
    def compile(UnaryAssertion u)'''«u.op»«u.right.compile»'''
    
    def compile(Always a)'''always {«a.expr.compile»}'''
    
    def compile(Anynext a)'''anynext {«a.expr.compile»}'''
}