/*
 * generated by Xtext
 */
package org.archware.sosadl.generator

import org.eclipse.emf.ecore.resource.Resource
import org.eclipse.xtext.generator.IGenerator
import org.eclipse.xtext.generator.IFileSystemAccess
import org.archware.sosadl.sosADL.*
import org.archware.sosadl.SosADLStandaloneSetupGenerated
import org.eclipse.emf.common.util.URI
import org.archware.sosadl.SosADLComparator
import org.eclipse.xtext.parser.IParser
import java.io.StringReader

/**
 * Generates code from your model files on save.
 * 
 * see http://www.eclipse.org/Xtext/documentation.html#TutorialCodeGeneration
 */
class SosADLPrettyPrinterGenerator implements IGenerator {

	override void doGenerate(Resource resource, IFileSystemAccess fsa) {

		for (e : resource.allContents.toIterable.filter(SosADL)) {
			val c = e.compile
		    System.out.println(c)
			check_roundtrip(resource.URI, e, c.toString())
		}
	}
	
	private def do_parse(CharSequence c) {
		val injector = new SosADLStandaloneSetupGenerated().createInjector
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
		val compare_e_p1 = SosADLComparator.compare(e, p1)
		val compare_e_p2 = SosADLComparator.compare(e, p2)
		val e1_equals_e2 = e1.equals(e2)
		if (compare_e_p1 && compare_e_p2 && e1_equals_e2) {
			System.out.println("Roundtrip test ok for " + uri.toString() + ": " + compare_e_p1 + " / " + compare_e_p2 + " / " + e1_equals_e2)
		} else {
			System.err.println("Warning! Roundtrip test KO for " + uri.toString() + ": " + compare_e_p1 + " / " + compare_e_p2 + " / " + e1_equals_e2)
		}
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
	with «i.importedLibrary»
	'''

	def compile(Library l)'''
    
    library «l.name» is {
      «l.decls.compile»
    }
	'''

	def compile(SoS s)'''
      sos «s.name» is {
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
      system «s.name» («s.parameters.map[compile].join(", ")») is {
        «FOR d : s.datatypes»
          «d.compile»
        «ENDFOR»
        «FOR g : s.gates»
          «g.compile»
        «ENDFOR»
      
        «s.behavior.compile»
      }«IF s.assertion != null» guarantee {
        «s.assertion.compile»
      }
      «ENDIF»
	'''

	def compile(ArchitectureDecl a)'''
      architecture «a.name» («a.parameters.map[compile].join(", ")») is {
        «FOR d : a.datatypes»
          «d.compile»
        «ENDFOR»
        «FOR g : a.gates»
          «g.compile»
        «ENDFOR»
        
        «a.behavior.compile»
      }«IF a.assertion != null» guarantee {
        «a.assertion.compile»
      }
      «ENDIF»
	'''

    def compile(MediatorDecl m)'''
      mediator «m.name» («m.parameters.map[compile].join(", ")») is {
        «FOR d : m.datatypes»
          «d.compile»
        «ENDFOR»
        «FOR d : m.duties»
          «d.compile»
        «ENDFOR»
        
        «m.behavior.compile»
      }«IF m.assumption != null» assume {
        «m.assumption.compile»
      }«ENDIF»«IF m.assertion != null» guarantee {
        «m.assertion.compile»
      }«ENDIF»
	'''
	
	def compile(GateDecl g)'''
      
      gate «g.name» is {
        «FOR c : g.connections»
        «c.compile»
        «ENDFOR»
      } guarantee {
        «g.protocol.compile»
      }
	'''
	
	def compile(DutyDecl d)'''
      
      duty «d.name» is {
        «FOR c : d.connections»
        «c.compile»
        «ENDFOR»
      } assume {
        «d.assertion.compile»
      } guarantee {
        «d.protocol.compile»
      }
      '''
	
	def compile(Connection c)'''«IF c.environment»environment «ENDIF»connection «c.name» is «c.mode»{«c.valueType.compile»}'''
	
	def compile(AssertionDecl a)'''
      property «a.name» is «a.body.compile»
    '''
    
    def compile(ProtocolDecl p)'''
      protocol «p.name» is «p.body.compile»
    '''
    
    def CharSequence compile(Protocol p)'''
    {
      «FOR s : p.statements»
      «s.compile»
      «ENDFOR»
    }
	'''
	
	def compile(ProtocolStatement p)'''
    «IF p instanceof ValuingProtocol»
      «(p as ValuingProtocol).valuing.compile»
    «ELSEIF p instanceof AssertProtocol»
      «(p as AssertProtocol).assertion.compile»
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
    «ELSEIF p instanceof DoExprProtocol»
      «(p as DoExprProtocol).compile»
    «ELSEIF p instanceof DoneProtocol»
      «(p as DoneProtocol).compile»
    «ENDIF»
	'''
	
	def compile(IfThenElseProtocol i)'''
    if «i.condition.compile» then «i.ifTrue.compile»«
    IF i.ifFalse != null»
    else «i.ifFalse.compile»
    «ENDIF»
    '''
	
	def compile(ChooseProtocol c)'''
    choose «c.branches.map[compile].join("or ")»
	'''
	
	def compile(ForEachProtocol f)'''
    foreach «f.variable» in «f.setOfValues.compile» «f.repeated.compile»
	'''
	
	def compile(DoExprProtocol d)'''
    do «d.expression.compile»
	'''
	
	def compile(DoExprBehavior d)'''
    do «d.expression.compile»
	'''
	
	def compile(RepeatProtocol r)'''
    repeat «r.repeated.compile»
	''' 
	
	def compile(DoneProtocol d)'''done'''
	
	def compile(DoneBehavior d)'''done'''
	    
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
    
    def compile(SendProtocolAction s)''' send «s.expression.compile»'''
    
    def compile(ReceiveAnyProtocolAction r)''' receive any'''
    
    def compile(ReceiveProtocolAction r)''' receive «r.variable»'''
    
    def compile(AnyAction a)'''anyaction'''
    
    def compile(BehaviorDecl b)'''
    behavior «b.name» is «b.body.compile»
    '''

	def CharSequence compile(Behavior b)'''
    {
      «FOR s : b.statements»
      «s.compile»
      «ENDFOR»
    } 
    '''
    
    def compile(BehaviorStatement b)'''
    «IF b instanceof ValuingBehavior»
      «(b as ValuingBehavior).valuing.compile»
    «ELSEIF b instanceof AssertBehavior»
      «(b as AssertBehavior).assertion.compile»
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
    «ELSEIF b instanceof DoExprBehavior»
      «(b as DoExprBehavior).compile»
    «ELSEIF b instanceof DoneBehavior»
      «(b as DoneBehavior).compile»
    «ELSEIF b instanceof RecursiveCall»
      «(b as RecursiveCall).compile»
    «ENDIF»
    '''

	def compile(RepeatBehavior f)'''
    repeat «f.repeated.compile»
    '''
	
	def compile(IfThenElseBehavior i)'''
    if «i.condition.compile» then «i.ifTrue.compile»«
    IF i.ifFalse != null»
    else «i.ifFalse.compile»
    «ENDIF»
	'''
	
	def compile(ChooseBehavior c)'''
    choose «c.branches.map[compile].join("or ")»
	'''
	
	def compile(ForEachBehavior f)'''
    foreach «f.variable» in «f.setOfValues.compile» «f.repeated.compile»
	'''
	
	def compile(RecursiveCall r)'''
    behavior («r.parameters.map[compile].join(", ")»)
	'''
	
    def compile(Assert a)'''
    «IF a instanceof TellAssertion»
       «(a as TellAssertion).compile»
    «ELSEIF a instanceof UntellAssertion»
       «(a as UntellAssertion).compile»
    «ELSEIF a instanceof AskAssertion»
       «(a as AskAssertion).compile»
    «ENDIF»
    '''
    
    def compile(TellAssertion a)'''
    tell «a.name» is {«a.expression.compile»}
    '''
    
    def compile(UntellAssertion a)'''
    untell «a.name»
    '''
    
    def compile(AskAssertion a)'''
    ask «a.name» is {«a.expression.compile»}
    '''

	def compile(Action a)'''
    via «a.complexName.compile»«
    IF a.suite instanceof SendAction»«(a.suite as SendAction).compile»«
    ELSEIF a.suite instanceof ReceiveAction»«(a.suite as ReceiveAction).compile»«
    ENDIF»'''
	
	def compile(SendAction s)''' send «s.expression.compile»'''
    
    def compile(ReceiveAction r)''' receive «r.variable»'''
        
	def compile(ArchBehaviorDecl a)'''
    behavior «a.name» is compose {
      «FOR c:a.constituents»
        «c.compile»
      «ENDFOR»
    } binding {
      «a.bindings.compile»
    }
	'''
	
	def compile(Constituent c)'''«c.name» is «c.value.compile»'''

    
    def compile(Relay r)'''
    relay «r.connLeft.compile» to «r.connRight.compile»
    '''

	def compile(Unify u)'''
    unify «u.multLeft»{«u.connLeft.compile»} to «u.multRight»{«u.connRight.compile»}
	'''

	def compile(Quantify q)'''
    «q.quantifier» {
      «q.elements.map[compile].join(", ")»
      suchthat
      «q.bindings.compile»
    }
	'''
	
	def compile(ElementInConstituent e)'''«e.variable» in «e.constituent»'''
	
	def compile(DataTypeDecl d)'''
    datatype «d.name»«IF d.datatype != null» is «d.datatype.compile»«ENDIF»«IF !d.functions.empty» { 
      «FOR f : d.functions»
      «f.compile»
      «ENDFOR»
    }
    «ENDIF»
	'''
	
	def CharSequence compile(DataType d)'''«
	IF d instanceof IntegerType»«
	  (d as IntegerType).compile»«
    ELSEIF d instanceof TupleType»«
      (d as TupleType).compile»«
    ELSEIF d instanceof SequenceType»«
      (d as SequenceType).compile»«
    ELSEIF d instanceof RangeType»integer{«(d as RangeType).vmin.compile»..«(d as RangeType).vmax.compile»}«
    ELSEIF d instanceof ConnectionType»«
      (d as ConnectionType).mode.compile»{«(d as ConnectionType).type.compile»}«
    ELSEIF d instanceof NamedType»«
      (d as NamedType).compile»«
    ENDIF»'''
	
	def compile(FunctionDecl f)'''
      function («f.data.compile»)::«f.name»(«f.parameters.map[compile].join(", ")»):«f.type.compile» is {
        «FOR v:f.valuing»
        «v.compile»
        «ENDFOR»
        return «f.expression.compile»
      }
	'''

	def compile(FormalParameter p)'''«p.name»:«p.type.compile»'''

	//def compile(BaseType t)'''integer'''
	def compile(IntegerType t)'''integer'''

/*
	def compile(ConstructedType t)'''«
	  IF t instanceof TupleType»«
        (t as TupleType).compile»«
      ELSEIF t instanceof SequenceType»«
        (t as SequenceType).compile»«
      ELSEIF t instanceof RangeType»integer{«(t as RangeType).vmin.compile»..«(t as RangeType).vmax.compile»}«
      ELSEIF t instanceof ConnectionType»«
        (t as ConnectionType).mode.compile»{«(t as ConnectionType).type.compile»}«
      ENDIF»'''
      */
	
	def compile(TupleType t)'''tuple{«t.fields.map[compile].join(", ")»}'''
	
	def compile(FieldDecl f)'''«f.name»:«f.type.compile»'''
	
	def compile(SequenceType s)'''sequence{«s.type.compile»}'''
	
	def compile(ModeType m)'''«m.literal»'''
	
	def compile(NamedType t)'''«t.name»'''

    def compile(ComplexName c)'''«IF c.name != null»«c.name.join("::")»«ENDIF»'''
    
	def compile(Valuing v)'''
      value «v.name»«IF v.type != null» : «v.type.compile»«ENDIF» = «v.expression.compile»
	'''
	
	def compile(IntegerValue i)'''«i.absInt»'''
	
	def compile(Any a)'''any'''
	
	
	def compile(Tuple t)'''tuple{«t.elements.map[compile].join(", ")»}'''
	
	def compile(TupleElement t)'''«t.label»=«t.value.compile»'''
	
	def compile(Sequence s)'''sequence{«s.elements.map[compile].join(", ")»}'''

    def CharSequence compile(Expression e)'''«
	//IF e instanceof BinaryExpression»(«(e as BinaryExpression).left.compile») «(e as BinaryExpression).op» («(e as BinaryExpression).right.compile»)«
	IF e instanceof BinaryExpression»(«(e as BinaryExpression).compile»)«
    ELSEIF e instanceof UnaryExpression»«(e as UnaryExpression).compile»«
	ELSEIF e instanceof CallExpression»«(e as CallExpression).compile»«
	ELSEIF e instanceof IdentExpression»«(e as IdentExpression).compile»«
	//ELSEIF e instanceof UnobservableValue»«(e as UnobservableValue).compile»«
	ELSEIF e instanceof Any»«(e as Any).compile»«
    ELSEIF e instanceof Tuple»«(e as Tuple).compile»«
    ELSEIF e instanceof Sequence»«(e as Sequence).compile»«
    ELSEIF e instanceof IntegerValue»«(e as IntegerValue).compile»«
    ELSEIF e instanceof Field»«(e as Field).compile»«
    ELSEIF e instanceof Select»«(e as Select).compile»«
    ELSEIF e instanceof Map»«(e as Map).compile»«
    ELSEIF e instanceof MethodCall»«(e as MethodCall).compile»«
    ELSEIF e instanceof Relay»«
      (e as Relay).compile»«
    ELSEIF e instanceof Unify»«
      (e as Unify).compile»«
    ELSEIF e instanceof Quantify»«
      (e as Quantify).compile»«
    ELSEIF e instanceof Tuple»«
      (e as Tuple).compile»«
    ELSEIF e instanceof Sequence»«
      (e as Sequence).compile»«
    ENDIF»'''
	
	def compile(BinaryExpression e)'''(«e.left.compile») «e.op» («e.right.compile»)'''
	
	def compile(UnaryExpression e)''' «e.op» («e.right.compile»)'''
	
	def compile(IdentExpression e)'''«e.ident»'''
	
	def compile(Field e)'''«e.object.compile»::«e.field»'''
	
	def compile(CallExpression e)'''«
	e.function»(«e.parameters.map[compile].join(", ")»)'''
	
	def compile(Select e)'''«
	e.object.compile»::select{«e.variable» suchthat «e.condition.compile»}'''

	def compile(Map e)'''«
	e.object.compile»::collect{«e.variable» suchthat «e.expression.compile»}'''

	def compile(MethodCall e)'''«
	e.object.compile»::«e.method»(«e.parameters.map[compile].join(", ")»)'''
	
	//def compile(UnobservableValue u)'''unobservable'''
	
    /* Assertion rules are not used anymore
    def compile(Assertion a)'''«
	IF a instanceof BinaryAssertion»(«(a as BinaryAssertion).left.compile») «(a as BinaryAssertion).op» («(a as BinaryAssertion).right.compile»)«
	ELSEIF a instanceof UnaryAssertion» «(a as UnaryAssertion).op» («(a as UnaryAssertion).right.compile»)«
	ELSEIF a instanceof Expression»«(a as Expression).compile»«
	ELSEIF a instanceof Always»«(a as Always).compile»«
	ELSEIF a instanceof Anynext»«(a as Anynext).compile»«
	ELSEIF a instanceof Action»«(a as Action).compile»«
	ENDIF»'''
	
    def compile(UnaryAssertion u)'''«u.op»«u.right.compile»'''
    
    def compile(Always a)'''always {«a.expression.compile»}'''
    
    def compile(Anynext a)'''anynext {«a.expression.compile»}'''
    */
}