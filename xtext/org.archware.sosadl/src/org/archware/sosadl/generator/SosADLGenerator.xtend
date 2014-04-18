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
			System.out.println(e.compile)
		}
	}

/* switch equivalent a:
  		«IF s.content instanceof NewNamedLibrary»
			«(s.content as NewNamedLibrary).compile»
		«ELSEIF s.content instanceof NewSoS»
			« (s.content as NewSoS).compile »
		«ENDIF»
 */
	def compile(SosADL s) '''
		«FOR i : s.imports»
			«i.compile»
		«ENDFOR»
		«switch s.content {
			NewNamedLibrary:(s.content as NewNamedLibrary).compile
			NewSoS:(s.content as NewSoS).compile
		}»
	'''

	def compile(Import i) '''
		with «i.importName»
	'''

	def compile(NewNamedLibrary l) '''
		library «l.libraryName» is {
			«l.decls.compile»
		}
	'''

	def compile(NewSoS s) '''
		sos «s.sosName» is {
  			«s.decls.compile»
		}
	'''

	def compile(EntityBlock e) '''
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

	def compile(SystemDecl s) '''
		system «s.systemName» («s.params.map[compile].join(", ")») is {
		«FOR d : s.datatypes»
			«d.compile»
		«ENDFOR»
		
		«FOR g : s.gates»
			«g.compile»
		«ENDFOR»
		
		«s.behavior.compile»
		}
		«IF s.assertionDecl != null»
			guarantee { «s.assertionDecl.compile» }
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
		}
	'''

    def compile(MediatorDecl m) '''
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
		} guarantee { «g.protocolDecl.compile»
		}
	'''
	
	def compile(DutyDecl d)'''
		duty «d.dutyName» is {
		«FOR c : d.connections»
			«c.compile»
		«ENDFOR»
		}
		require { «d.assertion.compile» }
		assume { «d.assumedProtocol.compile» }
		'''
	
	def compile(Connection c)'''
		«IF c.envConnection»environment «ENDIF»connection «c.name» is «c.mode»{«c.valueType.compile»}
	'''
	
	def compile(AssertionDecl a)'''
	assertion «a.assertionName» is {
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
    
    def compile(Protocol p)'''«
    IF p instanceof PrefixedProtocol»
	{ «(p as PrefixedProtocol).compile» }
	«ELSEIF p instanceof FinalProtocol»«(p as FinalProtocol).compile»«
	ENDIF»
	'''
	
	def compile(PrefixedProtocol p)'''
	«FOR s : p.statements»
		«s.compile»
	«ENDFOR»
	«IF p.finalProtocol != null»
		«IF p.finalProtocol instanceof IfThenElseProtocol»
		«(p.finalProtocol as IfThenElseProtocol).compile»
    	«ELSEIF p.finalProtocol instanceof ChooseProtocol»
		«(p.finalProtocol as ChooseProtocol).compile»
    	«ELSEIF p.finalProtocol instanceof ForEachProtocol»
		«(p.finalProtocol as ForEachProtocol).compile»
    	«ELSEIF p.finalProtocol instanceof DoExpr»
		«(p.finalProtocol as DoExpr).compile»
    	«ELSEIF p.finalProtocol instanceof RepeatForeverProtocol»
		«(p.finalProtocol as RepeatForeverProtocol).compile»
    	«ELSEIF p.finalProtocol instanceof Done»
		«(p.finalProtocol as Done).compile»
		«ENDIF»
	«ENDIF»
	'''
		
	def compile(FinalProtocol p)'''
		«IF p instanceof IfThenElseProtocol»
		«(p as IfThenElseProtocol).compile»
    	«ELSEIF p instanceof ChooseProtocol»
		«(p as ChooseProtocol).compile»
    	«ELSEIF p instanceof ForEachProtocol»
		«(p as ForEachProtocol).compile»
    	«ELSEIF p instanceof DoExpr»
		«(p as DoExpr).compile»
    	«ELSEIF p instanceof RepeatForeverProtocol»
		«(p as RepeatForeverProtocol).compile»
    	«ELSEIF p instanceof Done»
		«(p as Done).compile»
		«ENDIF»
	'''
	
	def compile(IfThenElseProtocol i) '''
	if «i.cond.compile» then {
		«i.ifTrueProtocol.compile»
	}
	«IF i.ifFalseProtocol != null»else { «i.ifFalseProtocol.compile»}«ENDIF»
	'''
	
	def compile(ChooseProtocol c) '''
	choose «c.choiceProtocol.map[compile].join("} or {")»
	'''
	
	def compile(ForEachProtocol f)'''
	foreach «f.name» in «f.setOfValues.compile» «f.foreachProtocol.compile»
	'''
	
	def compile(DoExpr d)'''
	do «d.expr.compile»
	'''
	
	def compile(RepeatForeverProtocol r) '''
	forever «r.repeatedProtocol.compile»
	''' 
	
	def compile(Done d) '''done'''
    
    def compile(ProtocolStatement p)'''
    «IF p instanceof Valuing»
		«(p as Valuing).compile»
	«ELSEIF p instanceof Assert»
		«(p as Assert).compile»
	«ELSEIF p instanceof ProtocolAction»
		«(p as ProtocolAction).compile»
	«ELSEIF p instanceof AnyAction»
    	«(p as AnyAction).compile»
	«ELSEIF p instanceof Repeat»
		«(p as Repeat).compile»
    «ENDIF»
	'''
    
    def compile(ProtocolAction p)'''
    via «p.complexName.compile»«IF p.suite instanceof SendProtocolAction»
		«(p.suite as SendProtocolAction).compile»
	«ELSEIF p.suite instanceof ReceiveAnyProtocolAction»
		«(p.suite as ReceiveAnyProtocolAction).compile»
	«ELSEIF p.suite instanceof ReceiveProtocolAction»
		«(p.suite as ReceiveProtocolAction).compile»
	«ENDIF»
    '''
    
    def compile(SendProtocolAction s)'''send «s.sendExpression.compile»'''
    
    def compile(ReceiveAnyProtocolAction r)'''any'''
    
    def compile(ReceiveProtocolAction r)'''receive «r.receivedValue.compile»'''
    
    def compile(AnyAction a)'''anyaction'''
    
    def compile(Repeat r)'''
    repeat {
    «FOR s:r.repeatedProtocol»
    	«s.compile»
    «ENDFOR»
    }
    '''
    
    def compile(BehaviorDecl b)'''
	behavior «b.behaviorName» («b.paramExpr.map[compile].join(", ")») is
	«b.behaviorBody.compile»
    '''

	def compile(Behavior b)'''
	«IF b instanceof PrefixedBehavior»
	{ «(b as PrefixedBehavior).compile» }
	«ELSEIF b instanceof FinalBehavior»
    «(b as FinalBehavior).compile»
	«ENDIF» 
    '''
    
	def compile(PrefixedBehavior p)'''
	«FOR s:p.statements»
	  «s.compile»
	«ENDFOR»
	«IF p.finalBehavior != null»
	  	«IF (p.finalBehavior) instanceof ForeverBehavior»
			«((p.finalBehavior) as ForeverBehavior).compile»
    	«ELSEIF (p.finalBehavior) instanceof IfThenElseBehavior»
			«((p.finalBehavior) as IfThenElseBehavior).compile»
    	«ELSEIF (p.finalBehavior) instanceof ChooseBehavior»
			«((p.finalBehavior) as ChooseBehavior).compile»
    	«ELSEIF (p.finalBehavior) instanceof ForEachBehavior»
			«((p.finalBehavior) as ForEachBehavior).compile»
    	«ELSEIF (p.finalBehavior) instanceof DoExpr»
			«((p.finalBehavior) as DoExpr).compile»
    	«ELSEIF (p.finalBehavior) instanceof Done»
			«((p.finalBehavior) as Done).compile»
		«ELSEIF (p.finalBehavior) instanceof RecursiveCall»
			«((p.finalBehavior) as RecursiveCall).compile»
    	«ENDIF»
    «ENDIF»
	'''
	
	def compile(FinalBehavior f)'''
	«IF f instanceof ForeverBehavior»
		«(f as ForeverBehavior).compile»
    «ELSEIF f instanceof IfThenElseBehavior»
		«(f as IfThenElseBehavior).compile»
    «ELSEIF f instanceof ChooseBehavior»
		«(f as ChooseBehavior).compile»
    «ELSEIF f instanceof ForEachBehavior»
		«(f as ForEachBehavior).compile»
    «ELSEIF f instanceof DoExpr»
		«(f as DoExpr).compile»
    «ELSEIF f instanceof Done»
		«(f as Done).compile»
	«ELSEIF f instanceof RecursiveCall»
		«(f as RecursiveCall).compile»
    «ENDIF»
	'''

	def compile(ForeverBehavior f)'''
	forever «f.repeatedBehavior.compile»
	'''
	
	def compile(IfThenElseBehavior i) '''
	if «i.cond.compile» then «i.ifTrueBehavior.compile»
	«IF i.ifFalseBehavior != null»else «(i.ifFalseBehavior as PrefixedBehavior).compile»«ENDIF»
	'''
	
	def compile(ChooseBehavior c) '''
	choose «c.choiceBehavior.map[compile].join("} or {")»
	'''
	
	def compile(ForEachBehavior f)'''
	foreach «f.name» in «f.setOfValues.compile» «f.foreachBehavior.compile»
	'''
	
	def compile(RecursiveCall r)'''
	behavior («r.paramExpr.map[compile].join(", ")»)
	'''
	
	def compile(BehaviorStatement b)'''
	«IF b instanceof Valuing»
		«(b as Valuing).compile»
    «ELSEIF b instanceof Assert»
		«(b as Assert).compile»
	«ELSEIF b instanceof Action»
		«(b as Action).compile»
	«ENDIF»
	'''
	
    def compile(Assert a)'''
    assert «a.assertName» is { «a.assertExpression.compile» }
    '''

	def compile(AssertExpression a)'''
	«IF a instanceof Valuing»
		«a.valueing.compile»
	«ELSEIF a instanceof BooleanExpression»
		«a.constraint.compile»
	«ENDIF»
	'''

	def compile(Action a)'''
	via «a.complexName.compile» «IF a.suite instanceof SendAction»send «(a.suite as SendAction).sendExpression.compile
	»«ELSEIF a.suite instanceof ReceiveAction»receive «(a.suite as ReceiveAction).receivedValue.compile
	»«ENDIF»
	'''
	
	def compile(ArchBehaviorDecl a)'''
	behavior «a.behaviorName» («a.paramExpr.map[compile].join(", ")») is compose {
		«a.constituentList.compile»
	}
	binding {«a.bindings.compile»}
	''' 
	
	def compile(ConstituentAndList l)'''
	«FOR c:l.constituent»
		«c.compile»
	«ENDFOR»
	'''

	def compile(Constituent c)'''«c.constituentName» is «c.constituentValue.compile»'''

    def compile(Binding b)'''
    «IF b instanceof Relay»
    	«(b as Relay).compile»
    «ELSEIF b instanceof Unify»
    	«(b as Unify).compile»
    «ELSEIF b instanceof Quantify»
    	«(b as Quantify).compile»    
	«ENDIF»
    '''
    
    def compile(Relay r)'''
    relay «r.gate» to «r.connection.compile»
    '''

	def compile(Unify u)'''
    unify «u.multLeft»{«u.connLeft.compile»} to «u.multRight»{«u.connRight.compile»}
	'''

	def compile(Quantify q)'''
	«q.quantifier» {
		«q.elementInConstituent.map[compile].join(", ")» suchthat «q.bindings.compile»
	}
	'''
	
	def compile(ElementInConstituent e)'''«e.element» in «e.constituent»'''
	
	def compile(DataTypeDecl d) '''
		datatype «d.datatypeName»«IF d.datatype != null» is «d.datatype.compile»«ENDIF»«IF !d.function.empty» { 
		«FOR f : d.function»
			«f.compile»
		«ENDFOR»
		}
		«ENDIF»
	'''
	
	def compile(DataType d)'''«IF d instanceof BaseType»«(d as BaseType).compile»«
		ELSEIF d instanceof ConstructedType»«(d as ConstructedType).compile»«
		ELSEIF d instanceof TypeName»«(d as TypeName).compile»«
		ENDIF»'''
	
	def compile(FunctionDecl f)'''
		function ( «f.dataName»:«f.dataTypeName» ) :: «f.functionName»(«f.params.map[compile].join(", ")») : «
		f.returnType.compile» is {
		«FOR v:f.valuing»
			«v.compile»
		«ENDFOR»
		return «f.returnExpression.compile»
		}
	'''

	def compile(ParamType p) '''«p.name»:«p.type.compile»'''

	def compile(BaseType t)'''integer'''

	def compile(ConstructedType t)'''
		«IF t instanceof TupleType»
			«(t as TupleType).compile»
		«ELSEIF t instanceof SequenceType»
		sequence { «(t as SequenceType).typeOfSequence»}
    	«ELSEIF t instanceof RangeType»
		integer { «(t as RangeType).vmin.compile»..«(t as RangeType).vmax.compile»}
    	«ELSEIF t instanceof ConnectionType»
		«(t as ConnectionType).mode.compile»{ «(t as ConnectionType).typeOfConnection» }
		«ENDIF»
	'''
	
	def compile(TupleType t)'''
	tuple {«t.field.map[compile].join(", ")»}
	'''
	
	def compile(LabelledType l) '''«l.label.toString»:«l.type.compile»'''

	def compile(ModeType m) '''«m.value»'''
	
	
	def compile(TypeName t) '''«t.typeName»'''

    def compile(ComplexName c)'''«IF c.complexName != null»«c.complexName.join("::")»«ENDIF»'''
    
	def compile(Valuing v) '''
		value «v.valueName»«IF v.valueType != null» is «v.valueType.compile»«ENDIF» = «v.expression.compile»
	'''
	
	/* la classe Value n'existe pas ! 
	def compile(Value v)'''
	«IF v instanceof BaseValue»
		«(v as BaseValue).compile»
	«ELSEIF v instanceof ConstructedValue»
	  «(v as ConstructedValue).compile»
	«ELSEIF v instanceof UnobservableValue»
	  «(v as UnobservableValue).compile»
	«ENDIF»
	'''
	*/
	/* la classe BaseValue n'existe pas !
	 def compile(BaseValue b)'''
	 «IF b instanceof IntegerValue»
		«(b as IntegerValue).compile»
	 «ELSEIF b instanceof Any»
		«(b as Any).compile»
	 «ENDIF»
	 '''
	 */
	
	def compile(IntegerValue i)'''«i»'''
	
	def compile(Any a)'''any'''
	
	def compile(ConstructedValue c)'''
	«IF c instanceof Tuple»
		«(c as Tuple).compile»
	«ELSEIF c instanceof Sequence»
		«(c as Sequence).compile»
	«ENDIF»
	'''
	
	def compile(Tuple t)'''tuple{«t.tupleElement.map[compile].join(", ")»}'''
	
	def compile(TupleElement t)'''«t.elementLabel»=«t.elementValue.compile»'''
	
	def compile(Sequence s)'''sequence{«s.paramExpr.map[compile].join(", ")»}'''

    def compile(BindingExpression b)'''«(b as Expression).compile»'''

    def compile(BooleanExpression b)'''«(b as Expression).compile»'''
    
    /* erreur de recursivite avec Expression si on ajoute :
    ELSEIF e instanceof UnaryExpression»«(e as UnaryExpression).compile»« 
     */
	def compile(Expression e) '''«
	IF e instanceof BinaryExpression»«(e as BinaryExpression).left.compile»«(e as BinaryExpression).op»«(e as BinaryExpression).right.compile»«
	ELSEIF e instanceof UnaryExpression»«(e as UnaryExpression).op»«(e as UnaryExpression).right.compile»« 
    ENDIF»'''

	/*
	| CallExpression
	| '(' Expression ')'
	| Binding
	* 
	*/

    def compile(UnaryExpression u)'''«u.op»«u.right.compile»'''

/*
 *
   CallExpression: 
     ( Ident
	 ({FunctionCall.target=current} '(' (params+=Expression (',' params+=Expression)*)? ')')?
	 | LitteralExpression
	 )
	 (    {Field.target=current} '::' field+=Name
	 	| {Select.target=current} '::' 'select' '{' var=Name 'suchthat' res=Expression '}'
	 	| {Map.target=current} '::' 'map' '{' var=Name 'to' res=Expression '}'
	 	| {MethodCall.target=current} '::' method+=Name '(' (params+=Expression (',' params+=Expression)*)? ')'
	 )*
 */

	def compile(Assertion a)'''«
	IF a instanceof BinaryAssertion»«(a as BinaryAssertion).left.compile»«(a as BinaryAssertion).op»«(a as BinaryAssertion).right.compile»«
	ELSEIF a instanceof Action»«(a as Action).compile»«
	ENDIF»'''
    
    def compile(UnaryAssertion u)'''«u.op»«u.right.compile»'''
 
 /*
  CallAssertion returns Assertion:
	( Ident
	 ({FunctionCall.target=current} '(' (params+=Expression (',' params+=Expression)*)? ')')?
	 | LitteralAssertion
	 )
	 (    {Field.target=current} '::' field+=Name
	 	| {Select.target=current} '::' 'select' '{' var=Name 'suchthat' res=Expression '}'
	 	| {Map.target=current} '::' 'map' '{' var=Name 'to' res=Expression '}'
	 	| {MethodCall.target=current} '::' method+=Name '(' (params+=Expression (',' params+=Expression)*)? ')'
	 )*
;

LitteralAssertion returns Assertion:
	Value
;

FinalAssertion returns Assertion:
	UnaryAssertion
	| CallAssertion
	| '(' Assertion ')'
	| {Always} 'always' '{' expr=Assertion '}'
	| {Anynext} 'anynext' '{' expr=Assertion '}'
;
  */   
}