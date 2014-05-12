package org.archware.sosadl

import com.google.common.collect.AbstractIterator
import java.util.Iterator
import java.util.List
import org.archware.sosadl.sosADL.ArchitectureDecl
import org.archware.sosadl.sosADL.DataType
import org.archware.sosadl.sosADL.DataTypeDecl
import org.archware.sosadl.sosADL.EntityBlock
import org.archware.sosadl.sosADL.FunctionDecl
import org.archware.sosadl.sosADL.Import
import org.archware.sosadl.sosADL.IntegerType
import org.archware.sosadl.sosADL.Library
import org.archware.sosadl.sosADL.MediatorDecl
import org.archware.sosadl.sosADL.SequenceType
import org.archware.sosadl.sosADL.SoS
import org.archware.sosadl.sosADL.SosADL
import org.archware.sosadl.sosADL.SystemDecl
import org.archware.sosadl.sosADL.TypeName
import org.archware.sosadl.sosADL.Unit
import org.eclipse.xtext.xbase.lib.Functions
import org.eclipse.xtext.xbase.lib.Pair
import org.archware.sosadl.sosADL.TupleType
import org.archware.sosadl.sosADL.Expression
import org.archware.sosadl.sosADL.ParamType
import org.archware.sosadl.sosADL.Valuing
import org.archware.sosadl.sosADL.GateDecl
import org.archware.sosadl.sosADL.BehaviorDecl
import org.archware.sosadl.sosADL.AssertionDecl
import org.archware.sosadl.sosADL.DutyDecl
import org.archware.sosadl.sosADL.ArchBehaviorDecl
import org.archware.sosadl.sosADL.Connection
import org.archware.sosadl.sosADL.ProtocolDecl
import org.archware.sosadl.sosADL.Protocol
import org.archware.sosadl.sosADL.Behavior
import org.archware.sosadl.sosADL.ConstituentList
import org.archware.sosadl.sosADL.Assertion
import org.archware.sosadl.sosADL.ProtocolStatement
import org.archware.sosadl.sosADL.BehaviorStatement
import org.archware.sosadl.sosADL.Constituent
import org.archware.sosadl.sosADL.Any
import org.archware.sosadl.sosADL.BinaryExpression
import org.archware.sosadl.sosADL.Quantify
import org.archware.sosadl.sosADL.Relay
import org.archware.sosadl.sosADL.Unify
import org.archware.sosadl.sosADL.CallExpression
import org.archware.sosadl.sosADL.Tuple
import org.archware.sosadl.sosADL.IdentExpression
import org.archware.sosadl.sosADL.IntegerValue
import org.archware.sosadl.sosADL.Map
import org.archware.sosadl.sosADL.MethodCall
import org.archware.sosadl.sosADL.Select
import org.archware.sosadl.sosADL.UnaryExpression
import org.archware.sosadl.sosADL.UnobservableValue
import org.archware.sosadl.sosADL.ElementInConstituent
import org.archware.sosadl.sosADL.ComplexName
import org.archware.sosadl.sosADL.Sequence
import org.archware.sosadl.sosADL.Field
import org.archware.sosadl.sosADL.TupleElement
import org.archware.sosadl.sosADL.Action
import org.archware.sosadl.sosADL.Always
import org.archware.sosadl.sosADL.Anynext
import org.archware.sosadl.sosADL.BinaryAssertion
import org.archware.sosadl.sosADL.UnaryAssertion
import org.archware.sosadl.sosADL.ActionSuite
import org.archware.sosadl.sosADL.ReceiveAction
import org.archware.sosadl.sosADL.SendAction
import org.archware.sosadl.sosADL.AnyAction
import org.archware.sosadl.sosADL.AskAssertion
import org.archware.sosadl.sosADL.TellAssertion
import org.archware.sosadl.sosADL.ChooseProtocol
import org.archware.sosadl.sosADL.DoExpr
import org.archware.sosadl.sosADL.Done
import org.archware.sosadl.sosADL.ForEachBehavior
import org.archware.sosadl.sosADL.ForEachProtocol
import org.archware.sosadl.sosADL.IfThenElseProtocol
import org.archware.sosadl.sosADL.ProtocolAction
import org.archware.sosadl.sosADL.RepeatProtocol
import org.archware.sosadl.sosADL.AssertExpression
import org.archware.sosadl.sosADL.ProtocolActionSuite
import org.archware.sosadl.sosADL.ReceiveAnyProtocolAction
import org.archware.sosadl.sosADL.ReceiveProtocolAction
import org.archware.sosadl.sosADL.SendProtocolAction
import org.archware.sosadl.sosADL.ChooseBehavior
import org.archware.sosadl.sosADL.IfThenElseBehavior
import org.archware.sosadl.sosADL.RecursiveCall
import org.archware.sosadl.sosADL.RepeatBehavior

class SosADLComparator {
	def static compare(SosADL l, SosADL r) {
		sameElements(l.imports, r.imports, [p, q | compare(p, q)]) && compareUnit(l.content, r.content)
	}
	
	def static <T,U> zip(Iterator<T> l, Iterator<U> r) {
		val AbstractIterator<Pair<T,U>> i = [|
			if (l.hasNext && r.hasNext) Pair.of(l.next, r.next) else self.endOfData
		]
		i
	}
	
	def static <T,U> sameElements(List<T> l, List<U> r, Functions.Function2<T,U,Boolean> f) {
		l.size == r.size && zip(l.iterator, r.iterator).forall[p | f.apply(p.key, p.value)]
	}
	
	def static <T> compareOpt(T l, T r, Functions.Function2<T,T,Boolean> f) {
		if(l == null) { r == null }
		else { r != null && f.apply(l, r) }
	}
	
	def static compare(Import l, Import r) { l.importName.equals(r.importName) }
	
	def static dispatch compareUnit(Library l, Library r)	{ l.libraryName.equals(r.libraryName) && compare(l.decls, r.decls) }
	def static dispatch compareUnit(SoS l, SoS r)			{ l.sosName.equals(r.sosName) && compare(l.decls, r.decls) }
	def static dispatch compareUnit(Unit l, Unit r)			{ false }
	
	def static compare(EntityBlock l, EntityBlock r) {
		sameElements(l.datatypes, r.datatypes, [p, q | compare(p, q)]) && sameElements(l.functions, r.functions, [p, q | compare(p, q)])
		&& sameElements(l.systems, r.systems, [p, q | compare(p, q)]) && sameElements(l.mediators, r.mediators, [p, q | compare(p, q)])
		&& sameElements(l.architectures, r.architectures, [p, q | compare(p, q)])
	}
	
	def static compare(DataTypeDecl l, DataTypeDecl r) {
		l.datatypeName.equals(r.datatypeName) && compareOpt(l.datatype, r.datatype, [p, q | compareDataType(p, q)]) && sameElements(l.function, r.function, [p, q | compare(p, q)])
	}
	
	def static dispatch boolean compareDataType(TypeName l, TypeName r)			{ l.typeName.equals(r.typeName) }
	def static dispatch boolean compareDataType(IntegerType l, IntegerType r)	{ true }
	def static dispatch boolean compareDataType(SequenceType l, SequenceType r)	{ compareDataType(l.typeOfSequence, r.typeOfSequence) }
	def static dispatch boolean compareDataType(TupleType l, TupleType r)		{ sameElements(l.field, r.field, [p, q | compare(p, q)]) }
	def static dispatch boolean compareDataType(DataType l, DataType r)			{ false }
	
	def static compare(FunctionDecl l, FunctionDecl r) {
		l.dataName.equals(r.dataName) && l.dataTypeName.equals(r.dataTypeName) && l.functionName.equals(r.functionName)
		&& sameElements(l.params, r.params, [p, q | compare(p, q)]) && compareDataType(l.returnType, r.returnType)
		&& sameElements(l.valuing, r.valuing, [p, q | compare(p, q)]) && compareExpression(l.returnExpression, r.returnExpression)
	}
	
	def static compare(ParamType l, ParamType r) { l.name.equals(r.name) && compareDataType(l.type, r.type) }
	
	def static compare(Valuing l, Valuing r) { l.valueName.equals(r.valueName) && compareOpt(l.valueType, r.valueType, [p, q | compareDataType(p, q)]) && compareExpression(l.expression, r.expression) }
	
	def static compare(SystemDecl l, SystemDecl r) {
		l.systemName.equals(r.systemName) && sameElements(l.params, r.params, [p, q | compare(p, q)])
		&& sameElements(l.datatypes, r.datatypes, [p, q | compare(p, q)])
		&& sameElements(l.gates, r.gates, [p, q | compare(p, q)])
		&& compare(l.behavior, r.behavior)
		&& compareOpt(l.assertionDecl, r.assertionDecl, [p, q | compare(p, q)])
	}
	
	def static compare(MediatorDecl l, MediatorDecl r) {
		l.mediatorName.equals(r.mediatorName) && sameElements(l.params, r.params, [p, q | compare(p, q)])
		&& sameElements(l.datatypes, r.datatypes, [p, q | compare(p, q)])
		&& sameElements(l.duties, r.duties, [p, q | compare(p, q)])
		&& compare(l.behavior, r.behavior)
	}
	
	def static compare(ArchitectureDecl l, ArchitectureDecl r) {
		l.architectureName.equals(r.architectureName) && sameElements(l.params, r.params, [p, q | compare(p, q)])
		&& sameElements(l.datatypes, r.datatypes, [p, q | compare(p, q)])
		&& sameElements(l.gates, r.gates, [p, q | compare(p, q)])
		&& compare(l.archBehavior, r.archBehavior)
		&& compareOpt(l.assertionDecl, r.assertionDecl, [p, q | compare(p, q)])
	}
	
	def static compare(GateDecl l, GateDecl r) {
		l.gateName.equals(r.gateName)
		&& sameElements(l.connections, r.connections, [p, q | compare(p, q)])
		&& compare(l.protocolDecl, r.protocolDecl)
	}

	def static compare(DutyDecl l, DutyDecl r) {
		l.dutyName.equals(r.dutyName)
		&& sameElements(l.connections, r.connections, [p, q | compare(p, q)])
		&& compare(l.assertion, r.assertion)
		&& compare(l.assumedProtocol, r.assumedProtocol)
	}
	
	def static compare(Connection l, Connection r) {
		l.envConnection == r.envConnection
		&& l.name.equals(r.name)
		&& l.mode == r.mode
		&& compareDataType(l.valueType, r.valueType)
	}
	
	def static compare(ProtocolDecl l, ProtocolDecl r) {
		l.protocolName.equals(r.protocolName) && compare(l.protocolBody, r.protocolBody)
	}
	
	def static compare(BehaviorDecl l, BehaviorDecl r) {
		l.behaviorName.equals(r.behaviorName)
		&& sameElements(l.paramExpr, r.paramExpr, [p, q | compareExpression(p, q)])
		&& compare(l.behaviorBody, r.behaviorBody)
	}

	def static compare(ArchBehaviorDecl l, ArchBehaviorDecl r) {
		l.behaviorName.equals(r.behaviorName)
		&& sameElements(l.paramExpr, r.paramExpr, [p, q | compareExpression(p, q)])
		&& compare(l.constituentList, r.constituentList)
		&& compareExpression(l.bindings, r.bindings)
	}
	
	def static compare(AssertionDecl l, AssertionDecl r) {
		l.assertionName.equals(r.assertionName)
		&& sameElements(l.valuing, r.valuing, [p, q | compare(p, q)])
		&& compareAssertion(l.assertionExpr, r.assertionExpr)
	}
	
	def static compare(Protocol l, Protocol r) { sameElements(l.statements, r.statements, [p, q | compareProtocolStatement(p, q)]) }
	
	def static compare(Behavior l, Behavior r) { sameElements(l.statements, r.statements, [p, q | compareBehaviorStatement(p, q)]) }
	
	def static compare(ConstituentList l, ConstituentList r) { sameElements(l.constituent, r.constituent, [p, q | compare(p, q)]) }
	
	def static compare(Constituent l, Constituent r) { l.constituentName.equals(r.constituentName) && compareExpression(l.constituentValue, r.constituentValue) }
	
	def static dispatch boolean compareExpression(Any l, Any r)								{ true }
	def static dispatch boolean compareExpression(BinaryExpression l, BinaryExpression r)	{ compareExpression(l.left, r.left) && l.op.equals(r.op) && compareExpression(l.right, r.right) }
	def static dispatch boolean compareExpression(Quantify l, Quantify r)					{ l.quantifier.equals(r.quantifier) && sameElements(l.elementInConstituent, r.elementInConstituent, [p, q | compare(p, q)]) && compareExpression(l.bindings, r.bindings) }
	def static dispatch boolean compareExpression(Relay l, Relay r)							{ compare(l.gate, r.gate) && compare(l.connection, r.connection) }
	def static dispatch boolean compareExpression(Unify l, Unify r)							{ l.multLeft.equals(r.multLeft) && compare(l.connLeft, r.connLeft) && l.multRight.equals(r.multRight) && compare(l.connRight, r.connRight) }
	def static dispatch boolean compareExpression(CallExpression l, CallExpression r)		{ l.functionName.equals(r.functionName) && sameElements(l.params, r.params, [p, q | compareExpression(p, q)]) }
	def static dispatch boolean compareExpression(Sequence l, Sequence r)					{ sameElements(l.paramExpr, r.paramExpr, [p, q | compareExpression(p, q)]) }
	def static dispatch boolean compareExpression(Tuple l, Tuple r)							{ sameElements(l.tupleElement, r.tupleElement, [p, q | compare(p, q)]) }
	def static dispatch boolean compareExpression(Field l, Field r)							{ compareExpression(l.object, r.object) && l.fieldName.equals(r.fieldName) }
	def static dispatch boolean compareExpression(IdentExpression l, IdentExpression r)		{ l.ident.equals(r.ident) }
	def static dispatch boolean compareExpression(IntegerValue l, IntegerValue r)			{ l.absInt == r.absInt }
	def static dispatch boolean compareExpression(Map l, Map r)								{ compareExpression(l.object, r.object) && l.mapName.equals(r.mapName) && compareExpression(l.mapExpr, r.mapExpr) }
	def static dispatch boolean compareExpression(MethodCall l, MethodCall r)				{ compareExpression(l.object, r.object) && l.methodName.equals(r.methodName) && sameElements(l.params, r.params, [p, q | compareExpression(p, q)]) }
	def static dispatch boolean compareExpression(Select l, Select r)						{ compareExpression(l.object, r.object) && l.selectName.equals(r.selectName) && compareExpression(l.selectExpr, r.selectExpr) }
	def static dispatch boolean compareExpression(UnaryExpression l, UnaryExpression r)		{ l.op.equals(r.op) && compareExpression(l.right, r.right) }
	def static dispatch boolean compareExpression(UnobservableValue l, UnobservableValue r)	{ true }
	def static dispatch boolean compareExpression(Expression l, Expression r)				{ false }
	
	def static compare(ElementInConstituent l, ElementInConstituent r) {
		l.element.equals(r.element) && l.constituent.equals(r.constituent)
	}
	
	def static compare(ComplexName l, ComplexName r) {
		sameElements(l.complexName, r.complexName, [p, q | p.equals(q)])
	}
	
	def static compare(TupleElement l, TupleElement r) { l.elementLabel.equals(r.elementLabel) && compareExpression(l.elementValue, r.elementValue) }

	def static dispatch boolean compareAssertion(Action l, Action r)					{ compare(l.complexName, r.complexName) && compareActionSuite(l.suite, r.suite) }
	def static dispatch boolean compareAssertion(Always l, Always r)					{ compareAssertion(l.expr, r.expr) }
	def static dispatch boolean compareAssertion(Anynext l, Anynext r)					{ compareAssertion(l.expr, r.expr) }
	def static dispatch boolean compareAssertion(BinaryAssertion l, BinaryAssertion r)	{ compareAssertion(l.left, r.left) && l.op.equals(r.op) && compareAssertion(l.right, r.right) }
	def static dispatch boolean compareAssertion(Expression l, Expression r)			{ compareExpression(l, r) }
	def static dispatch boolean compareAssertion(UnaryAssertion l, UnaryAssertion r)	{ l.op.equals(r.op) && compareAssertion(l.right, r.right) }
	def static dispatch boolean compareAssertion(Assertion l, Assertion r)				{ false }

	def static dispatch boolean compareActionSuite(ReceiveAction l, ReceiveAction r)	{ l.receivedValue.equals(r.receivedValue) }
	def static dispatch boolean compareActionSuite(SendAction l, SendAction r)			{ compareExpression(l.sendExpression, r.sendExpression) }
	def static dispatch boolean compareActionSuite(ActionSuite l, ActionSuite r)		{ false }
	
	def static dispatch boolean compareProtocolStatement(AnyAction l, AnyAction r)						{ true }
	def static dispatch boolean compareProtocolStatement(AskAssertion l, AskAssertion r)				{ l.assertName.equals(r.assertName) && compareAssertExpression(l.assertExpression, r.assertExpression) }
	def static dispatch boolean compareProtocolStatement(TellAssertion l, TellAssertion r)				{ l.assertName.equals(r.assertName) && compareAssertExpression(l.assertExpression, r.assertExpression) }
	def static dispatch boolean compareProtocolStatement(ChooseProtocol l, ChooseProtocol r)			{ sameElements(l.choiceProtocol, r.choiceProtocol, [p, q | compare(p, q)]) }
	def static dispatch boolean compareProtocolStatement(DoExpr l, DoExpr r)							{ compareExpression(l.expr, r.expr) }
	def static dispatch boolean compareProtocolStatement(Done l, Done r)								{ true }
	def static dispatch boolean compareProtocolStatement(ForEachProtocol l, ForEachProtocol r)			{ l.name.equals(r.name) && compareExpression(l.setOfValues, r.setOfValues) && compare(l.foreachProtocol, r.foreachProtocol) }
	def static dispatch boolean compareProtocolStatement(IfThenElseProtocol l, IfThenElseProtocol r)	{ compareExpression(l.cond, r.cond) && compare(l.ifTrueProtocol, r.ifTrueProtocol) && compareOpt(l.ifFalseProtocol, r.ifFalseProtocol, [p, q | compare(p, q)]) }
	def static dispatch boolean compareProtocolStatement(ProtocolAction l, ProtocolAction r)			{ compare(l.complexName, r.complexName) && compareProtocolActionSuite(l.suite, r.suite) }
	def static dispatch boolean compareProtocolStatement(RepeatProtocol l, RepeatProtocol r)			{ compare(l.repeatedProtocol, r.repeatedProtocol) }
	def static dispatch boolean compareProtocolStatement(Valuing l, Valuing r)							{ compare(l, r) }
	def static dispatch boolean compareProtocolStatement(ProtocolStatement l, ProtocolStatement r)		{ false }
	
	def static dispatch boolean compareProtocolActionSuite(ReceiveAnyProtocolAction l, ReceiveAnyProtocolAction r)	{ true }
	def static dispatch boolean compareProtocolActionSuite(ReceiveProtocolAction l, ReceiveProtocolAction r)		{ l.receivedValue.equals(r.receivedValue) }
	def static dispatch boolean compareProtocolActionSuite(SendProtocolAction l, SendProtocolAction r)				{ compareExpression(l.sendExpression, r.sendExpression) }
	def static dispatch boolean compareProtocolActionSuite(ProtocolActionSuite l, ProtocolActionSuite r)			{ false }

	def static dispatch boolean compareBehaviorStatement(Action l, Action r)							{ compare(l.complexName, r.complexName) && compareActionSuite(l.suite, r.suite) }
	def static dispatch boolean compareBehaviorStatement(AskAssertion l, AskAssertion r)				{ l.assertName.equals(r.assertName) && compareAssertExpression(l.assertExpression, r.assertExpression) }
	def static dispatch boolean compareBehaviorStatement(TellAssertion l, TellAssertion r)				{ l.assertName.equals(r.assertName) && compareAssertExpression(l.assertExpression, r.assertExpression) }
	def static dispatch boolean compareBehaviorStatement(ChooseBehavior l, ChooseBehavior r)			{ sameElements(l.choiceBehavior, r.choiceBehavior, [p, q | compare(p, q)]) }
	def static dispatch boolean compareBehaviorStatement(DoExpr l, DoExpr r)							{ compareExpression(l.expr, r.expr) }
	def static dispatch boolean compareBehaviorStatement(Done l, Done r)								{ true }
	def static dispatch boolean compareBehaviorStatement(ForEachBehavior l, ForEachBehavior r)			{ l.name.equals(r.name) && compareExpression(l.setOfValues, r.setOfValues) && compare(l.foreachBehavior, r.foreachBehavior) }
	def static dispatch boolean compareBehaviorStatement(IfThenElseBehavior l, IfThenElseBehavior r)	{ compareExpression(l.cond, r.cond) && compare(l.ifTrueBehavior, r.ifTrueBehavior) && compareOpt(l.ifFalseBehavior, r.ifFalseBehavior, [p, q | compare(p, q)]) }
	def static dispatch boolean compareBehaviorStatement(RecursiveCall l, RecursiveCall r)				{ sameElements(l.paramExpr, r.paramExpr, [p, q | compareExpression(p, q)]) }
	def static dispatch boolean compareBehaviorStatement(RepeatBehavior l, RepeatBehavior r)			{ compare(l.repeatedBehavior, r.repeatedBehavior) }
	def static dispatch boolean compareBehaviorStatement(Valuing l, Valuing r)							{ compare(l, r) }
	def static dispatch boolean compareBehaviorStatement(BehaviorStatement l, BehaviorStatement r)		{ false }
	
	def static dispatch boolean compareAssertExpression(Expression l, Expression r)					{ compareExpression(l, r) }
	def static dispatch boolean compareAssertExpression(Valuing l, Valuing r)						{ compare(l, r) }
	def static dispatch boolean compareAssertExpression(AssertExpression l, AssertExpression r)		{ false }
}
