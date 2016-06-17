// Automatically generated
package org.archware.sosadl.sosADL.generator

import java.util.List
import javax.annotation.Generated
import org.eclipse.xtext.xbase.lib.Functions.Function1

import org.archware.sosadl.sosADL.Quantifier
import org.archware.sosadl.sosADL.Multiplicity
import org.archware.sosadl.sosADL.ModeType

import org.archware.sosadl.sosADL.ReceiveAction
import org.archware.sosadl.sosADL.SendAction
import org.archware.sosadl.sosADL.ArchBehaviorDecl
import org.archware.sosadl.sosADL.ArchitectureDecl
import org.archware.sosadl.sosADL.AskAssertion
import org.archware.sosadl.sosADL.TellAssertion
import org.archware.sosadl.sosADL.AssertionDecl
import org.archware.sosadl.sosADL.Behavior
import org.archware.sosadl.sosADL.BehaviorDecl
import org.archware.sosadl.sosADL.Action
import org.archware.sosadl.sosADL.AssertBehavior
import org.archware.sosadl.sosADL.ChooseBehavior
import org.archware.sosadl.sosADL.DoExprBehavior
import org.archware.sosadl.sosADL.DoneBehavior
import org.archware.sosadl.sosADL.ForEachBehavior
import org.archware.sosadl.sosADL.IfThenElseBehavior
import org.archware.sosadl.sosADL.RecursiveCall
import org.archware.sosadl.sosADL.RepeatBehavior
import org.archware.sosadl.sosADL.ValuingBehavior
import org.archware.sosadl.sosADL.Quantify
import org.archware.sosadl.sosADL.Relay
import org.archware.sosadl.sosADL.Unify
import org.archware.sosadl.sosADL.ComplexName
import org.archware.sosadl.sosADL.Connection
import org.archware.sosadl.sosADL.Constituent
import org.archware.sosadl.sosADL.Sequence
import org.archware.sosadl.sosADL.Tuple
import org.archware.sosadl.sosADL.BooleanType
import org.archware.sosadl.sosADL.ConnectionType
import org.archware.sosadl.sosADL.IntegerType
import org.archware.sosadl.sosADL.NamedType
import org.archware.sosadl.sosADL.RangeType
import org.archware.sosadl.sosADL.SequenceType
import org.archware.sosadl.sosADL.TupleType
import org.archware.sosadl.sosADL.DataTypeDecl
import org.archware.sosadl.sosADL.DutyDecl
import org.archware.sosadl.sosADL.ElementInConstituent
import org.archware.sosadl.sosADL.EntityBlock
import org.archware.sosadl.sosADL.Any
import org.archware.sosadl.sosADL.BinaryExpression
import org.archware.sosadl.sosADL.CallExpression
import org.archware.sosadl.sosADL.Field
import org.archware.sosadl.sosADL.IdentExpression
import org.archware.sosadl.sosADL.IntegerValue
import org.archware.sosadl.sosADL.Map
import org.archware.sosadl.sosADL.MethodCall
import org.archware.sosadl.sosADL.Select
import org.archware.sosadl.sosADL.UnaryExpression
import org.archware.sosadl.sosADL.UnobservableValue
import org.archware.sosadl.sosADL.FieldDecl
import org.archware.sosadl.sosADL.FormalParameter
import org.archware.sosadl.sosADL.FunctionDecl
import org.archware.sosadl.sosADL.GateDecl
import org.archware.sosadl.sosADL.Import
import org.archware.sosadl.sosADL.MediatorDecl
import org.archware.sosadl.sosADL.Protocol
import org.archware.sosadl.sosADL.ReceiveAnyProtocolAction
import org.archware.sosadl.sosADL.ReceiveProtocolAction
import org.archware.sosadl.sosADL.SendProtocolAction
import org.archware.sosadl.sosADL.ProtocolDecl
import org.archware.sosadl.sosADL.AnyAction
import org.archware.sosadl.sosADL.AssertProtocol
import org.archware.sosadl.sosADL.ChooseProtocol
import org.archware.sosadl.sosADL.DoExprProtocol
import org.archware.sosadl.sosADL.DoneProtocol
import org.archware.sosadl.sosADL.ForEachProtocol
import org.archware.sosadl.sosADL.IfThenElseProtocol
import org.archware.sosadl.sosADL.ProtocolAction
import org.archware.sosadl.sosADL.RepeatProtocol
import org.archware.sosadl.sosADL.ValuingProtocol
import org.archware.sosadl.sosADL.SosADL
import org.archware.sosadl.sosADL.SystemDecl
import org.archware.sosadl.sosADL.TupleElement
import org.archware.sosadl.sosADL.Library
import org.archware.sosadl.sosADL.SoS
import org.archware.sosadl.sosADL.Valuing

@Generated(value = "sosADL")
class CoqGenerator {

	def <T> _generateO(T t, Function1<? super T, ? extends CharSequence> gen) {
		if (t == null) {
			return "None"
		} else {
			return '''(Some «gen.apply(t)»)'''
		}
	}

	def <T> _generateL(List<T> l, Function1<? super T, ? extends CharSequence> gen) '''[«l.map(gen).join("; ")»]'''

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

	def generatestring(String i) '''"«i»"'''

	def generateQuantifier(Quantifier n) {
		switch (n) {
			case QUANTIFIER_FORALL: {
				return '''QuantifierForall'''
			}
			
			case QUANTIFIER_EXISTS: {
				return '''QuantifierExists'''
			}
		}
	}
	
	def generateMultiplicity(Multiplicity n) {
		switch (n) {
			case MULTIPLICITY_ONE: {
				return '''MultiplicityOne'''
			}
			
			case MULTIPLICITY_NONE: {
				return '''MultiplicityNone'''
			}
			
			case MULTIPLICITY_LONE: {
				return '''MultiplicityLone'''
			}
			
			case MULTIPLICITY_ANY: {
				return '''MultiplicityAny'''
			}
			
			case MULTIPLICITY_SOME: {
				return '''MultiplicitySome'''
			}
			
			case MULTIPLICITY_ALL: {
				return '''MultiplicityAll'''
			}
		}
	}
	
	def generateModeType(ModeType n) {
		switch (n) {
			case MODE_TYPE_IN: {
				return '''ModeTypeIn'''
			}
			
			case MODE_TYPE_OUT: {
				return '''ModeTypeOut'''
			}
			
			case MODE_TYPE_INOUT: {
				return '''ModeTypeInout'''
			}
		}
	}

	def dispatch CharSequence generatet_ActionSuite(ReceiveAction n) '''(ReceiveAction «_generateO(n.getVariable(), [generatestring])»)'''
	
	def dispatch CharSequence generatet_ActionSuite(SendAction n) '''(SendAction «_generateO(n.getExpression(), [generatet_Expression])»)'''
	
	def CharSequence generatet_ArchBehaviorDecl(ArchBehaviorDecl n) '''(ArchBehaviorDecl «_generateO(n.getName(), [generatestring])» «_generateL(n.getConstituents(), [generatet_Constituent])» «_generateO(n.getBindings(), [generatet_Expression])»)'''
	
	def CharSequence generatet_ArchitectureDecl(ArchitectureDecl n) '''(ArchitectureDecl «_generateO(n.getName(), [generatestring])» «_generateL(n.getParameters(), [generatet_FormalParameter])» «_generateL(n.getDatatypes(), [generatet_DataTypeDecl])» «_generateL(n.getGates(), [generatet_GateDecl])» «_generateO(n.getBehavior(), [generatet_ArchBehaviorDecl])» «_generateO(n.getAssertion(), [generatet_AssertionDecl])»)'''
	
	def dispatch CharSequence generatet_Assert(AskAssertion n) '''(AskAssertion «_generateO(n.getName(), [generatestring])» «_generateO(n.getExpression(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_Assert(TellAssertion n) '''(TellAssertion «_generateO(n.getName(), [generatestring])» «_generateO(n.getExpression(), [generatet_Expression])»)'''
	
	def CharSequence generatet_AssertionDecl(AssertionDecl n) '''(AssertionDecl «_generateO(n.getName(), [generatestring])» «_generateO(n.getBody(), [generatet_Protocol])»)'''
	
	def CharSequence generatet_Behavior(Behavior n) '''(Behavior «_generateL(n.getStatements(), [generatet_BehaviorStatement])»)'''
	
	def CharSequence generatet_BehaviorDecl(BehaviorDecl n) '''(BehaviorDecl «_generateO(n.getName(), [generatestring])» «_generateO(n.getBody(), [generatet_Behavior])»)'''
	
	def dispatch CharSequence generatet_BehaviorStatement(Action n) '''(Action «_generateO(n.getComplexName(), [generatet_ComplexName])» «_generateO(n.getSuite(), [generatet_ActionSuite])»)'''
	
	def dispatch CharSequence generatet_BehaviorStatement(AssertBehavior n) '''(AssertBehavior «_generateO(n.getAssertion(), [generatet_Assert])»)'''
	
	def dispatch CharSequence generatet_BehaviorStatement(ChooseBehavior n) '''(ChooseBehavior «_generateL(n.getBranches(), [generatet_Behavior])»)'''
	
	def dispatch CharSequence generatet_BehaviorStatement(DoExprBehavior n) '''(DoExprBehavior «_generateO(n.getExpression(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_BehaviorStatement(DoneBehavior n) '''DoneBehavior'''
	
	def dispatch CharSequence generatet_BehaviorStatement(ForEachBehavior n) '''(ForEachBehavior «_generateO(n.getVariable(), [generatestring])» «_generateO(n.getSetOfValues(), [generatet_Expression])» «_generateO(n.getRepeated(), [generatet_Behavior])»)'''
	
	def dispatch CharSequence generatet_BehaviorStatement(IfThenElseBehavior n) '''(IfThenElseBehavior «_generateO(n.getCondition(), [generatet_Expression])» «_generateO(n.getIfTrue(), [generatet_Behavior])» «_generateO(n.getIfFalse(), [generatet_Behavior])»)'''
	
	def dispatch CharSequence generatet_BehaviorStatement(RecursiveCall n) '''(RecursiveCall «_generateL(n.getParameters(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_BehaviorStatement(RepeatBehavior n) '''(RepeatBehavior «_generateO(n.getRepeated(), [generatet_Behavior])»)'''
	
	def dispatch CharSequence generatet_BehaviorStatement(ValuingBehavior n) '''(ValuingBehavior «_generateO(n.getValuing(), [generatet_Valuing])»)'''
	
	def dispatch CharSequence generatet_Binding(Quantify n) '''(Binding_Quantify «_generateO(n.getQuantifier(), [generateQuantifier])» «_generateL(n.getElements(), [generatet_ElementInConstituent])» «_generateO(n.getBindings(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_Binding(Relay n) '''(Binding_Relay «_generateO(n.getConnLeft(), [generatet_ComplexName])» «_generateO(n.getConnRight(), [generatet_ComplexName])»)'''
	
	def dispatch CharSequence generatet_Binding(Unify n) '''(Binding_Unify «_generateO(n.getMultLeft(), [generateMultiplicity])» «_generateO(n.getConnLeft(), [generatet_ComplexName])» «_generateO(n.getMultRight(), [generateMultiplicity])» «_generateO(n.getConnRight(), [generatet_ComplexName])»)'''
	
	def CharSequence generatet_ComplexName(ComplexName n) '''(ComplexName «_generateL(n.getName(), [generatestring])»)'''
	
	def CharSequence generatet_Connection(Connection n) '''(Connection «_generateO(n.isEnvironment(), [generatebool])» «_generateO(n.getName(), [generatestring])» «_generateO(n.getMode(), [generateModeType])» «_generateO(n.getValueType(), [generatet_DataType])»)'''
	
	def CharSequence generatet_Constituent(Constituent n) '''(Constituent «_generateO(n.getName(), [generatestring])» «_generateO(n.getValue(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_ConstructedValue(Sequence n) '''(ConstructedValue_Sequence «_generateL(n.getElements(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_ConstructedValue(Tuple n) '''(ConstructedValue_Tuple «_generateL(n.getElements(), [generatet_TupleElement])»)'''
	
	def dispatch CharSequence generatet_DataType(BooleanType n) '''BooleanType'''
	
	def dispatch CharSequence generatet_DataType(ConnectionType n) '''(ConnectionType «_generateO(n.getMode(), [generateModeType])» «_generateO(n.getType(), [generatet_DataType])»)'''
	
	def dispatch CharSequence generatet_DataType(IntegerType n) '''IntegerType'''
	
	def dispatch CharSequence generatet_DataType(NamedType n) '''(NamedType «_generateO(n.getName(), [generatestring])»)'''
	
	def dispatch CharSequence generatet_DataType(RangeType n) '''(RangeType «_generateO(n.getVmin(), [generatet_Expression])» «_generateO(n.getVmax(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_DataType(SequenceType n) '''(SequenceType «_generateO(n.getType(), [generatet_DataType])»)'''
	
	def dispatch CharSequence generatet_DataType(TupleType n) '''(TupleType «_generateL(n.getFields(), [generatet_FieldDecl])»)'''
	
	def CharSequence generatet_DataTypeDecl(DataTypeDecl n) '''(DataTypeDecl «_generateO(n.getName(), [generatestring])» «_generateO(n.getDatatype(), [generatet_DataType])» «_generateL(n.getFunctions(), [generatet_FunctionDecl])»)'''
	
	def CharSequence generatet_DutyDecl(DutyDecl n) '''(DutyDecl «_generateO(n.getName(), [generatestring])» «_generateL(n.getConnections(), [generatet_Connection])» «_generateO(n.getAssertion(), [generatet_AssertionDecl])» «_generateO(n.getProtocol(), [generatet_ProtocolDecl])»)'''
	
	def CharSequence generatet_ElementInConstituent(ElementInConstituent n) '''(ElementInConstituent «_generateO(n.getVariable(), [generatestring])» «_generateO(n.getConstituent(), [generatestring])»)'''
	
	def CharSequence generatet_EntityBlock(EntityBlock n) '''(EntityBlock «_generateL(n.getDatatypes(), [generatet_DataTypeDecl])» «_generateL(n.getFunctions(), [generatet_FunctionDecl])» «_generateL(n.getSystems(), [generatet_SystemDecl])» «_generateL(n.getMediators(), [generatet_MediatorDecl])» «_generateL(n.getArchitectures(), [generatet_ArchitectureDecl])»)'''
	
	def dispatch CharSequence generatet_Expression(Any n) '''Any'''
	
	def dispatch CharSequence generatet_Expression(BinaryExpression n) '''(BinaryExpression «_generateO(n.getLeft(), [generatet_Expression])» «_generateO(n.getOp(), [generatestring])» «_generateO(n.getRight(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_Expression(CallExpression n) '''(CallExpression «_generateO(n.getFunction(), [generatestring])» «_generateL(n.getParameters(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_Expression(Field n) '''(Field «_generateO(n.getObject(), [generatet_Expression])» «_generateO(n.getField(), [generatestring])»)'''
	
	def dispatch CharSequence generatet_Expression(IdentExpression n) '''(IdentExpression «_generateO(n.getIdent(), [generatestring])»)'''
	
	def dispatch CharSequence generatet_Expression(IntegerValue n) '''(IntegerValue «_generateO(n.getAbsInt(), [generateZ])»)'''
	
	def dispatch CharSequence generatet_Expression(Map n) '''(Map «_generateO(n.getObject(), [generatet_Expression])» «_generateO(n.getVariable(), [generatestring])» «_generateO(n.getExpression(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_Expression(MethodCall n) '''(MethodCall «_generateO(n.getObject(), [generatet_Expression])» «_generateO(n.getMethod(), [generatestring])» «_generateL(n.getParameters(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_Expression(Quantify n) '''(Expression_Quantify «_generateO(n.getQuantifier(), [generateQuantifier])» «_generateL(n.getElements(), [generatet_ElementInConstituent])» «_generateO(n.getBindings(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_Expression(Relay n) '''(Expression_Relay «_generateO(n.getConnLeft(), [generatet_ComplexName])» «_generateO(n.getConnRight(), [generatet_ComplexName])»)'''
	
	def dispatch CharSequence generatet_Expression(Select n) '''(Select «_generateO(n.getObject(), [generatet_Expression])» «_generateO(n.getVariable(), [generatestring])» «_generateO(n.getCondition(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_Expression(Sequence n) '''(Expression_Sequence «_generateL(n.getElements(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_Expression(Tuple n) '''(Expression_Tuple «_generateL(n.getElements(), [generatet_TupleElement])»)'''
	
	def dispatch CharSequence generatet_Expression(UnaryExpression n) '''(UnaryExpression «_generateO(n.getOp(), [generatestring])» «_generateO(n.getRight(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_Expression(Unify n) '''(Expression_Unify «_generateO(n.getMultLeft(), [generateMultiplicity])» «_generateO(n.getConnLeft(), [generatet_ComplexName])» «_generateO(n.getMultRight(), [generateMultiplicity])» «_generateO(n.getConnRight(), [generatet_ComplexName])»)'''
	
	def dispatch CharSequence generatet_Expression(UnobservableValue n) '''UnobservableValue'''
	
	def CharSequence generatet_FieldDecl(FieldDecl n) '''(FieldDecl «_generateO(n.getName(), [generatestring])» «_generateO(n.getType(), [generatet_DataType])»)'''
	
	def CharSequence generatet_FormalParameter(FormalParameter n) '''(FormalParameter «_generateO(n.getName(), [generatestring])» «_generateO(n.getType(), [generatet_DataType])»)'''
	
	def CharSequence generatet_FunctionDecl(FunctionDecl n) '''(FunctionDecl «_generateO(n.getData(), [generatet_FormalParameter])» «_generateO(n.getName(), [generatestring])» «_generateL(n.getParameters(), [generatet_FormalParameter])» «_generateO(n.getType(), [generatet_DataType])» «_generateL(n.getValuing(), [generatet_Valuing])» «_generateO(n.getExpression(), [generatet_Expression])»)'''
	
	def CharSequence generatet_GateDecl(GateDecl n) '''(GateDecl «_generateO(n.getName(), [generatestring])» «_generateL(n.getConnections(), [generatet_Connection])» «_generateO(n.getProtocol(), [generatet_ProtocolDecl])»)'''
	
	def CharSequence generatet_Import(Import n) '''(Import «_generateO(n.getImportedLibrary(), [generatestring])»)'''
	
	def CharSequence generatet_MediatorDecl(MediatorDecl n) '''(MediatorDecl «_generateO(n.getName(), [generatestring])» «_generateL(n.getParameters(), [generatet_FormalParameter])» «_generateL(n.getDatatypes(), [generatet_DataTypeDecl])» «_generateL(n.getDuties(), [generatet_DutyDecl])» «_generateO(n.getBehavior(), [generatet_BehaviorDecl])» «_generateO(n.getAssumption(), [generatet_AssertionDecl])» «_generateO(n.getAssertion(), [generatet_AssertionDecl])»)'''
	
	def CharSequence generatet_Protocol(Protocol n) '''(Protocol «_generateL(n.getStatements(), [generatet_ProtocolStatement])»)'''
	
	def dispatch CharSequence generatet_ProtocolActionSuite(ReceiveAnyProtocolAction n) '''ReceiveAnyProtocolAction'''
	
	def dispatch CharSequence generatet_ProtocolActionSuite(ReceiveProtocolAction n) '''(ReceiveProtocolAction «_generateO(n.getVariable(), [generatestring])»)'''
	
	def dispatch CharSequence generatet_ProtocolActionSuite(SendProtocolAction n) '''(SendProtocolAction «_generateO(n.getExpression(), [generatet_Expression])»)'''
	
	def CharSequence generatet_ProtocolDecl(ProtocolDecl n) '''(ProtocolDecl «_generateO(n.getName(), [generatestring])» «_generateO(n.getBody(), [generatet_Protocol])»)'''
	
	def dispatch CharSequence generatet_ProtocolStatement(AnyAction n) '''AnyAction'''
	
	def dispatch CharSequence generatet_ProtocolStatement(AssertProtocol n) '''(AssertProtocol «_generateO(n.getAssertion(), [generatet_Assert])»)'''
	
	def dispatch CharSequence generatet_ProtocolStatement(ChooseProtocol n) '''(ChooseProtocol «_generateL(n.getBranches(), [generatet_Protocol])»)'''
	
	def dispatch CharSequence generatet_ProtocolStatement(DoExprProtocol n) '''(DoExprProtocol «_generateO(n.getExpression(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_ProtocolStatement(DoneProtocol n) '''DoneProtocol'''
	
	def dispatch CharSequence generatet_ProtocolStatement(ForEachProtocol n) '''(ForEachProtocol «_generateO(n.getVariable(), [generatestring])» «_generateO(n.getSetOfValues(), [generatet_Expression])» «_generateO(n.getRepeated(), [generatet_Protocol])»)'''
	
	def dispatch CharSequence generatet_ProtocolStatement(IfThenElseProtocol n) '''(IfThenElseProtocol «_generateO(n.getCondition(), [generatet_Expression])» «_generateO(n.getIfTrue(), [generatet_Protocol])» «_generateO(n.getIfFalse(), [generatet_Protocol])»)'''
	
	def dispatch CharSequence generatet_ProtocolStatement(ProtocolAction n) '''(ProtocolAction «_generateO(n.getComplexName(), [generatet_ComplexName])» «_generateO(n.getSuite(), [generatet_ProtocolActionSuite])»)'''
	
	def dispatch CharSequence generatet_ProtocolStatement(RepeatProtocol n) '''(RepeatProtocol «_generateO(n.getRepeated(), [generatet_Protocol])»)'''
	
	def dispatch CharSequence generatet_ProtocolStatement(ValuingProtocol n) '''(ValuingProtocol «_generateO(n.getValuing(), [generatet_Valuing])»)'''
	
	def CharSequence generatet_SosADL(SosADL n) '''(SosADL «_generateL(n.getImports(), [generatet_Import])» «_generateO(n.getContent(), [generatet_Unit])»)'''
	
	def CharSequence generatet_SystemDecl(SystemDecl n) '''(SystemDecl «_generateO(n.getName(), [generatestring])» «_generateL(n.getParameters(), [generatet_FormalParameter])» «_generateL(n.getDatatypes(), [generatet_DataTypeDecl])» «_generateL(n.getGates(), [generatet_GateDecl])» «_generateO(n.getBehavior(), [generatet_BehaviorDecl])» «_generateO(n.getAssertion(), [generatet_AssertionDecl])»)'''
	
	def CharSequence generatet_TupleElement(TupleElement n) '''(TupleElement «_generateO(n.getLabel(), [generatestring])» «_generateO(n.getValue(), [generatet_Expression])»)'''
	
	def dispatch CharSequence generatet_Unit(Library n) '''(Library «_generateO(n.getName(), [generatestring])» «_generateO(n.getDecls(), [generatet_EntityBlock])»)'''
	
	def dispatch CharSequence generatet_Unit(SoS n) '''(SoS «_generateO(n.getName(), [generatestring])» «_generateO(n.getDecls(), [generatet_EntityBlock])»)'''
	
	def CharSequence generatet_Valuing(Valuing n) '''(Valuing «_generateO(n.getName(), [generatestring])» «_generateO(n.getType(), [generatet_DataType])» «_generateO(n.getExpression(), [generatet_Expression])»)'''
}
