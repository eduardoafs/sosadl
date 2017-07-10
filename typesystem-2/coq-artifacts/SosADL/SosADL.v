Require Import List.
Require Import String.
Require Import BinInt.
Require Import SosADL.sosADL.

(**
 * Glue with the types of the abstract syntax tree

Since the Ecore2Coq transformation has evolved, the generated interface has changed: generated names are different; and parameters may have been reordered. This module bridges between previous work based on the older generated abstract syntax and the newest one.

The newest name schemes and parameter ordering is expected to be more stable.
 *)

Definition Quantifier := sosADL_Quantifier.
Definition QuantifierExists := sosADL_Quantifier_QuantifierExists.
Definition QuantifierForall := sosADL_Quantifier_QuantifierForall.

Definition Multiplicity := sosADL_Multiplicity.
Definition MultiplicityAll := sosADL_Multiplicity_MultiplicityAll.
Definition MultiplicityAny := sosADL_Multiplicity_MultiplicityAny.
Definition MultiplicityLone := sosADL_Multiplicity_MultiplicityLone.
Definition MultiplicityNone := sosADL_Multiplicity_MultiplicityNone.
Definition MultiplicityOne := sosADL_Multiplicity_MultiplicityOne.
Definition MultiplicitySome := sosADL_Multiplicity_MultiplicitySome.

Definition ModeType := sosADL_ModeType.
Definition ModeTypeIn := sosADL_ModeType_ModeTypeIn.
Definition ModeTypeInout := sosADL_ModeType_ModeTypeInout.
Definition ModeTypeOut := sosADL_ModeType_ModeTypeOut.

Definition t_ActionSuite := sosADL_ActionSuite.
Definition ReceiveAction := sosADL_ActionSuite_sosADL_ReceiveAction.
Definition SendAction := sosADL_ActionSuite_sosADL_SendAction.

Definition t_ArchBehaviorDecl := sosADL_ArchBehaviorDecl.
Definition ArchBehaviorDecl name constituents bindings := sosADL_ArchBehaviorDecl_sosADL_ArchBehaviorDecl bindings constituents name.

Definition t_ArchitectureDecl := sosADL_ArchitectureDecl.
Definition ArchitectureDecl name parameters datatypes gates behavior assertions := sosADL_ArchitectureDecl_sosADL_ArchitectureDecl assertions behavior datatypes gates name parameters.

Definition t_Assert := sosADL_Assert.
Definition AskAssertion name expression := sosADL_Assert_sosADL_AskAssertion expression name.
Definition TellAssertion name expression := sosADL_Assert_sosADL_TellAssertion expression name.
Definition UntellAssertion := sosADL_Assert_sosADL_UntellAssertion.

Definition t_AssertionDecl := sosADL_AssertionDecl.
Definition AssertionDecl name body := sosADL_AssertionDecl_sosADL_AssertionDecl body name.

Definition t_Behavior := sosADL_Behavior.
Definition Behavior := sosADL_Behavior_sosADL_Behavior.

Definition t_BehaviorDecl := sosADL_BehaviorDecl.
Definition BehaviorDecl name body := sosADL_BehaviorDecl_sosADL_BehaviorDecl body name.

Definition t_BehaviorStatement := sosADL_BehaviorStatement.
Definition Action := sosADL_BehaviorStatement_sosADL_Action.
Definition AssertBehavior := sosADL_BehaviorStatement_sosADL_AssertBehavior.
Definition ChooseBehavior := sosADL_BehaviorStatement_sosADL_ChooseBehavior.
Definition DoExprBehavior := sosADL_BehaviorStatement_sosADL_DoExprBehavior.
Definition DoneBehavior := sosADL_BehaviorStatement_sosADL_DoneBehavior.
Definition ForEachBehavior variable setOfValues repeated := sosADL_BehaviorStatement_sosADL_ForEachBehavior repeated setOfValues variable.
Definition IfThenElseBehavior condition ifTrue ifFalse := sosADL_BehaviorStatement_sosADL_IfThenElseBehavior condition ifFalse ifTrue.
Definition RecursiveCall := sosADL_BehaviorStatement_sosADL_RecursiveCall.
Definition RepeatBehavior := sosADL_BehaviorStatement_sosADL_RepeatBehavior.
Definition UnobservableBehavior := sosADL_BehaviorStatement_sosADL_UnobservableBehavior.
Definition ValuingBehavior := sosADL_BehaviorStatement_sosADL_ValuingBehavior.

Definition t_ComplexName := sosADL_ComplexName.
Definition ComplexName := sosADL_ComplexName_sosADL_ComplexName.

Definition t_Connection := sosADL_Connection.
Definition Connection environment name mode valueType := sosADL_Connection_sosADL_Connection environment mode name valueType.

Definition t_Constituent := sosADL_Constituent.
Definition Constituent := sosADL_Constituent_sosADL_Constituent.

Definition t_DataType := sosADL_DataType.
Definition BooleanType := sosADL_DataType_sosADL_BooleanType.
Definition ConnectionType := sosADL_DataType_sosADL_ConnectionType.
Definition IntegerType := sosADL_DataType_sosADL_IntegerType.
Definition NamedType :=  sosADL_DataType_sosADL_NamedType.
Definition RangeType vmin vmax := sosADL_DataType_sosADL_RangeType vmax vmin.
Definition SequenceType := sosADL_DataType_sosADL_SequenceType.
Definition TupleType := sosADL_DataType_sosADL_TupleType.

Definition t_DataTypeDecl := sosADL_DataTypeDecl.
Definition DataTypeDecl name datatype functions := sosADL_DataTypeDecl_sosADL_DataTypeDecl datatype functions name.

Definition t_DutyDecl := sosADL_DutyDecl.
Definition DutyDecl name connections assertions protocols := sosADL_DutyDecl_sosADL_DutyDecl assertions connections name protocols.

Definition t_ElementInConstituent := sosADL_ElementInConstituent.
Definition ElementInConstituent variable constituent := sosADL_ElementInConstituent_sosADL_ElementInConstituent constituent variable.

Definition t_EntityBlock := sosADL_EntityBlock.
Definition EntityBlock datatypes functions systems mediators architectures := sosADL_EntityBlock_sosADL_EntityBlock architectures datatypes functions mediators systems.

Definition t_Expression := sosADL_Expression.
Definition Any := sosADL_Expression_sosADL_Any.
Definition BinaryExpression := sosADL_Expression_sosADL_BinaryExpression.
Definition CallExpression := sosADL_Expression_sosADL_CallExpression.
Definition Field object field := sosADL_Expression_sosADL_Field field object.
Definition IdentExpression := sosADL_Expression_sosADL_IdentExpression.
Definition IntegerValue := sosADL_Expression_sosADL_IntegerValue.
Definition Map object variable expression := sosADL_Expression_sosADL_Map expression object variable.
Definition MethodCall object method parameters := sosADL_Expression_sosADL_MethodCall method object parameters.
Definition Quantify quantifier elements bindings := sosADL_Expression_sosADL_Quantify bindings elements quantifier.
Definition Relay := sosADL_Expression_sosADL_Relay.
Definition Select object variable condition := sosADL_Expression_sosADL_Select condition object variable.
Definition Sequence := sosADL_Expression_sosADL_Sequence.
Definition Tuple := sosADL_Expression_sosADL_Tuple.
Definition UnaryExpression := sosADL_Expression_sosADL_UnaryExpression.
Definition Unify multLeft connLeft multRight connRight := sosADL_Expression_sosADL_Unify connLeft connRight multLeft multRight.

Definition t_FieldDecl := sosADL_FieldDecl.
Definition FieldDecl := sosADL_FieldDecl_sosADL_FieldDecl.

Definition t_FormalParameter := sosADL_FormalParameter.
Definition FormalParameter := sosADL_FormalParameter_sosADL_FormalParameter.

Definition t_FunctionDecl := sosADL_FunctionDecl.
Definition FunctionDecl data name  parameters type valuing expression := sosADL_FunctionDecl_sosADL_FunctionDecl data expression name parameters type valuing.

Definition t_GateDecl := sosADL_GateDecl.
Definition GateDecl name connections protocols := sosADL_GateDecl_sosADL_GateDecl connections name protocols.

Definition t_Import := sosADL_Import.
Definition Import := sosADL_Import_sosADL_Import.

Definition t_MediatorDecl := sosADL_MediatorDecl.
Definition MediatorDecl name parameters datatypes duties behavior assumptions assertions := sosADL_MediatorDecl_sosADL_MediatorDecl assertions assumptions behavior datatypes duties name parameters.

Definition t_Protocol := sosADL_Protocol.
Definition Protocol := sosADL_Protocol_sosADL_Protocol.

Definition t_ProtocolActionSuite := sosADL_ProtocolActionSuite.
Definition ReceiveAnyProtocolAction := sosADL_ProtocolActionSuite_sosADL_ReceiveAnyProtocolAction.
Definition ReceiveProtocolAction := sosADL_ProtocolActionSuite_sosADL_ReceiveProtocolAction.
Definition SendProtocolAction := sosADL_ProtocolActionSuite_sosADL_SendProtocolAction.

Definition t_ProtocolDecl := sosADL_ProtocolDecl.
Definition ProtocolDecl name body := sosADL_ProtocolDecl_sosADL_ProtocolDecl body name.

Definition t_ProtocolStatement := sosADL_ProtocolStatement.
Definition AnyAction := sosADL_ProtocolStatement_sosADL_AnyAction.
Definition AssertProtocol := sosADL_ProtocolStatement_sosADL_AssertProtocol.
Definition ChooseProtocol := sosADL_ProtocolStatement_sosADL_ChooseProtocol.
Definition DoExprProtocol := sosADL_ProtocolStatement_sosADL_DoExprProtocol.
Definition DoneProtocol := sosADL_ProtocolStatement_sosADL_DoneProtocol.
Definition ForEachProtocol variable setOfValues repeated := sosADL_ProtocolStatement_sosADL_ForEachProtocol repeated setOfValues variable.
Definition IfThenElseProtocol condition ifTrue ifFalse := sosADL_ProtocolStatement_sosADL_IfThenElseProtocol condition ifFalse ifTrue.
Definition ProtocolAction := sosADL_ProtocolStatement_sosADL_ProtocolAction.
Definition RepeatProtocol := sosADL_ProtocolStatement_sosADL_RepeatProtocol.
Definition ValuingProtocol := sosADL_ProtocolStatement_sosADL_ValuingProtocol.

Definition t_SosADL := sosADL_SosADL.
Definition SosADL imports content := sosADL_SosADL_sosADL_SosADL content imports.

Definition  t_SystemDecl := sosADL_SystemDecl.
Definition SystemDecl name parameters datatypes gates behavior assertions := sosADL_SystemDecl_sosADL_SystemDecl assertions behavior datatypes gates name parameters.

Definition t_TupleElement := sosADL_TupleElement.
Definition TupleElement := sosADL_TupleElement_sosADL_TupleElement.

Definition t_Unit := sosADL_Unit.
Definition Library name decls := sosADL_Unit_sosADL_Library decls name.
Definition SoS name decls := sosADL_Unit_sosADL_SoS decls name.

Definition t_Valuing := sosADL_Valuing.
Definition Valuing name type expression := sosADL_Valuing_sosADL_Valuing expression name type.



(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
