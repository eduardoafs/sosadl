Require Import List.
Require Import String.
Require Import BinInt.

(**
 * Type of the abstract syntax tree

_This module has been automatically generated_.
 *)

Inductive Quantifier: Set :=
| QuantifierForall: Quantifier
| QuantifierExists: Quantifier.

Inductive Multiplicity: Set :=
| MultiplicityOne: Multiplicity
| MultiplicityNone: Multiplicity
| MultiplicityLone: Multiplicity
| MultiplicityAny: Multiplicity
| MultiplicitySome: Multiplicity
| MultiplicityAll: Multiplicity.

Inductive ModeType: Set :=
| ModeTypeIn: ModeType
| ModeTypeOut: ModeType
| ModeTypeInout: ModeType.

Inductive t_ActionSuite: Set :=
| ReceiveAction: option string ->  t_ActionSuite
| SendAction: option t_Expression ->  t_ActionSuite

with t_ArchBehaviorDecl: Set :=
| ArchBehaviorDecl: option string -> list t_Constituent -> option t_Expression ->  t_ArchBehaviorDecl

with t_ArchitectureDecl: Set :=
| ArchitectureDecl: option string -> list t_FormalParameter -> list t_DataTypeDecl -> list t_GateDecl -> option t_ArchBehaviorDecl -> option t_AssertionDecl ->  t_ArchitectureDecl

with t_Assert: Set :=
| Assert_AskAssertion: option string -> option t_Expression ->  t_Assert
| Assert_TellAssertion: option string -> option t_Expression ->  t_Assert

with t_AssertionDecl: Set :=
| AssertionDecl: option string -> option t_Protocol ->  t_AssertionDecl

with t_Behavior: Set :=
| Behavior: list t_BehaviorStatement ->  t_Behavior

with t_BehaviorDecl: Set :=
| BehaviorDecl: option string -> option t_Behavior ->  t_BehaviorDecl

with t_BehaviorStatement: Set :=
| Action: option t_ComplexName -> option t_ActionSuite ->  t_BehaviorStatement
| BehaviorStatement_AskAssertion: option string -> option t_Expression ->  t_BehaviorStatement
| ChooseBehavior: list t_Behavior ->  t_BehaviorStatement
| BehaviorStatement_DoExpr: option t_Expression ->  t_BehaviorStatement
| BehaviorStatement_Done: t_BehaviorStatement
| ForEachBehavior: option string -> option t_Expression -> option t_Behavior ->  t_BehaviorStatement
| IfThenElseBehavior: option t_Expression -> option t_Behavior -> option t_Behavior ->  t_BehaviorStatement
| RecursiveCall: list t_Expression ->  t_BehaviorStatement
| RepeatBehavior: option t_Behavior ->  t_BehaviorStatement
| BehaviorStatement_TellAssertion: option string -> option t_Expression ->  t_BehaviorStatement
| BehaviorStatement_Valuing: option string -> option t_DataType -> option t_Expression ->  t_BehaviorStatement

with t_Binding: Set :=
| Binding_Quantify: option Quantifier -> list t_ElementInConstituent -> option t_Expression ->  t_Binding
| Binding_Relay: option t_ComplexName -> option t_ComplexName ->  t_Binding
| Binding_Unify: option Multiplicity -> option t_ComplexName -> option Multiplicity -> option t_ComplexName ->  t_Binding

with t_ComplexName: Set :=
| ComplexName: list string ->  t_ComplexName

with t_Connection: Set :=
| Connection: option bool -> option string -> option ModeType -> option t_DataType ->  t_Connection

with t_Constituent: Set :=
| Constituent: option string -> option t_Expression ->  t_Constituent

with t_DataType: Set :=
| BooleanType: t_DataType
| ConnectionType: option ModeType -> option t_DataType ->  t_DataType
| IntegerType: t_DataType
| NamedType: option string ->  t_DataType
| RangeType: option t_Expression -> option t_Expression ->  t_DataType
| SequenceType: option t_DataType ->  t_DataType
| TupleType: list t_FieldDecl ->  t_DataType

with t_DataTypeDecl: Set :=
| DataTypeDecl: option string -> option t_DataType -> list t_FunctionDecl ->  t_DataTypeDecl

with t_DutyDecl: Set :=
| DutyDecl: option string -> list t_Connection -> option t_AssertionDecl -> option t_ProtocolDecl ->  t_DutyDecl

with t_ElementInConstituent: Set :=
| ElementInConstituent: option string -> option string ->  t_ElementInConstituent

with t_EntityBlock: Set :=
| EntityBlock: list t_DataTypeDecl -> list t_FunctionDecl -> list t_SystemDecl -> list t_MediatorDecl -> list t_ArchitectureDecl ->  t_EntityBlock

with t_Expression: Set :=
| Any: t_Expression
| BinaryExpression: option t_Expression -> option string -> option t_Expression ->  t_Expression
| CallExpression: option string -> list t_Expression ->  t_Expression
| Field: option t_Expression -> option string ->  t_Expression
| IdentExpression: option string ->  t_Expression
| IntegerValue: option Z ->  t_Expression
| Map: option t_Expression -> option string -> option t_Expression ->  t_Expression
| MethodCall: option t_Expression -> option string -> list t_Expression ->  t_Expression
| Expression_Quantify: option Quantifier -> list t_ElementInConstituent -> option t_Expression ->  t_Expression
| Expression_Relay: option t_ComplexName -> option t_ComplexName ->  t_Expression
| Select: option t_Expression -> option string -> option t_Expression ->  t_Expression
| Sequence: list t_Expression ->  t_Expression
| Tuple: list t_TupleElement ->  t_Expression
| UnaryExpression: option string -> option t_Expression ->  t_Expression
| Expression_Unify: option Multiplicity -> option t_ComplexName -> option Multiplicity -> option t_ComplexName ->  t_Expression
| UnobservableValue: t_Expression

with t_FieldDecl: Set :=
| FieldDecl: option string -> option t_DataType ->  t_FieldDecl

with t_FormalParameter: Set :=
| FormalParameter: option string -> option t_DataType ->  t_FormalParameter

with t_FunctionDecl: Set :=
| FunctionDecl: option t_FormalParameter -> option string -> list t_FormalParameter -> option t_DataType -> list t_Valuing -> option t_Expression ->  t_FunctionDecl

with t_GateDecl: Set :=
| GateDecl: option string -> list t_Connection -> option t_ProtocolDecl ->  t_GateDecl

with t_Import: Set :=
| Import: option string ->  t_Import

with t_MediatorDecl: Set :=
| MediatorDecl: option string -> list t_FormalParameter -> list t_DataTypeDecl -> list t_DutyDecl -> option t_BehaviorDecl -> option t_AssertionDecl -> option t_AssertionDecl ->  t_MediatorDecl

with t_Protocol: Set :=
| Protocol: list t_ProtocolStatement ->  t_Protocol

with t_ProtocolActionSuite: Set :=
| ReceiveAnyProtocolAction: t_ProtocolActionSuite
| ReceiveProtocolAction: option string ->  t_ProtocolActionSuite
| SendProtocolAction: option t_Expression ->  t_ProtocolActionSuite

with t_ProtocolDecl: Set :=
| ProtocolDecl: option string -> option t_Protocol ->  t_ProtocolDecl

with t_ProtocolStatement: Set :=
| AnyAction: t_ProtocolStatement
| ProtocolStatement_AskAssertion: option string -> option t_Expression ->  t_ProtocolStatement
| ChooseProtocol: list t_Protocol ->  t_ProtocolStatement
| ProtocolStatement_DoExpr: option t_Expression ->  t_ProtocolStatement
| ProtocolStatement_Done: t_ProtocolStatement
| ForEachProtocol: option string -> option t_Expression -> option t_Protocol ->  t_ProtocolStatement
| IfThenElseProtocol: option t_Expression -> option t_Protocol -> option t_Protocol ->  t_ProtocolStatement
| ProtocolAction: option t_ComplexName -> option t_ProtocolActionSuite ->  t_ProtocolStatement
| RepeatProtocol: option t_Protocol ->  t_ProtocolStatement
| ProtocolStatement_TellAssertion: option string -> option t_Expression ->  t_ProtocolStatement
| ProtocolStatement_Valuing: option string -> option t_DataType -> option t_Expression ->  t_ProtocolStatement

with t_SosADL: Set :=
| SosADL: list t_Import -> option t_Unit ->  t_SosADL

with t_SystemDecl: Set :=
| SystemDecl: option string -> list t_FormalParameter -> list t_DataTypeDecl -> list t_GateDecl -> option t_BehaviorDecl -> option t_AssertionDecl ->  t_SystemDecl

with t_TupleElement: Set :=
| TupleElement: option string -> option t_Expression ->  t_TupleElement

with t_Unit: Set :=
| Library: option string -> option t_EntityBlock ->  t_Unit
| SoS: option string -> option t_EntityBlock ->  t_Unit

with t_Valuing: Set :=
| Valuing_Valuing: option string -> option t_DataType -> option t_Expression ->  t_Valuing
.

Definition ArchBehaviorDecl_name x :=
	match x with
	| ArchBehaviorDecl y _ _ => y
	end.

Definition ArchBehaviorDecl_constituents x :=
	match x with
	| ArchBehaviorDecl _ y _ => y
	end.

Definition ArchBehaviorDecl_bindings x :=
	match x with
	| ArchBehaviorDecl _ _ y => y
	end.

Definition ArchitectureDecl_name x :=
	match x with
	| ArchitectureDecl y _ _ _ _ _ => y
	end.

Definition ArchitectureDecl_parameters x :=
	match x with
	| ArchitectureDecl _ y _ _ _ _ => y
	end.

Definition ArchitectureDecl_datatypes x :=
	match x with
	| ArchitectureDecl _ _ y _ _ _ => y
	end.

Definition ArchitectureDecl_gates x :=
	match x with
	| ArchitectureDecl _ _ _ y _ _ => y
	end.

Definition ArchitectureDecl_behavior x :=
	match x with
	| ArchitectureDecl _ _ _ _ y _ => y
	end.

Definition ArchitectureDecl_assertion x :=
	match x with
	| ArchitectureDecl _ _ _ _ _ y => y
	end.

Definition AssertionDecl_name x :=
	match x with
	| AssertionDecl y _ => y
	end.

Definition AssertionDecl_body x :=
	match x with
	| AssertionDecl _ y => y
	end.

Definition Behavior_statements x :=
	match x with
	| Behavior y => y
	end.

Definition BehaviorDecl_name x :=
	match x with
	| BehaviorDecl y _ => y
	end.

Definition BehaviorDecl_body x :=
	match x with
	| BehaviorDecl _ y => y
	end.

Definition ComplexName_name x :=
	match x with
	| ComplexName y => y
	end.

Definition Connection_environment x :=
	match x with
	| Connection y _ _ _ => y
	end.

Definition Connection_name x :=
	match x with
	| Connection _ y _ _ => y
	end.

Definition Connection_mode x :=
	match x with
	| Connection _ _ y _ => y
	end.

Definition Connection_valueType x :=
	match x with
	| Connection _ _ _ y => y
	end.

Definition Constituent_name x :=
	match x with
	| Constituent y _ => y
	end.

Definition Constituent_value x :=
	match x with
	| Constituent _ y => y
	end.

Definition DataTypeDecl_name x :=
	match x with
	| DataTypeDecl y _ _ => y
	end.

Definition DataTypeDecl_datatype x :=
	match x with
	| DataTypeDecl _ y _ => y
	end.

Definition DataTypeDecl_functions x :=
	match x with
	| DataTypeDecl _ _ y => y
	end.

Definition DutyDecl_name x :=
	match x with
	| DutyDecl y _ _ _ => y
	end.

Definition DutyDecl_connections x :=
	match x with
	| DutyDecl _ y _ _ => y
	end.

Definition DutyDecl_assertion x :=
	match x with
	| DutyDecl _ _ y _ => y
	end.

Definition DutyDecl_protocol x :=
	match x with
	| DutyDecl _ _ _ y => y
	end.

Definition ElementInConstituent_variable x :=
	match x with
	| ElementInConstituent y _ => y
	end.

Definition ElementInConstituent_constituent x :=
	match x with
	| ElementInConstituent _ y => y
	end.

Definition EntityBlock_datatypes x :=
	match x with
	| EntityBlock y _ _ _ _ => y
	end.

Definition EntityBlock_functions x :=
	match x with
	| EntityBlock _ y _ _ _ => y
	end.

Definition EntityBlock_systems x :=
	match x with
	| EntityBlock _ _ y _ _ => y
	end.

Definition EntityBlock_mediators x :=
	match x with
	| EntityBlock _ _ _ y _ => y
	end.

Definition EntityBlock_architectures x :=
	match x with
	| EntityBlock _ _ _ _ y => y
	end.

Definition FieldDecl_name x :=
	match x with
	| FieldDecl y _ => y
	end.

Definition FieldDecl_type x :=
	match x with
	| FieldDecl _ y => y
	end.

Definition FormalParameter_name x :=
	match x with
	| FormalParameter y _ => y
	end.

Definition FormalParameter_type x :=
	match x with
	| FormalParameter _ y => y
	end.

Definition FunctionDecl_data x :=
	match x with
	| FunctionDecl y _ _ _ _ _ => y
	end.

Definition FunctionDecl_name x :=
	match x with
	| FunctionDecl _ y _ _ _ _ => y
	end.

Definition FunctionDecl_parameters x :=
	match x with
	| FunctionDecl _ _ y _ _ _ => y
	end.

Definition FunctionDecl_type x :=
	match x with
	| FunctionDecl _ _ _ y _ _ => y
	end.

Definition FunctionDecl_valuing x :=
	match x with
	| FunctionDecl _ _ _ _ y _ => y
	end.

Definition FunctionDecl_expression x :=
	match x with
	| FunctionDecl _ _ _ _ _ y => y
	end.

Definition GateDecl_name x :=
	match x with
	| GateDecl y _ _ => y
	end.

Definition GateDecl_connections x :=
	match x with
	| GateDecl _ y _ => y
	end.

Definition GateDecl_protocol x :=
	match x with
	| GateDecl _ _ y => y
	end.

Definition Import_importedLibrary x :=
	match x with
	| Import y => y
	end.

Definition MediatorDecl_name x :=
	match x with
	| MediatorDecl y _ _ _ _ _ _ => y
	end.

Definition MediatorDecl_parameters x :=
	match x with
	| MediatorDecl _ y _ _ _ _ _ => y
	end.

Definition MediatorDecl_datatypes x :=
	match x with
	| MediatorDecl _ _ y _ _ _ _ => y
	end.

Definition MediatorDecl_duties x :=
	match x with
	| MediatorDecl _ _ _ y _ _ _ => y
	end.

Definition MediatorDecl_behavior x :=
	match x with
	| MediatorDecl _ _ _ _ y _ _ => y
	end.

Definition MediatorDecl_assumption x :=
	match x with
	| MediatorDecl _ _ _ _ _ y _ => y
	end.

Definition MediatorDecl_assertion x :=
	match x with
	| MediatorDecl _ _ _ _ _ _ y => y
	end.

Definition Protocol_statements x :=
	match x with
	| Protocol y => y
	end.

Definition ProtocolDecl_name x :=
	match x with
	| ProtocolDecl y _ => y
	end.

Definition ProtocolDecl_body x :=
	match x with
	| ProtocolDecl _ y => y
	end.

Definition SosADL_imports x :=
	match x with
	| SosADL y _ => y
	end.

Definition SosADL_content x :=
	match x with
	| SosADL _ y => y
	end.

Definition SystemDecl_name x :=
	match x with
	| SystemDecl y _ _ _ _ _ => y
	end.

Definition SystemDecl_parameters x :=
	match x with
	| SystemDecl _ y _ _ _ _ => y
	end.

Definition SystemDecl_datatypes x :=
	match x with
	| SystemDecl _ _ y _ _ _ => y
	end.

Definition SystemDecl_gates x :=
	match x with
	| SystemDecl _ _ _ y _ _ => y
	end.

Definition SystemDecl_behavior x :=
	match x with
	| SystemDecl _ _ _ _ y _ => y
	end.

Definition SystemDecl_assertion x :=
	match x with
	| SystemDecl _ _ _ _ _ y => y
	end.

Definition TupleElement_label x :=
	match x with
	| TupleElement y _ => y
	end.

Definition TupleElement_value x :=
	match x with
	| TupleElement _ y => y
	end.

Definition Valuing_Valuing_variable x :=
	match x with
	| Valuing_Valuing y _ _ => y
	end.

Definition Valuing_Valuing_type x :=
	match x with
	| Valuing_Valuing _ y _ => y
	end.

Definition Valuing_Valuing_expression x :=
	match x with
	| Valuing_Valuing _ _ y => y
	end.

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
