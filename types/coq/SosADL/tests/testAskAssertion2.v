Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testAskAssertion2") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") None [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeIn) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ProtocolStatement_Valuing (Some "a1") (Some (NamedType (Some "type1"))) (Some (IntegerValue (Some 1)))); (ProtocolStatement_AskAssertion (Some "something1") (Some (BinaryExpression (Some (IdentExpression (Some "a1"))) (Some "=") (Some (IdentExpression (Some "b1")))))); (ProtocolAction (Some (ComplexName ["gate1"; "connection1"])) (Some (SendProtocolAction (Some (IdentExpression (Some "a1")))))); (ProtocolAction (Some (ComplexName ["gate1"; "connection1"])) (Some (ReceiveProtocolAction (Some "b1"))))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(BehaviorStatement_Valuing (Some "a1") (Some (NamedType (Some "type1"))) (Some (IntegerValue (Some 1)))); (BehaviorStatement_AskAssertion (Some "something1") (Some (BinaryExpression (Some (IdentExpression (Some "a1"))) (Some "=") (Some (IdentExpression (Some "b1")))))); (Action (Some (ComplexName ["gate1"; "connection1"])) (Some (SendAction (Some (IdentExpression (Some "a1")))))); (Action (Some (ComplexName ["gate1"; "connection1"])) (Some (ReceiveAction (Some "b1"))))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
