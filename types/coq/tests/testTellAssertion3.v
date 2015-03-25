Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testAskAssertion1") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") None [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeIn) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ProtocolStatement_Valuing (Some "a1") (Some (NamedType (Some "type1"))) (Some (IntegerValue (Some 1)))); (ProtocolStatement_TellAssertion (Some "something1") (Some (BinaryExpression (Some (IdentExpression (Some "b1"))) (Some "=") (Some (IdentExpression (Some "a1"))))))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(BehaviorStatement_Valuing (Some "a1") (Some (NamedType (Some "type1"))) (Some (IntegerValue (Some 1)))); (BehaviorStatement_TellAssertion (Some "something1") (Some (BinaryExpression (Some (IdentExpression (Some "b1"))) (Some "=") (Some (IdentExpression (Some "a1"))))))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
