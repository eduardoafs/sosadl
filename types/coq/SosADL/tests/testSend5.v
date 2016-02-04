Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testSend5") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [(FormalParameter (Some "arg") (Some IntegerType))] [(DataTypeDecl (Some "type1") None [(FunctionDecl (Some (FormalParameter (Some "data") (Some (NamedType (Some "type1"))))) (Some "add") [(FormalParameter (Some "x") (Some (NamedType (Some "type1"))))] (Some (NamedType (Some "type1"))) [] (Some (BinaryExpression (Some (IdentExpression (Some "data"))) (Some "+") (Some (IdentExpression (Some "x"))))))])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeOut) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ProtocolStatement_Valuing (Some "data") (Some (NamedType (Some "type1"))) (Some (IntegerValue (Some 0)))); (ProtocolAction (Some (ComplexName ["gate1"; "connection1"])) (Some (SendProtocolAction (Some Any))))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(BehaviorStatement_Valuing (Some "data") (Some (NamedType (Some "type1"))) (Some (IntegerValue (Some 1)))); (Action (Some (ComplexName ["gate1"; "connection1"])) (Some (SendAction (Some (MethodCall (Some (IdentExpression (Some "data"))) (Some "add") [(IntegerValue (Some 1))])))))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
