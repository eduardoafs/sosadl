Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testIfThenElse1") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") None [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeIn) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(IfThenElseProtocol (Some (BinaryExpression (Some (IntegerValue (Some 1))) (Some "=") (Some (IntegerValue (Some 1))))) (Some (Protocol [ProtocolStatement_Done])) (Some (Protocol [ProtocolStatement_Done])))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(IfThenElseBehavior (Some (BinaryExpression (Some (IntegerValue (Some 1))) (Some "=") (Some (IntegerValue (Some 1))))) (Some (Behavior [BehaviorStatement_Done])) (Some (Behavior [BehaviorStatement_Done])))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
