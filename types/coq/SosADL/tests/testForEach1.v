Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testForEach1") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") None [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeIn) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ProtocolStatement_Valuing (Some "s") (Some (SequenceType (Some IntegerType))) (Some (Expression_Sequence [(IntegerValue (Some 1)); (IntegerValue (Some 2)); (IntegerValue (Some 3)); (IntegerValue (Some 4))]))); (ForEachProtocol (Some "e") (Some (IdentExpression (Some "s"))) (Some (Protocol [(ProtocolAction (Some (ComplexName ["gate1"; "connection1"])) (Some (SendProtocolAction (Some (IdentExpression (Some "e"))))))])))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(BehaviorStatement_Valuing (Some "s") (Some (SequenceType (Some IntegerType))) (Some (Expression_Sequence [(IntegerValue (Some 1)); (IntegerValue (Some 2)); (IntegerValue (Some 3)); (IntegerValue (Some 4))]))); (ForEachBehavior (Some "e") (Some (IdentExpression (Some "s"))) (Some (Behavior [(Action (Some (ComplexName ["gate1"; "connection1"])) (Some (SendAction (Some (IdentExpression (Some "e"))))))])))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
