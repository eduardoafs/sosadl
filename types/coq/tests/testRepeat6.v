Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testRepeat6") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") None [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeInout) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ProtocolStatement_Valuing (Some "data") None (Some (IntegerValue (Some 0)))); (RepeatProtocol (Some (Protocol [(IfThenElseProtocol (Some (BinaryExpression (Some (IntegerValue (Some 1))) (Some "=") (Some (IntegerValue (Some 1))))) (Some (Protocol [(ProtocolAction (Some (ComplexName ["gate1"; "connection1"])) (Some ReceiveAnyProtocolAction))])) (Some (Protocol [(ProtocolAction (Some (ComplexName ["gate1"; "connection1"])) (Some (SendProtocolAction (Some Any))))])))])))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(BehaviorStatement_Valuing (Some "data") None (Some (IntegerValue (Some 0)))); (RepeatBehavior (Some (Behavior [(IfThenElseBehavior (Some (BinaryExpression (Some (IntegerValue (Some 1))) (Some "=") (Some (IntegerValue (Some 1))))) (Some (Behavior [(Action (Some (ComplexName ["gate1"; "connection1"])) (Some (ReceiveAction (Some "data"))))])) (Some (Behavior [(Action (Some (ComplexName ["gate1"; "connection1"])) (Some (SendAction (Some (IntegerValue (Some 1))))))])))])))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)