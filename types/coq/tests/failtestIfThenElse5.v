Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testIfThenElse5") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") None [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeIn) (Some (NamedType (Some "type1")))); (Connection (Some false) (Some "connection2") (Some ModeTypeIn) (Some (NamedType (Some "type1")))); (Connection (Some false) (Some "connection3") (Some ModeTypeIn) (Some (NamedType (Some "type1")))); (Connection (Some false) (Some "connection4") (Some ModeTypeIn) (Some (NamedType (Some "type1")))); (Connection (Some false) (Some "connection5") (Some ModeTypeIn) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(IfThenElseProtocol (Some (BinaryExpression (Some (IntegerValue (Some 0))) (Some ">") (Some (IntegerValue (Some 1))))) (Some (Protocol [(IfThenElseProtocol (Some (BinaryExpression (Some (IntegerValue (Some 1))) (Some "<") (Some (IntegerValue (Some 2))))) (Some (Protocol [(ProtocolAction (Some (ComplexName ["gate1"; "connection1"])) (Some (SendProtocolAction (Some Any))))])) (Some (Protocol [(ProtocolAction (Some (ComplexName ["gate1"; "connection2"])) (Some (SendProtocolAction (Some Any))))])))])) (Some (Protocol [(IfThenElseProtocol (Some (BinaryExpression (Some (IntegerValue (Some 1))) (Some ">") (Some (IntegerValue (Some 2))))) (Some (Protocol [(ProtocolAction (Some (ComplexName ["gate1"; "connection3"])) (Some ReceiveAnyProtocolAction))])) (Some (Protocol [(ProtocolAction (Some (ComplexName ["gate1"; "connection4"])) (Some ReceiveAnyProtocolAction))])))]))); (ProtocolAction (Some (ComplexName ["gate1"; "connection5"])) (Some (SendProtocolAction (Some Any))))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(IfThenElseBehavior (Some (BinaryExpression (Some (IntegerValue (Some 0))) (Some ">") (Some (IntegerValue (Some 1))))) (Some (Behavior [(IfThenElseBehavior (Some (BinaryExpression (Some (IntegerValue (Some 1))) (Some "<") (Some (IntegerValue (Some 2))))) (Some (Behavior [(Action (Some (ComplexName ["gate1"; "connection1"])) (Some (SendAction (Some (IntegerValue (Some 1))))))])) (Some (Behavior [(Action (Some (ComplexName ["gate1"; "connection2"])) (Some (SendAction (Some (IntegerValue (Some 2))))))])))])) (Some (Behavior [(IfThenElseBehavior (Some (BinaryExpression (Some (IntegerValue (Some 1))) (Some ">") (Some (IntegerValue (Some 2))))) (Some (Behavior [(Action (Some (ComplexName ["gate1"; "connection3"])) (Some (ReceiveAction (Some "data3"))))])) (Some (Behavior [(Action (Some (ComplexName ["gate1"; "connection4"])) (Some (ReceiveAction (Some "data4"))))])))]))); (Action (Some (ComplexName ["gate1"; "connection5"])) (Some (SendAction (Some (IntegerValue (Some 5))))))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
