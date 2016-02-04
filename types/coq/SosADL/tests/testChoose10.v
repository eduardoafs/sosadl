Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testChoose10") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") None [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeInout) (Some (NamedType (Some "type1")))); (Connection (Some false) (Some "connection2") (Some ModeTypeInout) (Some (NamedType (Some "type1")))); (Connection (Some false) (Some "connection3") (Some ModeTypeInout) (Some (NamedType (Some "type1")))); (Connection (Some false) (Some "connection4") (Some ModeTypeInout) (Some (NamedType (Some "type1")))); (Connection (Some false) (Some "connection5") (Some ModeTypeInout) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ChooseProtocol [(Protocol [(ProtocolAction (Some (ComplexName ["gate1"; "connection1"])) (Some ReceiveAnyProtocolAction))]); (Protocol [(ProtocolStatement_Valuing (Some "data") None (Some (IntegerValue (Some 0)))); (ChooseProtocol [(Protocol [(ProtocolAction (Some (ComplexName ["gate1"; "connection2"])) (Some ReceiveAnyProtocolAction))]); (Protocol [(ProtocolAction (Some (ComplexName ["gate1"; "connection3"])) (Some (SendProtocolAction (Some Any))))])])]); (Protocol [(ProtocolAction (Some (ComplexName ["gate1"; "connection4"])) (Some (SendProtocolAction (Some Any))))])])])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(ChooseBehavior [(Behavior [(Action (Some (ComplexName ["gate1"; "connection1"])) (Some (ReceiveAction (Some "data1"))))]); (Behavior [(BehaviorStatement_Valuing (Some "data") None (Some (IntegerValue (Some 0)))); (ChooseBehavior [(Behavior [(Action (Some (ComplexName ["gate1"; "connection2"])) (Some (ReceiveAction (Some "data2"))))]); (Behavior [(Action (Some (ComplexName ["gate1"; "connection3"])) (Some (SendAction (Some (IntegerValue (Some 3))))))])])]); (Behavior [(Action (Some (ComplexName ["gate1"; "connection4"])) (Some (SendAction (Some (IntegerValue (Some 4))))))])])])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
