Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testChoose5") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") None [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeInout) (Some (NamedType (Some "type1")))); (Connection (Some false) (Some "connection2") (Some ModeTypeInout) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ProtocolStatement_Valuing (Some "data") None (Some (IntegerValue (Some 0)))); (ChooseProtocol [(Protocol [(ProtocolStatement_Valuing (Some "data11") None (Some (IntegerValue (Some 1)))); (ProtocolAction (Some (ComplexName ["gate1"; "connection1"])) (Some ReceiveAnyProtocolAction))]); (Protocol [(ProtocolStatement_Valuing (Some "data12") None (Some (IntegerValue (Some 2)))); (ProtocolAction (Some (ComplexName ["gate1"; "connection1"])) (Some (SendProtocolAction (Some Any))))])]); (ProtocolAction (Some (ComplexName ["gate1"; "connection2"])) (Some (SendProtocolAction (Some Any))))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(BehaviorStatement_Valuing (Some "data") None (Some (IntegerValue (Some 0)))); (ChooseBehavior [(Behavior [(BehaviorStatement_Valuing (Some "data11") None (Some (IntegerValue (Some 1)))); (Action (Some (ComplexName ["gate1"; "connection1"])) (Some (ReceiveAction (Some "data"))))]); (Behavior [(BehaviorStatement_Valuing (Some "data12") None (Some (IntegerValue (Some 2)))); (Action (Some (ComplexName ["gate1"; "connection1"])) (Some (SendAction (Some (IntegerValue (Some 1))))))])]); (Action (Some (ComplexName ["gate1"; "connection2"])) (Some (SendAction (Some (IntegerValue (Some 2))))))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)