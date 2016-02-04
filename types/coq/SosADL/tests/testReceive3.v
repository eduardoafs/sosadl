Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testReceive3") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") None [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeIn) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ProtocolStatement_Valuing (Some "data") (Some IntegerType) (Some (IntegerValue (Some 0)))); (ProtocolAction (Some (ComplexName ["gate1"; "connection1"])) (Some ReceiveAnyProtocolAction))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(BehaviorStatement_Valuing (Some "data") (Some IntegerType) (Some (IntegerValue (Some 0)))); (Action (Some (ComplexName ["gate1"; "connection1"])) (Some (ReceiveAction (Some "data"))))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
