Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testValuing6") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") None [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeOut) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ProtocolStatement_Valuing (Some "data1") (Some IntegerType) (Some (IntegerValue (Some 1)))); (ProtocolAction (Some (ComplexName ["gate1"; "connection1"])) (Some ReceiveAnyProtocolAction)); (ProtocolStatement_Valuing (Some "data2") (Some IntegerType) (Some (IntegerValue (Some 2)))); (ProtocolStatement_Valuing (Some "data3") (Some IntegerType) (Some (IntegerValue (Some 3))))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(BehaviorStatement_Valuing (Some "data1") (Some IntegerType) (Some (IntegerValue (Some 1)))); (Action (Some (ComplexName ["gate1"; "connection1"])) (Some (ReceiveAction (Some "data")))); (BehaviorStatement_Valuing (Some "data2") (Some IntegerType) (Some (IntegerValue (Some 2)))); (BehaviorStatement_Valuing (Some "data3") (Some IntegerType) (Some (IntegerValue (Some 3))))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
