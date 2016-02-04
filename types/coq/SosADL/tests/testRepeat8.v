Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testRepeat8") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") None [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeInout) (Some (NamedType (Some "type1")))); (Connection (Some false) (Some "connection2") (Some ModeTypeInout) (Some (NamedType (Some "type1")))); (Connection (Some false) (Some "connection3") (Some ModeTypeInout) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ProtocolStatement_Valuing (Some "data1") None (Some (IntegerValue (Some 1)))); (ProtocolStatement_Valuing (Some "data2") None (Some (IntegerValue (Some 2)))); (ProtocolStatement_Valuing (Some "data3") None (Some (IntegerValue (Some 3)))); (RepeatProtocol (Some (Protocol [(ProtocolStatement_Valuing (Some "data4") None (Some (IntegerValue (Some 4)))); (ProtocolStatement_Valuing (Some "data5") None (Some (IntegerValue (Some 5)))); (ProtocolStatement_Valuing (Some "data6") None (Some (IntegerValue (Some 6))))]))); (ProtocolStatement_Valuing (Some "data7") None (Some (IntegerValue (Some 7)))); (ProtocolStatement_Valuing (Some "data8") None (Some (IntegerValue (Some 8)))); (ProtocolStatement_Valuing (Some "data9") None (Some (IntegerValue (Some 9))))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [BehaviorStatement_Done])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
