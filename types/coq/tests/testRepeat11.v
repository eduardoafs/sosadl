Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testRepeat11") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") None [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeIn) (Some (NamedType (Some "type1")))); (Connection (Some false) (Some "connection2") (Some ModeTypeOut) (Some (NamedType (Some "type1")))); (Connection (Some false) (Some "connection3") (Some ModeTypeOut) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(RepeatProtocol (Some (Protocol [AnyAction]))); (ProtocolAction (Some (ComplexName ["gate1"; "connection3"])) (Some (SendProtocolAction (Some Any))))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [BehaviorStatement_Done])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)