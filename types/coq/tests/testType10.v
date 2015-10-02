Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testType10") (Some (EntityBlock [(DataTypeDecl (Some "type1") (Some IntegerType) []); (DataTypeDecl (Some "type2") (Some (RangeType (Some (IntegerValue (Some 0))) (Some (IntegerValue (Some 1))))) []); (DataTypeDecl (Some "type3") (Some (TupleType [(FieldDecl (Some "x") (Some (NamedType (Some "type1")))); (FieldDecl (Some "y") (Some (NamedType (Some "type2"))))])) []); (DataTypeDecl (Some "type4") (Some (SequenceType (Some (TupleType [(FieldDecl (Some "x") (Some (NamedType (Some "type1")))); (FieldDecl (Some "y") (Some (NamedType (Some "type2"))))])))) []); (DataTypeDecl (Some "type5") (Some (SequenceType (Some (NamedType (Some "type3"))))) [])] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type5") (Some (SequenceType (Some (TupleType [(FieldDecl (Some "x") (Some (NamedType (Some "type1")))); (FieldDecl (Some "y") (Some (NamedType (Some "type2"))))])))) []); (DataTypeDecl (Some "type6") (Some (SequenceType (Some (NamedType (Some "type3"))))) [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeOut) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [ProtocolStatement_Done])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [BehaviorStatement_Done])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
