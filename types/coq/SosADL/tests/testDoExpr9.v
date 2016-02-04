Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testDoExpr8") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") (Some (TupleType [(FieldDecl (Some "x") (Some IntegerType)); (FieldDecl (Some "y") (Some IntegerType))])) [])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeIn) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ProtocolStatement_Valuing (Some "v") (Some (NamedType (Some "type1"))) (Some (Expression_Tuple [(TupleElement (Some "x") (Some (IntegerValue (Some 0)))); (TupleElement (Some "y") (Some (IntegerValue (Some 1))))]))); (ProtocolStatement_DoExpr (Some (Field (Some (IdentExpression (Some "v"))) (Some "x"))))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(BehaviorStatement_Valuing (Some "v") (Some (NamedType (Some "type1"))) (Some (Expression_Tuple [(TupleElement (Some "x") (Some (IntegerValue (Some 1)))); (TupleElement (Some "y") (Some (IntegerValue (Some 2))))]))); (BehaviorStatement_DoExpr (Some (Field (Some (IdentExpression (Some "v"))) (Some "x"))))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
