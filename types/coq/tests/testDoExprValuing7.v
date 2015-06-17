Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testDoExprValuing2") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") (Some (TupleType [(FieldDecl (Some "z") (Some IntegerType)); (FieldDecl (Some "t") (Some IntegerType))])) [(FunctionDecl (Some "data") (Some "type1") (Some "y") [(FormalParameter (Some "x") (Some IntegerType))] (Some (NamedType (Some "type1"))) [] (Some (Expression_Tuple [(TupleElement (Some "z") (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "data"))) (Some "z"))) (Some "+") (Some (IdentExpression (Some "x")))))); (TupleElement (Some "t") (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "data"))) (Some "t"))) (Some "+") (Some (IdentExpression (Some "x"))))))])))])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeIn) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ProtocolStatement_Valuing (Some "data1") (Some IntegerType) (Some (IntegerValue (Some 1)))); (ProtocolStatement_DoExpr (Some (Field (Some (CallExpression (Some "y") [(IntegerValue (Some 5))])) (Some "z")))); (ProtocolStatement_Valuing (Some "data2") (Some IntegerType) (Some (IntegerValue (Some 2))))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(BehaviorStatement_Valuing (Some "data1") (Some IntegerType) (Some (IntegerValue (Some 1)))); (BehaviorStatement_DoExpr (Some (Field (Some (CallExpression (Some "y") [(IntegerValue (Some 5))])) (Some "z")))); (BehaviorStatement_Valuing (Some "data2") (Some IntegerType) (Some (IntegerValue (Some 2))))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)