Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testDoExpr10") (Some (EntityBlock [] [] [(SystemDecl (Some "test") [] [(DataTypeDecl (Some "type1") (Some (TupleType [(FieldDecl (Some "z") (Some (RangeType (Some (IntegerValue (Some 1))) (Some (IntegerValue (Some 1)))))); (FieldDecl (Some "t") (Some (RangeType (Some (IntegerValue (Some 2))) (Some (IntegerValue (Some 2))))))])) [(FunctionDecl (Some (FormalParameter (Some "data") (Some (NamedType (Some "type1"))))) (Some "y") [(FormalParameter (Some "x") (Some (RangeType (Some (IntegerValue (Some 0))) (Some (IntegerValue (Some 10))))))] (Some (TupleType [(FieldDecl (Some "z") (Some (RangeType (Some (IntegerValue (Some 1))) (Some (IntegerValue (Some 11)))))); (FieldDecl (Some "t") (Some (RangeType (Some (IntegerValue (Some 2))) (Some (IntegerValue (Some 12))))))])) [] (Some (Expression_Tuple [(TupleElement (Some "z") (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "data"))) (Some "z"))) (Some "+") (Some (IdentExpression (Some "x")))))); (TupleElement (Some "t") (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "data"))) (Some "t"))) (Some "+") (Some (IdentExpression (Some "x"))))))])))])] [(GateDecl (Some "gate1") [(Connection (Some false) (Some "connection1") (Some ModeTypeIn) (Some (NamedType (Some "type1"))))] (Some (ProtocolDecl (Some "gate1protocol") (Some (Protocol [(ProtocolStatement_DoExpr (Some (Field (Some (CallExpression (Some "y") [(IntegerValue (Some 5))])) (Some "z"))))])))))] (Some (BehaviorDecl (Some "test") (Some (Behavior [(BehaviorStatement_Valuing (Some "x") (Some (NamedType (Some "type1"))) (Some (Expression_Tuple [(TupleElement (Some "z") (Some (IntegerValue (Some 1)))); (TupleElement (Some "t") (Some (IntegerValue (Some 2))))]))); (BehaviorStatement_DoExpr (Some (Field (Some (MethodCall (Some (IdentExpression (Some "x"))) (Some "y") [(IntegerValue (Some 5))])) (Some "z"))))])))) None)] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
