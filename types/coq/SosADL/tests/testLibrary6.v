Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [(Import (Some "Base"))] (Some (Library (Some "testLibrary6") (Some (EntityBlock [(DataTypeDecl (Some "Complex") (Some (TupleType [(FieldDecl (Some "r") (Some IntegerType)); (FieldDecl (Some "i") (Some IntegerType))])) [(FunctionDecl (Some (FormalParameter (Some "a") (Some (NamedType (Some "Complex"))))) (Some "add") [(FormalParameter (Some "b") (Some (NamedType (Some "Complex"))))] (Some (NamedType (Some "Complex"))) [] (Some (Expression_Tuple [(TupleElement (Some "r") (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "a"))) (Some "r"))) (Some "+") (Some (Field (Some (IdentExpression (Some "b"))) (Some "r")))))); (TupleElement (Some "i") (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "a"))) (Some "i"))) (Some "+") (Some (Field (Some (IdentExpression (Some "b"))) (Some "i"))))))])))])] [(FunctionDecl (Some (FormalParameter (Some "a") (Some (NamedType (Some "Complex"))))) (Some "mult") [(FormalParameter (Some "b") (Some (TupleType [(FieldDecl (Some "r") (Some IntegerType)); (FieldDecl (Some "i") (Some IntegerType))])))] (Some (TupleType [(FieldDecl (Some "r") (Some IntegerType)); (FieldDecl (Some "i") (Some IntegerType))])) [] (Some (Expression_Tuple [(TupleElement (Some "r") (Some (BinaryExpression (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "a"))) (Some "r"))) (Some "*") (Some (Field (Some (IdentExpression (Some "b"))) (Some "r"))))) (Some "-") (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "a"))) (Some "i"))) (Some "*") (Some (Field (Some (IdentExpression (Some "b"))) (Some "i")))))))); (TupleElement (Some "i") (Some (BinaryExpression (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "a"))) (Some "r"))) (Some "*") (Some (Field (Some (IdentExpression (Some "b"))) (Some "i"))))) (Some "+") (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "a"))) (Some "i"))) (Some "*") (Some (Field (Some (IdentExpression (Some "b"))) (Some "r"))))))))])))] [] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
