Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [(Import (Some "Base")); (Import (Some "testLibrary6"))] (Some (Library (Some "testLibrary7") (Some (EntityBlock [] [(FunctionDecl (Some "a") (Some "Complex") (Some "sub") [(FormalParameter (Some "b") (Some (TupleType [(FieldDecl (Some "r") (Some IntegerType)); (FieldDecl (Some "i") (Some IntegerType))])))] (Some (TupleType [(FieldDecl (Some "r") (Some IntegerType)); (FieldDecl (Some "i") (Some IntegerType))])) [] (Some (Expression_Tuple [(TupleElement (Some "r") (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "a"))) (Some "r"))) (Some "-") (Some (Field (Some (IdentExpression (Some "b"))) (Some "r")))))); (TupleElement (Some "i") (Some (BinaryExpression (Some (Field (Some (IdentExpression (Some "a"))) (Some "i"))) (Some "-") (Some (Field (Some (IdentExpression (Some "b"))) (Some "i"))))))])))] [] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
