Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [(Import (Some "Base"))] (Some (Library (Some "testLibrary5") (Some (EntityBlock [(DataTypeDecl (Some "type1") (Some IntegerType) [(FunctionDecl (Some "i") (Some "type1") (Some "add") [(FormalParameter (Some "j") (Some (NamedType (Some "type1"))))] (Some (NamedType (Some "type1"))) [] (Some (BinaryExpression (Some (IdentExpression (Some "i"))) (Some "+") (Some (IdentExpression (Some "j"))))))])] [(FunctionDecl (Some "i") (Some "type1") (Some "mult") [(FormalParameter (Some "j") (Some IntegerType))] (Some IntegerType) [] (Some (BinaryExpression (Some (IdentExpression (Some "i"))) (Some "*") (Some (IdentExpression (Some "j"))))))] [] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
