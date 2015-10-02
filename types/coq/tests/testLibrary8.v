Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [(Import (Some "Base")); (Import (Some "testLibrary7"))] (Some (Library (Some "testLibrary8") (Some (EntityBlock [] [(FunctionDecl (Some (FormalParameter (Some "a") (Some (NamedType (Some "Complex"))))) (Some "sqr") [] (Some (NamedType (Some "Complex"))) [] (Some (MethodCall (Some (IdentExpression (Some "a"))) (Some "mult") [(IdentExpression (Some "a"))])))] [] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)
