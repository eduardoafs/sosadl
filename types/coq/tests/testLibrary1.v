Require Import SosADL.
Require Import String.
Require Import List.
Require Import BinInt.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition ast :=
(SosADL [] (Some (Library (Some "testLibrary1") (Some (EntityBlock [] [] [] [] []))))).

(*
Local Variables:
mode: coq
coding: utf-8
End:
 *)