Require Import TypeSystem.
Require Import tests.failtestIfThenElse4.

Import List.
Import AST.
Import ListNotations.
Import Utils.
Import String.
Import Interpretation.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Theorem well_typed: ~ SoSADL ast well typed.
Proof.
  unfold ast. intro WT.
  inversion_clear WT.
  inversion_clear H.
  inversion_clear H0.
  decompose [and] H. clear H H2 H3.
  inversion_clear H0.
  decompose [and] H. clear H H0.
  inversion_clear H1.
  decompose [and] H. clear H H0.
  inversion_clear H1.
  decompose [and] H. clear H H0 H2.
  inversion_clear H3.
  inversion_clear H.
  inversion_clear H0.
Qed.

(*
Local Variables:
mode: coq
coding: utf-8
coq-load-path: ("..")
End:
 *)