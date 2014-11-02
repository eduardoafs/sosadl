Require Import List.
Require Import String.
Require Import AbstractSoSADL.

Import AST.
Import ListNotations.

Definition ast :=
  SosADL
    []
    (Library
       "testDone"
       (EntityBlock
          []
          []
          [SystemDecl
              "test"
              []
              [DataTypeDecl "type1" None []]
              []
              (BehaviorDecl
                 "test"
                 []
                 (Behavior [Done]))
              None]
          []
          [])).

(*
Local Variables:
mode: coq
coding: utf-8
coq-load-path: ("..")
End:
 *)