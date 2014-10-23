Require Import String.

(**
* Environment *)

(* An environment is a [string] indexed mapping from names to some
given object. The concept is abstractly defined by the following
axioms. *)

Axiom environment: Set -> Set.
Axiom empty: forall {A: Set}, environment A.
Axiom get: forall {A: Set}, environment A -> string -> option A.
Axiom set: forall {A: Set}, environment A -> string -> A -> environment A.
Axiom merge: forall {A: Set}, environment A -> environment A -> environment A.

Notation "x [ n ]" := (get x n) (at level 0).
Notation "x [ n <- v ]" := (set x n v) (at level 0).
Notation "x <++ y" := (merge x y) (at level 0).

Definition contains {A: Set} (e: environment A) n v := e[n] = Some v.

