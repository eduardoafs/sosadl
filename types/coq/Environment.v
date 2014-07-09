Require Import String.

(**
* Notion of environment

An environment is a {string} indexed mapping from names to some given object.
*)

Axiom environment: Set -> Set.
Axiom contains: forall {A: Set}, environment A -> string -> A -> Prop.
Axiom empty: forall {A: Set}, environment A.
Axiom get: forall {A: Set}, environment A -> string -> A.
Axiom set: forall {A: Set}, environment A -> string -> A -> environment A.

Notation "x [ n ]" := (get x n) (at level 0).
Notation "x [ n <- v ]" := (set x n v) (at level 0).
