Require Import String.

(**
* Notion of environment

An environment is a {string} indexed mapping from names to some given object.
*)

Axiom environment: Set -> Set.
Axiom contains: forall {A: Set}, environment A -> string -> A -> Prop.
Axiom empty: forall {A: Set}, environment A.
