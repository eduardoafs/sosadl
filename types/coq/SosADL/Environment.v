Require Import String.

(**
* Environment *)

(* An environment is a [string] indexed mapping from names to some
given object. The concept is abstractly defined by the following
axioms. *)

Module Type Env.
  Axiom environment: Set -> Set.
  Axiom empty: forall {A: Set}, environment A.
  Axiom get: forall {A: Set}, environment A -> string -> option A.
  Axiom set: forall {A: Set}, environment A -> string -> A -> environment A.
  Axiom merge: forall {A: Set}, environment A -> environment A -> environment A.
End Env.

Require Import List.

Module ListBasedEnv <: Env.
  Import ListNotations.

  Record item {T: Set}: Set :=
    { key: string;
      value: T }.
  Definition environment (T: Set) := list (@item T).

  Definition empty {A: Set}: environment A := [].
  Fixpoint get {A: Set} (e: environment A) (k: string) {struct e}: option A :=
    match e with
      | [] => None
      | i :: tl =>
        if string_dec k (key i) then Some (value i)
        else get tl k
    end.
  Definition set {A: Set} (e: environment A) (k: string) (v: A): environment A :=
    {| key := k; value := v |} :: e.
  Fixpoint merge {A: Set} (l: environment A) (r: environment A) {struct r}: environment A :=
    match r with
      | [] => l
      | i :: tl => merge (set l (key i) (value i)) tl
    end.
End ListBasedEnv.

Export ListBasedEnv.

Notation "x [| n |]" := (get x n) (at level 0).
Notation "x [| n <- v |]" := (set x n v) (at level 0).
Notation "x <++ y" := (merge x y) (at level 0).

Definition contains {A: Set} (e: environment A) n v := e[|n|] = Some v.

