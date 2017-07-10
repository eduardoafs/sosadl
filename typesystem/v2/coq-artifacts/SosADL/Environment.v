Require Import String.
Require Import ZArith.

(**
* Environment *)

(* An environment is a [string] indexed mapping from names to some
given object. The concept is abstractly defined by the following
axioms. *)

Module Type Env.
  Axiom environment: Type -> Type.
  Axiom empty: forall {A: Type}, environment A.
  Axiom get: forall {A: Type}, environment A -> string -> option A.
  Axiom set: forall {A: Type}, environment A -> string -> A -> environment A.
  Axiom merge: forall {A: Type}, environment A -> environment A -> environment A.
  Axiom binds: forall {A: Type}, environment A -> A -> Prop.
End Env.

Require Import List.

Module ListBasedEnv <: Env.
  Import ListNotations.

  Record item {T: Type}: Type :=
    { key: string;
      value: T }.
  Definition environment (T: Type) := list (@item T).

  Definition empty {A: Type}: environment A := [].
  Fixpoint get {A: Type} (e: environment A) (k: string) {struct e}: option A :=
    match e with
      | [] => None
      | i :: tl =>
        if string_dec k (key i) then Some (value i)
        else get tl k
    end.
  Definition set {A: Type} (e: environment A) (k: string) (v: A): environment A :=
    {| key := k; value := v |} :: e.
  Fixpoint merge {A: Type} (l: environment A) (r: environment A) {struct r}: environment A :=
    match r with
      | [] => l
      | i :: tl => merge (set l (key i) (value i)) tl
    end.

  Fixpoint binds' {A: Type} (l: environment A) (x: A) {struct l}: Prop :=
    match l with
    | [] => False
    | i :: tl => (value i = x) \/ binds' tl x
    end.

  Definition binds'' {A: Type} (l: environment A) (x: A) :=
    exists (i: nat), match nth_error l i with
              | Some p => Some (value p)
              | None => None
              end = Some x.

  Lemma binds''_ok: forall A (l: environment A) x, binds' l x -> binds'' l x.
  Proof.
    intros. induction l.
    - destruct H.
    - destruct H as [ L | H ].
      + exists 0. rewrite <- L. reflexivity.
      + destruct (IHl H) as [ i P ].
        exists (S i). apply P.
  Qed.

  Lemma binds'_ok: forall A (l: environment A) x, binds'' l x -> binds' l x.
  Proof.
    intros. destruct H as [ i P ]. revert l P.
    induction i; intros.
    - destruct l.
      + discriminate.
      + left. inversion P. reflexivity.
    - destruct l.
      + discriminate.
      + right. apply (IHi l P).
  Qed.

  Definition binds {A: Type} (l: environment A) (x: A) :=
    exists (i: Z), match nth_error l (Z.to_nat i) with
              | Some p => Some (value p)
              | None => None
              end = Some x.

  Lemma binds''_ok': forall A (l: environment A) x, binds l x -> binds'' l x.
  Proof.
    intros. destruct H as [ i H ].
    exists (Z.to_nat i). apply H.
  Qed.

  Lemma binds_ok: forall A (l: environment A) x, binds'' l x -> binds l x.
  Proof.
    intros. destruct H as [ z H ].
    exists (Z.of_nat z). rewrite Znat.Nat2Z.id. apply H.
  Qed.
End ListBasedEnv.

Export ListBasedEnv.

Notation "x [| n |]" := (get x n) (at level 0).
Notation "x [| n <- v |]" := (set x n v) (at level 0).
Notation "x <++ y" := (merge x y) (at level 0).

Definition contains {A: Type} (e: environment A) n v := e[|n|] = Some v.

