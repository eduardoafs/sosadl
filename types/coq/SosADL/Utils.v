Require Import List.
Require Import String.
Section Decs.
  Variable A: Type.
  Variable A_dec: forall (x y: A), {x = y} + {x <> y}.

  Definition Some_dec (l: option A) (r: option A): {l = r} + {l <> r}.
  Proof.
    refine (match l with
              | Some ll => _
              | None => _
            end).
    - refine (match r with
                | Some rr => _
                | None => _
              end).
      + refine (match A_dec ll rr with
                  | left H => _
                  | right H => _
                end).
        * left. f_equal. exact H.
        * right. intro N. injection N. exact H.
      + right. discriminate.
    - refine (match r with
                | Some _ => _
                | None => _
              end).
      + right. discriminate.
      + left. reflexivity.
  Defined.

  Fixpoint NoDup_dec (l: list A) {struct l}: {NoDup l} + {~ NoDup l}.
  Proof.
    refine (match l with
              | nil => _
              | hd :: tl => _
            end).
    - left. apply NoDup_nil.
    - refine (match (in_dec A_dec hd tl) with
                | left H => _
                | right H => _
              end).
      + right. intro N. inversion N. contradiction.
      + refine (match (NoDup_dec tl) with
                  | left R => _
                  | right R => _
                end).
        * left. exact (NoDup_cons _ H R).
        * right. intro N. inversion N. contradiction.
  Defined.
End Decs.

Definition has_no_dup {A: Type} (eqdec: forall x y: A, {x=y} + {x<>y}) (l: list A) := if NoDup_dec A eqdec l then true else false.

(**
 * Some utility notations

 *)

Notation "'for' 'each' e 'of' l , p" :=
  (List.Forall (fun e => p) l)
    (at level 200, e ident, right associativity).

Notation "'values' e 'for' x 'of' l 'are' 'distinct' 'according' 'to' eqdec" :=
  (* List.NoDup (List.map (fun x => e) f) *)
  (has_no_dup eqdec (List.map (fun x => e) l) = true)
    (at level 200, x ident).

Notation "'for' 'each' e f 'of' l m , p" :=
  (List.Forall2 (fun e f => p) l m)
    (at level 200, e ident, f ident, right associativity, l at level 1, m at level 1).

(**
 * Some utility functions

 *)

Import ListNotations.

Definition option_string_dec := Some_dec string string_dec.

(*
Ltac decide_nodup dec :=
  match goal with
    | |- NoDup ?l =>
      let x := fresh "x" in
      let E := fresh "E" in
      remember (NoDup_dec _ dec l) as x eqn:E;
        vm_compute in E;
        match goal with
          | H: (x = left ?P) |- _ => exact P
        end
  end.
*)

Ltac decide_nodup dec :=
  match goal with
    | |- NoDup ?l =>
      match eval vm_compute in (NoDup_dec _ dec l) with
        | left ?P => exact P
      end
  end.

Ltac mysplit :=
  try match goal with
        | |- _ /\ _ => apply conj; mysplit
      end.