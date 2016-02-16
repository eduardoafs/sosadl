Require SosADL.SosADL.
Require Import BinInt.
Require Import String.

(** * General interpretation outcome *)

Inductive interpretation {A: Set}: Set :=
| Interpreted: A -> interpretation
| Failed: SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> interpretation.

(** * An interpretation function in [Z] *)

(** Currently, this interpretation function recognizes solely literal
interger values and arithmetic operations. *)

Local Open Scope string_scope.

Fixpoint interp_in_Z (e: SosADL.SosADL.t_Expression) {struct e} :=
  match e with
    | SosADL.SosADL.IntegerValue (Some x) => Interpreted x
    | SosADL.SosADL.UnaryExpression (Some op) (Some x) =>
      match match op with
              | "-" => Some Z.opp
              | "+" => Some id
              | _ => None
            end with
        | Some f =>
          match interp_in_Z x with
            | Interpreted y => Interpreted (f y)
            | Failed _ f => Failed e f
          end
        | None => Failed e e
      end
    | SosADL.SosADL.BinaryExpression (Some l) (Some op) (Some r) =>
      match match op with
              | "+" => Some Z.add
              | "-" => Some Z.sub
              | "*" => Some Z.mul
              | "/" => Some Z.quot
              | "mod" => Some Z.rem
              | _ => None
            end with
        | Some f =>
          match interp_in_Z l with
            | Interpreted ll =>
              match interp_in_Z r with
                | Interpreted rr => Interpreted (f ll rr)
                | Failed _ f => Failed e f
              end
            | Failed _ f => Failed e f
          end
        | None => Failed e e
      end
    | _ => Failed e e
  end.

Lemma interpInZ_unary o x (H: exists f, interp_in_Z (SosADL.SosADL.UnaryExpression (Some o) (Some x)) = Interpreted f):
  o = "+" \/ o = "-".
Proof.
  destruct H as [ f H ].
  simpl in H. destruct o; try discriminate.
  destruct a.
  destruct b; try discriminate;
    destruct b0; try discriminate;
      destruct b1; try discriminate;
        destruct b2; try discriminate;
          destruct b3; try discriminate;
            destruct b4; try discriminate;
              destruct b5; try discriminate;
                destruct b6; try discriminate;
                  destruct o; try discriminate;
                    auto.
Qed.

Lemma interpInZ_unary_pos x (H: exists f, interp_in_Z (SosADL.SosADL.UnaryExpression (Some "+") (Some x)) = Interpreted f):
  exists fx, interp_in_Z x = Interpreted fx.
Proof.
  destruct H as [ f H ].
  simpl in H.
  destruct (interp_in_Z x).
  - exists z. auto.
  - discriminate.
Qed.

Lemma interpInZ_unary_neg x (H: exists f, interp_in_Z (SosADL.SosADL.UnaryExpression (Some "-") (Some x)) = Interpreted f):
  exists fx, interp_in_Z x = Interpreted fx.
Proof.
  destruct H as [ f H ].
  simpl in H.
  destruct (interp_in_Z x).
  - exists z. auto.
  - discriminate.
Qed.

Lemma interpInZ_binary x o y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some o) (Some y)) = Interpreted f):
  o = "+" \/ o = "-" \/ o = "*" \/ o = "/" \/ o = "mod".
Proof.
  destruct H as [ f H ].
  simpl in H. destruct o; try discriminate.
  repeat (destruct a;
          destruct b; try discriminate;
          destruct b0; try discriminate;
          destruct b1; try discriminate;
          destruct b2; try discriminate;
          destruct b3; try discriminate;
          destruct b4; try discriminate;
          destruct b5; try discriminate;
          destruct b6; try discriminate;
          destruct o; try discriminate;
          auto).
Qed.

Lemma interpInZ_binary_add_l x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "+") (Some y)) = Interpreted f):
  exists fx, interp_in_Z x = Interpreted fx.
Proof.
  destruct H as [ f H ].
  simpl in H.
  destruct (interp_in_Z x).
  - exists z. auto.
  - discriminate.
Qed.

Lemma interpInZ_binary_add_r x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "+") (Some y)) = Interpreted f):
  exists fx, interp_in_Z y = Interpreted fx.
Proof.
  destruct H as [ f H ].
  simpl in H.
  destruct (interp_in_Z x).
  - destruct (interp_in_Z y).
    + exists z0. auto.
    + discriminate.
  - discriminate.
Qed.

Lemma interpInZ_binary_sub_l x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "-") (Some y)) = Interpreted f):
  exists fx, interp_in_Z x = Interpreted fx.
Proof.
  destruct H as [ f H ].
  simpl in H.
  destruct (interp_in_Z x).
  - exists z. auto.
  - discriminate.
Qed.

Lemma interpInZ_binary_sub_r x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "-") (Some y)) = Interpreted f):
  exists fx, interp_in_Z y = Interpreted fx.
Proof.
  destruct H as [ f H ].
  simpl in H.
  destruct (interp_in_Z x).
  - destruct (interp_in_Z y).
    + exists z0. auto.
    + discriminate.
  - discriminate.
Qed.

Lemma interpInZ_binary_mul_l x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "*") (Some y)) = Interpreted f):
  exists fx, interp_in_Z x = Interpreted fx.
Proof.
  destruct H as [ f H ].
  simpl in H.
  destruct (interp_in_Z x).
  - exists z. auto.
  - discriminate.
Qed.

Lemma interpInZ_binary_mul_r x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "*") (Some y)) = Interpreted f):
  exists fx, interp_in_Z y = Interpreted fx.
Proof.
  destruct H as [ f H ].
  simpl in H.
  destruct (interp_in_Z x).
  - destruct (interp_in_Z y).
    + exists z0. auto.
    + discriminate.
  - discriminate.
Qed.

Lemma interpInZ_binary_div_l x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "/") (Some y)) = Interpreted f):
  exists fx, interp_in_Z x = Interpreted fx.
Proof.
  destruct H as [ f H ].
  simpl in H.
  destruct (interp_in_Z x).
  - exists z. auto.
  - discriminate.
Qed.

Lemma interpInZ_binary_div_r x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "/") (Some y)) = Interpreted f):
  exists fx, interp_in_Z y = Interpreted fx.
Proof.
  destruct H as [ f H ].
  simpl in H.
  destruct (interp_in_Z x).
  - destruct (interp_in_Z y).
    + exists z0. auto.
    + discriminate.
  - discriminate.
Qed.

Lemma interpInZ_binary_mod_l x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "mod") (Some y)) = Interpreted f):
  exists fx, interp_in_Z x = Interpreted fx.
Proof.
  destruct H as [ f H ].
  simpl in H.
  destruct (interp_in_Z x).
  - exists z. auto.
  - discriminate.
Qed.

Lemma interpInZ_binary_mod_r x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "mod") (Some y)) = Interpreted f):
  exists fx, interp_in_Z y = Interpreted fx.
Proof.
  destruct H as [ f H ].
  simpl in H.
  destruct (interp_in_Z x).
  - destruct (interp_in_Z y).
    + exists z0. auto.
    + discriminate.
  - discriminate.
Qed.

Fixpoint interp_in_Z_ind (P: forall e, (exists f, interp_in_Z e = Interpreted f) -> Prop)
           (Plit: forall x (H: exists f, interp_in_Z (SosADL.SosADL.IntegerValue (Some x)) = Interpreted f), P (SosADL.SosADL.IntegerValue (Some x)) H)
           (Ppos: forall x (H: exists f, interp_in_Z (SosADL.SosADL.UnaryExpression (Some "+") (Some x)) = Interpreted f) (I: P x (interpInZ_unary_pos x H)), P (SosADL.SosADL.UnaryExpression (Some "+") (Some x)) H)
           (Pneg: forall x (H: exists f, interp_in_Z (SosADL.SosADL.UnaryExpression (Some "-") (Some x)) = Interpreted f) (I: P x (interpInZ_unary_neg x H)), P (SosADL.SosADL.UnaryExpression (Some "-") (Some x)) H)
           (Padd: forall x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "+") (Some y)) = Interpreted f) (I: P x (interpInZ_binary_add_l x y H)) (J: P y (interpInZ_binary_add_r x y H)), P (SosADL.SosADL.BinaryExpression (Some x) (Some "+") (Some y)) H)
           (Psub: forall x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "-") (Some y)) = Interpreted f) (I: P x (interpInZ_binary_sub_l x y H)) (J: P y (interpInZ_binary_sub_r x y H)), P (SosADL.SosADL.BinaryExpression (Some x) (Some "-") (Some y)) H)
           (Pmul: forall x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "*") (Some y)) = Interpreted f) (I: P x (interpInZ_binary_mul_l x y H)) (J: P y (interpInZ_binary_mul_r x y H)), P (SosADL.SosADL.BinaryExpression (Some x) (Some "*") (Some y)) H)
           (Pdiv: forall x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "/") (Some y)) = Interpreted f) (I: P x (interpInZ_binary_div_l x y H)) (J: P y (interpInZ_binary_div_r x y H)), P (SosADL.SosADL.BinaryExpression (Some x) (Some "/") (Some y)) H)
           (Pmod: forall x y (H: exists f, interp_in_Z (SosADL.SosADL.BinaryExpression (Some x) (Some "mod") (Some y)) = Interpreted f) (I: P x (interpInZ_binary_mod_l x y H)) (J: P y (interpInZ_binary_mod_r x y H)), P (SosADL.SosADL.BinaryExpression (Some x) (Some "mod") (Some y)) H)
           e (H: exists f, interp_in_Z e = Interpreted f) {struct e}: P e H.
  destruct e; try (destruct H; discriminate).
  - destruct o; try (destruct H; discriminate).
    destruct o0; try (destruct H; discriminate).
    destruct o1; try (destruct H; discriminate).
    destruct (interpInZ_binary _ _ _ H) as [ I | [ I | [ I | [ I | I ] ] ] ]; subst.
    + apply Padd; apply interp_in_Z_ind; auto.
    + apply Psub; apply interp_in_Z_ind; auto.
    + apply Pmul; apply interp_in_Z_ind; auto.
    + apply Pdiv; apply interp_in_Z_ind; auto.
    + apply Pmod; apply interp_in_Z_ind; auto.
  - destruct o; try (destruct H; discriminate). apply Plit.
  - destruct o; try (destruct H; discriminate).
    destruct o0; try (destruct H; discriminate).
    destruct (interpInZ_unary _ _ H) as [ I | I ]; subst.
    + apply Ppos; apply interp_in_Z_ind; auto.
    + apply Pneg; apply interp_in_Z_ind; auto.
Qed.

(** * Comparison of expressions *)

(** Currently, the sole way to prove comparison consists in
translating the SoSADL expression to [Z], then use the evaluation and
decision tools of this Coq library. *)

Inductive expression_le: SosADL.SosADL.t_Expression -> SosADL.SosADL.t_Expression -> Prop :=
| In_Z: forall
    (l: SosADL.SosADL.t_Expression)
    (zl: BinInt.Z)
    (r: SosADL.SosADL.t_Expression)
    (zr: BinInt.Z)
    (p1: interp_in_Z l = Interpreted zl)
    (p2: interp_in_Z r = Interpreted zr)
    (p3: (zl <=? zr = true)%Z)
  ,
    l <= r

where "e1 <= e2" := (expression_le e1 e2)
.

Ltac decide_in_Z :=
  match goal with
    | |- Interpretation.expression_le ?l ?r =>
      eapply Interpretation.In_Z;
        [ reflexivity | reflexivity | discriminate ]
  end.
