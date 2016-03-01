Require Import List.
Require Import String.
Require SosADL.SosADL.
Require Import SosADL.Environment.
Require Import SosADL.Utils.
Require Import SosADL.Interpretation.
Require Import SosADL.TypeSystem.
Require Import BinInt.
Require Import Omega.
Require Import ZArith.
Require Import ZArith.Zquot.


Local Open Scope list_scope.
Local Open Scope string_scope.

Lemma interpInZ_implies_constexpr: forall e f (H: interp_in_Z e = Interpreted f), expression e is constant integer.
Proof.
  intros.
  assert (exists f, interp_in_Z e = Interpreted f) as I by (exists f; auto).
  clear f H.
  revert e I.
  apply interp_in_Z_ind; intros; constructor; auto.
Qed.

Ltac Zbool_to_cmp :=
  repeat match goal with
         | H: ((_ <=? _)%Z = true) |- _ => apply Zbool.Zle_bool_imp_le in H
         end.

Ltac interp_to_Zle :=
  repeat match goal with
         | H: (_ <= _) |- _ => inversion H; subst; clear H
         end;
  repeat match goal with
         | H1: (interp_in_Z ?e = Interpreted ?f),
               H2: (interp_in_Z ?e = Interpreted ?g) |- _ =>
           rewrite H1 in H2; inversion H2; subst; clear H2
         end.

Ltac auto_rewrite :=
  simpl;
  repeat match goal with
         | H: (?x = _) |- _ => rewrite H
         end;
  auto.

Lemma range_modulo_min_ok: forall lmin l lmax rmin r rmax min
                                  (H1: range_modulo_min lmin lmax rmin rmax min)
                                  (H2: lmin <= l)
                                  (H3: l <= lmax)
                                  (H4: rmin <= r)
                                  (H5: r <= rmax),
    min <= (SosADL.SosADL.BinaryExpression (Some l) (Some "mod") (Some r)).
Proof.
  intros.
  interp_to_Zle.
  Zbool_to_cmp.
  destruct H1.
  - interp_to_Zle.
    assert (zr3 = (1 - zr)%Z) by (unfold interp_in_Z in *; rewrite p2 in p13; inversion p13; auto).
    subst. clear p13.
    inversion p10. subst. clear p10.
    apply In_Z with (zl := zl) (zr := Z.rem zr2 zr0).
    + auto.
    + auto_rewrite.
    + apply Zbool.Zle_imp_le_bool.
      Zbool_to_cmp.
      assert ((0 < zr0)%Z) by omega.
      destruct (Z.le_ge_cases zr2 0%Z).
      * generalize (Zrem_lt_neg_pos _ _ H0 H). omega.
      * generalize (Zrem_lt_pos_pos _ _ H0 H). omega.
  - interp_to_Zle. Zbool_to_cmp.
    apply In_Z with (zl := zl) (zr := (Z.rem zr2 zr0)).
    + auto.
    + auto_rewrite.
    + apply Zbool.Zle_imp_le_bool.
      inversion p13. subst. clear p13.
      assert ((0 <= zr2)%Z) by omega.
      Zquot.zero_or_not zr0.
      generalize (Zquot.Zrem_lt_pos _ _ H H0).
      omega.
  - interp_to_Zle. Zbool_to_cmp.
    apply In_Z with (zl := zl) (zr := (Z.rem zr2 zr0)).
    + auto.
    + auto_rewrite.
    + apply Zbool.Zle_imp_le_bool.
      inversion p13. rewrite p0 in H0. inversion H0. subst. clear H0 p13.
      inversion p15. subst. clear p15.
      assert ((zr0 < 0)%Z) by omega.
      destruct (Z.le_ge_cases zr2 0%Z).
      * generalize (Zrem_lt_neg_neg _ _ H0 H). omega.
      * generalize (Zrem_lt_pos_neg _ _ H0 H). omega.
Qed.

Lemma range_modulo_max_ok: forall lmin l lmax rmin r rmax max
                                  (H1: range_modulo_max lmin lmax rmin rmax max)
                                  (H2: lmin <= l)
                                  (H3: l <= lmax)
                                  (H4: rmin <= r)
                                  (H5: r <= rmax),
    (SosADL.SosADL.BinaryExpression (Some l) (Some "mod") (Some r)) <= max.
Proof.
  intros.
  interp_to_Zle.
  Zbool_to_cmp.
  destruct H1.
  - interp_to_Zle. Zbool_to_cmp.
    inversion p12. rewrite p2 in H0. inversion H0. subst. clear p12 H0.
    inversion p10. subst. clear p10.
    apply In_Z with (zl := Z.rem zr2 zr0) (zr := zr3).
    + auto_rewrite.
    + auto.
    + apply Zbool.Zle_imp_le_bool.
      assert ((0 < zr0)%Z) by omega.
      destruct (Z.le_ge_cases zr2 0%Z).
      * generalize (Zrem_lt_neg_pos _ _ H0 H). omega.
      * generalize (Zrem_lt_pos_pos _ _ H0 H). omega.
  - interp_to_Zle. Zbool_to_cmp.
    apply In_Z with (zl := (Z.rem zr2 zr0)) (zr := zr3).
    + auto_rewrite.
    + auto.
    + apply Zbool.Zle_imp_le_bool.
      inversion p12. subst. clear p12.
      assert ((zr2 <= 0)%Z) by omega.
      Zquot.zero_or_not zr0.
      generalize (Zquot.Zrem_lt_neg _ _ H H0).
      omega.
  - interp_to_Zle. Zbool_to_cmp.
    assert (zl = (1 - zl0)%Z) by (unfold interp_in_Z in *; rewrite p0 in p12; inversion p12; auto). subst. clear p12.
    inversion p15. subst. clear p15.
    apply In_Z with (zl := (Z.rem zr2 zr0)) (zr := zr3).
    + auto_rewrite.
    + auto.
    + apply Zbool.Zle_imp_le_bool.
      assert ((zr0 < 0)%Z) by omega.
      destruct (Z.le_ge_cases zr2 0%Z).
      * generalize (Zrem_lt_neg_neg _ _ H0 H). omega.
      * generalize (Zrem_lt_pos_neg _ _ H0 H). omega.
Qed.
