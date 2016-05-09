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
         end;
  try match goal with
      | |- ((_ <=? _)%Z = true) => apply Zle_imp_le_bool
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
    assert (zl = ((-1) - zl0)%Z) by (unfold interp_in_Z in *; rewrite p0 in p12; inversion p12; auto). subst. clear p12.
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

Lemma deinterp_in_Z: forall a b n, (a <=? b)%Z = true -> interp_in_Z n = Interpreted b -> (SosADL.SosADL.IntegerValue (Some a)) <= n.
Proof.
  intros.
  apply In_Z with (zl := a) (zr := b); auto.
Qed.

Lemma deinterp_in_Z': forall a b n, (b <=? a)%Z = true -> interp_in_Z n = Interpreted b -> n <= (SosADL.SosADL.IntegerValue (Some a)).
Proof.
  intros.
  apply In_Z with (zl := b) (zr := a); auto.
Qed.

Ltac simpl_in_Z :=
  repeat match goal with
             | H: interp_in_Z (SosADL.SosADL.IntegerValue _) = Interpreted _ |- _ => inversion H; subst; clear H
             | H: interp_in_Z (SosADL.SosADL.UnaryExpression _ (Some (SosADL.SosADL.IntegerValue _))) = Interpreted _ |- _ => inversion H; subst; clear H
             | H1: interp_in_Z (SosADL.SosADL.BinaryExpression (Some (SosADL.IntegerValue (Some ?l))) (Some "-") (Some ?v)) = Interpreted ?x,
                   H2: interp_in_Z ?v = Interpreted ?r
               |- _ => assert ((l - r)%Z = x) by (unfold interp_in_Z in *; rewrite H2 in H1; inversion H1; auto);
                     subst; clear H1
             | H1: interp_in_Z (SosADL.SosADL.BinaryExpression (Some (SosADL.SosADL.UnaryExpression (Some "-") (Some (SosADL.IntegerValue (Some ?l))))) (Some "-") (Some ?v)) = Interpreted ?x,
                   H2: interp_in_Z ?v = Interpreted ?r
               |- _ => assert (((-l) - r)%Z = x) by (unfold interp_in_Z in *; rewrite H2 in H1; inversion H1; auto);
                     subst; clear H1
             | H1: interp_in_Z (SosADL.SosADL.BinaryExpression (Some ?v) (Some "+") (Some (SosADL.IntegerValue (Some ?l)))) = Interpreted ?x,
                   H2: interp_in_Z ?v = Interpreted ?r
               |- _ => assert ((r + l)%Z = x) by (unfold interp_in_Z in *; rewrite H2 in H1; inversion H1; auto);
                     subst; clear H1
             | H1: interp_in_Z (SosADL.SosADL.BinaryExpression (Some ?v) (Some "-") (Some (SosADL.IntegerValue (Some ?l)))) = Interpreted ?x,
                   H2: interp_in_Z ?v = Interpreted ?r
               |- _ => assert ((r - l)%Z = x) by (unfold interp_in_Z in *; rewrite H2 in H1; inversion H1; auto);
                     subst; clear H1
         end.

Lemma range_modulo_min_best_pos_pos: forall lmin lmax rmin rmax
                             (H1: (SosADL.SosADL.IntegerValue (Some 1%Z)) <= rmin)
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax)
                             (H4: (SosADL.SosADL.IntegerValue (Some 0%Z)) <= lmin)
                             min
                             (H5: range_modulo_min lmin lmax rmin rmax min),
    min <= SosADL.SosADL.IntegerValue (Some 0%Z).
Proof.
  intros.
  destruct H5.
  - interp_to_Zle.
    simpl_in_Z.
    apply In_Z with (zl := zl) (zr := 0%Z); auto.
    Zbool_to_cmp.
    omega.
  - auto.
  - elimtype False. clear - H1 H3 p1.
    interp_to_Zle.
    simpl_in_Z.
    Zbool_to_cmp.
    omega.
Qed.

Lemma range_modulo_min_best_neg_pos: forall lmin lmax rmin rmax zlmin
                             (H1: (SosADL.SosADL.IntegerValue (Some 1%Z)) <= rmin)
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax)
                             (H4: interp_in_Z lmin = Interpreted zlmin)
                             (H5: (0 <=? zlmin)%Z = false)
                             min
                             (H': range_modulo_min lmin lmax rmin rmax min),
    min <= (SosADL.SosADL.BinaryExpression (Some (SosADL.SosADL.IntegerValue (Some 1%Z))) (Some "-") (Some rmax)).
Proof.
  intros. destruct H'.
  - auto.
  - elimtype False. clear - H4 H5 p1.
    interp_to_Zle.
    simpl_in_Z.
    rewrite H5 in p3.
    discriminate.
  - elimtype False.
    clear - H1 H3 p1.
    interp_to_Zle.
    simpl_in_Z.
    Zbool_to_cmp.
    omega.
Qed.

Lemma range_modulo_min_best_pos: forall lmin lmax rmin rmax
                             (H1: (SosADL.SosADL.IntegerValue (Some 1%Z)) <= rmin)
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax),
    exists min, range_modulo_min lmin lmax rmin rmax min
           /\ forall min', range_modulo_min lmin lmax rmin rmax min' -> min' <= min.
Proof.
  intros.
  inversion H2. subst.
  case_eq ((0 <=? zl)%Z); intro.
  - exists (SosADL.SosADL.IntegerValue (Some 0%Z)).
    split.
    + apply range_modulo_min_zero.
      * apply In_Z with (zl := 0%Z) (zr := zl); auto; reflexivity.
      * apply In_Z with (zl := 0%Z) (zr := 0%Z); auto.
    + eapply deinterp_in_Z in H; eauto.
      apply range_modulo_min_best_pos_pos; auto.
  - exists (SosADL.SosADL.BinaryExpression (Some (SosADL.SosADL.IntegerValue (Some 1%Z))) (Some "-") (Some rmax)).
    split.
    + apply range_modulo_min_pos.
      * interp_to_Zle. simpl_in_Z.
        apply In_Z with (zl := 1%Z) (zr := zr2); auto.
      * interp_to_Zle. simpl_in_Z.
        apply In_Z with (zl := (1 - zr0)%Z) (zr := (1 - zr0)%Z); try auto_rewrite; apply Zle_bool_refl.
    + eapply range_modulo_min_best_neg_pos; eauto.
Qed.

Lemma range_modulo_min_best_pos_neg: forall lmin lmax rmin rmax
                             (H1: rmax <= (SosADL.SosADL.UnaryExpression (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z)))))
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax)
                             (H4: (SosADL.SosADL.IntegerValue (Some 0%Z)) <= lmin)
                             min
                             (H5: range_modulo_min lmin lmax rmin rmax min),
    min <= SosADL.SosADL.IntegerValue (Some 0%Z).
Proof.
  intros. destruct H5.
  - elimtype False. clear - H1 H3 p1.
    interp_to_Zle. simpl_in_Z.
    Zbool_to_cmp.
    omega.
  - auto.
  - interp_to_Zle. simpl_in_Z.
    apply In_Z with (zl := zl) (zr := 0%Z); auto.
    Zbool_to_cmp.
    omega.
Qed.

Lemma range_modulo_min_best_neg_neg: forall lmin lmax rmin rmax zlmin
                             (H1: rmax <= (SosADL.SosADL.UnaryExpression (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z)))))
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax)
                             (H4: interp_in_Z lmin = Interpreted zlmin)
                             (H5: (0 <=? zlmin)%Z = false)
                             min
                             (H': range_modulo_min lmin lmax rmin rmax min),
    min <= (SosADL.SosADL.BinaryExpression (Some rmin) (Some "+") (Some (SosADL.SosADL.IntegerValue (Some 1%Z)))).
Proof.
  intros. destruct H'.
  - interp_to_Zle. simpl_in_Z.
    apply In_Z with (zl := zl) (zr := (zl1 + 1)%Z); auto; auto_rewrite.
    Zbool_to_cmp.
    omega.
  - elimtype False. clear - H4 H5 p1.
    interp_to_Zle. simpl_in_Z.
    rewrite H5 in p3.
    discriminate.
  - auto.
Qed.

Lemma range_modulo_min_best_neg: forall lmin lmax rmin rmax
                             (H1: rmax <= (SosADL.SosADL.UnaryExpression (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z)))))
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax),
    exists min, range_modulo_min lmin lmax rmin rmax min
           /\ forall min', range_modulo_min lmin lmax rmin rmax min' -> min' <= min.
Proof.
  intros.
  inversion H2. subst.
  case_eq ((0 <=? zl)%Z); intro.
  - exists (SosADL.SosADL.IntegerValue (Some 0%Z)).
    split.
    + apply range_modulo_min_zero.
      * apply In_Z with (zl := 0%Z) (zr := zl); auto; reflexivity.
      * apply In_Z with (zl := 0%Z) (zr := 0%Z); auto.
    + eapply deinterp_in_Z in H; eauto.
      apply range_modulo_min_best_pos_neg; auto.
  - exists (SosADL.SosADL.BinaryExpression (Some rmin) (Some "+") (Some (SosADL.SosADL.IntegerValue (Some 1%Z)))).
    split.
    + apply range_modulo_min_neg.
      * interp_to_Zle. simpl_in_Z.
        apply In_Z with (zl := zl2) (zr := (-1)%Z); auto.
      * interp_to_Zle. simpl_in_Z.
        apply In_Z with (zl := (zl0 + 1)%Z) (zr := (zl0 + 1)%Z); try auto_rewrite; apply Zle_bool_refl.
    + eapply range_modulo_min_best_neg_neg; eauto.
Qed.

Lemma range_modulo_max_best_neg_pos: forall lmin lmax rmin rmax
                             (H1: (SosADL.SosADL.IntegerValue (Some 1%Z)) <= rmin)
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax)
                             (H4: lmax <= SosADL.SosADL.IntegerValue (Some 0%Z))
                             max
                             (H': range_modulo_max lmin lmax rmin rmax max),
    SosADL.SosADL.IntegerValue (Some 0%Z) <= max.
Proof.
  intros. destruct H'.
  - interp_to_Zle. simpl_in_Z.
    apply In_Z with (zl := 0%Z) (zr := zr); auto.
    Zbool_to_cmp.
    omega.
  - auto.
  - elimtype False. clear - H1 H3 p1.
    interp_to_Zle. simpl_in_Z.
    Zbool_to_cmp.
    omega.
Qed.

Lemma range_modulo_max_best_neg_neg: forall lmin lmax rmin rmax
                             (H1: rmax <= SosADL.SosADL.UnaryExpression (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z))))
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax)
                             (H4: lmax <= SosADL.SosADL.IntegerValue (Some 0%Z))
                             max
                             (H': range_modulo_max lmin lmax rmin rmax max),
    SosADL.SosADL.IntegerValue (Some 0%Z) <= max.
Proof.
  intros. destruct H'.
  - elimtype False. clear - H1 H3 p1.
    interp_to_Zle. simpl_in_Z.
    Zbool_to_cmp.
    omega.
  - auto.
  - interp_to_Zle. simpl_in_Z.
    apply In_Z with (zl := 0%Z) (zr := zr); auto.
    Zbool_to_cmp.
    omega.
Qed.

Lemma range_modulo_max_best_pos_pos: forall lmin lmax rmin rmax zlmax
                             (H1: (SosADL.SosADL.IntegerValue (Some 1%Z)) <= rmin)
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax)
                             (H4: interp_in_Z lmax = Interpreted zlmax)
                             (H5: (zlmax <=? 0)%Z = false)
                             max
                             (H': range_modulo_max lmin lmax rmin rmax max),
    (SosADL.SosADL.BinaryExpression (Some rmax) (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z)))) <= max.
Proof.
  intros. destruct H'.
  - auto.
  - elimtype False. clear - H4 H5 p1.
    interp_to_Zle. simpl_in_Z.
    rewrite H5 in p3.
    discriminate.
  - interp_to_Zle. simpl_in_Z.
    apply In_Z with (zl := (zr1 - 1)%Z) (zr := zr); try auto_rewrite.
    Zbool_to_cmp.
    omega.
Qed.

Lemma range_modulo_max_best_pos_neg: forall lmin lmax rmin rmax zlmax
                             (H1: rmax <= SosADL.SosADL.UnaryExpression (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z))))
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax)
                             (H4: interp_in_Z lmax = Interpreted zlmax)
                             (H5: (zlmax <=? 0)%Z = false)
                             max
                             (H': range_modulo_max lmin lmax rmin rmax max),
    (SosADL.SosADL.BinaryExpression (Some (SosADL.SosADL.UnaryExpression (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z))))) (Some "-") (Some rmin)) <= max.
Proof.
  intros. destruct H'.
  - interp_to_Zle. simpl_in_Z.
    apply In_Z with (zl := ((-1) - zl1)%Z) (zr := zr).
    + auto_rewrite.
    + auto.
    + Zbool_to_cmp.
      omega.
  - elimtype False. clear - H4 H5 p1.
    interp_to_Zle. simpl_in_Z.
    rewrite H5 in p3.
    discriminate.
  - auto.
Qed.

Lemma range_modulo_max_best_pos: forall lmin lmax rmin rmax
                             (H1: (SosADL.SosADL.IntegerValue (Some 1%Z)) <= rmin)
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax),
    exists max, range_modulo_max lmin lmax rmin rmax max
           /\ forall max', range_modulo_max lmin lmax rmin rmax max' -> max <= max'.
Proof.
  intros.
  inversion H2. subst.
  case_eq ((zr <=? 0)%Z); intro.
  - exists (SosADL.SosADL.IntegerValue (Some 0%Z)).
    split.
    + apply range_modulo_max_zero.
      * apply In_Z with (zl := zr) (zr := 0%Z); auto.
      * apply In_Z with (zl := 0%Z) (zr := 0%Z); auto.
    + eapply deinterp_in_Z' in H; eauto.
      apply range_modulo_max_best_neg_pos; auto.
  - exists (SosADL.SosADL.BinaryExpression (Some rmax) (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z)))).
    split.
    + apply range_modulo_max_pos.
      * auto.
      * interp_to_Zle. simpl_in_Z.
        apply In_Z with (zl := (zr0 - 1)%Z) (zr := (zr0 - 1)%Z); try auto_rewrite; apply Zle_bool_refl.
    + eapply range_modulo_max_best_pos_pos; eauto.
Qed.

Lemma range_modulo_max_best_neg: forall lmin lmax rmin rmax
                             (H1: rmax <= SosADL.SosADL.UnaryExpression (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z))))
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax),
    exists max, range_modulo_max lmin lmax rmin rmax max
           /\ forall max', range_modulo_max lmin lmax rmin rmax max' -> max <= max'.
Proof.
  intros.
  inversion H2. subst.
  case_eq ((zr <=? 0)%Z); intro.
  - exists (SosADL.SosADL.IntegerValue (Some 0%Z)).
    split.
    + apply range_modulo_max_zero.
      * apply In_Z with (zl := zr) (zr := 0%Z); auto.
      * apply In_Z with (zl := 0%Z) (zr := 0%Z); auto.
    + eapply deinterp_in_Z' in H; eauto.
      apply range_modulo_max_best_neg_neg; auto.
  - exists (SosADL.SosADL.BinaryExpression (Some (SosADL.SosADL.UnaryExpression (Some "-") (Some (SosADL.SosADL.IntegerValue (Some 1%Z))))) (Some "-") (Some rmin)).
    split.
    + apply range_modulo_max_neg.
      * auto.
      * interp_to_Zle. simpl_in_Z.
        apply In_Z with (zl := ((-1) - zl0)%Z) (zr := ((-1) - zl0)%Z); try auto_rewrite; apply Zle_bool_refl.
    + eapply range_modulo_max_best_pos_neg; eauto.
Qed.

Lemma method_defined''_ok: forall m l tau f r, method_defined' m l tau f r -> method_defined'' m l tau f r.
Proof.
  intros. induction H.
  - exists 0. apply H.
  - destruct IHExists as [ i IH ].
    exists (S i). apply IH.
Qed.

Lemma method_defined'_ok: forall m l tau f r, method_defined'' m l tau f r -> method_defined' m l tau f r.
Proof.
  intros. destruct H as [ i H]. revert l H. induction i; intros.
  - destruct l.
    + contradiction.
    + apply Exists_cons_hd. apply H.
  - destruct l.
    + contradiction.
    + apply Exists_cons_tl. apply (IHi l H).
Qed.

Lemma method_defined''_ok': forall m l tau f r, method_defined m l tau f r -> method_defined'' m l tau f r.
Proof.
  intros. destruct H as [ z H ].
  exists (Z.to_nat z). apply H.
Qed.

Lemma method_defined_ok: forall m l tau f r, method_defined'' m l tau f r -> method_defined m l tau f r.
Proof.
  intros. destruct H as [ i H ].
  exists (Z.of_nat i). rewrite Znat.Nat2Z.id. apply H.
Qed.

Lemma field_type_correct: forall l n t, field_type l n = Some t -> field_has_type l n t.
Proof.
  intros. revert H.
  induction l.
  - discriminate.
  - destruct a. destruct o.
    + simpl. intros. destruct (string_dec n s).
      * subst. apply First_Field.
      * apply Next_Field. auto.
    + intros. apply Next_Field. auto. 
Qed.

Lemma distinct_tl: forall {A: Set}  f (hd: A) tl,
    (values (f x) for x of (hd :: tl) are distinct according to option_string_dec)
    -> values (f x) for x of tl are distinct according to option_string_dec.
Proof.
  simpl. unfold has_no_dup.
  intros. revert H. case (NoDup_dec _ option_string_dec (f hd :: map (fun x => f x) tl)).
  - intros I H. inversion I.
    case (NoDup_dec _ option_string_dec (map (fun x => f x) tl)).
    + reflexivity.
    + contradiction.
  - discriminate.
Qed.

Lemma distinct_hd: forall {A: Set} f (hd: A) tl,
    (values (f x) for x of (hd :: tl) are distinct according to option_string_dec)
    -> forall x, In x tl -> f x <> f hd.
Proof.
  simpl. unfold has_no_dup.
  intros. revert H. case (NoDup_dec _ option_string_dec (f hd :: map (fun x => f x) tl)).
  - intros. clear H. intro.
    apply in_map with (f:=fun x => f x) in H0.
    remember (f x) as fx.
    remember (f hd) as fh.
    remember (map (fun x => f x) tl) as ft.
    clear Heqfx Heqft Heqfh. subst fx.
    revert H0.
    destruct (NoDup_cons_iff fh ft) as [ H _ ].
    destruct (H n) as [ I _ ].
    apply I.
  - discriminate.
Qed.

Lemma field_type_other: forall h r n t, field_type r n = Some t -> SosADL.SosADL.FieldDecl_name h <> (Some n) -> field_type (h :: r) n = Some t.
Proof.
  intros. destruct h. destruct o.
  - simpl in H0. simpl. case (string_dec n s).
    + intro. elimtype False. subst. apply H0. reflexivity.
    + auto.
  - simpl. auto.
Qed.

Lemma field_type_some: forall r n t, field_type r n = Some t -> exists f, In f r /\ SosADL.SosADL.FieldDecl_name f = Some n.
Proof.
  intros r n t. induction r.
  - discriminate.
  - simpl. case_eq a. destruct o. intro.
    + destruct (string_dec n s).
      * exists a. { split.
               - left. auto.
               - subst. reflexivity. }
      * intros. { destruct (IHr H0) as [ f [ p1 p2 ] ].
                  exists f. split.
                  - right. auto.
                  - auto. }
    + intros. destruct (IHr H0) as [ f [ p1 p2 ] ].
      exists f. split.
      * right. auto.
      * auto.
Qed.

Lemma field_type_complete:
  forall l n t
    (ND: values (SosADL.SosADL.FieldDecl_name x) for x of l are distinct according to option_string_dec)
  ,
    field_has_type l n t -> field_type l n = Some t.
Proof.
  intros. induction H.
  - simpl. destruct (string_dec n n).
    + reflexivity.
    + elimtype False. apply n0. reflexivity.
  - assert (field_type r n = Some t) by ( apply IHfield_has_type; eapply distinct_tl; apply ND ).
    apply field_type_other.
    + auto.
    + destruct (field_type_some _ _ _ H0) as [ x [ I J ] ].
      rewrite <- J.
      intro X. symmetry in X. revert X.
      eapply distinct_hd.
      * apply ND.
      * auto.
Qed.

Lemma field_has_type_in: forall l n t, field_has_type l n t -> In (SosADL.SosADL.FieldDecl (Some n) (Some t)) l.
Proof.
  intros. induction H.
  - left. reflexivity.
  - right. auto.
Qed.

Lemma field_has_type_in': forall l n t, In (SosADL.SosADL.FieldDecl (Some n) (Some t)) l -> field_has_type l n t.
Proof.
  intros l n t.
  induction l.
  - intro. destruct H.
  - intro. destruct H as [ H | H ].
    + subst. apply First_Field.
    + apply Next_Field. auto.
Qed.
