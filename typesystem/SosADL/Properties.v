Require Import List.
Require Import String.
Require SosADL.SosADL.
Require Import SosADL.Environment.
Require Import SosADL.Utils.
Require Import SosADL.Interpretation.
Require Import SosADL.TypeSystem.
Require Import SosADL.SosADLNotations.
Require Import BinInt.
Require Import Omega.
Require Import ZArith.
Require Import ZArith.Zquot.

Local Open Scope list_scope.
Local Open Scope string_scope.


Lemma incrementally_fold_left:
  forall {T: Set} (P: env -> T -> env -> Prop) (name: T -> option string)
         (content: T -> option env_content)
         (p: forall g x g', P g x g' -> g' = augment_env g (name x) (content x))
         (l: list T)
         (Gamma: env) (Gamma': env)
         (s: @incrementally T P Gamma l Gamma'),
    Gamma' = fold_left (fun r x => augment_env r (name x) (content x)) l Gamma.
Proof.
  intros.
  induction s.
  - auto.
  - apply p in p1. subst. auto.
Qed.

Lemma simple_incrementally_fold_left:
  forall {T: Set} (P: env -> T -> Prop) (name: T -> option string)
         (content: T -> option env_content)
         (l: list T)
         (Gamma: env) (Gamma': env)
         (s: @incrementally T (simple_increment T P name content) Gamma l Gamma'),
    Gamma' = fold_left (fun r x => augment_env r (name x) (content x)) l Gamma.
Proof.
  intros T P name content l Gamma Gamma'. apply incrementally_fold_left. intros g x g' H.
  destruct H. auto.
Qed.

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
             | H1: interp_in_Z (SosADL.SosADL.BinaryExpression (Some ?v1) (Some "-") (Some ?v2)) = Interpreted ?x,
                   H2: interp_in_Z ?v1 = Interpreted ?r1,
                       H3: interp_in_Z ?v2 = Interpreted ?r2
               |- _ => assert ((r1 - r2)%Z = x) by (unfold interp_in_Z in *; rewrite H2 in H1; rewrite H3 in H1; inversion H1; auto);
                     subst; clear H1
             | H1: interp_in_Z (SosADL.SosADL.BinaryExpression (Some ?v1) (Some "-") (Some (SosADL.SosADL.BinaryExpression (Some ?v2) (Some "mod") (Some ?v3)))) = Interpreted ?x,
                   H2: interp_in_Z ?v1 = Interpreted ?r1,
                       H3: interp_in_Z ?v2 = Interpreted ?r2,
                           H4: interp_in_Z ?v3 = Interpreted ?r3
               |- _ => assert ((r1 - (Z.rem r2 r3))%Z = x) by (unfold interp_in_Z in *; try rewrite H2 in H1; try rewrite H3 in H1; try rewrite H4 in H1; inversion H1; auto);
                     subst; clear H1
             | H1: interp_in_Z (SosADL.SosADL.BinaryExpression (Some ?v1) (Some "-") (Some (SosADL.SosADL.BinaryExpression (Some ?v1) (Some "mod") (Some ?v3)))) = Interpreted ?x,
                   H2: interp_in_Z ?v1 = Interpreted ?r1,
                       H4: interp_in_Z ?v3 = Interpreted ?r3
               |- _ => assert ((r1 - (Z.rem r1 r3))%Z = x) by (unfold interp_in_Z in *; rewrite H2 in H1; rewrite H4 in H1; inversion H1; auto);
                     subst; clear H1
                      | H1: interp_in_Z (SosADL.SosADL.BinaryExpression (Some (SosADL.SosADL.BinaryExpression (Some ?v1) (Some "+") (Some (SosADL.SosADL.IntegerValue (Some 1%Z))))) (Some "-") (Some (SosADL.SosADL.BinaryExpression (Some ?v1) (Some "mod") (Some ?v3)))) = Interpreted ?x,
                   H2: interp_in_Z ?v1 = Interpreted ?r1,
                       H4: interp_in_Z ?v3 = Interpreted ?r3
               |- _ => assert (((r1 + 1) - (Z.rem r1 r3))%Z = x) by (unfold interp_in_Z in *; rewrite H2 in H1; rewrite H4 in H1; inversion H1; auto);
                     subst; clear H1
                      | H1: interp_in_Z (SosADL.SosADL.UnaryExpression (Some "-") (Some ?v)) = Interpreted ?x,
                            H2: interp_in_Z ?v = Interpreted ?r
                        |- _ => assert ((- r)%Z = x) by (unfold interp_in_Z in *; rewrite H2 in H1; inversion H1; auto);
                              subst; clear H1
         end.

Ltac apply_in_Z :=
  match goal with
  | A: (interp_in_Z ?l = Interpreted ?zzl),
       B: (interp_in_Z ?r = Interpreted ?zzr)
    |- ?l <= ?r
    => apply In_Z with (zl := zzl) (zr := zzr); auto
  | A: (interp_in_Z ?l = Interpreted ?zzl)
    |- ?l <= SosADL.SosADL.IntegerValue (Some ?zzr)
    => apply In_Z with (zl := zzl) (zr := zzr); auto
  | B: (interp_in_Z ?r = Interpreted ?zzr)
    |- SosADL.SosADL.IntegerValue (Some ?zzl) <= ?r
    => apply In_Z with (zl := zzl) (zr := zzr); auto
  | |- SosADL.SosADL.IntegerValue (Some ?zzl) <= SosADL.SosADL.IntegerValue (Some ?zzr)
    => apply In_Z with (zl := zzl) (zr := zzr); auto
  | |- ?a <= ?b
    => let za := interp_to_Z a in
      let zb := interp_to_Z b in
      apply In_Z with (zl := za) (zr := zb); auto; try (solve [ auto_rewrite ])
  end.

Lemma deinterp_in_Z: forall a b n, (a <=? b)%Z = true -> interp_in_Z n = Interpreted b -> (# a)%sosadl <= n.
Proof.
  intros.
  apply_in_Z.
Qed.

Lemma deinterp_in_Z': forall a b n, (b <=? a)%Z = true -> interp_in_Z n = Interpreted b -> n <= (# a)%sosadl.
Proof.
  intros.
  apply_in_Z.
Qed.

Lemma range_modulo_min_ok: forall lmin l lmax rmin r rmax min
                                  (H1: range_modulo_min lmin lmax rmin rmax min)
                                  (H2: lmin <= l)
                                  (H3: l <= lmax)
                                  (H4: rmin <= r)
                                  (H5: r <= rmax),
    min <= (l mod r)%sosadl.
Proof.
  intros.
  interp_to_Zle.
  simpl_in_Z.
  Zbool_to_cmp.
  destruct H1.
  - interp_to_Zle.
    simpl_in_Z.
    apply_in_Z.
    apply Zbool.Zle_imp_le_bool.
    Zbool_to_cmp.
    assert ((0 < zr0)%Z) by omega.
    destruct (Z.le_ge_cases zr2 0%Z).
    + generalize (Zrem_lt_neg_pos _ _ H0 H). omega.
    + generalize (Zrem_lt_pos_pos _ _ H0 H). omega.
  - interp_to_Zle. simpl_in_Z. Zbool_to_cmp.
    apply_in_Z.
    apply Zbool.Zle_imp_le_bool.
    assert ((0 <= zr2)%Z) by omega.
    Zquot.zero_or_not zr0.
    generalize (Zquot.Zrem_lt_pos _ _ H H0).
    omega.
  - interp_to_Zle. simpl_in_Z.
    Zbool_to_cmp.
    apply_in_Z.
    apply Zbool.Zle_imp_le_bool.
    assert ((zr0 < 0)%Z) by omega.
    destruct (Z.le_ge_cases zr2 0%Z).
    + generalize (Zrem_lt_neg_neg _ _ H0 H). omega.
    + generalize (Zrem_lt_pos_neg _ _ H0 H). omega.
Qed.

Lemma range_modulo_max_ok: forall lmin l lmax rmin r rmax max
                                  (H1: range_modulo_max lmin lmax rmin rmax max)
                                  (H2: lmin <= l)
                                  (H3: l <= lmax)
                                  (H4: rmin <= r)
                                  (H5: r <= rmax),
    (l mod r)%sosadl <= max.
Proof.
  intros.
  interp_to_Zle.
  simpl_in_Z.
  Zbool_to_cmp.
  destruct H1.
  - interp_to_Zle. simpl_in_Z. Zbool_to_cmp.
    apply_in_Z.
    apply Zbool.Zle_imp_le_bool.
    assert ((0 < zr0)%Z) by omega.
    destruct (Z.le_ge_cases zr2 0%Z).
    + generalize (Zrem_lt_neg_pos _ _ H0 H). omega.
    + generalize (Zrem_lt_pos_pos _ _ H0 H). omega.
  - interp_to_Zle. simpl_in_Z. Zbool_to_cmp.
    apply_in_Z.
    apply Zbool.Zle_imp_le_bool.
    assert ((zr2 <= 0)%Z) by omega.
    Zquot.zero_or_not zr0.
    generalize (Zquot.Zrem_lt_neg _ _ H H0).
    omega.
  - interp_to_Zle. simpl_in_Z. Zbool_to_cmp.
    apply_in_Z.
    apply Zbool.Zle_imp_le_bool.
    assert ((zr0 < 0)%Z) by omega.
    destruct (Z.le_ge_cases zr2 0%Z).
    + generalize (Zrem_lt_neg_neg _ _ H0 H). omega.
    + generalize (Zrem_lt_pos_neg _ _ H0 H). omega.
Qed.

Lemma range_modulo_min_best_pos_pos: forall lmin lmax rmin rmax
                             (H1: (# 1%Z)%sosadl <= rmin)
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax)
                             (H4: (# 0%Z)%sosadl <= lmin)
                             min
                             (H5: range_modulo_min lmin lmax rmin rmax min),
    min <= (# 0%Z)%sosadl.
Proof.
  intros.
  destruct H5.
  - interp_to_Zle.
    simpl_in_Z.
    apply_in_Z.
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
                             (H1: (# 1%Z)%sosadl <= rmin)
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax)
                             (H4: interp_in_Z lmin = Interpreted zlmin)
                             (H5: (0 <=? zlmin)%Z = false)
                             min
                             (H': range_modulo_min lmin lmax rmin rmax min),
    min <= (# 1%Z - rmax)%sosadl.
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

Lemma quot_rem'' a b: (a - Z.rem a b)%Z = (b * Z.quot a b)%Z.
Proof.
  symmetry.
  apply Zplus_minus_eq.
  rewrite Z.add_comm.
  apply Z.quot_rem'.
Qed.

Lemma rem_plus_b a b: (0 <= a*b)%Z -> Z.rem a b = Z.rem (a+b)%Z b.
Proof.
  intro.
  rewrite Zplus_rem; auto.
  rewrite Z_rem_same.
  rewrite Z.add_0_r.
  symmetry.
  apply Zrem_rem.
Qed.

Lemma rem_0 a b: Z.rem (a - (Z.rem a b))%Z b = 0%Z.
Proof.
  apply Zrem_divides.
  exists (a ÷ b)%Z.
  apply quot_rem''.
Qed.

Lemma opp_sub a b: (- (a - b))%Z = (b - a)%Z.
Proof.
  omega.
Qed.

Lemma opp_le a b: (a <= b)%Z <-> (-b <= - a)%Z.
Proof.
  omega.
Qed.

Lemma add_sub a b c: (a + b - c)%Z = ((a - c) + b)%Z.
Proof.
  omega.
Qed.

Lemma add_sub' a b c: ((a - b) + c)%Z = (a + (c - b))%Z.
Proof.
  omega.
Qed.

Lemma opp_add_opp a b: (- (a + -b))%Z = (b - a)%Z.
Proof.
  omega.
Qed.

Lemma range_modulo_min_best_pos: forall lmin lmax rmin rmax
                             (H1: (# 1%Z)%sosadl <= rmin)
                             (H2: lmin <= lmax)
                             (H3: rmin <= rmax),
    exists min, range_modulo_min lmin lmax rmin rmax min
           /\ (forall min', range_modulo_min lmin lmax rmin rmax min' -> min' <= min)
           /\ (exists l r, r <= (lmax - lmin)%sosadl ->
                     (forall zlmin, interp_in_Z lmin = Interpreted zlmin -> (zlmin < 0)%Z -> lmin <= (- r)%sosadl) ->
                     lmin <= l /\ l <= lmax /\ rmin <= r /\ r <= rmax
                     /\ min <= (l mod r)%sosadl
                     /\ (l mod r)%sosadl <= min).
Proof.
  intros.
  inversion H2. subst.
  case_eq ((0 <=? zl)%Z); intro.
  - exists (# 0%Z)%sosadl.
    split_intro H4.
    + apply range_modulo_min_zero.
      * apply_in_Z; reflexivity.
      * apply_in_Z.
    + split.
      * eapply deinterp_in_Z in H; eauto.
        apply range_modulo_min_best_pos_pos; auto.
      * exists (lmax - (lmax mod rmin))%sosadl.
        exists rmin.
        intros H5 _.
        interp_to_Zle. simpl_in_Z.
        { split_intro H6.
          - apply_in_Z.
            Zbool_to_cmp.
            assert ((Z.rem zr2 zr3 < zr3)%Z).
            + apply Zquot.Zrem_lt_pos_pos; omega.
            + omega.
          - split_intro H7.
            + interp_to_Zle. simpl_in_Z. apply_in_Z. Zbool_to_cmp.
              assert ((0 <= Z.rem zr2 zr3)%Z).
              * apply Zquot.Zrem_lt_pos_pos; omega.
              * omega.
            + split_intro H8.
              * interp_to_Zle. simpl_in_Z. apply_in_Z. Zbool_to_cmp. omega.
              * { split.
                  - apply_in_Z.
                  - split.
                    + eapply range_modulo_min_ok; eauto.
                      apply_in_Z.
                    + interp_to_Zle. simpl_in_Z.
                      apply_in_Z. Zbool_to_cmp.
                      rewrite rem_0.
                      omega. } }
  - assert (0 > zl)%Z
      by (generalize (Zle_cases 0 zl); intro X; rewrite H in X; auto).
    exists (# 1%Z - rmax)%sosadl.
    split_intro H4.
    + apply range_modulo_min_pos.
      * interp_to_Zle. simpl_in_Z.
        apply_in_Z.
      * interp_to_Zle. simpl_in_Z.
        apply_in_Z.
        apply Zle_bool_refl.
    + split.
      * eapply range_modulo_min_best_neg_pos; eauto.
      * exists (lmin + (# 1%Z) - lmin mod rmax)%sosadl.
        exists rmax.
        intros H5 H6.
        apply Z.gt_lt in H0.
        generalize (H6 _ p1 H0).
        intro H7.
        interp_to_Zle. simpl_in_Z. Zbool_to_cmp.
        { split_intro G1.
          - apply_in_Z. Zbool_to_cmp.
            assert (Z.rem zl3 zr2 <= 0)%Z
              by (apply Zquot.Zrem_lt_neg_pos; omega).
            omega.
          - split_intro G2.
            + apply_in_Z. Zbool_to_cmp.
              assert (-zr2 < Z.rem zl3 zr2)%Z
                by (apply Zquot.Zrem_lt_neg_pos; omega).
              omega.
            + split_intro G3.
              * apply_in_Z. Zbool_to_cmp. auto.
              * { split_intro G4.
                  - apply_in_Z. Zbool_to_cmp. reflexivity.
                  - split.
                    + eapply range_modulo_min_ok; eauto.
                    + interp_to_Zle. simpl_in_Z.
                      apply_in_Z. Zbool_to_cmp.
                      rewrite add_sub.
                      rewrite quot_rem''.
                      rewrite Z.add_comm.
                      apply opp_le.
                      rewrite <- Z.rem_opp_l'.
                      rewrite opp_sub.
                      remember (- zl2)%Z as mzl2.
                      rewrite <- (Z.opp_involutive zl2).
                      rewrite <- Heqmzl2.
                      rewrite Zquot_opp_l.
                      rewrite <- Z.mul_opp_comm.
                      rewrite Z.mul_opp_l.
                      rewrite opp_add_opp.
                      rewrite rem_plus_b.
                      * rewrite add_sub'.
                        rewrite Z.add_comm.
                        rewrite Z.mul_comm.
                        { rewrite Z_rem_plus.
                          - rewrite Z.rem_small; omega.
                          - rewrite <- (Z.mul_0_l 0%Z).
                            apply Zmult_le_compat; try omega.
                            remember (mzl2 ÷ zr0)%Z as a.
                            assert (0 <= a)%Z by (subst; apply Z_quot_pos; omega).
                            assert (0 <= a * zr0)%Z.
                            * rewrite <- (Z.mul_0_l 0%Z).
                              apply Zmult_le_compat; auto; try reflexivity; try omega.
                            * omega.
                        }
                      * rewrite <- (Z.mul_0_l 0%Z).
                        apply Zmult_le_compat; try omega.
                        assert (1 <= (mzl2 ÷ zr0))%Z by (apply Zquot_le_lower_bound; omega).
                        { assert (1 <= zr0 * (mzl2 ÷ zr0))%Z.
                          - rewrite <- (Z.mul_1_l 1%Z).
                            apply Zmult_le_compat; omega.
                          - omega. } } }
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
           /\ (forall min', range_modulo_min lmin lmax rmin rmax min' -> min' <= min).
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
