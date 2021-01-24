Require Import Bool.
Require Import List.
Require Import Omega.
Require Import Classical.
Require Import FinFun.
Require Import FunctionalExtensionality.

From mathcomp
Require Import ssreflect.

Require Import Utility.
Require Import Cell.
Require Import Concentric.
Require Import Tactic.

Import ListNotations.

Section Rotation.
  Open Scope Z_scope.
  Open Scope list_scope.

  Definition rotate (p : Z * Z) : Z * Z := mat_mul mat2_pi_over_2 p.

  Definition rotate' (p : Z * Z) : Z * Z := mat_mul mat2_pi_over_2' p.

  Definition rotate_st (st : State) : State :=
    fun (x y : Z) => let (x', y') := rotate (x, y) in st x' y'.

  Definition rotate_st' (st : State) : State :=
    fun (x y : Z) => let (x', y') := rotate' (x, y) in st x' y'.

  CoFixpoint rotate_run (r : Run) : Run :=
    RCons (rotate_st (hd r)) (rotate_run (tl r)).

  Lemma rot_reduction (st : State) (x y : Z)
    : rotate_st st x y = st y (-x).
  Proof.
    rewrite /rotate_st/rotate/mat_mul/mat2_pi_over_2/nth/fst/snd.
    repeat rewrite Z.mul_0_l.
    rewrite Z.mul_1_l.
    rewrite Z.add_0_l.
    rewrite Z.add_0_r.
    rewrite (Z.mul_opp_l 1 x).
    rewrite Z.mul_1_l.
    by [].
  Qed.

  Lemma rotation_is_bijective : Bijective rotate_st.
  Proof.
    rewrite /Bijective.
    exists rotate_st'.
    split.
    -move=> st.
      have s0: rotate_st st = fun (x y : Z) => st y (-x).
      rewrite /rotate_st/rotate/mat_mul/mat2_pi_over_2/nth/fst/snd.
      apply functional_extensionality.
      move=> x.
      apply functional_extensionality.
      move=> y.
      repeat rewrite Z.mul_0_l.
      rewrite Z.mul_1_l.
      rewrite Z.add_0_l.
      rewrite Z.add_0_r.
      rewrite (Z.mul_opp_l 1 x).
      by rewrite Z.mul_1_l.
      rewrite s0.
      rewrite /rotate_st'/rotate'/mat_mul/mat2_pi_over_2'/nth/fst/snd.
      apply functional_extensionality.
      move=> x.
      apply functional_extensionality.
      move=> y.
      rewrite Z.add_0_l.
      rewrite Z.add_0_r.
      rewrite (Z.mul_opp_l 1 y).
      rewrite Z.opp_involutive.
      by repeat rewrite Z.mul_1_l.
    -move=> st.
      have s0: rotate_st' st = fun (x y : Z) => st (-y) x.
      rewrite /rotate_st'/rotate'/mat_mul/mat2_pi_over_2'/nth/fst/snd.
      apply functional_extensionality.
      move=> x.
      apply functional_extensionality.
      move=> y.
      repeat rewrite Z.mul_0_l.
      rewrite Z.mul_1_l.
      rewrite Z.add_0_l.
      rewrite Z.add_0_r.
      rewrite -(Zopp_mult_distr_l 1 y).
      by rewrite Z.mul_1_l.
      rewrite s0.
      rewrite /rotate_st/rotate/mat_mul/mat2_pi_over_2/nth/fst/snd.
      apply functional_extensionality.
      move=> x.
      apply functional_extensionality.
      move=> y.
      rewrite Z.mul_1_l.
      rewrite Z.add_0_l.
      rewrite Z.add_0_r.
      rewrite -(Zopp_mult_distr_l 1 x).
      rewrite Z.opp_involutive.
      by repeat rewrite Z.mul_1_l.
  Qed.

  Lemma convert_inclusion (c : CellState) (st : State) (x y : Z)
    : In c [st y (- x + 1); st y (- x - 1); st (y - 1) (- x); st (y + 1) (- x)] <-> In c [st (y - 1) (- x); st (y + 1) (- x); st y (- x - 1); st y (- x + 1)].
  Proof.
    split.
    -move=> s0.
      case: s0 => [ s0 | s0 ].
      right. right. right. by left.
      case: s0 => [ s0 | s0 ].
      right. right. by left.
      case: s0 => [ s0 | s0 ].
      by left.
      case: s0 => [ s0 | s0 ].
      right. by left.
      case: s0.
    -move=> s0.
      case: s0 => [ s0 | s0 ].
      right. right. by left.
      case: s0 => [ s0 | s0 ].
      right. right. right. by left.
      case: s0 => [ s0 | s0 ].
      right. by left.
      case: s0 => [ s0 | s0 ].
      by left.
      case: s0.
  Qed.

  Lemma convert_inclusion2 (c : CellState) (st : State) (x y : Z)
    : In c [st x (y + 1); st x (y - 1); st (x - 1) y; st (x + 1) y]
    <-> In c [st (x - 1) y; st (x + 1) y; st x (y - 1); st x (y + 1)].
  Proof.
    split.
    -move=> s0.
      case: s0 => [ s0 | s0 ].
      right. right. right. by left.
      case: s0 => [ s0 | s0 ].
      right. right. by left.
      case: s0 => [ s0 | s0 ].
      by left.
      case: s0 => [ s0 | s0 ].
      right. by left.
      case: s0.
    -move=> s0.
      case: s0 => [ s0 | s0 ].
      right. right. by left.
      case: s0 => [ s0 | s0 ].
      right. right. right. by left.
      case: s0 => [ s0 | s0 ].
      right. by left.
      case: s0 => [ s0 | s0 ].
      by left.
      case: s0.
  Qed.
  
  Theorem trans_preservation_at_rot (st st' : State)
    : trans st st' <-> trans (rotate_st st) (rotate_st st').
  Proof.
    split.
    -move=> tr.
      rewrite /trans in tr.
      move=> x y.
      specialize (tr y (-x)).
      case: tr => [ s0 | ctrans ].
      +left.
        rewrite /rotate_st/rotate/mat_mul/mat2_pi_over_2/nth/fst/snd.
        repeat rewrite Z.mul_0_l.
        rewrite Z.mul_1_l.
        rewrite Z.add_0_l.
        rewrite Z.add_0_r.
        rewrite (Z.mul_opp_l 1 x).
        by rewrite Z.mul_1_l.
      +right.
        rewrite /rule_existence.
        rewrite rot_reduction.
        rewrite (rot_reduction st (x - 1) y).
        rewrite Z.opp_sub_distr.
        rewrite (rot_reduction st (x + 1) y).
        have s0: -(x + 1) = -x - 1. by omega. rewrite s0. clear s0.
        rewrite (rot_reduction st x (y - 1)).
        rewrite (rot_reduction st x (y + 1)).
        rewrite (rot_reduction st').
        remember [st y (- x + 1); st y (- x - 1); st (y - 1) (- x); st (y + 1) (- x)] as nbs.
        destruct_ctrans ctrans.
        *apply convert_inclusion in in0.
          rewrite Heqnbs.
          by constructor.
        *apply convert_inclusion in in0.
          apply (WtoTmp0 nbs alt).
          by subst.
        *apply convert_inclusion in in0.
          apply (WtoTmp1 nbs alt).
          by subst.
        *constructor.
        *constructor.
        *case: in0 => in0 in1.
          apply convert_inclusion in in0.
          apply convert_inclusion in in1.
          apply (TmptoDef0 nbs alt alt' i).
          rewrite Heqnbs.
          by subst.
        *case: in0 => in0 in1.
          apply convert_inclusion in in0.
          apply convert_inclusion in in1.
          apply (TmptoDef1 nbs alt alt' i).
          rewrite Heqnbs.
          by subst.
        *case: in0 => in0 in1.
          apply convert_inclusion in in0.
          apply convert_inclusion in in1.
          apply (TmptoDef2 nbs alt alt' i).
          rewrite Heqnbs.
          by subst.
    -move=> tr.
      rewrite /trans in tr.
      move=> x y.
      specialize (tr (-y) x).
      rewrite /rotate_st/rotate/mat_mul/mat2_pi_over_2/nth/fst/snd in tr.
      rewrite /rule_existence in tr.
      repeat rewrite Z.mul_0_l in tr.
      repeat rewrite Z.mul_1_l in tr.
      repeat rewrite Z.add_0_l in tr.
      repeat rewrite Z.add_0_r in tr.
      rewrite (Z.mul_opp_opp 1 y) in tr.
      rewrite Z.mul_1_l in tr.
      have s0: -1 * (- y - 1) = y + 1. by omega.
      have s1: -1 * (- y + 1) = y - 1. by omega.
      rewrite s0 s1 in tr. clear s0 s1.
      case: tr => [ s0 | ctrans ].
      +by left.
      +right.
        rewrite /rule_existence.
        remember [st (x - 1) y; st (x + 1) y; st x (y - 1); st x (y + 1)] as nbs.
        destruct_ctrans ctrans.
        *apply convert_inclusion2 in in0.
          rewrite Heqnbs.
          by constructor.
        *apply convert_inclusion2 in in0.
          apply (WtoTmp0 nbs alt).
          by subst.
        *apply convert_inclusion2 in in0.
          apply (WtoTmp1 nbs alt).
          by subst.
        *by constructor.
        *by constructor.
        *case: in0 => in0 in1.
          apply convert_inclusion2 in in0.
          apply convert_inclusion2 in in1.
          apply (TmptoDef0 nbs alt alt' i).
          rewrite Heqnbs.
          by subst.
        *case: in0 => in0 in1.
          apply convert_inclusion2 in in0.
          apply convert_inclusion2 in in1.
          apply (TmptoDef1 nbs alt alt' i).
          rewrite Heqnbs.
          by subst.
        *case: in0 => in0 in1.
          apply convert_inclusion2 in in0.
          apply convert_inclusion2 in in1.
          apply (TmptoDef2 nbs alt alt' i).
          rewrite Heqnbs.
          by subst.
  Qed.

  Theorem pred_preservation_at_rot (P : Run -> State -> State -> Prop)
    : (forall (r : Run) (st : State), exists (st' : State),
    P r st st') -> forall (r : Run) (st : State), exists (st' : State),
    P (rotate_run r) (rotate_st st) (rotate_st st').
  Proof.
    move=> s0 r st.
    specialize (s0 (rotate_run r) (rotate_st st)).
    destruct s0.
    move: x H => st' s0.
    move: (rotation_is_bijective) => s1.
    rewrite /Bijective in s1.
    destruct s1.
    move: x H => rot s1.
    case: s1 => s1 s2.
    exists (rot st').
    by rewrite (s2 st').
  Qed.

  Close Scope list_scope.
  Close Scope Z_scope.

End Rotation.

