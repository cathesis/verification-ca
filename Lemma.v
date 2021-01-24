Require Import Bool.
Require Import List.
Require Import Omega.

From mathcomp
Require Import ssreflect.

Require Import Utility.
Require Import Cell.
Require Import Concentric.
Require Import Tactic.

Import ListNotations.

Section ConcentricLemma.
  Open Scope Z_scope.
  Open Scope list_scope.

  Lemma s_alt_consistency (st st' : State) (x y : Z) (tmp alt : bool) :
    st x y = s tmp alt ->
    st' x y = s tmp (negb alt) ->
    c_type (st x y) = c_type (st' x y).
  Proof.
    move=> st_xy st'_xy.
    rewrite st_xy st'_xy.
    by case tmp.
  Qed.

  Lemma si_alt_consistency
    (st st' : State) (x y i : Z) (tmp alt : bool) :
    st x y = si tmp alt i ->
    st' x y = si tmp (negb alt) i ->
    c_type (st x y) = c_type (st' x y).
  Proof.
    move=> st_xy st'_xy.
    rewrite st_xy st'_xy.
    by case tmp.
  Qed.
  
  Lemma safe_to_safe
    (c : CellState) (cs : list CellState) (c' : CellState) :
    CTrans c cs c' -> c_type c = Safe -> c_type c' = Safe.
  Proof.
    move=> ctrans c_type_c.
    by destruct ctrans.
  Qed.

  Lemma safe_from_temp_or_safe
    (c : CellState) (cs : list CellState) (c' : CellState) :
    CTrans c cs c' -> c_type c' = Safe ->
    (c_type c = Temp \/ c_type c = Safe).
  Proof.
    move=> ctrans c_type_c'.
    destruct ctrans; auto; done.
  Qed.

  Lemma temp_from_white_or_temp
    (c : CellState) (cs : list CellState) (c' : CellState) :
    CTrans c cs c' -> c_type c' = Temp ->
    (c_type c = White \/ c_type c = Temp).
  Proof.
    move=> ctrans c_type_c'.
    destruct ctrans; auto.
  Qed.

  Lemma trans_safe_to_safe
    (st st' : State) (x y : Z) :
    trans st st' -> c_type (st x y) = Safe -> c_type (st' x y) = Safe.
  Proof.
    rewrite /trans => trans_st_st'.
    case (trans_st_st' x y) => st_st'.
    -by rewrite st_st'.
    -rewrite /rule_existence in st_st'.
      by destruct st_st'.
  Qed.

  Lemma trans_tmp_to_tmp_or_safe
    (st st' : State) (x y : Z) :
    trans st st' -> c_type (st x y) = Temp ->
    c_type (st' x y) = Safe \/ c_type (st' x y) = Temp.
  Proof.
    rewrite /trans => trans_st_st'.
    case (trans_st_st' x y) => ctrans.
    -rewrite ctrans.
      move=> s0. by right.
    -rewrite /rule_existence in ctrans.
      move=> s0.
      destruct_ctrans ctrans.
      +by right.
      +by right.
      +by right.
      +have s1: st x y = s tmp alt. by [].
        have s2: st' x y = s tmp (negb alt). by [].
        specialize (s_alt_consistency st st' x y tmp alt s1 s2).
        move=> s3.
        rewrite s2 in s3.
        right.
        by rewrite -s3.
      +have s1: st x y = si tmp alt i. by [].
        have s2: st' x y = si tmp (negb alt) i. by [].
        specialize (si_alt_consistency st st' x y i tmp alt s1 s2).
        move=> s3.
        rewrite s2 in s3.
        right.
        by rewrite -s3.
      +by left.
      +by left.
      +by left.
  Qed.

  Lemma trans_tmp_from_tmp_or_white
    (st st' : State) (x y : Z) :
    trans st st' ->
    c_type (st' x y) = Temp ->
    c_type (st x y) = Temp \/ c_type (st x y) = White.
  Proof.
    rewrite /trans => trans_st_st'.
    case (trans_st_st' x y) => st_st'.
    -rewrite st_st'. auto.
    -rewrite /rule_existence in st_st'.
      +by destruct st_st'; auto.
  Qed.
  
  Lemma trans_safe_from_safe_or_tmp
    (st st' : State) (x y : Z) :
    trans st st' ->
    c_type (st' x y) = Safe ->
    c_type (st x y) = Safe \/ c_type (st x y) = Temp.
  Proof.
    rewrite /trans => trans_st_st'.
    case (trans_st_st' x y) => st_st'.
    -rewrite st_st'. auto.
    -rewrite /rule_existence in st_st'.
      +destruct st_st'; auto; by rewrite /=.
  Qed.

  Lemma si_tmp_tmp_parallel_false
    (st : State) (x y i : Z) (alt : bool) :
    i_safe st ->
    ((x > 0 \/ x < 0) /\
    st (x - 1) y = si true alt i /\
    st (x + 1) y = si true (negb alt) i) \/
    ((y > 0 \/ y < 0) /\
    st x (y - 1) = si true alt i /\
    st x (y + 1) = si true (negb alt) i) ->
    False.
  Proof.
    move=> i_sf.
    case; case=> ex_mid; case=> s0 s1.
    -apply i_sf in s0. apply i_sf in s1.
      case ex_mid => x0.
      +have: 0 <= x - 1. omega. have: 0 <= x + 1. omega.
        move /(Z.abs_eq (x + 1)) => x_eq0.
        move /(Z.abs_eq (x - 1)) => x_eq1.
        rewrite x_eq0 x_eq1 in s0 s1.
        specialize (Zdiv.Zminus_mod
        (x - 1 + Z.abs y - 2)
        (x + 1 + Z.abs y - 2)
        5).
        rewrite -s0 -s1.
        suff eq: x - 1 + Z.abs y - 2 - (x + 1 + Z.abs y - 2) = -2.
        *by rewrite eq Z.sub_diag.
        *omega.
      +have: x - 1 <= 0. omega. have: x + 1 <= 0. omega.
        move /(Z.abs_neq (x + 1)) => x_eq0.
        move /(Z.abs_neq (x - 1)) => x_eq1.
        rewrite x_eq0 x_eq1 in s0 s1.
        specialize (Zdiv.Zminus_mod
        (- (x - 1) + Z.abs y - 2)
        (- (x + 1) + Z.abs y - 2)
        5).
        rewrite -s0 -s1.
        suff eq: -(x - 1) + Z.abs y - 2 - (-(x + 1) + Z.abs y - 2) = 2.
        *by rewrite eq Z.sub_diag.
        *omega.
    -apply i_sf in s0. apply i_sf in s1.
      case ex_mid => y0.
      +have: 0 <= y - 1. omega. have: 0 <= y + 1. omega.
        move /(Z.abs_eq (y + 1)) => y_eq0.
        move /(Z.abs_eq (y - 1)) => y_eq1.
        rewrite y_eq0 y_eq1 in s0 s1.
        specialize (Zdiv.Zminus_mod
        (Z.abs x + (y - 1) - 2)
        (Z.abs x + (y + 1) - 2)
        5).
        rewrite -s0 -s1.
        suff eq: Z.abs x + (y - 1) - 2 - (Z.abs x + (y + 1) - 2) = -2.
        *by rewrite eq Z.sub_diag.
        *omega.
      +have: y - 1 <= 0. omega. have: y + 1 <= 0. omega.
        move /(Z.abs_neq (y + 1)) => y_eq0.
        move /(Z.abs_neq (y - 1)) => y_eq1.
        rewrite y_eq0 y_eq1 in s0 s1.
        specialize (Zdiv.Zminus_mod
        (Z.abs x - (y - 1) - 2)
        (Z.abs x - (y + 1) - 2)
        5).
        rewrite -s0 -s1.
        suff eq: Z.abs x -(y - 1) - 2 - (Z.abs x - (y + 1) - 2) = 2.
        *by rewrite eq Z.sub_diag.
        *omega.
  Qed.

  Lemma tmp_safe_diag_x
    (st : State) (x y : Z) :
    t_safe st /\ s_safe st ->
    x > 0 /\ c_type (st (x + 1) y) = Temp \/
    x < 0 /\ c_type (st (x - 1) y) = Temp ->
    (y > 0 -> c_type (st x (y - 1)) = Safe) /\
    (y < 0 -> c_type (st x (y + 1)) = Safe).
  Proof.
    case=> t_sf s_sf.
    case; case=> x0 c_st_xy.
    -apply t_sf in c_st_xy.
      case: c_st_xy => s0.
      +case: s0 => x1 s0.
        rewrite Z.add_simpl_r in s0.
        apply s_sf in s0.
        case: s0 => s0 s1.
        case: s1 => s1 s2.
        case: s2 => s2 s3.
        by split.
      +case: s0 => s0. omega.
      +case: s0 => s0.
        case: s0 => y0 s0.
        apply s_sf in s0.
        case: s0 => s0 s1.
        rewrite Z.add_simpl_r in s0.
        split.
        *move=> y1.
          apply s0. omega.
        *omega.
      +case: s0 => y0 s0.
        apply s_sf in s0.
        case: s0 => s0 s1.
        rewrite Z.add_simpl_r in s0.
        split.
        *omega.
        *move=> y1.
          apply s0. omega.
    -apply t_sf in c_st_xy.
      case: c_st_xy => s0.
      +omega.
      +case: s0 => s0.
        case: s0 => x1 s0.
        rewrite Z.sub_simpl_r in s0.
        apply s_sf in s0.
        case: s0 => s0 s1.
        case: s1 => s1 s2.
        case: s2 => s2 s3.
        by split.
      +case: s0 => s0.
        case: s0 => y0 s0.
        apply s_sf in s0.
        case: s0 => s0 s1.
        case: s1 => s1 s2.
        rewrite Z.sub_simpl_r in s1.
        split.
        *move=> y1.
        apply s1. omega.
        *omega.
      +case: s0 => y0 s0.
        apply s_sf in s0.
        case: s0 => s0 s1.
        case: s1 => s1 s2.
        rewrite Z.sub_simpl_r in s1.
        split.
        *omega.
        *move=> y1.
        apply s1. omega.
  Qed.

  Lemma tmp_safe_diag_y
    (st : State) (x y : Z) :
    t_safe st /\ s_safe st ->
    y > 0 /\ c_type (st x (y + 1)) = Temp \/
    y < 0 /\ c_type (st x (y - 1)) = Temp ->
    (x > 0 -> c_type (st (x - 1) y) = Safe) /\
    (x < 0 -> c_type (st (x + 1) y) = Safe).
  Proof.
    case=> t_sf s_sf.
    case; case=> y0 c_st_xy.
    -apply t_sf in c_st_xy.
      case: c_st_xy => s0.
      +case: s0 => x0 s0.
        apply s_sf in s0.
        case: s0 => s0 s1.
        case: s1 => s1 s2.
        case: s2 => s2 s3.
        rewrite Z.add_simpl_r in s2.
        split.
        *move=> x1.
          apply s2. omega.
        *omega.
      +case: s0 => s0.
        case: s0 => x0 s0.
        apply s_sf in s0.
        case: s0 => s0 s1.
        case: s1 => s1 s2.
        case: s2 => s2 s3.
        rewrite Z.add_simpl_r in s2.
        split.
        *omega.
        *move=> x1.
          apply s2. omega.
      +case: s0 => s0.
        case: s0 => y1 s0.
        rewrite Z.add_simpl_r in s0.
        apply s_sf in s0.
        case: s0 => s0 s1.
        case: s1 => s1 s2.
        case: s2 => s2 s3.
        by split.
      +omega.
    -apply t_sf in c_st_xy.
      case: c_st_xy => s0.
      +case: s0 => x0 s0.
        apply s_sf in s0.
        case: s0 => s0 s1.
        case: s1 => s1 s2.
        case: s2 => s2 s3.
        rewrite Z.sub_simpl_r in s3.
        split.
        *move=> x1.
          apply s3. omega.
        *omega.
      +case: s0 => s0.
        case: s0 => x0 s0.
        apply s_sf in s0.
        case: s0 => s0 s1.
        case: s1 => s1 s2.
        case: s2 => s2 s3.
        rewrite Z.sub_simpl_r in s3.
        split.
        *omega.
        *move=> x1.
        apply s3. omega.
      +case: s0 => s0. omega.
      +case: s0 => y1 s0.
        rewrite Z.sub_simpl_r in s0.
        apply s_sf in s0.
        case: s0 => s0 s1.
        case: s1 => s1 s2.
        case: s2 => s2 s3.
        by split.
  Qed.

  Close Scope list_scope.
  Close Scope Z_scope.

End ConcentricLemma.

