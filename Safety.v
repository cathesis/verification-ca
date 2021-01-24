Require Import Bool.
Require Import List.
Require Import Omega.
Require Import Classical.

From mathcomp
Require Import ssreflect.

Require Import Utility.
Require Import Cell.
Require Import Concentric.
Require Import Tactic.
Require Import Lemma.

Import ListNotations.

Section Safety.
  Open Scope Z_scope.
  Open Scope list_scope.

  Lemma safe_to_init_safe (st st' : State ) :
    safe st -> trans st st' -> init_safe st'.
  Proof.
    move=> sf tr.
    case: sf => init_sf. case=> t_sf s0. case: s0 => s_sf i_sf.
    rewrite /init_safe.
    rewrite /init_safe in init_sf.
    specialize (tr 0 0).
    case: tr => s0.
    -by rewrite s0 in init_sf.
    -rewrite /rule_existence in s0.
    move: s0 => ctrans.
    destruct_ctrans ctrans.
    +by rewrite -src in init_sf.
    +by rewrite -src in init_sf.
    +by rewrite -src in init_sf.
    +by rewrite -src in init_sf.
    +by rewrite -src in init_sf.
    +by rewrite -src in init_sf.
    +by rewrite -src in init_sf.
    +by rewrite -src in init_sf.
  Qed.

  Theorem safe_to_t_safe (st st' : State) :
    safe st -> trans st st' -> t_safe st'.
  Proof.
    move=> sf tr.
    case: sf => init_sf. case=> t_sf s0. case: s0 => s_sf i_sf.
    rewrite /t_safe => x y c_st'_xy.
    (* src = tmp *)
    specialize (trans_tmp_from_tmp_or_white st st' x y tr c_st'_xy).
    case=> c_st_xy.
    -apply t_sf in c_st_xy.
      case c_st_xy => H0.
      +case H0 => x0 c_st_xy1.
        *left. split.
          omega.
          apply (trans_safe_to_safe st st' (x - 1) y tr c_st_xy1).
      +case H0.
        *case=> x0 c_st_xy1.
          right. left. split.
            omega.
            apply (trans_safe_to_safe st st' (x + 1) y tr c_st_xy1).
      +case.
        *case=> y0 c_st_xy1.
          right. right. left. split.
            omega.
            apply (trans_safe_to_safe st st' x (y - 1) tr c_st_xy1).
      +case=> y0 c_st_xy1.
        *right. right. right. split.
          omega.
          apply (trans_safe_to_safe st st' x (y + 1) tr c_st_xy1).
    -case (tr x y).
      (* src = white *)
      +move=> st_st'.
        rewrite st_st' in c_st_xy.
        rewrite c_st_xy in c_st'_xy.
        done.
      +rewrite /rule_existence => ctrans.
        destruct_ctrans ctrans.
        *destruct in0 as [ nb | in0 ].
          (* Wtos *)
          have: c_type (st (x - 1) y) = Safe. by rewrite nb.
          move=> c_st_xy1.
          left. split.
          ineq.
          specialize (s_sf (x - 1) y c_st_xy1).
          case: s_sf => s0 s1. case: s1 => s1 s2.
          move /s1.
          simpl_arith.
          by rewrite c_st_xy.
          by apply (trans_safe_to_safe st st' (x - 1) y tr).

          destruct in0 as [ nb | in0 ]. 
          have: c_type (st (x + 1) y) = Safe. by rewrite nb.
          move=> c_st_xy1.
          right. left. split.
          ineq.
          specialize (s_sf (x + 1) y c_st_xy1).
          case: s_sf => s0 s1.
          move /s0.
          simpl_arith.
          by rewrite c_st_xy.
          by apply (trans_safe_to_safe st st' (x + 1) y tr).

          destruct in0 as [ nb | in0 ]. 
          have: c_type (st x (y - 1)) = Safe. by rewrite nb.
          move=> c_st_xy1.
          right. right. left. split.
          ineq.
          specialize (s_sf x (y - 1) c_st_xy1).
          case: s_sf => s0 s1. case: s1 => s1 s2. case: s2 => s2 s3.
          move /s3.
          simpl_arith.
          by rewrite c_st_xy.
          by apply (trans_safe_to_safe st st' x (y - 1) tr).

          destruct in0 as [ nb | in0 ]. 
          have: c_type (st x (y + 1)) = Safe. by rewrite nb.
          move=> c_st_xy1.
          right. right. right. split.
          ineq.
          specialize (s_sf x (y + 1) c_st_xy1).
          case: s_sf => s0 s1. case: s1 => s1 s2. case: s2 => s2 s3.
          move /s2.
          simpl_arith.
          by rewrite c_st_xy.
          by apply (trans_safe_to_safe st st' x (y + 1) tr).

          destruct in0.
        *destruct in0 as [ nb | in0 ].
          (* WtoTmp0 *)
          have: c_type (st (x - 1) y) = Safe. by rewrite nb.
          move=> c_st_xy1.
          left. split.
          ineq.
          specialize (s_sf (x - 1) y c_st_xy1).
          case: s_sf => s0 s1. case: s1 => s1 s2.
          move /s1.
          simpl_arith.
          by rewrite c_st_xy.
          by apply (trans_safe_to_safe st st' (x - 1) y tr).

          destruct in0 as [ nb | in0 ]. 
          have: c_type (st (x + 1) y) = Safe. by rewrite nb.
          move=> c_st_xy1.
          right. left. split.
          ineq.
          specialize (s_sf (x + 1) y c_st_xy1).
          case: s_sf => s0 s1.
          move /s0.
          simpl_arith.
          by rewrite c_st_xy.
          by apply (trans_safe_to_safe st st' (x + 1) y tr).

          destruct in0 as [ nb | in0 ]. 
          have: c_type (st x (y - 1)) = Safe. by rewrite nb.
          move=> c_st_xy1.
          right. right. left. split.
          ineq.
          specialize (s_sf x (y - 1) c_st_xy1).
          case: s_sf => s0 s1. case: s1 => s1 s2. case: s2 => s2 s3.
          move /s3.
          simpl_arith.
          by rewrite c_st_xy.
          by apply (trans_safe_to_safe st st' x (y - 1) tr).

          destruct in0 as [ nb | in0 ]. 
          have: c_type (st x (y + 1)) = Safe. by rewrite nb.
          move=> c_st_xy1.
          right. right. right. split.
          ineq.
          specialize (s_sf x (y + 1) c_st_xy1).
          case: s_sf => s0 s1. case: s1 => s1 s2. case: s2 => s2 s3.
          move /s2.
          simpl_arith.
          by rewrite c_st_xy.
          by apply (trans_safe_to_safe st st' x (y + 1) tr).

          destruct in0.
        *destruct in0 as [ nb | in0 ].
          (* WtoTmp1 *)
          have: c_type (st (x - 1) y) = Safe. by rewrite nb.
          move=> c_st_xy1.
          left. split.
          ineq.
          specialize (s_sf (x - 1) y c_st_xy1).
          case: s_sf => s0 s1. case: s1 => s1 s2.
          move /s1.
          simpl_arith.
          by rewrite c_st_xy.
          by apply (trans_safe_to_safe st st' (x - 1) y tr).

          destruct in0 as [ nb | in0 ]. 
          have: c_type (st (x + 1) y) = Safe. by rewrite nb.
          move=> c_st_xy1.
          right. left. split.
          ineq.
          specialize (s_sf (x + 1) y c_st_xy1).
          case: s_sf => s0 s1.
          move /s0.
          simpl_arith.
          by rewrite c_st_xy.
          by apply (trans_safe_to_safe st st' (x + 1) y tr).

          destruct in0 as [ nb | in0 ]. 
          have: c_type (st x (y - 1)) = Safe. by rewrite nb.
          move=> c_st_xy1.
          right. right. left. split.
          ineq.
          specialize (s_sf x (y - 1) c_st_xy1).
          case: s_sf => s0 s1. case: s1 => s1 s2. case: s2 => s2 s3.
          move /s3.
          simpl_arith.
          by rewrite c_st_xy.
          by apply (trans_safe_to_safe st st' x (y - 1) tr).

          destruct in0 as [ nb | in0 ]. 
          have: c_type (st x (y + 1)) = Safe. by rewrite nb.
          move=> c_st_xy1.
          right. right. right. split.
          ineq.
          specialize (s_sf x (y + 1) c_st_xy1).
          case: s_sf => s0 s1. case: s1 => s1 s2. case: s2 => s2 s3.
          move /s2.
          simpl_arith.
          by rewrite c_st_xy.
          by apply (trans_safe_to_safe st st' x (y + 1) tr).

          destruct in0.
        *rewrite -src in c_st_xy. by case tmp in c_st_xy.
          (* sAlt *)
        *rewrite -src in c_st_xy. by case tmp in c_st_xy.
          (* siAlt *)
        *by rewrite -src in c_st_xy.
          (* TmpToDef0 *)
        *by rewrite -src in c_st_xy.
          (* TmpToDef1 *)
        *by rewrite -src in c_st_xy.
          (* TmpToDef2 *)
          (* src = white *)
  Qed.

  Theorem safe_to_s_safe (st st' : State) :
    safe st -> trans st st' -> s_safe st'.
  Proof.
    move=> sf tr.
    case: sf => init_sf. case=> t_sf s0. case: s0 => s_sf i_sf.
    rewrite /t_safe => x y c_st'_xy.
    specialize (trans_safe_from_safe_or_tmp st st' x y tr c_st'_xy).
    case=> c_st_xy0.
    -apply s_sf in c_st_xy0.
      (* src = safe *)
      case: c_st_xy0 => s0 s1. case: s1 => s1 s2. case: s2 => s2 s3.
        split.
        +move /s0 => c_st_xy0.
          by apply (trans_safe_to_safe st st' (x - 1) y tr c_st_xy0).
        +split.
          move /s1 => c_st_xy0.
          by apply (trans_safe_to_safe st st' (x + 1) y tr c_st_xy0).
        +split.
          move /s2 => c_st_xy0.
          by apply (trans_safe_to_safe st st' x (y - 1) tr c_st_xy0).
        +move /s3 => c_st_xy0.
          by apply (trans_safe_to_safe st st' x (y + 1) tr c_st_xy0).
    -have: c_type (st x y) = Temp. by [].
      have ts_sf: t_safe st /\ s_safe st. by [].
      have tr': trans st st'. by [].
      move /t_sf => s0.
      (* src = tmp *)
      split.
      (* 0 *)
        +move=> x0.
          case: s0  => s0.
          *case: s0 => x1 c_st_xy1.
            by apply (trans_safe_to_safe st st' (x - 1) y tr c_st_xy1).
          *case: s0 => s0. omega.
          *case: s0 => s0.
            case: s0 => y0 c_st_xy1.
            have ex_mid_x: x > 0 \/ x < 0. omega.
            have ex_mid_y: y > 0 \/ y < 0. omega.
            case (tr' x y) => [ st_st' | ctrans ].
            rewrite st_st' in c_st_xy0.
            by rewrite c_st'_xy in c_st_xy0.
            rewrite /rule_existence in ctrans.
            destruct_ctrans ctrans.
            (* Wtos *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp0 *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp1 *)
            by rewrite -src in c_st_xy0.
            (* sAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (s_alt_consistency st st' x y tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* siAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (si_alt_consistency st st' x y i tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* TmpToDef0 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            case: in1 => [ nb10 | in1 ].
            rewrite nb00 in nb10.
            by case alt' in nb10.
            case: in1 => [ nb11 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 alt' i_sf) => s0.
            case: s0.
            by left.
            case: in1 => [ nb12 | in1 ].
            apply t_sf in c_st_xy0.
            case: c_st_xy0 => s0.
            case: s0 => s0 s1.
            apply (trans_safe_to_safe st st' (x - 1) y tr s1).
            case: s0 => s0. omega.
            case: s0.
            case=> s0 s1.
            by rewrite nb12 in s1.
            move=> s0. omega.
            case: in1 => [ nb13 | in1 ].
            have: c_type (st x (y + 1)) = Temp. by rewrite nb13.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. left.
            split. omega. by rewrite nb13.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x - 1) y tr (s0 x0)).
            case in1.

            case: in0 => [ nb01 | in0 ].
            have c_st_xy2: c_type (st (x + 1) y) = Temp. by rewrite nb01.
            case: in1 => [ nb10 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 (negb alt') i_sf) => s0.
            case: s0.
            left.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb11 | in1 ].
            rewrite nb01 in nb11.
            by case alt' in nb11.
            case: in1 => [ nb12 | in1 ].
            by rewrite nb12 in c_st_xy1.
            case: in1 => [ nb13 | in1 ].
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. left. split.
            by [].
            by rewrite nb13.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' (x - 1) y tr (s0 x0)).
            case in1.

            case: in0 => [ nb02 | in0 ].
            by rewrite nb02 in c_st_xy1.
            case: in0 => [ nb03 | in0 ].
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. left. split.
            by [].
            by rewrite nb03.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' (x - 1) y tr (s0 x0)).
            case in0.
            (* TmpToDef1 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            case: in1 => [ nb10 | in1 ].
            rewrite nb00 in nb10.
            by case alt' in nb10.
            case: in1 => [ nb11 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) alt' i_sf) => s0.
            case: s0.
            by left.
            case: in1 => [ nb12 | in1 ].
            apply t_sf in c_st_xy0.
            case: c_st_xy0 => s0.
            case: s0 => s0 s1.
            apply (trans_safe_to_safe st st' (x - 1) y tr s1).
            case: s0 => s0. omega.
            case: s0.
            case=> s0 s1.
            by rewrite nb12 in s1.
            move=> s0. omega.
            case: in1 => [ nb13 | in1 ].
            have: c_type (st x (y + 1)) = Temp. by rewrite nb13.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. left.
            split. omega. by rewrite nb13.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x - 1) y tr (s0 x0)).
            case in1.

            case: in0 => [ nb01 | in0 ].
            have c_st_xy2: c_type (st (x + 1) y) = Temp. by rewrite nb01.
            case: in1 => [ nb10 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) (negb alt') i_sf) => s0.
            case: s0.
            left.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb11 | in1 ].
            rewrite nb01 in nb11.
            by case alt' in nb11.
            case: in1 => [ nb12 | in1 ].
            by rewrite nb12 in c_st_xy1.
            case: in1 => [ nb13 | in1 ].
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. left. split.
            by [].
            by rewrite nb13.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' (x - 1) y tr (s0 x0)).
            case in1.

            case: in0 => [ nb02 | in0 ].
            by rewrite nb02 in c_st_xy1.
            case: in0 => [ nb03 | in0 ].
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. left. split.
            by [].
            by rewrite nb03.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' (x - 1) y tr (s0 x0)).
            case in0.
            (* TmpToDef2 *)
            have x1: x + 1 > 0. omega.
            have y1: y + 1 > 0. omega.
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            have c_st_xy2: c_type (st (x - 1) y) = Safe. by rewrite nb00.
            apply (trans_safe_to_safe st st' (x - 1) y tr c_st_xy2).

            case: in0 => [ nb01 | in0 ].
            have c_st_xy2: c_type (st (x + 1) y) = Safe. by rewrite nb01.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            specialize (s0 x1).
            rewrite Z.add_simpl_r in s0.
            by rewrite c_st_xy0 in s0.
            case: in0 => [ nb02 | in0 ].
            case: in1 => [ nb10 | in1 ].
            have c_st_xy2: c_type (st (x - 1) y) = Safe. by rewrite nb10.
            apply (trans_safe_to_safe st st' (x - 1) y tr c_st_xy2).
            case: in1 => [ nb11 | in1 ].
            have c_st_xy2: c_type (st (x + 1) y) = Safe. by rewrite nb11.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            specialize (s0 x1).
            rewrite Z.add_simpl_r in s0.
            by rewrite c_st_xy0 in s0.
            case: in1 => [ nb12 | in1 ].
            rewrite nb02 in nb12.
            by case alt' in nb12.
            case: in1 => [ nb13 | in1 ].
            have c_st_xy2: c_type (st x (y + 1)) = Safe. by rewrite nb13.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s2 y1).
            rewrite Z.add_simpl_r in s2.
            by rewrite c_st_xy0 in s2.
            case in1.

            case: in0 => [ nb03 | in0 ].
            have c_st_xy2: c_type (st x (y + 1)) = Safe. by rewrite nb03.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s2 y1).
            rewrite Z.add_simpl_r in s2.
            by rewrite c_st_xy0 in s2.

            case in0.

          *case: s0 => y0 c_st_xy1.
            have ex_mid_x: x > 0 \/ x < 0. omega.
            have ex_mid_y: y > 0 \/ y < 0. omega.
            case (tr' x y) => [ st_st' | ctrans ].
            rewrite st_st' in c_st_xy0.
            by rewrite c_st'_xy in c_st_xy0.
            rewrite /rule_existence in ctrans.
            inversion ctrans as [
            cs in0 src l0 dst |
            cs alt in0 src l0 dst |
            cs alt i in0 src l0 dst |
            cs tmp alt src l0 dst |
            cs tmp alt i src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst
            ].
            (* Wtos *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp0 *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp1 *)
            by rewrite -src in c_st_xy0.
            (* sAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (s_alt_consistency st st' x y tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* siAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (si_alt_consistency st st' x y i tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* TmpToDef0 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            case: in1 => [ nb10 | in1 ].
            rewrite nb00 in nb10.
            by case alt' in nb10.
            case: in1 => [ nb11 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 alt' i_sf) => s0.
            case: s0.
            by left.
            case: in1 => [ nb12 | in1 ].
            have: c_type (st x (y - 1)) = Temp. by rewrite nb12.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb12.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x - 1) y tr (s0 x0)). 
            case: in1 => [ nb13 | in1 ].
            rewrite nb13 in c_st_xy1. by [].
            case in1.

            case: in0 => [ nb01 | in0 ].
            case: in1 => [ nb10 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 (negb alt') i_sf) => s0.
            case: s0.
            left.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb11 | in1 ].
            rewrite nb01 in nb11.
            by case alt' in nb11.
            case: in1 => [ nb12 | in1 ].
            have: c_type (st x (y - 1)) = Temp. by rewrite nb12.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb12.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x - 1) y tr (s0 x0)).
            case: in1 => [ nb12 | in1 ].
            by rewrite nb12 in c_st_xy1.
            case in1.

            case: in0 => [ nb02 | in0 ].
            have: c_type (st x (y - 1)) = Temp. by rewrite nb02.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. omega.
            by rewrite nb02.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x - 1) y tr (s0 x0)).

            case: in0 => [ nb03 | in0 ].
            by rewrite nb03 in c_st_xy1.

            case in0.

            (* TmpToDef1 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            case: in1 => [ nb10 | in1 ].
            rewrite nb00 in nb10.
            by case alt' in nb10.
            case: in1 => [ nb11 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) alt' i_sf) => s0.
            case: s0.
            by left.
            case: in1 => [ nb12 | in1 ].
            have: c_type (st x (y - 1)) = Temp. by rewrite nb12.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb12.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x - 1) y tr (s0 x0)).
            case: in1 => [ nb13 | in1 ].
            rewrite nb13 in c_st_xy1. by [].
            case in1.

            case: in0 => [ nb01 | in0 ].
            case: in1 => [ nb10 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) (negb alt') i_sf) => s0.
            case: s0.
            left.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb11 | in1 ].
            rewrite nb01 in nb11.
            by case alt' in nb11.
            case: in1 => [ nb12 | in1 ].
            have: c_type (st x (y - 1)) = Temp. by rewrite nb12.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb12.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x - 1) y tr (s0 x0)).
            case: in1 => [ nb12 | in1 ].
            by rewrite nb12 in c_st_xy1.
            case in1.

            case: in0 => [ nb02 | in0 ].
            have: c_type (st x (y - 1)) = Temp. by rewrite nb02.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. omega.
            by rewrite nb02.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x - 1) y tr (s0 x0)).

            case: in0 => [ nb03 | in0 ].
            by rewrite nb03 in c_st_xy1.

            case in0.

            (* TmpToDef2 *)
            have x1: x + 1 > 0. omega.
            have y1: y - 1 < 0. omega.
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            have c_st_xy2: c_type (st (x - 1) y) = Safe. by rewrite nb00.
            apply (trans_safe_to_safe st st' (x - 1) y tr c_st_xy2).

            case: in0 => [ nb01 | in0 ].
            have c_st_xy2: c_type (st (x + 1) y) = Safe. by rewrite nb01.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            specialize (s0 x1).
            rewrite Z.add_simpl_r in s0.
            by rewrite c_st_xy0 in s0.
            case: in0 => [ nb02 | in0 ].
            have c_st_xy2: c_type (st x (y - 1)) = Safe. by rewrite nb02.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s3 y1).
            rewrite Z.sub_simpl_r in s3.
            by rewrite c_st_xy0 in s3.
            case: in0 => [ nb03 | in0 ].
            case: in1 => [ nb10 | in1 ].
            have c_st_xy2: c_type (st (x - 1) y) = Safe. by rewrite nb10.
            apply (trans_safe_to_safe st st' (x - 1) y tr c_st_xy2).
            case: in1 => [ nb11 | in1 ].
            have c_st_xy2: c_type (st (x + 1) y) = Safe. by rewrite nb11.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            specialize (s0 x1).
            rewrite Z.add_simpl_r in s0.
            by rewrite c_st_xy0 in s0.
            case: in1 => [ nb12 | in1 ].
            have c_st_xy2: c_type (st x (y - 1)) = Safe. by rewrite nb12.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s3 y1).
            rewrite Z.sub_simpl_r in s3.
            by rewrite c_st_xy0 in s3.
            case: in1 => [ nb13 | in1 ].
            rewrite nb03 in nb13.
            by case alt' in nb13.
            case in1.

            case in0.

    -split.
      (* 1 *)
        +move=> x0.
          *case: s0 => s0. omega.
          *case: s0.
            case=> x1 c_st_xy1.
            by apply (trans_safe_to_safe st st' (x + 1) y tr c_st_xy1).
          *case=> s0.
            case: s0 => y0 c_st_xy1.
            have ex_mid_x: x > 0 \/ x < 0. omega.
            have ex_mid_y: y > 0 \/ y < 0. omega.
            case (tr' x y) => [ st_st' | ctrans ].
            rewrite st_st' in c_st_xy0.
            by rewrite c_st'_xy in c_st_xy0.
            rewrite /rule_existence in ctrans.
            inversion ctrans as [
            cs in0 src l0 dst |
            cs alt in0 src l0 dst |
            cs alt i in0 src l0 dst |
            cs tmp alt src l0 dst |
            cs tmp alt i src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst
            ].
            (* Wtos *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp0 *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp1 *)
            by rewrite -src in c_st_xy0.
            (* sAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (s_alt_consistency st st' x y tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* siAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (si_alt_consistency st st' x y i tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* TmpToDef0 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            case: in1 => [ nb10 | in1 ].
            rewrite nb00 in nb10.
            by case alt' in nb10.
            case: in1 => [ nb11 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 alt' i_sf) => s0.
            case: s0.
            by left.
            case: in1 => [ nb12 | in1 ].
            apply t_sf in c_st_xy0.
            case: c_st_xy0 => s0. omega.
            case: s0.
            case=> x1 s1.
            apply (trans_safe_to_safe st st' (x + 1) y tr s1).
            case=> s0.
            case: s0 => y1 s1.
            by rewrite nb12 in s1.
            omega.
            case: in1 => [ nb13 | in1 ].
            have: c_type (st x (y + 1)) = Temp.
            by rewrite nb13.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. left.
            split. omega. by rewrite nb13.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x + 1) y tr (s1 x0)).
            case in1.

            case: in0 => [ nb01 | in0 ].
            have c_st_xy2: c_type (st (x + 1) y) = Temp. by rewrite nb01.
            case: in1 => [ nb10 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 (negb alt') i_sf) => s0.
            case: s0.
            left.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb11 | in1 ].
            rewrite nb01 in nb11.
            by case alt' in nb11.
            case: in1 => [ nb12 | in1 ].
            by rewrite nb12 in c_st_xy1.
            case: in1 => [ nb13 | in1 ].
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. left. split.
            by [].
            by rewrite nb13.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' (x + 1) y tr (s1 x0)).
            case in1.

            case: in0 => [ nb02 | in0 ].
            by rewrite nb02 in c_st_xy1.
            case: in0 => [ nb03 | in0 ].
            case: in1 => [ nb10 | in1 ].
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. left. split.
            by [].
            by rewrite nb03.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' (x + 1) y tr (s1 x0)).
            case: in1 => [ nb11 | in1 ].
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. left. split.
            by [].
            by rewrite nb03.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' (x + 1) y tr (s1 x0)).
            case: in1 => [ nb11 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 (negb alt') i_sf) => s0.
            case: s0.
            right. split.
            by [].
            split.
            by [].
            by rewrite negb_involutive.
            case: in1 => [ nb11 | in1 ].
            rewrite nb03 in nb11.
            by case alt' in nb11.
            case in1.
            
            case in0.
            (* TmpToDef1 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            case: in1 => [ nb10 | in1 ].
            rewrite nb00 in nb10.
            by case alt' in nb10.
            case: in1 => [ nb11 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) alt' i_sf) => s0.
            case: s0.
            by left.
            case: in1 => [ nb12 | in1 ].
            apply t_sf in c_st_xy0.
            case: c_st_xy0 => s0. omega.
            case: s0.
            case=> x1 s1.
            apply (trans_safe_to_safe st st' (x + 1) y tr s1).
            case=> s0.
            case: s0 => y1 s0.
            by rewrite nb12 in s0.
            omega.
            case: in1 => [ nb12 | in1 ].
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. left.
            split. omega. by rewrite nb12.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' (x + 1) y tr (s1 x0)).
            case in1.

            case: in0 => [ nb01 | in0 ].
            have c_st_xy2: c_type (st (x + 1) y) = Temp. by rewrite nb01.
            case: in1 => [ nb10 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) (negb alt') i_sf) => s0.
            case: s0.
            left.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb11 | in1 ].
            rewrite nb01 in nb11.
            by case alt' in nb11.
            case: in1 => [ nb12 | in1 ].
            by rewrite nb12 in c_st_xy1.
            case: in1 => [ nb13 | in1 ].
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. left. split.
            by [].
            by rewrite nb13.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' (x + 1) y tr (s1 x0)).
            case in1.

            case: in0 => [ nb02 | in0 ].
            by rewrite nb02 in c_st_xy1.
            case: in0 => [ nb03 | in0 ].
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. left. split.
            by [].
            by rewrite nb03.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' (x + 1) y tr (s1 x0)).
            case in0.
            (* TmpToDef2 *)
            have x1: x - 1 < 0. omega.
            have y1: y + 1 > 0. omega.
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            have c_st_xy2: c_type (st (x - 1) y) = Safe. by rewrite nb00.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            specialize (s1 x1).
            rewrite Z.sub_simpl_r in s1.
            by rewrite c_st_xy0 in s1.
            case: in0 => [ nb01 | in0 ].
            have c_st_xy2: c_type (st (x + 1) y) = Safe. by rewrite nb01.
            apply (trans_safe_to_safe st st' (x + 1) y tr c_st_xy2).
            case: in0 => [ nb02 | in0 ].
            case: in1 => [ nb10 | in1 ].
            have c_st_xy2: c_type (st (x - 1) y) = Safe. by rewrite nb10.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            specialize (s1 x1).
            rewrite Z.sub_simpl_r in s1.
            by rewrite c_st_xy0 in s1.
            case: in1 => [ nb11 | in1 ].
            have c_st_xy2: c_type (st (x + 1) y) = Safe. by rewrite nb11.
            apply (trans_safe_to_safe st st' (x + 1) y tr c_st_xy2).
            case: in1 => [ nb12 | in1 ].
            rewrite nb02 in nb12.
            by case alt' in nb12.
            case: in1 => [ nb13 | in1 ].
            have c_st_xy2: c_type (st x (y + 1)) = Safe. by rewrite nb13.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s2 y1).
            rewrite Z.add_simpl_r in s2.
            by rewrite c_st_xy0 in s2.
            case in1.

            case: in0 => [ nb03 | in0 ].
            have c_st_xy2: c_type (st x (y + 1)) = Safe. by rewrite nb03.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s2 y1).
            rewrite Z.add_simpl_r in s2.
            by rewrite c_st_xy0 in s2.

            case in0.

          *case: s0 => y0 c_st_xy1.
            have ex_mid_x: x > 0 \/ x < 0. omega.
            have ex_mid_y: y > 0 \/ y < 0. omega.
            case (tr' x y) => [ st_st' | ctrans ].
            rewrite st_st' in c_st_xy0.
            by rewrite c_st'_xy in c_st_xy0.
            rewrite /rule_existence in ctrans.
            inversion ctrans as [
            cs in0 src l0 dst |
            cs alt in0 src l0 dst |
            cs alt i in0 src l0 dst |
            cs tmp alt src l0 dst |
            cs tmp alt i src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst
            ].
            (* Wtos *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp0 *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp1 *)
            by rewrite -src in c_st_xy0.
            (* sAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (s_alt_consistency st st' x y tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* siAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (si_alt_consistency st st' x y i tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* TmpToDef0 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            case: in1 => [ nb10 | in1 ].
            rewrite nb00 in nb10.
            by case alt' in nb10.
            case: in1 => [ nb11 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 alt' i_sf) => s0.
            case: s0.
            by left.
            case: in1 => [ nb12 | in1 ].
            have: c_type (st x (y - 1)) = Temp. by rewrite nb12.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb12.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x + 1) y tr (s1 x0)).
            case: in1 => [ nb13 | in1 ].
            rewrite nb13 in c_st_xy1. by [].
            case in1.

            case: in0 => [ nb01 | in0 ].
            case: in1 => [ nb10 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 (negb alt') i_sf) => s0.
            case: s0.
            left.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb11 | in1 ].
            rewrite nb01 in nb11.
            by case alt' in nb11.
            case: in1 => [ nb12 | in1 ].
            have: c_type (st x (y - 1)) = Temp. by rewrite nb12.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb12.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x + 1) y tr (s1 x0)).
            case: in1 => [ nb12 | in1 ].
            by rewrite nb12 in c_st_xy1.
            case in1.

            case: in0 => [ nb02 | in0 ].
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb02.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' (x + 1) y tr (s1 x0)).

            case: in0 => [ nb03 | in0 ].
            by rewrite nb03 in c_st_xy1.

            case in0.

            (* TmpToDef1 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            case: in1 => [ nb10 | in1 ].
            rewrite nb00 in nb10.
            by case alt' in nb10.
            case: in1 => [ nb11 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) alt' i_sf) => s0.
            case: s0.
            by left.
            case: in1 => [ nb12 | in1 ].
            have: c_type (st x (y - 1)) = Temp. by rewrite nb12.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb12.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x + 1) y tr (s1 x0)).
            case: in1 => [ nb13 | in1 ].
            rewrite nb13 in c_st_xy1. by [].
            case in1.

            case: in0 => [ nb01 | in0 ].
            case: in1 => [ nb10 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) (negb alt') i_sf) => s0.
            case: s0.
            left.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb11 | in1 ].
            rewrite nb01 in nb11.
            by case alt' in nb11.
            case: in1 => [ nb12 | in1 ].
            have: c_type (st x (y - 1)) = Temp. by rewrite nb12.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb12.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x + 1) y tr (s1 x0)).
            case: in1 => [ nb13 | in1 ].
            by rewrite nb13 in c_st_xy1.
            case in1.

            case: in0 => [ nb02 | in0 ].
            have: c_type (st x (y - 1)) = Temp. by rewrite nb02.
            specialize (tmp_safe_diag_y st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. omega.
            by rewrite nb02.
            move=> s0 s1 s2.
            apply (trans_safe_to_safe st st' (x + 1) y tr (s1 x0)).

            case: in0 => [ nb03 | in0 ].
            by rewrite nb03 in c_st_xy1.

            case in0.

            (* TmpToDef2 *)
            have x1: x - 1 < 0. omega.
            have y1: y - 1 < 0. omega.
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            have c_st_xy2: c_type (st (x - 1) y) = Safe. by rewrite nb00.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            specialize (s1 x1).
            rewrite Z.sub_simpl_r in s1.
            by rewrite c_st_xy0 in s1.

            case: in0 => [ nb01 | in0 ].
            have c_st_xy2: c_type (st (x + 1) y) = Safe. by rewrite nb01.
            apply (trans_safe_to_safe st st' (x + 1) y tr c_st_xy2).

            case: in0 => [ nb02 | in0 ].
            have c_st_xy2: c_type (st x (y - 1)) = Safe. by rewrite nb02.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s3 y1).
            rewrite Z.sub_simpl_r in s3.
            by rewrite c_st_xy0 in s3.

            case: in0 => [ nb03 | in0 ].
            case: in1 => [ nb10 | in1 ].
            have c_st_xy2: c_type (st (x - 1) y) = Safe. by rewrite nb10.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            specialize (s1 x1).
            rewrite Z.sub_simpl_r in s1.
            by rewrite c_st_xy0 in s1.
            case: in1 => [ nb11 | in1 ].
            have c_st_xy2: c_type (st (x + 1) y) = Safe. by rewrite nb11.
            apply (trans_safe_to_safe st st' (x + 1) y tr c_st_xy2).
            case: in1 => [ nb12 | in1 ].
            have c_st_xy2: c_type (st x (y - 1)) = Safe. by rewrite nb12.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s3 y1).
            rewrite Z.sub_simpl_r in s3.
            by rewrite c_st_xy0 in s3.
            case: in1 => [ nb13 | in1 ].
            rewrite nb03 in nb13.
            by case alt' in nb13.
            case in1.

            case in0.

    -split.
      (* 2 *)
        +move=> y0.
          case: s0  => s0.
          *case: s0 => x0 c_st_xy1.
            have ex_mid_x: x > 0 \/ x < 0. omega.
            have ex_mid_y: y > 0 \/ y < 0. omega.
            case (tr' x y) => [ st_st' | ctrans ].
            rewrite st_st' in c_st_xy0.
            by rewrite c_st'_xy in c_st_xy0.
            rewrite /rule_existence in ctrans.
            inversion ctrans as [
            cs in0 src l0 dst |
            cs alt in0 src l0 dst |
            cs alt i in0 src l0 dst |
            cs tmp alt src l0 dst |
            cs tmp alt i src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst
            ].
            (* Wtos *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp0 *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp1 *)
            by rewrite -src in c_st_xy0.
            (* sAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (s_alt_consistency st st' x y tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* siAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (si_alt_consistency st st' x y i tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* TmpToDef0 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            by rewrite nb00 in c_st_xy1.

            case: in0 => [ nb01 | in0 ].
            have s0: c_type (st (x + 1) y) = Temp. rewrite nb01. by [].
            diag st.
            (*
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s1.
            case: s1. left. split.
            by [].
            by rewrite nb01.
            move=> s1 s2.
            by apply (trans_safe_to_safe st st' x (y - 1) tr (s1 y0)).
             *)
            by apply (trans_safe_to_safe st st' x (y - 1) tr s0).
            by apply (trans_safe_to_safe st st' x (y - 1) tr s0).

            case: in0 => [ nb02 | in0 ].
            case: in1 => [ nb10 | in1 ].
            by rewrite nb10 in c_st_xy1.
            case: in1 => [ nb11 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. left. split.
            by [].
            by rewrite nb11.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y - 1) tr (s0 y0)).
            case: in1 => [ nb12 | in1 ].
            rewrite nb02 in nb12.
            by case alt' in nb12.
            case: in1 => [ nb13 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 alt' i_sf) => s0.
            case: s0.
            by right.
            case in1.

            case: in0 => [ nb03 | in0 ].
            case: in1 => [ nb10 | in1 ].
            by rewrite nb10 in c_st_xy1.
            case: in1 => [ nb11 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. left. split.
            by [].
            by rewrite nb11.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y - 1) tr (s0 y0)).
            case: in1 => [ nb12 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 (negb alt') i_sf) => s0.
            case: s0.
            right. split.
            by [].
            split.
            by [].
            by rewrite negb_involutive.
            case: in1 => [ nb13 | in1 ].
            rewrite nb03 in nb13.
            by case alt' in nb13.
            case in1.

            case in0.
            (* TmpToDef1 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            by rewrite nb00 in c_st_xy1.

            case: in0 => [ nb01 | in0 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. left. split.
            by [].
            by rewrite nb01.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y - 1) tr (s0 y0)).

            case: in0 => [ nb02 | in0 ].
            case: in1 => [ nb10 | in1 ].
            by rewrite nb10 in c_st_xy1.
            case: in1 => [ nb11 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. left. split.
            by [].
            by rewrite nb11.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y - 1) tr (s0 y0)).
            case: in1 => [ nb12 | in1 ].
            rewrite nb02 in nb12.
            by case alt' in nb12.
            case: in1 => [ nb13 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) alt' i_sf) => s0.
            case: s0.
            by right.
            case in1.

            case: in0 => [ nb03 | in0 ].
            case: in1 => [ nb10 | in1 ].
            by rewrite nb10 in c_st_xy1.
            case: in1 => [ nb11 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. left.
            split. omega. by rewrite nb11.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y - 1) tr (s0 y0)).
            case: in1 => [ nb12 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) (negb alt') i_sf) => s0.
            case: s0.
            right.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb13 | in1 ].
            rewrite nb03 in nb13.
            by case alt' in nb13.
            case in1.

            case in0.
            (* TmpToDef2 *)
            have x1: x + 1 > 0. omega.
            have y1: y + 1 > 0. omega.
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            case: in1 => [ nb10 | in1 ].
            rewrite nb00 in nb10.
            by case alt' in nb10.
            case: in1 => [ nb11 | in1 ].
            have c_st_xy2: c_type (st (x + 1) y) = Safe. by rewrite nb11.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            specialize (s0 x1).
            rewrite Z.add_simpl_r in s0.
            by rewrite c_st_xy0 in s0.
            case: in1 => [ nb12 | in1 ].
            have c_st_xy2: c_type (st x (y - 1)) = Safe. by rewrite nb12.
            apply (trans_safe_to_safe st st' x (y - 1) tr c_st_xy2).
            case: in1 => [ nb13 | in1 ].
            have c_st_xy2: c_type (st x (y + 1)) = Safe. by rewrite nb13.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s2 y1).
            rewrite Z.add_simpl_r in s2.
            by rewrite c_st_xy0 in s2.
            case in1.

            case: in0 => [ nb01 | in0 ].
            have c_st_xy2: c_type (st (x + 1) y) = Safe. by rewrite nb01.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            specialize (s0 x1).
            rewrite Z.add_simpl_r in s0.
            by rewrite c_st_xy0 in s0.

            case: in0 => [ nb02 | in0 ].
            have c_st_xy2: c_type (st x (y - 1)) = Safe. by rewrite nb02.
            by apply (trans_safe_to_safe st st' x (y - 1) tr c_st_xy2).

            case: in0 => [ nb03 | in0 ].
            have c_st_xy2: c_type (st x (y + 1)) = Safe. by rewrite nb03.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s2 y1).
            rewrite Z.add_simpl_r in s2.
            by rewrite c_st_xy0 in s2.

            case in0.

          *case: s0.
            case=> x0 c_st_xy1.
            have ex_mid_x: x > 0 \/ x < 0. omega.
            have ex_mid_y: y > 0 \/ y < 0. omega.
            case (tr' x y) => [ st_st' | ctrans ].
            rewrite st_st' in c_st_xy0.
            by rewrite c_st'_xy in c_st_xy0.
            rewrite /rule_existence in ctrans.
            inversion ctrans as [
            cs in0 src l0 dst |
            cs alt in0 src l0 dst |
            cs alt i in0 src l0 dst |
            cs tmp alt src l0 dst |
            cs tmp alt i src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst
            ].
            (* Wtos *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp0 *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp1 *)
            by rewrite -src in c_st_xy0.
            (* sAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (s_alt_consistency st st' x y tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* siAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (si_alt_consistency st st' x y i tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* TmpToDef0 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb00.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y - 1) tr (s0 y0)).

            case: in0 => [ nb01 | in0 ].
            by rewrite nb01 in c_st_xy1.

            case: in0 => [ nb02 | in0 ].
            case: in1 => [ nb10 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb10.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y - 1) tr (s0 y0)).
            case: in1 => [ nb11 | in1 ].
            by rewrite nb11 in c_st_xy1.
            case: in1 => [ nb12 | in1 ].
            rewrite nb02 in nb12.
            by case alt' in nb12.
            case: in1 => [ nb13 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 alt' i_sf) => s0.
            case: s0.
            by right.
            case in1.

            case: in0 => [ nb03 | in0 ].
            case: in1 => [ nb10 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. omega.
            by rewrite nb10.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y - 1) tr (s0 y0)).
            case: in1 => [ nb11 | in1 ].
            by rewrite nb11 in c_st_xy1.
            case: in1 => [ nb12 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 (negb alt') i_sf) => s0.
            case: s0.
            right.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb13 | in1 ].
            rewrite nb03 in nb13.
            by case alt' in nb13.
            case in1.

            case in0.
            (* TmpToDef1 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb00.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y - 1) tr (s0 y0)).

            case: in0 => [ nb01 | in0 ].
            by rewrite nb01 in c_st_xy1.

            case: in0 => [ nb02 | in0 ].
            case: in1 => [ nb10 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb10.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y - 1) tr (s0 y0)).
            case: in1 => [ nb11 | in1 ].
            by rewrite nb11 in c_st_xy1.
            case: in1 => [ nb12 | in1 ].
            rewrite nb02 in nb12.
            by case alt' in nb12.
            case: in1 => [ nb13 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) alt' i_sf) => s0.
            case: s0.
            by right.
            case in1.

            case: in0 => [ nb03 | in0 ].
            case: in1 => [ nb10 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. omega.
            by rewrite nb10.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y - 1) tr (s0 y0)).
            case: in1 => [ nb11 | in1 ].
            by rewrite nb11 in c_st_xy1.
            case: in1 => [ nb12 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) (negb alt') i_sf) => s0.
            case: s0.
            right.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb13 | in1 ].
            rewrite nb03 in nb13.
            by case alt' in nb13.
            case in1.

            case in0.
            (* TmpToDef2 *)
            have x1: x - 1 < 0. omega.
            have y1: y + 1 > 0. omega.
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            have c_st_xy2: c_type (st (x - 1) y) = Safe. by rewrite nb00.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            specialize (s1 x1).
            rewrite Z.sub_simpl_r in s1.
            by rewrite c_st_xy0 in s1.

            case: in0 => [ nb01 | in0 ].
            case: in1 => [ nb10 | in1 ].
            have c_st_xy2: c_type (st (x - 1) y) = Safe. by rewrite nb10.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            specialize (s1 x1).
            rewrite Z.sub_simpl_r in s1.
            by rewrite c_st_xy0 in s1.
            case: in1 => [ nb11 | in1 ].
            rewrite nb01 in nb11.
            by case alt' in nb11.
            case: in1 => [ nb12 | in1 ].
            have c_st_xy2: c_type (st x (y - 1)) = Safe. by rewrite nb12.
            apply (trans_safe_to_safe st st' x (y - 1) tr c_st_xy2).
            case: in1 => [ nb13 | in1 ].
            have c_st_xy2: c_type (st x (y + 1)) = Safe. by rewrite nb13.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s2 y1).
            rewrite Z.add_simpl_r in s2.
            by rewrite c_st_xy0 in s2.
            case in1.

            case: in0 => [ nb02 | in0 ].
            have c_st_xy2: c_type (st x (y - 1)) = Safe. by rewrite nb02.
            apply (trans_safe_to_safe st st' x (y - 1) tr c_st_xy2).
            case: in0 => [ nb03 | in0 ].
            have c_st_xy2: c_type (st x (y + 1)) = Safe. by rewrite nb03.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s2 y1).
            rewrite Z.add_simpl_r in s2.
            by rewrite c_st_xy0 in s2.

            case in0.

          *case=> s0.
            case: s0 => y1 c_st_xy1.
            apply (trans_safe_to_safe st st' x (y - 1) tr c_st_xy1).
            omega.
      (* 3 *)
    -move=> y0.
        +case: s0  => s0.
          *case: s0 => x0 c_st_xy1.
            have ex_mid_x: x > 0 \/ x < 0. omega.
            have ex_mid_y: y > 0 \/ y < 0. omega.
            case (tr' x y) => [ st_st' | ctrans ].
            rewrite st_st' in c_st_xy0.
            by rewrite c_st'_xy in c_st_xy0.
            rewrite /rule_existence in ctrans.
            inversion ctrans as [
            cs in0 src l0 dst |
            cs alt in0 src l0 dst |
            cs alt i in0 src l0 dst |
            cs tmp alt src l0 dst |
            cs tmp alt i src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst
            ].
            (* Wtos *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp0 *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp1 *)
            by rewrite -src in c_st_xy0.
            (* sAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (s_alt_consistency st st' x y tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* siAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (si_alt_consistency st st' x y i tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* TmpToDef0 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            by rewrite nb00 in c_st_xy1.
            case: in0 => [ nb01 | in0 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. left.
            split. omega. by rewrite nb01.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y + 1) tr (s1 y0)).

            case: in0 => [ nb02 | in0 ].
            case: in1 => [ nb10 | in1 ].
            rewrite nb10 in c_st_xy1.
            by case alt' in c_st_xy1.
            case: in1 => [ nb11 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. left.
            split. omega. by rewrite nb11.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y + 1) tr (s1 y0)).
            case: in1 => [ nb12 | in1 ].
            rewrite nb02 in nb12.
            by case alt' in nb12.
            case: in1 => [ nb13 | in1 ].

            specialize (si_tmp_tmp_parallel_false st x y 0 alt' i_sf) => s0.
            case: s0.
            by right.
            case in1.

            case: in0 => [ nb03 | in0 ].
            case: in1 => [ nb10 | in1 ].
            by rewrite nb10 in c_st_xy1.
            case: in1 => [ nb11 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. left.
            split. omega. by rewrite nb11.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y + 1) tr (s1 y0)).
            case: in1 => [ nb12 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 (negb alt') i_sf) => s0.
            case: s0.
            right.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb13 | in1 ].
            rewrite nb03 in nb13.
            by case alt' in nb13.
            case in1.
            
            case in0.
            (* TmpToDef1 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            by rewrite nb00 in c_st_xy1.

            case: in0 => [ nb01 | in0 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. left.
            split. omega. by rewrite nb01.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y + 1) tr (s1 y0)).

            case: in0 => [ nb02 | in0 ].
            case: in1 => [ nb10 | in1 ].
            by rewrite nb10 in c_st_xy1.
            case: in1 => [ nb11 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. left.
            split. omega. by rewrite nb11.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y + 1) tr (s1 y0)).
            case: in1 => [ nb12 | in1 ].
            rewrite nb02 in nb12.
            by case alt' in nb12.
            case: in1 => [ nb13 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) alt' i_sf) => s0.
            case: s0.
            by right.
            case in1.

            case: in0 => [ nb03 | in0 ].
            case: in1 => [ nb10 | in1 ].
            by rewrite nb10 in c_st_xy1.
            case: in1 => [ nb11 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. left.
            split. omega. by rewrite nb11.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y + 1) tr (s1 y0)).
            case: in1 => [ nb12 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) (negb alt') i_sf) => s0.
            case: s0.
            right.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb13 | in1 ].
            rewrite nb03 in nb13.
            by case alt' in nb13.
            case in1.

            case in0.
            (* TmpToDef2 *)
            have x1: x + 1 > 0. omega.
            have y1: y - 1 < 0. omega.
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            case: in1 => [ nb10 | in1 ].
            rewrite nb00 in nb10.
            by case alt' in nb10.
            case: in1 => [ nb11 | in1 ].
            have c_st_xy2: c_type (st (x + 1) y) = Safe. by rewrite nb11.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            specialize (s0 x1).
            rewrite Z.add_simpl_r in s0.
            by rewrite c_st_xy0 in s0.
            case: in1 => [ nb12 | in1 ].
            have c_st_xy2: c_type (st x (y - 1)) = Safe. by rewrite nb12.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s3 y1).
            rewrite Z.sub_simpl_r in s3.
            by rewrite c_st_xy0 in s3.
            case: in1 => [ nb13 | in1 ].
            have c_st_xy2: c_type (st x (y + 1)) = Safe. by rewrite nb13.
            apply (trans_safe_to_safe st st' x (y + 1) tr c_st_xy2).
            case in1.

            case: in0 => [ nb01 | in0 ].
            have c_st_xy2: c_type (st (x + 1) y) = Safe. by rewrite nb01.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            specialize (s0 x1).
            rewrite Z.add_simpl_r in s0.
            by rewrite c_st_xy0 in s0.

            case: in0 => [ nb02 | in0 ].
            have c_st_xy2: c_type (st x (y - 1)) = Safe. by rewrite nb02.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s3 y1).
            rewrite Z.sub_simpl_r in s3.
            by rewrite c_st_xy0 in s3.

            case: in0 => [ nb03 | in0 ].
            have c_st_xy2: c_type (st x (y + 1)) = Safe. by rewrite nb03.
            by apply (trans_safe_to_safe st st' x (y + 1) tr c_st_xy2).
            
            case in0.
          *case: s0 => s0.
            case: s0 => x0 c_st_xy1.
            have ex_mid_x: x > 0 \/ x < 0. omega.
            have ex_mid_y: y > 0 \/ y < 0. omega.
            case (tr' x y) => [ st_st' | ctrans ].
            rewrite st_st' in c_st_xy0.
            by rewrite c_st'_xy in c_st_xy0.
            rewrite /rule_existence in ctrans.
            inversion ctrans as [
            cs in0 src l0 dst |
            cs alt in0 src l0 dst |
            cs alt i in0 src l0 dst |
            cs tmp alt src l0 dst |
            cs tmp alt i src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst |
            cs alt alt' i in0 src l0 dst
            ].
            (* Wtos *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp0 *)
            by rewrite -src in c_st_xy0.
            (* WtoTmp1 *)
            by rewrite -src in c_st_xy0.
            (* sAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (s_alt_consistency st st' x y tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* siAlt *)
            apply eq_sym in src.
            apply eq_sym in dst.
            specialize (si_alt_consistency st st' x y i tmp alt src dst).
            by rewrite c_st'_xy c_st_xy0.
            (* TmpToDef0 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb00.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y + 1) tr (s1 y0)).

            case: in0 => [ nb01 | in0 ].
            by rewrite nb01 in c_st_xy1.

            case: in0 => [ nb02 | in0 ].
            case: in1 => [ nb10 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb10.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y + 1) tr (s1 y0)).
            case: in1 => [ nb11 | in1 ].
            by rewrite nb11 in c_st_xy1.
            case: in1 => [ nb12 | in1 ].
            rewrite nb02 in nb12.
            by case alt' in nb12.
            case: in1 => [ nb13 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 alt' i_sf) => s0.
            case: s0.
            by right.
            case in1.

            case: in0 => [ nb03 | in0 ].
            case: in1 => [ nb10 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb10.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y + 1) tr (s1 y0)).
            case: in1 => [ nb11 | in1 ].
            by rewrite nb11 in c_st_xy1.
            case: in1 => [ nb12 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y 0 (negb alt') i_sf) => s0.
            case: s0.
            right.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb13 | in1 ].
            rewrite nb03 in nb13.
            by case alt' in nb13.
            case in1.

            case in0.
            (* TmpToDef1 *)
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb00.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y + 1) tr (s1 y0)).

            case: in0 => [ nb01 | in0 ].
            by rewrite nb01 in c_st_xy1.

            case: in0 => [ nb02 | in0 ].
            case: in1 => [ nb10 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb10.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y + 1) tr (s1 y0)).
            case: in1 => [ nb11 | in1 ].
            by rewrite nb11 in c_st_xy1.
            case: in1 => [ nb12 | in1 ].
            rewrite nb02 in nb12.
            by case alt' in nb12.
            case: in1 => [ nb13 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) alt' i_sf) => s0.
            case: s0.
            by right.
            case in1.

            case: in0 => [ nb03 | in0 ].
            case: in1 => [ nb10 | in1 ].
            specialize (tmp_safe_diag_x st x y ts_sf).
            move=> s0.
            case: s0. right.
            split. by [].
            by rewrite nb10.
            move=> s0 s1.
            apply (trans_safe_to_safe st st' x (y + 1) tr (s1 y0)).
            case: in1 => [ nb11 | in1 ].
            by rewrite nb11 in c_st_xy1.
            case: in1 => [ nb12 | in1 ].
            specialize (si_tmp_tmp_parallel_false st x y (succ i) (negb alt') i_sf) => s0.
            case: s0.
            right.
            split. by [].
            split. by [].
            by rewrite negb_involutive.
            case: in1 => [ nb13 | in1 ].
            rewrite nb03 in nb13.
            by case alt' in nb13.
            case in1.

            case in0.
            (* TmpToDef2 *)
            have x1: x - 1 < 0. omega.
            have y1: y - 1 < 0. omega.
            case: in0 => in0 in1.
            case: in0 => [ nb00 | in0 ].
            have c_st_xy2: c_type (st (x - 1) y) = Safe. by rewrite nb00.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            specialize (s1 x1).
            rewrite Z.sub_simpl_r in s1.
            by rewrite c_st_xy0 in s1.

            case: in0 => [ nb01 | in0 ].
            case: in1 => [ nb10 | in1 ].
            have c_st_xy2: c_type (st (x - 1) y) = Safe. by rewrite nb10.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            specialize (s1 x1).
            rewrite Z.sub_simpl_r in s1.
            by rewrite c_st_xy0 in s1.
            case: in1 => [ nb11 | in1 ].
            rewrite nb01 in nb11.
            by case alt' in nb11.
            case: in1 => [ nb12 | in1 ].
            have c_st_xy2: c_type (st x (y - 1)) = Safe. by rewrite nb12.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s3 y1).
            rewrite Z.sub_simpl_r in s3.
            by rewrite c_st_xy0 in s3.
            case: in1 => [ nb13 | in1 ].
            have c_st_xy2: c_type (st x (y + 1)) = Safe. by rewrite nb13.
            by apply (trans_safe_to_safe st st' x (y + 1) tr c_st_xy2).
            case in1.

            case: in0 => [ nb02 | in0 ].
            have c_st_xy2: c_type (st x (y - 1)) = Safe. by rewrite nb02.
            apply s_sf in c_st_xy2.
            case: c_st_xy2 => s0 s1.
            case: s1 => s1 s2.
            case: s2 => s2 s3.
            specialize (s3 y1).
            rewrite Z.sub_simpl_r in s3.
            by rewrite c_st_xy0 in s3.

            case: in0 => [ nb03 | in0 ].
            have c_st_xy2: c_type (st x (y + 1)) = Safe. by rewrite nb03.
            by apply (trans_safe_to_safe st st' x (y + 1) tr c_st_xy2).

            case in0.
          *case: s0 => s0. omega.
          *case: s0 => y1 c_st_xy1.
            apply (trans_safe_to_safe st st' x (y + 1) tr c_st_xy1).
  Qed.

  Theorem safe_to_i_safe (st st' : State) :
    safe st -> trans st st' -> i_safe st'.
  Proof.
    move=> sf tr.
    case: sf => init_sf. case=> t_sf s0. case: s0 => s_sf i_sf.
    move=> x y i tmp alt.
    rewrite /trans in tr.
    specialize (tr x y).
    case: tr => s0.
    -specialize (i_sf x y i tmp alt).
      by rewrite s0 in i_sf.
    -rewrite /rule_existence in s0.
      move: s0 => ctrans.
      inversion ctrans as [
      cs in0 src l0 dst |
      cs alt0 in0 src l0 dst |
      cs alt0 i0 in0 src l0 dst |
      cs tmp0 alt0 src l0 dst |
      cs tmp0 alt0 i0 src l0 dst |
      cs alt0 alt0' i0 in0 src l0 dst |
      cs alt0 alt0' i0 in0 src l0 dst |
      cs alt0 alt0' i0 in0 src l0 dst
      ].
      +split. (* Wtos *)
        *by [].
        *split.
          case: in0 => [ nb00 | in0 ].
          specialize (i_sf (x - 1) y i tmp alt). 
          case: i_sf => s1 s2.
          specialize (s1 nb00).
          omega.
          case: in0 => [ nb00 | in0 ].
          specialize (i_sf (x + 1) y i tmp alt). 
          case: i_sf => s1 s2.
          specialize (s1 nb00).
          omega.
          case: in0 => [ nb00 | in0 ].
          specialize (i_sf x (y - 1) i tmp alt). 
          case: i_sf => s1 s2.
          specialize (s1 nb00).
          omega.
          case: in0 => [ nb00 | in0 ].
          specialize (i_sf x (y + 1) i tmp alt). 
          case: i_sf => s1 s2.
          specialize (s1 nb00).
          omega.
          case in0.
        *by [].
      +split. (* WtoTmp0 *)
        *by [].
        *split. by [].
        *move=> s0.
          induction i.
          case: in0 => [ nb00 | in0 ].
          case: (i_sf (x - 1) y 0 false alt0) => s1 s2.
          case: s2 => s2 s3.
          apply s2 in nb00.
          case nb00 => s4.
          case: s4 => s4 s5.
          have s6: x = 2. omega.
          rewrite s5 s6.
          by rewrite /=.
          case: s4 => s4.
          case: s4 => s4 s5.
          have s6: x = 0. omega.
          rewrite s5 s6 in src.
          by rewrite init_sf in src.
          case: s4 => s4.
          case: s4 => s4 s5.
          have s6: x = 1. omega.
          rewrite s5 s6.
          by rewrite /=.
          case: s4 => s4.
          move=> s5.
          have s6: x = 1. omega.
          rewrite s5 s6.
          by rewrite /=.
          case: in0 => [ nb00 | in0 ].
          case: (i_sf (x + 1) y 0 false alt0) => s1 s2.
          case: s2 => s2 s3.
          apply s2 in nb00.
          case nb00 => s4.
          case: s4 => s4 s5.
          have s6: x = 0. omega.
          rewrite s5 s6 in src.
          by rewrite init_sf in src.
          case: s4 => s4.
          case: s4 => s4 s5.
          have s6: x = -2. omega.
          rewrite s5 s6.
          by rewrite /=.
          case: s4 => s4.
          case: s4 => s4 s5.
          have s6: x = -1. omega.
          rewrite s5 s6.
          by rewrite /=.
          case: s4 => s4 s5.
          have s6: x = -1. omega.
          rewrite s5 s6.
          by rewrite /=.
          case: in0 => [ nb00 | in0 ].
          case: (i_sf x (y - 1) 0 false alt0) => s1 s2.
          case: s2 => s2 s3.
          apply s2 in nb00.
          case nb00 => s4.
          case: s4 => s4 s5.
          have s6: y = 1. omega.
          rewrite s4 s6.
          by rewrite /=.
          case: s4 => s4.
          case: s4 => s4 s5.
          have s6: y = 1. omega.
          rewrite s4 s6.
          by rewrite /=.
          case: s4 => s4.
          case: s4 => s4 s5.
          have s6: y = 2. omega.
          rewrite s4 s6.
          by rewrite /=.
          case: s4 => s4 s5.
          have s6: y = 0. omega.
          rewrite s4 s6 in src.
          by rewrite init_sf in src.
          case: in0 => [ nb00 | in0 ].
          case: (i_sf x (y + 1) 0 false alt0) => s1 s2.
          case: s2 => s2 s3.
          apply s2 in nb00.
          case nb00 => s4.
          case: s4 => s4 s5.
          have s6: y = -1. omega.
          rewrite s4 s6.
          by rewrite /=.
          case: s4 => s4.
          case: s4 => s4 s5.
          have s6: y = -1. omega.
          rewrite s4 s6.
          by rewrite /=.
          case: s4 => s4.
          case: s4 => s4 s5.
          have s6: y = 0. omega.
          rewrite s4 s6 in src.
          by rewrite init_sf in src.
          case: s4 => s4 s5.
          have s6: y = -2. omega.
          rewrite s4 s6.
          by rewrite /=.
          case in0.
          by [].
          by [].
      +split. (* WtoTmp1 *)
        *by [].
        *split. by [].
        *move=> s0.
          inversion s0.
          case: in0 => [ nb00 | in0 ].
          have s1: x - 1 < 0 -> False.
          move=> s1.
          have s2: c_type (st (x - 1) y) = Safe. by rewrite nb00.
          case: (s_sf (x - 1) y s2) => s3 s4.
          case: s4 => s4 s5.
          specialize (s4 s1).
          rewrite Z.sub_simpl_r in s4.
          by rewrite -src in s4.
          case: (i_sf (x - 1) y i0 false alt0) => s2 s3.
          case: s3 => s3 s4.
          apply s4 in nb00.
          rewrite /succ in s0.
          have s5: Z.abs (x - 1) + 1 = Z.abs x. 
          move: (Znot_lt_ge (x - 1) 0 s1) => s5.
          have s6: 0 <= x - 1. omega.
          move: (Z.abs_eq (x - 1) s6) => s7.
          rewrite s7.
          rewrite Z.sub_simpl_r.
          have s8: 0 < x. omega.
          by specialize (abs_eq_gt x s8).
          move: (Zdiv.Zplus_mod_idemp_l (Z.abs (x - 1) + Z.abs y - 2) 1 5) => s6.
          rewrite -nb00 in s6.
          have s7: Z.abs (x - 1) + Z.abs y - 2 + 1 = Z.abs (x - 1) + 1 + Z.abs y - 2. omega.
          rewrite s7 in s6.
          by rewrite s5 in s6.
          case: in0 => [ nb00 | in0 ].
          have s1: x + 1 > 0 -> False.
          move=> s1.
          have s2: c_type (st (x + 1) y) = Safe. by rewrite nb00.
          case: (s_sf (x + 1) y s2) => s3 s4.
          specialize (s3 s1).
          rewrite Z.add_simpl_r in s3.
          by rewrite -src in s3.
          case: (i_sf (x + 1) y i0 false alt0) => s2 s3.
          case: s3 => s3 s4.
          apply s4 in nb00.
          rewrite /succ in s0.
          have s5: Z.abs (x + 1) + 1 = Z.abs x. 
          move: (Znot_gt_le (x + 1) 0 s1) => s5.
          move: (Z.abs_neq (x + 1) s5) => s6.
          rewrite s6.
          have s7: - (x + 1) + 1 = -x. omega.
          rewrite s7.
          have s8: x < 0. omega.
          by specialize (abs_eq_lt x s8).
          move: (Zdiv.Zplus_mod_idemp_l (Z.abs (x + 1) + Z.abs y - 2) 1 5) => s6.
          rewrite -nb00 in s6.
          have s7: Z.abs (x + 1) + Z.abs y - 2 + 1 = Z.abs (x + 1) + 1 + Z.abs y - 2. omega.
          rewrite s7 in s6.
          by rewrite s5 in s6.
          case: in0 => [ nb00 | in0 ].
          have s1: y - 1 < 0 -> False.
          move=> s1.
          have s2: c_type (st x (y - 1)) = Safe. by rewrite nb00.
          case: (s_sf x (y - 1) s2) => s3 s4.
          case: s4 => s4 s5.
          case: s5 => s5 s6.
          specialize (s6 s1).
          rewrite Z.sub_simpl_r in s6.
          by rewrite -src in s6.
          case: (i_sf x (y - 1) i0 false alt0) => s2 s3.
          case: s3 => s3 s4.
          apply s4 in nb00.
          rewrite /succ in s0.
          have s5: Z.abs (y - 1) + 1 = Z.abs y.
          move: (Znot_lt_ge (y - 1) 0 s1) => s5.
          have s6: 0 <= y - 1. omega.
          move: (Z.abs_eq (y - 1) s6) => s7.
          rewrite s7.
          rewrite Z.sub_simpl_r.
          have s8: 0 < y. omega.
          by specialize (abs_eq_gt y s8).
          move: (Zdiv.Zplus_mod_idemp_l (Z.abs x + Z.abs (y - 1) - 2) 1 5) => s6.
          rewrite -nb00 in s6.
          have s7: Z.abs x + Z.abs (y - 1) - 2 + 1 = Z.abs x + (Z.abs (y - 1) + 1) - 2. omega.
          rewrite s7 in s6.
          by rewrite s5 in s6.
          case: in0 => [ nb00 | in0 ].
          have s1: y + 1 > 0 -> False.
          move=> s1.
          have s2: c_type (st x (y + 1)) = Safe. by rewrite nb00.
          case: (s_sf x (y + 1) s2) => s3 s4.
          case: s4 => s4 s5.
          case: s5 => s5 s6.
          specialize (s5 s1).
          rewrite Z.add_simpl_r in s5.
          by rewrite -src in s5.
          case: (i_sf x (y + 1) i0 false alt0) => s2 s3.
          case: s3 => s3 s4.
          apply s4 in nb00.
          rewrite /succ in s0.
          have s5: Z.abs (y + 1) + 1 = Z.abs y.
          move: (Znot_gt_le (y + 1) 0 s1) => s5.
          move: (Z.abs_neq (y + 1) s5) => s6.
          rewrite s6.
          have s7: - (y + 1) + 1 = -y. omega.
          rewrite s7.
          have s8: y < 0. omega.
          by specialize (abs_eq_lt y s8).
          move: (Zdiv.Zplus_mod_idemp_l (Z.abs x + Z.abs (y + 1) - 2) 1 5) => s6.
          rewrite -nb00 in s6.
          have s7: Z.abs x + Z.abs (y + 1) - 2 + 1 = Z.abs x + (Z.abs (y + 1) + 1) - 2. omega.
          rewrite s7 in s6.
          by rewrite s5 in s6.
          case in0.
      +split. (* sAlt *)
        *by [].
        *split.
          move=> s0.
          case: (i_sf x y i tmp0 alt0) => s1 s2.
          case: s2 => s2 s3.
          by apply s2.
        *by [].
      +split. (* siAlt *)
        *by [].
        *split. by [].
        *move=> s0.
          inversion s0.
          case: (i_sf x y i0 tmp0 alt0) => s1 s2.
          case: s2 => s2 s3.
          rewrite -H2.
          by apply s3.
      +split. (* TmpToDef0 *)
        *by [].
        *split.
          move=> s0.
          case: (i_sf x y i true alt0) => s1 s2.
          case: s2 => s2 s3.
          by apply s2.
        *by [].
      +split. (* TmpToDef1 *)
        *by [].
        *split. by [].
        *move=> s0.
          inversion s0.
          case: (i_sf x y i0 true alt0) => s1 s2.
          case: s2 => s2 s3.
          rewrite -H2.
          by apply s3.
      +split. (* TmpToDef2 *)
        *by [].
        *split. by [].
        *move=> s0.
          inversion s0.
          case: (i_sf x y i0 true alt0) => s1 s2.
          case: s2 => s2 s3.
          rewrite -H2.
          by apply s3.
  Qed.

  Theorem safety (st st' : State) : safe st /\ trans st st' -> safe st'.
  Proof.
    case=> sf tr.
    rewrite /safe.
    split.
    -apply (safe_to_init_safe st st' sf tr).
    -split.
      +apply (safe_to_t_safe st st' sf tr).
    -split.
      +apply (safe_to_s_safe st st' sf tr).
    -apply (safe_to_i_safe st st' sf tr).
  Qed.

  Close Scope list_scope.
  Close Scope Z_scope.

End Safety.
