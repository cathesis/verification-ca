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
Require Import Safety.
Require Import Rotation.

Import ListNotations.

Section Fairness.
  Open Scope Z_scope.
  Open Scope list_scope.

  Theorem safety_subset (ul : list Coord) (st st' : State)
    : pre_cnd ul st /\ trans st st' -> pre_cnd ul st'.
  Proof.
    case=> pre tr.
    case: pre => sf sc.
    split.
    -apply (safety st st').
      split.
      +by [].
      +by [].
    -induction ul.
      +by constructor.
      +case: sc => [ s0 | x y res s0 s1 sc ].
        *by [].
        *inversion s0.
          rewrite -H1 in sc.
          apply IHul in sc.
          right with x y res.
          by [].
          case: s1 => s1.
          left.
          apply (trans_safe_to_safe st st' x y tr s1).
          apply (trans_tmp_to_tmp_or_safe st st' x y tr s1).
          by rewrite -H1.
  Qed.

  Theorem axis_fair (x y : Z) :
    forall (r : Run) (n : Z),
    ValidRun r ->
    n > 0 ->
    fair r (axis_coords n) (pre_cnd (axis_coords n)) axis_safe ->
    exists (st' : State),
    InRun st' r /\ axis_safe (map_coord st' (axis_coords n)).
  Proof.
    move=> r n vr n0 fr.
    apply fr.
    -by [].
    -move=> st s0.
      case: s0 => ir pre.
      rewrite /axis_coords in fr pre.
      case: pre => sf s0.
      simpl.
      rewrite /axis_coords.
      destruct (c_type (st n 0)) as [] eqn:s1.
      (*** (n, 0) = White ***)
      +case: s0 => [ s0 | x0 y0 res0 ].
        *by [].
        *move=> s2 s3 sc0.
          inversion s2.
          rewrite -H2 in sc0.
          case: sc0 => [ s0 | x1 y1 res1 ].
          by [].
          move=> s4 s5 sc1.
          inversion s4.
          subst.
          case: s5 => s5.
          by rewrite s5 in s1.
          by rewrite s5 in s1.
      (*** (n, 0) = Temp ***)
      +case: s0 => [ s0 | x0 y0 res0 ].
        *by [].
        *move=> s2 s3 sc0.
          inversion s2.
          rewrite -H2 in sc0.
          case: s3 => s0.
          subst.
          (** (n, 1) = Safe **)
          apply sf in s0.
          simpl in s0.
          case: s0 => s0 s3.
          case: s3 => s3 s4.
          case: s4 => s4 s5.
          have s6: 1 > 0. omega.
          apply s4 in s6.
          by rewrite s6 in s1.
          (** (n, 1) = Temp **)
          case: sc0 => [ s3 | x1 y1 res1 ].
          by [].
          move=> s3 s4 sc1.
          inversion s3.
          subst.
          case: s4 => s4.
          by rewrite s4 in s1.
          clear s4.
          case: sc1 => [ s4 | x2 y2 res2 ].
          by [].
          move=> s4 s5 sc2.
          inversion s4.
          subst.
          case: s5 => s5.
          (* (n, -1) = Safe *)
          apply sf in s5.
          simpl in s5.
          case: s5 => s5 s6.
          case: s6 => s6 s7.
          case: s7 => s7 s8.
          have s9: -1 < 0. omega.
          apply s8 in s9.
          by rewrite s8 in s1.
          remember x2 as n.
          clear sc2 s2 s3 s4.
          (* (n, -1) = Temp *)
          move: s0 s1 s5 => c0 c1 c2.
          apply temp_imply in c0.
          apply temp_imply in c1.
          apply temp_imply in c2.
          have sf': safe st. by [].
          rewrite /safe in sf.
          case: sf => ini_sf sf.
          case: sf => t_sf sf.
          case: sf => s_sf i_sf.
          clear ini_sf t_sf s_sf.
          have i_sf': i_safe st. by [].
          destruct c0, H.
          specialize (i_sf n 1 x1 true x0).
          case: i_sf => s3 s4.
          case: s4 => s4 s5.
          case: H => s6.
          apply s4 in s6.
          case: s6 => s6.
          omega.
          case: s6 => s6.
          omega.
          case: s6 => s6.
          omega.
          omega.
          destruct c2, H.
          specialize (i_sf' n (-1) x4 true x3).
          case: i_sf' => s7 s8.
          case: s8 => s8 s9.
          case: H => s10.
          apply s8 in s10.
          case: s10 => s10.
          omega.
          case: s10 => s10.
          omega.
          case: s10 => s10.
          omega.
          omega.
          specialize (s5 s6).
          specialize (s9 s10).
          rewrite (Z.abs_opp 1) in s9.
          rewrite -s9 in s5.
          rewrite -s5 in s10.
          clear s3 s4 s5 s7 s8 s9.
          destruct c1, H.
          case: H => s11.
          move: s6 s11 s10 => c0 c1 c2.
          (* st n 0 = s true x5 *)
          case x0, x3.
          (* x0, x3 = true, true *)
          exists [ si true false x1; s false false; si true true x1 ].

          split.
          right with [ si true false x1; s true x5; si true true x1 ].
          rewrite /trans_ss.
          move=> st_src s0.
          case: s0 => s0 s1.
          remember (si_temp_st st_src true false n 1 x1) as st_dst.
          exists st_dst.
          simpl.
          inversion s1.
          clear s1.
          split.
          rewrite Heqst_dst/si_temp_st.
          rewrite Z.eqb_refl.
          rewrite -H0 -H1 -H2 c1 c2.
          by simpl.
          have tr: trans st_src st_dst.
          rewrite /trans/rule_existence.
          move=> x0 y0.
          specialize (classic (x0 = n /\ y0 = 1)).
          case=> s2.
          case: s2 => s10 s11.
          right.
          rewrite s10 s11 -H0 c0 Heqst_dst.
          rewrite /si_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          constructor.
          left.
          apply not_and_or in s2.
          case: s2 => s2.
          apply Z.eqb_neq in s2.
          rewrite Heqst_dst.
          rewrite /si_temp_st.
          by rewrite s2.
          apply Z.eqb_neq in s2.
          rewrite Heqst_dst.
          rewrite /si_temp_st.
          rewrite s2.
          by rewrite andb_false_r.
          split.
          by [].
          split.
          apply (safety_subset (axis_coords n) st_src st_dst).
          split. by []. by [].

          move=> x0 y0 s1.
          apply not_or_and in s1.
          case: s1 => s1 s2.
          apply not_or_and in s2.
          case: s2 => s2 s3.
          apply not_or_and in s3.
          case: s3 => s3 s4.
          clear s4.
          rewrite Heqst_dst/si_temp_st.
          apply eqp_neq in s1.
          case: s1 => s1.
          rewrite Z.eqb_sym in s1.
          by rewrite s1.
          rewrite Z.eqb_sym in s1.
          rewrite s1.
          by rewrite andb_false_r.

          right with [ si true false x1; s false false; si true true x1 ].
          rewrite /trans_ss.
          move=> st_src s0.
          case: s0 => s0 s1.
          remember (s_temp_st st_src false false n 0) as st_dst.
          exists st_dst.
          simpl.
          inversion s1.
          clear s1.
          split.
          rewrite Heqst_dst/s_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          by rewrite -H0 -H2.
          have tr: trans st_src st_dst.
          rewrite /trans/rule_existence.
          move=> x0 y0.
          specialize (classic (x0 = n /\ y0 = 0)).
          case=> s2.
          case: s2 => s10 s11.
          right.
          rewrite s10 s11 -H1 Heqst_dst.
          rewrite /s_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          remember (map_coord st_src [((n - 1), 0); ((n + 1), 0); (n, (-1)); (n, 1)]) as s12.
          simpl in Heqs12.
          rewrite -H0 -H2 in Heqs12.
          have s1: pre_cnd (axis_coords n) st_src. by [].
          case: s1 => s1 s2.
          case: s1 => s1 s3.
          case: s3 => s3 s4.
          case: s4 => s4 s5.
          have s6: i_safe st_src. by [].
          specialize (s6 n 0 x1 true x5).
          case: s6 => s6 s7.
          case: s7 => s7 s8.
          have s9: st_src n 0 = s true x5. by rewrite H1.
          apply s7 in s9.
          specialize (s5 n 1 x1 true false).
          case: s5 => s5 s13.
          case: s13 => s13 s14.
          have s15: st_src n 1 = si true false x1. by rewrite H0.
          apply s14 in s15.
          case: s9 => s9.
          case: s9 => s9 s16.
          clear s16.
          rewrite s9 in s15.
          rewrite Z.abs_eq in s15.
          have s16: 1 + 1 - 2 = 0. by omega.
          rewrite s16 in s15.
          simpl in s15.
          rewrite Zdiv.Zmod_0_l in s15.
          rewrite s9.
          simpl.
          rewrite s9 in Heqs12.
          simpl in Heqs12.
          specialize (TmptoDef0 s12 x5 false 0).
          subst.
          clear s1 s2 s3 s4 s5 s6 s7 s8 s13 s14 s16.
          move=> s1.
          rewrite -H0 -H2.
          apply s1.
          rewrite H0 H2.
          split.
          right. right. right. by left.
          right. right. by left.
          by omega.

          case: s9 => s9.
          case: s9 => s9 s16.
          clear s16.
          rewrite s9 in s15.
          rewrite Z.abs_neq in s15.
          simpl in s15.
          rewrite Zdiv.Zmod_0_l in s15.
          rewrite s9.
          simpl.
          rewrite s9 in Heqs12.
          simpl in Heqs12.
          specialize (TmptoDef0 s12 x5 false 0).
          subst.
          clear s1 s2 s3 s4 s5 s6 s7 s8 s13 s14.
          move=> s1.
          rewrite -H0 -H2.
          apply s1.
          rewrite H0 H2.
          split.
          right. right. right. by left.
          right. right. by left.
          by omega.
          case: s9 => s9. by omega.
          by omega.
          apply not_and_or in s2.
          left.
          rewrite Heqst_dst/s_temp_st.
          case: s2 => s2.
          apply Z.eqb_neq in s2.
          by rewrite s2.
          apply Z.eqb_neq in s2.
          rewrite s2.
          by rewrite andb_false_r.

          split.
          by [].
          split.
          apply (safety_subset (axis_coords n) st_src st_dst).
          split.
          by [].
          by [].

          move=> x0 y0 s1.
          apply not_or_and in s1.
          case: s1 => s1 s2.
          apply not_or_and in s2.
          case: s2 => s2 s3.
          apply not_or_and in s3.
          case: s3 => s3 s4.
          clear s4.
          rewrite Heqst_dst/s_temp_st.
          apply eqp_neq in s2.
          case: s2 => s2.
          rewrite Z.eqb_sym in s2.
          by rewrite s2.
          rewrite Z.eqb_sym in s2.
          rewrite s2.
          by rewrite andb_false_r.

          by constructor.
          by rewrite /axis_safe.

          (* x0, x3 = true, false *)
          exists [ si true true x1; s false false; si true false x1 ].

          split.
          right with [ si true true x1; s false false; si true false x1 ].
          rewrite /trans_ss.
          move=> st_src s0.
          case: s0 => s0 s1.
          remember (s_temp_st st_src false false n 0) as st_dst.
          exists st_dst.
          simpl.
          inversion s1.
          clear s1.
          split.
          rewrite Heqst_dst/s_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          by rewrite -H0 -H2 c0 c2.
          have tr: trans st_src st_dst.
          rewrite /trans/rule_existence.
          move=> x0 y0.
          specialize (classic (x0 = n /\ y0 = 0)).
          case=> s2.
          case: s2 => s10 s11.
          right.
          rewrite s10 s11 -H1 Heqst_dst.
          rewrite /s_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          remember (map_coord st_src [((n - 1), 0); ((n + 1), 0); (n, (-1)); (n, 1)]) as s12.
          simpl in Heqs12.
          rewrite -H0 -H2 in Heqs12.
          have s1: pre_cnd (axis_coords n) st_src. by [].
          case: s1 => s1 s2.
          case: s1 => s1 s3.
          case: s3 => s3 s4.
          case: s4 => s4 s5.
          have s6: i_safe st_src. by [].
          specialize (s6 n 0 x1 true x5).
          case: s6 => s6 s7.
          case: s7 => s7 s8.
          have s9: st_src n 0 = s true x5. rewrite -H1. by rewrite c1.
          apply s7 in s9.
          specialize (s5 n (-1) x1 true false).
          case: s5 => s5 s13.
          case: s13 => s13 s14.
          have s15: st_src n (-1) = si true false x1. rewrite -H2. by rewrite c2.
          apply s14 in s15.
          case: s9 => s9.
          case: s9 => s9 s16.
          clear s16.
          rewrite s9 in s15.
          rewrite Z.abs_eq in s15.
          have s16: 1 + 1 - 2 = 0. by omega.
          rewrite s16 in s15.
          simpl in s15.
          rewrite Zdiv.Zmod_0_l in s15.
          rewrite s9.
          simpl.
          rewrite s9 in Heqs12.
          simpl in Heqs12.
          specialize (TmptoDef0 s12 x5 false 0).
          subst.
          clear s1 s2 s3 s4 s5 s6 s7 s8 s13 s14 s16.
          move=> s1.
          rewrite -H0 -H2.
          rewrite c1.
          apply s1.
          split.
          rewrite -c2.
          right. right. by left.
          rewrite (negb_involutive true).
          rewrite -c0.
          right. right. right. by left.
          by omega.

          case: s9 => s9.
          case: s9 => s9 s16.
          clear s16.
          rewrite s9 in s15.
          rewrite Z.abs_neq in s15.
          rewrite Zdiv.Zmod_0_l in s15.
          rewrite s9.
          simpl.
          rewrite s9 in Heqs12.
          simpl in Heqs12.
          specialize (TmptoDef0 s12 x5 false 0).
          subst.
          clear s1 s2 s3 s4 s5 s6 s7 s8 s13 s14.
          move=> s1.
          rewrite -H0 -H2.
          rewrite c1.
          apply s1.
          split.
          rewrite -c2.
          right. right. by left.
          rewrite (negb_involutive true).
          rewrite -c0.
          right. right. right. by left.
          by omega.

          case: s9 => s9. by omega.
          by omega.

          left.
          rewrite Heqst_dst/s_temp_st.
          apply not_and_or in s2.
          case: s2 => s2.
          apply Z.eqb_neq in s2.
          by rewrite s2.
          apply Z.eqb_neq in s2.
          rewrite s2.
          by rewrite andb_false_r.

          split.
          by [].
          split.
          apply (safety_subset (axis_coords n) st_src st_dst).
          split.
          by [].
          by [].

          move=> x0 y0 s1.
          apply not_or_and in s1.
          case: s1 => s1 s2.
          apply not_or_and in s2.
          case: s2 => s2 s3.
          apply not_or_and in s3.
          case: s3 => s3 s4.
          clear s4.
          rewrite Heqst_dst/s_temp_st.
          apply eqp_neq in s2.
          case: s2 => s2.
          rewrite Z.eqb_sym in s2.
          by rewrite s2.
          rewrite Z.eqb_sym in s2.
          rewrite s2.
          by rewrite andb_false_r.

          by constructor.
          by rewrite /axis_safe.

          (* x0, x3 = false, true *)
          exists [ si true false x1; s false false; si true true x1 ].

          split.
          right with [ si true false x1; s false false; si true true x1 ].
          rewrite /trans_ss.
          move=> st_src s0.
          case: s0 => s0 s1.
          remember (s_temp_st st_src false false n 0) as st_dst.
          exists st_dst.
          simpl.
          inversion s1.
          clear s1.
          split.
          rewrite Heqst_dst/s_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          by rewrite -H0 -H2 c0 c2.
          have tr: trans st_src st_dst.
          rewrite /trans/rule_existence.
          move=> x0 y0.
          specialize (classic (x0 = n /\ y0 = 0)).
          case=> s2.
          case: s2 => s10 s11.
          right.
          rewrite s10 s11 -H1 Heqst_dst.
          rewrite /s_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          remember (map_coord st_src [((n - 1), 0); ((n + 1), 0); (n, (-1)); (n, 1)]) as s12.
          simpl in Heqs12.
          rewrite -H0 -H2 in Heqs12.
          have s1: pre_cnd (axis_coords n) st_src. by [].
          case: s1 => s1 s2.
          case: s1 => s1 s3.
          case: s3 => s3 s4.
          case: s4 => s4 s5.
          have s6: i_safe st_src. by [].
          specialize (s6 n 0 x1 true x5).
          case: s6 => s6 s7.
          case: s7 => s7 s8.
          have s9: st_src n 0 = s true x5. rewrite -H1. by rewrite c1.
          apply s7 in s9.
          specialize (s5 n 1 x1 true false).
          case: s5 => s5 s13.
          case: s13 => s13 s14.
          have s15: st_src n 1 = si true false x1. rewrite -H0. by rewrite c0.
          apply s14 in s15.
          case: s9 => s9.
          case: s9 => s9 s16.
          clear s16.
          rewrite s9 in s15.
          rewrite Z.abs_eq in s15.
          have s16: 1 + 1 - 2 = 0. by omega.
          rewrite s16 in s15.
          simpl in s15.
          rewrite Zdiv.Zmod_0_l in s15.
          rewrite s9.
          simpl.
          rewrite s9 in Heqs12.
          simpl in Heqs12.
          specialize (TmptoDef0 s12 x5 false 0).
          subst.
          clear s1 s2 s3 s4 s5 s6 s7 s8 s13 s14 s16.
          move=> s1.
          rewrite -H0 -H2.
          rewrite c1.
          apply s1.
          split.
          rewrite -c0.
          right. right. right. by left.
          rewrite (negb_involutive true).
          rewrite -c2.
          right. right. by left.
          by omega.

          case: s9 => s9.
          case: s9 => s9 s16.
          clear s16.
          rewrite s9 in s15.
          rewrite Z.abs_neq in s15.
          rewrite Zdiv.Zmod_0_l in s15.
          rewrite s9.
          simpl.
          rewrite s9 in Heqs12.
          simpl in Heqs12.
          specialize (TmptoDef0 s12 x5 false 0).
          subst.
          clear s1 s2 s3 s4 s5 s6 s7 s8 s13 s14.
          move=> s1.
          rewrite -H0 -H2.
          rewrite c1.
          apply s1.
          split.
          rewrite -c0.
          right. right. by left.
          rewrite (negb_involutive true).
          rewrite -c2.
          right. right. by left.
          by omega.

          case: s9 => s9. by omega.
          by omega.

          left.
          rewrite Heqst_dst/s_temp_st.
          apply not_and_or in s2.
          case: s2 => s2.
          apply Z.eqb_neq in s2.
          by rewrite s2.
          apply Z.eqb_neq in s2.
          rewrite s2.
          by rewrite andb_false_r.

          split.
          by [].
          split.
          apply (safety_subset (axis_coords n) st_src st_dst).
          split.
          by [].
          by [].

          move=> x0 y0 s1.
          apply not_or_and in s1.
          case: s1 => s1 s2.
          apply not_or_and in s2.
          case: s2 => s2 s3.
          apply not_or_and in s3.
          case: s3 => s3 s4.
          clear s4.
          rewrite Heqst_dst/s_temp_st.
          apply eqp_neq in s2.
          case: s2 => s2.
          rewrite Z.eqb_sym in s2.
          by rewrite s2.
          rewrite Z.eqb_sym in s2.
          rewrite s2.
          by rewrite andb_false_r.

          by constructor.
          by rewrite /axis_safe.

          (* x0, x3 = false, false *)
          exists [ si true true x1; s false false; si true false x1 ].

          split.
          right with [ si true true x1; s true x5; si true false x1 ].
          rewrite /trans_ss.
          move=> st_src s0.
          case: s0 => s0 s1.
          remember (si_temp_st st_src true true n 1 x1) as st_dst.
          exists st_dst.
          simpl.
          inversion s1.
          clear s1.
          split.
          rewrite Heqst_dst/si_temp_st.
          rewrite Z.eqb_refl.
          rewrite -H0 -H1 -H2 c1 c2.
          by simpl.
          have tr: trans st_src st_dst.
          rewrite /trans/rule_existence.
          move=> x0 y0.
          specialize (classic (x0 = n /\ y0 = 1)).
          case=> s2.
          case: s2 => s10 s11.
          right.
          rewrite s10 s11 -H0 c0 Heqst_dst.
          rewrite /si_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          constructor.
          left.
          apply not_and_or in s2.
          case: s2 => s2.
          apply Z.eqb_neq in s2.
          rewrite Heqst_dst.
          rewrite /si_temp_st.
          by rewrite s2.
          apply Z.eqb_neq in s2.
          rewrite Heqst_dst.
          rewrite /si_temp_st.
          rewrite s2.
          by rewrite andb_false_r.
          split.
          by [].
          split.
          apply (safety_subset (axis_coords n) st_src st_dst).
          split. by []. by [].

          move=> x0 y0 s1.
          apply not_or_and in s1.
          case: s1 => s1 s2.
          apply not_or_and in s2.
          case: s2 => s2 s3.
          apply not_or_and in s3.
          case: s3 => s3 s4.
          clear s4.
          rewrite Heqst_dst/si_temp_st.
          apply eqp_neq in s1.
          case: s1 => s1.
          rewrite Z.eqb_sym in s1.
          by rewrite s1.
          rewrite Z.eqb_sym in s1.
          rewrite s1.
          by rewrite andb_false_r.

          right with [ si true true x1; s false false; si true false x1 ].
          rewrite /trans_ss.
          move=> st_src s0.
          case: s0 => s0 s1.
          remember (s_temp_st st_src false false n 0) as st_dst.
          exists st_dst.
          simpl.
          inversion s1.
          clear s1.
          split.
          rewrite Heqst_dst/s_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          by rewrite -H0 -H2.
          have tr: trans st_src st_dst.
          rewrite /trans/rule_existence.
          move=> x0 y0.
          specialize (classic (x0 = n /\ y0 = 0)).
          case=> s2.
          case: s2 => s10 s11.
          right.
          rewrite s10 s11 -H1 Heqst_dst.
          rewrite /s_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          remember (map_coord st_src [((n - 1), 0); ((n + 1), 0); (n, (-1)); (n, 1)]) as s12.
          simpl in Heqs12.
          rewrite -H0 -H2 in Heqs12.
          have s1: pre_cnd (axis_coords n) st_src. by [].
          case: s1 => s1 s2.
          case: s1 => s1 s3.
          case: s3 => s3 s4.
          case: s4 => s4 s5.
          have s6: i_safe st_src. by [].
          specialize (s6 n 0 x1 true x5).
          case: s6 => s6 s7.
          case: s7 => s7 s8.
          have s9: st_src n 0 = s true x5. by rewrite H1.
          apply s7 in s9.
          specialize (s5 n 1 x1 true true).
          case: s5 => s5 s13.
          case: s13 => s13 s14.
          have s15: st_src n 1 = si true true x1. by rewrite H0.
          apply s14 in s15.
          case: s9 => s9.
          case: s9 => s9 s16.
          clear s16.
          rewrite s9 in s15.
          rewrite Z.abs_eq in s15.
          have s16: 1 + 1 - 2 = 0. by omega.
          rewrite s16 in s15.
          simpl in s15.
          rewrite Zdiv.Zmod_0_l in s15.
          rewrite s9.
          simpl.
          rewrite s9 in Heqs12.
          simpl in Heqs12.
          specialize (TmptoDef0 s12 x5 false 0).
          subst.
          clear s1 s2 s3 s4 s5 s6 s7 s8 s13 s14 s16.
          move=> s1.
          rewrite -H0 -H2.
          apply s1.
          rewrite H0 H2.
          split.
          right. right. by left.
          right. right. right. by left.
          by omega.

          case: s9 => s9.
          case: s9 => s9 s16.
          clear s16.
          rewrite s9 in s15.
          rewrite Z.abs_neq in s15.
          simpl in s15.
          rewrite Zdiv.Zmod_0_l in s15.
          rewrite s9.
          simpl.
          rewrite s9 in Heqs12.
          simpl in Heqs12.
          specialize (TmptoDef0 s12 x5 false 0).
          subst.
          clear s1 s2 s3 s4 s5 s6 s7 s8 s13 s14.
          move=> s1.
          rewrite -H0 -H2.
          apply s1.
          rewrite H0 H2.
          split.
          right. right. right. by left.
          right. right. by left.
          by omega.
          case: s9 => s9. by omega.
          by omega.
          apply not_and_or in s2.
          left.
          rewrite Heqst_dst/s_temp_st.
          case: s2 => s2.
          apply Z.eqb_neq in s2.
          by rewrite s2.
          apply Z.eqb_neq in s2.
          rewrite s2.
          by rewrite andb_false_r.

          split.
          by [].
          split.
          apply (safety_subset (axis_coords n) st_src st_dst).
          split.
          by [].
          by [].

          move=> x0 y0 s1.
          apply not_or_and in s1.
          case: s1 => s1 s2.
          apply not_or_and in s2.
          case: s2 => s2 s3.
          apply not_or_and in s3.
          case: s3 => s3 s4.
          clear s4.
          rewrite Heqst_dst/s_temp_st.
          apply eqp_neq in s2.
          case: s2 => s2.
          rewrite Z.eqb_sym in s2.
          by rewrite s2.
          rewrite Z.eqb_sym in s2.
          rewrite s2.
          by rewrite andb_false_r.

          by constructor.
          by rewrite /axis_safe.

          (* st n 0 = si true x5 x6 *)
          move: s6 s11 s10 => c0 c1 c2.
          case x0, x3.
          (* x0, x3 = true, true *)
          exists [ si true false x1; si false false x6; si true true x1 ].

          split.
          right with [ si true false x1; si true x5 x6; si true true x1 ].
          rewrite /trans_ss.
          move=> st_src s0.
          case: s0 => s0 s1.
          remember (si_temp_st st_src true false n 1 x1) as st_dst.
          exists st_dst.
          simpl.
          inversion s1.
          clear s1.
          split.
          rewrite Heqst_dst/si_temp_st.
          rewrite Z.eqb_refl.
          rewrite -H0 -H1 -H2 c1 c2.
          by simpl.
          have tr: trans st_src st_dst.
          rewrite /trans/rule_existence.
          move=> x0 y0.
          specialize (classic (x0 = n /\ y0 = 1)).
          case=> s2.
          case: s2 => s10 s11.
          right.
          rewrite s10 s11 -H0 c0 Heqst_dst.
          rewrite /si_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          constructor.
          left.
          apply not_and_or in s2.
          case: s2 => s2.
          apply Z.eqb_neq in s2.
          rewrite Heqst_dst/si_temp_st.
          by rewrite s2.
          apply Z.eqb_neq in s2.
          rewrite Heqst_dst/si_temp_st.
          rewrite s2.
          by rewrite andb_false_r.
          split.
          by [].
          split.
          apply (safety_subset (axis_coords n) st_src st_dst).
          split. by []. by [].

          move=> x0 y0 s1.
          apply not_or_and in s1.
          case: s1 => s1 s2.
          apply not_or_and in s2.
          case: s2 => s2 s3.
          apply not_or_and in s3.
          case: s3 => s3 s4.
          clear s4.
          rewrite Heqst_dst/si_temp_st.
          apply eqp_neq in s1.
          case: s1 => s1.
          rewrite Z.eqb_sym in s1.
          by rewrite s1.
          rewrite Z.eqb_sym in s1.
          rewrite s1.
          by rewrite andb_false_r.

          right with [ si true false x1; si false false x6; si true true x1 ].
          rewrite /trans_ss.
          move=> st_src s0.
          case: s0 => s0 s1.
          remember (si_temp_st st_src false false n 0 x6) as st_dst.
          exists st_dst.
          simpl.
          inversion s1.
          clear s1.
          split.
          rewrite Heqst_dst/si_temp_st/Z.eqb_refl.
          rewrite -H0 -H2.
          rewrite Z.eqb_refl.
          by simpl.
          have tr: trans st_src st_dst.
          rewrite /trans/rule_existence.
          move=> x0 y0.
          specialize (classic (x0 = n /\ y0 = 0)).
          case=> s2.
          case: s2 => s10 s11.
          right.
          rewrite s10 s11 -H1 Heqst_dst/si_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          remember (map_coord st_src [((n - 1), 0); ((n + 1), 0); (n, (-1)); (n, 1)]) as s12.
          simpl in Heqs12.
          have s1: pre_cnd (axis_coords n) st_src. by [].
          case: s1 => s1 s2.
          case: s1 => s1 s3.
          case: s3 => s3 s4.
          case: s4 => s4 s5.
          clear s1 s3 s4.
          have s6: i_safe st_src. by [].
          specialize (s6 n 0 x6 true x5).
          case: s6 => s6 s7.
          case: s7 => s7 s8.
          clear s6 s7.
          have s9: st_src n 0 = si true x5 x6. by rewrite H1.
          apply s8 in s9.
          specialize (s5 n 1 x1 true false).
          case: s5 => s5 s6.
          case: s6 => s6 s7.
          clear s5 s6.
          have s15: st_src n 1 = si true false x1. by rewrite H0.
          apply s7 in s15.
          clear s7 s8.
          have s3: 0 < n. by omega.
          rewrite (abs_eq_gt n s3) in s9 s15.
          clear s3.
          rewrite Z.abs_0 in s9.
          have s3: 0 <= 1. by omega.
          rewrite (Z.abs_eq 1 s3) in s15.
          clear s3.
          have s4: n + 0 - 2 = n - 2. by omega.
          have s5: n + 1 - 2 = n - 1. by omega.
          rewrite s4 s5 in s9 s15.
          clear s4 s5.
          move: (Zdiv.Zplus_mod_idemp_l (n - 2) 1 5) => s3.
          have s4: n - 2 + 1 = n - 1. by omega.
          rewrite s4 in s3.
          clear s4.
          rewrite -s9 -s15 in s3.
          have s4: succ x6 = x1. by rewrite /succ.
          clear s2 s3 s9 s15.
          move: (TmptoDef1 s12 x5 false x6) => s1.
          rewrite -Heqs12.
          apply s1.
          rewrite s4.
          split.
          rewrite H0 Heqs12.
          right. right. right. by left.
          rewrite (negb_involutive true).
          rewrite H2 Heqs12.
          right. right. by left.

          apply not_and_or in s2.
          left.
          rewrite Heqst_dst/si_temp_st.
          case: s2 => s2.
          apply Z.eqb_neq in s2.
          by rewrite s2.
          apply Z.eqb_neq in s2.
          rewrite s2.
          by rewrite andb_false_r.

          split.
          by [].
          split.
          apply (safety_subset (axis_coords n) st_src st_dst).
          split.
          by [].
          by [].

          move=> x0 y0 s1.
          apply not_or_and in s1.
          case: s1 => s1 s2.
          apply not_or_and in s2.
          case: s2 => s2 s3.
          apply not_or_and in s3.
          case: s3 => s3 s4.
          clear s4.
          rewrite Heqst_dst/si_temp_st.
          apply eqp_neq in s2.
          case: s2 => s2.
          rewrite Z.eqb_sym in s2.
          by rewrite s2.
          rewrite Z.eqb_sym in s2.
          rewrite s2.
          by rewrite andb_false_r.

          by constructor.
          by rewrite /axis_safe.

          (* x0, x3 = true, false *)
          exists [ si true true x1; si false false x6; si true false x1 ].

          split.
          right with [ si true true x1; si false false x6; si true false x1 ].
          rewrite /trans_ss.
          move=> st_src s0.
          case: s0 => s0 s1.
          remember (si_temp_st st_src false false n 0 x6) as st_dst.
          exists st_dst.
          simpl.
          inversion s1.
          clear s1.
          split.
          rewrite Heqst_dst/si_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          by rewrite -H0 -H2 -c0 -c2.
          have tr: trans st_src st_dst.
          rewrite /trans/rule_existence.
          move=> x0 y0.
          specialize (classic (x0 = n /\ y0 = 0)).
          case=> s2.
          case: s2 => s10 s11.
          right.
          rewrite s10 s11 -H0 c0 Heqst_dst.
          rewrite /si_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          remember (map_coord st_src [((n - 1), 0); ((n + 1), 0); (n, (-1)); (n, 1)]) as s12.
          simpl in Heqs12.
          have s1: pre_cnd (axis_coords n) st_src. by [].
          case: s1 => s1 s2.
          case: s1 => s1 s3.
          case: s3 => s3 s4.
          case: s4 => s4 s5.
          clear s1 s3 s4.
          have s6: i_safe st_src. by [].
          specialize (s6 n 0 x6 true x5).
          case: s6 => s6 s7.
          case: s7 => s7 s8.
          clear s6 s7.
          have s9: st_src n 0 = si true x5 x6.
          rewrite -H1. by rewrite c1.
          apply s8 in s9.
          move: (s5 n 1 x1 true true) => s6.
          case: s6 => s6 s7.
          case: s7 => s7 s13.
          clear s5 s6 s7.
          have s15: st_src n 1 = si true true x1.
          rewrite -H0. by rewrite c0.
          apply s13 in s15.
          clear s8 s13.
          have s3: 0 < n. by omega.
          rewrite (abs_eq_gt n s3) in s9 s15.
          clear s3.
          rewrite Z.abs_0 in s9.
          have s3: 0 <= 1. by omega.
          rewrite (Z.abs_eq 1 s3) in s15.
          clear s3.
          have s4: n + 0 - 2 = n - 2. by omega.
          have s5: n + 1 - 2 = n - 1. by omega.
          rewrite s4 s5 in s9 s15.
          clear s4 s5.
          move: (Zdiv.Zplus_mod_idemp_l (n - 2) 1 5) => s3.
          have s4: n - 2 + 1 = n - 1. by omega.
          rewrite s4 in s3.
          clear s4.
          rewrite -s9 -s15 in s3.
          have s4: succ x6 = x1. by rewrite /succ.
          clear s2 s3 s9 s15.
          move: (TmptoDef1 s12 x5 true x6) => s1.
          rewrite -c0 H0.
          rewrite -c1 H1 in s1.
          rewrite -Heqs12.
          apply s1.
          rewrite s4.
          split.
          rewrite -c0 H0 Heqs12.
          right. right. right. by left.
          rewrite (negb_involutive false).
          rewrite -c2 H2 Heqs12.
          right. right. by left.

          apply not_and_or in s2.
          left.
          rewrite Heqst_dst/si_temp_st.
          case: s2 => s2.
          apply Z.eqb_neq in s2.
          by rewrite s2.
          apply Z.eqb_neq in s2.
          rewrite s2.
          by rewrite andb_false_r.

          split.
          by [].
          split.
          apply (safety_subset (axis_coords n) st_src st_dst).
          split.
          by [].
          by [].

          move=> x0 y0 s1.
          apply not_or_and in s1.
          case: s1 => s1 s2.
          apply not_or_and in s2.
          case: s2 => s2 s3.
          apply not_or_and in s3.
          case: s3 => s3 s4.
          clear s4.
          rewrite Heqst_dst/si_temp_st.
          apply eqp_neq in s2.
          case: s2 => s2.
          rewrite Z.eqb_sym in s2.
          by rewrite s2.
          rewrite Z.eqb_sym in s2.
          rewrite s2.
          by rewrite andb_false_r.

          by constructor.
          by rewrite /axis_safe.

          (* x0, x3 = false, true *)
          exists [ si true false x1; si false false x6; si true true x1 ].

          split.
          right with [ si true false x1; si false false x6; si true true x1 ].
          rewrite /trans_ss.
          move=> st_src s0.
          case: s0 => s0 s1.
          remember (si_temp_st st_src false false n 0 x6) as st_dst.
          exists st_dst.
          simpl.
          inversion s1.
          clear s1.
          split.
          rewrite Heqst_dst/si_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          by rewrite -H0 -H2 -c0 -c2.
          have tr: trans st_src st_dst.
          rewrite /trans/rule_existence.
          move=> x0 y0.
          specialize (classic (x0 = n /\ y0 = 0)).
          case=> s2.
          case: s2 => s10 s11.
          right.
          rewrite s10 s11 -H0 c0 Heqst_dst.
          rewrite /si_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          remember (map_coord st_src [((n - 1), 0); ((n + 1), 0); (n, (-1)); (n, 1)]) as s12.
          simpl in Heqs12.
          have s1: pre_cnd (axis_coords n) st_src. by [].
          case: s1 => s1 s2.
          case: s1 => s1 s3.
          case: s3 => s3 s4.
          case: s4 => s4 s5.
          clear s1 s3 s4.
          have s6: i_safe st_src. by [].
          specialize (s6 n 0 x6 true x5).
          case: s6 => s6 s7.
          case: s7 => s7 s8.
          clear s6 s7.
          have s9: st_src n 0 = si true x5 x6.
          rewrite -H1. by rewrite c1.
          apply s8 in s9.
          move: (s5 n 1 x1 true false) => s6.
          case: s6 => s6 s7.
          case: s7 => s7 s13.
          clear s5 s6 s7.
          have s15: st_src n 1 = si true false x1.
          rewrite -H0. by rewrite c0.
          apply s13 in s15.
          clear s8 s13.
          have s3: 0 < n. by omega.
          rewrite (abs_eq_gt n s3) in s9 s15.
          clear s3.
          rewrite Z.abs_0 in s9.
          have s3: 0 <= 1. by omega.
          rewrite (Z.abs_eq 1 s3) in s15.
          clear s3.
          have s4: n + 0 - 2 = n - 2. by omega.
          have s5: n + 1 - 2 = n - 1. by omega.
          rewrite s4 s5 in s9 s15.
          clear s4 s5.
          move: (Zdiv.Zplus_mod_idemp_l (n - 2) 1 5) => s3.
          have s4: n - 2 + 1 = n - 1. by omega.
          rewrite s4 in s3.
          clear s4.
          rewrite -s9 -s15 in s3.
          have s4: succ x6 = x1. by rewrite /succ.
          clear s2 s3 s9 s15.
          move: (TmptoDef1 s12 x5 false x6) => s1.
          rewrite -c0 H0.
          rewrite -c1 H1 in s1.
          rewrite -Heqs12.
          apply s1.
          rewrite s4.
          split.
          rewrite -c0 H0 Heqs12.
          right. right. right. by left.
          rewrite (negb_involutive true).
          rewrite -c2 H2 Heqs12.
          right. right. by left.

          apply not_and_or in s2.
          left.
          rewrite Heqst_dst/si_temp_st.
          case: s2 => s2.
          apply Z.eqb_neq in s2.
          by rewrite s2.
          apply Z.eqb_neq in s2.
          rewrite s2.
          by rewrite andb_false_r.

          split.
          by [].
          split.
          apply (safety_subset (axis_coords n) st_src st_dst).
          split.
          by [].
          by [].

          move=> x0 y0 s1.
          apply not_or_and in s1.
          case: s1 => s1 s2.
          apply not_or_and in s2.
          case: s2 => s2 s3.
          apply not_or_and in s3.
          case: s3 => s3 s4.
          clear s4.
          rewrite Heqst_dst/si_temp_st.
          apply eqp_neq in s2.
          case: s2 => s2.
          rewrite Z.eqb_sym in s2.
          by rewrite s2.
          rewrite Z.eqb_sym in s2.
          rewrite s2.
          by rewrite andb_false_r.

          by constructor.
          by rewrite /axis_safe.

          (* x0, x3 = false, false *)
          exists [ si true true x1; si false false x6; si true false x1 ].

          split.
          right with [ si true true x1; si true x5 x6; si true false x1 ].
          rewrite /trans_ss.
          move=> st_src s0.
          case: s0 => s0 s1.
          remember (si_temp_st st_src true true n 1 x1) as st_dst.
          exists st_dst.
          simpl.
          inversion s1.
          clear s1.
          split.
          rewrite Heqst_dst/si_temp_st.
          rewrite Z.eqb_refl.
          rewrite -H0 -H1 -H2 c1 c2.
          by simpl.
          have tr: trans st_src st_dst.
          rewrite /trans/rule_existence.
          move=> x0 y0.
          specialize (classic (x0 = n /\ y0 = 1)).
          case=> s2.
          case: s2 => s10 s11.
          right.
          rewrite s10 s11 -H0 c0 Heqst_dst.
          rewrite /si_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          constructor.
          left.
          apply not_and_or in s2.
          case: s2 => s2.
          apply Z.eqb_neq in s2.
          rewrite Heqst_dst/si_temp_st.
          by rewrite s2.
          apply Z.eqb_neq in s2.
          rewrite Heqst_dst/si_temp_st.
          rewrite s2.
          by rewrite andb_false_r.
          split.
          by [].
          split.
          apply (safety_subset (axis_coords n) st_src st_dst).
          split. by []. by [].

          move=> x0 y0 s1.
          apply not_or_and in s1.
          case: s1 => s1 s2.
          apply not_or_and in s2.
          case: s2 => s2 s3.
          apply not_or_and in s3.
          case: s3 => s3 s4.
          clear s4.
          rewrite Heqst_dst/si_temp_st.
          apply eqp_neq in s1.
          case: s1 => s1.
          rewrite Z.eqb_sym in s1.
          by rewrite s1.
          rewrite Z.eqb_sym in s1.
          rewrite s1.
          by rewrite andb_false_r.

          right with [ si true true x1; si false false x6; si true false x1 ].
          rewrite /trans_ss.
          move=> st_src s0.
          case: s0 => s0 s1.
          remember (si_temp_st st_src false false n 0 x6) as st_dst.
          exists st_dst.
          simpl.
          inversion s1.
          clear s1.
          split.
          rewrite Heqst_dst/si_temp_st/Z.eqb_refl.
          rewrite -H0 -H2.
          rewrite Z.eqb_refl.
          by simpl.
          have tr: trans st_src st_dst.
          rewrite /trans/rule_existence.
          move=> x0 y0.
          specialize (classic (x0 = n /\ y0 = 0)).
          case=> s2.
          case: s2 => s10 s11.
          right.
          rewrite s10 s11 -H1 Heqst_dst/si_temp_st.
          rewrite Z.eqb_refl.
          simpl.
          remember (map_coord st_src [((n - 1), 0); ((n + 1), 0); (n, (-1)); (n, 1)]) as s12.
          simpl in Heqs12.
          have s1: pre_cnd (axis_coords n) st_src. by [].
          case: s1 => s1 s2.
          case: s1 => s1 s3.
          case: s3 => s3 s4.
          case: s4 => s4 s5.
          clear s1 s3 s4.
          have s6: i_safe st_src. by [].
          specialize (s6 n 0 x6 true x5).
          case: s6 => s6 s7.
          case: s7 => s7 s8.
          clear s6 s7.
          have s9: st_src n 0 = si true x5 x6. by rewrite H1.
          apply s8 in s9.
          specialize (s5 n 1 x1 true true).
          case: s5 => s5 s6.
          case: s6 => s6 s7.
          clear s5 s6.
          have s15: st_src n 1 = si true true x1. by rewrite H0.
          apply s7 in s15.
          clear s7 s8.
          have s3: 0 < n. by omega.
          rewrite (abs_eq_gt n s3) in s9 s15.
          clear s3.
          rewrite Z.abs_0 in s9.
          have s3: 0 <= 1. by omega.
          rewrite (Z.abs_eq 1 s3) in s15.
          clear s3.
          have s4: n + 0 - 2 = n - 2. by omega.
          have s5: n + 1 - 2 = n - 1. by omega.
          rewrite s4 s5 in s9 s15.
          clear s4 s5.
          move: (Zdiv.Zplus_mod_idemp_l (n - 2) 1 5) => s3.
          have s4: n - 2 + 1 = n - 1. by omega.
          rewrite s4 in s3.
          clear s4.
          rewrite -s9 -s15 in s3.
          have s4: succ x6 = x1. by rewrite /succ.
          clear s2 s3 s9 s15.
          move: (TmptoDef1 s12 x5 false x6) => s1.
          rewrite -Heqs12.
          apply s1.
          rewrite s4.
          split.
          rewrite H2 Heqs12.
          right. right. by left.
          rewrite (negb_involutive true).
          rewrite H0 Heqs12.
          right. right. right. by left.

          apply not_and_or in s2.
          left.
          rewrite Heqst_dst/si_temp_st.
          case: s2 => s2.
          apply Z.eqb_neq in s2.
          by rewrite s2.
          apply Z.eqb_neq in s2.
          rewrite s2.
          by rewrite andb_false_r.

          split.
          by [].
          split.
          apply (safety_subset (axis_coords n) st_src st_dst).
          split.
          by [].
          by [].

          move=> x0 y0 s1.
          apply not_or_and in s1.
          case: s1 => s1 s2.
          apply not_or_and in s2.
          case: s2 => s2 s3.
          apply not_or_and in s3.
          case: s3 => s3 s4.
          clear s4.
          rewrite Heqst_dst/si_temp_st.
          apply eqp_neq in s2.
          case: s2 => s2.
          rewrite Z.eqb_sym in s2.
          by rewrite s2.
          rewrite Z.eqb_sym in s2.
          rewrite s2.
          by rewrite andb_false_r.

          by constructor.
          by rewrite /axis_safe.

      (* (n, 0) = Safe *)
      +exists (map_coord st (axis_coords n)).
        split.
        *constructor. by [].
        *by simpl.
  Qed.

  Close Scope list_scope.
  Close Scope Z_scope.

End Fairness.
