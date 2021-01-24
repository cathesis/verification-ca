Require Import List.
Require Import ZArith.
Require Import Classical.
Require Import FinFun.

From mathcomp
Require Import ssreflect.

Import ListNotations.

Section Utility.
  Open Scope Z_scope.
  Open Scope list_scope.

  Definition succ (i : Z) : Z :=
    (i + 1) mod 5.

  Definition pred (i : Z) : Z :=
    (i - 1) mod 5.

  Definition Mat2 := list (list Z).

  Definition mat_mul (m : Mat2) (p : Z * Z) : (Z * Z) :=
    let row0 := nth 0 m [] in
    let row1 := nth 1 m [] in
    let (a, b) := (nth 0 row0 0, nth 1 row0 0) in
    let (c, d) := (nth 0 row1 0, nth 1 row1 0) in
    (a * (fst p) + b * (snd p), (c * (fst p) + d * (snd p))).
    
  Notation "m * p" := (mat_mul m p).

  Definition mat2_pi_over_2 : Mat2 := [ [ 0; 1 ]; [ -1; 0 ] ].

  Definition mat2_pi_over_2' : Mat2 := [ [ 0; -1 ]; [ 1; 0 ] ].

  Lemma lt_imply_false (x : Z) : (x < 0 -> False) -> 0 <= x.
  Proof. omega. Qed.

  Lemma gt_imply_false (x : Z) : (0 < x -> False) -> x <= 0.
  Proof. omega. Qed.

  Lemma abs_eq_gt (x : Z) : 0 < x -> Z.abs x = x.
  Proof.
    have x_gt_imply_ge: 0 < x -> 0 <= x. omega.
    move /x_gt_imply_ge.
    apply: Z.abs_eq.
  Qed.

  Lemma abs_eq_lt (x : Z) : x < 0 -> Z.abs x = -x.
  Proof.
    have x_lt_imply_le: x < 0 -> x <= 0. omega.
    move /x_lt_imply_le.
    apply Z.abs_neq.
  Qed.

  Lemma pair_eq_and (a b c d : Z) : (a, b) = (c, d) <-> a = c /\ b = d.
  Proof.
    split.
    -move=> s0.
      inversion s0.
      split.
      +by [].
      +by [].
    -move=> s0.
      case: s0 => s0 s1.
      by rewrite s0 s1.
  Qed.

  Lemma eqp_neq (a b c d : Z) :
    (a, b) <> (c, d) <-> a =? c = false \/ b =? d = false.
  Proof.
    split.
    -move=> s0.
      unfold not in s0.
      move /pair_eq_and in s0.
      apply not_and_or in s0.
      case: s0 => s0.
      +left. by apply Z.eqb_neq.
      +right. by apply Z.eqb_neq.
    -move=> s0.
      move=> s1.
      inversion s1.
      case: s0 => s0.
      +by apply Z.eqb_neq in s0.
      +by apply Z.eqb_neq in s0.
  Qed.

  Close Scope list_scope.
  Close Scope Z_scope.

End Utility.
