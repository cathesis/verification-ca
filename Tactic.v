Require Import Bool.
Require Import List.
Require Import Omega.

From mathcomp
Require Import ssreflect.

Import ListNotations.

Require Import Utility.
Require Import Cell.
Require Import Concentric.

  Open Scope Z_scope.
  Open Scope list_scope.

  Ltac destruct_ctrans ctr :=
    inversion ctr as [
    cs in0 src l0 dst |
    cs alt in0 src l0 dst |
    cs alt i in0 src l0 dst |
    cs tmp alt src l0 dst |
    cs tmp alt i src l0 dst |
    cs alt alt' i in0 src l0 dst |
    cs alt alt' i in0 src l0 dst |
    cs alt alt' i in0 src l0 dst
    ].

  Ltac simpl_arith :=
    repeat match goal with 
    | |- _ => rewrite Z.add_simpl_r
    | |- _ => rewrite Z.sub_simpl_r
    | H : _ |- _ => rewrite Z.add_simpl_r in H
    | H : _ |- _ => rewrite Z.sub_simpl_r in H 
    end.

  Ltac ineq :=
    match goal with
    | |- ?x > 0 =>
        apply: Znot_le_gt;
        let a := fresh "x" in 
        have a: x <= 0 -> x - 1 < 0;
        [ omega | move /a; clear a ]
    | |- ?x < 0 =>
        apply: Znot_ge_lt;
        let a := fresh "x" in 
        have a: x >= 0 -> x + 1 > 0;
        [ omega | move /a; clear a ]
    end.

  Ltac diag st :=
    match goal with
    |
        H0 : t_safe st, H1 : s_safe st,
        H2 : ?x > 0, H3 : ?y > 0,
        H4 : c_type (st (?x + 1) ?y) = Temp
    |- _ =>
        apply H0 in H4; simpl_arith;
        case: H4;
        [
        let a := fresh "H" in
        let b := fresh "H" in
        case=> a b; apply H1 in b;
        let c := fresh "H" in
        case: b => b c;
        let d := fresh "H" in
        case: c => c d;
        let e := fresh "H" in
        case: d => d e;
        specialize (d H3);
        move: d => H4;
        clear a b c e
        (* auto *)
    |
        let a := fresh "H" in
        case=> a;
        [ omega |
            case: a => a;
            [
            let b := fresh "H" in
            case: a => a b;
            apply H1 in b; simpl_arith;
            let c := fresh "H" in
            case: b => b c;
            let d := fresh "H" in
            have d: x + 1 > 0;
            [ omega | apply b in d; move: d => H4; clear a b c ]
                (* auto *)
    |
        omega
        ]
        ]
        ]
    end.

     Close Scope list_scope.
     Close Scope Z_scope.

