Require Import Bool.
Require Import List.
Require Import Omega.

Require Import Utility.

Import ListNotations.

Section ConcentricCell.
  Open Scope Z_scope.
  Open Scope list_scope.

  Inductive CellState: Set :=
    | W
    | S
    | s : forall (tmp alt : bool), CellState
    | si : forall (tmp alt : bool) (i : Z), CellState.

  Definition State: Type := Z -> Z -> CellState.

  Inductive CTrans :
    CellState -> list CellState -> CellState -> Prop :=
    | Wtos : forall (cs : list CellState),
        In S cs -> CTrans W cs (s true false)
    | WtoTmp0 : forall (cs : list CellState) (alt : bool),
        In (s false alt) cs ->
        CTrans W cs (si true false 0)
    | WtoTmp1 : forall (cs : list CellState) (alt : bool) (i : Z),
        In (si false alt i) cs ->
        CTrans W cs (si true false (succ i))
    | sAlt : forall (cs : list CellState) (tmp alt : bool),
        CTrans (s tmp alt) cs (s tmp (negb alt))
    | siAlt : forall (cs : list CellState) (tmp alt : bool) (i : Z),
        CTrans (si tmp alt i) cs (si tmp (negb alt) i)
    | TmptoDef0 : forall (cs : list CellState) (alt alt' : bool) (i : Z),
        In (si true alt' 0) cs /\
        In (si true (negb alt') 0) cs ->
        CTrans (s true alt) cs (s false false)
    | TmptoDef1 : forall (cs : list CellState) (alt alt' : bool) (i : Z),
        In (si true alt' (succ i)) cs /\
        In (si true (negb alt') (succ i)) cs ->
        CTrans (si true alt i) cs (si false false i)
    | TmptoDef2 : forall (cs : list CellState) (alt alt' : bool) (i : Z),
        In (si false alt' (pred i)) cs /\
        In (si false (negb alt') (pred i)) cs ->
        CTrans (si true alt i) cs (si false false i).

  Definition rule_existence
    (st st' : State) (x y : Z) : Prop :=
    CTrans
    (st x y)
    [(st (x - 1) y); (st (x + 1) y); (st x (y - 1)); (st x (y + 1))]
    (st' x y).

  Definition trans (st st' : State) : Prop :=
    forall (x y : Z), st x y = st' x y \/ rule_existence st st' x y.

  Close Scope list_scope.
  Close Scope Z_scope.

End ConcentricCell.
