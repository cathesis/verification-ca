Require Import Bool.
Require Import List.
Require Import Omega.
Require Import Classical.

From mathcomp
Require Import ssreflect.

Require Import Utility.
Require Import Cell.

Import ListNotations.

Section Concentric.
  Open Scope Z_scope.
  Open Scope list_scope.

  Inductive CellType: Set :=
    | White
    | Temp
    | Safe.

  Definition c_type (s: CellState): CellType :=
    match s with
    | W => White
    | s true _ | si true _ _ => Temp
    | S | s false _ | si false _ _ => Safe
    end.

  (***** Safety *****)
  Definition init_safe (st : State) : Prop := st 0 0 = S.

  Definition t_safe (st : State) : Prop :=
    forall (x y : Z), c_type (st x y) = Temp ->
    ((x > 0 /\ c_type (st (x - 1) y) = Safe) \/
    (x < 0 /\ c_type (st (x + 1) y) = Safe) \/
    (y > 0 /\ c_type (st x (y - 1)) = Safe) \/
    (y < 0 /\ c_type (st x (y + 1)) = Safe)
    ).

  Definition s_safe (st : State) : Prop :=
    forall (x y : Z), c_type (st x y) = Safe ->
    ((x > 0 -> c_type (st (x - 1) y) = Safe) /\
    (x < 0 -> c_type (st (x + 1) y) = Safe) /\
    (y > 0 -> c_type (st x (y - 1)) = Safe) /\
    (y < 0 -> c_type (st x (y + 1)) = Safe)).

  Definition i_safe (st : State) : Prop :=
    forall (x y i : Z) (tmp alt : bool),
    (st x y = S -> x = 0 /\ y = 0) /\
    (st x y = s tmp alt ->
    (x = 1 /\ y = 0) \/ (x = -1 /\ y = 0) \/
    (x = 0 /\ y = 1) \/ (x = 0 /\ y = -1)) /\
    (st x y = si tmp alt i -> i = (Z.abs x + Z.abs y - 2) mod 5).

  Definition safe (st : State) : Prop :=
    init_safe st /\ t_safe st /\ s_safe st /\ i_safe st.
  (***** Safety *****)

  (***** Reachability *****)
  CoInductive Run : Type :=
    | RCons : State -> Run -> Run.

  Definition hd (r : Run) : State := let (a, b) := r in a.
  Definition tl (r : Run) : Run := let (a, b) := r in b.

  Definition Coord := prod Z Z.

  Definition map_coord
    (st : State) (cl : list Coord) : list CellState :=
    map (fun c : Coord => st (fst c) (snd c)) cl.

  CoInductive ValidRun : Run -> Prop :=
    | VCons : forall (st : State) (r : Run),
        ValidRun r -> trans st (hd r) -> ValidRun (RCons st r).

  Inductive InRun (st : State) (r : Run) : Prop :=
    | Here : st = hd r -> InRun st r
    | Further : InRun st (tl r) -> InRun st r.

  Definition trans_ss
    (cl : list Coord)
    (ul vl : list CellState)
    (P : State -> Prop) (* e.g. safe *)
    : Prop :=
    forall (st : State),
    P st /\ ul = map_coord st cl ->
    exists (st' : State),
    vl = map_coord st' cl /\ trans st st' /\ P st' /\
    (forall (x y : Z), ~In (x, y) cl -> st x y = st' x y).

  Inductive trans_subset
    (cl : list Coord)
    (ul vl : list CellState)
    (P : State -> Prop) (* e.g. safe *)
    : Prop :=
    | I : ul = vl -> trans_subset cl ul vl P
    | V : forall (wl : list CellState), 
        trans_ss cl ul wl P ->
        trans_subset cl wl vl P ->
        trans_subset cl ul vl P.

  Definition fair
    (r : Run)
    (cl : list Coord) (* i.e. list (prod Z Z) *)
    (P : State -> Prop) (* e.g. safe *)
    (Q : list CellState -> Prop)
    : Prop :=
    ValidRun r ->
    (forall (st : State), InRun st r /\ P st ->
    (exists (vl : list CellState),
    trans_subset cl (map_coord st cl) vl P /\ Q vl)) ->
    (exists (st' : State), InRun st' r /\ Q (map_coord st' cl)).

  Definition side_coords (n y : Z) : list Coord :=
    [ (n, y); (n + 1, y) ].

  Definition axis_coords (n : Z) : list Coord :=
    [ (n, 1); (n, 0); (n, -1) ].

  (* P *)
  Definition SideSSCnd (ul : list Coord) (st : State) : Prop :=
    let l := map c_type (map_coord st ul) in
    let a := nth 0 l White in
    a = Safe.

  Inductive subset_cnd (ul : list Coord) (st : State) : Prop :=
    | I0 : ul = [] -> subset_cnd ul st
    | I1 : forall (x y : Z) (res : list Coord),
        ul = (x, y) :: res ->
        c_type (st x y) = Safe \/ c_type (st x y) = Temp ->
        subset_cnd res st ->
        subset_cnd ul st.

  Definition pre_cnd (ul : list Coord) (st : State) : Prop :=
    safe st /\ subset_cnd ul st.

  (* Q *)
  Definition side_safe (vl : list CellState) : Prop :=
    let l := map c_type vl in
    let a := nth 1 l White in
    a = Safe \/ a = Temp.

  Definition axis_safe (vl : list CellState) : Prop :=
    let l := map c_type vl in
    nth 1 l White = Safe.

  Lemma temp_imply : forall (c : CellState),
    c_type c = Temp -> exists (alt : bool) (i : Z),
    c = s true alt \/ c = si true alt i.
  Proof.
    move=> c s0.
    destruct c.
    -by [].
    -by [].
    -exists alt.
      destruct tmp.
      exists 0.
      by left.
      by discriminate.
    -exists alt.
      destruct tmp.
      exists i.
      by right.
      by discriminate.
  Qed.

  Definition si_temp_st
    (st : State) (tmp alt: bool) (n m i : Z) (x y : Z) : CellState :=
    if ((x =? n) && (y =? m)) then si tmp alt i else st x y.

  Definition s_temp_st
    (st : State) (tmp alt: bool) (n m : Z) (x y : Z) : CellState :=
    if ((x =? n) && (y =? m)) then s tmp alt else st x y.
  (***** Reachability *****)

  Close Scope list_scope.
  Close Scope Z_scope.

End Concentric.

