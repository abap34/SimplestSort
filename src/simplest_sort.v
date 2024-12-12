(* 
    SimplestSort: https://arxiv.org/abs/2110.01111
    がソートアルゴリズムであることを証明するプログラム.
*)

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Lia.

(* --- SimpleSort 自体の実装 --- *)

(* まずスワップ *)
Definition swap (l : list nat) (i j : nat) : list nat :=
  if i =? j then
    l
  else
    if i <? j then
      firstn i l ++ [nth j l 0] ++ skipn (S i) (firstn j l) ++ [nth i l 0] ++ skipn (S j) l
    else
      firstn j l ++ [nth i l 0] ++ skipn (S j) (firstn i l) ++ [nth j l 0] ++ skipn (S i) l.


Compute swap [1; 2; 3; 4; 5] 1 2. 
(* 1; 3; 2; 4; 5 *)

Compute swap [1; 2; 3; 4; 5] 2 1.
(* 1; 3; 2; 4; 5 *)

Compute swap [1; 2; 3; 4; 5] 0 4.
(* 5; 2; 3; 4; 1 *)
Compute swap [1; 2; 3; 4; 5] 4 0.
(* 5; 2; 3; 4; 1 *)

Compute swap [1; 2; 3; 4; 5] 0 0.
(* 1; 2; 3; 4; 5 *)

Compute swap [1; 2; 3; 4; 5] 2 2.
(* 1; 2; 3; 4; 5 *)


Fixpoint inner_loop (arr : list nat) (n i m : nat) : list nat :=
  match m with
  | 0 => arr
  | S m' =>
      let j := n - m in
      let arr' :=
        if nth i arr 0 <? nth j arr 0 then
          swap arr i j
        else
          arr in
      inner_loop arr' n i m'
  end.

Fixpoint outer_loop (arr : list nat) (n m : nat) : list nat :=
  match m with
  | 0 => arr
  | S m' =>
      let i := n - m in
      let arr' := inner_loop arr n i n in
      outer_loop arr' n m'
  end.

Definition simplest_sort (arr : list nat) : list nat :=
  let n := length arr in
  outer_loop arr n n.

Compute simplest_sort [1; 3; 2; 5; 4].
(* [1; 2; 3; 4; 5] *)

Compute simplest_sort [4; 3; 1; 4; 2].
(* [1; 2; 3; 4; 5] *)

Compute simplest_sort [5; 4; 3; 2; 1].
(* [1; 2; 3; 4; 5] *)

Compute simplest_sort [1; 2; 3; 4; 5].
(* [1; 2; 3; 4; 5] *)




(* --- 正しさの証明 --- *)
(* swap が Permutation であることを証明する *)
Require Import Coq.Sorting.Permutation.


Lemma firstn_nth : forall (l : list nat) (i : nat),
  i < length l ->
  firstn i l ++ [nth i l 0] = firstn (S i) l.
Proof.
  intros l i Hlen.
  generalize dependent i.
  induction l as [| x xs IH]; intros i Hlen.
  - destruct i; simpl in Hlen; inversion Hlen.
  - destruct i as [| i']; simpl.
    + reflexivity.
    + f_equal; apply IH; apply Nat.succ_lt_mono, Hlen.
Qed. 


(* a ++ b ++ c <-- perm --> c ++ b ++ a *)
Lemma app3_permutation : forall (a b c : list nat),
  Permutation (a ++ b ++ c) (c ++ b ++ a).
Proof.
  intros a b c.
  rewrite app_assoc.
  rewrite app_assoc with (l := c).
  rewrite Permutation_app_comm.

  rewrite <- app_assoc with (l := c).
  apply Permutation_app_head.
  rewrite Permutation_app_comm  with (l := b).
  apply Permutation_refl.
Qed.

Lemma firstn_skipn_firstn : forall (l : list nat) (i j : nat),
  (i <= j /\ j < length l /\ i < length l) ->
  firstn i l ++ skipn i (firstn j l) = firstn j l.
Proof.
  intros l i j [Hi_lt [Hj_len Hi_len]].
  revert i j Hi_lt Hj_len Hi_len.
  induction l as [| x xs IH]; intros.
  - (* l = [] *)
    simpl in Hj_len. 
    destruct j; simpl in Hj_len; inversion Hj_len.
  - (* Cl = x :: xs *)
    destruct i as [| i']; destruct j as [| j']; simpl in *.
    + reflexivity.
    + (*  i = 0, j = S j' *)
      simpl. reflexivity.
    + (*  i = S i', j = 0 *)
      exfalso. 
      inversion Hi_lt.
    + (*  i = S i', j = S j' *)
      simpl.
      f_equal.
      apply IH.
      apply Nat.succ_le_mono, Hi_lt.
      apply Nat.succ_lt_mono, Hj_len.
      apply Nat.succ_lt_mono, Hi_len.
Qed.  
  

Definition decompose (l : list nat) (i j : nat) : list nat :=
  firstn i l ++ [nth i l 0] ++ skipn (S i) (firstn j l) ++ [nth j l 0] ++ skipn (S j) l.


(* swap のための分割が Permutation であるという補題 *)
Lemma decompose_permutation : forall (l : list nat) (i j : nat),
 (i < j) /\ (j < length l) /\ (i < length l) ->
    Permutation (decompose l i j) l.
Proof.
  intros l i j [Hi_lt [Hj_len Hi_len]].
  unfold decompose.
  rewrite app_assoc.
  rewrite firstn_nth with (i := i) by apply Hi_len.
  rewrite app_assoc.
  rewrite firstn_skipn_firstn with (i := S i) (j := j).
  - rewrite app_assoc.
    rewrite firstn_nth with (i := j) (l := l) by apply Hj_len.
    rewrite firstn_skipn with (n := (S j)) (l := l).
    apply Permutation_refl.
   -  split.
      (* i < j -> S i <= j *)
      + apply Hi_lt.
      + split.
        (* j < length l *)
        * apply Hj_len.
        (* S i < length l *)
        * apply (Nat.le_lt_trans (S i) j (length l)).
          apply Hi_lt.
          apply Hj_len.
Qed.


(* 

swap が perm の証明の方針:

[i = j のとき]
 → swap (l i j) = l より. 

[i != j のとき]

1. decompose <-- perm --> l
2. decompose <-- perm --> swap

で l <-- perm --> swap が示せる. (perm の trans)

 *)
(* decompose <-- perm --> swap *)
Lemma decompose_swap_permutation : forall (l : list nat) (i j : nat),
  (i < j) /\ (j < length l) /\ (i < length l) ->
  Permutation (decompose l i j) (swap l i j).
Proof.
  intros l i j [Hi_lt [Hj_len Hi_len]].
  unfold swap.
  destruct (i =? j) eqn:Hij_eq.
  - exfalso.
    apply Nat.eqb_eq in Hij_eq.
    (* i < j  ->  i != j で矛盾 *)
    apply Nat.lt_neq in Hi_lt.
    exact (Hi_lt Hij_eq).
  - destruct (i <? j) eqn:Hij_lt.
    + (* i < j *)
      unfold decompose.
      apply Permutation_app_head.

      (* 右とそれ以外に持ってく *)
      rewrite app_assoc.
      rewrite app_assoc.
      rewrite app_assoc.
      rewrite app_assoc.
      apply Permutation_app_tail with (tl := skipn (S j) l).

      rewrite <- app_assoc.
      rewrite <- app_assoc.
      apply app3_permutation.
    + (* j < i *)
      exfalso.
      apply Nat.ltb_ge in Hij_lt.
      lia.
Qed.

