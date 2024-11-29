(* 
    SimplestSort: https://arxiv.org/abs/2110.01111
    がソートアルゴリズムであることを証明するプログラム.
*)

Require Import List.
Import ListNotations.
Require Import Arith.


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
Compute simplest_sort [4; 3; 1; 4; 2].

Compute simplest_sort [5; 4; 3; 2; 1].
Compute simplest_sort [1; 2; 3; 4; 5].

(* --- 正しさの証明 --- *)
(* swap が Permutation であることを証明する *)
Require Import Coq.Sorting.Permutation.


(* もうちょっと考える *)
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
    + f_equal; apply IH; apply PeanoNat.Nat.succ_lt_mono, Hlen.
Qed. 

(* a ++ b ++ c <- peerm --> c ++ b ++ a  を示す *)
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
  - (* Case: l = [] *)
    simpl in Hj_len. (* 長さ 0 のリストで j が 0 未満になる矛盾を処理 *)
    destruct j; simpl in Hj_len; inversion Hj_len.
  - (* Case: l = x :: xs *)
    destruct i as [| i']; destruct j as [| j']; simpl in *.
    + reflexivity.

    + (* Subcase: i = 0, j = S j' *)
      simpl. reflexivity.
    + (* Subcase: i = S i', j = 0 *)
      exfalso. (* i < j の仮定が矛盾している *)
      inversion Hi_lt.
    + (* Subcase: i = S i', j = S j' *)
      simpl.
      f_equal.
      apply IH.
      apply PeanoNat.Nat.succ_le_mono, Hi_lt.
      apply PeanoNat.Nat.succ_lt_mono, Hj_len.
      apply PeanoNat.Nat.succ_lt_mono, Hi_len.
Qed.  
