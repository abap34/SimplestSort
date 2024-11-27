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

