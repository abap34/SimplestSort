(* 
    SimplestSort: https://arxiv.org/abs/2110.01111
    がソートアルゴリズムであることを証明するプログラム.
*)

Require Import List.
Import ListNotations.
Require Import Arith.

(* --- SimpleSort 自体の実装 --- *)

(* まずスワップ *)
Fixpoint swap (l : list nat) (i j : nat) : list nat :=
  match l with
  | [] => []         
  (* 空リストの場合は何もしない *)
  | x :: xs =>       
  (* head, tail に分ける *)
    match i, j with  
    | 0, 0 => x :: xs 
     (* i = j = 0 の場合はそのままくっつける *)
    | 0, S j' => nth j' xs x :: firstn j' xs ++ x :: skipn (S j') xs  
    (* i = 0, j = S j' の場合は [j' 番目, 0 ~ j' 番目, x, j' + 1 ~ 最後] *)
    | S i', 0 => nth i' xs x :: firstn i' xs ++ x :: skipn (S i') xs
    (* i = S i', j = 0 の場合は [i' 番目, 0 ~ i' 番目, x, i' + 1 ~ 最後]*)
    | S i', S j' => x :: swap xs i' j'
    (* それ以外の場合, head はそのままで、 tail のインデックスを一つ減らして再帰 *)
    end
  end.

Compute swap [1; 2; 3; 4; 5] 1 2.
Compute swap [1; 2; 3; 4; 5] 0 4.


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

