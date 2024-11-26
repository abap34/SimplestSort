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


Fixpoint simplest_sort (arr : list nat) (n i j : nat) : list nat :=
  if i <? n then
    if j <? n then
      if nth i arr 0 <=? nth j arr 0 then
        simplest_sort (swap arr i j) n i (j + 1)
      else
        simplest_sort arr n i (j + 1)
    else
      simplest_sort arr n (i + 1) 0
  else
    arr.