# SimplestSort (WIP)

A Coq proof of SimplestSort (https://arxiv.org/abs/2110.01111).

# Roadmap

- [ ] Proof of Permutation

- [ ] Proof of Sorted

# Proof Outline (WIP)

## Permutation

First, we prove that the output of `simplest_sort` is a permutation of the input list.

```coq
simplest_sort_permutation : forall l, Permutation l (simplest_sort l).
```

To prove this, we have to prove that `swap` is a permutation of the input list.

```coq
swap_permutation : forall l i j, Permutation l (swap l i j).
```

For this, we prove some lemmas.

```coq
Lemma firstn_nth : forall (l : list nat) (i : nat),
  i < length l ->
  firstn i l ++ [nth i l 0] = firstn (S i) l.

Lemma app3_permutation : forall (a b c : list nat),
  Permutation (a ++ b ++ c) (c ++ b ++ a).

Lemma decompose_permutation : forall (l : list nat) (i j : nat),
 (i < j) /\ (j < length l) /\ (i < length l) ->
    Permutation l (
     firstn i l ++ [nth i l 0] ++ skipn (S i) (firstn j l) ++ [nth j l 0] ++ skipn (S j) l
    ).
```

Using these lemmas, we can prove `swap_permutation` as follows.

1. Decompose the input list into 5 parts (referred to as `decompose l`).
2. Apply `decompose_permutation`, resulting in `Permutation l (decompose l)`.
3. To prove `Permutation l (swap l i j)`, it suffices to prove 
   `Permutation (decompose l) (swap l i j)` because `Permutation` is transitive.
4. `swap l i j` reduces to swapping the second and fourth elements of `decompose l`.
   Therefore, use `Permutation_app_inv_l` and `Permutation_app_inv_r` to remove
   the first and last parts, and then apply `Permutation_app3` to swap the
   second and fourth elements.
5. This results in `Permutation (decompose l) (swap l i j)`.
6. Finally, use `Permutation_trans` to prove `Permutation l (swap l i j)`.



