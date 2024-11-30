# SimplestSort (WIP)

A Coq proof of SimplestSort (https://arxiv.org/abs/2110.01111).

# Roadmap

- [x] Proof of Permutation

- [ ] Proof of Sorted

# Proof Outline (WIP)

## Permutation

First, we prove that the output of `simplest_sort` is a permutation of the input list.

```
simplest_sort_permutation : forall l, Permutation l (simplest_sort l).
```

To prove this, we have to prove that `swap` is a permutation of the input list.

```
swap_permutation : forall l i j, Permutation l (swap l i j).
```

For this, we prove some lemmas.

```
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

1. Decompose the input list into 5 parts. (we call it `decompose l`).
2. Apply `decompose_permutation`, then we get `Permutation l (decompose l)`.
3. Remove first and last parts by `Permutation_app_inv_l`, `Permutation_app_inv_r`.
4. Apply `app3_permutation` to the remaining parts.
5. After that, we get the result that `Permutation (decompose l) (swap l i j)`.
6. Finally, we can prove `Permutation l (swap l i j)` by `Permutation_trans`.


