Require Import List Arith.
Import ListNotations.

Fixpoint insert (a : nat) (l : list nat) : list nat :=
  match l with
  | [] => [a]
  | b :: l' => if Nat.leb a b then a :: l else b :: insert a l'
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | a :: l' => insert a (sort l')
  end.

Fixpoint all_subset_sums (nums : list nat) : list nat :=
  match nums with
  | [] => [0]
  | x :: xs =>
      let rec := all_subset_sums xs in
      rec ++ map (fun y => x + y) rec
  end.

Fixpoint prune_delta (delta : nat) (last : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => if Nat.leb x (last + delta - 1)
               then prune_delta delta last xs
               else x :: prune_delta delta x xs
  end.

Definition adaptive_pruned_subset_sums (delta : nat) (nums : list nat) : list nat :=
  let sums := all_subset_sums nums in
  let sums_sorted := sort sums in
  let sums_nodup := nodup Nat.eq_dec sums_sorted in
  match sums_nodup with
  | [] => []
  | y :: ys => y :: prune_delta delta y ys
  end.
