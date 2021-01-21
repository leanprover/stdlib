/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import tactic.monotonicity.basic
import data.set.lattice

variables {α : Type*}

@[mono]
lemma mul_mono_nonneg {x y z : α} [ordered_semiring α]
  (h' : 0 ≤ z)
  (h : x ≤ y)
: x * z ≤ y * z :=
by apply mul_le_mul_of_nonneg_right; assumption

lemma lt_of_mul_lt_mul_neg_right {a b c : α}  [linear_ordered_ring α]
  (h : a * c < b * c) (hc : c ≤ 0) : b < a :=
have nhc : -c ≥ 0, from neg_nonneg_of_nonpos hc,
have h2 : -(b * c) < -(a * c), from neg_lt_neg h,
have h3 : b * (-c) < a * (-c), from calc
     b * (-c) = - (b * c)    : by rewrite neg_mul_eq_mul_neg
          ... < - (a * c)    : h2
          ... = a * (-c)     : by rewrite neg_mul_eq_mul_neg,
lt_of_mul_lt_mul_right h3 nhc

@[mono]
lemma mul_mono_nonpos {x y z : α} [linear_ordered_ring α]
  (h' : z ≤ 0) (h : y ≤ x) : x * z ≤ y * z :=
begin
  classical,
  by_contradiction h'',
  revert h,
  apply not_le_of_lt,
  apply lt_of_mul_lt_mul_neg_right _ h',
  apply lt_of_not_ge h''
end

@[mono]
lemma nat.sub_mono_left_strict {x y z : ℕ}
  (h' : z ≤ x)
  (h : x < y)
: x - z < y - z :=
begin
  have : z ≤ y,
  { transitivity, assumption, apply le_of_lt h, },
  apply @nat.lt_of_add_lt_add_left z,
  rw [nat.add_sub_of_le,nat.add_sub_of_le];
    solve_by_elim
end

@[mono]
lemma nat.sub_mono_right_strict {x y z : ℕ}
  (h' : x ≤ z)
  (h : y < x)
: z - x < z - y :=
begin
  have h'' : y ≤ z,
  { transitivity, apply le_of_lt h, assumption },
  apply @nat.lt_of_add_lt_add_right _ x,
  rw [nat.sub_add_cancel h'],
  apply @lt_of_le_of_lt _ _ _ (z - y + y),
  rw [nat.sub_add_cancel h''],
  apply nat.add_lt_add_left h
end

open set

attribute [mono] inter_subset_inter union_subset_union
                 sUnion_mono bUnion_mono sInter_subset_sInter bInter_mono
                 image_subset preimage_mono prod_mono monotone_prod seq_mono
                 image2_subset
attribute [mono] upper_bounds_mono_set lower_bounds_mono_set
                 upper_bounds_mono_mem  lower_bounds_mono_mem
                 upper_bounds_mono  lower_bounds_mono
                 bdd_above.mono bdd_below.mono
