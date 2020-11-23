/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/

import data.finset
import data.fintype.basic
import data.nat.choose
import combinatorics.basic

/-!
# Shadows

This file defines shadows of a set family and proves the local LYM and LYM
theorems, as well as Sperner's theorem.

## Main definitions
The `shadow` of a set family is everything we can get by removing an element
from each set.

The rth slice of a set family 𝒜 is given by `slice 𝒜 r`, and is the subset of
its elements which have cardinality r.

## Main statements
* local_lym
* lubell_yamamoto_meshalkin
* sperner

## Notation
We introduce the notation ∂ to denote the shadow.
We also maintain the convention that A, B, ... denote sets (usually finset α),
𝒜, ℬ, ... denote set families, i.e. `finset (finset α)` and lower-case letters
denote elements of the ground set α.

## References
* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags
shadow, lym, slice, sperner, antichain
-/

open fintype
open finset
open nat

variables {α : Type*}

/-!
### Shadows
The shadow of a set family is everything we can get by removing an element
from each set.

This section develops the introductory theory of shadows, with some lemmas on
iterated shadows as well.
-/
section shadow

variables [decidable_eq α]
/--
Everything we get by removing one element from the set `A`, used to define
the shadow.
-/
def all_removals (A : finset α) : finset (finset α) := A.image (erase A)

/-- B ∈ all_removals A iff we can remove something from A to get B. -/
lemma mem_all_removals {A : finset α} {B : finset α} :
  B ∈ all_removals A ↔ ∃ i ∈ A, erase A i = B :=
by simp only [all_removals, mem_image]

/--
If A has size r, then there are r things we get by removing one element.
-/
lemma card_all_removals {A : finset α} {r : ℕ} (H : card A = r) :
  (all_removals A).card = r :=
begin
  rwa [all_removals, card_image_of_inj_on],
  intros i ih j _ k,
  have q: i ∉ erase A j := k ▸ not_mem_erase i A,
  rw [mem_erase, not_and] at q,
  by_contra a,
  apply q a ih
end

/--
The shadow of a set family 𝒜 is all sets we can get by removing one element
from any set in 𝒜, and the (k times) iterated shadow is all sets we can get
by removing k elements from any set in 𝒜.
-/
def shadow (𝒜 : finset (finset α)) : finset (finset α) := 𝒜.bind all_removals

reserve prefix `∂`:90
notation ∂𝒜 := shadow 𝒜

/-- Shadow of the empty set is empty. -/
lemma shadow_empty : shadow (∅ : finset (finset α)) = ∅ := rfl

/-- Iterated shadow of the empty set is empty. -/
lemma iter_shadow_empty (k : ℕ) : shadow^[k] (∅ : finset (finset α)) = ∅ :=
begin
  induction k with k ih,
  { refl },
  { rwa [iterate, shadow_empty] },
end

/-- The shadow is monotonic (though not strictly so). -/
lemma shadow_monotone {𝒜 ℬ : finset (finset α)} : 𝒜 ⊆ ℬ → ∂𝒜 ⊆ ∂ℬ :=
bind_subset_bind_of_subset_left _

/--
B ∈ ∂𝒜 iff there is an A ∈ 𝒜 from which we can remove something to get B.
-/
lemma mem_shadow {𝒜 : finset (finset α)} (B : finset α) :
  B ∈ shadow 𝒜 ↔ ∃ A ∈ 𝒜, ∃ i ∈ A, erase A i = B :=
by simp only [shadow, all_removals, mem_bind, mem_image]

/--
Alternatively, B ∈ ∂𝒜 iff we can put something new into B, and land in 𝒜.
-/
lemma mem_shadow' {𝒜 : finset (finset α)} {B : finset α} :
  B ∈ shadow 𝒜 ↔ ∃ j ∉ B, insert j B ∈ 𝒜 :=
begin
  rw mem_shadow,
  split,
  { rintro ⟨A, HA, i, Hi, k⟩,
    rw ← k,
    refine ⟨i, not_mem_erase i A, _⟩,
    rwa insert_erase Hi },
  { rintro ⟨i, Hi, k⟩,
    refine ⟨insert i B, k, i, mem_insert_self _ _, _⟩,
    rw erase_insert Hi }
end

/-- Everything in the shadow is one smaller than things in the original. -/
lemma shadow_sized {𝒜 : finset (finset α)} {r : ℕ} (a : all_sized 𝒜 r) :
  all_sized (∂𝒜) (r-1) :=
begin
  intros A H,
  simp_rw [shadow, mem_bind, all_removals, mem_image] at H,
  rcases H with ⟨A, hA, i, hi, rfl⟩,
  rw [card_erase_of_mem hi, a _ hA],
  refl,
end

/--
B ∈ ∂𝒜 iff B is exactly one element less than something from 𝒜
-/
lemma sub_iff_shadow_one {𝒜 : finset (finset α)} {B : finset α} :
  B ∈ ∂𝒜 ↔ ∃ A ∈ 𝒜, B ⊆ A ∧ card (A \ B) = 1 :=
begin
  rw mem_shadow',
  split,
  { rintro ⟨i, ih, inA⟩,
    refine ⟨insert i B, inA, subset_insert _ _, _⟩,
    rw card_sdiff (subset_insert _ _),
    simp [card_insert_of_not_mem ih] },
  { rintro ⟨A, hA, a_h_h⟩,
    rw card_eq_one at a_h_h,
    rcases a_h_h with ⟨subs, j, eq⟩,
    refine ⟨j, _, _⟩,
    { intro a,
      have : j ∉ A \ B := not_mem_sdiff_of_mem_right a,
      apply this,
      rw eq,
      apply mem_singleton_self },
    { rwa [insert_eq j B, ← eq, sdiff_union_of_subset subs] } },
end

/--
In particular, being in the shadow means we're a subset of something in 𝒜.
-/
lemma sub_of_shadow {𝒜 : finset (finset α)} {B : finset α} :
  B ∈ ∂𝒜 → ∃ A ∈ 𝒜, B ⊆ A :=
by rw sub_iff_shadow_one; tauto

/-- B ∈ ∂^k 𝒜 iff B is exactly k elements less than something from 𝒜. -/
lemma sub_iff_shadow_iter {𝒜 : finset (finset α)} {B : finset α} (k : ℕ) :
  B ∈ (shadow^[k] 𝒜) ↔ ∃ A ∈ 𝒜, B ⊆ A ∧ card (A \ B) = k :=
begin
  induction k with k ih generalizing 𝒜 B,
  { simp [sdiff_eq_empty_iff_subset],
    split,
    { intro p,
      exact ⟨B, p, subset.refl _, subset.refl _⟩ },
    { rintro ⟨A, _, q⟩,
      rw ← subset.antisymm_iff at q,
      rwa q } },
  { simp,
    rw iterate,
    rw @ih (∂𝒜) B,
    clear ih,
    split,
    { rintro ⟨A, hA, BsubA, card_AdiffB_is_k⟩,
      rw sub_iff_shadow_one at hA,
      rcases hA with ⟨C, CinA, AsubC, card_CdiffA_is_1⟩,
      refine ⟨C, CinA, trans BsubA AsubC, _⟩,
      rw card_sdiff (trans BsubA AsubC),
      rw card_sdiff BsubA at card_AdiffB_is_k,
      rw card_sdiff AsubC at card_CdiffA_is_1,
      rw [← nat.sub_add_cancel (card_le_of_subset AsubC),
          nat.add_sub_assoc (card_le_of_subset BsubA), card_CdiffA_is_1,
          card_AdiffB_is_k, add_comm] },
    { rintro ⟨A, hA, a_h_right_left, a_h_right_right⟩,
      have z: (A \ B).nonempty,
      { rw [← card_pos, a_h_right_right],
        exact nat.succ_pos _ },
      rcases z with ⟨i, hi⟩,
      have: i ∈ A, rw mem_sdiff at hi,
      { exact hi.1 },
      have: B ⊆ erase A i,
      { intros t th,
        apply mem_erase_of_ne_of_mem _ (a_h_right_left th),
        intro a,
        rw mem_sdiff at hi,
        rw a at th,
        exact hi.2 th },
      refine ⟨erase A i, _, ‹_›, _⟩,
      { rw mem_shadow,
        refine ⟨A, hA, i, ‹_›, rfl⟩ },
      rw [card_sdiff ‹B ⊆ erase A i›,
        card_erase_of_mem ‹i ∈ A›, nat.pred_sub,
        ← card_sdiff a_h_right_left, a_h_right_right],
      simp } }
end
/--
Everything in the `k`th shadow is `k` smaller than things in the original.
-/
lemma iter_shadow_sized {𝒜 : finset (finset α)} {r k : ℕ}
  (a : all_sized 𝒜 r) : all_sized (shadow^[k] 𝒜) (r-k) :=
begin
  intro B,
  rw sub_iff_shadow_iter,
  rintro ⟨A, hA, subs, card⟩,
  rw [card_sdiff ‹B ⊆ A›, a _ hA] at card,
  rw [← card, nat.sub_sub_self],
  rw ← a _ hA,
  apply card_le_of_subset ‹B ⊆ A›
end

end shadow

/-!
### Build up and proof of local LYM

If there is a fintype α which is our universe, informally write α^(r) for the
set {A : finset α | |A| = r}. Then if 𝒜 is a subset of α^(r), we get that ∂𝒜
is a subset of α^(r-1).
The local LYM inequality says 𝒜 'takes up less' of α^(r) than ∂𝒜 takes up of
α^(r-1). In particular,
|𝒜| / choose |α| r ≤ |∂𝒜| / choose |α| (r-1)
-/
section local_lym
variables [decidable_eq α]
/--
Start by multiplying out the inequality so it's in a slightly nicer form.
-/
lemma multiply_out {A B n r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ n)
  (h : A * r ≤ B * (n - r + 1)) :
  (A : ℚ) / nat.choose n r ≤ B / nat.choose n (r-1) :=
begin
  rw div_le_div_iff; norm_cast,
  { apply le_of_mul_le_mul_right _ ‹0 < r›,
    cases r,
    { simp },
    { rw nat.succ_eq_add_one at *,
      rw [← nat.sub_add_comm hr2, nat.add_sub_add_right] at h,
      convert nat.mul_le_mul_right (choose n r) h using 1;
      { simp [mul_assoc, nat.choose_succ_right_eq],
        left,
        ac_refl } } },
  { apply nat.choose_pos hr2 },
  { apply nat.choose_pos (le_trans (nat.pred_le _) hr2) },
end

/--
We'll prove local LYM by a double counting argument. Here's the first set
we'll count, which is effectively {(A,B) | A ∈ 𝒜, B ∈ all_removals A}
-/
def the_pairs (𝒜 : finset (finset α)) : finset (finset α × finset α) :=
𝒜.bind (λ A, (all_removals A).image (prod.mk A))

/--
Find how big the_pairs is: for each A ∈ 𝒜 there are r possible B, giving the
exact cardinality.
-/
lemma card_the_pairs {r : ℕ} (𝒜 : finset (finset α)) (a : all_sized 𝒜 r) :
  (the_pairs 𝒜).card = 𝒜.card * r :=
begin
  rw [the_pairs, card_bind],
  { convert sum_const_nat _,
    intros x hx,
    rw card_image_of_inj_on,
    rw card_all_removals (a _ hx),
    exact (λ _ _ _ _ k, (prod.mk.inj k).2) },
  simp only [disjoint_left, mem_image],
  rintros _ _ _ _ k a ⟨_, _, rfl⟩ ⟨_, _, a₂⟩,
  exact k (prod.mk.inj a₂.symm).1,
end

/--
Here's the second set we'll count. We're trying to get the same set, but we
count B first, so we overestimate a bit. It's pretty much
{(A,B) | B ∈ ∂𝒜, ∃ i ∉ B: A = B ∪ i}
-/
def from_below [fintype α] (𝒜 : finset (finset α)) :
  finset (finset α × finset α) :=
(∂𝒜).bind (λ B, (univ \ B).image (λ x, (insert x B, B)))

/--
Note the first is a subset of the second: if A ∈ 𝒜 and B ∈ all_removals A
then certainly B ∈ ∂𝒜, and there's some i that was removed from A to make B.
-/
lemma above_sub_below [fintype α] (𝒜 : finset (finset α)) :
  the_pairs 𝒜 ⊆ from_below 𝒜 :=
begin
  rintros ⟨A,B⟩,
  simp only [the_pairs, from_below, mem_bind, mem_all_removals, mem_shadow,
              true_and, and_imp, exists_prop, mem_sdiff, mem_image,
              prod.mk.inj_iff, mem_univ, exists_imp_distrib],
  rintros A Ah B i ih z rfl rfl,
  exact ⟨B, ⟨A, Ah, i, ih, z⟩, i, z ▸ not_mem_erase _ _,
          z ▸ insert_erase ih, rfl⟩
end

/-
It'll be useful to abbreviate this. It's helpful to think of α = fin n.
-/
local notation `n` := card α
/--
We can also find how big the second set is: for each B there are
(|α| - r + 1) choices for what to put into it.
-/
lemma card_from_below [fintype α] {𝒜 : finset (finset α)} {r : ℕ}
  (a : all_sized 𝒜 r) :
  (from_below 𝒜).card = (∂𝒜).card * (n - (r - 1)) :=
begin
  rw [from_below, card_bind],
  { apply sum_const_nat,
    intros,
    rw [card_image_of_inj_on,
    card_univ_diff,
    shadow_sized a _ H],
    intros x1 x1h _ _ h,
    injection h,
    have q := mem_insert_self x1 x,
    rw [h_1, mem_insert] at q,
    apply q.resolve_right (mem_sdiff.1 x1h).2 },
  intros _ _ _ _ t,
  rw disjoint_left,
  simp_rw [mem_image, not_exists, exists_prop, mem_sdiff,
            mem_univ, true_and, exists_imp_distrib,
            prod.forall, prod.mk.inj_iff, and_imp, not_and],
  rintro _ b i hi rfl rfl j hj k,
  rwa eq_comm,
end

/--
The local LYM inequality says 𝒜 'takes up less' of α^(r) than ∂𝒜 takes up of
α^(r-1). In particular,
|𝒜| / choose |α| r ≤ |∂𝒜| / choose |α| (r-1)
Its proof is just the double counting argument we've now set up.
-/
theorem local_lym [fintype α] {𝒜 : finset (finset α)} {r : ℕ} (hr1 : 1 ≤ r)
  (H : all_sized 𝒜 r) :
  (𝒜.card : ℚ) / nat.choose n r ≤ (∂𝒜).card / nat.choose n (r-1) :=
begin
  cases lt_or_le n r with z hr2,
  -- Take care of the r > n case: it's trivial
  { rw [choose_eq_zero_of_lt z, cast_zero, div_zero],
    refine div_nonneg _ _; norm_cast,
    any_goals { apply nat.zero_le } },
  { apply multiply_out hr1 hr2,
  -- Multiply out, convert to the cardinality forms we got above and done
    rw [← card_the_pairs _ H, ← nat.sub_sub_assoc hr2 hr1,
        ← card_from_below H],
    apply card_le_of_subset,
    apply above_sub_below }
end

end local_lym

/-!
### Slices

The `r`th slice of a set family the subset of its elements which have
cardinality `r`.
A few basic facts about slices.
-/
section slice
/--
The `r`th slice of a set family the subset of its elements which have
cardinality `r`.
-/
def slice (𝒜 : finset (finset α)) (r : ℕ) : finset (finset α) :=
𝒜.filter (λ i, card i = r)

reserve infix `#`:100
notation 𝒜#r := slice 𝒜 r

/-- `A` is in the `r`th slice of `𝒜` iff it's in `𝒜` and has cardinality `r`. -/
lemma mem_slice {𝒜 : finset (finset α)} {r : ℕ} {A : finset α} :
  A ∈ 𝒜#r ↔ A ∈ 𝒜 ∧ A.card = r :=
by rw [slice, mem_filter]

/-- The `r`th slice of `𝒜` is a subset of `𝒜`. -/
lemma slice_subset {𝒜 : finset (finset α)} {r : ℕ} : 𝒜#r ⊆ 𝒜 :=
λ _, and.left ∘ mem_slice.mp

/-- Everything in the `r`th slice of `𝒜` has size `r`. -/
lemma sized_slice {𝒜 : finset (finset α)} {r : ℕ} : all_sized (𝒜#r) r :=
λ _, and.right ∘ mem_slice.mp

/-- Elements in distinct slices must be distinct. -/
lemma ne_of_diff_slice {𝒜 : finset (finset α)} {r₁ r₂ : ℕ}
  {A₁ A₂ : finset α} (h₁ : A₁ ∈ 𝒜#r₁) (h₂ : A₂ ∈ 𝒜#r₂) :
  r₁ ≠ r₂ → A₁ ≠ A₂ :=
mt $ λ h, (sized_slice A₁ h₁).symm.trans ((congr_arg card h).trans (sized_slice A₂ h₂))

end slice

/- It's useful to abbreviate this. We can think of α = fin n. -/
local notation `n` := card α

/-!
The LYM inequality says ∑_i |A#i|/(n choose i) ≤ 1 for an antichain A.
Observe that A#i is all the stuff in A which has size i, and the collection of
subsets of (fin n) with size i has size (n choose i).
So, |A#i|/(n choose i) represents how much of each that A can take up.

Other proofs of LYM exist, but we'll do it by applying local LYM.
-/
section lym

variables [fintype α]

/--
An inductive definition, from the top down.
`falling 𝒜 k` is all the sets with cardinality (card α - k) which are a
subset of something in 𝒜.
-/
def falling [decidable_eq α] (𝒜 : finset (finset α)) : Π (k : ℕ), finset (finset α)
  | 0 := 𝒜#n
  | (k+1) := 𝒜#(n - (k+1)) ∪ shadow (falling k)

/--
Everything in the kth fallen has size `n-k`
-/
lemma falling_sized [decidable_eq α] (𝒜 : finset (finset α)) (k : ℕ) :
  all_sized (falling 𝒜 k) (n - k) :=
begin
  induction k with k ih; rw falling,
  { apply sized_slice },
  { rw ← union_layer,
    split,
    { apply sized_slice },
    { apply shadow_sized ih } },
end

/--
Here's the first key proposition, helping to give the disjointness
property in the next lemma.
-/
theorem antichain_prop [decidable_eq α] {𝒜 : finset (finset α)} {r k : ℕ}
  (hk : k ≤ n) (hr : r < k) (H : antichain 𝒜) :
  ∀ A ∈ 𝒜#(n - k), ∀ B ∈ ∂falling 𝒜 r, ¬(A ⊆ B) :=
begin
  intros A HA B HB k,
  rcases sub_of_shadow HB with ⟨C, HC, _⟩,
  replace k := trans k ‹B ⊆ C›,
  clear HB h_h B,
  induction r with r ih generalizing A C;
  rw falling at HC,
  any_goals { rw mem_union at HC, cases HC },
  any_goals { refine H A (mem_slice.1 HA).1 C (mem_slice.1 HC).1 _ ‹A ⊆ C›,
              apply ne_of_diff_slice HA HC _,
              apply ne_of_lt },
  { apply nat.sub_lt_of_pos_le _ _ hr hk },
  { mono },
  { obtain ⟨_, HB', HB''⟩ := sub_of_shadow HC,
    exact ih (lt_of_succ_lt hr) _ _ HA HB' (trans k_1 HB'') }
end

/--
This tells us that `falling 𝒜 k` is disjoint from the n - (k+1) -sized
elements of 𝒜, thanks to the antichain property.
-/
lemma disjoint_of_antichain [decidable_eq α] {𝒜 : finset (finset α)} {k : ℕ}
  (hk : k + 1 ≤ n) (H : antichain 𝒜) :
  disjoint (𝒜#(n - (k + 1))) (∂falling 𝒜 k) :=
disjoint_left.2 $ λ A HA HB,
  antichain_prop hk (lt_add_one k) H A HA A HB (subset.refl _)

/--
In particular, we can use induction and local LYM to get a bound on any top
part of the sum in LYM in terms of the size of `falling 𝒜 k`.
-/
lemma card_falling [decidable_eq α] {𝒜 : finset (finset α)} {k : ℕ} (hk : k ≤ card α)
  (H : antichain 𝒜) :
  (range (k+1)).sum
    (λ r, ((𝒜#(n - r)).card : ℚ) / nat.choose n (n - r))
  ≤ (falling 𝒜 k).card / nat.choose n (n - k) :=
begin
  induction k with k ih,
  { simp [falling] },
  { rw [sum_range_succ, falling],
    convert add_le_add_left (trans (ih (le_of_lt hk)) _) _,
    { rw [card_disjoint_union, ← add_div, cast_add],
      exact disjoint_of_antichain hk H },
    { exact local_lym (nat.le_sub_left_of_add_le hk) (falling_sized _ _) } }
end

/--
A stepping-stone lemma to get to LYM.
-/
lemma card_fallen [decidable_eq α] {𝒜 : finset (finset α)} (H : antichain 𝒜) :
  (range (n+1)).sum (λ r, ((𝒜#r).card : ℚ) / nat.choose n r)
≤ (falling 𝒜 n).card / nat.choose n 0 :=
begin
  rw [← nat.sub_self n],
  convert ← card_falling (le_refl _) H using 1,
  apply sum_flip (λ r, ((𝒜#r).card : ℚ) / nat.choose n r),
end

/--
The LYM inequality says ∑_i |A#i|/(n choose i) ≤ 1 for an antichain A.
Observe that A#i is all the stuff in A which has size i, and the collection of
subsets of (fin n) with size i has size (n choose i).
So, |A#i|/(n choose i) represents how much of each that A can take up.

The proof is easy using the developed lemmas above.
-/
theorem lubell_yamamoto_meshalkin {𝒜 : finset (finset α)} (H : antichain 𝒜) :
  (range (n + 1)).sum (λ r, ((𝒜#r).card : ℚ) / nat.choose n r) ≤ 1 :=
begin
  classical,
  transitivity,
  { apply card_fallen H },
  rw div_le_iff; norm_cast,
  { simpa only [mul_one, nat.choose_zero_right, nat.sub_self]
      using number_of_fixed_size (falling_sized 𝒜 (card α)) },
  apply nat.choose_pos (nat.zero_le _)
end

end lym

/--
Sperner's theorem gives a bound on the size of an antichain. This can be
proved in a few ways, but this uses the machinery already developed about LYM.
The idea is simple: with LYM, we get a bound on how much of A can have any
particular size.  So to maximise the size of A, we'd like to fit it all into
the term with the biggest denominator.
In other words,
∑_i |A#i|/(n choose i) ≤ 1, so
∑_i |A#i|/(n choose (n/2)) ≤ 1, so
∑_i |A#i| ≤ (n choose (n/2)), as required.
-/
theorem sperner [fintype α] {𝒜 : finset (finset α)} (H : antichain 𝒜) :
  𝒜.card ≤ nat.choose n (n / 2) :=
begin
  classical,
  have: (range (n + 1)).sum (λ (r : ℕ), ((𝒜#r).card : ℚ) / nat.choose n (n/2)) ≤ 1,
  { apply le_trans _ (lubell_yamamoto_meshalkin H),
    apply sum_le_sum,
    intros r hr,
    apply div_le_div_of_le_left; norm_cast,
    { apply nat.zero_le },
    { apply choose_pos, rw mem_range at hr, rwa ← nat.lt_succ_iff },
    { apply choose_le_middle } },
  rw [← sum_div, ← sum_nat_cast, div_le_one] at this,
  { norm_cast at this,
    rw ← card_bind at this,
    convert this,
    simp only [ext_iff, mem_slice, mem_bind, exists_prop, mem_range, lt_succ_iff],
    intro a,
    split,
    { intro ha,
      refine ⟨a.card, card_le_of_subset (subset_univ _), ha, rfl⟩ },
    { rintro ⟨_, _, q, _⟩,
      exact q },
    intros x _ y _ ne,
    rw disjoint_left,
    intros a Ha k,
    exact ne_of_diff_slice Ha k ne rfl },
  norm_cast,
  apply choose_pos,
  apply nat.div_le_self,
end
