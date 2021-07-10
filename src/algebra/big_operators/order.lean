/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import algebra.big_operators.basic

/-!
# Results about big operators with values in an ordered algebraic structure.

Mostly monotonicity results for the `∏` and `∑` operations.

-/

open_locale big_operators

variables {ι α β M N G k R : Type*}

namespace finset

section

variables [comm_monoid M] [ordered_comm_monoid N]

/-- Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` be a map
submultiplicative on `{x | p x}`, i.e., `p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be
a nonempty finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∏ x in s, g x) ≤ ∏ x in s, f (g x)`. -/
@[to_additive le_sum_nonempty_of_subadditive_on_pred]
lemma le_prod_nonempty_of_submultiplicative_on_pred
  (f : M → N) (p : M → Prop) (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y)
  (hp_mul : ∀ x y, p x → p y → p (x * y)) (g : ι → M) (s : finset ι) (hs_nonempty : s.nonempty)
  (hs : ∀ i ∈ s, p (g i)) :
  f (∏ i in s, g i) ≤ ∏ i in s, f (g i) :=
begin
  refine le_trans (multiset.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul _ _ _) _,
  { simp [hs_nonempty.ne_empty], },
  { exact multiset.forall_mem_map_iff.mpr hs, },
  rw multiset.map_map,
  refl,
end

/-- Let `{x | p x}` be an additive subsemigroup of an additive commutative monoid `M`. Let `f : M →
N` be a map subadditive on `{x | p x}`, i.e., `p x → p y → f (x + y) ≤ f x + f y`. Let `g i`, `i ∈
s`, be a nonempty finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∑ i in s, g i) ≤ ∏ i in s, f (g i)`. -/
add_decl_doc le_sum_nonempty_of_subadditive_on_pred

/-- If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y` and `g i`, `i ∈ s`, is a
nonempty finite family of elements of `M`, then `f (∏ i in s, g i) ≤ ∏ i in s, f (g i)`. -/
@[to_additive le_sum_nonempty_of_subadditive]
lemma le_prod_nonempty_of_submultiplicative
  (f : M → N) (h_mul : ∀ x y, f (x * y) ≤ f x * f y) {s : finset ι} (hs : s.nonempty) (g : ι → M) :
  f (∏ i in s, g i) ≤ ∏ i in s, f (g i) :=
le_prod_nonempty_of_submultiplicative_on_pred f (λ i, true) (λ x y _ _, h_mul x y)
  (λ _ _ _ _, trivial) g s hs (λ _ _, trivial)

/-- If `f : M → N` is a subadditive function, `f (x + y) ≤ f x + f y` and `g i`, `i ∈ s`, is a
nonempty finite family of elements of `M`, then `f (∑ i in s, g i) ≤ ∑ i in s, f (g i)`. -/
add_decl_doc le_sum_nonempty_of_subadditive

/-- Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` be a map
such that `f 1 = 1` and `f` is submultiplicative on `{x | p x}`, i.e.,
`p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be a finite family of elements of `M` such
that `∀ i ∈ s, p (g i)`. Then `f (∏ i in s, g i) ≤ ∏ i in s, f (g i)`. -/
@[to_additive le_sum_of_subadditive_on_pred]
lemma le_prod_of_submultiplicative_on_pred (f : M → N) (p : M → Prop) (h_one : f 1 = 1)
  (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y)
  (hp_mul : ∀ x y, p x → p y → p (x * y)) (g : ι → M) {s : finset ι} (hs : ∀ i ∈ s, p (g i)) :
  f (∏ i in s, g i) ≤ ∏ i in s, f (g i) :=
begin
  rcases eq_empty_or_nonempty s with rfl|hs_nonempty,
  { simp [h_one] },
  { exact le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul g s hs_nonempty hs, },
end

/-- Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` be a map
such that `f 1 = 1` and `f` is submultiplicative on `{x | p x}`, i.e.,
`p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be a finite family of elements of `M` such
that `∀ i ∈ s, p (g i)`. Then `f (∏ x in s, g x) ≤ ∏ x in s, f (g x)`. -/
add_decl_doc le_sum_of_subadditive_on_pred

/-- If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y`, `f 1 = 1`, and `g i`,
`i ∈ s`, is a finite family of elements of `M`, then `f (∏ i in s, g i) ≤ ∏ i in s, f (g i)`. -/
@[to_additive le_sum_of_subadditive]
lemma le_prod_of_submultiplicative (f : M → N) (h_one : f 1 = 1)
  (h_mul : ∀ x y, f (x * y) ≤ f x * f y) (s : finset ι) (g : ι → M) :
  f (∏ i in s, g i) ≤ ∏ i in s, f (g i) :=
begin
  refine le_trans (multiset.le_prod_of_submultiplicative f h_one h_mul _) _,
  rw multiset.map_map,
  refl,
end

/-- If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y`, `f 1 = 1`, and `g i`,
`i ∈ s`, is a finite family of elements of `M`, then `f (∏ i in s, g i) ≤ ∏ i in s, f (g i)`. -/
add_decl_doc le_sum_of_subadditive

variables {f g : ι → N} {s t : finset ι}

/-- In an ordered commutative monoid, if each factor `f i` of one finite product is less than or
equal to the corresponding factor `g i` of another finite product, then
`∏ i in s, f i ≤ ∏ i in s, g i`. -/
@[to_additive sum_le_sum]
lemma prod_le_prod'' (h : ∀ i ∈ s, f i ≤ g i) : ∏ i in s, f i ≤ ∏ i in s, g i :=
begin
  classical,
  induction s using finset.induction_on with i s hi ihs h,
  { refl },
  { simp only [prod_insert hi],
    exact mul_le_mul' (h _ (mem_insert_self _ _)) (ihs $ λ j hj, h j (mem_insert_of_mem hj)) }
end

/-- In an ordered additive commutative monoid, if each summand `f i` of one finite sum is less than
or equal to the corresponding summand `g i` of another finite sum, then
`∑ i in s, f i ≤ ∑ i in s, g i`. -/
add_decl_doc sum_le_sum

@[to_additive sum_nonneg]  lemma one_le_prod' (h : ∀i ∈ s, 1 ≤ f i) : 1 ≤ (∏ i in s, f i) :=
le_trans (by rw prod_const_one) (prod_le_prod'' h)

@[to_additive sum_nonpos] lemma prod_le_one' (h : ∀i ∈ s, f i ≤ 1) : (∏ i in s, f i) ≤ 1 :=
(prod_le_prod'' h).trans_eq (by rw prod_const_one)

@[to_additive sum_le_sum_of_subset_of_nonneg]
lemma prod_le_prod_of_subset_of_one_le' (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i) :
  ∏ i in s, f i ≤ ∏ i in t, f i :=
by classical;
calc (∏ i in s, f i) ≤ (∏ i in t \ s, f i) * (∏ i in s, f i) :
    le_mul_of_one_le_left' $ one_le_prod' $ by simpa only [mem_sdiff, and_imp]
  ... = ∏ i in t \ s ∪ s, f i : (prod_union sdiff_disjoint).symm
  ... = ∏ i in t, f i         : by rw [sdiff_union_of_subset h]

@[to_additive sum_mono_set_of_nonneg]
lemma prod_mono_set_of_one_le' (hf : ∀ x, 1 ≤ f x) : monotone (λ s, ∏ x in s, f x) :=
λ s t hst, prod_le_prod_of_subset_of_one_le' hst $ λ x _ _, hf x

@[to_additive sum_le_univ_sum_of_nonneg]
lemma prod_le_univ_prod_of_one_le' [fintype ι] {s : finset ι} (w : ∀ x, 1 ≤ f x) :
  ∏ x in s, f x ≤ ∏ x, f x :=
prod_le_prod_of_subset_of_one_le' (subset_univ s) (λ a _ _, w a)

@[to_additive sum_eq_zero_iff_of_nonneg]
lemma prod_eq_one_iff_of_one_le' : (∀ i ∈ s, 1 ≤ f i) → (∏ i in s, f i = 1 ↔ ∀ i ∈ s, f i = 1) :=
begin
  classical,
  apply finset.induction_on s,
  exact λ _, ⟨λ _ _, false.elim, λ _, rfl⟩,
  assume a s ha ih H,
  have : ∀ i ∈ s, 1 ≤ f i, from λ _, H _ ∘ mem_insert_of_mem,
  rw [prod_insert ha, mul_eq_one_iff' (H _ $ mem_insert_self _ _) (one_le_prod' this),
    forall_mem_insert, ih this]
end

@[to_additive sum_eq_zero_iff_of_nonneg]
lemma prod_eq_one_iff_of_le_one' : (∀ i ∈ s, f i ≤ 1) → (∏ i in s, f i = 1 ↔ ∀ i ∈ s, f i = 1) :=
@prod_eq_one_iff_of_one_le' _ (order_dual N) _ _ _

@[to_additive single_le_sum]
lemma single_le_prod' (hf : ∀ i ∈ s, 1 ≤ f i) {a} (h : a ∈ s) : f a ≤ (∏ x in s, f x) :=
calc f a = ∏ i in {a}, f i : prod_singleton.symm
     ... ≤ ∏ i in s, f i   :
  prod_le_prod_of_subset_of_one_le' (singleton_subset_iff.2 h) $ λ i hi _, hf i hi

variables {ι' : Type*} [decidable_eq ι']

@[to_additive sum_fiberwise_le_sum_of_sum_fiber_nonneg]
lemma prod_fiberwise_le_prod_of_one_le_prod_fiber' {t : finset ι'}
  {g : ι → ι'} {f : ι → N} (h : ∀ y ∉ t, (1 : N) ≤ ∏ x in s.filter (λ x, g x = y), f x) :
  ∏ y in t, ∏ x in s.filter (λ x, g x = y), f x ≤ ∏ x in s, f x :=
calc (∏ y in t, ∏ x in s.filter (λ x, g x = y), f x) ≤
  (∏ y in t ∪ s.image g, ∏ x in s.filter (λ x, g x = y), f x) :
  prod_le_prod_of_subset_of_one_le' (subset_union_left _ _) $ λ y hyts, h y
... = ∏ x in s, f x :
  prod_fiberwise_of_maps_to (λ x hx, mem_union.2 $ or.inr $ mem_image_of_mem _ hx) _

@[to_additive sum_le_sum_fiberwise_of_sum_fiber_nonpos]
lemma prod_le_prod_fiberwise_of_prod_fiber_le_one' {t : finset ι'}
  {g : ι → ι'} {f : ι → N} (h : ∀ y ∉ t, (∏ x in s.filter (λ x, g x = y), f x) ≤ 1) :
  (∏ x in s, f x) ≤ ∏ y in t, ∏ x in s.filter (λ x, g x = y), f x :=
@prod_fiberwise_le_prod_of_one_le_prod_fiber' _ (order_dual N) _ _ _ _ _ _ _ h

end

lemma abs_sum_le_sum_abs {G : Type*} [linear_ordered_add_comm_group G] (f : ι → G) (s : finset ι) :
  abs (∑ i in s, f i) ≤ ∑ i in s, abs (f i) :=
le_sum_of_subadditive _ abs_zero abs_add s f

lemma abs_prod {R : Type*} [linear_ordered_comm_ring R] {f : ι → R} {s : finset ι} :
  abs (∏ x in s, f x) = ∏ x in s, abs (f x) :=
(abs_hom.to_monoid_hom : R →* R).map_prod _ _

section pigeonhole

variable [decidable_eq β]

theorem card_le_mul_card_image_of_maps_to {f : α → β} {s : finset α} {t : finset β}
  (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ a ∈ t, (s.filter (λ x, f x = a)).card ≤ n) :
  s.card ≤ n * t.card :=
calc s.card = (∑ a in t, (s.filter (λ x, f x = a)).card) : card_eq_sum_card_fiberwise Hf
        ... ≤ (∑ _ in t, n)                              : sum_le_sum hn
        ... = _                                          : by simp [mul_comm]

theorem card_le_mul_card_image {f : α → β} (s : finset α)
  (n : ℕ) (hn : ∀ a ∈ s.image f, (s.filter (λ x, f x = a)).card ≤ n) :
  s.card ≤ n * (s.image f).card :=
card_le_mul_card_image_of_maps_to (λ x, mem_image_of_mem _) n hn

theorem mul_card_image_le_card_of_maps_to {f : α → β} {s : finset α} {t : finset β}
  (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ a ∈ t, n ≤ (s.filter (λ x, f x = a)).card) :
  n * t.card ≤ s.card :=
calc n * t.card = (∑ _ in t, n) : by simp [mul_comm]
            ... ≤ (∑ a in t, (s.filter (λ x, f x = a)).card) : sum_le_sum hn
            ... = s.card : by rw ← card_eq_sum_card_fiberwise Hf

theorem mul_card_image_le_card {f : α → β} (s : finset α)
  (n : ℕ) (hn : ∀ a ∈ s.image f, n ≤ (s.filter (λ x, f x = a)).card) :
  n * (s.image f).card ≤ s.card :=
mul_card_image_le_card_of_maps_to (λ x, mem_image_of_mem _) n hn

end pigeonhole

section canonically_ordered_monoid

variables [canonically_ordered_monoid M] {f : ι → M} {s t : finset ι}

@[simp, to_additive sum_eq_zero_iff]
lemma prod_eq_one_iff' : ∏ x in s, f x = 1 ↔ ∀ x ∈ s, f x = 1 :=
prod_eq_one_iff_of_one_le' $ λ x hx, one_le (f x)

@[to_additive sum_le_sum_of_subset]
lemma prod_le_prod_of_subset' (h : s ⊆ t) : ∏ x in s, f x ≤ ∏ x in t, f x :=
prod_le_prod_of_subset_of_one_le' h $ assume x h₁ h₂, one_le _

@[to_additive sum_mono_set]
lemma prod_mono_set' (f : ι → M) : monotone (λ s, ∏ x in s, f x) :=
λ s₁ s₂ hs, prod_le_prod_of_subset' hs

@[to_additive sum_le_sum_of_ne_zero]
lemma prod_le_prod_of_ne_one' (h : ∀ x ∈ s, f x ≠ 1 → x ∈ t) :
  ∏ x in s, f x ≤ ∏ x in t, f x :=
by classical;
calc ∏ x in s, f x = (∏ x in s.filter (λ x, f x = 1), f x) * ∏ x in s.filter (λ x, f x ≠ 1), f x :
    by rw [← prod_union, filter_union_filter_neg_eq];
       exact disjoint_filter.2 (assume _ _ h n_h, n_h h)
  ... ≤ (∏ x in t, f x) : mul_le_of_le_one_of_le
      (prod_le_one' $ by simp only [mem_filter, and_imp]; exact λ _ _, le_of_eq)
      (prod_le_prod_of_subset' $ by simpa only [subset_iff, mem_filter, and_imp])

end canonically_ordered_monoid

section ordered_cancel_comm_monoid

variables [ordered_cancel_comm_monoid M] {f g : ι → M} {s t : finset ι}

@[to_additive sum_lt_sum]
theorem prod_lt_prod' (Hle : ∀ i ∈ s, f i ≤ g i) (Hlt : ∃ i ∈ s, f i < g i) :
  ∏ i in s, f i < ∏ i in s, g i :=
begin
  classical,
  rcases Hlt with ⟨i, hi, hlt⟩,
  rw [← insert_erase hi, prod_insert (not_mem_erase _ _), prod_insert (not_mem_erase _ _)],
  exact mul_lt_mul_of_lt_of_le hlt (prod_le_prod'' $ λ j hj, Hle j  $ mem_of_mem_erase hj)
end

@[to_additive sum_lt_sum_of_nonempty]
lemma prod_lt_prod_of_nonempty' (hs : s.nonempty) (Hlt : ∀ i ∈ s, f i < g i) :
  ∏ i in s, f i < ∏ i in s, g i :=
begin
  apply prod_lt_prod',
  { intros i hi, apply le_of_lt (Hlt i hi) },
  cases hs with i hi,
  exact ⟨i, hi, Hlt i hi⟩,
end

@[to_additive sum_lt_sum_of_subset]
lemma prod_lt_prod_of_subset' (h : s ⊆ t) {i : ι} (ht : i ∈ t) (hs : i ∉ s) (hlt : 1 < f i)
  (hle : ∀ j ∈ t, j ∉ s → 1 ≤ f j) :
  ∏ j in s, f j < ∏ j in t, f j :=
by classical;
calc ∏ j in s, f j < ∏ j in insert i s, f j :
begin
  rw prod_insert hs,
  exact lt_mul_of_one_lt_left' (∏ j in s, f j) hlt,
end
... ≤ ∏ j in t, f j :
begin
  apply prod_le_prod_of_subset_of_one_le',
  { simp [finset.insert_subset, h, ht] },
  { assume x hx h'x,
    simp only [mem_insert, not_or_distrib] at h'x,
    exact hle x hx h'x.2 }
end

@[to_additive single_lt_sum]
lemma single_lt_prod' {i j : ι} (hij : j ≠ i) (hi : i ∈ s) (hj : j ∈ s) (hlt : 1 < f j)
  (hle : ∀ k ∈ s, k ≠ i → 1 ≤ f k) :
  f i < ∏ k in s, f k :=
calc f i = ∏ k in {i}, f k : prod_singleton.symm
     ... < ∏ k in s, f k   :
  prod_lt_prod_of_subset' (singleton_subset_iff.2 hi) hj (mt mem_singleton.1 hij) hlt $
    λ k hks hki, hle k hks (mt mem_singleton.2 hki)

end ordered_cancel_comm_monoid

section linear_ordered_cancel_comm_monoid

variables [linear_ordered_cancel_comm_monoid M] {f g : ι → M} {s t : finset ι}

@[to_additive exists_lt_of_sum_lt]
theorem exists_lt_of_prod_lt' (Hlt : ∏ i in s, f i < ∏ i in s, g i) :
  ∃ i ∈ s, f i < g i :=
begin
  contrapose! Hlt with Hle,
  exact prod_le_prod'' Hle
end

@[to_additive exists_le_of_sum_le]
theorem exists_le_of_prod_le' (hs : s.nonempty) (Hle : ∏ i in s, f i ≤ ∏ i in s, g i) :
  ∃ i ∈ s, f i ≤ g i :=
begin
  contrapose! Hle with Hlt,
  exact prod_lt_prod_of_nonempty' hs Hlt
end

@[to_additive exists_pos_of_sum_zero_of_exists_nonzero]
lemma exists_one_lt_of_prod_one_of_exists_ne_one' (f : ι → M)
  (h₁ : ∏ i in s, f i = 1) (h₂ : ∃ i ∈ s, f i ≠ 1) :
  ∃ i ∈ s, 1 < f i :=
begin
  contrapose! h₁,
  obtain ⟨i, m, i_ne⟩ : ∃ i ∈ s, f i ≠ 1 := h₂,
  apply ne_of_lt,
  calc ∏ j in s, f j < ∏ j in s, 1 : prod_lt_prod' h₁ ⟨i, m, (h₁ i m).lt_of_ne i_ne⟩
                 ... = 1           : prod_const_one
end

end linear_ordered_cancel_comm_monoid

section ordered_comm_semiring

variables [ordered_comm_semiring R] {f g : ι → R} {s t : finset ι}
open_locale classical

/- this is also true for a ordered commutative multiplicative monoid -/
lemma prod_nonneg (h0 : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∏ i in s, f i :=
prod_induction f (λ i, 0 ≤ i) (λ _ _ ha hb, mul_nonneg ha hb) zero_le_one h0

/- this is also true for a ordered commutative multiplicative monoid -/
lemma prod_pos [nontrivial R] (h0 : ∀ i ∈ s, 0 < f i) :
  0 < ∏ i in s, f i :=
prod_induction f (λ x, 0 < x) (λ _ _ ha hb, mul_pos ha hb) zero_lt_one h0

/-- If all `f i`, `i ∈ s`, are nonnegative and each `f i` is less than or equal to `g i`, then the
product of `f i` is less than or equal to the product of `g i`. See also `finset.prod_le_prod''` for
the case of an ordered commutative multiplicative monoid. -/
lemma prod_le_prod (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
  ∏ i in s, f i ≤ ∏ i in s, g i :=
begin
  induction s using finset.induction with a s has ih h,
  { simp },
  { simp only [prod_insert has], apply mul_le_mul,
    { exact h1 a (mem_insert_self a s) },
    { apply ih (λ x H, h0 _ _) (λ x H, h1 _ _); exact (mem_insert_of_mem H) },
    { apply prod_nonneg (λ x H, h0 x (mem_insert_of_mem H)) },
    { apply le_trans (h0 a (mem_insert_self a s)) (h1 a (mem_insert_self a s)) } }
end

/-- If each `f i`, `i ∈ s` belongs to `[0, 1]`, then their product is less than or equal to one.
See also `finset.prod_le_one'` for the case of an ordered commutative multiplicative monoid. -/
lemma prod_le_one (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
  ∏ i in s, f i ≤ 1 :=
begin
  convert ← prod_le_prod h0 h1,
  exact finset.prod_const_one
end

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `ordered_comm_semiring`. -/
lemma prod_add_prod_le {i : ι} {f g h : ι → R}
  (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
  (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) (hg : ∀ i ∈ s, 0 ≤ g i) (hh : ∀ i ∈ s, 0 ≤ h i) :
  ∏ i in s, g i + ∏ i in s, h i ≤ ∏ i in s, f i :=
begin
  simp_rw [prod_eq_mul_prod_diff_singleton hi],
  refine le_trans _ (mul_le_mul_of_nonneg_right h2i _),
  { rw [right_distrib],
    apply add_le_add; apply mul_le_mul_of_nonneg_left; try { apply_assumption; assumption };
      apply prod_le_prod; simp * { contextual := tt } },
  { apply prod_nonneg, simp only [and_imp, mem_sdiff, mem_singleton],
    intros j h1j h2j, exact le_trans (hg j h1j) (hgf j h1j h2j) }
end

end ordered_comm_semiring

section canonically_ordered_comm_semiring

variables [canonically_ordered_comm_semiring R] {f g h : ι → R} {s : finset ι} {i : ι}

lemma prod_le_prod' (h : ∀ i ∈ s, f i ≤ g i) :
  ∏ i in s, f i ≤ ∏ i in s, g i :=
begin
  classical,
  induction s using finset.induction with a s has ih h,
  { simp },
  { rw [finset.prod_insert has, finset.prod_insert has],
    apply canonically_ordered_semiring.mul_le_mul,
    { exact h _ (finset.mem_insert_self a s) },
    { exact ih (λ i hi, h _ (finset.mem_insert_of_mem hi)) } }
end

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `canonically_ordered_comm_semiring`.
-/
lemma prod_add_prod_le' (hi : i ∈ s) (h2i : g i + h i ≤ f i)
  (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j) (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) :
  ∏ i in s, g i + ∏ i in s, h i ≤ ∏ i in s, f i :=
begin
  classical, simp_rw [prod_eq_mul_prod_diff_singleton hi],
  refine le_trans _ (canonically_ordered_semiring.mul_le_mul_right' h2i _),
  rw [right_distrib],
  apply add_le_add; apply canonically_ordered_semiring.mul_le_mul_left'; apply prod_le_prod';
  simp only [and_imp, mem_sdiff, mem_singleton]; intros; apply_assumption; assumption
end

end canonically_ordered_comm_semiring

end finset

namespace fintype

variables [fintype ι]

@[mono, to_additive sum_mono]
lemma prod_mono' [ordered_comm_monoid M] : monotone (λ f : ι → M, ∏ i, f i) :=
λ f g hfg, finset.prod_le_prod'' $ λ x _, hfg x

@[to_additive sum_strict_mono]
lemma prod_strict_mono' [ordered_cancel_comm_monoid M] : strict_mono (λ f : ι → M, ∏ x, f x) :=
λ f g hfg, let ⟨hle, i, hlt⟩ := pi.lt_def.mp hfg in
  finset.prod_lt_prod' (λ i _, hle i) ⟨i, finset.mem_univ i, hlt⟩

end fintype

namespace with_top
open finset

/-- A product of finite numbers is still finite -/
lemma prod_lt_top [canonically_ordered_comm_semiring R] [nontrivial R] [decidable_eq R]
  {s : finset ι} {f : ι → with_top R} (h : ∀ i ∈ s, f i < ⊤) :
  ∏ i in s, f i < ⊤ :=
prod_induction f (λ a, a < ⊤) (λ a b, mul_lt_top) (coe_lt_top 1) h

/-- A sum of finite numbers is still finite -/
lemma sum_lt_top [ordered_add_comm_monoid M] {s : finset ι} {f : ι → with_top M} :
  (∀ i ∈ s, f i < ⊤) → (∑ i in s, f i) < ⊤ :=
sum_induction f (λ a, a < ⊤) (by { simp_rw add_lt_top, tauto }) zero_lt_top

/-- A sum of numbers is infinite iff one of them is infinite -/
lemma sum_eq_top_iff [ordered_add_comm_monoid M] {s : finset ι} {f : ι → with_top M} :
  ∑ i in s, f i = ⊤ ↔ ∃ i ∈ s, f i = ⊤ :=
begin
  classical,
  split,
  { contrapose!,
    exact λ h, (sum_lt_top $ λ i hi, lt_top_iff_ne_top.2 (h i hi)).ne },
  { rintro ⟨i, his, hi⟩,
    rw [sum_eq_add_sum_diff_singleton his, hi, top_add] }
end

/-- A sum of finite numbers is still finite -/
lemma sum_lt_top_iff [ordered_add_comm_monoid M] {s : finset ι} {f : ι → with_top M} :
  ∑ i in s, f i < ⊤ ↔ ∀ i ∈ s, f i < ⊤ :=
by simp only [lt_top_iff_ne_top, ne.def, sum_eq_top_iff, not_exists]

end with_top
