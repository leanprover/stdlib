/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import algebra.big_operators.basic
import algebra.linear_ordered_comm_group_with_zero

/-!
# Results about big operators with values in an ordered algebraic structure.

Mostly monotonicity results for the `∑` operation.

-/

universes u v w

open_locale big_operators

variables {α : Type u} {β : Type v} {γ : Type w}

namespace finset
variables {s s₁ s₂ : finset α} {a : α} {f g : α → β}

lemma le_sum_of_subadditive [add_comm_monoid α] [ordered_add_comm_monoid β]
  (f : α → β) (h_zero : f 0 = 0) (h_add : ∀x y, f (x + y) ≤ f x + f y) (s : finset γ) (g : γ → α) :
  f (∑ x in s, g x) ≤ ∑ x in s, f (g x) :=
begin
  refine le_trans (multiset.le_sum_of_subadditive f h_zero h_add _) _,
  rw [multiset.map_map],
  refl
end

lemma abs_sum_le_sum_abs [linear_ordered_field α] {f : β → α} {s : finset β} :
  abs (∑ x in s, f x) ≤ ∑ x in s, abs (f x) :=
le_sum_of_subadditive _ abs_zero abs_add s f

lemma abs_prod [linear_ordered_comm_ring α] {f : β → α} {s : finset β} :
  abs (∏ x in s, f x) = ∏ x in s, abs (f x) :=
(abs_hom.to_monoid_hom : α →* α).map_prod _ _

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid β]

lemma sum_le_sum : (∀x∈s, f x ≤ g x) → (∑ x in s, f x) ≤ (∑ x in s, g x) :=
begin
  classical,
  apply finset.induction_on s,
  exact (λ _, le_refl _),
  assume a s ha ih h,
  have : f a + (∑ x in s, f x) ≤ g a + (∑ x in s, g x),
    from add_le_add (h _ (mem_insert_self _ _)) (ih $ assume x hx, h _ $ mem_insert_of_mem hx),
  by simpa only [sum_insert ha]
end

theorem card_le_mul_card_image_of_maps_to [decidable_eq γ] {f : α → γ} {s : finset α} {t : finset γ}
  (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ a ∈ t, (s.filter (λ x, f x = a)).card ≤ n) :
  s.card ≤ n * t.card :=
calc s.card = (∑ a in t, (s.filter (λ x, f x = a)).card) : card_eq_sum_card_fiberwise Hf
        ... ≤ (∑ _ in t, n)                              : sum_le_sum hn
        ... = _                                          : by simp [mul_comm]

theorem card_le_mul_card_image [decidable_eq γ] {f : α → γ} (s : finset α)
  (n : ℕ) (hn : ∀ a ∈ s.image f, (s.filter (λ x, f x = a)).card ≤ n) :
  s.card ≤ n * (s.image f).card :=
card_le_mul_card_image_of_maps_to (λ x, mem_image_of_mem _) n hn

theorem mul_card_image_le_card_of_maps_to [decidable_eq γ] {f : α → γ} {s : finset α} {t : finset γ}
  (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ a ∈ t, n ≤ (s.filter (λ x, f x = a)).card) :
  n * t.card ≤ s.card :=
calc n * t.card = (∑ _ in t, n) : by simp [mul_comm]
            ... ≤ (∑ a in t, (s.filter (λ x, f x = a)).card) : sum_le_sum hn
            ... = s.card : by rw ← card_eq_sum_card_fiberwise Hf

theorem mul_card_image_le_card [decidable_eq γ] {f : α → γ} (s : finset α)
  (n : ℕ) (hn : ∀ a ∈ s.image f, n ≤ (s.filter (λ x, f x = a)).card) :
  n * (s.image f).card ≤ s.card :=
mul_card_image_le_card_of_maps_to (λ x, mem_image_of_mem _) n hn

lemma sum_nonneg (h : ∀x∈s, 0 ≤ f x) : 0 ≤ (∑ x in s, f x) :=
le_trans (by rw [sum_const_zero]) (sum_le_sum h)

lemma sum_nonpos (h : ∀x∈s, f x ≤ 0) : (∑ x in s, f x) ≤ 0 :=
le_trans (sum_le_sum h) (by rw [sum_const_zero])

lemma sum_le_sum_of_subset_of_nonneg
  (h : s₁ ⊆ s₂) (hf : ∀x∈s₂, x ∉ s₁ → 0 ≤ f x) : (∑ x in s₁, f x) ≤ (∑ x in s₂, f x) :=
by classical;
calc (∑ x in s₁, f x) ≤ (∑ x in s₂ \ s₁, f x) + (∑ x in s₁, f x) :
    le_add_of_nonneg_left $ sum_nonneg $ by simpa only [mem_sdiff, and_imp]
  ... = ∑ x in s₂ \ s₁ ∪ s₁, f x : (sum_union sdiff_disjoint).symm
  ... = (∑ x in s₂, f x)         : by rw [sdiff_union_of_subset h]

lemma sum_mono_set_of_nonneg (hf : ∀ x, 0 ≤ f x) : monotone (λ s, ∑ x in s, f x) :=
λ s₁ s₂ hs, sum_le_sum_of_subset_of_nonneg hs $ λ x _ _, hf x

lemma sum_fiberwise_le_sum_of_sum_fiber_nonneg [decidable_eq γ] {s : finset α} {t : finset γ}
  {g : α → γ} {f : α → β} (h : ∀ y ∉ t, (0 : β) ≤ ∑ x in s.filter (λ x, g x = y), f x) :
  (∑ y in t, ∑ x in s.filter (λ x, g x = y), f x) ≤ ∑ x in s, f x :=
calc (∑ y in t, ∑ x in s.filter (λ x, g x = y), f x) ≤
  (∑ y in t ∪ s.image g, ∑ x in s.filter (λ x, g x = y), f x) :
  sum_le_sum_of_subset_of_nonneg (subset_union_left _ _) $ λ y hyts, h y
... = ∑ x in s, f x :
  sum_fiberwise_of_maps_to (λ x hx, mem_union.2 $ or.inr $ mem_image_of_mem _ hx) _

lemma sum_le_sum_fiberwise_of_sum_fiber_nonpos [decidable_eq γ] {s : finset α} {t : finset γ}
  {g : α → γ} {f : α → β} (h : ∀ y ∉ t, (∑ x in s.filter (λ x, g x = y), f x) ≤ 0) :
  (∑ x in s, f x) ≤ ∑ y in t, ∑ x in s.filter (λ x, g x = y), f x :=
@sum_fiberwise_le_sum_of_sum_fiber_nonneg α (order_dual β) _ _ _ _ _ _ _ h

lemma sum_eq_zero_iff_of_nonneg : (∀x∈s, 0 ≤ f x) → ((∑ x in s, f x) = 0 ↔ ∀x∈s, f x = 0) :=
begin
  classical,
  apply finset.induction_on s,
  exact λ _, ⟨λ _ _, false.elim, λ _, rfl⟩,
  assume a s ha ih H,
  have : ∀ x ∈ s, 0 ≤ f x, from λ _, H _ ∘ mem_insert_of_mem,
  rw [sum_insert ha, add_eq_zero_iff' (H _ $ mem_insert_self _ _) (sum_nonneg this),
    forall_mem_insert, ih this]
end

lemma sum_eq_zero_iff_of_nonpos : (∀x∈s, f x ≤ 0) → ((∑ x in s, f x) = 0 ↔ ∀x∈s, f x = 0) :=
@sum_eq_zero_iff_of_nonneg _ (order_dual β) _ _ _

lemma single_le_sum (hf : ∀x∈s, 0 ≤ f x) {a} (h : a ∈ s) : f a ≤ (∑ x in s, f x) :=
have ∑ x in {a}, f x ≤ (∑ x in s, f x),
  from sum_le_sum_of_subset_of_nonneg
  (λ x e, (mem_singleton.1 e).symm ▸ h) (λ x h _, hf x h),
by rwa sum_singleton at this

end ordered_add_comm_monoid

section canonically_ordered_add_monoid
variables [canonically_ordered_add_monoid β]

@[simp] lemma sum_eq_zero_iff : ∑ x in s, f x = 0 ↔ ∀ x ∈ s, f x = 0 :=
sum_eq_zero_iff_of_nonneg $ λ x hx, zero_le (f x)

lemma sum_le_sum_of_subset (h : s₁ ⊆ s₂) : (∑ x in s₁, f x) ≤ (∑ x in s₂, f x) :=
sum_le_sum_of_subset_of_nonneg h $ assume x h₁ h₂, zero_le _

lemma sum_mono_set (f : α → β) : monotone (λ s, ∑ x in s, f x) :=
λ s₁ s₂ hs, sum_le_sum_of_subset hs

lemma sum_le_sum_of_ne_zero (h : ∀x∈s₁, f x ≠ 0 → x ∈ s₂) :
  (∑ x in s₁, f x) ≤ (∑ x in s₂, f x) :=
by classical;
calc (∑ x in s₁, f x) = ∑ x in s₁.filter (λx, f x = 0), f x + ∑ x in s₁.filter (λx, f x ≠ 0), f x :
    by rw [←sum_union, filter_union_filter_neg_eq];
       exact disjoint_filter.2 (assume _ _ h n_h, n_h h)
  ... ≤ (∑ x in s₂, f x) : add_le_of_nonpos_of_le'
      (sum_nonpos $ by simp only [mem_filter, and_imp]; exact λ _ _, le_of_eq)
      (sum_le_sum_of_subset $ by simpa only [subset_iff, mem_filter, and_imp])

end canonically_ordered_add_monoid

section ordered_cancel_comm_monoid

variables [ordered_cancel_add_comm_monoid β]

theorem sum_lt_sum (Hle : ∀ i ∈ s, f i ≤ g i) (Hlt : ∃ i ∈ s, f i < g i) :
  (∑ x in s, f x) < (∑ x in s, g x) :=
begin
  classical,
  rcases Hlt with ⟨i, hi, hlt⟩,
  rw [← insert_erase hi, sum_insert (not_mem_erase _ _), sum_insert (not_mem_erase _ _)],
  exact add_lt_add_of_lt_of_le hlt (sum_le_sum $ λ j hj, Hle j  $ mem_of_mem_erase hj)
end

lemma sum_lt_sum_of_nonempty (hs : s.nonempty) (Hlt : ∀ x ∈ s, f x < g x) :
  (∑ x in s, f x) < (∑ x in s, g x) :=
begin
  apply sum_lt_sum,
  { intros i hi, apply le_of_lt (Hlt i hi) },
  cases hs with i hi,
  exact ⟨i, hi, Hlt i hi⟩,
end

lemma sum_lt_sum_of_subset [decidable_eq α]
  (h : s₁ ⊆ s₂) {i : α} (hi : i ∈ s₂ \ s₁) (hpos : 0 < f i) (hnonneg : ∀ j ∈ s₂ \ s₁, 0 ≤ f j) :
  (∑ x in s₁, f x) < (∑ x in s₂, f x) :=
calc (∑ x in s₁, f x) < (∑ x in insert i s₁, f x) :
begin
  simp only [mem_sdiff] at hi,
  rw sum_insert hi.2,
  exact lt_add_of_pos_left (∑ x in s₁, f x) hpos,
end
... ≤ (∑ x in s₂, f x) :
begin
  simp only [mem_sdiff] at hi,
  apply sum_le_sum_of_subset_of_nonneg,
  { simp [finset.insert_subset, h, hi.1] },
  { assume x hx h'x,
    apply hnonneg x,
    simp [mem_insert, not_or_distrib] at h'x,
    rw mem_sdiff,
    simp [hx, h'x] }
end

end ordered_cancel_comm_monoid

section linear_ordered_cancel_comm_monoid

variables [linear_ordered_cancel_add_comm_monoid β]

theorem exists_lt_of_sum_lt (Hlt : (∑ x in s, f x) < ∑ x in s, g x) :
  ∃ i ∈ s, f i < g i :=
begin
  contrapose! Hlt with Hle,
  exact sum_le_sum Hle
end

theorem exists_le_of_sum_le (hs : s.nonempty) (Hle : (∑ x in s, f x) ≤ ∑ x in s, g x) :
  ∃ i ∈ s, f i ≤ g i :=
begin
  contrapose! Hle with Hlt,
  rcases hs with ⟨i, hi⟩,
  exact sum_lt_sum (λ i hi, le_of_lt (Hlt i hi)) ⟨i, hi, Hlt i hi⟩
end

lemma exists_pos_of_sum_zero_of_exists_nonzero (f : α → β)
  (h₁ : ∑ e in s, f e = 0) (h₂ : ∃ x ∈ s, f x ≠ 0) :
  ∃ x ∈ s, 0 < f x :=
begin
  contrapose! h₁,
  obtain ⟨x, m, x_nz⟩ : ∃ x ∈ s, f x ≠ 0 := h₂,
  apply ne_of_lt,
  calc ∑ e in s, f e < ∑ e in s, 0 : sum_lt_sum h₁ ⟨x, m, lt_of_le_of_ne (h₁ x m) x_nz⟩
                 ... = 0           : by rw [finset.sum_const, nsmul_zero],
end

end linear_ordered_cancel_comm_monoid

section linear_ordered_comm_monoid_with_zero
variables [linear_ordered_comm_monoid_with_zero β]

lemma prod_nonneg' {s : finset α} {f : α → β}
  (h0 : ∀(x ∈ s), 0 ≤ f x) : 0 ≤ (∏ x in s, f x) :=
begin
  refine prod_induction f (λ x, 0 ≤ x) _ linear_ordered_comm_monoid_with_zero.zero_le_one h0,
  intros a b ha hb,
  rw ← mul_zero (0:β),
  exact mul_le_mul' ha hb
end

lemma prod_le_prod'' {s : finset α} {f g : α → β} (h0 : ∀(x ∈ s), 0 ≤ f x)
  (h1 : ∀(x ∈ s), f x ≤ g x) : (∏ x in s, f x) ≤ (∏ x in s, g x) :=
begin
  classical,
  induction s using finset.induction with a s has ih h,
  { simp },
  { simp [has], apply mul_le_mul',
      exact h1 a (mem_insert_self a s),
      apply ih (λ x H, h0 _ _) (λ x H, h1 _ _); exact (mem_insert_of_mem H) }
end

lemma prod_le_one' {s : finset α} {f : α → β} (h0 : ∀(x ∈ s), 0 ≤ f x)
  (h1 : ∀(x ∈ s), f x ≤ 1) : (∏ x in s, f x) ≤ 1 :=
begin
  convert ← prod_le_prod'' h0 h1,
  exact finset.prod_const_one
end

end linear_ordered_comm_monoid_with_zero

section linear_ordered_comm_ring

variables [linear_ordered_comm_ring β]
open_locale classical

lemma prod_nonneg {s : finset α} {f : α → β}
  (h0 : ∀(x ∈ s), 0 ≤ f x) : 0 ≤ (∏ x in s, f x) :=
prod_induction f (λ x, 0 ≤ x) (λ _ _ ha hb, mul_nonneg ha hb) zero_le_one h0

lemma prod_pos {s : finset α} {f : α → β} (h0 : ∀(x ∈ s), 0 < f x) : 0 < (∏ x in s, f x) :=
prod_induction f (λ x, 0 < x) (λ _ _ ha hb, mul_pos ha hb) zero_lt_one h0

lemma prod_le_prod {s : finset α} {f g : α → β} (h0 : ∀(x ∈ s), 0 ≤ f x)
  (h1 : ∀(x ∈ s), f x ≤ g x) : (∏ x in s, f x) ≤ (∏ x in s, g x) :=
begin
  induction s using finset.induction with a s has ih h,
  { simp },
  { simp [has], apply mul_le_mul,
      exact h1 a (mem_insert_self a s),
      apply ih (λ x H, h0 _ _) (λ x H, h1 _ _); exact (mem_insert_of_mem H),
      apply prod_nonneg (λ x H, h0 x (mem_insert_of_mem H)),
      apply le_trans (h0 a (mem_insert_self a s)) (h1 a (mem_insert_self a s)) }
end

lemma prod_le_one {s : finset α} {f : α → β} (h0 : ∀(x ∈ s), 0 ≤ f x)
  (h1 : ∀(x ∈ s), f x ≤ 1) : (∏ x in s, f x) ≤ 1 :=
begin
  convert ← prod_le_prod h0 h1,
  exact finset.prod_const_one
end

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `linear_ordered_comm_ring`. -/
lemma prod_add_prod_le {s : finset α} {i : α} {f g h : α → β}
  (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
  (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) (hg : ∀ i ∈ s, 0 ≤ g i) (hh : ∀ i ∈ s, 0 ≤ h i) :
  ∏ i in s, g i + ∏ i in s, h i ≤ ∏ i in s, f i :=
begin
  simp_rw [← mul_prod_diff_singleton hi],
  refine le_trans _ (mul_le_mul_of_nonneg_right h2i _),
  { rw [right_distrib],
    apply add_le_add; apply mul_le_mul_of_nonneg_left; try { apply prod_le_prod };
    simp only [and_imp, mem_sdiff, mem_singleton]; intros; apply_assumption; assumption },
  { apply prod_nonneg, simp only [and_imp, mem_sdiff, mem_singleton],
    intros j h1j h2j, refine le_trans (hg j h1j) (hgf j h1j h2j) }
end

end linear_ordered_comm_ring

section canonically_ordered_comm_semiring

variables [canonically_ordered_comm_semiring β]

lemma prod_le_prod' {s : finset α} {f g : α → β} (h : ∀ i ∈ s, f i ≤ g i) :
  (∏ x in s, f x) ≤ (∏ x in s, g x) :=
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
lemma prod_add_prod_le' {s : finset α} {i : α} {f g h : α → β} (hi : i ∈ s) (h2i : g i + h i ≤ f i)
  (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j) (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) :
  ∏ i in s, g i + ∏ i in s, h i ≤ ∏ i in s, f i :=
begin
  classical, simp_rw [← mul_prod_diff_singleton hi],
  refine le_trans _ (canonically_ordered_semiring.mul_le_mul_right' h2i _),
  rw [right_distrib],
  apply add_le_add; apply canonically_ordered_semiring.mul_le_mul_left'; apply prod_le_prod';
  simp only [and_imp, mem_sdiff, mem_singleton]; intros; apply_assumption; assumption
end

end canonically_ordered_comm_semiring

end finset

namespace fintype

variables [fintype α]

@[mono] lemma sum_mono [ordered_add_comm_monoid β] : monotone (λ f : α → β, ∑ x, f x) :=
λ f g hfg, finset.sum_le_sum $ λ x _, hfg x

lemma sum_strict_mono [ordered_cancel_add_comm_monoid β] : strict_mono (λ f : α → β, ∑ x, f x) :=
λ f g hfg, let ⟨hle, i, hlt⟩ := pi.lt_def.mp hfg in
  finset.sum_lt_sum (λ i _, hle i) ⟨i, finset.mem_univ i, hlt⟩

end fintype

namespace with_top
open finset

/-- A product of finite numbers is still finite -/
lemma prod_lt_top [canonically_ordered_comm_semiring β] [nontrivial β] [decidable_eq β]
  {s : finset α} {f : α → with_top β} (h : ∀ a ∈ s, f a < ⊤) :
  (∏ x in s, f x) < ⊤ :=
prod_induction f (λ a, a < ⊤) (λ a b, mul_lt_top) (coe_lt_top 1) h

/-- A sum of finite numbers is still finite -/
lemma sum_lt_top [ordered_add_comm_monoid β] {s : finset α} {f : α → with_top β} :
  (∀a∈s, f a < ⊤) → (∑ x in s, f x) < ⊤ :=
λ h, sum_induction f (λ a, a < ⊤) (by { simp_rw add_lt_top, tauto }) zero_lt_top h

/-- A sum of finite numbers is still finite -/
lemma sum_lt_top_iff [canonically_ordered_add_monoid β] {s : finset α} {f : α → with_top β} :
  (∑ x in s, f x) < ⊤ ↔ (∀a∈s, f a < ⊤) :=
iff.intro (λh a ha, lt_of_le_of_lt (single_le_sum (λa ha, zero_le _) ha) h) sum_lt_top

/-- A sum of numbers is infinite iff one of them is infinite -/
lemma sum_eq_top_iff [canonically_ordered_add_monoid β] {s : finset α} {f : α → with_top β} :
  (∑ x in s, f x) = ⊤ ↔ (∃a∈s, f a = ⊤) :=
begin
  rw ← not_iff_not,
  push_neg,
  simp only [← lt_top_iff_ne_top],
  exact sum_lt_top_iff
end

end with_top
