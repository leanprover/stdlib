/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.fintype.basic
import data.nat.choose
import tactic.ring

/-!
Results about "big operations" over a `fintype`, and consequent
results about cardinalities of certain types.

## Implementation note
This content had previously been in `data.fintype`, but was moved here to avoid
requiring `algebra.big_operators` (and hence many other imports) as a
dependency of `fintype`.
-/

universes u v

variables {α : Type*} {β : Type*} {γ : Type*}

open_locale big_operators

namespace fintype

lemma card_eq_sum_ones {α} [fintype α] : fintype.card α = ∑ a : α, 1 :=
finset.card_eq_sum_ones _

section
open finset

variables {ι : Type*} [fintype ι] [decidable_eq ι]

@[to_additive]
lemma prod_extend_by_one [comm_monoid α] (s : finset ι) (f : ι → α) :
  ∏ i, (if i ∈ s then f i else 1) = ∏ i in s, f i :=
by rw [← prod_filter, filter_mem_eq_inter, univ_inter]

end

section
variables {M : Type*} [fintype α] [comm_monoid M]

@[to_additive]
lemma prod_eq_one (f : α → M) (h : ∀ a, f a = 1) :
  (∏ a, f a) = 1 :=
finset.prod_eq_one $ λ a ha, h a

@[to_additive]
lemma prod_congr (f g : α → M) (h : ∀ a, f a = g a) :
  (∏ a, f a) = ∏ a, g a :=
finset.prod_congr rfl $ λ a ha, h a

@[to_additive]
lemma prod_unique [unique β] (f : β → M) :
  (∏ x, f x) = f (default β) :=
by simp only [finset.prod_singleton, univ_unique]

end

end fintype

open finset

theorem fin.prod_univ_succ [comm_monoid β] {n:ℕ} (f : fin n.succ → β) :
  univ.prod f = f 0 * univ.prod (λ i:fin n, f i.succ) :=
begin
  rw [fin.univ_succ, prod_insert, prod_image],
  { intros x _ y _ hxy, exact fin.succ.inj hxy },
  { simpa using fin.succ_ne_zero }
end

@[simp, to_additive] theorem fin.prod_univ_zero [comm_monoid β] (f : fin 0 → β) : univ.prod f = 1 := rfl

theorem fin.sum_univ_succ [add_comm_monoid β] {n:ℕ} (f : fin n.succ → β) :
  univ.sum f = f 0 + univ.sum (λ i:fin n, f i.succ) :=
@fin.prod_univ_succ (multiplicative β) _ _ f

attribute [to_additive] fin.prod_univ_succ

theorem fin.prod_univ_cast_succ [comm_monoid β] {n:ℕ} (f : fin n.succ → β) :
  univ.prod f = univ.prod (λ i:fin n, f i.cast_succ) * f (fin.last n) :=
begin
  rw [fin.univ_cast_succ, prod_insert, prod_image, mul_comm],
  { intros x _ y _ hxy, exact fin.cast_succ_inj.mp hxy },
  { simpa using fin.cast_succ_ne_last }
end

theorem fin.sum_univ_cast_succ [add_comm_monoid β] {n:ℕ} (f : fin n.succ → β) :
  univ.sum f = univ.sum (λ i:fin n, f i.cast_succ) + f (fin.last n) :=
@fin.prod_univ_cast_succ (multiplicative β) _ _ f
attribute [to_additive] fin.prod_univ_cast_succ

@[simp] theorem fintype.card_sigma {α : Type*} (β : α → Type*)
  [fintype α] [∀ a, fintype (β a)] :
  fintype.card (sigma β) = univ.sum (λ a, fintype.card (β a)) :=
card_sigma _ _

-- FIXME ouch, this should be in the main file.
@[simp] theorem fintype.card_sum (α β : Type*) [fintype α] [fintype β] :
  fintype.card (α ⊕ β) = fintype.card α + fintype.card β :=
by simp [sum.fintype, fintype.of_equiv_card]

@[simp] lemma fintype.card_pi_finset [decidable_eq α] [fintype α]
  {δ : α → Type*} (t : Π a, finset (δ a)) :
  (fintype.pi_finset t).card = finset.univ.prod (λ a, card (t a)) :=
by simp [fintype.pi_finset, card_map]

@[simp] lemma fintype.card_pi {β : α → Type*} [fintype α] [decidable_eq α]
  [f : Π a, fintype (β a)] : fintype.card (Π a, β a) = univ.prod (λ a, fintype.card (β a)) :=
fintype.card_pi_finset _

-- FIXME ouch, this should be in the main file.
@[simp] lemma fintype.card_fun [fintype α] [decidable_eq α] [fintype β] :
  fintype.card (α → β) = fintype.card β ^ fintype.card α :=
by rw [fintype.card_pi, finset.prod_const, nat.pow_eq_pow]; refl

@[simp] lemma card_vector [fintype α] (n : ℕ) :
  fintype.card (vector α n) = fintype.card α ^ n :=
by rw fintype.of_equiv_card; simp


@[simp, to_additive]
lemma finset.prod_attach_univ [fintype α] [comm_monoid β] (f : {a : α // a ∈ @univ α _} → β) :
  univ.attach.prod (λ x, f x) = univ.prod (λ x, f ⟨x, (mem_univ _)⟩) :=
prod_bij (λ x _, x.1) (λ _ _, mem_univ _) (λ _ _ , by simp) (by simp) (λ b _, ⟨⟨b, mem_univ _⟩, by simp⟩)

@[to_additive]
lemma finset.range_prod_eq_univ_prod [comm_monoid β] (n : ℕ) (f : ℕ → β) :
  (range n).prod f = univ.prod (λ (k : fin n), f k) :=
begin
  symmetry,
  refine prod_bij (λ k hk, k) _ _ _ _,
  { rintro ⟨k, hk⟩ _, simp * },
  { rintro ⟨k, hk⟩ _, simp * },
  { intros, rwa fin.eq_iff_veq },
  { intros k hk, rw mem_range at hk,
    exact ⟨⟨k, hk⟩, mem_univ _, rfl⟩ }
end

/-- Taking a product over `univ.pi t` is the same as taking the product over `fintype.pi_finset t`.
  `univ.pi t` and `fintype.pi_finset t` are essentially the same `finset`, but differ
  in the type of their element, `univ.pi t` is a `finset (Π a ∈ univ, t a)` and
  `fintype.pi_finset t` is a `finset (Π a, t a)`. -/
@[to_additive "Taking a sum over `univ.pi t` is the same as taking the sum over
  `fintype.pi_finset t`. `univ.pi t` and `fintype.pi_finset t` are essentially the same `finset`,
  but differ in the type of their element, `univ.pi t` is a `finset (Π a ∈ univ, t a)` and
  `fintype.pi_finset t` is a `finset (Π a, t a)`."]
lemma finset.prod_univ_pi [decidable_eq α] [fintype α] [comm_monoid β]
  {δ : α → Type*} {t : Π (a : α), finset (δ a)}
  (f : (Π (a : α), a ∈ (univ : finset α) → δ a) → β) :
  (univ.pi t).prod f = (fintype.pi_finset t).prod (λ x, f (λ a _, x a)) :=
prod_bij (λ x _ a, x a (mem_univ _))
  (by simp)
  (by simp)
  (by simp [function.funext_iff] {contextual := tt})
  (λ x hx, ⟨λ a _, x a, by simp * at *⟩)

/-- The product over `univ` of a sum can be written as a sum over the product of sets,
  `fintype.pi_finset`. `finset.prod_sum` is an alternative statement when the product is not
  over `univ` -/
lemma finset.prod_univ_sum [decidable_eq α] [fintype α] [comm_semiring β] {δ : α → Type u_1}
  [Π (a : α), decidable_eq (δ a)] {t : Π (a : α), finset (δ a)}
  {f : Π (a : α), δ a → β} :
  univ.prod (λ a, (t a).sum (λ b, f a b)) =
  (fintype.pi_finset t).sum (λ p, univ.prod (λ x, f x (p x))) :=
by simp only [finset.prod_attach_univ, prod_sum, finset.sum_univ_pi]

/-- Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a fintype of cardinality `n`
gives `(a + b)^n`. The "good" proof involves expanding along all coordinates using the fact that
`x^n` is multilinear, but multilinear maps are only available now over rings, so we give instead
a proof reducing to the usual binomial theorem to have a result over semirings. -/
lemma fintype.sum_pow_mul_eq_add_pow
  (α : Type*) [fintype α] {R : Type*} [comm_semiring R] (a b : R) :
  finset.univ.sum (λ (s : finset α), a ^ s.card * b ^ (fintype.card α - s.card)) =
  (a + b) ^ (fintype.card α) :=
finset.sum_pow_mul_eq_add_pow _ _ _

lemma fin.sum_pow_mul_eq_add_pow {n : ℕ} {R : Type*} [comm_semiring R] (a b : R) :
  finset.univ.sum (λ (s : finset (fin n)), a ^ s.card * b ^ (n - s.card)) =
  (a + b) ^ n :=
by simpa using fintype.sum_pow_mul_eq_add_pow (fin n) a b

/-- It is equivalent to sum a function over `fin n` or `finset.range n`. -/
@[to_additive]
lemma fin.prod_univ_eq_prod_range [comm_monoid α] (f : ℕ → α) (n : ℕ) :
  finset.univ.prod (λ (i : fin n), f i.val) = (finset.range n).prod f :=
begin
  apply finset.prod_bij (λ (a : fin n) ha, a.val),
  { assume a ha, simp [a.2] },
  { assume a ha, refl },
  { assume a b ha hb H, exact (fin.ext_iff _ _).2 H },
  { assume b hb, exact ⟨⟨b, list.mem_range.mp hb⟩, finset.mem_univ _, rfl⟩, }
end

@[to_additive]
lemma finset.prod_equiv [fintype α] [fintype β] [comm_monoid γ] (e : α ≃ β) (f : β → γ) :
  finset.univ.prod (f ∘ e) = finset.univ.prod f :=
begin
  apply prod_bij (λ i hi, e i) (λ i hi, mem_univ _) _ (λ a b _ _ h, e.injective h),
  { assume b hb,
    rcases e.surjective b with ⟨a, ha⟩,
    exact ⟨a, mem_univ _, ha.symm⟩, },
  { simp }
end

@[to_additive]
lemma finset.prod_subtype {M : Type*} [comm_monoid M]
  {p : α → Prop} {F : fintype (subtype p)} {s : finset α} (h : ∀ x, x ∈ s ↔ p x) (f : α → M) :
  ∏ a in s, f a = ∏ a : subtype p, f a :=
have (∈ s) = p, from set.ext h,
begin
  rw ← prod_attach,
  resetI,
  subst p,
  congr,
  simp [finset.ext]
end

@[to_additive] lemma finset.prod_fiberwise [fintype β] [decidable_eq β] [comm_monoid γ]
  (s : finset α) (f : α → β) (g : α → γ) :
  ∏ b : β, ∏ a in s.filter (λ a, f a = b), g a = ∏ a in s, g a :=
begin
  classical,
  have key : ∏ (b : β), ∏ a in s.filter (λ a, f a = b), g a =
    ∏ (a : α) in univ.bind (λ (b : β), s.filter (λ a, f a = b)), g a :=
  (@prod_bind _ _ β g _ _ finset.univ (λ b : β, s.filter (λ a, f a = b)) _).symm,
  { simp only [key, filter_congr_decidable],
    apply finset.prod_congr,
    { ext, simp only [mem_bind, mem_filter, mem_univ, exists_prop_of_true, exists_eq_right'] },
    { intros, refl } },
  { intros x hx y hy H z hz, apply H,
    simp only [mem_filter, inf_eq_inter, mem_inter] at hz,
    rw [← hz.1.2, ← hz.2.2] }
end

@[to_additive]
lemma fintype.prod_fiberwise [fintype α] [fintype β] [decidable_eq β] [comm_monoid γ]
  (f : α → β) (g : α → γ) :
  (∏ b : β, ∏ a : {a // f a = b}, g (a : α)) = ∏ a, g a :=
begin
  rw [← finset.prod_equiv (equiv.sigma_preimage_equiv f) _, ← univ_sigma_univ, prod_sigma],
  refl
end

section
open finset

variables {α₁ : Type*} {α₂ : Type*} {M : Type*} [fintype α₁] [fintype α₂] [comm_monoid M]

@[to_additive]
lemma fintype.prod_sum_type (f : α₁ ⊕ α₂ → M) :
  (∏ x, f x) = (∏ a₁, f (sum.inl a₁)) * (∏ a₂, f (sum.inr a₂)) :=
begin
  classical,
  let s : finset (α₁ ⊕ α₂) := univ.image sum.inr,
  rw [← prod_sdiff (subset_univ s),
      ← @prod_image (α₁ ⊕ α₂) _ _ _ _ _ _ sum.inl,
      ← @prod_image (α₁ ⊕ α₂) _ _ _ _ _ _ sum.inr],
  { congr, rw finset.ext, rintro (a|a);
    { simp only [mem_image, exists_eq, mem_sdiff, mem_univ, exists_false,
        exists_prop_of_true, not_false_iff, and_self, not_true, and_false], } },
  all_goals { intros, solve_by_elim [sum.inl.inj, sum.inr.inj], }
end

end

namespace list

lemma prod_take_of_fn [comm_monoid α] {n : ℕ} (f : fin n → α) (i : ℕ) :
  ((of_fn f).take i).prod = (finset.univ.filter (λ (j : fin n), j.val < i)).prod f :=
begin
  have A : ∀ (j : fin n), ¬ (j.val < 0) := λ j, not_lt_bot,
  induction i with i IH, { simp [A] },
  by_cases h : i < n,
  { have : i < length (of_fn f), by rwa [length_of_fn f],
    rw prod_take_succ _ _ this,
    have A : ((finset.univ : finset (fin n)).filter (λ j, j.val < i + 1))
      = ((finset.univ : finset (fin n)).filter (λ j, j.val < i)) ∪ {(⟨i, h⟩ : fin n)},
        by { ext j, simp [nat.lt_succ_iff_lt_or_eq, fin.ext_iff, - add_comm] },
    have B : _root_.disjoint (finset.filter (λ (j : fin n), j.val < i) finset.univ)
      (singleton (⟨i, h⟩ : fin n)), by simp,
    rw [A, finset.prod_union B, IH],
    simp },
  { have A : (of_fn f).take i = (of_fn f).take i.succ,
    { rw ← length_of_fn f at h,
      have : length (of_fn f) ≤ i := not_lt.mp h,
      rw [take_all_of_le this, take_all_of_le (le_trans this (nat.le_succ _))] },
    have B : ∀ (j : fin n), (j.val < i.succ) = (j.val < i),
    { assume j,
      have : j.val < i := lt_of_lt_of_le j.2 (not_lt.mp h),
      simp [this, lt_trans this (nat.lt_succ_self _)] },
    simp [← A, B, IH] }
end

-- `to_additive` does not work on `prod_take_of_fn` because of `0 : ℕ` in the proof. Copy-paste the
-- proof instead...
lemma sum_take_of_fn [add_comm_monoid α] {n : ℕ} (f : fin n → α) (i : ℕ) :
  ((of_fn f).take i).sum = (finset.univ.filter (λ (j : fin n), j.val < i)).sum f :=
begin
  have A : ∀ (j : fin n), ¬ (j.val < 0) := λ j, not_lt_bot,
  induction i with i IH, { simp [A] },
  by_cases h : i < n,
  { have : i < length (of_fn f), by rwa [length_of_fn f],
    rw sum_take_succ _ _ this,
    have A : ((finset.univ : finset (fin n)).filter (λ j, j.val < i + 1))
      = ((finset.univ : finset (fin n)).filter (λ j, j.val < i)) ∪ singleton (⟨i, h⟩ : fin n),
        by { ext j, simp [nat.lt_succ_iff_lt_or_eq, fin.ext_iff, - add_comm] },
    have B : _root_.disjoint (finset.filter (λ (j : fin n), j.val < i) finset.univ)
      (singleton (⟨i, h⟩ : fin n)), by simp,
    rw [A, finset.sum_union B, IH],
    simp },
  { have A : (of_fn f).take i = (of_fn f).take i.succ,
    { rw ← length_of_fn f at h,
      have : length (of_fn f) ≤ i := not_lt.mp h,
      rw [take_all_of_le this, take_all_of_le (le_trans this (nat.le_succ _))] },
    have B : ∀ (j : fin n), (j.val < i.succ) = (j.val < i),
    { assume j,
      have : j.val < i := lt_of_lt_of_le j.2 (not_lt.mp h),
      simp [this, lt_trans this (nat.lt_succ_self _)] },
    simp [← A, B, IH] }
end

attribute [to_additive] prod_take_of_fn

@[to_additive]
lemma prod_of_fn [comm_monoid α] {n : ℕ} {f : fin n → α} :
  (of_fn f).prod = finset.univ.prod f :=
begin
  convert prod_take_of_fn f n,
  { rw [take_all_of_le (le_of_eq (length_of_fn f))] },
  { have : ∀ (j : fin n), j.val < n := λ j, j.2,
    simp [this] }
end

end list
