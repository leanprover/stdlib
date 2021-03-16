/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.fintype.basic
import algebra.big_operators.ring

/-!
Results about "big operations" over a `fintype`, and consequent
results about cardinalities of certain types.

## Implementation note
This content had previously been in `data.fintype.basic`, but was moved here to avoid
requiring `algebra.big_operators` (and hence many other imports) as a
dependency of `fintype`.

However many of the results here really belong in `algebra.big_operators.basic`
and should be moved at some point.
-/

universes u v

variables {α : Type*} {β : Type*} {γ : Type*}

open_locale big_operators

namespace fintype

@[to_additive]
lemma prod_bool [comm_monoid α] (f : bool → α) : ∏ b, f b = f tt * f ff := by simp

lemma card_eq_sum_ones {α} [fintype α] : fintype.card α = ∑ a : α, 1 :=
finset.card_eq_sum_ones _

section
open finset

variables {ι : Type*} [decidable_eq ι] [fintype ι]

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
lemma prod_eq_single {f : α → M} (a : α) (h : ∀ x ≠ a, f x = 1) :
  (∏ x, f x) = f a :=
finset.prod_eq_single a (λ x _ hx, h x hx) $ λ ha, (ha (finset.mem_univ a)).elim

@[to_additive]
lemma prod_unique [unique β] (f : β → M) :
  (∏ x, f x) = f (default β) :=
by simp only [finset.prod_singleton, univ_unique]

/-- If a product of a `finset` of a subsingleton type has a given
value, so do the terms in that product. -/
@[to_additive "If a sum of a `finset` of a subsingleton type has a given
value, so do the terms in that sum."]
lemma eq_of_subsingleton_of_prod_eq {ι : Type*} [subsingleton ι] {s : finset ι}
    {f : ι → M} {b : M} (h : ∏ i in s, f i = b) : ∀ i ∈ s, f i = b :=
finset.eq_of_card_le_one_of_prod_eq (finset.card_le_one_of_subsingleton s) h

end

end fintype

open finset

section

variables {M : Type*} [fintype α] [comm_monoid M]

@[simp, to_additive]
lemma fintype.prod_option (f : option α → M) : ∏ i, f i = f none * ∏ i, f (some i) :=
show ((finset.insert_none _).1.map f).prod = _,
by simp only [finset.prod, finset.insert_none, multiset.map_cons, multiset.prod_cons,
  multiset.map_map]

end

@[to_additive]
theorem fin.prod_univ_def [comm_monoid β] {n : ℕ} (f : fin n → β) :
  ∏ i, f i = ((list.fin_range n).map f).prod :=
by simp [fin.univ_def, finset.fin_range]

@[to_additive]
theorem fin.prod_of_fn [comm_monoid β] {n : ℕ} (f : fin n → β) :
  (list.of_fn f).prod = ∏ i, f i :=
by rw [list.of_fn_eq_map, fin.prod_univ_def]

/-- A product of a function `f : fin 0 → β` is `1` because `fin 0` is empty -/
@[simp, to_additive "A sum of a function `f : fin 0 → β` is `0` because `fin 0` is empty"]
theorem fin.prod_univ_zero [comm_monoid β] (f : fin 0 → β) : ∏ i, f i = 1 := rfl

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f x`, for some `x : fin (n + 1)` times the remaining product -/
theorem fin.prod_univ_succ_above [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) (x : fin (n + 1)) :
  ∏ i, f i = f x * ∏ i : fin n, f (x.succ_above i) :=
begin
  rw [fin.univ_succ_above, finset.prod_insert, finset.prod_image],
  { intros x _ y _ hxy, exact fin.succ_above_right_inj.mp hxy },
  { simp [fin.succ_above_ne] }
end

/-- A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the sum of `f x`, for some `x : fin (n + 1)` plus the remaining product -/
theorem fin.sum_univ_succ_above [add_comm_monoid β] {n : ℕ} (f : fin (n + 1) → β)
  (x : fin (n + 1)) :
  ∑ i, f i = f x + ∑ i : fin n, f (x.succ_above i) :=
by simpa using congr_arg multiplicative.to_add
  (fin.prod_univ_succ_above (multiplicative.of_add ∘ f) _)

attribute [to_additive] fin.prod_univ_succ_above

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f 0` plus the remaining product -/
theorem fin.prod_univ_succ [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) :
  ∏ i, f i = f 0 * ∏ i : fin n, f i.succ :=
fin.prod_univ_succ_above f 0

/-- A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the sum of `f 0` plus the remaining product -/
theorem fin.sum_univ_succ [add_comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) :
  ∑ i, f i = f 0 + ∑ i : fin n, f i.succ :=
fin.sum_univ_succ_above f 0

attribute [to_additive] fin.prod_univ_succ

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f (fin.last n)` plus the remaining product -/
theorem fin.prod_univ_cast_succ [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) :
  ∏ i, f i = (∏ i : fin n, f i.cast_succ) * f (fin.last n) :=
by simpa [mul_comm] using fin.prod_univ_succ_above f (fin.last n)

/-- A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the sum of `f (fin.last n)` plus the remaining sum -/
theorem fin.sum_univ_cast_succ [add_comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) :
  ∑ i, f i = ∑ i : fin n, f i.cast_succ + f (fin.last n) :=
by simpa using congr_arg multiplicative.to_add (fin.prod_univ_cast_succ (multiplicative.of_add ∘ f))

attribute [to_additive] fin.prod_univ_cast_succ

open finset

@[simp] theorem fintype.card_sigma {α : Type*} (β : α → Type*)
  [fintype α] [∀ a, fintype (β a)] :
  fintype.card (sigma β) = ∑ a, fintype.card (β a) :=
card_sigma _ _

-- FIXME ouch, this should be in the main file.
@[simp] theorem fintype.card_sum (α β : Type*) [fintype α] [fintype β] :
  fintype.card (α ⊕ β) = fintype.card α + fintype.card β :=
by simp [sum.fintype, fintype.of_equiv_card]

@[simp] lemma finset.card_pi [decidable_eq α] {δ : α → Type*}
  (s : finset α) (t : Π a, finset (δ a)) :
  (s.pi t).card = ∏ a in s, card (t a) :=
multiset.card_pi _ _

@[simp] lemma fintype.card_pi_finset [decidable_eq α] [fintype α]
  {δ : α → Type*} (t : Π a, finset (δ a)) :
  (fintype.pi_finset t).card = ∏ a, card (t a) :=
by simp [fintype.pi_finset, card_map]

@[simp] lemma fintype.card_pi {β : α → Type*} [decidable_eq α] [fintype α]
  [f : Π a, fintype (β a)] : fintype.card (Π a, β a) = ∏ a, fintype.card (β a) :=
fintype.card_pi_finset _

-- FIXME ouch, this should be in the main file.
@[simp] lemma fintype.card_fun [decidable_eq α] [fintype α] [fintype β] :
  fintype.card (α → β) = fintype.card β ^ fintype.card α :=
by rw [fintype.card_pi, finset.prod_const]; refl

@[simp] lemma card_vector [fintype α] (n : ℕ) :
  fintype.card (vector α n) = fintype.card α ^ n :=
by rw fintype.of_equiv_card; simp

@[simp, to_additive]
lemma finset.prod_attach_univ [fintype α] [comm_monoid β] (f : {a : α // a ∈ @univ α _} → β) :
  ∏ x in univ.attach, f x = ∏ x, f ⟨x, (mem_univ _)⟩ :=
prod_bij (λ x _, x.1) (λ _ _, mem_univ _) (λ _ _ , by simp) (by simp)
  (λ b _, ⟨⟨b, mem_univ _⟩, by simp⟩)

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
  ∏ x in univ.pi t, f x = ∏ x in fintype.pi_finset t, f (λ a _, x a) :=
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
  ∏ a, ∑ b in t a, f a b = ∑ p in fintype.pi_finset t, ∏ x, f x (p x) :=
by simp only [finset.prod_attach_univ, prod_sum, finset.sum_univ_pi]

/-- Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a fintype of cardinality `n`
gives `(a + b)^n`. The "good" proof involves expanding along all coordinates using the fact that
`x^n` is multilinear, but multilinear maps are only available now over rings, so we give instead
a proof reducing to the usual binomial theorem to have a result over semirings. -/
lemma fintype.sum_pow_mul_eq_add_pow
  (α : Type*) [fintype α] {R : Type*} [comm_semiring R] (a b : R) :
  ∑ s : finset α, a ^ s.card * b ^ (fintype.card α - s.card) =
  (a + b) ^ (fintype.card α) :=
finset.sum_pow_mul_eq_add_pow _ _ _

lemma fin.sum_pow_mul_eq_add_pow {n : ℕ} {R : Type*} [comm_semiring R] (a b : R) :
  ∑ s : finset (fin n), a ^ s.card * b ^ (n - s.card) =
  (a + b) ^ n :=
by simpa using fintype.sum_pow_mul_eq_add_pow (fin n) a b

@[to_additive]
lemma function.bijective.prod_comp [fintype α] [fintype β] [comm_monoid γ] {f : α → β}
  (hf : function.bijective f) (g : β → γ) :
  ∏ i, g (f i) = ∏ i, g i :=
prod_bij (λ i hi, f i) (λ i hi, mem_univ _) (λ i hi, rfl) (λ i j _ _ h, hf.1 h) $
  λ i hi, (hf.2 i).imp $ λ j hj, ⟨mem_univ _, hj.symm⟩

@[to_additive]
lemma equiv.prod_comp [fintype α] [fintype β] [comm_monoid γ] (e : α ≃ β) (f : β → γ) :
  ∏ i, f (e i) = ∏ i, f i :=
e.bijective.prod_comp f

/-- It is equivalent to sum a function over `fin n` or `finset.range n`. -/
@[to_additive]
lemma fin.prod_univ_eq_prod_range [comm_monoid α] (f : ℕ → α) (n : ℕ) :
  ∏ i : fin n, f i = ∏ i in range n, f i :=
calc (∏ i : fin n, f i) = ∏ i : {x // x ∈ range n}, f i :
  ((equiv.fin_equiv_subtype n).trans
    (equiv.subtype_equiv_right (λ _, mem_range.symm))).prod_comp (f ∘ coe)
... = ∏ i in range n, f i : by rw [← attach_eq_univ, prod_attach]

@[to_additive]
lemma finset.prod_fin_eq_prod_range [comm_monoid β] {n : ℕ} (c : fin n → β) :
  ∏ i, c i = ∏ i in finset.range n, if h : i < n then c ⟨i, h⟩ else 1 :=
begin
  rw [← fin.prod_univ_eq_prod_range, finset.prod_congr rfl],
  rintros ⟨i, hi⟩ _,
  simp only [fin.coe_eq_val, hi, dif_pos]
end

@[to_additive]
lemma finset.prod_subtype {M : Type*} [comm_monoid M]
  {p : α → Prop} {F : fintype (subtype p)} (s : finset α) (h : ∀ x, x ∈ s ↔ p x) (f : α → M) :
  ∏ a in s, f a = ∏ a : subtype p, f a :=
have (∈ s) = p, from set.ext h,
begin
  rw [← prod_attach, attach_eq_univ],
  substI p,
  congr
end

@[to_additive]
lemma finset.prod_to_finset_eq_subtype {M : Type*} [comm_monoid M] [fintype α]
  (p : α → Prop) [decidable_pred p] (f : α → M) :
    ∏ a in {x | p x}.to_finset, f a = ∏ a : subtype p, f a :=
by { rw ← finset.prod_subtype, simp }

@[to_additive] lemma finset.prod_fiberwise [decidable_eq β] [fintype β] [comm_monoid γ]
  (s : finset α) (f : α → β) (g : α → γ) :
  ∏ b : β, ∏ a in s.filter (λ a, f a = b), g a = ∏ a in s, g a :=
finset.prod_fiberwise_of_maps_to (λ x _, mem_univ _) _

@[to_additive]
lemma fintype.prod_fiberwise [fintype α] [decidable_eq β] [fintype β] [comm_monoid γ]
  (f : α → β) (g : α → γ) :
  (∏ b : β, ∏ a : {a // f a = b}, g (a : α)) = ∏ a, g a :=
begin
  rw [← (equiv.sigma_preimage_equiv f).prod_comp, ← univ_sigma_univ, prod_sigma],
  refl
end

lemma fintype.prod_dite [fintype α] {p : α → Prop} [decidable_pred p]
  [comm_monoid β] (f : Π (a : α) (ha : p a), β) (g : Π (a : α) (ha : ¬p a), β) :
  (∏ a, dite (p a) (f a) (g a)) = (∏ a : {a // p a}, f a a.2) * (∏ a : {a // ¬p a}, g a a.2) :=
begin
  simp only [prod_dite, attach_eq_univ],
  congr' 1,
  { convert (equiv.subtype_equiv_right _).prod_comp (λ x : {x // p x}, f x x.2),
    simp },
  { convert (equiv.subtype_equiv_right _).prod_comp (λ x : {x // ¬p x}, g x x.2),
    simp }
end

section
open finset

variables {α₁ : Type*} {α₂ : Type*} {M : Type*} [fintype α₁] [fintype α₂] [comm_monoid M]

@[to_additive]
lemma fintype.prod_sum_elim (f : α₁ → M) (g : α₂ → M) :
  (∏ x, sum.elim f g x) = (∏ a₁, f a₁) * (∏ a₂, g a₂) :=
by { classical, rw [univ_sum_type, prod_sum_elim] }

@[to_additive]
lemma fintype.prod_sum_type (f : α₁ ⊕ α₂ → M) :
  (∏ x, f x) = (∏ a₁, f (sum.inl a₁)) * (∏ a₂, f (sum.inr a₂)) :=
by simp only [← fintype.prod_sum_elim, sum.elim_comp_inl_inr]

end

namespace list

lemma prod_take_of_fn [comm_monoid α] {n : ℕ} (f : fin n → α) (i : ℕ) :
  ((of_fn f).take i).prod = ∏ j in finset.univ.filter (λ (j : fin n), j.val < i), f j :=
begin
  have A : ∀ (j : fin n), ¬ ((j : ℕ) < 0) := λ j, not_lt_bot,
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
    have B : ∀ (j : fin n), ((j : ℕ) < i.succ) = ((j : ℕ) < i),
    { assume j,
      have : (j : ℕ) < i := lt_of_lt_of_le j.2 (not_lt.mp h),
      simp [this, lt_trans this (nat.lt_succ_self _)] },
    simp [← A, B, IH] }
end

-- `to_additive` does not work on `prod_take_of_fn` because of `0 : ℕ` in the proof.
-- Use `multiplicative` instead.
lemma sum_take_of_fn [add_comm_monoid α] {n : ℕ} (f : fin n → α) (i : ℕ) :
  ((of_fn f).take i).sum = ∑ j in finset.univ.filter (λ (j : fin n), j.val < i), f j :=
by simpa [list.to_add_prod, list.map_take] using
  congr_arg multiplicative.to_add (prod_take_of_fn (multiplicative.of_add ∘ f) i)

attribute [to_additive] prod_take_of_fn

@[to_additive]
lemma prod_of_fn [comm_monoid α] {n : ℕ} {f : fin n → α} :
  (of_fn f).prod = ∏ i, f i :=
begin
  convert prod_take_of_fn f n,
  { rw [take_all_of_le (le_of_eq (length_of_fn f))] },
  { have : ∀ (j : fin n), (j : ℕ) < n := λ j, j.is_lt,
    simp [this] }
end

lemma alternating_sum_eq_finset_sum {G : Type*} [add_comm_group G] :
  ∀ (L : list G), alternating_sum L = ∑ i : fin L.length, (-1 : ℤ) ^ (i : ℕ) •ℤ L.nth_le i i.is_lt
| [] := by { rw [alternating_sum, finset.sum_eq_zero], rintro ⟨i, ⟨⟩⟩ }
| (g :: []) :=
begin
  show g = ∑ i : fin 1, (-1 : ℤ) ^ (i : ℕ) •ℤ [g].nth_le i i.2,
  rw [fin.sum_univ_succ], simp,
end
| (g :: h :: L) :=
calc g + -h + L.alternating_sum
    = g + -h + ∑ i : fin L.length, (-1 : ℤ) ^ (i : ℕ) •ℤ L.nth_le i i.2 :
      congr_arg _ (alternating_sum_eq_finset_sum _)
... = ∑ i : fin (L.length + 2), (-1 : ℤ) ^ (i : ℕ) •ℤ list.nth_le (g :: h :: L) i _ :
begin
  rw [fin.sum_univ_succ, fin.sum_univ_succ, add_assoc],
  unfold_coes,
  simp [nat.succ_eq_add_one, pow_add],
  refl,
end

@[to_additive]
lemma alternating_prod_eq_finset_prod {G : Type*} [comm_group G] :
  ∀ (L : list G), alternating_prod L = ∏ i : fin L.length, (L.nth_le i i.2) ^ ((-1 : ℤ) ^ (i : ℕ))
| [] := by { rw [alternating_prod, finset.prod_eq_one], rintro ⟨i, ⟨⟩⟩ }
| (g :: []) :=
begin
  show g = ∏ i : fin 1, [g].nth_le i i.2 ^ (-1 : ℤ) ^ (i : ℕ),
  rw [fin.prod_univ_succ], simp,
end
| (g :: h :: L) :=
calc g * h⁻¹ * L.alternating_prod
    = g * h⁻¹ * ∏ i : fin L.length, L.nth_le i i.2 ^ (-1 : ℤ) ^ (i : ℕ) :
      congr_arg _ (alternating_prod_eq_finset_prod _)
... = ∏ i : fin (L.length + 2), list.nth_le (g :: h :: L) i _ ^ (-1 : ℤ) ^ (i : ℕ) :
begin
  rw [fin.prod_univ_succ, fin.prod_univ_succ, mul_assoc],
  unfold_coes,
  simp [nat.succ_eq_add_one, pow_add],
  refl,
end

end list
