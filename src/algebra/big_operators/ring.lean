/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import algebra.big_operators.basic

/-!
# Results about big operators with values in a (semi)ring

We prove results about big operators that involve some interaction between
multiplicative and additive structures on the values being combined.
-/

universes u v w

open_locale big_operators

variables {α : Type u} {β : Type v} {γ : Type w}

namespace finset
variables {s s₁ s₂ : finset α} {a : α} {b : β}  {f g : α → β}


section semiring
variables [semiring β]

lemma sum_mul : (∑ x in s, f x) * b = ∑ x in s, f x * b :=
(s.sum_hom (λ x, x * b)).symm

lemma mul_sum : b * (∑ x in s, f x) = ∑ x in s, b * f x :=
(s.sum_hom _).symm

lemma sum_mul_boole [decidable_eq α] (s : finset α) (f : α → β) (a : α) :
  (∑ x in s, (f x * ite (a = x) 1 0)) = ite (a ∈ s) (f a) 0 :=
by simp

lemma sum_boole_mul [decidable_eq α] (s : finset α) (f : α → β) (a : α) :
  (∑ x in s, (ite (a = x) 1 0) * f x) = ite (a ∈ s) (f a) 0 :=
by simp

end semiring

lemma sum_div [division_ring β] {s : finset α} {f : α → β} {b : β} :
  (∑ x in s, f x) / b = ∑ x in s, f x / b :=
by simp only [div_eq_mul_inv, sum_mul]

section comm_semiring
variables [comm_semiring β]

/-- The product over a sum can be written as a sum over the product of sets, `finset.pi`.
  `finset.prod_univ_sum` is an alternative statement when the product is over `univ`. -/
lemma prod_sum {δ : α → Type*} [decidable_eq α] [∀a, decidable_eq (δ a)]
  {s : finset α} {t : Πa, finset (δ a)} {f : Πa, δ a → β} :
  (∏ a in s, ∑ b in (t a), f a b) =
    ∑ p in (s.pi t), ∏ x in s.attach, f x.1 (p x.1 x.2) :=
begin
  induction s using finset.induction with a s ha ih,
  { rw [pi_empty, sum_singleton], refl },
  { have h₁ : ∀x ∈ t a, ∀y ∈ t a, ∀h : x ≠ y,
        disjoint (image (pi.cons s a x) (pi s t)) (image (pi.cons s a y) (pi s t)),
    { assume x hx y hy h,
      simp only [disjoint_iff_ne, mem_image],
      rintros _ ⟨p₂, hp, eq₂⟩ _ ⟨p₃, hp₃, eq₃⟩ eq,
      have : pi.cons s a x p₂ a (mem_insert_self _ _) = pi.cons s a y p₃ a (mem_insert_self _ _),
      { rw [eq₂, eq₃, eq] },
      rw [pi.cons_same, pi.cons_same] at this,
      exact h this },
    rw [prod_insert ha, pi_insert ha, ih, sum_mul, sum_bind h₁],
    refine sum_congr rfl (λ b _, _),
    have h₂ : ∀p₁∈pi s t, ∀p₂∈pi s t, pi.cons s a b p₁ = pi.cons s a b p₂ → p₁ = p₂, from
      assume p₁ h₁ p₂ h₂ eq, pi_cons_injective ha eq,
    rw [sum_image h₂, mul_sum],
    refine sum_congr rfl (λ g _, _),
    rw [attach_insert, prod_insert, prod_image],
    { simp only [pi.cons_same],
      congr' with ⟨v, hv⟩, congr',
      exact (pi.cons_ne (by rintro rfl; exact ha hv)).symm },
    { exact λ _ _ _ _, subtype.eq ∘ subtype.mk.inj },
    { simp only [mem_image], rintro ⟨⟨_, hm⟩, _, rfl⟩, exact ha hm } }
end

lemma sum_mul_sum {ι₁ : Type*} {ι₂ : Type*} (s₁ : finset ι₁) (s₂ : finset ι₂)
  (f₁ : ι₁ → β) (f₂ : ι₂ → β) :
  (∑ x₁ in s₁, f₁ x₁) * (∑ x₂ in s₂, f₂ x₂) = ∑ p in s₁.product s₂, f₁ p.1 * f₂ p.2 :=
by { rw [sum_product, sum_mul, sum_congr rfl], intros, rw mul_sum }

open_locale classical

/-- The product of `f a + g a` over all of `s` is the sum
  over the powerset of `s` of the product of `f` over a subset `t` times
  the product of `g` over the complement of `t`  -/
lemma prod_add (f g : α → β) (s : finset α) :
  ∏ a in s, (f a + g a) = ∑ t in s.powerset, ((∏ a in t, f a) * (∏ a in (s \ t), g a)) :=
calc ∏ a in s, (f a + g a)
    = ∏ a in s, ∑ p in ({true, false} : finset Prop), if p then f a else g a : by simp
... = ∑ p in (s.pi (λ _, {true, false}) : finset (Π a ∈ s, Prop)),
        ∏ a in s.attach, if p a.1 a.2 then f a.1 else g a.1 : prod_sum
... = ∑ t in s.powerset, (∏ a in t, f a) * (∏ a in (s \ t), g a) : begin
  refine eq.symm (sum_bij (λ t _ a _, a ∈ t) _ _ _ _),
  { simp [subset_iff]; tauto },
  { intros t ht,
    erw [prod_ite (λ a : {a // a ∈ s}, f a.1) (λ a : {a // a ∈ s}, g a.1)],
    refine congr_arg2 _
      (prod_bij (λ (a : α) (ha : a ∈ t), ⟨a, mem_powerset.1 ht ha⟩)
         _ _ _
        (λ b hb, ⟨b, by cases b; finish⟩))
      (prod_bij (λ (a : α) (ha : a ∈ s \ t), ⟨a, by simp * at *⟩)
        _ _ _
        (λ b hb, ⟨b, by cases b; finish⟩));
    intros; simp * at *; simp * at * },
  { finish [function.funext_iff, finset.ext_iff, subset_iff] },
  { assume f hf,
    exact ⟨s.filter (λ a : α, ∃ h : a ∈ s, f a h),
      by simp, by funext; intros; simp *⟩ }
end

/--  Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a `finset`
gives `(a + b)^s.card`.-/
lemma sum_pow_mul_eq_add_pow
  {α R : Type*} [comm_semiring R] (a b : R) (s : finset α) :
  (∑ t in s.powerset, a ^ t.card * b ^ (s.card - t.card)) = (a + b) ^ s.card :=
begin
  rw [← prod_const, prod_add],
  refine finset.sum_congr rfl (λ t ht, _),
  rw [prod_const, prod_const, ← card_sdiff (mem_powerset.1 ht)]
end

lemma prod_pow_eq_pow_sum {x : β} {f : α → ℕ} :
  ∀ {s : finset α}, (∏ i in s, x ^ (f i)) = x ^ (∑ x in s, f x) :=
begin
  apply finset.induction,
  { simp },
  { assume a s has H,
    rw [finset.prod_insert has, finset.sum_insert has, pow_add, H] }
end

theorem dvd_sum {b : β} {s : finset α} {f : α → β}
  (h : ∀ x ∈ s, b ∣ f x) : b ∣ ∑ x in s, f x :=
multiset.dvd_sum (λ y hy, by rcases multiset.mem_map.1 hy with ⟨x, hx, rfl⟩; exact h x hx)

@[norm_cast]
lemma prod_nat_cast (s : finset α) (f : α → ℕ) :
  ↑(∏ x in s, f x : ℕ) = (∏ x in s, (f x : β)) :=
(nat.cast_ring_hom β).map_prod f s

end comm_semiring

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive]
lemma prod_powerset_insert [decidable_eq α] [comm_monoid β] {s : finset α} {x : α} (h : x ∉ s)
  (f : finset α → β) :
  (∏ a in (insert x s).powerset, f a) =
    (∏ a in s.powerset, f a) * (∏ t in s.powerset, f (insert x t)) :=
begin
  rw [powerset_insert, finset.prod_union, finset.prod_image],
  { assume t₁ h₁ t₂ h₂ heq,
    rw [← finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₁ h),
        ← finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₂ h), heq] },
  { rw finset.disjoint_iff_ne,
    assume t₁ h₁ t₂ h₂,
    rcases finset.mem_image.1 h₂ with ⟨t₃, h₃, H₃₂⟩,
    rw ← H₃₂,
    exact ne_insert_of_not_mem _ _ (not_mem_of_mem_powerset_of_not_mem h₁ h) }
end

end finset
