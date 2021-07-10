/-
Copyright (c) 2020 Kexing Ying and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Kevin Buzzard, Yury Kudryashov
-/

import data.set.finite
import data.set.disjointed
import algebra.big_operators
import algebra.indicator_function

/-!
# Finite products and sums over types and sets

We define products and sums over types and subsets of types, with no finiteness hypotheses.
All infinite products and sums are defined to be junk values (i.e. one or zero).
This approach is sometimes easier to use than `finset.sum`,
when issues arise with `finset` and `fintype` being data.

## Main definitions

We use the following variables:

* `α`, `β` - types with no structure;
* `s`, `t` - sets
* `M`, `N` - additive or multiplicative commutative monoids
* `f`, `g` - functions

Definitions in this file:

* `finsum f : M` : the sum of `f x` as `x` ranges over the support of `f`, if it's finite.
   Zero otherwise.

* `finprod f : M` : the product of `f x` as `x` ranges over the multiplicative support of `f`, if
   it's finite. One otherwise.

## Notation

* `∑ᶠ i, f i` and `∑ᶠ i : α, f i` for `finsum f`

* `∏ᶠ i, f i` and `∏ᶠ i : α, f i` for `finprod f`

This notation works for functions `f : p → M`, where `p : Prop`, so the following works:

* `∑ᶠ i ∈ s, f i`, where `f : α → M`, `s : set α` : sum over the set `s`;
* `∑ᶠ n < 5, f n`, where `f : ℕ → M` : same as `f 0 + f 1 + f 2 + f 3 + f 4`;
* `∏ᶠ (n >= -2) (hn : n < 3), f n`, where `f : ℤ → M` : same as `f (-2) * f (-1) * f 0 * f 1 * f 2`.

## Implementation notes

`finsum` and `finprod` is "yet another way of doing finite sums and products in Lean". However
experiments in the wild (e.g. with matroids) indicate that it is a helpful approach in settings
where the user is not interested in computability and wants to do reasoning without running into
typeclass diamonds caused by the constructive finiteness used in definitions such as `finset` and
`fintype`. By sticking solely to `set.finite` we avoid these problems. We are aware that there are
other solutions but for beginner mathematicians this approach is easier in practice.

Another application is the construction of a partition of unity from a collection of “bump”
function. In this case the finite set depends on the point and it's convenient to have a definition
that does not mention the set explicitly.

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

## Todo

We did not add `is_finite (X : Type) : Prop`, because it is simply `nonempty (fintype X)`.
There is work on `fincard` in the pipeline, which returns the cardinality of `X` if it
is finite, and 0 otherwise.

## Tags

finsum, finprod, finite sum, finite product
-/

open function set

/-!
### Definition and relation to `finset.sum` and `finset.prod`
-/

section sort
variables {M N : Type*} {α β ι : Sort*} [comm_monoid M] [comm_monoid N]

open_locale big_operators

section

/- Note: we use classical logic only for these definitions, to ensure that we do not write lemmas
with `classical.dec` in their statement. -/
open_locale classical

/-- Sum of `f x` as `x` ranges over the elements of the support of `f`, if it's finite. Zero
otherwise. -/
@[irreducible] noncomputable def finsum {M α} [add_comm_monoid M] (f : α → M) : M :=
if h : finite (support (f ∘ plift.down)) then ∑ i in h.to_finset, f i.down else 0

/-- Product of `f x` as `x` ranges over the elements of the multiplicative support of `f`, if it's
finite. One otherwise. -/
@[irreducible, to_additive]
noncomputable def finprod (f : α → M) : M :=
if h : finite (mul_support (f ∘ plift.down)) then ∏ i in h.to_finset, f i.down else 1

end

localized "notation `∑ᶠ` binders `, ` r:(scoped:67 f, finsum f) := r" in big_operators

localized "notation `∏ᶠ` binders `, ` r:(scoped:67 f, finprod f) := r" in big_operators

@[to_additive] lemma finprod_eq_prod_plift_of_mul_support_to_finset_subset
  {f : α → M} (hf : finite (mul_support (f ∘ plift.down))) {s : finset (plift α)}
  (hs : hf.to_finset ⊆ s) :
  ∏ᶠ i, f i = ∏ i in s, f i.down :=
begin
  rw [finprod, dif_pos],
  refine finset.prod_subset hs (λ x hx hxf, _),
  rwa [hf.mem_to_finset, nmem_mul_support] at hxf
end

@[to_additive] lemma finprod_eq_prod_plift_of_mul_support_subset
  {f : α → M} {s : finset (plift α)} (hs : mul_support (f ∘ plift.down) ⊆ s) :
  ∏ᶠ i, f i = ∏ i in s, f i.down :=
finprod_eq_prod_plift_of_mul_support_to_finset_subset
  (s.finite_to_set.subset hs) $ λ x hx, by { rw finite.mem_to_finset at hx, exact hs hx }

@[simp, to_additive] lemma finprod_one : ∏ᶠ i : α, (1 : M) = 1 :=
begin
  have : mul_support (λ x : plift α, (λ _, 1 : α → M) x.down) ⊆ (∅ : finset (plift α)),
    from λ x h, h rfl,
  rw [finprod_eq_prod_plift_of_mul_support_subset this, finset.prod_empty]
end

@[to_additive] lemma finprod_of_is_empty [is_empty α] (f : α → M) : ∏ᶠ i, f i = 1 :=
by { rw ← finprod_one, congr }

@[simp, to_additive] lemma finprod_false (f : false → M) : ∏ᶠ i, f i = 1 :=
finprod_of_is_empty _

@[to_additive] lemma finprod_eq_single (f : α → M) (a : α) (ha : ∀ x ≠ a, f x = 1) :
  ∏ᶠ x, f x = f a :=
begin
  have : mul_support (f ∘ plift.down) ⊆ ({plift.up a} : finset (plift α)),
  { intro x, contrapose,
    simpa [plift.eq_up_iff_down_eq] using ha x.down },
  rw [finprod_eq_prod_plift_of_mul_support_subset this, finset.prod_singleton],
end

@[to_additive] lemma finprod_unique [unique α] (f : α → M) : ∏ᶠ i, f i = f (default α) :=
finprod_eq_single f (default α) $ λ x hx, (hx $ unique.eq_default _).elim

@[simp, to_additive] lemma finprod_true (f : true → M) : ∏ᶠ i, f i = f trivial :=
@finprod_unique M true _ ⟨⟨trivial⟩, λ _, rfl⟩ f

@[to_additive] lemma finprod_eq_dif {p : Prop} [decidable p] (f : p → M) :
  ∏ᶠ i, f i = if h : p then f h else 1 :=
begin
  split_ifs,
  { haveI : unique p := ⟨⟨h⟩, λ _, rfl⟩, exact finprod_unique f },
  { haveI : is_empty p := ⟨h⟩, exact finprod_of_is_empty f }
end

@[to_additive] lemma finprod_eq_if {p : Prop} [decidable p] {x : M} :
  ∏ᶠ i : p, x = if p then x else 1 :=
finprod_eq_dif (λ _, x)

@[to_additive] lemma finprod_congr {f g : α → M} (h : ∀ x, f x = g x) :
  finprod f = finprod g :=
congr_arg _ $ funext h

@[congr, to_additive] lemma finprod_congr_Prop {p q : Prop} {f : p → M} {g : q → M} (hpq : p = q)
  (hfg : ∀ h : q, f (hpq.mpr h) = g h) :
  finprod f = finprod g :=
by { subst q, exact finprod_congr hfg }

attribute [congr] finsum_congr_Prop

/-- To prove a property of a finite product, it suffices to prove that the property is
multiplicative and holds on multipliers. -/
@[to_additive] lemma finprod_induction {f : α → M} (p : M → Prop) (hp₀ : p 1)
  (hp₁ : ∀ x y, p x → p y → p (x * y)) (hp₂ : ∀ i, p (f i)) :
  p (∏ᶠ i, f i) :=
begin
  rw finprod,
  split_ifs,
  exacts [finset.prod_induction _ _ hp₁ hp₀ (λ i hi, hp₂ _), hp₀]
end

/-- To prove a property of a finite sum, it suffices to prove that the property is
additive and holds on summands. -/
add_decl_doc finsum_induction

lemma finprod_nonneg {R : Type*} [ordered_comm_semiring R] {f : α → R} (hf : ∀ x, 0 ≤ f x) :
  0 ≤ ∏ᶠ x, f x :=
finprod_induction (λ x, 0 ≤ x) zero_le_one (λ x y, mul_nonneg) hf

@[to_additive finsum_nonneg]
lemma one_le_finprod' {M : Type*} [ordered_comm_monoid M] {f : α → M} (hf : ∀ i, 1 ≤ f i) :
  1 ≤ ∏ᶠ i, f i :=
finprod_induction _ le_rfl (λ _ _, one_le_mul) hf

@[to_additive] lemma monoid_hom.map_finprod_plift (f : M →* N) (g : α → M)
  (h : finite (mul_support $ g ∘ plift.down)) :
  f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) :=
begin
  rw [finprod_eq_prod_plift_of_mul_support_subset h.coe_to_finset.ge,
    finprod_eq_prod_plift_of_mul_support_subset, f.map_prod],
  rw [h.coe_to_finset],
  exact mul_support_comp_subset f.map_one (g ∘ plift.down)
end

@[to_additive] lemma monoid_hom.map_finprod_Prop {p : Prop} (f : M →* N) (g : p → M) :
  f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) :=
f.map_finprod_plift g (finite.of_fintype _)

end sort

section type

variables {α β ι M N : Type*} [comm_monoid M] [comm_monoid N]

open_locale big_operators

@[to_additive] lemma finprod_eq_mul_indicator_apply (s : set α)
  (f : α → M) (a : α) :
  ∏ᶠ (h : a ∈ s), f a = mul_indicator s f a :=
by convert finprod_eq_if

@[simp, to_additive] lemma finprod_mem_mul_support (f : α → M) (a : α) :
  ∏ᶠ (h : f a ≠ 1), f a = f a :=
by rw [← mem_mul_support, finprod_eq_mul_indicator_apply, mul_indicator_mul_support]

@[to_additive] lemma finprod_mem_def (s : set α) (f : α → M) :
  ∏ᶠ a ∈ s, f a = ∏ᶠ a, mul_indicator s f a :=
finprod_congr $ finprod_eq_mul_indicator_apply s f

@[to_additive] lemma finprod_eq_prod_of_mul_support_subset (f : α → M) {s : finset α}
  (h : mul_support f ⊆ s) :
  ∏ᶠ i, f i = ∏ i in s, f i :=
begin
  have A : mul_support (f ∘ plift.down) = equiv.plift.symm '' mul_support f,
  { rw mul_support_comp_eq_preimage,
    exact (equiv.plift.symm.image_eq_preimage _).symm },
  have : mul_support (f ∘ plift.down) ⊆ s.map equiv.plift.symm.to_embedding,
  { rw [A, finset.coe_map], exact image_subset _ h },
  rw [finprod_eq_prod_plift_of_mul_support_subset this],
  simp
end

@[to_additive] lemma finprod_eq_prod_of_mul_support_to_finset_subset (f : α → M)
  (hf : finite (mul_support f)) {s : finset α} (h : hf.to_finset ⊆ s) :
  ∏ᶠ i, f i = ∏ i in s, f i :=
finprod_eq_prod_of_mul_support_subset _ $ λ x hx, h $ hf.mem_to_finset.2 hx

@[to_additive] lemma finprod_def (f : α → M) [decidable (mul_support f).finite] :
  ∏ᶠ i : α, f i = if h : (mul_support f).finite then ∏ i in h.to_finset, f i else 1 :=
begin
  split_ifs,
  { exact finprod_eq_prod_of_mul_support_to_finset_subset _ h (finset.subset.refl _) },
  { rw [finprod, dif_neg],
    rw [mul_support_comp_eq_preimage],
    exact mt (λ hf, hf.of_preimage equiv.plift.surjective) h}
end

@[to_additive] lemma finprod_of_infinite_mul_support {f : α → M} (hf : (mul_support f).infinite) :
  ∏ᶠ i, f i = 1 :=
by { classical, rw [finprod_def, dif_neg hf] }

@[to_additive] lemma finprod_eq_prod (f : α → M) (hf : (mul_support f).finite) :
  ∏ᶠ i : α, f i = ∏ i in hf.to_finset, f i :=
by { classical, rw [finprod_def, dif_pos hf] }

@[to_additive] lemma finprod_eq_prod_of_fintype [fintype α] (f : α → M) :
  ∏ᶠ i : α, f i = ∏ i, f i :=
finprod_eq_prod_of_mul_support_to_finset_subset _ (finite.of_fintype _) $ finset.subset_univ _

@[to_additive] lemma finprod_cond_eq_prod_of_cond_iff (f : α → M) {p : α → Prop} {t : finset α}
  (h : ∀ {x}, f x ≠ 1 → (p x ↔ x ∈ t)) :
  ∏ᶠ i (hi : p i), f i = ∏ i in t, f i :=
begin
  set s := {x | p x},
  have : mul_support (s.mul_indicator f) ⊆ t,
  { rw [set.mul_support_mul_indicator], intros x hx, exact (h hx.2).1 hx.1 },
  erw [finprod_mem_def, finprod_eq_prod_of_mul_support_subset _ this],
  refine finset.prod_congr rfl (λ x hx, mul_indicator_apply_eq_self.2 $ λ hxs, _),
  contrapose! hxs,
  exact (h hxs).2 hx
end

@[to_additive] lemma finprod_mem_eq_prod_of_inter_mul_support_eq (f : α → M) {s : set α}
  {t : finset α} (h : s ∩ mul_support f = t ∩ mul_support f) :
  ∏ᶠ i ∈ s, f i = ∏ i in t, f i :=
finprod_cond_eq_prod_of_cond_iff _ $ by simpa [set.ext_iff] using h

@[to_additive] lemma finprod_mem_eq_prod_of_subset (f : α → M) {s : set α} {t : finset α}
  (h₁ : s ∩ mul_support f ⊆ t) (h₂ : ↑t ⊆ s) :
  ∏ᶠ i ∈ s, f i = ∏ i in t, f i :=
finprod_cond_eq_prod_of_cond_iff _ $ λ x hx, ⟨λ h, h₁ ⟨h, hx⟩, λ h, h₂ h⟩

@[to_additive] lemma finprod_mem_eq_prod (f : α → M) {s : set α}
  (hf : (s ∩ mul_support f).finite) :
  ∏ᶠ i ∈ s, f i = ∏ i in hf.to_finset, f i :=
finprod_mem_eq_prod_of_inter_mul_support_eq _ $ by simp [inter_assoc]

@[to_additive] lemma finprod_mem_eq_prod_filter (f : α → M) (s : set α) [decidable_pred (∈ s)]
  (hf : (mul_support f).finite) :
  ∏ᶠ i ∈ s, f i = ∏ i in finset.filter (∈ s) hf.to_finset, f i :=
finprod_mem_eq_prod_of_inter_mul_support_eq _ $ by simp [inter_comm, inter_left_comm]

@[to_additive] lemma finprod_mem_eq_to_finset_prod (f : α → M) (s : set α) [fintype s] :
  ∏ᶠ i ∈ s, f i = ∏ i in s.to_finset, f i :=
finprod_mem_eq_prod_of_inter_mul_support_eq _ $ by rw [coe_to_finset]

@[to_additive] lemma finprod_mem_eq_finite_to_finset_prod (f : α → M) {s : set α} (hs : s.finite) :
  ∏ᶠ i ∈ s, f i = ∏ i in hs.to_finset, f i :=
finprod_mem_eq_prod_of_inter_mul_support_eq _ $ by rw [hs.coe_to_finset]

@[to_additive] lemma finprod_mem_finset_eq_prod (f : α → M) (s : finset α) :
  ∏ᶠ i ∈ s, f i = ∏ i in s, f i :=
finprod_mem_eq_prod_of_inter_mul_support_eq _ rfl

@[to_additive] lemma finprod_mem_coe_finset (f : α → M) (s : finset α) :
  ∏ᶠ i ∈ (s : set α), f i = ∏ i in s, f i :=
finprod_mem_eq_prod_of_inter_mul_support_eq _ rfl

@[to_additive] lemma finprod_mem_eq_one_of_infinite {f : α → M} {s : set α}
  (hs : (s ∩ mul_support f).infinite) : ∏ᶠ i ∈ s, f i = 1 :=
begin
  rw finprod_mem_def,
  apply finprod_of_infinite_mul_support,
  rwa [← mul_support_mul_indicator] at hs
end

@[to_additive] lemma finprod_mem_inter_mul_support (f : α → M) (s : set α) :
  ∏ᶠ i ∈ (s ∩ mul_support f), f i = ∏ᶠ i ∈ s, f i :=
by rw [finprod_mem_def, finprod_mem_def, mul_indicator_inter_mul_support]

@[to_additive] lemma finprod_mem_inter_mul_support_eq (f : α → M) (s t : set α)
  (h : s ∩ mul_support f = t ∩ mul_support f) :
  ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, f i :=
by rw [← finprod_mem_inter_mul_support, h, finprod_mem_inter_mul_support]

@[to_additive] lemma finprod_mem_inter_mul_support_eq' (f : α → M) (s t : set α)
  (h : ∀ x ∈ mul_support f, x ∈ s ↔ x ∈ t) :
  ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, f i :=
begin
  apply finprod_mem_inter_mul_support_eq,
  ext x,
  exact and_congr_left (h x)
end

@[to_additive] lemma finprod_mem_univ (f : α → M) : ∏ᶠ i ∈ @set.univ α, f i = ∏ᶠ i : α, f i :=
finprod_congr $ λ i, finprod_true _

variables {f g : α → M} {a b : α} {s t : set α}

@[to_additive] lemma finprod_mem_congr (h₀ : s = t) (h₁ : ∀ x ∈ t, f x = g x) :
  ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, g i :=
h₀.symm ▸ (finprod_congr $ λ i, finprod_congr_Prop rfl (h₁ i))

/-!
### Distributivity w.r.t. addition, subtraction, and (scalar) multiplication
-/

/-- If the multiplicative supports of `f` and `g` are finite, then the product of `f i * g i` equals
the product of `f i` multiplied by the product over `g i`. -/
@[to_additive] lemma finprod_mul_distrib (hf : (mul_support f).finite)
  (hg : (mul_support g).finite) :
  ∏ᶠ i, (f i * g i) = (∏ᶠ i, f i) * ∏ᶠ i, g i :=
begin
  classical,
  rw [finprod_eq_prod_of_mul_support_to_finset_subset _ hf (finset.subset_union_left _ _),
    finprod_eq_prod_of_mul_support_to_finset_subset _ hg (finset.subset_union_right _ _),
    ← finset.prod_mul_distrib],
  refine finprod_eq_prod_of_mul_support_subset _ _,
  simp [mul_support_mul]
end

/-- A more general version of `finprod_mem_mul_distrib` that requires `s ∩ mul_support f` and
`s ∩ mul_support g` instead of `s` to be finite. -/
@[to_additive] lemma finprod_mem_mul_distrib' (hf : (s ∩ mul_support f).finite)
  (hg : (s ∩ mul_support g).finite) :
  ∏ᶠ i ∈ s, (f i * g i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ s, g i :=
begin
  rw [← mul_support_mul_indicator] at hf hg,
  simp only [finprod_mem_def, mul_indicator_mul, finprod_mul_distrib hf hg]
end

/-- The product of constant one over any set equals one. -/
@[to_additive] lemma finprod_mem_one (s : set α) : ∏ᶠ i ∈ s, (1 : M) = 1 := by simp

/-- If a function `f` equals one on a set `s`, then the product of `f i` over `i ∈ s` equals one. -/
@[to_additive] lemma finprod_mem_of_eq_on_one (hf : eq_on f 1 s) : ∏ᶠ i ∈ s, f i = 1 :=
by { rw ← finprod_mem_one s, exact finprod_mem_congr rfl hf }

/-- If the product of `f i` over `i ∈ s` is not equal to one, then there is some `x ∈ s`
such that `f x ≠ 1`. -/
@[to_additive] lemma exists_ne_one_of_finprod_mem_ne_one (h : ∏ᶠ i ∈ s, f i ≠ 1) :
  ∃ x ∈ s, f x ≠ 1 :=
begin
  by_contra h', push_neg at h',
  exact h (finprod_mem_of_eq_on_one h')
end

/-- Given a finite set `s`, the product of `f i * g i` over `i ∈ s` equals the product of `f i`
over `i ∈ s` times the product of `g i` over `i ∈ s`. -/
@[to_additive] lemma finprod_mem_mul_distrib (hs : s.finite) :
  ∏ᶠ i ∈ s, (f i * g i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ s, g i :=
finprod_mem_mul_distrib' (hs.inter_of_left _) (hs.inter_of_left _)

@[to_additive] lemma monoid_hom.map_finprod {f : α → M} (g : M →* N) (hf : (mul_support f).finite) :
  g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
g.map_finprod_plift f $ hf.preimage $ equiv.plift.injective.inj_on _

/-- A more general version of `monoid_hom.map_finprod_mem` that requires `s ∩ mul_support f` and
  instead of `s` to be finite. -/
@[to_additive] lemma monoid_hom.map_finprod_mem' {f : α → M} (g : M →* N)
  (h₀ : (s ∩ mul_support f).finite) :
  g (∏ᶠ j ∈ s, f j) = ∏ᶠ i ∈ s, (g (f i)) :=
begin
  rw [g.map_finprod],
  { simp only [g.map_finprod_Prop] },
  { simpa only [finprod_eq_mul_indicator_apply, mul_support_mul_indicator] }
end

/-- Given a monoid homomorphism `g : M →* N`, and a function `f : α → M`, the value of `g` at the
product of `f i` over `i ∈ s` equals the product of `(g ∘ f) i` over `s`. -/
@[to_additive] lemma monoid_hom.map_finprod_mem (f : α → M) (g : M →* N) (hs : s.finite) :
  g (∏ᶠ j ∈ s, f j) = ∏ᶠ i ∈ s, g (f i) :=
g.map_finprod_mem' (hs.inter_of_left _)

/-!
### `∏ᶠ x ∈ s, f x` and set operations
-/

/-- The product of any function over an empty set is one. -/
@[to_additive] lemma finprod_mem_empty : ∏ᶠ i ∈ (∅ : set α), f i = 1 := by simp

/-- A set `s` is not empty if the product of some function over `s` is not equal to one. -/
@[to_additive] lemma nonempty_of_finprod_mem_ne_one (h : ∏ᶠ i ∈ s, f i ≠ 1) : s.nonempty :=
ne_empty_iff_nonempty.1 $ λ h', h $ h'.symm ▸ finprod_mem_empty

/-- Given finite sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` times the product of
`f i` over `i ∈ s ∩ t` equals the product of `f i` over `i ∈ s` times the product of `f i`
over `i ∈ t`. -/
@[to_additive] lemma finprod_mem_union_inter (hs : s.finite) (ht : t.finite) :
  (∏ᶠ i ∈ s ∪ t, f i) * ∏ᶠ i ∈ s ∩ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
begin
  unfreezingI { lift s to finset α using hs, lift t to finset α using ht },
  classical,
  rw [← finset.coe_union, ← finset.coe_inter],
  simp only [finprod_mem_coe_finset, finset.prod_union_inter]
end

/-- A more general version of `finprod_mem_union_inter` that requires `s ∩ mul_support f` and
`t ∩ mul_support f` instead of `s` and `t` to be finite. -/
@[to_additive] lemma finprod_mem_union_inter'
  (hs : (s ∩ mul_support f).finite) (ht : (t ∩ mul_support f).finite) :
  (∏ᶠ i ∈ s ∪ t, f i) * ∏ᶠ i ∈ s ∩ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
begin
  rw [← finprod_mem_inter_mul_support f s, ← finprod_mem_inter_mul_support f t,
    ← finprod_mem_union_inter hs ht, ← union_inter_distrib_right, finprod_mem_inter_mul_support,
    ← finprod_mem_inter_mul_support f (s ∩ t)],
  congr' 2,
  rw [inter_left_comm, inter_assoc, inter_assoc, inter_self, inter_left_comm]
end

/-- A more general version of `finprod_mem_union` that requires `s ∩ mul_support f` and
`t ∩ mul_support f` instead of `s` and `t` to be finite. -/
@[to_additive] lemma finprod_mem_union' (hst : disjoint s t) (hs : (s ∩ mul_support f).finite)
  (ht : (t ∩ mul_support f).finite) :
  ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
by rw [← finprod_mem_union_inter' hs ht, disjoint_iff_inter_eq_empty.1 hst, finprod_mem_empty,
  mul_one]

/-- Given two finite disjoint sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` equals the
product of `f i` over `i ∈ s` times the product of `f i` over `i ∈ t`. -/
@[to_additive] lemma finprod_mem_union (hst : disjoint s t) (hs : s.finite) (ht : t.finite) :
  ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
finprod_mem_union' hst (hs.inter_of_left _) (ht.inter_of_left _)

/-- A more general version of `finprod_mem_union'` that requires `s ∩ mul_support f` and
`t ∩ mul_support f` instead of `s` and `t` to be disjoint -/
@[to_additive] lemma finprod_mem_union'' (hst : disjoint (s ∩ mul_support f) (t ∩ mul_support f))
  (hs : (s ∩ mul_support f).finite) (ht : (t ∩ mul_support f).finite) :
  ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
by rw [← finprod_mem_inter_mul_support f s, ← finprod_mem_inter_mul_support f t,
  ← finprod_mem_union hst hs ht, ← union_inter_distrib_right, finprod_mem_inter_mul_support]

/-- The product of `f i` over `i ∈ {a}` equals `f a`. -/
@[to_additive] lemma finprod_mem_singleton : ∏ᶠ i ∈ ({a} : set α), f i = f a :=
by rw [← finset.coe_singleton, finprod_mem_coe_finset, finset.prod_singleton]

@[simp, to_additive] lemma finprod_cond_eq_left : ∏ᶠ i = a, f i = f a :=
finprod_mem_singleton

@[simp, to_additive] lemma finprod_cond_eq_right : ∏ᶠ i (hi : a = i), f i = f a :=
by simp [@eq_comm _ a]

/-- A more general version of `finprod_mem_insert` that requires `s ∩ mul_support f` instead of
`s` to be finite. -/
@[to_additive] lemma finprod_mem_insert' (f : α → M) (h : a ∉ s)
  (hs : (s ∩ mul_support f).finite) :
  ∏ᶠ i ∈ insert a s, f i = f a * ∏ᶠ i ∈ s, f i :=
begin
  rw [insert_eq, finprod_mem_union' _ _ hs, finprod_mem_singleton],
  { rwa disjoint_singleton_left },
  { exact (finite_singleton a).inter_of_left _ }
end

/-- Given a finite set `s` and an element `a ∉ s`, the product of `f i` over `i ∈ insert a s` equals
`f a` times the product of `f i` over `i ∈ s`. -/
@[to_additive] lemma finprod_mem_insert (f : α → M) (h : a ∉ s) (hs : s.finite) :
  ∏ᶠ i ∈ insert a s, f i = f a * ∏ᶠ i ∈ s, f i :=
finprod_mem_insert' f h $ hs.inter_of_left _

/-- If `f a = 1` for all `a ∉ s`, then the product of `f i` over `i ∈ insert a s` equals the
product of `f i` over `i ∈ s`. -/
@[to_additive] lemma finprod_mem_insert_of_eq_one_if_not_mem (h : a ∉ s → f a = 1) :
  ∏ᶠ i ∈ (insert a s), f i = ∏ᶠ i ∈ s, f i :=
begin
  refine finprod_mem_inter_mul_support_eq' _ _ _ (λ x hx, ⟨_, or.inr⟩),
  rintro (rfl|hxs),
  exacts [not_imp_comm.1 h hx, hxs]
end

/-- If `f a = 1`, then the product of `f i` over `i ∈ insert a s` equals the product of `f i` over
`i ∈ s`. -/
@[to_additive] lemma finprod_mem_insert_one (h : f a = 1) :
  ∏ᶠ i ∈ (insert a s), f i = ∏ᶠ i ∈ s, f i :=
finprod_mem_insert_of_eq_one_if_not_mem (λ _, h)

/-- The product of `f i` over `i ∈ {a, b}`, `a ≠ b`, is equal to `f a * f b`. -/
@[to_additive] lemma finprod_mem_pair (h : a ≠ b) : ∏ᶠ i ∈ ({a, b} : set α), f i = f a * f b :=
by { rw [finprod_mem_insert, finprod_mem_singleton], exacts [h, finite_singleton b] }

/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s`
provided that `g` is injective on `s ∩ mul_support (f ∘ g)`. -/
@[to_additive] lemma finprod_mem_image' {s : set β} {g : β → α}
  (hg : set.inj_on g (s ∩ mul_support (f ∘ g))) :
  ∏ᶠ i ∈ (g '' s), f i = ∏ᶠ j ∈ s, f (g j) :=
begin
  classical,
  by_cases hs : finite (s ∩ mul_support (f ∘ g)),
  { have hg : ∀ (x ∈ hs.to_finset) (y ∈ hs.to_finset), g x = g y → x = y,
      by simpa only [hs.mem_to_finset],
    rw [finprod_mem_eq_prod _ hs, ← finset.prod_image hg],
    refine finprod_mem_eq_prod_of_inter_mul_support_eq f _,
    rw [finset.coe_image, hs.coe_to_finset, ← image_inter_mul_support_eq, inter_assoc,
      inter_self] },
  { rw [finprod_mem_eq_one_of_infinite hs, finprod_mem_eq_one_of_infinite],
    rwa [image_inter_mul_support_eq, infinite_image_iff hg] }
end

/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s`
provided that `g` is injective on `s`. -/
@[to_additive] lemma finprod_mem_image {β} {s : set β} {g : β → α} (hg : set.inj_on g s) :
  ∏ᶠ i ∈ (g '' s), f i = ∏ᶠ j ∈ s, f (g j) :=
finprod_mem_image' $ hg.mono $ inter_subset_left _ _

/-- The product of `f y` over `y ∈ set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective on `mul_support (f ∘ g)`. -/
@[to_additive] lemma finprod_mem_range' {g : β → α} (hg : set.inj_on g (mul_support (f ∘ g))) :
  ∏ᶠ i ∈ range g, f i = ∏ᶠ j, f (g j) :=
begin
  rw [← image_univ, finprod_mem_image', finprod_mem_univ],
  rwa univ_inter
end

/-- The product of `f y` over `y ∈ set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective. -/
@[to_additive] lemma finprod_mem_range {g : β → α} (hg : injective g) :
  ∏ᶠ i ∈ range g, f i = ∏ᶠ j, f (g j) :=
finprod_mem_range' (hg.inj_on _)

/-- The product of `f i` over `s : set α` is equal to the product of `g j` over `t : set β`
if there exists a function `e : α → β` such that `e` is bijective from `s` to `t` and for all
`x` in `s` we have `f x = g (e x)`. -/
@[to_additive] lemma finprod_mem_eq_of_bij_on {s : set α} {t : set β} {f : α → M} {g : β → M}
  (e : α → β) (he₀ : set.bij_on e s t) (he₁ : ∀ x ∈ s, f x = g (e x)) :
  ∏ᶠ i ∈ s, f i = ∏ᶠ j ∈ t, g j :=
begin
  rw [← set.bij_on.image_eq he₀, finprod_mem_image he₀.2.1],
  exact finprod_mem_congr rfl he₁
end

@[to_additive] lemma finprod_set_coe_eq_finprod_mem (s : set α) : ∏ᶠ j : s, f j = ∏ᶠ i ∈ s, f i :=
begin
  rw [← finprod_mem_range, subtype.range_coe],
  exact subtype.coe_injective
end

@[to_additive] lemma finprod_subtype_eq_finprod_cond (p : α → Prop) :
  ∏ᶠ j : subtype p, f j = ∏ᶠ i (hi : p i), f i :=
finprod_set_coe_eq_finprod_mem {i | p i}

@[to_additive] lemma finprod_mem_inter_mul_diff' (t : set α) (h : (s ∩ mul_support f).finite) :
  (∏ᶠ i ∈ s ∩ t, f i) * ∏ᶠ i ∈ s \ t, f i = ∏ᶠ i ∈ s, f i :=
begin
  rw [← finprod_mem_union', inter_union_diff],
  exacts [λ x hx, hx.2.2 hx.1.2, h.subset (λ x hx, ⟨hx.1.1, hx.2⟩),
    h.subset (λ x hx, ⟨hx.1.1, hx.2⟩)],
end

@[to_additive] lemma finprod_mem_inter_mul_diff (t : set α) (h : s.finite) :
  (∏ᶠ i ∈ s ∩ t, f i) * ∏ᶠ i ∈ s \ t, f i = ∏ᶠ i ∈ s, f i :=
finprod_mem_inter_mul_diff' _ $ h.inter_of_left _

/-- A more general version of `finprod_mem_mul_diff` that requires `t ∩ mul_support f` instead of
  `t` to be finite. -/
@[to_additive] lemma finprod_mem_mul_diff' (hst : s ⊆ t) (ht : (t ∩ mul_support f).finite) :
  (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t \ s, f i = ∏ᶠ i ∈ t, f i :=
by rw [← finprod_mem_inter_mul_diff' _ ht, inter_eq_self_of_subset_right hst]

/-- Given a finite set `t` and a subset `s` of `t`, the product of `f i` over `i ∈ s`
times the product of `f i` over `t \ s` equals the product of `f i` over `i ∈ t`. -/
@[to_additive] lemma finprod_mem_mul_diff (hst : s ⊆ t) (ht : t.finite) :
  (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t \ s, f i = ∏ᶠ i ∈ t, f i :=
finprod_mem_mul_diff' hst (ht.inter_of_left _)

/-- Given a family of pairwise disjoint finite sets `t i` indexed by a finite type,
the product of `f a` over the union `⋃ i, t i` is equal to the product over all indexes `i`
of the products of `f a` over `a ∈ t i`. -/
@[to_additive] lemma finprod_mem_Union [fintype ι] {t : ι → set α}
  (h : pairwise (disjoint on t)) (ht : ∀ i, (t i).finite) :
  ∏ᶠ a ∈ (⋃ i : ι, t i), f a = ∏ᶠ i, (∏ᶠ a ∈ t i, f a) :=
begin
  unfreezingI { lift t to ι → finset α using ht },
  classical,
  rw [← bUnion_univ, ← finset.coe_univ, ← finset.coe_bUnion,
    finprod_mem_coe_finset, finset.prod_bUnion],
  { simp only [finprod_mem_coe_finset, finprod_eq_prod_of_fintype] },
  { exact λ x _ y _ hxy, finset.disjoint_iff_disjoint_coe.2 (h x y hxy) }
end

/-- Given a family of sets `t : ι → set α`, a finite set `I` in the index type such that all
sets `t i`, `i ∈ I`, are finite, if all `t i`, `i ∈ I`, are pairwise disjoint, then
the product of `f a` over `a ∈ ⋃ i ∈ I, t i` is equal to the product over `i ∈ I`
of the products of `f a` over `a ∈ t i`. -/
@[to_additive] lemma finprod_mem_bUnion {I : set ι} {t : ι → set α}
  (h : pairwise_on I (disjoint on t)) (hI : I.finite) (ht : ∀ i ∈ I, (t i).finite) :
  ∏ᶠ a ∈ ⋃ x ∈ I, t x, f a = ∏ᶠ i ∈ I, ∏ᶠ j ∈ t i, f j :=
begin
  haveI := hI.fintype,
  rw [← Union_subtype, finprod_mem_Union, ← finprod_set_coe_eq_finprod_mem],
  exacts [λ x y hxy, h x x.2 y y.2 (subtype.coe_injective.ne hxy), λ b, ht b b.2]
end

/-- If `t` is a finite set of pairwise disjoint finite sets, then the product of `f a`
over `a ∈ ⋃₀ t` is the product over `s ∈ t` of the products of `f a` over `a ∈ s`. -/
@[to_additive] lemma finprod_mem_sUnion {t : set (set α)} (h : pairwise_on t disjoint)
  (ht₀ : t.finite) (ht₁ : ∀ x ∈ t, set.finite x):
  ∏ᶠ a ∈ ⋃₀ t, f a = ∏ᶠ s ∈ t, ∏ᶠ a ∈ s, f a :=
by rw [set.sUnion_eq_bUnion, finprod_mem_bUnion h ht₀ ht₁]

/-- If `s : set α` and `t : set β` are finite sets, then the product over `s` commutes
with the product over `t`. -/
@[to_additive] lemma finprod_mem_comm {s : set α} {t : set β}
  (f : α → β → M) (hs : s.finite) (ht : t.finite) :
  ∏ᶠ i ∈ s, ∏ᶠ j ∈ t, f i j = ∏ᶠ j ∈ t, ∏ᶠ i ∈ s, f i j :=
begin
  unfreezingI { lift s to finset α using hs, lift t to finset β using ht },
  simp only [finprod_mem_coe_finset],
  exact finset.prod_comm
end

/-- To prove a property of a finite product, it suffices to prove that the property is
multiplicative and holds on multipliers. -/
@[to_additive] lemma finprod_mem_induction (p : M → Prop) (hp₀ : p 1)
  (hp₁ : ∀ x y, p x → p y → p (x * y)) (hp₂ : ∀ x ∈ s, p $ f x) :
  p (∏ᶠ i ∈ s, f i) :=
finprod_induction _ hp₀ hp₁ $ λ x, finprod_induction _ hp₀ hp₁ $ hp₂ x

lemma finprod_cond_nonneg {R : Type*} [ordered_comm_semiring R] {p : α → Prop} {f : α → R}
  (hf : ∀ x, p x → 0 ≤ f x) :
  0 ≤ ∏ᶠ x (h : p x), f x :=
finprod_nonneg $ λ x, finprod_nonneg $ hf x

@[to_additive]
lemma single_le_finprod {M : Type*} [ordered_comm_monoid M] (i : α) {f : α → M}
  (hf : finite (mul_support f)) (h : ∀ j, 1 ≤ f j) :
  f i ≤ ∏ᶠ j, f j :=
by classical;
calc f i ≤ ∏ j in insert i hf.to_finset, f j :
  finset.single_le_prod' (λ j hj, h j) (finset.mem_insert_self _ _)
     ... = ∏ᶠ j, f j                :
  (finprod_eq_prod_of_mul_support_to_finset_subset _ hf (finset.subset_insert _ _)).symm

lemma finprod_eq_zero {M₀ : Type*} [comm_monoid_with_zero M₀] (f : α → M₀) (x : α)
  (hx : f x = 0) (hf : finite (mul_support f)) :
  ∏ᶠ x, f x = 0 :=
begin
  nontriviality,
  rw [finprod_eq_prod f hf],
  refine finset.prod_eq_zero (hf.mem_to_finset.2 _) hx,
  simp [hx]
end

@[to_additive] lemma finprod_prod_comm (s : finset β) (f : α → β → M)
  (h : ∀ b ∈ s, (mul_support (λ a, f a b)).finite) :
  ∏ᶠ a : α, ∏ b in s, f a b = ∏ b in s, ∏ᶠ a : α, f a b :=
begin
  have hU : mul_support (λ a, ∏ b in s, f a b) ⊆
    (s.finite_to_set.bUnion (λ b hb, h b (finset.mem_coe.1 hb))).to_finset,
  { rw finite.coe_to_finset,
    intros x hx,
    simp only [exists_prop, mem_Union, ne.def, mem_mul_support, finset.mem_coe],
    contrapose! hx,
    rw [mem_mul_support, not_not, finset.prod_congr rfl hx, finset.prod_const_one] },
  rw [finprod_eq_prod_of_mul_support_subset _ hU, finset.prod_comm],
  refine finset.prod_congr rfl (λ b hb, (finprod_eq_prod_of_mul_support_subset _ _).symm),
  intros a ha,
  simp only [finite.coe_to_finset, mem_Union],
  exact ⟨b, hb, ha⟩
end

@[to_additive] lemma prod_finprod_comm (s : finset α) (f : α → β → M)
  (h : ∀ a ∈ s, (mul_support (f a)).finite) :
  ∏ a in s, ∏ᶠ b : β, f a b = ∏ᶠ b : β, ∏ a in s, f a b :=
(finprod_prod_comm s (λ b a, f a b) h).symm

lemma mul_finsum {R : Type*} [semiring R] (f : α → R) (r : R)
  (h : (function.support f).finite) :
  r * ∑ᶠ a : α, f a = ∑ᶠ a : α, r * f a :=
(add_monoid_hom.mul_left r).map_finsum h

lemma finsum_mul {R : Type*} [semiring R] (f : α → R) (r : R)
  (h : (function.support f).finite) :
  (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r :=
(add_monoid_hom.mul_right r).map_finsum h

@[to_additive] lemma finset.mul_support_of_fiberwise_prod_subset_image [decidable_eq β]
  (s : finset α) (f : α → M) (g : α → β) :
  mul_support (λ b, (s.filter (λ a, g a = b)).prod f) ⊆ s.image g :=
begin
  simp only [finset.coe_image, set.mem_image, finset.mem_coe, function.support_subset_iff],
  intros b h,
  suffices : (s.filter (λ (a : α), g a = b)).nonempty,
  { simpa only [s.fiber_nonempty_iff_mem_image g b, finset.mem_image, exists_prop], },
  exact finset.nonempty_of_prod_ne_one h,
end

/-- Note that `b ∈ (s.filter (λ ab, prod.fst ab = a)).image prod.snd` iff `(a, b) ∈ s` so we can
simplify the right hand side of this lemma. However the form stated here is more useful for
iterating this lemma, e.g., if we have `f : α × β × γ → M`. -/
@[to_additive] lemma finprod_mem_finset_product' [decidable_eq α] [decidable_eq β]
  (s : finset (α × β)) (f : α × β → M) :
  ∏ᶠ ab (h : ab ∈ s), f ab =
  ∏ᶠ a b (h : b ∈ (s.filter (λ ab, prod.fst ab = a)).image prod.snd), f (a, b) :=
begin
  have : ∀ a, ∏ (i : β) in (s.filter (λ ab, prod.fst ab = a)).image prod.snd, f (a, i) =
    (finset.filter (λ ab, prod.fst ab = a) s).prod f,
  { intros a, apply finset.prod_bij (λ b _, (a, b)); finish, },
  rw finprod_mem_finset_eq_prod,
  simp_rw [finprod_mem_finset_eq_prod, this],
  rw [finprod_eq_prod_of_mul_support_subset _
    (s.mul_support_of_fiberwise_prod_subset_image f prod.fst),
    ← finset.prod_fiberwise_of_maps_to _ f],
  finish,
end

/-- See also `finprod_mem_finset_product'`. -/
@[to_additive] lemma finprod_mem_finset_product (s : finset (α × β)) (f : α × β → M) :
  ∏ᶠ ab (h : ab ∈ s), f ab = ∏ᶠ a b (h : (a, b) ∈ s), f (a, b) :=
by { classical, rw finprod_mem_finset_product', simp, }

@[to_additive] lemma finprod_mem_finset_product₃ {γ : Type*}
  (s : finset (α × β × γ)) (f : α × β × γ → M) :
  ∏ᶠ abc (h : abc ∈ s), f abc = ∏ᶠ a b c (h : (a, b, c) ∈ s), f (a, b, c) :=
by { classical, rw finprod_mem_finset_product', simp_rw finprod_mem_finset_product', simp, }

@[to_additive] lemma finprod_curry (f : α × β → M) (hf : (mul_support f).finite) :
  ∏ᶠ ab, f ab = ∏ᶠ a b, f (a, b) :=
begin
  have h₁ : ∀ a, ∏ᶠ (h : a ∈ hf.to_finset), f a = f a, { simp, },
  have h₂ : ∏ᶠ a, f a = ∏ᶠ a (h : a ∈ hf.to_finset), f a, { simp, },
  simp_rw [h₂, finprod_mem_finset_product, h₁],
end

@[to_additive] lemma finprod_curry₃ {γ : Type*} (f : α × β × γ → M) (h : (mul_support f).finite) :
  ∏ᶠ abc, f abc = ∏ᶠ a b c, f (a, b, c) :=
by { rw finprod_curry f h, congr, ext a, rw finprod_curry, simp [h], }

@[to_additive]
lemma finprod_dmem {s : set α} [decidable_pred (∈ s)] (f : (Π (a : α), a ∈ s → M)) :
  ∏ᶠ (a : α) (h : a ∈ s), f a h = ∏ᶠ (a : α) (h : a ∈ s), if h' : a ∈ s then f a h' else 1 :=
finprod_congr (λ a, finprod_congr (λ ha, (dif_pos ha).symm))

@[to_additive]
lemma finprod_emb_domain' {f : α → β} (hf : function.injective f)
  [decidable_pred (∈ set.range f)] (g : α → M) :
  ∏ᶠ (b : β), (if h : b ∈ set.range f then g (classical.some h) else 1) = ∏ᶠ (a : α), g a :=
begin
  simp_rw [← finprod_eq_dif],
  rw [finprod_dmem, finprod_mem_range hf, finprod_congr (λ a, _)],
  rw [dif_pos (set.mem_range_self a), hf (classical.some_spec (set.mem_range_self a))]
end

@[to_additive]
lemma finprod_emb_domain (f : α ↪ β) [decidable_pred (∈ set.range f)] (g : α → M) :
  ∏ᶠ (b : β), (if h : b ∈ set.range f then g (classical.some h) else 1) = ∏ᶠ (a : α), g a :=
finprod_emb_domain' f.injective g

end type
