/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import algebra.ring.pi
import algebra.big_operators.basic
/-!
# Big operators for Pi Types

This file contains theorems relevant to big operators in binary and arbitrary product
of monoids and groups
-/

open_locale big_operators

namespace pi

@[to_additive]
lemma list_prod_apply {α : Type*} {β : α → Type*} [Πa, monoid (β a)] (a : α) (l : list (Πa, β a)) :
  l.prod a = (l.map (λf:Πa, β a, f a)).prod :=
(monoid_hom.apply β a).map_list_prod _

@[to_additive]
lemma multiset_prod_apply {α : Type*} {β : α → Type*} [∀a, comm_monoid (β a)] (a : α)
  (s : multiset (Πa, β a)) : s.prod a = (s.map (λf:Πa, β a, f a)).prod :=
(monoid_hom.apply β a).map_multiset_prod _

end pi

@[simp, to_additive]
lemma finset.prod_apply {α : Type*} {β : α → Type*} {γ} [∀a, comm_monoid (β a)] (a : α)
  (s : finset γ) (g : γ → Πa, β a) : (∏ c in s, g c) a = ∏ c in s, g c a :=
(monoid_hom.apply β a).map_prod _ _

@[simp, to_additive]
lemma fintype.prod_apply {α : Type*} {β : α → Type*} {γ : Type*} [fintype γ]
  [∀a, comm_monoid (β a)] (a : α) (g : γ → Πa, β a) : (∏ c, g c) a = ∏ c, g c a :=
finset.prod_apply a finset.univ g

@[simp, to_additive]
lemma monoid_hom.finset_prod_apply {ι M N : Type*} [monoid M] [comm_monoid N] (f : ι → M →* N)
  (s : finset ι) (a : M) :
  (∏ i in s, f i) a = ∏ i in s, f i a :=
(monoid_hom.eval a).map_prod _ _

@[to_additive prod_mk_sum]
lemma prod_mk_prod {α β γ : Type*} [comm_monoid α] [comm_monoid β] (s : finset γ)
  (f : γ → α) (g : γ → β) : (∏ x in s, f x, ∏ x in s, g x) = ∏ x in s, (f x, g x) :=
by haveI := classical.dec_eq γ; exact
finset.induction_on s rfl (by simp [prod.ext_iff] {contextual := tt})

section single
variables {I : Type*} [decidable_eq I] {Z : I → Type*}
variables [Π i, add_comm_monoid (Z i)]

-- As we only defined `single` into `add_monoid`, we only prove the `finset.sum` version here.
lemma finset.univ_sum_single [fintype I] (f : Π i, Z i) :
  ∑ i, pi.single i (f i) = f :=
begin
  ext a,
  rw [finset.sum_apply, finset.sum_eq_single a],
  { simp, },
  { intros b _ h, simp [h.symm], },
  { intro h, exfalso, simpa using h, },
end

@[ext]
lemma add_monoid_hom.functions_ext [fintype I] (G : Type*)
  [add_comm_monoid G] (g h : (Π i, Z i) →+ G)
  (w : ∀ (i : I) (x : Z i), g (pi.single i x) = h (pi.single i x)) : g = h :=
begin
  ext k,
  rw [←finset.univ_sum_single k, add_monoid_hom.map_sum, add_monoid_hom.map_sum],
  apply finset.sum_congr rfl,
  intros,
  apply w,
end

end single

section ring_hom
open pi
variables {I : Type*} [decidable_eq I] {f : I → Type*}
variables [Π i, semiring (f i)]

-- we need `apply`+`convert` because Lean fails to unify different `add_monoid` instances
-- on `Π i, f i`
@[ext]
lemma ring_hom.functions_ext [fintype I] (G : Type*) [semiring G] (g h : (Π i, f i) →+* G)
  (w : ∀ (i : I) (x : f i), g (single i x) = h (single i x)) : g = h :=
begin
  apply ring_hom.coe_add_monoid_hom_injective,
  convert add_monoid_hom.functions_ext _ _ _ _; assumption
end

end ring_hom

namespace prod

variables {α β γ : Type*} [comm_monoid α] [comm_monoid β] {s : finset γ} {f : γ → α × β}

@[to_additive]
lemma fst_prod : (∏ c in s, f c).1 = ∏ c in s, (f c).1 :=
(monoid_hom.fst α β).map_prod f s

@[to_additive]
lemma snd_prod  : (∏ c in s, f c).2 = ∏ c in s, (f c).2 :=
(monoid_hom.snd α β).map_prod f s

end prod
