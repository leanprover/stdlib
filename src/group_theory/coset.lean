/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison
-/

import group_theory.subgroup

/-!
# Cosets

This file develops the basic theory of left and right cosets.

## Main definitions

* `left_coset a s`: the left coset `a * s` for an element `a : α` and a subset `s ⊆ α`, for an
  `add_group` this is `left_add_coset a s`.
* `right_coset s a`: the right coset `s * a` for an element `a : α` and a subset `s ⊆ α`, for an
  `add_group` this is `right_add_coset s a`.
* `quotient_group.quotient s`: the quotient type representing the left cosets with respect to a
  subgroup `s`, for an `add_group` this is `quotient_add_group.quotient s`.
* `quotient_group.mk`: the canonical map from `α` to `α/s` for a subgroup `s` of `α`, for an
  `add_group` this is `quotient_add_group.mk`.
* `subgroup.left_coset_equiv_subgroup`: the natural bijection between a left coset and the subgroup,
  for an `add_group` this is `add_subgroup.left_coset_equiv_add_subgroup`.

## Notation

* `a *l s`: for `left_coset a s`.
* `a +l s`: for `left_add_coset a s`.
* `s *r a`: for `right_coset s a`.
* `s +r a`: for `right_add_coset s a`.

## TODO

Add `to_additive` to `preimage_mk_equiv_subgroup_times_set`.
-/

open set function

variable {α : Type*}

/-- The left coset `a * s` for an element `a : α` and a subset `s : set α` -/
@[to_additive left_add_coset "The left coset `a+s` for an element `a : α`
and a subset `s : set α`"]
def left_coset [has_mul α] (a : α) (s : set α) : set α := (λ x, a * x) '' s

/-- The right coset `s * a` for an element `a : α` and a subset `s : set α` -/
@[to_additive right_add_coset "The right coset `s+a` for an element `a : α`
and a subset `s : set α`"]
def right_coset [has_mul α] (s : set α) (a : α) : set α := (λ x, x * a) '' s

localized "infix ` *l `:70 := left_coset" in coset
localized "infix ` +l `:70 := left_add_coset" in coset
localized "infix ` *r `:70 := right_coset" in coset
localized "infix ` +r `:70 := right_add_coset" in coset

section coset_mul
variable [has_mul α]

@[to_additive mem_left_add_coset]
lemma mem_left_coset {s : set α} {x : α} (a : α) (hxS : x ∈ s) : a * x ∈ a *l s :=
mem_image_of_mem (λ b : α, a * b) hxS

@[to_additive mem_right_add_coset]
lemma mem_right_coset {s : set α} {x : α} (a : α) (hxS : x ∈ s) : x * a ∈ s *r a :=
mem_image_of_mem (λ b : α, b * a) hxS

/-- Equality of two left cosets `a * s` and `b * s`. -/
@[to_additive left_add_coset_equivalence "Equality of two left cosets `a + s` and `b + s`."]
def left_coset_equivalence (s : set α) (a b : α) := a *l s = b *l s

@[to_additive left_add_coset_equivalence_rel]
lemma left_coset_equivalence_rel (s : set α) : equivalence (left_coset_equivalence s) :=
mk_equivalence (left_coset_equivalence s) (λ a, rfl) (λ a b, eq.symm) (λ a b c, eq.trans)

/-- Equality of two right cosets `s * a` and `s * b`. -/
@[to_additive right_add_coset_equivalence "Equality of two right cosets `s + a` and `s + b`."]
def right_coset_equivalence (s : set α) (a b : α) := s *r a = s *r b

@[to_additive right_add_coset_equivalence_rel]
lemma right_coset_equivalence_rel (s : set α) : equivalence (right_coset_equivalence s) :=
mk_equivalence (right_coset_equivalence s) (λ a, rfl) (λ a b, eq.symm) (λ a b c, eq.trans)

end coset_mul

section coset_semigroup
variable [semigroup α]

@[simp] lemma left_coset_assoc (s : set α) (a b : α) : a *l (b *l s) = (a * b) *l s :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]
attribute [to_additive left_add_coset_assoc] left_coset_assoc

@[simp] lemma right_coset_assoc (s : set α) (a b : α) : s *r a *r b = s *r (a * b) :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]
attribute [to_additive right_add_coset_assoc] right_coset_assoc

@[to_additive left_add_coset_right_add_coset]
lemma left_coset_right_coset (s : set α) (a b : α) : a *l s *r b = a *l (s *r b) :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]

end coset_semigroup

section coset_monoid
variables [monoid α] (s : set α)

@[simp] lemma one_left_coset : 1 *l s = s :=
set.ext $ by simp [left_coset]
attribute [to_additive zero_left_add_coset] one_left_coset

@[simp] lemma right_coset_one : s *r 1 = s :=
set.ext $ by simp [right_coset]
attribute [to_additive right_add_coset_zero] right_coset_one

end coset_monoid

section coset_submonoid
open submonoid
variables [monoid α] (s : submonoid α)

@[to_additive mem_own_left_add_coset]
lemma mem_own_left_coset (a : α) : a ∈ a *l s :=
suffices a * 1 ∈ a *l s, by simpa,
mem_left_coset a (one_mem s)

@[to_additive mem_own_right_add_coset]
lemma mem_own_right_coset (a : α) : a ∈ (s : set α) *r a :=
suffices 1 * a ∈ (s : set α) *r a, by simpa,
mem_right_coset a (one_mem s)

@[to_additive mem_left_add_coset_left_add_coset]
lemma mem_left_coset_left_coset {a : α} (ha : a *l s = s) : a ∈ s :=
by rw [←set_like.mem_coe, ←ha]; exact mem_own_left_coset s a

@[to_additive mem_right_add_coset_right_add_coset]
lemma mem_right_coset_right_coset {a : α} (ha : (s : set α) *r a = s) : a ∈ s :=
by rw [←set_like.mem_coe, ←ha]; exact mem_own_right_coset s a

end coset_submonoid

section coset_group
variables [group α] {s : set α} {x : α}

@[to_additive mem_left_add_coset_iff]
lemma mem_left_coset_iff (a : α) : x ∈ a *l s ↔ a⁻¹ * x ∈ s :=
iff.intro
  (assume ⟨b, hb, eq⟩, by simp [eq.symm, hb])
  (assume h, ⟨a⁻¹ * x, h, by simp⟩)

@[to_additive mem_right_add_coset_iff]
lemma mem_right_coset_iff (a : α) : x ∈ s *r a ↔ x * a⁻¹ ∈ s :=
iff.intro
  (assume ⟨b, hb, eq⟩, by simp [eq.symm, hb])
  (assume h, ⟨x * a⁻¹, h, by simp⟩)

end coset_group

section coset_subgroup
open subgroup

variables [group α] (s : subgroup α)

@[to_additive left_add_coset_mem_left_add_coset]
lemma left_coset_mem_left_coset {a : α} (ha : a ∈ s) : a *l s = s :=
set.ext $ by simp [mem_left_coset_iff, mul_mem_cancel_left s (s.inv_mem ha)]

@[to_additive right_add_coset_mem_right_add_coset]
lemma right_coset_mem_right_coset {a : α} (ha : a ∈ s) : (s : set α) *r a = s :=
set.ext $ assume b, by simp [mem_right_coset_iff, mul_mem_cancel_right s (s.inv_mem ha)]

@[to_additive eq_add_cosets_of_normal]
theorem eq_cosets_of_normal (N : s.normal) (g : α) : g *l s = s *r g :=
set.ext $ assume a, by simp [mem_left_coset_iff, mem_right_coset_iff]; rw [N.mem_comm_iff]

@[to_additive normal_of_eq_add_cosets]
theorem normal_of_eq_cosets (h : ∀ g : α, g *l s = s *r g) : s.normal :=
⟨assume a ha g, show g * a * g⁻¹ ∈ (s : set α),
  by rw [← mem_right_coset_iff, ← h]; exact mem_left_coset g ha⟩

@[to_additive normal_iff_eq_add_cosets]
theorem normal_iff_eq_cosets : s.normal ↔ ∀ g : α, g *l s = s *r g :=
⟨@eq_cosets_of_normal _ _ s, normal_of_eq_cosets s⟩

end coset_subgroup

run_cmd to_additive.map_namespace `quotient_group `quotient_add_group

namespace quotient_group

/-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup.-/
@[to_additive "The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup."]
def left_rel [group α] (s : subgroup α) : setoid α :=
⟨λ x y, x⁻¹ * y ∈ s,
  assume x, by simp [s.one_mem],
  assume x y hxy,
    have (x⁻¹ * y)⁻¹ ∈ s, from s.inv_mem hxy,
    by simpa using this,
  assume x y z hxy hyz,
    have x⁻¹ * y * (y⁻¹ * z) ∈ s, from s.mul_mem hxy hyz,
    by simpa [mul_assoc] using this⟩

@[to_additive]
instance left_rel_decidable [group α] (s : subgroup α) [d : decidable_pred (∈ s)] :
  decidable_rel (left_rel s).r := λ _ _, d _

/-- `quotient s` is the quotient type representing the left cosets of `s`.
  If `s` is a normal subgroup, `quotient s` is a group -/
def quotient [group α] (s : subgroup α) : Type* := quotient (left_rel s)

/-- The equivalence relation corresponding to the partition of a group by right cosets of a
subgroup. -/
@[to_additive "The equivalence relation corresponding to the partition of a group by right cosets of
a subgroup."]
def right_rel [group α] (s : subgroup α) : setoid α :=
⟨λ x y, y * x⁻¹ ∈ s,
  assume x, by simp [s.one_mem],
  assume x y hxy,
    have (y * x⁻¹)⁻¹ ∈ s, from s.inv_mem hxy,
    by simpa using this,
  assume x y z hxy hyz,
    have (z * y⁻¹) * (y * x⁻¹) ∈ s, from s.mul_mem hyz hxy,
    by simpa [mul_assoc] using this⟩

@[to_additive]
instance right_rel_decidable [group α] (s : subgroup α) [d : decidable_pred (∈ s)] :
  decidable_rel (left_rel s).r := λ _ _, d _

end quotient_group

namespace quotient_add_group

/-- `quotient s` is the quotient type representing the left cosets of `s`.
  If `s` is a normal subgroup, `quotient s` is a group -/
def quotient [add_group α] (s : add_subgroup α) : Type* := quotient (left_rel s)

end quotient_add_group

attribute [to_additive quotient_add_group.quotient] quotient_group.quotient

namespace quotient_group

variables [group α] {s : subgroup α}

@[to_additive]
instance fintype [fintype α] (s : subgroup α) [decidable_rel (left_rel s).r] :
  fintype (quotient_group.quotient s) :=
quotient.fintype (left_rel s)

/-- The canonical map from a group `α` to the quotient `α/s`. -/
@[to_additive "The canonical map from an `add_group` `α` to the quotient `α/s`."]
abbreviation mk (a : α) : quotient s :=
quotient.mk' a

@[elab_as_eliminator, to_additive]
lemma induction_on {C : quotient s → Prop} (x : quotient s)
  (H : ∀ z, C (quotient_group.mk z)) : C x :=
quotient.induction_on' x H

@[to_additive]
instance : has_coe_t α (quotient s) := ⟨mk⟩ -- note [use has_coe_t]

@[elab_as_eliminator, to_additive]
lemma induction_on' {C : quotient s → Prop} (x : quotient s)
  (H : ∀ z : α, C z) : C x :=
quotient.induction_on' x H

@[to_additive]
instance (s : subgroup α) : inhabited (quotient s) :=
⟨((1 : α) : quotient s)⟩

@[to_additive quotient_add_group.eq]
protected lemma eq {a b : α} : (a : quotient s) = b ↔ a⁻¹ * b ∈ s :=
quotient.eq'

@[to_additive]
lemma eq_class_eq_left_coset (s : subgroup α) (g : α) :
  {x : α | (x : quotient s) = g} = left_coset g s :=
set.ext $ λ z, by { rw [mem_left_coset_iff, set.mem_set_of_eq, eq_comm, quotient_group.eq], simp }

@[to_additive]
lemma preimage_image_coe (N : subgroup α) (s : set α) :
  coe ⁻¹' ((coe : α → quotient N) '' s) = ⋃ x : N, (λ y : α, y * x) ⁻¹' s :=
begin
  ext x,
  simp only [quotient_group.eq, set_like.exists, exists_prop, set.mem_preimage, set.mem_Union,
    set.mem_image, subgroup.coe_mk, ← eq_inv_mul_iff_mul_eq],
  exact ⟨λ ⟨y, hs, hN⟩, ⟨_, N.inv_mem hN, by simpa using hs⟩,
         λ ⟨z, hz, hxz⟩, ⟨x*z, hxz, by simpa using hz⟩⟩,
end

end quotient_group

namespace subgroup
open quotient_group
variables [group α] {s : subgroup α}

/-- The natural bijection between a left coset `g * s` and `s`. -/
@[to_additive "The natural bijection between the cosets `g + s` and `s`."]
def left_coset_equiv_subgroup (g : α) : left_coset g s ≃ s :=
⟨λ x, ⟨g⁻¹ * x.1, (mem_left_coset_iff _).1 x.2⟩,
 λ x, ⟨g * x.1, x.1, x.2, rfl⟩,
 λ ⟨x, hx⟩, subtype.eq $ by simp,
 λ ⟨g, hg⟩, subtype.eq $ by simp⟩

/-- The natural bijection between a right coset `s * g` and `s`. -/
@[to_additive "The natural bijection between the cosets `s + g` and `s`."]
def right_coset_equiv_subgroup (g : α) : right_coset ↑s g ≃ s :=
⟨λ x, ⟨x.1 * g⁻¹, (mem_right_coset_iff _).1 x.2⟩,
 λ x, ⟨x.1 * g, x.1, x.2, rfl⟩,
 λ ⟨x, hx⟩, subtype.eq $ by simp,
 λ ⟨g, hg⟩, subtype.eq $ by simp⟩

/-- A (non-canonical) bijection between a group `α` and the product `(α/s) × s` -/
@[to_additive "A (non-canonical) bijection between an add_group `α` and the product `(α/s) × s`"]
noncomputable def group_equiv_quotient_times_subgroup :
  α ≃ quotient s × s :=
calc α ≃ Σ L : quotient s, {x : α // (x : quotient s) = L} :
  (equiv.sigma_preimage_equiv quotient_group.mk).symm
    ... ≃ Σ L : quotient s, left_coset (quotient.out' L) s :
  equiv.sigma_congr_right (λ L,
    begin
      rw ← eq_class_eq_left_coset,
      show _root_.subtype (λ x : α, quotient.mk' x = L) ≃
        _root_.subtype (λ x : α, quotient.mk' x = quotient.mk' _),
      simp [-quotient.eq'],
    end)
    ... ≃ Σ L : quotient s, s :
  equiv.sigma_congr_right (λ L, left_coset_equiv_subgroup _)
    ... ≃ quotient s × s :
  equiv.sigma_equiv_prod _ _

lemma card_eq_card_quotient_mul_card_subgroup [fintype α] (s : subgroup α) [fintype s]
  [decidable_pred (λ a, a ∈ s)] : fintype.card α = fintype.card (quotient s) * fintype.card s :=
by rw ← fintype.card_prod;
  exact fintype.card_congr (subgroup.group_equiv_quotient_times_subgroup)

/-- **Order of a Subgroup** -/
lemma card_subgroup_dvd_card [fintype α] (s : subgroup α) [fintype s] :
  fintype.card s ∣ fintype.card α :=
by haveI := classical.prop_decidable; simp [card_eq_card_quotient_mul_card_subgroup s]

lemma card_quotient_dvd_card [fintype α] (s : subgroup α) [decidable_pred (λ a, a ∈ s)]
  [fintype s] : fintype.card (quotient s) ∣ fintype.card α :=
by simp [card_eq_card_quotient_mul_card_subgroup s]

end subgroup

namespace quotient_group

variables [group α]

-- FIXME -- why is there no `to_additive`?

/-- If `s` is a subgroup of the group `α`, and `t` is a subset of `α/s`, then
there is a (typically non-canonical) bijection between the preimage of `t` in
`α` and the product `s × t`. -/
noncomputable def preimage_mk_equiv_subgroup_times_set
  (s : subgroup α) (t : set (quotient s)) : quotient_group.mk ⁻¹' t ≃ s × t :=
have h : ∀ {x : quotient s} {a : α}, x ∈ t → a ∈ s →
  (quotient.mk' (quotient.out' x * a) : quotient s) = quotient.mk' (quotient.out' x) :=
    λ x a hx ha, quotient.sound' (show (quotient.out' x * a)⁻¹ * quotient.out' x ∈ s,
      from (s.inv_mem_iff).1 $
        by rwa [mul_inv_rev, inv_inv, ← mul_assoc, inv_mul_self, one_mul]),
{ to_fun := λ ⟨a, ha⟩, ⟨⟨(quotient.out' (quotient.mk' a))⁻¹ * a,
    @quotient.exact' _ (left_rel s) _ _ $ (quotient.out_eq' _)⟩,
      ⟨quotient.mk' a, ha⟩⟩,
  inv_fun := λ ⟨⟨a, ha⟩, ⟨x, hx⟩⟩, ⟨quotient.out' x * a, show quotient.mk' _ ∈ t,
    by simp [h hx ha, hx]⟩,
  left_inv := λ ⟨a, ha⟩, subtype.eq $ show _ * _ = a, by simp,
  right_inv := λ ⟨⟨a, ha⟩, ⟨x, hx⟩⟩, show (_, _) = _, by simp [h hx ha] }

end quotient_group

/--
We use the class `has_coe_t` instead of `has_coe` if the first argument is a variable,
or if the second argument is a variable not occurring in the first.
Using `has_coe` would cause looping of type-class inference. See
<https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/remove.20all.20instances.20with.20variable.20domain>
-/
library_note "use has_coe_t"
