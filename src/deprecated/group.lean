/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.group.type_tags
import algebra.group.units_hom
import algebra.ring.basic
import data.equiv.mul_add

/-!
# Unbundled monoid and group homomorphisms

This file defines predicates for unbundled monoid and group homomorphisms. Though
bundled morphisms are preferred in mathlib, these unbundled predicates are still occasionally used
in mathlib, and probably will not go away before Lean 4
because Lean 3 often fails to coerce a bundled homomorphism to a function.

## Main Definitions

`is_monoid_hom` (deprecated), `is_group_hom` (deprecated)

## Tags

is_group_hom, is_monoid_hom

-/

universes u v
variables {α : Type u} {β : Type v}

/-- Predicate for maps which preserve an addition. -/
structure is_add_hom {α β : Type*} [has_add α] [has_add β] (f : α → β) : Prop :=
(map_add [] : ∀ x y, f (x + y) = f x + f y)

/-- Predicate for maps which preserve a multiplication. -/
@[to_additive]
structure is_mul_hom {α β : Type*} [has_mul α] [has_mul β] (f : α → β) : Prop :=
(map_mul [] : ∀ x y, f (x * y) = f x * f y)

namespace is_mul_hom
variables [has_mul α] [has_mul β] {γ : Type*} [has_mul γ]

/-- The identity map preserves multiplication. -/
@[to_additive "The identity map preserves addition"]
lemma id : is_mul_hom (id : α → α) := {map_mul := λ _ _, rfl}

/-- The composition of maps which preserve multiplication, also preserves multiplication. -/
@[to_additive "The composition of addition preserving maps also preserves addition"]
lemma comp {f : α → β} {g : β → γ} (hf : is_mul_hom f) (hg : is_mul_hom g) : is_mul_hom (g ∘ f) :=
{ map_mul := λ x y, by simp only [function.comp, hf.map_mul, hg.map_mul] }

/-- A product of maps which preserve multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive]
lemma mul {α β} [semigroup α] [comm_semigroup β]
  {f g : α → β} (hf : is_mul_hom f) (hg : is_mul_hom g) :
  is_mul_hom (λ a, f a * g a) :=
{ map_mul := λ a b, by simp only [hf.map_mul, hg.map_mul, mul_comm, mul_assoc, mul_left_comm] }

/-- The inverse of a map which preserves multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive]
lemma inv {α β} [has_mul α] [comm_group β] {f : α → β} (hf : is_mul_hom f) :
  is_mul_hom (λ a, (f a)⁻¹) :=
{ map_mul := λ a b, (hf.map_mul a b).symm ▸ mul_inv _ _ }

end is_mul_hom

/-- Predicate for add_monoid homomorphisms (deprecated -- use the bundled `monoid_hom` version). -/
structure is_add_monoid_hom [add_zero_class α] [add_zero_class β] (f : α → β)
  extends is_add_hom f : Prop :=
(map_zero [] : f 0 = 0)

/-- Predicate for monoid homomorphisms (deprecated -- use the bundled `monoid_hom` version). -/
@[to_additive]
structure is_monoid_hom [mul_one_class α] [mul_one_class β] (f : α → β)
  extends is_mul_hom f : Prop :=
(map_one [] : f 1 = 1)

namespace monoid_hom

variables {M : Type*} {N : Type*} [mM : mul_one_class M] [mN : mul_one_class N]

include mM mN
/-- Interpret a map `f : M → N` as a homomorphism `M →* N`. -/
@[to_additive "Interpret a map `f : M → N` as a homomorphism `M →+ N`."]
def of {f : M → N} (h : is_monoid_hom f) : M →* N :=
{ to_fun := f,
  map_one' := h.2,
  map_mul' := h.1.1 }

variables {mM mN}
@[simp, to_additive]
lemma coe_of {f : M → N} (hf : is_monoid_hom f) : ⇑ (monoid_hom.of hf) = f :=
rfl

@[to_additive]
lemma is_monoid_hom_coe (f : M →* N) : is_monoid_hom (f : M → N) :=
{ map_mul := f.map_mul,
  map_one := f.map_one }

end monoid_hom

namespace mul_equiv

variables {M : Type*} {N : Type*} [mul_one_class M] [mul_one_class N]

/-- A multiplicative isomorphism preserves multiplication (deprecated). -/
@[to_additive]
theorem is_mul_hom (h : M ≃* N) : is_mul_hom h := ⟨h.map_mul⟩

/-- A multiplicative bijection between two monoids is a monoid hom
  (deprecated -- use `mul_equiv.to_monoid_hom`). -/
@[to_additive]
lemma is_monoid_hom (h : M ≃* N) : is_monoid_hom h :=
{ map_mul := h.map_mul,
  map_one := h.map_one }

end mul_equiv

namespace is_monoid_hom
variables [mul_one_class α] [mul_one_class β] {f : α → β} (hf : is_monoid_hom f)

/-- A monoid homomorphism preserves multiplication. -/
@[to_additive]
lemma map_mul (x y) : f (x * y) = f x * f y :=
hf.map_mul x y

/-- The inverse of a map which preserves multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive]
lemma inv {α β} [mul_one_class α] [comm_group β] {f : α → β} (hf : is_monoid_hom f) :
  is_monoid_hom (λ a, (f a)⁻¹) :=
{ map_one := hf.map_one.symm ▸ one_inv,
  map_mul := λ a b, (hf.map_mul a b).symm ▸ mul_inv _ _ }

-- do we ever need this? It's a pain to prove here because we have no `int.induction_on` yet
--@[to_additive]
--lemma gpow (z : ℤ) [comm_group β] : is_monoid_hom (gpow z : β → β) := sorry

end is_monoid_hom

--TODO -- delete this and replace with is_mul_hom.is_monoid_hom
/-- A map to a group preserving multiplication is a monoid homomorphism. -/
@[to_additive]
theorem is_monoid_hom.of_mul [mul_one_class α] [group β] {f : α → β} (hf : is_mul_hom f) :
  is_monoid_hom f :=
{ map_one := mul_right_eq_self.1 $ by rw [← hf.map_mul, one_mul],
  map_mul := hf.map_mul }

@[to_additive]
theorem is_mul_hom.to_is_monoid_hom [mul_one_class α] [group β] {f : α → β} (hf : is_mul_hom f) :
  is_monoid_hom f :=
{ map_one := mul_right_eq_self.1 $ by rw [← hf.map_mul, one_mul],
  map_mul := hf.map_mul }

namespace is_monoid_hom
variables [mul_one_class α] [mul_one_class β] {f : α → β}

/-- The identity map is a monoid homomorphism. -/
@[to_additive]
lemma id : is_monoid_hom (@id α) := { map_one := rfl, map_mul := λ _ _, rfl }

/-- The composite of two monoid homomorphisms is a monoid homomorphism. -/
@[to_additive]
lemma comp (hf : is_monoid_hom f) {γ} [mul_one_class γ] {g : β → γ} (hg : is_monoid_hom g) :
  is_monoid_hom (g ∘ f) :=
{ map_one := show g _ = 1, by rw [hf.map_one, hg.map_one],
  ..is_mul_hom.comp hf.to_is_mul_hom hg.to_is_mul_hom }

end is_monoid_hom

namespace is_add_monoid_hom

/-- Left multiplication in a ring is an additive monoid morphism. -/
lemma is_add_monoid_hom_mul_left {γ : Type*} [non_unital_non_assoc_semiring γ] (x : γ) :
  is_add_monoid_hom (λ y : γ, x * y) :=
{ map_zero := mul_zero x, map_add := λ y z, mul_add x y z }

/-- Right multiplication in a ring is an additive monoid morphism. -/
lemma is_add_monoid_hom_mul_right {γ : Type*} [non_unital_non_assoc_semiring γ] (x : γ) :
  is_add_monoid_hom (λ y : γ, y * x) :=
{ map_zero := zero_mul x, map_add := λ y z, add_mul y z x }

end is_add_monoid_hom

/-- Predicate for additive group homomorphism (deprecated -- use bundled `monoid_hom`). -/
structure is_add_group_hom [add_group α] [add_group β] (f : α → β) extends is_add_hom f : Prop

/-- Predicate for group homomorphisms (deprecated -- use bundled `monoid_hom`). -/
@[to_additive]
structure is_group_hom [group α] [group β] (f : α → β) extends is_mul_hom f : Prop

@[to_additive]
lemma monoid_hom.is_group_hom {G H : Type*} {_ : group G} {_ : group H} (f : G →* H) :
  is_group_hom (f : G → H) :=
{ map_mul := f.map_mul }

@[to_additive]
lemma mul_equiv.is_group_hom {G H : Type*} {_ : group G} {_ : group H} (h : G ≃* H) :
  is_group_hom h := { map_mul := h.map_mul }

/-- Construct `is_group_hom` from its only hypothesis. -/
@[to_additive]
lemma is_group_hom.mk' [group α] [group β] {f : α → β} (hf : ∀ x y, f (x * y) = f x * f y) :
  is_group_hom f :=
{ map_mul := hf }

namespace is_group_hom
variables [group α] [group β] {f : α → β} (hf : is_group_hom f)
open is_mul_hom (map_mul)

lemma map_mul : ∀ (x y), f (x * y) = f x * f y := hf.to_is_mul_hom.map_mul

/-- A group homomorphism is a monoid homomorphism. -/
@[to_additive]
lemma to_is_monoid_hom : is_monoid_hom f :=
hf.to_is_mul_hom.to_is_monoid_hom

/-- A group homomorphism sends 1 to 1. -/
@[to_additive]
lemma map_one : f 1 = 1 := hf.to_is_monoid_hom.map_one

/-- A group homomorphism sends inverses to inverses. -/
@[to_additive]
theorem map_inv (hf : is_group_hom f) (a : α) : f a⁻¹ = (f a)⁻¹ :=
eq_inv_of_mul_eq_one $ by rw [← hf.map_mul, inv_mul_self, hf.map_one]

/-- The identity is a group homomorphism. -/
@[to_additive]
lemma id : is_group_hom (@id α) := { map_mul := λ _ _, rfl}

/-- The composition of two group homomorphisms is a group homomorphism. -/
@[to_additive]
lemma comp (hf : is_group_hom f) {γ} [group γ] {g : β → γ} (hg : is_group_hom g) :
  is_group_hom (g ∘ f) :=
{ ..is_mul_hom.comp hf.to_is_mul_hom hg.to_is_mul_hom }

/-- A group homomorphism is injective iff its kernel is trivial. -/
@[to_additive]
lemma injective_iff {f : α → β} (hf : is_group_hom f) :
  function.injective f ↔ (∀ a, f a = 1 → a = 1) :=
⟨λ h _, by rw ← hf.map_one; exact @h _ _,
  λ h x y hxy, by rw [← inv_inv (f x), inv_eq_iff_mul_eq_one, ← hf.map_inv,
      ← hf.map_mul] at hxy;
    simpa using inv_eq_of_mul_eq_one (h _ hxy)⟩

/-- The product of group homomorphisms is a group homomorphism if the target is commutative. -/
@[to_additive]
lemma mul {α β} [group α] [comm_group β]
  {f g : α → β} (hf : is_group_hom f) (hg : is_group_hom g) :
  is_group_hom (λa, f a * g a) :=
{ map_mul := (hf.to_is_mul_hom.mul hg.to_is_mul_hom).map_mul }

/-- The inverse of a group homomorphism is a group homomorphism if the target is commutative. -/
@[to_additive]
lemma inv {α β} [group α] [comm_group β] {f : α → β} (hf : is_group_hom f) :
  is_group_hom (λa, (f a)⁻¹) :=
{ map_mul := hf.to_is_mul_hom.inv.map_mul }

end is_group_hom

namespace ring_hom
/-!
These instances look redundant, because `deprecated.ring` provides `is_ring_hom` for a `→+*`.
Nevertheless these are harmless, and helpful for stripping out dependencies on `deprecated.ring`.
-/
variables {R : Type*} {S : Type*}

section
variables [non_assoc_semiring R] [non_assoc_semiring S]

lemma to_is_monoid_hom (f : R →+* S) : is_monoid_hom f :=
{ map_one := f.map_one,
  map_mul := f.map_mul }

lemma to_is_add_monoid_hom (f : R →+* S) : is_add_monoid_hom f :=
{ map_zero := f.map_zero,
  map_add := f.map_add }
end

section
variables [ring R] [ring S]

lemma to_is_add_group_hom (f : R →+* S) : is_add_group_hom f :=
{ map_add := f.map_add }
end

end ring_hom

-- TODO `is_group_hom.inv` is a better name for this so delete this
/-- Inversion is a group homomorphism if the group is commutative. -/
@[to_additive neg.is_add_group_hom
"Negation is an `add_group` homomorphism if the `add_group` is commutative."]
lemma inv.is_group_hom [comm_group α] : is_group_hom (has_inv.inv : α → α) :=
{ map_mul := mul_inv }

namespace is_add_group_hom
variables [add_group α] [add_group β] {f : α → β} (hf : is_add_group_hom f)

/-- Additive group homomorphisms commute with subtraction. -/
lemma map_sub (a b) : f (a - b) = f a - f b :=
calc f (a - b) = f (a + -b)   : congr_arg f (sub_eq_add_neg a b)
           ... = f a + f (-b) : hf.map_add _ _
           ... = f a + -f b   : by rw [hf.map_neg]
           ... = f a - f b    : (sub_eq_add_neg _ _).symm

end is_add_group_hom

/-- The difference of two additive group homomorphisms is an additive group
homomorphism if the target is commutative. -/
lemma is_add_group_hom.sub {α β} [add_group α] [add_comm_group β]
  {f g : α → β} (hf : is_add_group_hom f) (hg : is_add_group_hom g) :
  is_add_group_hom (λa, f a - g a) :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

namespace units

variables {M : Type*} {N : Type*} [monoid M] [monoid N]

/-- The group homomorphism on units induced by a multiplicative morphism. -/
@[reducible] def map' {f : M → N} (hf : is_monoid_hom f) : units M →* units N :=
  map (monoid_hom.of hf)

@[simp] lemma coe_map' {f : M → N} (hf : is_monoid_hom f) (x : units M) :
  ↑((map' hf : units M → units N) x) = f x :=
rfl

lemma coe_is_monoid_hom : is_monoid_hom (coe : units M → M) := (coe_hom M).is_monoid_hom_coe

end units

namespace is_unit

variables {M : Type*} {N : Type*} [monoid M] [monoid N] {x : M}

lemma map' {f : M → N} (hf :is_monoid_hom f) {x : M} (h : is_unit x) :
  is_unit (f x) :=
h.map (monoid_hom.of hf)

end is_unit

lemma additive.is_add_hom [has_mul α] [has_mul β] {f : α → β} (hf : is_mul_hom f) :
  @is_add_hom (additive α) (additive β) _ _ f :=
{ map_add := is_mul_hom.map_mul hf }

lemma multiplicative.is_mul_hom [has_add α] [has_add β] {f : α → β} (hf : is_add_hom f) :
  @is_mul_hom (multiplicative α) (multiplicative β) _ _ f :=
{ map_mul := is_add_hom.map_add hf }

-- defeq abuse
lemma additive.is_add_monoid_hom [mul_one_class α] [mul_one_class β] {f : α → β}
  (hf : is_monoid_hom f) : @is_add_monoid_hom (additive α) (additive β) _ _ f :=
{ map_zero := @is_monoid_hom.map_one α β _ _ f hf,
  ..additive.is_add_hom hf.to_is_mul_hom }

lemma multiplicative.is_monoid_hom
  [add_zero_class α] [add_zero_class β] {f : α → β} (hf : is_add_monoid_hom f) :
  @is_monoid_hom (multiplicative α) (multiplicative β) _ _ f :=
{ map_one := is_add_monoid_hom.map_zero hf,
  ..multiplicative.is_mul_hom hf.to_is_add_hom }

lemma additive.is_add_group_hom [group α] [group β] {f : α → β} (hf : is_group_hom f) :
  @is_add_group_hom (additive α) (additive β) _ _ f :=
{ map_add := hf.to_is_mul_hom.map_mul }

lemma multiplicative.is_group_hom [add_group α] [add_group β] {f : α → β}
  (hf : is_add_group_hom f) : @is_group_hom (multiplicative α) (multiplicative β) _ _ f :=
{ map_mul := hf.to_is_add_hom.map_add }
