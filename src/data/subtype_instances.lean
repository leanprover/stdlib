/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.module.basic

/-!
# Typeclasses on subtypes derived from closure of their predicates

A subtype `subtype p` is said to be "closed" under an operator `op` if `p a → p (op a)`. The
subscripts in the typeclass names indicate the number of arguments to the operation.
-/

namespace subtype

/-! ### Typeclasses on predicates -/

/-- A typeclass to indicate that `p` holds for `op`. -/
class closed_under₀ {α : Type*} (p : α → Prop) (op : α) :=
(closed : p op)

/-- A typeclass to indicate that `p` holds for `op a` if it holds for `a`. -/
class closed_under₁ {α : Type*} (p : α → Prop) (op : α → α) :=
(closed : ∀ {a}, p a → p (op a))

/-- A typeclass to indicate that `p` holds for `op a b` if it holds for `a` and `b`. -/
class closed_under₂ {α : Type*} (p : α → Prop) (op : α → α → α) :=
(closed : ∀ {a b}, p a → p b → p (op a b))

/-! ### Notation classes -/

variables {M α : Type*} {p : α → Prop}

@[to_additive]
instance [has_one α] [closed_under₀ p 1] : has_one (subtype p) :=
{ one := ⟨1, closed_under₀.closed _⟩}

@[simp, to_additive] lemma coe_one [has_one α] [closed_under₀ p 1] :
  ↑(1 : subtype p) = (1 : α) := rfl

@[to_additive]
instance [has_mul α] [closed_under₂ p (*)] : has_mul (subtype p) :=
{ mul := λ f g, ⟨f * g, closed_under₂.closed _ f.2 g.2⟩}

@[simp, to_additive] lemma coe_mul [has_mul α] [closed_under₂ p (*)]
  (f g : subtype p) : ↑(f * g) = (f * g : α) := rfl

@[to_additive]
instance [has_div α] [closed_under₂ p (/)] : has_div (subtype p) :=
{ div := λ f g, ⟨f / g, closed_under₂.closed _ f.2 g.2⟩}

@[simp, to_additive] lemma coe_div [has_div α] [closed_under₂ p (/)]
  (f g : subtype p) : ↑(f / g) = (f / g : α) := rfl

@[to_additive]
instance [has_inv α] [closed_under₁ p has_inv.inv] : has_inv (subtype p) :=
{ inv := λ f, ⟨f⁻¹, closed_under₁.closed _ f.2⟩}

@[simp, to_additive] lemma coe_inv [has_inv α] [closed_under₁ p has_inv.inv]
  (f : subtype p) : ↑(f⁻¹) = (f⁻¹ : α) := rfl

instance [has_scalar M α] [∀ m : M, closed_under₁ p ((•) m)] :
  has_scalar M (subtype p) :=
{ smul := λ c f, ⟨c • f, closed_under₁.closed _ f.2⟩}

@[simp] lemma coe_smul [has_scalar M α] [∀ m : M, closed_under₁ p ((•) m)]
  (c : M) (f : subtype p) : ↑(c • f) = (c • f : α) := rfl

/-! ### Algebra classes -/

/- otherwise these would clash with the instance names in `deprecated/sub***` -/
namespace closed_under

@[to_additive]
instance [mul_one_class α] [closed_under₀ p 1] [closed_under₂ p (*)] :
  mul_one_class (subtype p) :=
coe_injective.mul_one_class _ coe_one coe_mul

instance [mul_zero_one_class α] [closed_under₀ p 0] [closed_under₀ p 1] [closed_under₂ p (*)] :
  mul_zero_one_class (subtype p) :=
coe_injective.mul_zero_one_class _ coe_zero coe_one coe_mul

@[to_additive]
instance [semigroup α] [closed_under₂ p (*)] :
  semigroup (subtype p) :=
coe_injective.semigroup _ coe_mul

instance [semigroup_with_zero α] [closed_under₀ p 0] [closed_under₂ p (*)] :
  semigroup_with_zero (subtype p) :=
coe_injective.semigroup_with_zero _ coe_zero coe_mul

@[to_additive]
instance monoid' [monoid α] [closed_under₀ p 1] [closed_under₂ p (*)] :
  monoid (subtype p) :=
coe_injective.monoid _ coe_one coe_mul

instance [monoid_with_zero α] [closed_under₀ p 0] [closed_under₀ p 1] [closed_under₂ p (*)] :
  monoid_with_zero (subtype p) :=
coe_injective.monoid_with_zero _ coe_zero coe_one coe_mul

@[to_additive]
instance comm_monoid' [comm_monoid α] [closed_under₀ p 1] [closed_under₂ p (*)] :
  comm_monoid (subtype p) :=
coe_injective.comm_monoid _ coe_one coe_mul

instance [comm_monoid_with_zero α] [closed_under₀ p 0] [closed_under₀ p 1] [closed_under₂ p (*)] :
  comm_monoid_with_zero (subtype p) :=
coe_injective.comm_monoid_with_zero _ coe_zero coe_one coe_mul

@[to_additive]
instance [group α] [closed_under₀ p 1] [closed_under₂ p (*)]
  [closed_under₂ p (/)] [closed_under₁ p (has_inv.inv)] :
  group (subtype p) :=
coe_injective.group _ coe_one coe_mul coe_inv coe_div

instance [group_with_zero α] [closed_under₀ p 0] [closed_under₀ p 1] [closed_under₂ p (*)]
  [closed_under₂ p (/)] [closed_under₁ p (has_inv.inv)] :
  group_with_zero (subtype p) :=
coe_injective.group_with_zero _ coe_zero coe_one coe_mul coe_inv coe_div

@[to_additive]
instance [comm_group α] [closed_under₀ p 1] [closed_under₂ p (*)] [closed_under₂ p (/)]
  [closed_under₁ p (has_inv.inv)]  :
  comm_group (subtype p) :=
coe_injective.comm_group _ coe_one coe_mul coe_inv coe_div

instance [comm_group_with_zero α] [closed_under₀ p 0] [closed_under₀ p 1] [closed_under₂ p (*)]
  [closed_under₂ p (/)] [closed_under₁ p (has_inv.inv)] :
  comm_group_with_zero (subtype p) :=
coe_injective.comm_group_with_zero _ coe_zero coe_one coe_mul coe_inv coe_div

/-! #### Rings -/

instance [semiring α]
  [closed_under₀ p 0] [closed_under₀ p 1] [closed_under₂ p (+)] [closed_under₂ p (*)] :
  semiring (subtype p) :=
coe_injective.semiring _ coe_zero coe_one coe_add coe_mul

instance [comm_semiring α]
  [closed_under₀ p 0] [closed_under₀ p 1] [closed_under₂ p (+)] [closed_under₂ p (*)] :
  comm_semiring (subtype p) :=
coe_injective.comm_semiring _ coe_zero coe_one coe_add coe_mul

instance [ring α]
  [closed_under₀ p 0] [closed_under₀ p 1] [closed_under₂ p (+)] [closed_under₂ p (*)]
  [closed_under₁ p (has_neg.neg)] [closed_under₂ p (has_sub.sub)] :
  ring (subtype p) :=
coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub

instance [comm_ring α]
  [closed_under₀ p 0] [closed_under₀ p 1] [closed_under₂ p (+)] [closed_under₂ p (*)]
  [closed_under₁ p (has_neg.neg)] [closed_under₂ p (has_sub.sub)] :
  comm_ring (subtype p) :=
coe_injective.comm_ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub

instance [division_ring α]
  [closed_under₀ p 0] [closed_under₀ p 1] [closed_under₂ p (+)] [closed_under₂ p (*)]
  [closed_under₁ p (has_neg.neg)] [closed_under₂ p (has_sub.sub)]
  [closed_under₁ p (has_inv.inv)] [closed_under₂ p (has_div.div)] :
  division_ring (subtype p) :=
coe_injective.division_ring _
  coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_inv coe_div

instance [field α]
  [closed_under₀ p 0] [closed_under₀ p 1] [closed_under₂ p (+)] [closed_under₂ p (*)]
  [closed_under₁ p (has_neg.neg)] [closed_under₂ p (has_sub.sub)]
  [closed_under₁ p (has_inv.inv)] [closed_under₂ p (has_div.div)] :
  field (subtype p) :=
coe_injective.field _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_inv coe_div

/-! #### Actions -/

instance [monoid M] [mul_action M α] [Π m : M, closed_under₁ p ((•) m)] :
  mul_action M (subtype p) :=
coe_injective.mul_action _ coe_smul

instance [monoid M] [add_monoid α] [distrib_mul_action M α]
  [closed_under₀ p 0] [closed_under₂ p (+)] [Π m : M, closed_under₁ p ((•) m)] :
  distrib_mul_action M (subtype p) :=
function.injective.distrib_mul_action ⟨coe, coe_zero, coe_add⟩ coe_injective coe_smul

instance [semiring M] [add_comm_monoid α] [module M α]
  [closed_under₀ p 0] [closed_under₂ p (+)] [Π m : M, closed_under₁ p ((•) m)] :
  module M (subtype p) :=
function.injective.module M ⟨coe, coe_zero, coe_add⟩ coe_injective coe_smul

end closed_under

end subtype
