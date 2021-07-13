/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import order.category.PartialOrder

/-! # Category of linearly ordered types -/

universe u

open category_theory

/-- The category of linearly ordered types. -/
def LinearOrder := bundled linear_order

namespace LinearOrder

instance : bundled_hom.parent_projection @linear_order.to_partial_order := ⟨⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] LinearOrder

/-- Construct a bundled LinearOrder from the underlying type and typeclass. -/
def of (α : Type*) [linear_order α] : LinearOrder := bundled.of α

instance : inhabited LinearOrder := ⟨of punit⟩

instance (α : LinearOrder) : linear_order α := α.str

instance : representably_concrete LinearOrder.{u} :=
{ out := functor.corepresentable_of_nat_iso _ (opposite.op (of punit))
          (nat_iso.of_components
            (λ X, { hom := λ (f : _ ⟶ _), f ⟨⟩,
                    inv := λ x, ⟨λ _, x, monotone_const⟩})
            (λ X Y f, rfl)) }

end LinearOrder
