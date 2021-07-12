/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import category_theory.types
import category_theory.endomorphism
import group_theory.group_action.group
/-!
A monoid action on `X` corresponds to a monoid homomorphism to `category_theory.End X`.
-/

variables {M X : Type*} [monoid M]

/-- The monoid homomorphism corresponding to a monoid action. -/
def mul_action.to_End_hom [mul_action M X] : M →* (category_theory.End X) :=
{ to_fun := (•),
  map_one' := funext mul_action.one_smul,
  map_mul' := λ g h, funext (mul_action.mul_smul g h) }

/-- The tautological action of `category_theory.End X` on `X`. -/
instance End_mul_action : mul_action (category_theory.End X) X :=
{ smul := ($), one_smul := λ _, rfl, mul_smul := λ _ _ _, rfl }

/-- The action induced by a monoid homomorphism. -/
def mul_action.of_End_hom (f : M →* category_theory.End X) : mul_action M X :=
mul_action.comp_hom _ f
