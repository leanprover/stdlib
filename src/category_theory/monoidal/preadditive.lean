/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.additive_functor
import category_theory.monoidal.category

/-!
# Preadditive monoidal categories

A monoidal category is `monoidal_preadditive` if it is preadditive and tensor product of morphisms
is linear in both factors.
-/

noncomputable theory

namespace category_theory

open category_theory.limits
open category_theory.monoidal_category

variables (C : Type*) [category C] [preadditive C] [monoidal_category C]

/--
A category is `monoidal_preadditive` if tensoring is linear in both factors.

Note we don't `extend preadditive C` here, as `abelian C` already extends it,
and we'll need to have both typeclasses sometimes.
-/
class monoidal_preadditive :=
(tensor_zero' : ∀ {W X Y Z : C} (f : W ⟶ X), f ⊗ (0 : Y ⟶ Z) = 0 . obviously)
(zero_tensor' : ∀ {W X Y Z : C} (f : Y ⟶ Z), (0 : W ⟶ X) ⊗ f = 0 . obviously)
(tensor_add' : ∀ {W X Y Z : C} (f : W ⟶ X) (g h : Y ⟶ Z), f ⊗ (g + h) = f ⊗ g + f ⊗ h . obviously)
(add_tensor' : ∀ {W X Y Z : C} (f g : W ⟶ X) (h : Y ⟶ Z), (f + g) ⊗ h = f ⊗ h + g ⊗ h . obviously)

restate_axiom monoidal_preadditive.tensor_zero'
restate_axiom monoidal_preadditive.zero_tensor'
restate_axiom monoidal_preadditive.tensor_add'
restate_axiom monoidal_preadditive.add_tensor'
attribute [simp] monoidal_preadditive.tensor_zero monoidal_preadditive.zero_tensor

variables [monoidal_preadditive C]

local attribute [simp] monoidal_preadditive.tensor_add monoidal_preadditive.add_tensor

instance tensoring_left_additive (X : C) : ((tensoring_left C).obj X).additive := {}
instance tensoring_right_additive (X : C) : ((tensoring_right C).obj X).additive := {}

end category_theory
