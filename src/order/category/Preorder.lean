/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import order.preorder_hom
import category_theory.concrete_category
import algebra.punit_instances
import category_theory.concrete_category.representable

/-! # Category of preorders -/

universe u

open category_theory

/-- The category of preorders. -/
def Preorder := bundled preorder

namespace Preorder

instance : bundled_hom @preorder_hom :=
{ to_fun := @preorder_hom.to_fun,
  id := @preorder_hom.id,
  comp := @preorder_hom.comp,
  hom_ext := @preorder_hom.ext }

attribute [derive [has_coe_to_sort, large_category, concrete_category]] Preorder

/-- Construct a bundled Preorder from the underlying type and typeclass. -/
def of (α : Type*) [preorder α] : Preorder := bundled.of α

instance : inhabited Preorder := ⟨of punit⟩

instance (α : Preorder) : preorder α := α.str

def free : Type u ⥤ Preorder.{u} :=
{ obj := λ X, ⟨X, { le := λ x y, x = y, le_refl := λ x, rfl, le_trans := λ x y z, eq.trans }⟩,
  map := λ X Y f,
  { to_fun := f,
    monotone' := by { rintro x y ⟨⟩, refl } } }

def adj : free ⊣ forget Preorder.{u} :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, f,
    inv_fun := λ f,
    { to_fun := f,
      monotone' := by { rintro x y ⟨⟩, refl } },
    left_inv := λ f, by { ext, refl },
    right_inv := λ f, rfl } }

instance : is_right_adjoint (forget Preorder.{u}) :=
⟨_, adj⟩

instance : representably_concrete Preorder :=
{ out := corepresentable_of_right_adjoint _ _ }

end Preorder
