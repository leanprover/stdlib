/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.category
import category_theory.equivalence
import category_theory.filtered

/-!
# Basic API for ulift

This file contains a very basic API for working with the categorical
instance on `ulift C` where `C` is a type with a category instance.

1. `category_theory.ulift.up` is the functorial version of the usual `ulift.up`.
2. `category_theory.ulift.down` is the functorial version of the usual `ulift.down`.
3. `category_theory.ulift.equivalence` is the categorical equivalence between
  `C` and `ulift C`.

# ulift_hom

Given a type `C : Type u`, `ulift_hom.{w} C` is just an alias for `C`.
If we have `category.{v} C`, then `ulift_hom.{w} C` is endowed with a category instance
whose morphisms are obtained by applying `ulift.{w}` to the morphisms from `C`.

This is a category equivalent to `C`. The forward direction of the equivalence is `ulift_hom.up`,
the backward direction is `ulift_hom.donw` and the equivalence is `ulift_hom.equiv`.

# as_small

This file also contains a construction which takes a type `C : Type u` with a
category instance `category.{v} C` and makes a small category
`as_small.{w} C : Type (max w v u)` equivalent to `C`.

The forward direction of the equivalence, `C ⥤ as_small C`, is denoted `as_small.up`
and the backward direction is `as_small.down`. The equivalence itself is `as_small.equiv`.
-/

universes w₁ v₁ v₂ u₁ u₂

namespace category_theory

variables {C : Type u₁} [category.{v₁} C]

/-- The functorial version of `ulift.up`. -/
@[simps]
def ulift.up : C ⥤ (ulift.{u₂} C) :=
{ obj := ulift.up,
  map := λ X Y f, f }

/-- The functorial version of `ulift.down`. -/
@[simps]
def ulift.down : (ulift.{u₂} C) ⥤ C :=
{ obj := ulift.down,
  map := λ X Y f, f }

/-- The categorical equivalence between `C` and `ulift C`. -/
@[simps]
def ulift.equivalence : C ≌ (ulift.{u₂} C) :=
{ functor := ulift.up,
  inverse := ulift.down,
  unit_iso :=
  { hom := 𝟙 _,
    inv := 𝟙 _ },
  counit_iso :=
  { hom :=
    { app := λ X, 𝟙 _,
      naturality' := λ X Y f, by {change f ≫ 𝟙 _ = 𝟙 _ ≫ f, simp} },
    inv :=
    { app := λ X, 𝟙 _,
      naturality' := λ X Y f, by {change f ≫ 𝟙 _ = 𝟙 _ ≫ f, simp} },
  hom_inv_id' := by {ext, change (𝟙 _) ≫ (𝟙 _) = 𝟙 _, simp},
  inv_hom_id' := by {ext, change (𝟙 _) ≫ (𝟙 _) = 𝟙 _, simp} },
  functor_unit_iso_comp' := λ X, by {change (𝟙 X) ≫ (𝟙 X) = 𝟙 X, simp} }

instance [is_filtered C] : is_filtered (ulift.{u₂} C) :=
is_filtered.of_equivalence ulift.equivalence

instance [is_cofiltered C] : is_cofiltered (ulift.{u₂} C) :=
is_cofiltered.of_equivalence ulift.equivalence

section ulift_hom

/-- `ulift_hom.{w} C` is an alias for `C`, which is endowed with a category instance
  whose morphisms are obtained by applying `ulift.{w}` to the morphisms from `C`.
-/
def {w u} ulift_hom (C : Type u) := C

instance {C} [inhabited C] : inhabited (ulift_hom C) := ⟨(arbitrary C : C)⟩

/-- The obvious function `ulift_hom C → C`. -/
def ulift_hom.obj_down {C} (A : ulift_hom C) : C := A

/-- The obvious function `C → ulift_hom C`. -/
def ulift_hom.obj_up {C} (A : C) : ulift_hom C := A

@[simp] lemma obj_down_obj_up {C} (A : C) : (ulift_hom.obj_up A).obj_down = A := rfl
@[simp] lemma obj_up_obj_down {C} (A : ulift_hom C) : ulift_hom.obj_up A.obj_down = A := rfl

instance : category.{max v₂ v₁} (ulift_hom.{v₂} C) :=
{ hom := λ A B, ulift.{v₂} $ A.obj_down ⟶ B.obj_down,
  id := λ A, ⟨𝟙 _⟩,
  comp := λ A B C f g, ⟨f.down ≫ g.down⟩}

/-- One half of the quivalence between `C` and `ulift_hom C`. -/
@[simps]
def ulift_hom.up : C ⥤ ulift_hom C :=
{ obj := ulift_hom.obj_up,
  map := λ X Y f, ⟨f⟩ }

/-- One half of the quivalence between `C` and `ulift_hom C`. -/
@[simps]
def ulift_hom.down : ulift_hom C ⥤ C :=
{ obj := ulift_hom.obj_down,
  map := λ X Y f, f.down }

/-- The equivalence between `C` and `ulift_hom C`. -/
def ulift_hom.equiv : C ≌ ulift_hom C :=
{ functor := ulift_hom.up,
  inverse := ulift_hom.down,
  unit_iso := nat_iso.of_components (λ A, eq_to_iso rfl) (by tidy),
  counit_iso := nat_iso.of_components (λ A, eq_to_iso rfl) (by tidy) }

instance [is_filtered C] : is_filtered (ulift_hom C) :=
is_filtered.of_equivalence ulift_hom.equiv

instance [is_cofiltered C] : is_cofiltered (ulift_hom C) :=
is_cofiltered.of_equivalence ulift_hom.equiv

end ulift_hom

/-- `as_small C` is a small category equivalent to `C`.
  More specifically, if `C : Type u` is endowed with `category.{v} C`, then
  `as_small.{w} C : Type (max w v u)` is endowed with an instance of a small category.

  The objects and morphisms of `as_small C` are defined by applying `ulift` to the
  objects and morphisms of `C`.

  Note: We require a category instance for this definition in order to have direct
  access to the universe level `v`.
-/
@[nolint unused_arguments]
def {w v u} as_small (C : Type u) [category.{v} C] := ulift.{max w v} C

instance : small_category (as_small.{w₁} C) :=
{ hom := λ X Y, ulift.{(max w₁ u₁)} $ X.down ⟶ Y.down,
  id := λ X, ⟨𝟙 _⟩,
  comp := λ X Y Z f g, ⟨f.down ≫ g.down⟩ }

/-- One half of the equivalence between `C` and `as_small C`. -/
@[simps]
def as_small.up : C ⥤ as_small C :=
{ obj := λ X, ⟨X⟩,
  map := λ X Y f, ⟨f⟩ }

/-- One half of the equivalence between `C` and `as_small C`. -/
@[simps]
def as_small.down : as_small C ⥤ C :=
{ obj := λ X, X.down,
  map := λ X Y f, f.down }

/-- The equivalence between `C` and `as_small C`. -/
@[simps]
def as_small.equiv : C ≌ as_small C :=
{ functor := as_small.up,
  inverse := as_small.down,
  unit_iso := nat_iso.of_components (λ X, eq_to_iso rfl) (by tidy),
  counit_iso := nat_iso.of_components (λ X, eq_to_iso $ by { ext, refl }) (by tidy) }

instance [inhabited C] : inhabited (as_small C) := ⟨⟨arbitrary _⟩⟩

instance [is_filtered C] : is_filtered (as_small C) :=
is_filtered.of_equivalence as_small.equiv

instance [is_cofiltered C] : is_cofiltered (as_small C) :=
is_cofiltered.of_equivalence as_small.equiv

end category_theory
