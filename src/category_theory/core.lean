/-
Copyright (c) 2019 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.groupoid
import control.equiv_functor

namespace category_theory

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

/-- The core of a category C is the groupoid whose morphisms are all the
isomorphisms of C. -/
@[nolint has_inhabited_instance]
def core (C : Type u₁) := C

variables {C : Type u₁} [category.{v₁} C]

instance core_category : groupoid.{v₁} (core C) :=
{ hom  := λ X Y : C, X ≅ Y,
  inv  := λ X Y f, iso.symm f,
  id   := λ X, iso.refl X,
  comp := λ X Y Z f g, iso.trans f g }

namespace core
@[simp] lemma id_hom (X : core C) : iso.hom (𝟙 X) = 𝟙 X := rfl
@[simp] lemma comp_hom {X Y Z : core C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom :=
rfl

/-- The core of a category is naturally included in the category. -/
def inclusion : core C ⥤ C :=
{ obj := id,
  map := λ X Y f, f.hom }

variables {G : Type u₂} [groupoid.{v₂} G]

/-- A functor from a groupoid to a category C factors through the core of C. -/
-- Note that this function is not functorial
-- (consider the two functors from [0] to [1], and the natural transformation between them).
def functor_to_core (F : G ⥤ C) : G ⥤ core C :=
{ obj := λ X, F.obj X,
  map := λ X Y f, ⟨F.map f, F.map (inv f)⟩ }

/--
We can functorially associate to any functor from a groupoid to the core of a category `C`,
a functor from the groupoid to `C`, simply by composing with the embedding `core C ⥤ C`.
-/
def forget_functor_to_core : (G ⥤ core C) ⥤ (G ⥤ C) := (whiskering_right _ _ _).obj inclusion
end core

/--
`of_equiv_functor m` lifts a type-level `equiv_functor`
to a categorical functor `core (Type u₁) ⥤ core (Type u₂)`.
-/
def of_equiv_functor (m : Type u₁ → Type u₂) [equiv_functor m] :
  core (Type u₁) ⥤ core (Type u₂) :=
{ obj       := m,
  map       := λ α β f, (equiv_functor.map_equiv m f.to_equiv).to_iso,
  -- These are not very pretty.
  map_id' := λ α, begin ext, exact (congr_fun (equiv_functor.map_refl _) x), end,
  map_comp' := λ α β γ f g,
  begin
    ext,
    simp only [equiv_functor.map_equiv_apply, equiv.to_iso_hom,
      function.comp_app, core.comp_hom, types_comp],
    erw [iso.to_equiv_comp, equiv_functor.map_trans],
  end, }

end category_theory
