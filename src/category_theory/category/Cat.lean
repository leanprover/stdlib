/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import category_theory.concrete_category
import category_theory.discrete_category

/-!
# Category of categories

This file contains the definition of the category `Cat` of all categories.
In this category objects are categories and
morphisms are functors between these categories.

## Implementation notes

Though `Cat` is not a concrete category, we use `bundled` to define
its carrier type.
-/

universes v u

namespace category_theory

/-- Category of categories. -/
def Cat := bundled category.{v u}

namespace Cat

instance : inhabited Cat := ⟨⟨Type u, category_theory.types⟩⟩

instance : has_coe_to_sort Cat :=
{ S := Type u,
  coe := bundled.α }

instance str (C : Cat.{v u}) : category.{v u} C := C.str

/-- Construct a bundled `Cat` from the underlying type and the typeclass. -/
def of (C : Type u) [category.{v} C] : Cat.{v u} := bundled.of C

/-- Category structure on `Cat` -/
instance category : large_category.{max v u} Cat.{v u} :=
{ hom := λ C D, C ⥤ D,
  id := λ C, 𝟭 C,
  comp := λ C D E F G, F ⋙ G,
  id_comp' := λ C D F, by cases F; refl,
  comp_id' := λ C D F, by cases F; refl,
  assoc' := by intros; refl }

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Cat.{v u} ⥤ Type u :=
{ obj := λ C, C,
  map := λ C D F, F.obj }

/-- Any isomorphism in `Cat` induces an equivalence of the underlying categories. -/
def equiv_of_iso {C D : Cat} (γ : C ≅ D) : C ≌ D :=
{ functor := γ.hom,
  inverse := γ.inv,
  unit_iso := eq_to_iso $ eq.symm γ.hom_inv_id,
  counit_iso := eq_to_iso γ.inv_hom_id }

end Cat

/--
Embedding `Type` into `Cat` as discrete categories.

This ought to be modelled as a 2-functor!
-/
@[simps]
def Type_to_Cat : Type u ⥤ Cat :=
{ obj := λ X, Cat.of (discrete X),
  map := λ X Y f, discrete.functor f,
  map_id' := λ X, begin apply functor.ext, tidy, end,
  map_comp' := λ X Y Z f g, begin apply functor.ext, tidy, end }

instance : faithful Type_to_Cat := {}
instance : full Type_to_Cat :=
{ preimage := λ X Y F, F.obj,
  witness' :=
  begin
    intros X Y F,
    apply functor.ext,
    { intros x y f, dsimp, ext, },
    { intros x, refl, }
  end }

end category_theory
