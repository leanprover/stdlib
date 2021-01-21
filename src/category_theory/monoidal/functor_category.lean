/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.braided
import category_theory.const

/-!
# Monoidal structure on `C ⥤ D` when `D` is monoidal.

When `C` is any category, and `D` is a monoidal category,
there is a natural "pointwise" monoidal structure on `C ⥤ D`.

The initial intended application is tensor product of presheaves.
-/

universes v₁ v₂ u₁ u₂

open category_theory
open category_theory.monoidal_category

namespace category_theory.monoidal

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D] [monoidal_category.{v₂} D]

namespace functor_category

variables (F G F' G' : C ⥤ D)

/--
(An auxiliary definition for `functor_category_monoidal`.)
Tensor product of functors `C ⥤ D`, when `D` is monoidal.
 -/
@[simps]
def tensor_obj : C ⥤ D :=
{ obj := λ X, F.obj X ⊗ G.obj X,
  map := λ X Y f, F.map f ⊗ G.map f,
  map_id' := λ X, by rw [F.map_id, G.map_id, tensor_id],
  map_comp' := λ X Y Z f g, by rw [F.map_comp, G.map_comp, tensor_comp], }

variables {F G F' G'}
variables (α : F ⟶ G) (β : F' ⟶ G')

/--
(An auxiliary definition for `functor_category_monoidal`.)
Tensor product of natural transformations into `D`, when `D` is monoidal.
-/
@[simps]
def tensor_hom : tensor_obj F F' ⟶ tensor_obj G G' :=
{ app := λ X, α.app X ⊗ β.app X,
  naturality' :=
  λ X Y f, by { dsimp, rw [←tensor_comp, α.naturality, β.naturality, tensor_comp], } }

end functor_category

open category_theory.monoidal.functor_category

/--
When `C` is any category, and `D` is a monoidal category,
the functor category `C ⥤ D` has a natural pointwise monoidal structure,
where `(F ⊗ G).obj X = F.obj X ⊗ G.obj X`.
-/
instance functor_category_monoidal : monoidal_category (C ⥤ D) :=
{ tensor_obj := λ F G, tensor_obj F G,
  tensor_hom := λ F G F' G' α β, tensor_hom α β,
  tensor_id' := λ F G, by { ext, dsimp, rw [tensor_id], },
  tensor_comp' := λ F G H F' G' H' α β γ δ, by { ext, dsimp, rw [tensor_comp], },
  tensor_unit := (category_theory.functor.const C).obj (𝟙_ D),
  left_unitor :=  λ F,
    nat_iso.of_components (λ X, λ_ (F.obj X)) (λ X Y f, by { dsimp, rw left_unitor_naturality, }),
  right_unitor := λ F,
    nat_iso.of_components (λ X, ρ_ (F.obj X)) (λ X Y f, by { dsimp, rw right_unitor_naturality, }),
  associator := λ F G H,
    nat_iso.of_components
      (λ X, α_ (F.obj X) (G.obj X) (H.obj X)) (λ X Y f, by { dsimp, rw associator_naturality, }),
  left_unitor_naturality' := λ F G α, by { ext X, dsimp, rw left_unitor_naturality, },
  right_unitor_naturality' := λ F G α, by { ext X, dsimp, rw right_unitor_naturality, },
  associator_naturality' := λ F G H F' G' H' α β γ, by { ext X, dsimp, rw associator_naturality, },
  triangle' := λ F G, begin ext X, dsimp, rw triangle, end,
  pentagon' := λ F G H K, begin ext X, dsimp, rw pentagon, end, }

@[simp]
lemma tensor_unit_obj {X} : (𝟙_ (C ⥤ D)).obj X = 𝟙_ D := rfl

@[simp]
lemma tensor_unit_map {X Y} {f : X ⟶ Y} : (𝟙_ (C ⥤ D)).map f = 𝟙 (𝟙_ D) := rfl

@[simp]
lemma tensor_obj_obj {F G : C ⥤ D} {X} : (F ⊗ G).obj X = F.obj X ⊗ G.obj X := rfl

@[simp]
lemma tensor_obj_map {F G : C ⥤ D} {X Y} {f : X ⟶ Y} : (F ⊗ G).map f = F.map f ⊗ G.map f := rfl

@[simp]
lemma tensor_hom_app {F G F' G' : C ⥤ D} {α : F ⟶ G} {β : F' ⟶ G'} {X} :
  (α ⊗ β).app X = α.app X ⊗ β.app X := rfl

@[simp]
lemma left_unitor_hom_app {F : C ⥤ D} {X} :
  ((λ_ F).hom : (𝟙_ _) ⊗ F ⟶ F).app X = (λ_ (F.obj X)).hom := rfl

@[simp]
lemma left_unitor_inv_app {F : C ⥤ D} {X} :
  ((λ_ F).inv : F ⟶ (𝟙_ _) ⊗ F).app X = (λ_ (F.obj X)).inv := rfl

@[simp]
lemma right_unitor_hom_app {F : C ⥤ D} {X} :
  ((ρ_ F).hom : F ⊗ (𝟙_ _) ⟶ F).app X = (ρ_ (F.obj X)).hom := rfl

@[simp]
lemma right_unitor_inv_app {F : C ⥤ D} {X} :
  ((ρ_ F).inv : F ⟶ F ⊗ (𝟙_ _)).app X = (ρ_ (F.obj X)).inv := rfl

@[simp]
lemma associator_hom_app {F G H : C ⥤ D} {X} :
  ((α_ F G H).hom : (F ⊗ G) ⊗ H ⟶ F ⊗ (G ⊗ H)).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).hom := rfl

@[simp]
lemma associator_inv_app {F G H : C ⥤ D} {X} :
  ((α_ F G H).inv : F ⊗ (G ⊗ H) ⟶ (F ⊗ G) ⊗ H).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).inv := rfl

section braided_category

open category_theory.braided_category
variables [braided_category.{v₂} D]

/--
When `C` is any category, and `D` is a braided monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also braided.
-/
instance functor_category_braided : braided_category (C ⥤ D) :=
{ braiding := λ F G, nat_iso.of_components (λ X, β_ _ _) (by tidy),
  hexagon_forward' := λ F G H, by { ext X, apply hexagon_forward, },
  hexagon_reverse' := λ F G H, by { ext X, apply hexagon_reverse, }, }

example : braided_category (C ⥤ D) := category_theory.monoidal.functor_category_braided

end braided_category

section symmetric_category

open category_theory.symmetric_category
variables [symmetric_category.{v₂} D]

/--
When `C` is any category, and `D` is a symmetric monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also symmetric.
-/
instance functor_category_symmetric : symmetric_category (C ⥤ D) :=
{ symmetry' := λ F G, by { ext X, apply symmetry, },}

end symmetric_category

end category_theory.monoidal
