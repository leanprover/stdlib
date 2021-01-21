/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Mario Carneiro
-/
import topology.category.Top.basic

universe u

open category_theory
open Top

namespace Top

/-- Equipping a type with the discrete topology is left adjoint to the forgetful functor `Top ⥤ Type`. -/
def adj₁ : discrete ⊣ forget Top.{u} :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, f,
    inv_fun := λ f, ⟨f, continuous_bot⟩,
    left_inv := by tidy,
    right_inv := by tidy },
  unit := { app := λ X, id },
  counit := { app := λ X, ⟨id, continuous_bot⟩ } }

/-- Equipping a type with the trivial topology is right adjoint to the forgetful functor `Top ⥤ Type`. -/
def adj₂ : forget Top.{u} ⊣ trivial :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, ⟨f, continuous_top⟩,
    inv_fun := λ f, f,
    left_inv := λ X, rfl,
    right_inv := λ Y, continuous_map.coe_inj rfl, },
  unit := { app := λ X, ⟨id, continuous_top⟩ },
  counit := { app := λ X, id }, }

end Top
