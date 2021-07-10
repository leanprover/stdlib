/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Mario Carneiro
-/
import topology.category.Top.basic
import category_theory.adjunction.basic

/-!
# Adjunctions regarding the category of topological spaces

This file shows that the forgetful functor from topological spaces to types has a left and right
adjoint, given by `Top.discrete`, resp. `Top.trivial`, the functors which equip a type with the
discrete, resp. trivial, topology.
-/

universe u

open category_theory
open Top

namespace Top

/-- Equipping a type with the discrete topology is left adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps unit counit]
def adj₁ : discrete ⊣ forget Top.{u} :=
adjunction.mk_of_unit_counit
{ unit := { app := λ X, id },
  counit := { app := λ X, ⟨id, continuous_bot⟩ } }

/-- Equipping a type with the trivial topology is right adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps unit counit]
def adj₂ : forget Top.{u} ⊣ trivial :=
adjunction.mk_of_unit_counit
{ unit := { app := λ X, ⟨id, continuous_top⟩ },
  counit := { app := λ X, id } }

instance : is_right_adjoint (forget Top.{u}) := ⟨_, adj₁⟩

end Top
