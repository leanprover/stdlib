/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.category.Group.Z_Module_equivalence
import algebra.category.Group.colimits
import algebra.category.Module.abelian

/-!
# The category of abelian groups is abelian
-/

open category_theory
open category_theory.limits

universe u

noncomputable theory

namespace AddCommGroup

section
variables {X Y : AddCommGroup.{u}} (f : X ⟶ Y)

/-- In the category of abelian groups, every monomorphism is normal. -/
def normal_mono (hf : mono f) : normal_mono f :=
equivalence_reflects_normal_mono (forget₂ (Module.{u} ℤ) AddCommGroup.{u}).inv $
  Module.normal_mono _ $ right_adjoint_preserves_mono (functor.adjunction _) hf

/-- In the category of abelian groups, every epimorphism is normal. -/
def normal_epi (hf : epi f) : normal_epi f :=
equivalence_reflects_normal_epi (forget₂ (Module.{u} ℤ) AddCommGroup.{u}).inv $
  Module.normal_epi _ $ left_adjoint_preserves_epi (functor.adjunction _) hf

end

/-- The category of abelian groups is abelian. -/
instance : abelian AddCommGroup :=
{ has_finite_products := by { dsimp [has_finite_products], apply_instance },
  normal_mono := λ X Y, normal_mono,
  normal_epi := λ X Y, normal_epi }

end AddCommGroup
