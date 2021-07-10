/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.preadditive.projective
import algebra.category.Module.abelian
import linear_algebra.finsupp_vector_space
import algebra.module.projective

/-!
# The category of `R`-modules has enough projectives.
-/

universes v u

open category_theory
open category_theory.limits
open linear_map

open_locale Module

/-- The categorical notion of projective object agrees with the explicit module-theoretic notion. -/
theorem is_projective.iff_projective {R : Type u} [ring R]
  {P : Type (max u v)} [add_comm_group P] [module R P] :
  module.projective R P ↔ projective (Module.of R P) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { letI : module.projective R ↥(Module.of R P) := h,
    exact ⟨λ E X f e epi, module.projective_lifting_property _ _
      ((Module.epi_iff_surjective _).mp epi)⟩ },
  { refine module.projective_of_lifting_property _,
    introsI E X mE mX sE sX f g s,
    haveI : epi ↟f := (Module.epi_iff_surjective ↟f).mpr s,
    letI : projective (Module.of R P) := h,
    exact ⟨projective.factor_thru ↟g ↟f, projective.factor_thru_comp ↟g ↟f⟩ }
end

namespace Module
variables {R : Type u} [ring R] {M : Module.{(max u v)} R}

/-- Modules that have a basis are projective. -/
-- We transport the corresponding result from `module.projective`.
lemma projective_of_free {ι : Type*} (b : basis ι R M) : projective M :=
projective.of_iso (Module.of_self_iso _)
  ((is_projective.iff_projective).mp (module.projective_of_basis b))

/-- The category of modules has enough projectives, since every module is a quotient of a free
    module. -/
instance Module_enough_projectives : enough_projectives (Module.{max u v} R) :=
{ presentation :=
  λ M,
  ⟨{ P := Module.of R (M →₀ R),
    projective := projective_of_free finsupp.basis_single_one,
    f := finsupp.basis_single_one.constr ℕ id,
    epi := (epi_iff_range_eq_top _).mpr
      (range_eq_top.2 (λ m, ⟨finsupp.single m (1 : R), by simp [basis.constr]⟩)) }⟩, }

end Module
