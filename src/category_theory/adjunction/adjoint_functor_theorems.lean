/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.adjunction.basic
import category_theory.adjunction.comma
import category_theory.limits.constructions.weakly_initial
import category_theory.limits.preserves.basic
import category_theory.limits.creates
import category_theory.limits.comma
import category_theory.punit

/-!
# Adjoint functor theorem

This file proves the (general) adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` has limits, and satisfies the solution set condition,
  then it has a left adjoint.

We show that the converse holds, i.e. that if `G` has a left adjoint then it satisfies the solution
set condition (`category_theory/adjunction/limits` already shows it preserves limits).

We define the solution set condition for the functor `G : D ⥤ C` to mean, for every object `A : C`,
there is a set-indexed family ${f_i : A ⟶ G (B_i)}$ such that any morphism `A ⟶ G X` factors
through one of the `f_i`.

-/
universes v u

namespace category_theory
open limits

variables {J : Type v}
variables {C : Type u} [category.{v} C]

/--
The functor `G : D ⥤ C` satisfies the *solution set condition* if for every `A : C`, there is a
family of morphisms `{f_i : A ⟶ G (B_i) // i ∈ ι}` such that given any morphism `h : A ⟶ G X`,
there is some `i ∈ ι` such that `h` factors through `f_i`.

The key part of this definition is that the indexing set `ι` lives in `Type v`, where `v` is the
universe of morphisms of the category: this is the "smallness" condition which allows the general
adjoint functor theorem to go through.
-/
def solution_set_condition {D : Type u} [category.{v} D] (G : D ⥤ C) : Prop :=
  ∀ (A : C), ∃ (ι : Type v) (B : ι → D) (f : Π (i : ι), A ⟶ G.obj (B i)),
  ∀ X (h : A ⟶ G.obj X), ∃ (i : ι) (g : B i ⟶ X), f i ≫ G.map g = h

variables {D : Type u} [category.{v} D]

section gaft

variables (G : D ⥤ C)

/-- If `G : D ⥤ C` is a right adjoint it satisfies the solution set condition.  -/
lemma solution_set_condition_of_is_right_adjoint [is_right_adjoint G] :
  solution_set_condition G :=
begin
  intros A,
  refine ⟨punit, λ _, (left_adjoint G).obj A, λ _, (adjunction.of_right_adjoint G).unit.app A, _⟩,
  intros B h,
  refine ⟨punit.star, ((adjunction.of_right_adjoint G).hom_equiv _ _).symm h, _⟩,
  rw [←adjunction.hom_equiv_unit, equiv.apply_symm_apply],
end

/--
The general adjoint functor theorem says that if `G : D ⥤ C` preserves limits and `D` has them,
then `G` is a right adjoint.
-/
noncomputable def is_right_adjoint_of_preserves_limits_of_solution_set_condition
  [has_limits D] [preserves_limits G] (hG : solution_set_condition G) :
  is_right_adjoint G :=
begin
  apply is_right_adjoint_of_structured_arrow_initials _,
  intro A,
  specialize hG A,
  choose ι B f g using hG,
  let B' : ι → structured_arrow A G := λ i, structured_arrow.mk (f i),
  have hB' : ∀ (A' : structured_arrow A G), ∃ i, nonempty (B' i ⟶ A'),
  { intros A',
    obtain ⟨i, _, t⟩ := g _ A'.hom,
    exact ⟨i, ⟨structured_arrow.hom_mk _ t⟩⟩ },
  obtain ⟨T, hT⟩ := has_weakly_initial_of_weakly_initial_set_and_has_products hB',
  apply has_initial_of_weakly_initial_and_has_wide_equalizers hT,
end



end gaft

end category_theory
