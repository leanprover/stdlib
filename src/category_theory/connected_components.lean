/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.list.chain
import category_theory.punit
import category_theory.is_connected
import category_theory.sigma.basic
import category_theory.full_subcategory

/-!
# Connected components of a category

Defines a type `connected_components J` indexing the connected components of a category, and the
full subcategories giving each connected component: `component j : Type u₁`.
We show that each `component j` is in fact connected.

We show every category can be expressed as a disjoint union of its connected components, in
particular `decomposed J` is the category (definitionally) given by the sigma-type of the connected
components of `J`, and it is shown that this is equivalent to `J`.
-/

universes v₁ v₂ v₃ u₁ u₂

noncomputable theory

open category_theory.category

namespace category_theory

attribute [instance, priority 100] is_connected.is_nonempty

variables {J : Type u₁} [category.{v₁} J]
variables {C : Type u₂} [category.{u₁} C]

/-- This type indexes the connected components of the category `J`. -/
def connected_components (J : Type u₁) [category.{v₁} J] : Type u₁ := quotient (zigzag.setoid J)

instance [inhabited J] : inhabited (connected_components J) := ⟨quotient.mk' (default J)⟩

/-- Given an index for a connected component, produce the actual component as a full subcategory. -/
@[derive category]
def component (j : connected_components J) : Type u₁ := {k : J // quotient.mk' k = j}

/-- The inclusion functor from a connected component to the whole category. -/
@[derive [full, faithful], simps {rhs_md := semireducible}]
def component.ι (j) : component j ⥤ J :=
full_subcategory_inclusion _

/-- Each connected component of the category is nonempty. -/
instance (j : connected_components J) : nonempty (component j) :=
begin
  apply quotient.induction_on' j,
  intro k,
  refine ⟨⟨k, rfl⟩⟩,
end

instance (j : connected_components J) : inhabited (component j) := classical.inhabited_of_nonempty'

/-- Each connected component of the category is connected. -/
instance (j : connected_components J) : is_connected (component j) :=
begin
  -- Show it's connected by constructing a zigzag (in `component j`) between any two objects
  apply is_connected_of_zigzag,
  rintro ⟨j₁, hj₁⟩ ⟨j₂, rfl⟩,
  -- We know that the underlying objects j₁ j₂ have some zigzag between them in `J`
  have h₁₂ : zigzag j₁ j₂ := quotient.exact' hj₁,
  -- Get an explicit zigzag as a list
  rcases list.exists_chain_of_relation_refl_trans_gen h₁₂ with ⟨l, hl₁, hl₂⟩,
  -- Everything which has a zigzag to j₂ can be lifted to the same component as `j₂`.
  let f : Π x, zigzag x j₂ → component (quotient.mk' j₂) := λ x h, ⟨x, quotient.sound' h⟩,
  -- Everything in our chosen zigzag from `j₁` to `j₂` has a zigzag to `j₂`.
  have hf : ∀ (a : J), a ∈ l → zigzag a j₂,
  { intros i hi,
    apply list.chain.induction (λ t, zigzag t j₂) _ hl₁ hl₂ _ _ _ (or.inr hi),
    { intros j k,
      apply relation.refl_trans_gen.head },
    { apply relation.refl_trans_gen.refl } },
  -- Now lift the zigzag from `j₁` to `j₂` in `J` to the same thing in `component j`.
  refine ⟨l.pmap f hf, _, _⟩,
  { refine @@list.chain_pmap_of_chain _ _ _ f (λ x y _ _ h, _) hl₁ h₁₂ _,
    exact zag_of_zag_obj (component.ι _) h },
  { erw list.last_pmap _ f (j₁ :: l) (by simpa [h₁₂] using hf) (list.cons_ne_nil _ _),
    exact subtype.ext hl₂ },
end

/--
The disjoint union of `J`s connected components, written explicitly as a sigma-type with the
category structure.
This category is equivalent to `J`.
-/
abbreviation decomposed (J : Type u₁) [category.{v₁} J] :=
Σ (j : connected_components J), component j

/--
The inclusion of each component into the decomposed category. This is just `sigma.incl` but having
this abbreviation helps guide typeclass search to get the right category instance on `decomposed J`.
-/
-- This name may cause clashes further down the road, and so might need to be changed.
abbreviation inclusion (j : connected_components J) : component j ⥤ decomposed J :=
sigma.incl _

/-- The forward direction of the equivalence between the decomposed category and the original. -/
@[simps {rhs_md := semireducible}]
def decomposed_to (J : Type u₁) [category.{v₁} J] : decomposed J ⥤ J :=
sigma.desc component.ι

@[simp]
lemma inclusion_comp_decomposed_to (j : connected_components J) :
  inclusion j ⋙ decomposed_to J = component.ι j :=
rfl

instance : full (decomposed_to J) :=
{ preimage :=
  begin
    rintro ⟨j', X, hX⟩ ⟨k', Y, hY⟩ f,
    dsimp at f,
    have : j' = k',
      rw [← hX, ← hY, quotient.eq'],
      exact relation.refl_trans_gen.single (or.inl ⟨f⟩),
    subst this,
    refine sigma.sigma_hom.mk f,
  end,
  witness' :=
  begin
    rintro ⟨j', X, hX⟩ ⟨_, Y, rfl⟩ f,
    have : quotient.mk' Y = j',
    { rw [← hX, quotient.eq'],
      exact relation.refl_trans_gen.single (or.inr ⟨f⟩) },
    subst this,
    refl,
  end }

instance : faithful (decomposed_to J) :=
{ map_injective' :=
  begin
    rintro ⟨_, j, rfl⟩ ⟨_, k, hY⟩ ⟨_, _, _, f⟩ ⟨_, _, _, g⟩ e,
    change f = g at e,
    subst e,
  end }

instance : ess_surj (decomposed_to J) :=
{ mem_ess_image := λ j, ⟨⟨_, j, rfl⟩, ⟨iso.refl _⟩⟩ }

instance : is_equivalence (decomposed_to J) :=
equivalence.of_fully_faithfully_ess_surj _

/-- This gives that any category is equivalent to a disjoint union of connected categories. -/
@[simps functor {rhs_md := semireducible}]
def decomposed_equiv : decomposed J ≌ J :=
(decomposed_to J).as_equivalence

end category_theory
