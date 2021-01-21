/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.binary_products

/-!
# Subterminal objects

Subterminal objects are the objects which can be thought of as subobjects of the terminal object.
In fact, the definition can be constructed to not require a terminal object, by defining `A` to be
subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`.
An alternate definition is that the diagonal morphism `A ⟶ A ⨯ A` is an isomorphism.
In this file we define subterminal objects and show the equivalence of these three definitions.

We also construct the subcategory of subterminal objects.

## TODO

* Define exponential ideals, and show this subcategory is an exponential ideal.
* Define subobject lattices in general, show that `subterminals C` is equivalent to the subobject
category of a terminal object.
* Use both the above to show that in a locally cartesian closed category, every subobject lattice
  is cartesian closed (equivalently, a Heyting algebra).

-/
universes v₁ v₂ u₁ u₂

noncomputable theory

namespace category_theory

open limits category

variables {C : Type u₁} [category.{v₁} C] {A : C}

/-- An object `A` is subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`. -/
def is_subterminal (A : C) : Prop := ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g

lemma is_subterminal.def : is_subterminal A ↔ ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g := iff.rfl

/--
If `A` is subterminal, the unique morphism from it to a terminal object is a monomorphism.
The converse of `is_subterminal_of_mono_is_terminal_from`.
-/
lemma is_subterminal.mono_is_terminal_from (hA : is_subterminal A) {T : C} (hT : is_terminal T) :
  mono (hT.from A) :=
{ right_cancellation := λ Z g h _, hA _ _ }

/--
If `A` is subterminal, the unique morphism from it to the terminal object is a monomorphism.
The converse of `is_subterminal_of_mono_terminal_from`.
-/
lemma is_subterminal.mono_terminal_from [has_terminal C] (hA : is_subterminal A) :
  mono (terminal.from A) :=
hA.mono_is_terminal_from terminal_is_terminal

/--
If the unique morphism from `A` to a terminal object is a monomorphism, `A` is subterminal.
The converse of `is_subterminal.mono_is_terminal_from`.
-/
lemma is_subterminal_of_mono_is_terminal_from {T : C} (hT : is_terminal T) [mono (hT.from A)] :
  is_subterminal A :=
λ Z f g, by { rw ← cancel_mono (hT.from A), apply hT.hom_ext }

/--
If the unique morphism from `A` to the terminal object is a monomorphism, `A` is subterminal.
The converse of `is_subterminal.mono_terminal_from`.
-/
lemma is_subterminal_of_mono_terminal_from [has_terminal C] [mono (terminal.from A)] :
  is_subterminal A :=
λ Z f g, by { rw ← cancel_mono (terminal.from A), apply subsingleton.elim }

lemma is_subterminal_of_is_terminal {T : C} (hT : is_terminal T) : is_subterminal T :=
λ Z f g, hT.hom_ext _ _

lemma is_subterminal_of_terminal [has_terminal C] : is_subterminal (⊤_ C) :=
λ Z f g, subsingleton.elim _ _

/--
If `A` is subterminal, its diagonal morphism is an isomorphism.
The converse of `is_subterminal_of_is_iso_diag`.
-/
def is_subterminal.is_iso_diag (hA : is_subterminal A) [has_binary_product A A] :
  is_iso (diag A) :=
{ inv := limits.prod.fst,
  inv_hom_id' := by { rw is_subterminal.def at hA, tidy } }

/--
If the diagonal morphism of `A` is an isomorphism, then it is subterminal.
The converse of `is_subterminal.is_iso_diag`.
-/
lemma is_subterminal_of_is_iso_diag [has_binary_product A A] [is_iso (diag A)] :
  is_subterminal A :=
λ Z f g,
begin
  have : (limits.prod.fst : A ⨯ A ⟶ _) = limits.prod.snd,
  { simp [←cancel_epi (diag A)] },
  rw [←prod.lift_fst f g, this, prod.lift_snd],
end

/-- If `A` is subterminal, it is isomorphic to `A ⨯ A`. -/
@[simps]
def is_subterminal.iso_diag (hA : is_subterminal A) [has_binary_product A A] :
  A ⨯ A ≅ A :=
begin
  letI := is_subterminal.is_iso_diag hA,
  apply (as_iso (diag A)).symm,
end

variables (C)
/--
The (full sub)category of subterminal objects.
TODO: If `C` is the category of sheaves on a topological space `X`, this category is equivalent
to the lattice of open subsets of `X`. More generally, if `C` is a topos, this is the lattice of
"external truth values".
-/
@[derive category]
def subterminals (C : Type u₁) [category.{v₁} C] :=
{A : C // is_subterminal A}

instance [has_terminal C] : inhabited (subterminals C) :=
⟨⟨⊤_ C, is_subterminal_of_terminal⟩⟩

/-- The inclusion of the subterminal objects into the original category. -/
@[derive [full, faithful]]
def subterminal_inclusion : subterminals C ⥤ C := full_subcategory_inclusion _

end category_theory
