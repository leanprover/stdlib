/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Simon Hudon
-/
import category_theory.monoidal.braided
import category_theory.limits.shapes.binary_products

/-!
# The natural monoidal structure on any category with finite (co)products.

A category with a monoidal structure provided in this way is sometimes called a (co)cartesian category,
although this is also sometimes used to mean a finitely complete category.
(See <https://ncatlab.org/nlab/show/cartesian+category>.)

As this works with either products or coproducts,
and sometimes we want to think of a different monoidal structure entirely,
we don't set up either construct as an instance.

## Implementation
We had previously chosen to rely on `has_terminal` and `has_binary_products` instead of
`has_finite_products`, because we were later relying on the definitional form of the tensor product.
Now that `has_limit` has been refactored to be a `Prop`,
this issue is irrelevant and we could simplify the construction here.

See `category_theory.monoidal.of_chosen_finite_products` for a variant of this construction
which allows specifying a particular choice of terminal object and binary products.
-/

universes v u

noncomputable theory

namespace category_theory

variables (C : Type u) [category.{v} C] {X Y : C}

open category_theory.limits

section
local attribute [tidy] tactic.case_bash

/-- A category with a terminal object and binary products has a natural monoidal structure. -/
def monoidal_of_has_finite_products [has_terminal C] [has_binary_products C] : monoidal_category C :=
{ tensor_unit  := ⊤_ C,
  tensor_obj   := λ X Y, X ⨯ Y,
  tensor_hom   := λ _ _ _ _ f g, limits.prod.map f g,
  associator   := prod.associator,
  left_unitor  := λ P, prod.left_unitor P,
  right_unitor := λ P, prod.right_unitor P,
  pentagon'    := prod.pentagon,
  triangle'    := prod.triangle,
  associator_naturality' := @prod.associator_naturality _ _ _, }
end

section
local attribute [instance] monoidal_of_has_finite_products

open monoidal_category

/--
The monoidal structure coming from finite products is symmetric.
-/
@[simps]
def symmetric_of_has_finite_products [has_terminal C] [has_binary_products C] :
  symmetric_category C :=
{ braiding := λ X Y, limits.prod.braiding X Y,
  braiding_naturality' := λ X X' Y Y' f g,
    by { dsimp [tensor_hom], simp, },
  hexagon_forward' := λ X Y Z,
    by { dsimp [monoidal_of_has_finite_products], simp },
  hexagon_reverse' := λ X Y Z,
    by { dsimp [monoidal_of_has_finite_products], simp },
  symmetry' := λ X Y, by { dsimp, simp, refl, }, }

end

namespace monoidal_of_has_finite_products

variables [has_terminal C] [has_binary_products C]
local attribute [instance] monoidal_of_has_finite_products

@[simp]
lemma tensor_obj (X Y : C) : X ⊗ Y = (X ⨯ Y) := rfl
@[simp]
lemma tensor_hom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ g = limits.prod.map f g := rfl

@[simp]
lemma left_unitor_hom (X : C) : (λ_ X).hom = limits.prod.snd := rfl
@[simp]
lemma left_unitor_inv (X : C) : (λ_ X).inv = prod.lift (terminal.from X) (𝟙 _) := rfl
@[simp]
lemma right_unitor_hom (X : C) : (ρ_ X).hom = limits.prod.fst := rfl
@[simp]
lemma right_unitor_inv (X : C) : (ρ_ X).inv = prod.lift (𝟙 _) (terminal.from X) := rfl
-- We don't mark this as a simp lemma, even though in many particular
-- categories the right hand side will simplify significantly further.
-- For now, we'll plan to create specialised simp lemmas in each particular category.
lemma associator_hom (X Y Z : C) :
  (α_ X Y Z).hom =
  prod.lift
    (limits.prod.fst ≫ limits.prod.fst)
    (prod.lift (limits.prod.fst ≫ limits.prod.snd) limits.prod.snd) := rfl

end monoidal_of_has_finite_products

section
local attribute [tidy] tactic.case_bash

/-- A category with an initial object and binary coproducts has a natural monoidal structure. -/
def monoidal_of_has_finite_coproducts [has_initial C] [has_binary_coproducts C] : monoidal_category C :=
{ tensor_unit  := ⊥_ C,
  tensor_obj   := λ X Y, X ⨿ Y,
  tensor_hom   := λ _ _ _ _ f g, limits.coprod.map f g,
  associator   := coprod.associator,
  left_unitor  := coprod.left_unitor,
  right_unitor := coprod.right_unitor,
  pentagon'    := coprod.pentagon,
  triangle'    := coprod.triangle,
  associator_naturality' := @coprod.associator_naturality _ _ _, }
end


section
local attribute [instance] monoidal_of_has_finite_coproducts

open monoidal_category

/--
The monoidal structure coming from finite coproducts is symmetric.
-/
@[simps]
def symmetric_of_has_finite_coproducts [has_initial C] [has_binary_coproducts C] :
  symmetric_category C :=
{ braiding := limits.coprod.braiding,
  braiding_naturality' := λ X X' Y Y' f g,
    by { dsimp [tensor_hom], simp, },
  hexagon_forward' := λ X Y Z,
    by { dsimp [monoidal_of_has_finite_coproducts], simp },
  hexagon_reverse' := λ X Y Z,
    by { dsimp [monoidal_of_has_finite_coproducts], simp },
  symmetry' := λ X Y, by { dsimp, simp, refl, }, }

end

namespace monoidal_of_has_finite_coproducts

variables [has_initial C] [has_binary_coproducts C]
local attribute [instance] monoidal_of_has_finite_coproducts

@[simp]
lemma tensor_obj (X Y : C) : X ⊗ Y = (X ⨿ Y) := rfl
@[simp]
lemma tensor_hom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ g = limits.coprod.map f g := rfl

@[simp]
lemma left_unitor_hom (X : C) : (λ_ X).hom = coprod.desc (initial.to X) (𝟙 _) := rfl
@[simp]
lemma right_unitor_hom (X : C) : (ρ_ X).hom = coprod.desc (𝟙 _) (initial.to X) := rfl
@[simp]
lemma left_unitor_inv (X : C) : (λ_ X).inv = limits.coprod.inr := rfl
@[simp]
lemma right_unitor_inv (X : C) : (ρ_ X).inv = limits.coprod.inl := rfl
-- We don't mark this as a simp lemma, even though in many particular
-- categories the right hand side will simplify significantly further.
-- For now, we'll plan to create specialised simp lemmas in each particular category.
lemma associator_hom (X Y Z : C) :
  (α_ X Y Z).hom =
  coprod.desc
    (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr))
    (coprod.inr ≫ coprod.inr) := rfl

end monoidal_of_has_finite_coproducts

end category_theory
