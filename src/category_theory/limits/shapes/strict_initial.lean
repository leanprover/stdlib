/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.terminal
import category_theory.limits.shapes.binary_products
import category_theory.epi_mono

/-!
# Strict initial objects

This file sets up the basic theory of strict initial objects: initial objects where every morphism
to it is an isomorphism. This generalises a property of the empty set in the category of sets:
namely that the only function to the empty set is from itself.

We say `C` has strict initial objects if every initial object is strict, ie given any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.
Strictly speaking, this says that *any* initial object must be strict, rather than that strict
initial objects exist, which turns out to be a more useful notion to formalise.

If the binary product of `X` with a strict initial object exists, it is also initial.

To show a category `C` with an initial object has strict initial objects, the most convenient way
is to show any morphism to the (chosen) initial object is an isomorphism and use
`has_strict_initial_object_of_initial_is_strict`.

The dual notion (strict terminal objects) occurs much less frequently in practice so is ignored.

## TODO

* Construct examples of this: `Type*`, `Top`, `Groupoid`, simplicial types, posets.
* Construct the bottom element of the subobject lattice given strict initials.
* Show cartesian closed categories have strict initials

## References
* https://ncatlab.org/nlab/show/strict+initial+object
-/


universes v u

namespace category_theory
namespace limits
open category

variables (C : Type u) [category.{v} C]

/--
We say `C` has strict initial objects if every initial object is strict, ie given any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.

Strictly speaking, this says that *any* initial object must be strict, rather than that strict
initial objects exist.
-/
class has_strict_initial_object : Prop :=
(out : ∀ {I A : C} (f : A ⟶ I), is_initial I → is_iso f)

variables {C}

section
variables [has_strict_initial_object C] {I : C}

lemma is_initial.is_iso_to (hI : is_initial I) {A : C} (f : A ⟶ I) :
  is_iso f :=
has_strict_initial_object.out f hI

lemma is_initial.strict_hom_ext (hI : is_initial I) {A : C} (f g : A ⟶ I) :
  f = g :=
begin
  haveI := hI.is_iso_to f,
  haveI := hI.is_iso_to g,
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g)),
end

lemma is_initial.subsingleton_to (hI : is_initial I) {A : C} :
  subsingleton (A ⟶ I) :=
⟨hI.strict_hom_ext⟩

/-- If `I` is initial, then `X ⨯ I` is isomorphic to it. -/
@[simps hom]
noncomputable def mul_is_initial (X : C) [has_binary_product X I] (hI : is_initial I) :
  X ⨯ I ≅ I :=
@@as_iso _ prod.snd (hI.is_iso_to _)

@[simp] lemma mul_is_initial_inv (X : C) [has_binary_product X I] (hI : is_initial I) :
  (mul_is_initial X hI).inv = hI.to _ :=
hI.hom_ext _ _

/-- If `I` is initial, then `I ⨯ X` is isomorphic to it. -/
@[simps hom]
noncomputable def is_initial_mul (X : C) [has_binary_product I X] (hI : is_initial I) :
  I ⨯ X ≅ I :=
@@as_iso _ prod.fst (hI.is_iso_to _)

@[simp] lemma is_initial_mul_inv (X : C) [has_binary_product I X] (hI : is_initial I) :
  (is_initial_mul X hI).inv = hI.to _ :=
hI.hom_ext _ _

variable [has_initial C]

instance initial_is_iso_to {A : C} (f : A ⟶ ⊥_ C) : is_iso f :=
initial_is_initial.is_iso_to _

@[ext] lemma initial.hom_ext {A : C} (f g : A ⟶ ⊥_ C) : f = g :=
initial_is_initial.strict_hom_ext _ _

lemma initial.subsingleton_to {A : C} : subsingleton (A ⟶ ⊥_ C) :=
initial_is_initial.subsingleton_to

/--
The product of `X` with an initial object in a category with strict initial objects is itself
initial.
This is the generalisation of the fact that `X × empty ≃ empty` for types (or `n * 0 = 0`).
-/
@[simps hom]
noncomputable def mul_initial (X : C) [has_binary_product X ⊥_ C] :
  X ⨯ ⊥_ C ≅ ⊥_ C :=
mul_is_initial _ initial_is_initial

@[simp] lemma mul_initial_inv (X : C) [has_binary_product X ⊥_ C] :
  (mul_initial X).inv = initial.to _ :=
subsingleton.elim _ _

/--
The product of `X` with an initial object in a category with strict initial objects is itself
initial.
This is the generalisation of the fact that `empty × X ≃ empty` for types (or `0 * n = 0`).
-/
@[simps hom]
noncomputable def initial_mul (X : C) [has_binary_product (⊥_ C) X] :
  ⊥_ C ⨯ X ≅ ⊥_ C :=
is_initial_mul _ initial_is_initial

@[simp] lemma initial_mul_inv (X : C) [has_binary_product (⊥_ C) X] :
  (initial_mul X).inv = initial.to _ :=
subsingleton.elim _ _
end

/-- If `C` has an initial object such that every morphism *to* it is an isomorphism, then `C`
has strict initial objects. -/
lemma has_strict_initial_object_of_initial_is_strict [has_initial C]
  (h : ∀ A (f : A ⟶ ⊥_ C), is_iso f) :
  has_strict_initial_object C :=
{ out := λ I A f hI,
  begin
    haveI := h A (f ≫ hI.to _),
    exact ⟨⟨hI.to _ ≫ inv (f ≫ hI.to ⊥_ C), by rw [←assoc, is_iso.hom_inv_id], hI.hom_ext _ _⟩⟩,
  end }

end limits
end category_theory
