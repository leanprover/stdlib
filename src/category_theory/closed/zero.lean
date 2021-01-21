/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.closed.cartesian
import category_theory.punit

/-!
# A cartesian closed category with zero object is trivial

A cartesian closed category with zero object is trivial: it is equivalent to the category with one
object and one morphism.

## References

* https://mathoverflow.net/a/136480

-/

universes v u

noncomputable theory

namespace category_theory

open category limits

variables {C : Type u} [category.{v} C]
variables [has_finite_products C] [cartesian_closed C]

/--
If a cartesian closed category has an initial object which is isomorphic to the terminal object,
then each homset has exactly one element.
-/
def unique_homset_of_initial_iso_terminal [has_initial C] (i : ⊥_ C ≅ ⊤_ C) (X Y : C) :
  unique (X ⟶ Y) :=
equiv.unique $
calc (X ⟶ Y) ≃ (X ⨯ ⊤_ C ⟶ Y) : iso.hom_congr (prod.right_unitor _).symm (iso.refl _)
         ... ≃ (X ⨯ ⊥_ C ⟶ Y) : iso.hom_congr (prod.map_iso (iso.refl _) i.symm) (iso.refl _)
         ... ≃ (⊥_ C ⟶ Y ^^ X) : (exp.adjunction _).hom_equiv _ _

local attribute [instance] has_zero_object.has_zero
local attribute [instance] has_zero_object.unique_to has_zero_object.unique_from

/-- If a cartesian closed category has a zero object, each homset has exactly one element. -/
def unique_homset_of_zero [has_zero_object C] (X Y : C) :
  unique (X ⟶ Y) :=
begin
  haveI : has_initial C := has_zero_object.has_initial,
  apply unique_homset_of_initial_iso_terminal _ X Y,
  refine ⟨default _, default (⊤_ C ⟶ 0) ≫ default _, _, _⟩;
  simp,
end

local attribute [instance] unique_homset_of_zero

/--
A cartesian closed category with a zero object is equivalent to the category with one object and
one morphism.
-/
def equiv_punit [has_zero_object C] : C ≌ discrete punit :=
equivalence.mk
  (functor.star C)
  (functor.from_punit 0)
  (nat_iso.of_components
    (λ X, { hom := default (X ⟶ 0),
            inv := default (0 ⟶ X) })
    (λ X Y f, dec_trivial))
  (functor.punit_ext _ _)

end category_theory
