/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.sheaf_condition.equalizer_products

/-!
# Sheaves

We define sheaves on a topological space, with values in an arbitrary category with products.

The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i ⊓ U j)`.

We provide the instance `category (sheaf C X)` as the full subcategory of presheaves,
and the fully faithful functor `sheaf.forget : sheaf C X ⥤ presheaf C X`.

## Equivalent conditions

While the "official" definition is in terms of an equalizer diagram,
in `src/topology/sheaves/sheaf_condition/pairwise_intersections.lean`
and in `src/topology/sheaves/sheaf_condition/open_le_cover.lean`
we provide two equivalent conditions (and prove they are equivalent).

The first is that `F.obj U` is the limit point of the diagram consisting of all the `F.obj (U i)`
and `F.obj (U i ⊓ U j)`.
(That is, we explode the equalizer of two products out into its component pieces.)

The second is that `F.obj U` is the limit point of the diagram constisting of all the `F.obj V`,
for those `V : opens X` such that `V ≤ U i` for some `i`.
(This condition is particularly easy to state, and perhaps should become the "official" definition.)

-/

universes v u

noncomputable theory

open category_theory
open category_theory.limits
open topological_space
open opposite
open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C] [has_products C]
variables {X : Top.{v}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

namespace presheaf

open sheaf_condition_equalizer_products

/--
The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
-/
-- One might prefer to work with sets of opens, rather than indexed families,
-- which would reduce the universe level here to `max u v`.
-- However as it's a subsingleton the universe level doesn't matter much.
@[derive subsingleton]
def sheaf_condition (F : presheaf C X) : Type (max u (v+1)) :=
Π ⦃ι : Type v⦄ (U : ι → opens X), is_limit (sheaf_condition_equalizer_products.fork F U)

/--
The presheaf valued in `punit` over any topological space is a sheaf.
-/
def sheaf_condition_punit (F : presheaf (category_theory.discrete punit) X) :
  sheaf_condition F :=
λ ι U, punit_cone_is_limit

-- Let's construct a trivial example, to keep the inhabited linter happy.
instance sheaf_condition_inhabited (F : presheaf (category_theory.discrete punit) X) :
  inhabited (sheaf_condition F) := ⟨sheaf_condition_punit F⟩

/--
Transfer the sheaf condition across an isomorphism of presheaves.
-/
def sheaf_condition_equiv_of_iso {F G : presheaf C X} (α : F ≅ G) :
  sheaf_condition F ≃ sheaf_condition G :=
equiv_of_subsingleton_of_subsingleton
(λ c ι U, is_limit.of_iso_limit
  ((is_limit.postcompose_inv_equiv _ _).symm (c U)) (sheaf_condition_equalizer_products.fork.iso_of_iso U α.symm).symm)
(λ c ι U, is_limit.of_iso_limit
  ((is_limit.postcompose_inv_equiv _ _).symm (c U)) (sheaf_condition_equalizer_products.fork.iso_of_iso U α).symm)

end presheaf

variables (C X)

/--
A `sheaf C X` is a presheaf of objects from `C` over a (bundled) topological space `X`,
satisfying the sheaf condition.
-/
structure sheaf :=
(presheaf : presheaf C X)
(sheaf_condition : presheaf.sheaf_condition)

instance : category (sheaf C X) := induced_category.category sheaf.presheaf

-- Let's construct a trivial example, to keep the inhabited linter happy.
instance sheaf_inhabited : inhabited (sheaf (category_theory.discrete punit) X) :=
⟨{ presheaf := functor.star _, sheaf_condition := default _ }⟩

namespace sheaf

/--
The forgetful functor from sheaves to presheaves.
-/
@[derive [full, faithful]]
def forget : Top.sheaf C X ⥤ Top.presheaf C X := induced_functor sheaf.presheaf

end sheaf

end Top
