/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import topology.sheaves.sheaf
import category_theory.category.pairwise

/-!
# Equivalent formulations of the sheaf condition

We give an equivalent formulation of the sheaf condition.

Given any indexed type `ι`, we define `overlap ι`,
a category with objects corresponding to
* individual open sets, `single i`, and
* intersections of pairs of open sets, `pair i j`,
with morphisms from `pair i j` to both `single i` and `single j`.

Any open cover `U : ι → opens X` provides a functor `diagram U : overlap ι ⥤ (opens X)ᵒᵖ`.

There is a canonical cone over this functor, `cone U`, whose cone point is `supr U`,
and in fact this is a limit cone.

A presheaf `F : presheaf C X` is a sheaf precisely if it preserves this limit.
We express this in two equivalent ways, as
* `is_limit (F.map_cone (cone U))`, or
* `preserves_limit (diagram U) F`
-/

noncomputable theory

universes v u

open topological_space
open Top
open opposite
open category_theory
open category_theory.limits

namespace Top.presheaf

variables {X : Top.{v}}

variables {C : Type u} [category.{v} C]

/--
An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`sheaf_condition_equiv_sheaf_condition_pairwise_intersections`).

A presheaf is a sheaf if `F` sends the cone `(pairwise.cocone U).op` to a limit cone.
(Recall `pairwise.cocone U`, has cone point `supr U`, mapping down to the `U i` and the `U i ⊓ U j`.)
-/
@[derive subsingleton, nolint has_inhabited_instance]
def sheaf_condition_pairwise_intersections (F : presheaf C X) : Type (max u (v+1)) :=
Π ⦃ι : Type v⦄ (U : ι → opens X), is_limit (F.map_cone (pairwise.cocone U).op)

/--
An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`sheaf_condition_equiv_sheaf_condition_preserves_limit_pairwise_intersections`).

A presheaf is a sheaf if `F` preserves the limit of `pairwise.diagram U`.
(Recall `pairwise.diagram U` is the diagram consisting of the pairwise intersections
`U i ⊓ U j` mapping into the open sets `U i`. This diagram has limit `supr U`.)
-/
@[derive subsingleton, nolint has_inhabited_instance]
def sheaf_condition_preserves_limit_pairwise_intersections
  (F : presheaf C X) : Type (max u (v+1)) :=
Π ⦃ι : Type v⦄ (U : ι → opens X), preserves_limit (pairwise.diagram U).op F

/-!
The remainder of this file shows that these conditions are equivalent
to the usual sheaf condition.
-/

variables [has_products C]

namespace sheaf_condition_pairwise_intersections

open category_theory.pairwise category_theory.pairwise.hom
open sheaf_condition_equalizer_products

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_functor_obj (F : presheaf C X)
  ⦃ι : Type v⦄ (U : ι → opens ↥X) (c : limits.cone ((diagram U).op ⋙ F)) :
  limits.cone (sheaf_condition_equalizer_products.diagram F U) :=
{ X := c.X,
  π :=
  { app := λ Z,
      walking_parallel_pair.cases_on Z
        (pi.lift (λ (i : ι), c.π.app (op (single i))))
        (pi.lift (λ (b : ι × ι), c.π.app (op (pair b.1 b.2)))),
    naturality' := λ Y Z f,
    begin
      cases Y; cases Z; cases f,
      { ext i, dsimp,
        simp only [limit.lift_π, category.id_comp, fan.mk_π_app, category_theory.functor.map_id, category.assoc],
        dsimp,
        simp only [limit.lift_π, category.id_comp, fan.mk_π_app], },
      { ext ⟨i, j⟩, dsimp [sheaf_condition_equalizer_products.left_res],
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc],
        have h := c.π.naturality (has_hom.hom.op (hom.left i j)),
        dsimp at h,
        simpa using h, },
      { ext ⟨i, j⟩, dsimp [sheaf_condition_equalizer_products.right_res],
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc],
        have h := c.π.naturality (has_hom.hom.op (hom.right i j)),
        dsimp at h,
        simpa using h,  },
      { ext i, dsimp,
        simp only [limit.lift_π, category.id_comp, fan.mk_π_app, category_theory.functor.map_id, category.assoc],
        dsimp,
        simp only [limit.lift_π, category.id_comp, fan.mk_π_app], },
    end, }, }

section
local attribute [tidy] tactic.case_bash

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_functor (F : presheaf C X)
  ⦃ι : Type v⦄ (U : ι → opens ↥X) :
  limits.cone ((diagram U).op ⋙ F) ⥤ limits.cone (sheaf_condition_equalizer_products.diagram F U) :=
{ obj := λ c, cone_equiv_functor_obj F U c,
  map := λ c c' f,
  { hom := f.hom, }, }.

end

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_inverse_obj (F : presheaf C X)
  ⦃ι : Type v⦄ (U : ι → opens ↥X)
  (c : limits.cone (sheaf_condition_equalizer_products.diagram F U)) :
  limits.cone ((diagram U).op ⋙ F) :=
{ X := c.X,
  π :=
  { app :=
    begin
      intro x,
      op_induction x,
      rcases x with (⟨i⟩|⟨i,j⟩),
      { exact c.π.app (walking_parallel_pair.zero) ≫ pi.π _ i, },
      { exact c.π.app (walking_parallel_pair.one) ≫ pi.π _ (i, j), }
    end,
    naturality' :=
    begin
      -- Unfortunately `op_induction` isn't up to the task here, and we need to use `generalize`.
      intros x y f,
      have ex : x = op (unop x) := rfl,
      have ey : y = op (unop y) := rfl,
      revert ex ey,
      generalize : unop x = x',
      generalize : unop y = y',
      rintro rfl rfl,
      have ef : f = f.unop.op := rfl,
      revert ef,
      generalize : f.unop = f',
      rintro rfl,
      rcases x' with ⟨i⟩|⟨⟩; rcases y' with ⟨⟩|⟨j,j⟩; rcases f' with ⟨⟩,
      { dsimp, erw [F.map_id], simp, },
      { dsimp, simp only [category.id_comp, category.assoc],
        have h := c.π.naturality (walking_parallel_pair_hom.left),
        dsimp [sheaf_condition_equalizer_products.left_res] at h,
        simp only [category.id_comp] at h,
        have h' := h =≫ pi.π _ (i, j),
        rw h',
        simp,
        refl, },
      { dsimp, simp only [category.id_comp, category.assoc],
        have h := c.π.naturality (walking_parallel_pair_hom.right),
        dsimp [sheaf_condition_equalizer_products.right_res] at h,
        simp only [category.id_comp] at h,
        have h' := h =≫ pi.π _ (j, i),
        rw h',
        simp,
        refl, },
      { dsimp, erw [F.map_id], simp, },
    end, }, }

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_inverse (F : presheaf C X)
  ⦃ι : Type v⦄ (U : ι → opens ↥X) :
  limits.cone (sheaf_condition_equalizer_products.diagram F U) ⥤ limits.cone ((diagram U).op ⋙ F) :=
{ obj := λ c, cone_equiv_inverse_obj F U c,
  map := λ c c' f,
  { hom := f.hom,
    w' :=
    begin
      intro x,
      op_induction x,
      rcases x with (⟨i⟩|⟨i,j⟩),
      { dsimp,
        rw [←(f.w walking_parallel_pair.zero), category.assoc], },
      { dsimp,
        rw [←(f.w walking_parallel_pair.one), category.assoc], },
    end }, }.

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_unit_iso_app (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens ↥X)
  (c : cone ((diagram U).op ⋙ F)) :
  (𝟭 (cone ((diagram U).op ⋙ F))).obj c ≅
    (cone_equiv_functor F U ⋙ cone_equiv_inverse F U).obj c :=
{ hom :=
  { hom := 𝟙 _,
    w' := λ j, begin op_induction j, rcases j; tidy, end, },
  inv :=
  { hom := 𝟙 _,
    w' := λ j, begin op_induction j, rcases j; tidy, end }}

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_unit_iso (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X) :
  𝟭 (limits.cone ((diagram U).op ⋙ F)) ≅
    cone_equiv_functor F U ⋙ cone_equiv_inverse F U :=
nat_iso.of_components (cone_equiv_unit_iso_app F U) (by tidy)

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_counit_iso (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X) :
  cone_equiv_inverse F U ⋙ cone_equiv_functor F U ≅
    𝟭 (limits.cone (sheaf_condition_equalizer_products.diagram F U)) :=
nat_iso.of_components (λ c,
{ hom :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨_|_⟩,
      { ext, dsimp, simp, },
      { ext ⟨i,j⟩, dsimp, simp, },
    end },
  inv :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨_|_⟩,
      { ext, dsimp, simp, },
      { ext ⟨i,j⟩, dsimp, simp, },
    end, }}) (by tidy)

/--
Cones over `diagram U ⋙ F` are the same as a cones over the usual sheaf condition equalizer diagram.
-/
@[simps]
def cone_equiv (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X) :
  limits.cone ((diagram U).op ⋙ F) ≌ limits.cone (sheaf_condition_equalizer_products.diagram F U) :=
{ functor := cone_equiv_functor F U,
  inverse := cone_equiv_inverse F U,
  unit_iso := cone_equiv_unit_iso F U,
  counit_iso := cone_equiv_counit_iso F U, }

local attribute [reducible]
  sheaf_condition_equalizer_products.res
  sheaf_condition_equalizer_products.left_res

/--
If `sheaf_condition_equalizer_products.fork` is an equalizer,
then `F.map_cone (cone U)` is a limit cone.
-/
def is_limit_map_cone_of_is_limit_sheaf_condition_fork
  (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X)
  (P : is_limit (sheaf_condition_equalizer_products.fork F U)) :
  is_limit (F.map_cone (cocone U).op) :=
is_limit.of_iso_limit ((is_limit.of_cone_equiv (cone_equiv F U).symm).symm P)
{ hom :=
  { hom := 𝟙 _,
    w' :=
    begin
      intro x,
      op_induction x,
      rcases x with ⟨⟩,
      { dsimp, simp, refl, },
      { dsimp,
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc],
        rw ←F.map_comp,
        refl, }
    end },
  inv :=
  { hom := 𝟙 _,
    w' :=
    begin
      intro x,
      op_induction x,
      rcases x with ⟨⟩,
      { dsimp, simp, refl, },
      { dsimp,
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc],
        rw ←F.map_comp,
        refl, }
    end }, }

/--
If `F.map_cone (cone U)` is a limit cone,
then `sheaf_condition_equalizer_products.fork` is an equalizer.
-/
def is_limit_sheaf_condition_fork_of_is_limit_map_cone
  (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X)
  (Q : is_limit (F.map_cone (cocone U).op)) :
  is_limit (sheaf_condition_equalizer_products.fork F U) :=
is_limit.of_iso_limit ((is_limit.of_cone_equiv (cone_equiv F U)).symm Q)
{ hom :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨⟩,
      { dsimp, simp, refl, },
      { dsimp, ext ⟨i, j⟩,
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc],
        rw ←F.map_comp,
        refl, }
    end },
  inv :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨⟩,
      { dsimp, simp, refl, },
      { dsimp, ext ⟨i, j⟩,
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc],
        rw ←F.map_comp,
        refl, }
    end }, }


end sheaf_condition_pairwise_intersections

open sheaf_condition_pairwise_intersections

/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
def sheaf_condition_equiv_sheaf_condition_pairwise_intersections (F : presheaf C X) :
  F.sheaf_condition ≃ F.sheaf_condition_pairwise_intersections :=
equiv.Pi_congr_right (λ i, equiv.Pi_congr_right (λ U,
  equiv_of_subsingleton_of_subsingleton
    (is_limit_map_cone_of_is_limit_sheaf_condition_fork F U)
    (is_limit_sheaf_condition_fork_of_is_limit_map_cone F U)))

/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of the presheaf preserving the limit of the diagram
consisting of the `U i` and `U i ⊓ U j`.
-/
def sheaf_condition_equiv_sheaf_condition_preserves_limit_pairwise_intersections
(F : presheaf C X) :
  F.sheaf_condition ≃ F.sheaf_condition_preserves_limit_pairwise_intersections :=
equiv.trans
  (sheaf_condition_equiv_sheaf_condition_pairwise_intersections F)
  (equiv.Pi_congr_right (λ i, equiv.Pi_congr_right (λ U,
     equiv_of_subsingleton_of_subsingleton
       (λ P, preserves_limit_of_preserves_limit_cone (pairwise.cocone_is_colimit U).op P)
       (by { introI, exact preserves_limit.preserves (pairwise.cocone_is_colimit U).op }))))

end Top.presheaf
