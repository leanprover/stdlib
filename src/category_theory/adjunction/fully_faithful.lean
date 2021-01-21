/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.conj
import category_theory.yoneda

open category_theory

namespace category_theory
universes v₁ v₂ u₁ u₂

open category
open opposite

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]
variables {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)

/--
If the left adjoint is fully faithful, then the unit is an isomorphism.

See
* Lemma 4.5.13 from [Riehl][riehl2017]
* https://math.stackexchange.com/a/2727177
* https://stacks.math.columbia.edu/tag/07RB (we only prove the forward direction!)
-/
instance unit_is_iso_of_L_fully_faithful [full L] [faithful L] : is_iso (adjunction.unit h) :=
@nat_iso.is_iso_of_is_iso_app _ _ _ _ _ _ (adjunction.unit h) $ λ X,
@yoneda.is_iso _ _ _ _ ((adjunction.unit h).app X)
{ inv := { app := λ Y f, L.preimage ((h.hom_equiv (unop Y) (L.obj X)).symm f) },
  inv_hom_id' :=
  begin
    ext, dsimp,
    simp only [adjunction.hom_equiv_counit, preimage_comp, preimage_map, category.assoc],
    rw ←h.unit_naturality,
    simp,
  end,
  hom_inv_id' :=
  begin
    ext, dsimp,
    apply L.map_injective,
    simp,
  end }.

/--
If the right adjoint is fully faithful, then the counit is an isomorphism.

See https://stacks.math.columbia.edu/tag/07RB (we only prove the forward direction!)
-/
instance counit_is_iso_of_R_fully_faithful [full R] [faithful R] : is_iso (adjunction.counit h) :=
@nat_iso.is_iso_of_is_iso_app _ _ _ _ _ _ (adjunction.counit h) $ λ X,
@is_iso_of_op _ _ _ _ _ $
@coyoneda.is_iso _ _ _ _ ((adjunction.counit h).app X).op
{ inv := { app := λ Y f, R.preimage ((h.hom_equiv (R.obj X) Y) f) },
  inv_hom_id' :=
  begin
    ext, dsimp,
    simp only [adjunction.hom_equiv_unit, preimage_comp, preimage_map],
    rw ←h.counit_naturality,
    simp,
  end,
  hom_inv_id' :=
  begin
    ext, dsimp,
    apply R.map_injective,
    simp,
  end }

-- TODO also prove the converses?
-- def L_full_of_unit_is_iso [is_iso (adjunction.unit h)] : full L := sorry
-- def L_faithful_of_unit_is_iso [is_iso (adjunction.unit h)] : faithful L := sorry
-- def R_full_of_counit_is_iso [is_iso (adjunction.counit h)] : full R := sorry
-- def R_faithful_of_counit_is_iso [is_iso (adjunction.counit h)] : faithful R := sorry

-- TODO also do the statements from Riehl 4.5.13 for full and faithful separately?

universes v₃ v₄ u₃ u₄

variables {C' : Type u₃} [category.{v₃} C']
variables {D' : Type u₄} [category.{v₄} D']

-- TODO: This needs some lemmas describing the produced adjunction, probably in terms of `adj`,
-- `iC` and `iD`.
/--
If `C` is a full subcategory of `C'` and `D` is a full subcategory of `D'`, then we can restrict
an adjunction `L' ⊣ R'` where `L' : C' ⥤ D'` and `R' : D' ⥤ C'` to `C` and `D`.
The construction here is slightly more general, in that `C` is required only to have a full and
faithful "inclusion" functor `iC : C ⥤ C'` (and similarly `iD : D ⥤ D'`) which commute (up to
natural isomorphism) with the proposed restrictions.
-/
def adjunction.restrict_fully_faithful (iC : C ⥤ C') (iD : D ⥤ D') {L' : C' ⥤ D'} {R' : D' ⥤ C'}
  (adj : L' ⊣ R') {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)
  [full iC] [faithful iC] [full iD] [faithful iD] :
  L ⊣ R :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  calc (L.obj X ⟶ Y) ≃ (iD.obj (L.obj X) ⟶ iD.obj Y) : equiv_of_fully_faithful iD
       ... ≃ (L'.obj (iC.obj X) ⟶ iD.obj Y) : iso.hom_congr (comm1.symm.app X) (iso.refl _)
       ... ≃ (iC.obj X ⟶ R'.obj (iD.obj Y)) : adj.hom_equiv _ _
       ... ≃ (iC.obj X ⟶ iC.obj (R.obj Y)) : iso.hom_congr (iso.refl _) (comm2.app Y)
       ... ≃ (X ⟶ R.obj Y) : (equiv_of_fully_faithful iC).symm,
  hom_equiv_naturality_left_symm' := λ X' X Y f g,
  begin
    apply iD.map_injective,
    simpa using (comm1.inv.naturality_assoc f _).symm,
  end,
  hom_equiv_naturality_right' := λ X Y' Y f g,
  begin
    apply iC.map_injective,
    suffices : R'.map (iD.map g) ≫ comm2.hom.app Y = comm2.hom.app Y' ≫ iC.map (R.map g),
      simp [this],
    apply comm2.hom.naturality g,
  end }


end category_theory
