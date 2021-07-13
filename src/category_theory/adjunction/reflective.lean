/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.preserves.shapes.binary_products
import category_theory.limits.preserves.shapes.terminal
import category_theory.adjunction.fully_faithful

/-!
# Reflective functors

Basic properties of reflective functors, especially those relating to their essential image.

Note properties of reflective functors relating to limits and colimits are included in
`category_theory.monad.limits`.
-/

universes v₁ v₂ v₃ u₁ u₂ u₃

noncomputable theory

namespace category_theory

open category adjunction limits

variables {C : Type u₁} {D : Type u₂} {E : Type u₃}
variables [category.{v₁} C] [category.{v₂} D] [category.{v₃} E]

/--
A functor is *reflective*, or *a reflective inclusion*, if it is fully faithful and right adjoint.
-/
class reflective (R : D ⥤ C) extends is_right_adjoint R, full R, faithful R.

variables {i : D ⥤ C}

/--
For a reflective functor `i` (with left adjoint `L`), with unit `η`, we have `η_iL = iL η`.
-/
-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
lemma unit_obj_eq_map_unit [reflective i] (X : C) :
  (of_right_adjoint i).unit.app (i.obj ((left_adjoint i).obj X))
    = i.map ((left_adjoint i).map ((of_right_adjoint i).unit.app X)) :=
begin
 rw [←cancel_mono (i.map ((of_right_adjoint i).counit.app ((left_adjoint i).obj X))),
     ←i.map_comp],
 simp,
end

/--
When restricted to objects in `D` given by `i : D ⥤ C`, the unit is an isomorphism. In other words,
`η_iX` is an isomorphism for any `X` in `D`.
More generally this applies to objects essentially in the reflective subcategory, see
`functor.ess_image.unit_iso`.
-/
instance is_iso_unit_obj [reflective i] {B : D} :
  is_iso ((of_right_adjoint i).unit.app (i.obj B)) :=
begin
  have : (of_right_adjoint i).unit.app (i.obj B) =
            inv (i.map ((of_right_adjoint i).counit.app B)),
  { rw ← comp_hom_eq_id,
    apply (of_right_adjoint i).right_triangle_components },
  rw this,
  exact is_iso.inv_is_iso,
end

/--
If `A` is essentially in the image of a reflective functor `i`, then `η_A` is an isomorphism.
This gives that the "witness" for `A` being in the essential image can instead be given as the
reflection of `A`, with the isomorphism as `η_A`.

(For any `B` in the reflective subcategory, we automatically have that `ε_B` is an iso.)
-/
lemma functor.ess_image.unit_is_iso [reflective i] {A : C} (h : A ∈ i.ess_image) :
  is_iso ((of_right_adjoint i).unit.app A) :=
begin
  suffices : (of_right_adjoint i).unit.app A =
                h.get_iso.inv ≫ (of_right_adjoint i).unit.app (i.obj h.witness) ≫
                  (left_adjoint i ⋙ i).map h.get_iso.hom,
  { rw this,
    apply_instance },
  rw ← nat_trans.naturality,
  simp,
end

/-- If `η_A` is an isomorphism, then `A` is in the essential image of `i`. -/
lemma mem_ess_image_of_unit_is_iso [is_right_adjoint i] (A : C)
  [is_iso ((of_right_adjoint i).unit.app A)] : A ∈ i.ess_image :=
⟨(left_adjoint i).obj A, ⟨(as_iso ((of_right_adjoint i).unit.app A)).symm⟩⟩

/-- If `η_A` is a split monomorphism, then `A` is in the reflective subcategory. -/
lemma mem_ess_image_of_unit_split_mono [reflective i] {A : C}
  [split_mono ((of_right_adjoint i).unit.app A)] : A ∈ i.ess_image :=
begin
  let η : 𝟭 C ⟶ left_adjoint i ⋙ i := (of_right_adjoint i).unit,
  haveI : is_iso (η.app (i.obj ((left_adjoint i).obj A))) := (i.obj_mem_ess_image _).unit_is_iso,
  have : epi (η.app A),
  { apply epi_of_epi (retraction (η.app A)) _,
    rw (show retraction _ ≫ η.app A = _, from η.naturality (retraction (η.app A))),
    apply epi_comp (η.app (i.obj ((left_adjoint i).obj A))) },
  resetI,
  haveI := is_iso_of_epi_of_split_mono (η.app A),
  exact mem_ess_image_of_unit_is_iso A,
end

/-- Composition of reflective functors. -/
instance reflective.comp (F : C ⥤ D) (G : D ⥤ E) [Fr : reflective F] [Gr : reflective G] :
  reflective (F ⋙ G) := { to_faithful := faithful.comp F G, }

/-- (Implementation) Auxiliary definition for `unit_comp_partial_bijective`. -/
def unit_comp_partial_bijective_aux [reflective i] (A : C) (B : D) :
  (A ⟶ i.obj B) ≃ (i.obj ((left_adjoint i).obj A) ⟶ i.obj B) :=
((adjunction.of_right_adjoint i).hom_equiv _ _).symm.trans (equiv_of_fully_faithful i)

/-- The description of the inverse of the bijection `unit_comp_partial_bijective_aux`. -/
lemma unit_comp_partial_bijective_aux_symm_apply [reflective i] {A : C} {B : D}
  (f : i.obj ((left_adjoint i).obj A) ⟶ i.obj B) :
  (unit_comp_partial_bijective_aux _ _).symm f = (of_right_adjoint i).unit.app A ≫ f :=
by simp [unit_comp_partial_bijective_aux, hom_equiv_unit]

/--
If `i` has a reflector `L`, then the function `(i.obj (L.obj A) ⟶ B) → (A ⟶ B)` given by
precomposing with `η.app A` is a bijection provided `B` is in the essential image of `i`.
That is, the function `λ (f : i.obj (L.obj A) ⟶ B), η.app A ≫ f` is bijective, as long as `B` is in
the essential image of `i`.
This definition gives an equivalence: the key property that the inverse can be described
nicely is shown in `unit_comp_partial_bijective_symm_apply`.

This establishes there is a natural bijection `(A ⟶ B) ≃ (i.obj (L.obj A) ⟶ B)`. In other words,
from the point of view of objects in `D`, `A` and `i.obj (L.obj A)` look the same: specifically
that `η.app A` is an isomorphism.
-/
def unit_comp_partial_bijective [reflective i] (A : C) {B : C} (hB : B ∈ i.ess_image) :
  (A ⟶ B) ≃ (i.obj ((left_adjoint i).obj A) ⟶ B) :=
calc (A ⟶ B) ≃ (A ⟶ i.obj hB.witness) : iso.hom_congr (iso.refl _) hB.get_iso.symm
     ...     ≃ (i.obj _ ⟶ i.obj hB.witness) : unit_comp_partial_bijective_aux _ _
     ...     ≃ (i.obj ((left_adjoint i).obj A) ⟶ B) : iso.hom_congr (iso.refl _) hB.get_iso

@[simp]
lemma unit_comp_partial_bijective_symm_apply [reflective i] (A : C) {B : C}
  (hB : B ∈ i.ess_image) (f) :
  (unit_comp_partial_bijective A hB).symm f = (of_right_adjoint i).unit.app A ≫ f :=
by simp [unit_comp_partial_bijective, unit_comp_partial_bijective_aux_symm_apply]

lemma unit_comp_partial_bijective_symm_natural [reflective i] (A : C) {B B' : C} (h : B ⟶ B')
  (hB : B ∈ i.ess_image) (hB' : B' ∈ i.ess_image) (f : i.obj ((left_adjoint i).obj A) ⟶ B) :
  (unit_comp_partial_bijective A hB').symm (f ≫ h) =
    (unit_comp_partial_bijective A hB).symm f ≫ h :=
by simp

lemma unit_comp_partial_bijective_natural [reflective i] (A : C) {B B' : C} (h : B ⟶ B')
  (hB : B ∈ i.ess_image) (hB' : B' ∈ i.ess_image) (f : A ⟶ B) :
  (unit_comp_partial_bijective A hB') (f ≫ h) = unit_comp_partial_bijective A hB f ≫ h :=
by rw [←equiv.eq_symm_apply, unit_comp_partial_bijective_symm_natural A h, equiv.symm_apply_apply]

end category_theory
