/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.full_subcategory

/-!
# Essential image of a functor

The essential image `ess_image` of a functor consists of the objects in the target category which
are isomorphic to an object in the image of the object function.
This, for instance, allows us to talk about objects belonging to a subcategory expressed as a
functor rather than a subtype, preserving the principle of equivalence. For example this lets us
define exponential ideals.

The essential image can also be seen as a subcategory of the target category, and witnesses that
a functor decomposes into a essentially surjective functor and a fully faithful functor.
(TODO: show that this decomposition forms an orthogonal factorisation system).
-/
universes v₁ v₂ u₁ u₂

noncomputable theory

namespace category_theory

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] {F : C ⥤ D}

namespace functor

/--
The essential image of a functor `F` consists of those objects in the target category which are
isomorphic to an object in the image of the function `F.obj`. In other words, this is the closure
under isomorphism of the function `F.obj`.
This is the "non-evil" way of describing the image of a functor.
-/
def ess_image (F : C ⥤ D) : set D := λ Y, ∃ (X : C), nonempty (F.obj X ≅ Y)

/-- Get the witnessing object that `Y` is in the subcategory given by `F`. -/
def ess_image.witness {Y : D} (h : Y ∈ F.ess_image) : C := h.some

/-- Extract the isomorphism between `F.obj h.witness` and `Y` itself. -/
def ess_image.get_iso {Y : D} (h : Y ∈ F.ess_image) : F.obj h.witness ≅ Y :=
classical.choice h.some_spec

/-- Being in the essential image is a "hygenic" property: it is preserved under isomorphism. -/
lemma ess_image.of_iso {Y Y' : D} (h : Y ≅ Y') (hY : Y ∈ ess_image F) :
  Y' ∈ ess_image F :=
hY.imp (λ B, nonempty.map (≪≫ h))

/--
If `Y` is in the essential image of `F` then it is in the essential image of `F'` as long as
`F ≅ F'`.
-/
lemma ess_image.of_nat_iso {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : Y ∈ ess_image F) :
  Y ∈ ess_image F' :=
hY.imp (λ X, nonempty.map (λ t, h.symm.app X ≪≫ t))

/-- Isomorphic functors have equal essential images. -/
lemma ess_image_eq_of_nat_iso {F' : C ⥤ D} (h : F ≅ F') :
  ess_image F = ess_image F' :=
set.ext $ λ A, ⟨ess_image.of_nat_iso h, ess_image.of_nat_iso h.symm⟩

/-- An object in the image is in the essential image. -/
lemma obj_mem_ess_image (F : D ⥤ C) (Y : D) : F.obj Y ∈ ess_image F := ⟨Y, ⟨iso.refl _⟩⟩

instance : category F.ess_image := category_theory.full_subcategory _

/-- The essential image as a subcategory has a fully faithful inclusion into the target category. -/
@[derive [full, faithful], simps]
def ess_image_inclusion (F : C ⥤ D) : F.ess_image ⥤ D :=
full_subcategory_inclusion _

/--
Given a functor `F : C ⥤ D`, we have an (essentially surjective) functor from `C` to the essential
image of `F`.
-/
@[simps]
def to_ess_image (F : C ⥤ D) : C ⥤ F.ess_image :=
{ obj := λ X, ⟨_, obj_mem_ess_image _ X⟩,
  map := λ X Y f, (ess_image_inclusion F).preimage (F.map f) }

/--
The functor `F` factorises through its essential image, where the first functor is essentially
surjective and the second is fully faithful.
-/
@[simps]
def to_ess_image_comp_essential_image_inclusion :
  F.to_ess_image ⋙ F.ess_image_inclusion ≅ F :=
nat_iso.of_components (λ X, iso.refl _) (by tidy)

end functor

/--
A functor `F : C ⥤ D` is essentially surjective if every object of `D` is in the essential image
of `F`. In other words, for every `Y : D`, there is some `X : C` with `F.obj X ≅ Y`.

See https://stacks.math.columbia.edu/tag/001C.
-/
class ess_surj (F : C ⥤ D) : Prop :=
(mem_ess_image [] (Y : D) : Y ∈ F.ess_image)

instance : ess_surj F.to_ess_image :=
{ mem_ess_image := λ ⟨Y, hY⟩, ⟨_, ⟨⟨_, _, hY.get_iso.hom_inv_id, hY.get_iso.inv_hom_id⟩⟩⟩ }

variables (F) [ess_surj F]

/-- Given an essentially surjective functor, we can find a preimage for every object `Y` in the
    codomain. Applying the functor to this preimage will yield an object isomorphic to `Y`, see
    `obj_obj_preimage_iso`. -/
def functor.obj_preimage (Y : D) : C := (ess_surj.mem_ess_image F Y).witness
/-- Applying an essentially surjective functor to a preimage of `Y` yields an object that is
    isomorphic to `Y`. -/
def functor.obj_obj_preimage_iso (Y : D) : F.obj (F.obj_preimage Y) ≅ Y :=
(ess_surj.mem_ess_image F Y).get_iso

end category_theory
