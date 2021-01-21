/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.kernels

/-!
# The morphism from `image f` to `kernel g` when `f ≫ g = 0`

We define the map, as the lift of `image.ι f` to `kernel g`,
and check some basic properties:

* this map is a monomorphism
* given `A --0--> B --g--> C`, where `[mono g]`, this map is an epimorphism
* given `A --f--> B --0--> C`, where `[epi f]`, this map is an epimorphism

In later files, we define the homology of complex as the cokernel of this map,
and say a complex is exact at a point if this map is an epimorphism.
-/

universes v u

open category_theory
open category_theory.limits

variables {V : Type u} [category.{v} V] [has_zero_morphisms V]

namespace category_theory

/-!
At this point we assume that we have all images, and all equalizers.
We need to assume all equalizers, not just kernels, so that
`factor_thru_image` is an epimorphism.
-/
variables [has_images V] [has_equalizers V]
variables {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

/--
The morphism from `image f` to `kernel g` when `f ≫ g = 0`.
-/
noncomputable
abbreviation image_to_kernel_map (w : f ≫ g = 0) :
  image f ⟶ kernel g :=
kernel.lift g (image.ι f) $ (cancel_epi (factor_thru_image f)).1 $ by simp [w]

@[simp]
lemma image_to_kernel_map_zero_left [has_zero_object V] {w} :
  image_to_kernel_map (0 : A ⟶ B) g w = 0 :=
by { delta image_to_kernel_map, simp }

lemma image_to_kernel_map_zero_right {w} :
  image_to_kernel_map f (0 : B ⟶ C) w = image.ι f ≫ inv (kernel.ι (0 : B ⟶ C)) :=
by { ext, simp }

lemma image_to_kernel_map_comp_right {D : V} (h : C ⟶ D) (w : f ≫ g = 0) :
  image_to_kernel_map f (g ≫ h) (by simp [reassoc_of w]) =
    image_to_kernel_map f g w ≫ kernel.lift (g ≫ h) (kernel.ι g) (by simp) :=
by { ext, simp }

lemma image_to_kernel_map_comp_left {Z : V} (h : Z ⟶ A) (w : f ≫ g = 0) :
  image_to_kernel_map (h ≫ f) g (by simp [w]) = image.pre_comp h f ≫ image_to_kernel_map f g w :=
by { ext, simp }

@[simp]
lemma image_to_kernel_map_comp_iso {D : V} (h : C ⟶ D) [is_iso h] (w) :
  image_to_kernel_map f (g ≫ h) w =
  image_to_kernel_map f g ((cancel_mono h).mp (by simpa using w : (f ≫ g) ≫ h = 0 ≫ h)) ≫
    (kernel_comp_is_iso g h).inv :=
by { ext, simp, }

@[simp]
lemma image_to_kernel_map_iso_comp {Z : V} (h : Z ⟶ A) [is_iso h] (w) :
  image_to_kernel_map (h ≫ f) g w =
  image.pre_comp h f ≫
    image_to_kernel_map f g ((cancel_epi h).mp (by simpa using w : h ≫ f ≫ g = h ≫ 0)) :=
by { ext, simp, }

@[simp]
lemma image_to_kernel_map_comp_hom_inv_comp {Z : V} {i : B ≅ Z} (w) :
  image_to_kernel_map (f ≫ i.hom) (i.inv ≫ g) w =
  (image.post_comp_is_iso f i.hom).inv ≫ image_to_kernel_map f g (by simpa using w) ≫
    (kernel_is_iso_comp i.inv g).inv :=
by { ext, simp }

local attribute [instance] has_zero_object.has_zero

/--
`image_to_kernel_map` for `A --0--> B --g--> C`, where `[mono g]` is an epi
(i.e. the sequence is exact at `B`).
-/
lemma image_to_kernel_map_epi_of_zero_of_mono [mono g] [has_zero_object V] :
  epi (image_to_kernel_map (0 : A ⟶ B) g (by simp)) :=
epi_of_target_iso_zero _ (kernel.of_mono g)

/--
`image_to_kernel_map` for `A --f--> B --0--> C`, where `[epi g]` is an epi
(i.e. the sequence is exact at `B`).
-/
lemma image_to_kernel_map_epi_of_epi_of_zero [epi f] :
  epi (image_to_kernel_map f (0 : B ⟶ C) (by simp)) :=
begin
  simp only [image_to_kernel_map_zero_right],
  haveI := epi_image_of_epi f,
  apply epi_comp,
end

end category_theory
