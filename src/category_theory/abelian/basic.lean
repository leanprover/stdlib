/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import category_theory.limits.constructions.pullbacks
import category_theory.limits.shapes.biproducts
import category_theory.limits.shapes.images
import category_theory.abelian.non_preadditive

/-!
# Abelian categories

This file contains the definition and basic properties of abelian categories.

There are many definitions of abelian category. Our definition is as follows:
A category is called abelian if it is preadditive,
has a finite products, kernels and cokernels,
and if every monomorphism and epimorphism is normal.

It should be noted that if we also assume coproducts, then preadditivity is
actually a consequence of the other properties, as we show in
`non_preadditive_abelian.lean`. However, this fact is of little practical
relevance, since essentially all interesting abelian categories come with a
preadditive structure. In this way, by requiring preadditivity, we allow the
user to pass in the preadditive structure the specific category they are
working with has natively.

## Main definitions

* `abelian` is the type class indicating that a category is abelian. It extends `preadditive`.
* `abelian.image f` is `kernel (cokernel.π f)`, and
* `abelian.coimage f` is `cokernel (kernel.ι f)`.

## Main results

* In an abelian category, mono + epi = iso.
* If `f : X ⟶ Y`, then the map `factor_thru_image f : X ⟶ image f` is an epimorphism, and the map
  `factor_thru_coimage f : coimage f ⟶ Y` is a monomorphism.
* Factoring through the image and coimage is a strong epi-mono factorisation. This means that
  * every abelian category has images. We instantiated this in such a way that `abelian.image f` is
    definitionally equal to `limits.image f`, and
  * there is a canonical isomorphism `coimage_iso_image : coimage f ≅ image f` such that
    `coimage.π f ≫ (coimage_iso_image f).hom ≫ image.ι f = f`. The lemma stating this is called
    `full_image_factorisation`.
* Every epimorphism is a cokernel of its kernel. Every monomorphism is a kernel of its cokernel.
* The pullback of an epimorphism is an epimorphism. The pushout of a monomorphism is a monomorphism.
  (This is not to be confused with the fact that the pullback of a monomorphism is a monomorphism,
  which is true in any category).

## Implementation notes

The typeclass `abelian` does not extend `non_preadditive_abelian`,
to avoid having to deal with comparing the two `has_zero_morphisms` instances
(one from `preadditive` in `abelian`, and the other a field of `non_preadditive_abelian`).
As a consequence, at the beginning of this file we trivially build
a `non_preadditive_abelian` instance from an `abelian` instance,
and use this to restate a number of theorems,
in each case just reusing the proof from `non_preadditive_abelian.lean`.

We don't show this yet, but abelian categories are finitely complete and finitely cocomplete.
However, the limits we can construct at this level of generality will most likely be less nice than
the ones that can be created in specific applications. For this reason, we adopt the following
convention:

* If the statement of a theorem involves limits, the existence of these limits should be made an
  explicit typeclass parameter.
* If a limit only appears in a proof, but not in the statement of a theorem, the limit should not
  be a typeclass parameter, but instead be created using `abelian.has_pullbacks` or a similar
  definition.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
* [P. Aluffi, *Algebra: Chaper 0*][aluffi2016]

-/

noncomputable theory

open category_theory
open category_theory.preadditive
open category_theory.limits

universes v u

namespace category_theory

variables {C : Type u} [category.{v} C]

variables (C)

/--
A (preadditive) category `C` is called abelian if it has all finite products,
all kernels and cokernels, and if every monomorphism is the kernel of some morphism
and every epimorphism is the cokernel of some morphism.

(This definition implies the existence of zero objects:
finite products give a terminal object, and in a preadditive category
any terminal object is a zero object.)
-/
class abelian extends preadditive C :=
[has_finite_products : has_finite_products C]
[has_kernels : has_kernels C]
[has_cokernels : has_cokernels C]
(normal_mono : Π {X Y : C} (f : X ⟶ Y) [mono f], normal_mono f)
(normal_epi : Π {X Y : C} (f : X ⟶ Y) [epi f], normal_epi f)

attribute [instance, priority 100] abelian.has_finite_products
attribute [instance, priority 100] abelian.has_kernels abelian.has_cokernels

end category_theory

open category_theory

namespace category_theory.abelian
variables {C : Type u} [category.{v} C] [abelian C]

/-- An abelian category has finite biproducts. -/
@[priority 100]
instance has_finite_biproducts : has_finite_biproducts C :=
limits.has_finite_biproducts.of_has_finite_products

@[priority 100]
instance has_binary_biproducts : has_binary_biproducts C :=
limits.has_binary_biproducts_of_finite_biproducts _

@[priority 100]
instance has_zero_object : has_zero_object C :=
has_zero_object_of_has_initial_object

section to_non_preadditive_abelian

/-- Every abelian category is, in particular, `non_preadditive_abelian`. -/
def non_preadditive_abelian : non_preadditive_abelian C := { ..‹abelian C› }

end to_non_preadditive_abelian

section strong
local attribute [instance] abelian.normal_epi

/-- In an abelian category, every epimorphism is strong. -/
lemma strong_epi_of_epi {P Q : C} (f : P ⟶ Q) [epi f] : strong_epi f := by apply_instance

end strong

section mono_epi_iso
variables {X Y : C} (f : X ⟶ Y)

local attribute [instance] strong_epi_of_epi

/-- In an abelian category, a monomorphism which is also an epimorphism is an isomorphism. -/
lemma is_iso_of_mono_of_epi [mono f] [epi f] : is_iso f :=
is_iso_of_mono_of_strong_epi _

end mono_epi_iso

section factor
local attribute [instance] non_preadditive_abelian

variables {P Q : C} (f : P ⟶ Q)

section

lemma mono_of_zero_kernel (R : C)
  (l : is_limit (kernel_fork.of_ι (0 : R ⟶ P) (show 0 ≫ f = 0, by simp))) : mono f :=
non_preadditive_abelian.mono_of_zero_kernel _ _ l

lemma mono_of_kernel_ι_eq_zero (h : kernel.ι f = 0) : mono f :=
mono_of_kernel_zero h

lemma epi_of_zero_cokernel (R : C)
  (l : is_colimit (cokernel_cofork.of_π (0 : Q ⟶ R) (show f ≫ 0 = 0, by simp))) : epi f :=
non_preadditive_abelian.epi_of_zero_cokernel _ _ l

lemma epi_of_cokernel_π_eq_zero (h : cokernel.π f = 0) : epi f :=
begin
  apply epi_of_zero_cokernel _ (cokernel f),
  simp_rw ←h,
  exact is_colimit.of_iso_colimit (colimit.is_colimit (parallel_pair f 0)) (iso_of_π _)
end

end

namespace images

/-- The kernel of the cokernel of `f` is called the image of `f`. -/
protected abbreviation image : C := kernel (cokernel.π f)

/-- The inclusion of the image into the codomain. -/
protected abbreviation image.ι : images.image f ⟶ Q :=
kernel.ι (cokernel.π f)

/-- There is a canonical epimorphism `p : P ⟶ image f` for every `f`. -/
protected abbreviation factor_thru_image : P ⟶ images.image f :=
kernel.lift (cokernel.π f) f $ cokernel.condition f

/-- `f` factors through its image via the canonical morphism `p`. -/
@[simp, reassoc] protected lemma image.fac :
  images.factor_thru_image f ≫ image.ι f = f :=
kernel.lift_ι _ _ _

/-- The map `p : P ⟶ image f` is an epimorphism -/
instance : epi (images.factor_thru_image f) :=
show epi (non_preadditive_abelian.factor_thru_image f), by apply_instance

section
variables {f}

lemma image_ι_comp_eq_zero {R : C} {g : Q ⟶ R} (h : f ≫ g = 0) : images.image.ι f ≫ g = 0 :=
zero_of_epi_comp (images.factor_thru_image f) $ by simp [h]

end

instance mono_factor_thru_image [mono f] : mono (images.factor_thru_image f) :=
mono_of_mono_fac $ image.fac f

instance is_iso_factor_thru_image [mono f] : is_iso (images.factor_thru_image f) :=
is_iso_of_mono_of_epi _

/-- Factoring through the image is a strong epi-mono factorisation. -/
@[simps] def image_strong_epi_mono_factorisation : strong_epi_mono_factorisation f :=
{ I := images.image f,
  m := image.ι f,
  m_mono := by apply_instance,
  e := images.factor_thru_image f,
  e_strong_epi := strong_epi_of_epi _ }

end images

namespace coimages

/-- The cokernel of the kernel of `f` is called the coimage of `f`. -/
protected abbreviation coimage : C := cokernel (kernel.ι f)

/-- The projection onto the coimage. -/
protected abbreviation coimage.π : P ⟶ coimages.coimage f :=
cokernel.π (kernel.ι f)

/-- There is a canonical monomorphism `i : coimage f ⟶ Q`. -/
protected abbreviation factor_thru_coimage : coimages.coimage f ⟶ Q :=
cokernel.desc (kernel.ι f) f $ kernel.condition f

/-- `f` factors through its coimage via the canonical morphism `p`. -/
protected lemma coimage.fac : coimage.π f ≫ coimages.factor_thru_coimage f = f :=
cokernel.π_desc _ _ _

/-- The canonical morphism `i : coimage f ⟶ Q` is a monomorphism -/
instance : mono (coimages.factor_thru_coimage f) :=
show mono (non_preadditive_abelian.factor_thru_coimage f), by apply_instance

instance epi_factor_thru_coimage [epi f] : epi (coimages.factor_thru_coimage f) :=
epi_of_epi_fac $ coimage.fac f

instance is_iso_factor_thru_coimage [epi f] : is_iso (coimages.factor_thru_coimage f) :=
is_iso_of_mono_of_epi _

/-- Factoring through the coimage is a strong epi-mono factorisation. -/
@[simps] def coimage_strong_epi_mono_factorisation : strong_epi_mono_factorisation f :=
{ I := coimages.coimage f,
  m := coimages.factor_thru_coimage f,
  m_mono := by apply_instance,
  e := coimage.π f,
  e_strong_epi := strong_epi_of_epi _ }

end coimages

end factor

section has_strong_epi_mono_factorisations

/-- An abelian category has strong epi-mono factorisations. -/
@[priority 100] instance : has_strong_epi_mono_factorisations C :=
has_strong_epi_mono_factorisations.mk $ λ X Y f, images.image_strong_epi_mono_factorisation f

/- In particular, this means that it has well-behaved images. -/
example : has_images C := by apply_instance
example : has_image_maps C := by apply_instance

end has_strong_epi_mono_factorisations

section images
variables {X Y : C} (f : X ⟶ Y)

/-- There is a canonical isomorphism between the coimage and the image of a morphism. -/
abbreviation coimage_iso_image : coimages.coimage f ≅ images.image f :=
is_image.iso_ext (coimages.coimage_strong_epi_mono_factorisation f).to_mono_is_image
  (images.image_strong_epi_mono_factorisation f).to_mono_is_image

/-- There is a canonical isomorphism between the abelian image and the categorical image of a
    morphism. -/
abbreviation image_iso_image : images.image f ≅ image f :=
is_image.iso_ext (images.image_strong_epi_mono_factorisation f).to_mono_is_image (image.is_image f)

/-- There is a canonical isomorphism between the abelian coimage and the categorical image of a
    morphism. -/
abbreviation coimage_iso_image' : coimages.coimage f ≅ image f :=
is_image.iso_ext (coimages.coimage_strong_epi_mono_factorisation f).to_mono_is_image
  (image.is_image f)

lemma full_image_factorisation : coimages.coimage.π f ≫ (coimage_iso_image f).hom ≫
  images.image.ι f = f :=
by rw [limits.is_image.iso_ext_hom,
  ←images.image_strong_epi_mono_factorisation_to_mono_factorisation_m, is_image.lift_fac,
  coimages.coimage_strong_epi_mono_factorisation_to_mono_factorisation_m, coimages.coimage.fac]

end images

section cokernel_of_kernel
variables {X Y : C} {f : X ⟶ Y}

local attribute [instance] non_preadditive_abelian

/-- In an abelian category, an epi is the cokernel of its kernel. More precisely:
    If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a cokernel
    of `fork.ι s`. -/
def epi_is_cokernel_of_kernel [epi f] (s : fork f 0) (h : is_limit s) :
  is_colimit (cokernel_cofork.of_π f (kernel_fork.condition s)) :=
non_preadditive_abelian.epi_is_cokernel_of_kernel s h

/-- In an abelian category, a mono is the kernel of its cokernel. More precisely:
    If `f` is a monomorphism and `s` is some colimit cokernel cocone on `f`, then `f` is a kernel
    of `cofork.π s`. -/
def mono_is_kernel_of_cokernel [mono f] (s : cofork f 0) (h : is_colimit s) :
  is_limit (kernel_fork.of_ι f (cokernel_cofork.condition s)) :=
non_preadditive_abelian.mono_is_kernel_of_cokernel s h

end cokernel_of_kernel

section

@[priority 100]
instance has_equalizers : has_equalizers C :=
preadditive.has_equalizers_of_has_kernels

/-- Any abelian category has pullbacks -/
@[priority 100]
instance has_pullbacks : has_pullbacks C :=
has_pullbacks_of_has_binary_products_of_has_equalizers C

end

section

@[priority 100]
instance has_coequalizers : has_coequalizers C :=
preadditive.has_coequalizers_of_has_cokernels

/-- Any abelian category has pushouts -/
@[priority 100]
instance has_pushouts : has_pushouts C :=
has_pushouts_of_has_binary_coproducts_of_has_coequalizers C

end

namespace pullback_to_biproduct_is_kernel
variables [limits.has_pullbacks C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

/-! This section contains a slightly technical result about pullbacks and biproducts.
    We will need it in the proof that the pullback of an epimorphism is an epimorpism. -/

/-- The canonical map `pullback f g ⟶ X ⊞ Y` -/
abbreviation pullback_to_biproduct : pullback f g ⟶ X ⊞ Y :=
biprod.lift pullback.fst pullback.snd

/-- The canonical map `pullback f g ⟶ X ⊞ Y` induces a kernel cone on the map
    `biproduct X Y ⟶ Z` induced by `f` and `g`. A slightly more intuitive way to think of
    this may be that it induces an equalizer fork on the maps induced by `(f, 0)` and
    `(0, g)`. -/
abbreviation pullback_to_biproduct_fork : kernel_fork (biprod.desc f (-g)) :=
kernel_fork.of_ι (pullback_to_biproduct f g) $
by rw [biprod.lift_desc, comp_neg, pullback.condition, add_right_neg]

/-- The canonical map `pullback f g ⟶ X ⊞ Y` is a kernel of the map induced by
    `(f, -g)`. -/
def is_limit_pullback_to_biproduct : is_limit (pullback_to_biproduct_fork f g) :=
fork.is_limit.mk _
  (λ s, pullback.lift (fork.ι s ≫ biprod.fst) (fork.ι s ≫ biprod.snd) $
    sub_eq_zero.1 $ by rw [category.assoc, category.assoc, ←comp_sub, sub_eq_add_neg, ←comp_neg,
      ←biprod.desc_eq, kernel_fork.condition s])
  (λ s,
  begin
    ext; rw [fork.ι_of_ι, category.assoc],
    { rw [biprod.lift_fst, pullback.lift_fst] },
    { rw [biprod.lift_snd, pullback.lift_snd] }
  end)
  (λ s m h, by ext; simp [fork.ι_eq_app_zero, ←h walking_parallel_pair.zero])

end pullback_to_biproduct_is_kernel

namespace biproduct_to_pushout_is_cokernel
variables [limits.has_pushouts C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

/-- The canonical map `Y ⊞ Z ⟶ pushout f g` -/
abbreviation biproduct_to_pushout : Y ⊞ Z ⟶ pushout f g :=
biprod.desc pushout.inl pushout.inr

/-- The canonical map `Y ⊞ Z ⟶ pushout f g` induces a cokernel cofork on the map
    `X ⟶ Y ⊞ Z` induced by `f` and `-g`. -/
abbreviation biproduct_to_pushout_cofork : cokernel_cofork (biprod.lift f (-g)) :=
cokernel_cofork.of_π (biproduct_to_pushout f g) $
by rw [biprod.lift_desc, neg_comp, pushout.condition, add_right_neg]

/-- The cofork induced by the canonical map `Y ⊞ Z ⟶ pushout f g` is in fact a colimit cokernel
    cofork. -/
def is_colimit_biproduct_to_pushout : is_colimit (biproduct_to_pushout_cofork f g) :=
cofork.is_colimit.mk _
  (λ s, pushout.desc (biprod.inl ≫ cofork.π s) (biprod.inr ≫ cofork.π s) $
    sub_eq_zero.1 $ by rw [←category.assoc, ←category.assoc, ←sub_comp, sub_eq_add_neg, ←neg_comp,
      ←biprod.lift_eq, cofork.condition s, zero_comp])
  (λ s, by ext; simp)
  (λ s m h, by ext; simp [cofork.π_eq_app_one, ←h walking_parallel_pair.one] )

end biproduct_to_pushout_is_cokernel

section epi_pullback
variables [limits.has_pullbacks C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- In an abelian category, the pullback of an epimorphism is an epimorphism.
    Proof from [aluffi2016, IX.2.3], cf. [borceux-vol2, 1.7.6] -/
instance epi_pullback_of_epi_f [epi f] : epi (pullback.snd : pullback f g ⟶ Y) :=
-- It will suffice to consider some morphism e : Y ⟶ R such that
-- pullback.snd ≫ e = 0 and show that e = 0.
epi_of_cancel_zero _ $ λ R e h,
begin
  -- Consider the morphism u := (0, e) : X ⊞ Y⟶ R.
  let u := biprod.desc (0 : X ⟶ R) e,
  -- The composite pullback f g ⟶ X ⊞ Y ⟶ R is zero by assumption.
  have hu : pullback_to_biproduct_is_kernel.pullback_to_biproduct f g ≫ u = 0 := by simpa,
  -- pullback_to_biproduct f g is a kernel of (f, -g), so (f, -g) is a
  -- cokernel of pullback_to_biproduct f g
  have := epi_is_cokernel_of_kernel _
    (pullback_to_biproduct_is_kernel.is_limit_pullback_to_biproduct f g),
  -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
  obtain ⟨d, hd⟩ := cokernel_cofork.is_colimit.desc' this u hu,
  change Z ⟶ R at d,
  change biprod.desc f (-g) ≫ d = u at hd,
  -- But then f ≫ d = 0:
  have : f ≫ d = 0, calc
    f ≫ d = (biprod.inl ≫ biprod.desc f (-g)) ≫ d : by rw biprod.inl_desc
    ... = biprod.inl ≫ u : by rw [category.assoc, hd]
    ... = 0 : biprod.inl_desc _ _,
  -- But f is an epimorphism, so d = 0...
  have : d = 0 := (cancel_epi f).1 (by simpa),
  -- ...or, in other words, e = 0.
  calc
    e = biprod.inr ≫ u : by rw biprod.inr_desc
    ... = biprod.inr ≫ biprod.desc f (-g) ≫ d : by rw ←hd
    ... = biprod.inr ≫ biprod.desc f (-g) ≫ 0 : by rw this
    ... = (biprod.inr ≫ biprod.desc f (-g)) ≫ 0 : by rw ←category.assoc
    ... = 0 : has_zero_morphisms.comp_zero _ _
end

/-- In an abelian category, the pullback of an epimorphism is an epimorphism. -/
instance epi_pullback_of_epi_g [epi g] : epi (pullback.fst : pullback f g ⟶ X) :=
-- It will suffice to consider some morphism e : X ⟶ R such that
-- pullback.fst ≫ e = 0 and show that e = 0.
epi_of_cancel_zero _ $ λ R e h,
begin
  -- Consider the morphism u := (e, 0) : X ⊞ Y ⟶ R.
  let u := biprod.desc e (0 : Y ⟶ R),
  -- The composite pullback f g ⟶ X ⊞ Y ⟶ R is zero by assumption.
  have hu : pullback_to_biproduct_is_kernel.pullback_to_biproduct f g ≫ u = 0 := by simpa,
  -- pullback_to_biproduct f g is a kernel of (f, -g), so (f, -g) is a
  -- cokernel of pullback_to_biproduct f g
  have := epi_is_cokernel_of_kernel _
    (pullback_to_biproduct_is_kernel.is_limit_pullback_to_biproduct f g),
  -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
  obtain ⟨d, hd⟩ := cokernel_cofork.is_colimit.desc' this u hu,
  change Z ⟶ R at d,
  change biprod.desc f (-g) ≫ d = u at hd,
  -- But then (-g) ≫ d = 0:
  have : (-g) ≫ d = 0, calc
    (-g) ≫ d = (biprod.inr ≫ biprod.desc f (-g)) ≫ d : by rw biprod.inr_desc
    ... = biprod.inr ≫ u : by rw [category.assoc, hd]
    ... = 0 : biprod.inr_desc _ _,
  -- But g is an epimorphism, thus so is -g, so d = 0...
  have : d = 0 := (cancel_epi (-g)).1 (by simpa),
  -- ...or, in other words, e = 0.
  calc
    e = biprod.inl ≫ u : by rw biprod.inl_desc
    ... = biprod.inl ≫ biprod.desc f (-g) ≫ d : by rw ←hd
    ... = biprod.inl ≫ biprod.desc f (-g) ≫ 0 : by rw this
    ... = (biprod.inl ≫ biprod.desc f (-g)) ≫ 0 : by rw ←category.assoc
    ... = 0 : has_zero_morphisms.comp_zero _ _
end

end epi_pullback

section mono_pushout
variables [limits.has_pushouts C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

instance mono_pushout_of_mono_f [mono f] : mono (pushout.inr : Z ⟶ pushout f g) :=
mono_of_cancel_zero _ $ λ R e h,
begin
  let u := biprod.lift (0 : R ⟶ Y) e,
  have hu : u ≫ biproduct_to_pushout_is_cokernel.biproduct_to_pushout f g = 0 := by simpa,
  have := mono_is_kernel_of_cokernel _
    (biproduct_to_pushout_is_cokernel.is_colimit_biproduct_to_pushout f g),
  obtain ⟨d, hd⟩ := kernel_fork.is_limit.lift' this u hu,
  change R ⟶ X at d,
  change d ≫ biprod.lift f (-g) = u at hd,
  have : d ≫ f = 0, calc
    d ≫ f = d ≫ biprod.lift f (-g) ≫ biprod.fst : by rw biprod.lift_fst
    ... = u ≫ biprod.fst : by rw [←category.assoc, hd]
    ... = 0 : biprod.lift_fst _ _,
  have : d = 0 := (cancel_mono f).1 (by simpa),
  calc
    e = u ≫ biprod.snd : by rw biprod.lift_snd
    ... = (d ≫ biprod.lift f (-g)) ≫ biprod.snd : by rw ←hd
    ... = (0 ≫ biprod.lift f (-g)) ≫ biprod.snd : by rw this
    ... = 0 ≫ biprod.lift f (-g) ≫ biprod.snd : by rw category.assoc
    ... = 0 : zero_comp
end

instance mono_pushout_of_mono_g [mono g] : mono (pushout.inl : Y ⟶ pushout f g) :=
mono_of_cancel_zero _ $ λ R e h,
begin
  let u := biprod.lift e (0 : R ⟶ Z),
  have hu : u ≫ biproduct_to_pushout_is_cokernel.biproduct_to_pushout f g = 0 := by simpa,
  have := mono_is_kernel_of_cokernel _
    (biproduct_to_pushout_is_cokernel.is_colimit_biproduct_to_pushout f g),
  obtain ⟨d, hd⟩ := kernel_fork.is_limit.lift' this u hu,
  change R ⟶ X at d,
  change d ≫ biprod.lift f (-g) = u at hd,
  have : d ≫ (-g) = 0, calc
    d ≫ (-g) = d ≫ biprod.lift f (-g) ≫ biprod.snd : by rw biprod.lift_snd
    ... = u ≫ biprod.snd : by rw [←category.assoc, hd]
    ... = 0 : biprod.lift_snd _ _,
  have : d = 0 := (cancel_mono (-g)).1 (by simpa),
  calc
    e = u ≫ biprod.fst : by rw biprod.lift_fst
    ... = (d ≫ biprod.lift f (-g)) ≫ biprod.fst : by rw ←hd
    ... = (0 ≫ biprod.lift f (-g)) ≫ biprod.fst : by rw this
    ... = 0 ≫ biprod.lift f (-g) ≫ biprod.fst : by rw category.assoc
    ... = 0 : zero_comp
end

end mono_pushout

end category_theory.abelian

namespace category_theory.non_preadditive_abelian

variables (C : Type u) [category.{v} C] [non_preadditive_abelian C]

/-- Every non_preadditive_abelian category can be promoted to an abelian category. -/
def abelian : abelian C :=
{ has_finite_products := by apply_instance,
/- We need the `convert`s here because the instances we have are slightly different from the
   instances we need: `has_kernels` depends on an instance of `has_zero_morphisms`. In the
   case of `non_preadditive_abelian`, this instance is an explicit argument. However, in the case
   of `abelian`, the `has_zero_morphisms` instance is derived from `preadditive`. So we need to
   transform an instance of "has kernels with non_preadditive_abelian.has_zero_morphisms" to an
   instance of "has kernels with non_preadditive_abelian.preadditive.has_zero_morphisms". Luckily,
   we have a `subsingleton` instance for `has_zero_morphisms`, so `convert` can immediately close
   the goal it creates for the two instances of `has_zero_morphisms`, and the proof is complete. -/
  has_kernels := by convert (by apply_instance : limits.has_kernels C),
  has_cokernels := by convert (by apply_instance : limits.has_cokernels C),
  normal_mono := by { introsI, convert normal_mono f },
  normal_epi := by { introsI, convert normal_epi f },
  ..non_preadditive_abelian.preadditive }

end category_theory.non_preadditive_abelian
