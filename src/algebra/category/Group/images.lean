/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.abelian

/-!
# The category of commutative additive groups has images.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `AddCommGroup` is an abelian category.
-/

open category_theory
open category_theory.limits

universe u

namespace AddCommGroup

-- Note that because `injective_of_mono` is currently only proved in `Type 0`,
-- we restrict to the lowest universe here for now.
variables {G H : AddCommGroup.{0}} (f : G ⟶ H)

local attribute [ext] subtype.ext_val

section -- implementation details of `has_image` for AddCommGroup; use the API, not these
/-- the image of a morphism in AddCommGroup is just the bundling of `add_monoid_hom.range f` -/
def image : AddCommGroup := AddCommGroup.of (add_monoid_hom.range f)

/-- the inclusion of `image f` into the target -/
def image.ι : image f ⟶ H := f.range.subtype

instance : mono (image.ι f) := concrete_category.mono_of_injective (image.ι f) subtype.val_injective

/-- the corestriction map to the image -/
def factor_thru_image : G ⟶ image f := f.to_range

lemma image.fac : factor_thru_image f ≫ image.ι f = f :=
by { ext, refl, }

local attribute [simp] image.fac

variables {f}
/-- the universal property for the image factorisation -/
noncomputable def image.lift (F' : mono_factorisation f) : image f ⟶ F'.I :=
{ to_fun :=
  (λ x, F'.e (classical.indefinite_description _ x.2).1 : image f → F'.I),
  map_zero' :=
  begin
    haveI := F'.m_mono,
    apply injective_of_mono F'.m,
    change (F'.e ≫ F'.m) _ = _,
    rw [F'.fac, add_monoid_hom.map_zero],
    convert (classical.indefinite_description (λ y, f y = 0) _).2,
  end,
  map_add' :=
  begin
    intros x y,
    haveI := F'.m_mono,
    apply injective_of_mono F'.m,
    rw [add_monoid_hom.map_add],
    change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _,
    rw [F'.fac],
    rw (classical.indefinite_description (λ z, f z = _) _).2,
    rw (classical.indefinite_description (λ z, f z = _) _).2,
    rw (classical.indefinite_description (λ z, f z = _) _).2,
    refl,
  end,
 }
lemma image.lift_fac (F' : mono_factorisation f) : image.lift F' ≫ F'.m = image.ι f :=
begin
  ext x,
  change (F'.e ≫ F'.m) _ = _,
  rw [F'.fac, (classical.indefinite_description _ x.2).2],
  refl,
end
end

/-- the factorisation of any morphism in AddCommGroup through a mono. -/
def mono_factorisation : mono_factorisation f :=
{ I := image f,
  m := image.ι f,
  e := factor_thru_image f }

/-- the factorisation of any morphism in AddCommGroup through a mono has the universal property of
the image. -/
noncomputable def is_image : is_image (mono_factorisation f) :=
{ lift := image.lift,
  lift_fac' := image.lift_fac }

/--
The categorical image of a morphism in `AddCommGroup`
agrees with the usual group-theoretical range.
-/
noncomputable def image_iso_range {G H : AddCommGroup.{0}} (f : G ⟶ H) :
  limits.image f ≅ AddCommGroup.of f.range :=
is_image.iso_ext (image.is_image f) (is_image f)

end AddCommGroup
