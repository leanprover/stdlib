/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import category_theory.subobject.lattice

/-!
# Specific subobjects

We define `equalizer_subobject`, `kernel_subobject` and `image_subobject`, which are the subobjects
represented by the equalizer, kernel and image of (a pair of) morphism(s) and provide conditions
for `P.factors f`, where `P` is one of these special subobjects.

TODO: Add conditions for when `P` is a pullback subobject.
TODO: an iff characterisation of `(image_subobject f).factors h`

-/

universes v u

noncomputable theory

open category_theory category_theory.category category_theory.limits category_theory.subobject

variables {C : Type u} [category.{v} C] {X Y Z : C}

namespace category_theory

namespace limits

section equalizer
variables (f g : X ⟶ Y) [has_equalizer f g]

/-- The equalizer of morphisms `f g : X ⟶ Y` as a `subobject X`. -/
abbreviation equalizer_subobject : subobject X :=
subobject.mk (equalizer.ι f g)

/-- The underlying object of `equalizer_subobject f g` is (up to isomorphism!)
the same as the chosen object `equalizer f g`. -/
def equalizer_subobject_iso : (equalizer_subobject f g : C) ≅ equalizer f g :=
subobject.underlying_iso (equalizer.ι f g)

@[simp, reassoc]
lemma equalizer_subobject_arrow :
  (equalizer_subobject_iso f g).hom ≫ equalizer.ι f g = (equalizer_subobject f g).arrow :=
by simp [equalizer_subobject_iso]

@[simp, reassoc]
lemma equalizer_subobject_arrow' :
  (equalizer_subobject_iso f g).inv ≫ (equalizer_subobject f g).arrow = equalizer.ι f g :=
by simp [equalizer_subobject_iso]

@[reassoc]
lemma equalizer_subobject_arrow_comp :
  (equalizer_subobject f g).arrow ≫ f = (equalizer_subobject f g).arrow ≫ g :=
by rw [←equalizer_subobject_arrow, category.assoc, category.assoc, equalizer.condition]

lemma equalizer_subobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g) :
  (equalizer_subobject f g).factors h :=
⟨equalizer.lift h w, by simp⟩

lemma equalizer_subobject_factors_iff {W : C} (h : W ⟶ X) :
  (equalizer_subobject f g).factors h ↔ h ≫ f = h ≫ g :=
⟨λ w, by rw [←subobject.factor_thru_arrow _ _ w, category.assoc,
  equalizer_subobject_arrow_comp, category.assoc],
equalizer_subobject_factors f g h⟩

end equalizer

section kernel
variables [has_zero_morphisms C] (f : X ⟶ Y) [has_kernel f]

/-- The kernel of a morphism `f : X ⟶ Y` as a `subobject X`. -/
abbreviation kernel_subobject : subobject X :=
subobject.mk (kernel.ι f)

/-- The underlying object of `kernel_subobject f` is (up to isomorphism!)
the same as the chosen object `kernel f`. -/
def kernel_subobject_iso :
  (kernel_subobject f : C) ≅ kernel f :=
subobject.underlying_iso (kernel.ι f)

@[simp, reassoc]
lemma kernel_subobject_arrow :
  (kernel_subobject_iso f).hom ≫ kernel.ι f = (kernel_subobject f).arrow :=
by simp [kernel_subobject_iso]

@[simp, reassoc]
lemma kernel_subobject_arrow' :
  (kernel_subobject_iso f).inv ≫ (kernel_subobject f).arrow = kernel.ι f :=
by simp [kernel_subobject_iso]

@[simp, reassoc]
lemma kernel_subobject_arrow_comp :
  (kernel_subobject f).arrow ≫ f = 0 :=
by { rw [←kernel_subobject_arrow], simp only [category.assoc, kernel.condition, comp_zero], }

lemma kernel_subobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
  (kernel_subobject f).factors h :=
⟨kernel.lift _ h w, by simp⟩

lemma kernel_subobject_factors_iff {W : C} (h : W ⟶ X) :
  (kernel_subobject f).factors h ↔ h ≫ f = 0 :=
⟨λ w, by rw [←subobject.factor_thru_arrow _ _ w, category.assoc,
  kernel_subobject_arrow_comp, comp_zero],
kernel_subobject_factors f h⟩

/-- A factorisation of `h : W ⟶ X` through `kernel_subobject f`, assuming `h ≫ f = 0`. -/
def factor_thru_kernel_subobject {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
  W ⟶ kernel_subobject f :=
(kernel_subobject f).factor_thru h (kernel_subobject_factors f h w)

@[simp] lemma factor_thru_kernel_subobject_comp_arrow {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
  factor_thru_kernel_subobject f h w ≫ (kernel_subobject f).arrow = h :=
by { dsimp [factor_thru_kernel_subobject], simp, }

section
variables {f} {X' Y' : C} {f' : X' ⟶ Y'} [has_kernel f']

/-- A commuting square induces a morphism between the kernel subobjects. -/
def kernel_subobject_map (sq : arrow.mk f ⟶ arrow.mk f') :
  (kernel_subobject f : C) ⟶ (kernel_subobject f' : C) :=
subobject.factor_thru _
  ((kernel_subobject f).arrow ≫ sq.left)
  (kernel_subobject_factors _ _ (by simp [sq.w]))

@[simp, reassoc]
lemma kernel_subobject_map_arrow (sq : arrow.mk f ⟶ arrow.mk f') :
  kernel_subobject_map sq ≫ (kernel_subobject f').arrow =
    (kernel_subobject f).arrow ≫ sq.left :=
by simp [kernel_subobject_map]

@[simp] lemma kernel_subobject_map_id : kernel_subobject_map (𝟙 (arrow.mk f)) = 𝟙 _ :=
by { ext, simp, dsimp, simp, } -- See library note [dsimp, simp].

@[simp] lemma kernel_subobject_map_comp {X'' Y'' : C} {f'' : X'' ⟶ Y''} [has_kernel f'']
  (sq : arrow.mk f ⟶ arrow.mk f') (sq' : arrow.mk f' ⟶ arrow.mk f'') :
  kernel_subobject_map (sq ≫ sq') = kernel_subobject_map sq ≫ kernel_subobject_map sq' :=
by { ext, simp, }

end

@[simp]
lemma kernel_subobject_zero {A B : C} : kernel_subobject (0 : A ⟶ B) = ⊤ :=
(is_iso_iff_mk_eq_top _).mp (by apply_instance)

instance is_iso_kernel_subobject_zero_arrow : is_iso (kernel_subobject (0 : X ⟶ Y)).arrow :=
(is_iso_arrow_iff_eq_top _).mpr kernel_subobject_zero

lemma le_kernel_subobject (A : subobject X) (h : A.arrow ≫ f = 0) : A ≤ kernel_subobject f :=
subobject.le_mk_of_comm (kernel.lift f A.arrow h) (by simp)

/--
The isomorphism between the kernel of `f ≫ g` and the kernel of `g`,
when `f` is an isomorphism.
-/
def kernel_subobject_iso_comp
  {X' : C} (f : X' ⟶ X) [is_iso f] (g : X ⟶ Y) [has_kernel g] :
  (kernel_subobject (f ≫ g) : C) ≅ (kernel_subobject g : C) :=
(kernel_subobject_iso _) ≪≫ (kernel_is_iso_comp f g) ≪≫ (kernel_subobject_iso _).symm

@[simp]
lemma kernel_subobject_iso_comp_hom_arrow
  {X' : C} (f : X' ⟶ X) [is_iso f] (g : X ⟶ Y) [has_kernel g] :
  (kernel_subobject_iso_comp f g).hom ≫ (kernel_subobject g).arrow =
    (kernel_subobject (f ≫ g)).arrow ≫ f :=
by { simp [kernel_subobject_iso_comp], }

@[simp]
lemma kernel_subobject_iso_comp_inv_arrow
  {X' : C} (f : X' ⟶ X) [is_iso f] (g : X ⟶ Y) [has_kernel g] :
  (kernel_subobject_iso_comp f g).inv ≫ (kernel_subobject (f ≫ g)).arrow =
    (kernel_subobject g).arrow ≫ inv f :=
by { simp [kernel_subobject_iso_comp], }

/-- The kernel of `f` is always a smaller subobject than the kernel of `f ≫ h`. -/
lemma kernel_subobject_comp_le
  (f : X ⟶ Y) [has_kernel f] {Z : C} (h : Y ⟶ Z) [has_kernel (f ≫ h)]:
  kernel_subobject f ≤ kernel_subobject (f ≫ h) :=
le_kernel_subobject _ _ (by simp)

/-- Postcomposing by an monomorphism does not change the kernel subobject. -/
@[simp]
lemma kernel_subobject_comp_mono
  (f : X ⟶ Y) [has_kernel f] {Z : C} (h : Y ⟶ Z) [mono h] :
  kernel_subobject (f ≫ h) = kernel_subobject f :=
le_antisymm
  (le_kernel_subobject _ _ ((cancel_mono h).mp (by simp)))
  (kernel_subobject_comp_le f h)

instance kernel_subobject_comp_mono_is_iso
  (f : X ⟶ Y) [has_kernel f] {Z : C} (h : Y ⟶ Z) [mono h] :
  is_iso (subobject.of_le _ _ (kernel_subobject_comp_le f h)) :=
begin
  rw of_le_mk_le_mk_of_comm (kernel_comp_mono f h).inv,
  { apply_instance, },
  { simp, },
end

end kernel

section image
variables (f : X ⟶ Y) [has_image f]

/-- The image of a morphism `f g : X ⟶ Y` as a `subobject Y`. -/
abbreviation image_subobject : subobject Y :=
subobject.mk (image.ι f)

/-- The underlying object of `image_subobject f` is (up to isomorphism!)
the same as the chosen object `image f`. -/
def image_subobject_iso :
  (image_subobject f : C) ≅ image f :=
subobject.underlying_iso (image.ι f)

@[simp, reassoc]
lemma image_subobject_arrow :
  (image_subobject_iso f).hom ≫ image.ι f = (image_subobject f).arrow :=
by simp [image_subobject_iso]

@[simp, reassoc]
lemma image_subobject_arrow' :
  (image_subobject_iso f).inv ≫ (image_subobject f).arrow = image.ι f :=
by simp [image_subobject_iso]

/-- A factorisation of `f : X ⟶ Y` through `image_subobject f`. -/
def factor_thru_image_subobject : X ⟶ image_subobject f :=
factor_thru_image f ≫ (image_subobject_iso f).inv

instance [has_equalizers C] : epi (factor_thru_image_subobject f) :=
by { dsimp [factor_thru_image_subobject], apply epi_comp,  }

@[simp, reassoc]
lemma image_subobject_arrow_comp :
  factor_thru_image_subobject f ≫ (image_subobject f).arrow = f :=
by simp [factor_thru_image_subobject, image_subobject_arrow]

lemma image_subobject_arrow_comp_eq_zero
  [has_zero_morphisms C] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [has_image f]
  [epi (factor_thru_image_subobject f)] (h : f ≫ g = 0) : (image_subobject f).arrow ≫ g = 0 :=
zero_of_epi_comp (factor_thru_image_subobject f) $ by simp [h]

lemma image_subobject_factors_comp_self {W : C} (k : W ⟶ X)  :
  (image_subobject f).factors (k ≫ f) :=
⟨k ≫ factor_thru_image f, by simp⟩

@[simp]
lemma factor_thru_image_subobject_comp_self {W : C} (k : W ⟶ X) (h) :
  (image_subobject f).factor_thru (k ≫ f) h = k ≫ factor_thru_image_subobject f :=
by { ext, simp, }

@[simp]
lemma factor_thru_image_subobject_comp_self_assoc {W W' : C} (k : W ⟶ W') (k' : W' ⟶ X) (h) :
  (image_subobject f).factor_thru (k ≫ k' ≫ f) h = k ≫ k' ≫ factor_thru_image_subobject f :=
by { ext, simp, }

/-- The image of `h ≫ f` is always a smaller subobject than the image of `f`. -/
lemma image_subobject_comp_le
  {X' : C} (h : X' ⟶ X) (f : X ⟶ Y) [has_image f] [has_image (h ≫ f)] :
  image_subobject (h ≫ f) ≤ image_subobject f :=
subobject.mk_le_mk_of_comm (image.pre_comp h f) (by simp)

section
open_locale zero_object
variables [has_zero_morphisms C] [has_zero_object C]

@[simp]
lemma image_subobject_zero_arrow :
  (image_subobject (0 : X ⟶ Y)).arrow = 0 :=
by { rw ←image_subobject_arrow, simp, }

@[simp]
lemma image_subobject_zero {A B : C} :
  image_subobject (0 : A ⟶ B) = ⊥ :=
subobject.eq_of_comm
  (image_subobject_iso _ ≪≫ image_zero ≪≫ subobject.bot_coe_iso_zero.symm) (by simp)

end

section
variables [has_equalizers C]
local attribute [instance] epi_comp

/--
The morphism `image_subobject (h ≫ f) ⟶ image_subobject f`
is an epimorphism when `h` is an epimorphism.
In general this does not imply that `image_subobject (h ≫ f) = image_subobject f`,
although it will when the ambient category is abelian.
 -/
instance image_subobject_comp_le_epi_of_epi
  {X' : C} (h : X' ⟶ X) [epi h] (f : X ⟶ Y) [has_image f] [has_image (h ≫ f)] :
  epi (subobject.of_le _ _ (image_subobject_comp_le h f)) :=
begin
  rw of_le_mk_le_mk_of_comm (image.pre_comp h f),
  { apply_instance, },
  { simp, },
end

end

section
variables [has_equalizers C]

/-- Postcomposing by an isomorphism gives an isomorphism between image subobjects. -/
def image_subobject_comp_iso
  (f : X ⟶ Y) [has_image f] {Y' : C} (h : Y ⟶ Y') [is_iso h] :
  (image_subobject (f ≫ h) : C) ≅ (image_subobject f : C) :=
(image_subobject_iso _) ≪≫ (image.comp_iso _ _).symm ≪≫ (image_subobject_iso _).symm

@[simp, reassoc]
lemma image_subobject_comp_iso_hom_arrow
  (f : X ⟶ Y) [has_image f] {Y' : C} (h : Y ⟶ Y') [is_iso h] :
  (image_subobject_comp_iso f h).hom ≫ (image_subobject f).arrow =
    (image_subobject (f ≫ h)).arrow ≫ inv h :=
by simp [image_subobject_comp_iso]

@[simp, reassoc]
lemma image_subobject_comp_iso_inv_arrow
  (f : X ⟶ Y) [has_image f] {Y' : C} (h : Y ⟶ Y') [is_iso h] :
  (image_subobject_comp_iso f h).inv ≫ (image_subobject (f ≫ h)).arrow =
    (image_subobject f).arrow ≫ h :=
by simp [image_subobject_comp_iso]

end

/-- Precomposing by an isomorphism does not change the image subobject. -/
lemma image_subobject_iso_comp [has_equalizers C]
  {X' : C} (h : X' ⟶ X) [is_iso h] (f : X ⟶ Y) [has_image f] :
  image_subobject (h ≫ f) = image_subobject f :=
le_antisymm
  (image_subobject_comp_le h f)
  (subobject.mk_le_mk_of_comm (inv (image.pre_comp h f)) (by simp))

lemma image_subobject_le {A B : C} {X : subobject B} (f : A ⟶ B) [has_image f]
  (h : A ⟶ X) (w : h ≫ X.arrow = f) :
  image_subobject f ≤ X :=
subobject.le_of_comm
  ((image_subobject_iso f).hom ≫ image.lift { I := (X : C), e := h, m := X.arrow, })
  (by simp)

lemma image_subobject_le_mk {A B : C} {X : C} (g : X ⟶ B) [mono g] (f : A ⟶ B) [has_image f]
  (h : A ⟶ X) (w : h ≫ g = f) :
  image_subobject f ≤ subobject.mk g :=
image_subobject_le f (h ≫ (subobject.underlying_iso g).inv) (by simp [w])

/-- Given a commutative square between morphisms `f` and `g`,
we have a morphism in the category from `image_subobject f` to `image_subobject g`. -/
def image_subobject_map {W X Y Z : C} {f : W ⟶ X} [has_image f] {g : Y ⟶ Z} [has_image g]
  (sq : arrow.mk f ⟶ arrow.mk g) [has_image_map sq] :
  (image_subobject f : C) ⟶ (image_subobject g : C) :=
(image_subobject_iso f).hom ≫ image.map sq ≫ (image_subobject_iso g).inv

@[simp, reassoc]
lemma image_subobject_map_arrow {W X Y Z : C} {f : W ⟶ X} [has_image f] {g : Y ⟶ Z} [has_image g]
  (sq : arrow.mk f ⟶ arrow.mk g) [has_image_map sq] :
  image_subobject_map sq ≫ (image_subobject g).arrow = (image_subobject f).arrow ≫ sq.right :=
begin
  simp only [image_subobject_map, category.assoc, image_subobject_arrow'],
  erw [image.map_ι, ←category.assoc, image_subobject_arrow],
end

end image

end limits

end category_theory
