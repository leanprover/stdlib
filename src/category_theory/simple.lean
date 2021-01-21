/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.abelian.basic

noncomputable theory

open category_theory.limits

namespace category_theory

universes v u
variables {C : Type u} [category.{v} C]

section
variables [has_zero_morphisms C]

/-- An object is simple if monomorphisms into it are (exclusively) either isomorphisms or zero. -/
-- This is a constructive definition, from which we can extract an inverse for `f` given `f ≠ 0`.
-- We show below that although it contains data, it is a subsingleton.
class simple (X : C) : Type (max u v) :=
(mono_is_iso_equiv_nonzero : ∀ {Y : C} (f : Y ⟶ X) [mono f], is_iso f ≃ (f ≠ 0))

@[ext] lemma simple.ext {X : C} {a b : simple X} : a = b :=
begin
  casesI a, casesI b,
  congr,
end

instance subsingleton_simple (X : C) : subsingleton (simple X) :=
subsingleton.intro (@simple.ext _ _ _ X)

/-- A nonzero monomorphism to a simple object is an isomorphism. -/
def is_iso_of_mono_of_nonzero {X Y : C} [simple Y] {f : X ⟶ Y} [mono f] (w : f ≠ 0) :
  is_iso f :=
(simple.mono_is_iso_equiv_nonzero f).symm w

lemma kernel_zero_of_nonzero_from_simple
  {X Y : C} [simple X] {f : X ⟶ Y} [has_kernel f] (w : f ≠ 0) :
  kernel.ι f = 0 :=
begin
  classical,
  by_contradiction h,
  haveI := is_iso_of_mono_of_nonzero h,
  exact w (eq_zero_of_epi_kernel f),
end

lemma mono_to_simple_zero_of_not_iso
  {X Y : C} [simple Y] {f : X ⟶ Y} [mono f] (w : is_iso f → false) : f = 0 :=
begin
  classical,
  by_contradiction h,
  apply w,
  exact is_iso_of_mono_of_nonzero h,
end

lemma id_nonzero (X : C) [simple.{v} X] : 𝟙 X ≠ 0 :=
(simple.mono_is_iso_equiv_nonzero (𝟙 X)) (by apply_instance)

section
variable [has_zero_object C]
local attribute [instance] has_zero_object.has_zero

/-- We don't want the definition of 'simple' to include the zero object, so we check that here. -/
lemma zero_not_simple [simple (0 : C)] : false :=
(simple.mono_is_iso_equiv_nonzero (0 : (0 : C) ⟶ (0 : C))) { inv := 0, } rfl

end
end

-- We next make the dual arguments, but for this we must be in an abelian category.
section abelian
variables [abelian C]

/-- In an abelian category, an object satisfying the dual of the definition of a simple object is
    simple. -/
def simple_of_cosimple (X : C) (h : ∀ {Z : C} (f : X ⟶ Z) [epi f], is_iso f ≃ (f ≠ 0)) :
  simple X :=
⟨λ Y f I,
 begin
  classical,
  apply equiv_of_subsingleton_of_subsingleton,
  { introsI,
    have hx := cokernel.π_of_epi f,
    by_contradiction h,
    push_neg at h,
    substI h,
    exact h _ (cokernel.π_of_zero _ _) hx },
  { intro hf,
    suffices : epi f,
    { resetI, apply abelian.is_iso_of_mono_of_epi },
    apply preadditive.epi_of_cokernel_zero,
    by_contradiction h',
    exact cokernel_not_iso_of_nonzero hf ((h _).symm h') }
 end⟩

/-- A nonzero epimorphism from a simple object is an isomorphism. -/
def is_iso_of_epi_of_nonzero {X Y : C} [simple X] {f : X ⟶ Y} [epi f] (w : f ≠ 0) :
  is_iso f :=
begin
  -- `f ≠ 0` means that `kernel.ι f` is not an iso, and hence zero, and hence `f` is a mono.
  haveI : mono f :=
    preadditive.mono_of_kernel_zero (mono_to_simple_zero_of_not_iso (kernel_not_iso_of_nonzero w)),
  exact abelian.is_iso_of_mono_of_epi f,
end

lemma cokernel_zero_of_nonzero_to_simple
  {X Y : C} [simple Y] {f : X ⟶ Y} [has_cokernel f] (w : f ≠ 0) :
  cokernel.π f = 0 :=
begin
  classical,
  by_contradiction h,
  haveI := is_iso_of_epi_of_nonzero h,
  exact w (eq_zero_of_mono_cokernel f),
end

lemma epi_from_simple_zero_of_not_iso
  {X Y : C} [simple X] {f : X ⟶ Y} [epi f] (w : is_iso f → false) : f = 0 :=
begin
  classical,
  by_contradiction h,
  apply w,
  exact is_iso_of_epi_of_nonzero h,
end

end abelian

end category_theory
