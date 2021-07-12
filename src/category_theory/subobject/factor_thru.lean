/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import category_theory.subobject.basic

/-!
# Factoring through subobjects

The predicate `h : P.factors f`, for `P : subobject Y` and `f : X ⟶ Y`
asserts the existence of some `P.factor_thru f : X ⟶ (P : C)` making the obvious diagram commute.

-/

universes v₁ v₂ u₁ u₂

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v₁} C] {X Y Z : C}
variables {D : Type u₂} [category.{v₂} D]

namespace category_theory

namespace mono_over

/-- When `f : X ⟶ Y` and `P : mono_over Y`,
`P.factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.factors f`, you can recover the morphism as `P.factor_thru f h`.
-/
def factors {X Y : C} (P : mono_over Y) (f : X ⟶ Y) : Prop := ∃ g : X ⟶ (P : C), g ≫ P.arrow = f

lemma factors_congr {X : C} {f g : mono_over X} {Y : C} (h : Y ⟶ X) (e : f ≅ g) :
  f.factors h ↔ g.factors h :=
⟨λ ⟨u, hu⟩, ⟨u ≫ (((mono_over.forget _).map e.hom)).left, by simp [hu]⟩,
 λ ⟨u, hu⟩, ⟨u ≫ (((mono_over.forget _).map e.inv)).left, by simp [hu]⟩⟩

/-- `P.factor_thru f h` provides a factorisation of `f : X ⟶ Y` through some `P : mono_over Y`,
given the evidence `h : P.factors f` that such a factorisation exists. -/
def factor_thru {X Y : C} (P : mono_over Y) (f : X ⟶ Y) (h : factors P f) : X ⟶ (P : C) :=
classical.some h

end mono_over

namespace subobject

/-- When `f : X ⟶ Y` and `P : subobject Y`,
`P.factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.factors f`, you can recover the morphism as `P.factor_thru f h`.
-/
def factors {X Y : C} (P : subobject Y) (f : X ⟶ Y) : Prop :=
quotient.lift_on' P (λ P, P.factors f)
begin
  rintros P Q ⟨h⟩,
  apply propext,
  split,
  { rintro ⟨i, w⟩,
    exact ⟨i ≫ h.hom.left, by erw [category.assoc, over.w h.hom, w]⟩, },
  { rintro ⟨i, w⟩,
    exact ⟨i ≫ h.inv.left, by erw [category.assoc, over.w h.inv, w]⟩, },
end

@[simp] lemma mk_factors_iff {X Y Z : C} (f : Y ⟶ X) [mono f] (g : Z ⟶ X) :
  (subobject.mk f).factors g ↔ (mono_over.mk' f).factors g :=
iff.rfl

lemma factors_iff {X Y : C} (P : subobject Y) (f : X ⟶ Y) :
  P.factors f ↔ (representative.obj P).factors f :=
quot.induction_on P $ λ a, mono_over.factors_congr _ (representative_iso _).symm

lemma factors_self {X : C} (P : subobject X) : P.factors P.arrow :=
(factors_iff _ _).mpr ⟨𝟙 P, (by simp)⟩

lemma factors_comp_arrow {X Y : C} {P : subobject Y} (f : X ⟶ P) : P.factors (f ≫ P.arrow) :=
(factors_iff _ _).mpr ⟨f, rfl⟩

lemma factors_of_factors_right {X Y Z : C} {P : subobject Z} (f : X ⟶ Y) {g : Y ⟶ Z}
  (h : P.factors g) : P.factors (f ≫ g) :=
begin
  revert P,
  refine quotient.ind' _,
  intro P,
  rintro ⟨g, rfl⟩,
  exact ⟨f ≫ g, by simp⟩,
end

lemma factors_zero [has_zero_morphisms C] {X Y : C} {P : subobject Y} :
  P.factors (0 : X ⟶ Y) :=
(factors_iff _ _).mpr ⟨0, by simp⟩

lemma factors_of_le {Y Z : C} {P Q : subobject Y} (f : Z ⟶ Y) (h : P ≤ Q) :
  P.factors f → Q.factors f :=
by { simp only [factors_iff], exact λ ⟨u, hu⟩, ⟨u ≫ of_le _ _ h, by simp [←hu]⟩ }

/-- `P.factor_thru f h` provides a factorisation of `f : X ⟶ Y` through some `P : subobject Y`,
given the evidence `h : P.factors f` that such a factorisation exists. -/
def factor_thru {X Y : C} (P : subobject Y) (f : X ⟶ Y) (h : factors P f) : X ⟶ P :=
classical.some ((factors_iff _ _).mp h)

@[simp, reassoc] lemma factor_thru_arrow {X Y : C} (P : subobject Y) (f : X ⟶ Y) (h : factors P f) :
  P.factor_thru f h ≫ P.arrow = f :=
classical.some_spec ((factors_iff _ _).mp h)

@[simp] lemma factor_thru_self {X : C} (P : subobject X) (h) :
  P.factor_thru P.arrow h = 𝟙 P :=
by { ext, simp, }

@[simp] lemma factor_thru_comp_arrow {X Y : C} {P : subobject Y} (f : X ⟶ P) (h) :
  P.factor_thru (f ≫ P.arrow) h = f :=
by { ext, simp, }

@[simp] lemma factor_thru_eq_zero [has_zero_morphisms C]
  {X Y : C} {P : subobject Y} {f : X ⟶ Y} {h : factors P f} :
  P.factor_thru f h = 0 ↔ f = 0 :=
begin
  fsplit,
  { intro w,
    replace w := w =≫ P.arrow,
    simpa using w, },
  { rintro rfl,
    ext, simp, },
end

lemma factor_thru_right {X Y Z : C} {P : subobject Z} (f : X ⟶ Y) (g : Y ⟶ Z) (h : P.factors g) :
  f ≫ P.factor_thru g h = P.factor_thru (f ≫ g) (factors_of_factors_right f h) :=
begin
  apply (cancel_mono P.arrow).mp,
  simp,
end

@[simp]
lemma factor_thru_zero
  [has_zero_morphisms C] {X Y : C} {P : subobject Y} (h : P.factors (0 : X ⟶ Y)) :
  P.factor_thru 0 h = 0 :=
by simp

-- `h` is an explicit argument here so we can use
-- `rw factor_thru_le h`, obtaining a subgoal `P.factors f`.
-- (While the reverse direction looks plausible as a simp lemma, it seems to be unproductive.)
lemma factor_thru_of_le
  {Y Z : C} {P Q : subobject Y} {f : Z ⟶ Y} (h : P ≤ Q) (w : P.factors f) :
  Q.factor_thru f (factors_of_le f h w) = P.factor_thru f w ≫ of_le P Q h :=
by { ext, simp, }

section preadditive

variables [preadditive C]

lemma factors_add {X Y : C} {P : subobject Y} (f g : X ⟶ Y) (wf : P.factors f) (wg : P.factors g) :
  P.factors (f + g) :=
(factors_iff _ _).mpr ⟨P.factor_thru f wf + P.factor_thru g wg, by simp⟩

-- This can't be a `simp` lemma as `wf` and `wg` may not exist.
-- However you can `rw` by it to assert that `f` and `g` factor through `P` separately.
lemma factor_thru_add {X Y : C} {P : subobject Y} (f g : X ⟶ Y)
   (w : P.factors (f + g)) (wf : P.factors f) (wg : P.factors g) :
  P.factor_thru (f + g) w = P.factor_thru f wf + P.factor_thru g wg :=
by { ext, simp, }

lemma factors_left_of_factors_add {X Y : C} {P : subobject Y} (f g : X ⟶ Y)
  (w : P.factors (f + g)) (wg : P.factors g) : P.factors f :=
(factors_iff _ _).mpr ⟨P.factor_thru (f + g) w - P.factor_thru g wg, by simp⟩

@[simp]
lemma factor_thru_add_sub_factor_thru_right {X Y : C} {P : subobject Y} (f g : X ⟶ Y)
  (w : P.factors (f + g)) (wg : P.factors g) :
  P.factor_thru (f + g) w - P.factor_thru g wg =
    P.factor_thru f (factors_left_of_factors_add f g w wg) :=
by { ext, simp, }

lemma factors_right_of_factors_add {X Y : C} {P : subobject Y} (f g : X ⟶ Y)
  (w : P.factors (f + g)) (wf : P.factors f) : P.factors g :=
(factors_iff _ _).mpr ⟨P.factor_thru (f + g) w - P.factor_thru f wf, by simp⟩

@[simp]
lemma factor_thru_add_sub_factor_thru_left {X Y : C} {P : subobject Y} (f g : X ⟶ Y)
  (w : P.factors (f + g)) (wf : P.factors f) :
  P.factor_thru (f + g) w - P.factor_thru f wf =
    P.factor_thru g (factors_right_of_factors_add f g w wf) :=
by { ext, simp, }

end preadditive

end subobject

end category_theory
