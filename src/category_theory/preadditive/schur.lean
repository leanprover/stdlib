/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.simple
import category_theory.linear
import category_theory.endomorphism
import field_theory.algebraic_closure

/-!
# Schur's lemma
We first prove the part of Schur's Lemma that holds in any preadditive category with kernels,
that any nonzero morphism between simple objects
is an isomorphism.

Second, we prove Schur's lemma for `𝕜`-linear categories with finite dimensional hom spaces,
over an algebraically closed field `𝕜`:
the hom space `X ⟶ Y` between simple objects `X` and `Y` is at most one dimensional,
and is 1-dimensional iff `X` and `Y` are isomorphic.

## Future work
It might be nice to provide a `division_ring` instance on `End X` when `X` is simple.
This is an easy consequence of the results here,
but may take some care setting up usable instances.
-/

namespace category_theory

open category_theory.limits

universes v u
variables {C : Type u} [category.{v} C]
variables [preadditive C]

/--
The part of **Schur's lemma** that holds in any preadditive category with kernels:
that a nonzero morphism between simple objects is an isomorphism.
-/
lemma is_iso_of_hom_simple [has_kernels C] {X Y : C} [simple X] [simple Y] {f : X ⟶ Y} (w : f ≠ 0) :
  is_iso f :=
begin
  haveI : mono f := preadditive.mono_of_kernel_zero (kernel_zero_of_nonzero_from_simple w),
  exact is_iso_of_mono_of_nonzero w
end

/--
As a corollary of Schur's lemma for preadditive categories,
any morphism between simple objects is (exclusively) either an isomorphism or zero.
-/
lemma is_iso_iff_nonzero [has_kernels C] {X Y : C} [simple.{v} X] [simple.{v} Y] (f : X ⟶ Y) :
  is_iso.{v} f ↔ f ≠ 0 :=
⟨λ I,
  begin
    introI h,
    apply id_nonzero X,
    simp only [←is_iso.hom_inv_id f, h, zero_comp],
  end,
  λ w, is_iso_of_hom_simple w⟩

open finite_dimensional

variables (𝕜 : Type*) [field 𝕜]

/--
Part of **Schur's lemma** for `𝕜`-linear categories:
the hom space between two non-isomorphic simple objects is 0-dimensional.
-/
lemma finrank_hom_simple_simple_eq_zero_of_not_iso
  [has_kernels C] [linear 𝕜 C] {X Y : C} [simple.{v} X] [simple.{v} Y]
  (h : (X ≅ Y) → false):
  finrank 𝕜 (X ⟶ Y) = 0 :=
begin
  haveI := subsingleton_of_forall_eq (0 : X ⟶ Y) (λ f, begin
    have p := not_congr (is_iso_iff_nonzero f),
    simp only [not_not, ne.def] at p,
    refine p.mp (λ _, by exactI h (as_iso f)),
  end),
  exact finrank_zero_of_subsingleton,
end

variables [is_alg_closed 𝕜] [linear 𝕜 C]

-- In the proof below we have some difficulty using `I : finite_dimensional 𝕜 (X ⟶ X)`
-- where we need a `finite_dimensional 𝕜 (End X)`.
-- These are definitionally equal, but without eta reduction Lean can't see this.
-- To get around this, we use `convert I`,
-- then check the various instances agree field-by-field,
-- using `ext` equipped with the following extra lemmas:
local attribute [ext] add_comm_group module distrib_mul_action mul_action has_scalar

/--
An auxiliary lemma for Schur's lemma.

If `X ⟶ X` is finite dimensional, and every nonzero endomorphism is invertible,
then `X ⟶ X` is 1-dimensional.
-/
-- We prove this with the explicit `is_iso_iff_nonzero` assumption,
-- rather than just `[simple X]`, as this form is useful for
-- Müger's formulation of semisimplicity.
lemma finrank_endomorphism_eq_one
  {X : C} (is_iso_iff_nonzero : ∀ f : X ⟶ X, is_iso f ↔ f ≠ 0)
  [I : finite_dimensional 𝕜 (X ⟶ X)] :
  finrank 𝕜 (X ⟶ X) = 1 :=
begin
  have id_nonzero := (is_iso_iff_nonzero (𝟙 X)).mp (by apply_instance),
  apply finrank_eq_one (𝟙 X),
  { exact id_nonzero, },
  { intro f,
    haveI : nontrivial (End X) := nontrivial_of_ne _ _ id_nonzero,
    obtain ⟨c, nu⟩ := @exists_spectrum_of_is_alg_closed_of_finite_dimensional 𝕜 _ _ (End X) _ _ _
      (by { convert I, ext; refl, ext; refl, }) (End.of f),
    use c,
    rw [is_unit_iff_is_iso, is_iso_iff_nonzero, ne.def, not_not, sub_eq_zero,
      algebra.algebra_map_eq_smul_one] at nu,
    exact nu.symm, },
end

variables [has_kernels C]

/--
**Schur's lemma** for endomorphisms in `𝕜`-linear categories.
-/
lemma finrank_endomorphism_simple_eq_one
  (X : C) [simple.{v} X] [I : finite_dimensional 𝕜 (X ⟶ X)] :
  finrank 𝕜 (X ⟶ X) = 1 :=
finrank_endomorphism_eq_one 𝕜 is_iso_iff_nonzero

lemma endomorphism_simple_eq_smul_id
  {X : C} [simple.{v} X] [I : finite_dimensional 𝕜 (X ⟶ X)] (f : X ⟶ X) :
  ∃ c : 𝕜, c • 𝟙 X = f :=
(finrank_eq_one_iff_of_nonzero' (𝟙 X) (id_nonzero X)).mp (finrank_endomorphism_simple_eq_one 𝕜 X) f

/--
**Schur's lemma** for `𝕜`-linear categories:
if hom spaces are finite dimensional, then the hom space between simples is at most 1-dimensional.

See `finrank_hom_simple_simple_eq_one_iff` and `finrank_hom_simple_simple_eq_zero_iff` below
for the refinements when we know whether or not the simples are isomorphic.
-/
-- We don't really need `[∀ X Y : C, finite_dimensional 𝕜 (X ⟶ Y)]` here,
-- just at least one of `[finite_dimensional 𝕜 (X ⟶ X)]` or `[finite_dimensional 𝕜 (Y ⟶ Y)]`.
lemma finrank_hom_simple_simple_le_one
  (X Y : C) [∀ X Y : C, finite_dimensional 𝕜 (X ⟶ Y)] [simple.{v} X] [simple.{v} Y] :
  finrank 𝕜 (X ⟶ Y) ≤ 1 :=
begin
  cases subsingleton_or_nontrivial (X ⟶ Y) with h,
  { resetI,
    convert zero_le_one,
    exact finrank_zero_of_subsingleton, },
  { obtain ⟨f, nz⟩ := (nontrivial_iff_exists_ne 0).mp h,
    haveI fi := (is_iso_iff_nonzero f).mpr nz,
    apply finrank_le_one f,
    intro g,
    obtain ⟨c, w⟩ := endomorphism_simple_eq_smul_id 𝕜 (g ≫ inv f),
    exact ⟨c, by simpa using w =≫ f⟩, },
end

lemma finrank_hom_simple_simple_eq_one_iff
  (X Y : C) [∀ X Y : C, finite_dimensional 𝕜 (X ⟶ Y)] [simple.{v} X] [simple.{v} Y] :
  finrank 𝕜 (X ⟶ Y) = 1 ↔ nonempty (X ≅ Y) :=
begin
  fsplit,
  { intro h,
    rw finrank_eq_one_iff' at h,
    obtain ⟨f, nz, -⟩ := h,
    rw ←is_iso_iff_nonzero at nz,
    exactI ⟨as_iso f⟩, },
  { rintro ⟨f⟩,
    have le_one := finrank_hom_simple_simple_le_one 𝕜 X Y,
    have zero_lt : 0 < finrank 𝕜 (X ⟶ Y) :=
      finrank_pos_iff_exists_ne_zero.mpr ⟨f.hom, (is_iso_iff_nonzero f.hom).mp infer_instance⟩,
    linarith, }
end

lemma finrank_hom_simple_simple_eq_zero_iff
  (X Y : C) [∀ X Y : C, finite_dimensional 𝕜 (X ⟶ Y)] [simple.{v} X] [simple.{v} Y] :
  finrank 𝕜 (X ⟶ Y) = 0 ↔ ¬ nonempty (X ≅ Y) :=
begin
  rw ←not_congr (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y),
  refine ⟨λ h, by { rw h, simp, }, λ h, _⟩,
  have := finrank_hom_simple_simple_le_one 𝕜 X Y,
  interval_cases finrank 𝕜 (X ⟶ Y) with h',
  { exact h', },
  { exact false.elim (h h'), },
end

end category_theory
