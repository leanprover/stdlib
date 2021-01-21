/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.times_cont_diff

/-!
# Normed space structure on `ℂ`.

This file gathers basic facts on complex numbers of an analytic nature.

## Main results

This file registers `ℂ` as a normed field, expresses basic properties of the norm, and gives
tools on the real vector space structure of `ℂ`. Notably, in the namespace `complex`,
it defines functions:

* `continuous_linear_map.re`
* `continuous_linear_map.im`
* `continuous_linear_map.of_real`

They are bundled versions of the real part, the imaginary part, and the embedding of `ℝ` in `ℂ`,
as continuous `ℝ`-linear maps.

`has_deriv_at.real_of_complex` expresses that, if a function on `ℂ` is differentiable (over `ℂ`),
then its restriction to `ℝ` is differentiable over `ℝ`, with derivative the real part of the
complex derivative.
-/
noncomputable theory


namespace complex

instance : has_norm ℂ := ⟨abs⟩

instance : normed_group ℂ :=
normed_group.of_core ℂ
{ norm_eq_zero_iff := λ z, abs_eq_zero,
  triangle := abs_add,
  norm_neg := abs_neg }

instance : normed_field ℂ :=
{ norm := abs,
  dist_eq := λ _ _, rfl,
  norm_mul' := abs_mul,
  .. complex.field }

instance : nondiscrete_normed_field ℂ :=
{ non_trivial := ⟨2, by simp [norm]; norm_num⟩ }

instance normed_algebra_over_reals : normed_algebra ℝ ℂ :=
{ norm_algebra_map_eq := abs_of_real,
  ..complex.algebra_over_reals }

@[simp] lemma norm_eq_abs (z : ℂ) : ∥z∥ = abs z := rfl

lemma dist_eq (z w : ℂ) : dist z w = abs (z - w) := rfl

@[simp] lemma norm_real (r : ℝ) : ∥(r : ℂ)∥ = ∥r∥ := abs_of_real _

@[simp] lemma norm_rat (r : ℚ) : ∥(r : ℂ)∥ = _root_.abs (r : ℝ) :=
suffices ∥((r : ℝ) : ℂ)∥ = _root_.abs r, by simpa,
by rw [norm_real, real.norm_eq_abs]

@[simp] lemma norm_nat (n : ℕ) : ∥(n : ℂ)∥ = n := abs_of_nat _

@[simp] lemma norm_int {n : ℤ} : ∥(n : ℂ)∥ = _root_.abs n :=
suffices ∥((n : ℝ) : ℂ)∥ = _root_.abs n, by simpa,
by rw [norm_real, real.norm_eq_abs]

lemma norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : ∥(n : ℂ)∥ = n :=
by rw [norm_int, _root_.abs_of_nonneg]; exact int.cast_nonneg.2 hn

/-- A complex normed vector space is also a real normed vector space. -/
@[priority 900]
instance normed_space.restrict_scalars_real (E : Type*) [normed_group E] [normed_space ℂ E] :
  normed_space ℝ E := normed_space.restrict_scalars ℝ ℂ E

open continuous_linear_map

/-- The space of continuous linear maps over `ℝ`, from a real vector space to a complex vector
space, is a normed vector space over `ℂ`. -/
instance continuous_linear_map.real_smul_complex (E : Type*) [normed_group E] [normed_space ℝ E]
  (F : Type*) [normed_group F] [normed_space ℂ F] :
  normed_space ℂ (E →L[ℝ] F) :=
continuous_linear_map.normed_space_extend_scalars

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def continuous_linear_map.re : ℂ →L[ℝ] ℝ := linear_map.re.to_continuous_linear_map

@[simp] lemma continuous_linear_map.re_coe :
  (coe (continuous_linear_map.re) : ℂ →ₗ[ℝ] ℝ) = linear_map.re := rfl

@[simp] lemma continuous_linear_map.re_apply (z : ℂ) :
  (continuous_linear_map.re : ℂ → ℝ) z = z.re := rfl

@[simp] lemma continuous_linear_map.re_norm :
  ∥continuous_linear_map.re∥ = 1 :=
le_antisymm (op_norm_le_bound _ zero_le_one $ λ z, by simp [real.norm_eq_abs, abs_re_le_abs]) $
calc 1 = ∥continuous_linear_map.re 1∥ : by simp
   ... ≤ ∥continuous_linear_map.re∥ : unit_le_op_norm _ _ (by simp)

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def continuous_linear_map.im : ℂ →L[ℝ] ℝ := linear_map.im.to_continuous_linear_map

@[simp] lemma continuous_linear_map.im_coe :
  (coe (continuous_linear_map.im) : ℂ →ₗ[ℝ] ℝ) = linear_map.im := rfl

@[simp] lemma continuous_linear_map.im_apply (z : ℂ) :
  (continuous_linear_map.im : ℂ → ℝ) z = z.im := rfl

@[simp] lemma continuous_linear_map.im_norm :
  ∥continuous_linear_map.im∥ = 1 :=
le_antisymm (op_norm_le_bound _ zero_le_one $ λ z, by simp [real.norm_eq_abs, abs_im_le_abs]) $
calc 1 = ∥continuous_linear_map.im I∥ : by simp
   ... ≤ ∥continuous_linear_map.im∥ : unit_le_op_norm _ _ (by simp)

/-- Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def continuous_linear_map.of_real : ℝ →L[ℝ] ℂ := linear_map.of_real.to_continuous_linear_map

lemma continuous_of_real : continuous (coe : ℝ → ℂ) := continuous_linear_map.of_real.continuous

@[simp] lemma continuous_linear_map.of_real_coe :
  (coe (continuous_linear_map.of_real) : ℝ →ₗ[ℝ] ℂ) = linear_map.of_real := rfl

@[simp] lemma continuous_linear_map.of_real_apply (x : ℝ) :
  (continuous_linear_map.of_real : ℝ → ℂ) x = x := rfl

@[simp] lemma continuous_linear_map.of_real_norm :
  ∥continuous_linear_map.of_real∥ = 1 :=
le_antisymm (op_norm_le_bound _ zero_le_one $ λ z, by simp) $
calc 1 = ∥continuous_linear_map.of_real 1∥ : by simp
   ... ≤ ∥continuous_linear_map.of_real∥ : unit_le_op_norm _ _ (by simp)

lemma continuous_linear_map.of_real_isometry :
  isometry continuous_linear_map.of_real :=
continuous_linear_map.isometry_iff_norm_image_eq_norm.2 (λx, by simp)

end complex

section real_deriv_of_complex
/-! ### Differentiability of the restriction to `ℝ` of complex functions -/
open complex
variables {e : ℂ → ℂ} {e' : ℂ} {z : ℝ}

/-- If a complex function is differentiable at a real point, then the induced real function is also
differentiable at this point, with a derivative equal to the real part of the complex derivative. -/
theorem has_deriv_at.real_of_complex (h : has_deriv_at e e' z) :
  has_deriv_at (λx:ℝ, (e x).re) e'.re z :=
begin
  have A : has_fderiv_at continuous_linear_map.of_real continuous_linear_map.of_real z :=
    continuous_linear_map.of_real.has_fderiv_at,
  have B : has_fderiv_at e ((continuous_linear_map.smul_right 1 e' : ℂ →L[ℂ] ℂ).restrict_scalars ℝ)
    (continuous_linear_map.of_real z) :=
    (has_deriv_at_iff_has_fderiv_at.1 h).restrict_scalars ℝ,
  have C : has_fderiv_at continuous_linear_map.re continuous_linear_map.re
    (e (continuous_linear_map.of_real z)) := continuous_linear_map.re.has_fderiv_at,
  simpa using has_fderiv_at_iff_has_deriv_at.1 (C.comp z (B.comp z A)),
end

theorem times_cont_diff_at.real_of_complex {n : with_top ℕ} (h : times_cont_diff_at ℂ n e z) :
  times_cont_diff_at ℝ n (λ x : ℝ, (e x).re) z :=
begin
  have A : times_cont_diff_at ℝ n continuous_linear_map.of_real z,
    from continuous_linear_map.of_real.times_cont_diff.times_cont_diff_at,
  have B : times_cont_diff_at ℝ n e z := h.restrict_scalars ℝ,
  have C : times_cont_diff_at ℝ n continuous_linear_map.re (e z),
    from continuous_linear_map.re.times_cont_diff.times_cont_diff_at,
  exact C.comp z (B.comp z A)
end

theorem times_cont_diff.real_of_complex {n : with_top ℕ} (h : times_cont_diff ℂ n e) :
  times_cont_diff ℝ n (λ x : ℝ, (e x).re) :=
times_cont_diff_iff_times_cont_diff_at.2 $ λ x,
  h.times_cont_diff_at.real_of_complex

end real_deriv_of_complex
