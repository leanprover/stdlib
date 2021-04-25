/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import measure_theory.interval_integral

/-!
# Integration of specific interval integrals

This file contains proofs of the integrals of various simple functions, including `pow`, `exp`,
`inv`/`one_div`, `sin`, `cos`, and `λ x, 1 / (1 + x^2)`.

There are also facts about more complicated integrals:
* `sin x ^ n`: We prove a recursive formula for `sin x ^ (n + 2)` in terms of `sin x ^ n`,
  along with explicit product formulas for even and odd `n`.
* `cos x ^ 2 - sin x ^ 2`

With these lemmas, many simple integrals can be computed by `simp` or `norm_num`.
See `test/integration.lean` for specific examples.

This file is still being developed.
-/

open real set
open_locale real big_operators
variables {a b : ℝ}

namespace interval_integral
open measure_theory
variables {f : ℝ → ℝ} {μ ν : measure ℝ} [locally_finite_measure μ] (c d : ℝ)

@[simp]
lemma integral_const_mul : ∫ x in a..b, c * f x = c * ∫ x in a..b, f x :=
integral_smul c

@[simp]
lemma integral_mul_const : ∫ x in a..b, f x * c = (∫ x in a..b, f x) * c :=
by simp only [mul_comm, integral_const_mul]

@[simp]
lemma integral_div : ∫ x in a..b, f x / c = (∫ x in a..b, f x) / c :=
integral_mul_const c⁻¹

@[simp]
lemma mul_integral_comp_mul_right : c * ∫ x in a..b, f (x * c) = ∫ x in a*c..b*c, f x :=
smul_integral_comp_mul_right f c

@[simp]
lemma mul_integral_comp_mul_left : c * ∫ x in a..b, f (c * x) = ∫ x in c*a..c*b, f x :=
smul_integral_comp_mul_left f c

@[simp]
lemma inv_mul_integral_comp_div : c⁻¹ * ∫ x in a..b, f (x / c) = ∫ x in a/c..b/c, f x :=
inv_smul_integral_comp_div f c

@[simp]
lemma mul_integral_comp_mul_add : c * ∫ x in a..b, f (c * x + d) = ∫ x in c*a+d..c*b+d, f x :=
smul_integral_comp_mul_add f c d

@[simp]
lemma mul_integral_comp_add_mul : c * ∫ x in a..b, f (d + c * x) = ∫ x in d+c*a..d+c*b, f x :=
smul_integral_comp_add_mul f c d

@[simp]
lemma inv_mul_integral_comp_div_add : c⁻¹ * ∫ x in a..b, f (x / c + d) = ∫ x in a/c+d..b/c+d, f x :=
inv_smul_integral_comp_div_add f c d

@[simp]
lemma inv_mul_integral_comp_add_div : c⁻¹ * ∫ x in a..b, f (d + x / c) = ∫ x in d+a/c..d+b/c, f x :=
inv_smul_integral_comp_add_div f c d

@[simp]
lemma mul_integral_comp_mul_sub : c * ∫ x in a..b, f (c * x - d) = ∫ x in c*a-d..c*b-d, f x :=
smul_integral_comp_mul_sub f c d

@[simp]
lemma mul_integral_comp_sub_mul : c * ∫ x in a..b, f (d - c * x) = ∫ x in d-c*b..d-c*a, f x :=
smul_integral_comp_sub_mul f c d

@[simp]
lemma inv_mul_integral_comp_div_sub : c⁻¹ * ∫ x in a..b, f (x / c - d) = ∫ x in a/c-d..b/c-d, f x :=
inv_smul_integral_comp_div_sub f c d

@[simp]
lemma inv_mul_integral_comp_sub_div : c⁻¹ * ∫ x in a..b, f (d - x / c) = ∫ x in d-b/c..d-a/c, f x :=
inv_smul_integral_comp_sub_div f c d

@[simp]
lemma interval_integrable_pow (n : ℕ) : interval_integrable (λ x, x^n) μ a b :=
(continuous_pow n).interval_integrable a b

@[simp]
lemma interval_integrable_id : interval_integrable (λ x, x) μ a b :=
continuous_id.interval_integrable a b

@[simp]
lemma interval_integrable_const (c : ℝ) : interval_integrable (λ x, c) μ a b :=
continuous_const.interval_integrable a b

@[simp]
lemma interval_integrable.const_mul (c : ℝ) (h : interval_integrable f ν a b) :
  interval_integrable (λ x, c * f x) ν a b :=
by convert h.smul c

@[simp]
lemma interval_integrable.mul_const (c : ℝ) (h : interval_integrable f ν a b) :
  interval_integrable (λ x, f x * c) ν a b :=
by simp only [mul_comm, interval_integrable.const_mul c h]

@[simp]
lemma interval_integrable.div (c : ℝ) (h : interval_integrable f ν a b) :
  interval_integrable (λ x, f x / c) ν a b :=
interval_integrable.mul_const c⁻¹ h

lemma interval_integrable_one_div (h : ∀ x : ℝ, x ∈ interval a b → f x ≠ 0)
  (hf : continuous_on f (interval a b)) :
  interval_integrable (λ x, 1 / f x) μ a b :=
(continuous_on_const.div hf h).interval_integrable

@[simp]
lemma interval_integrable_inv (h : ∀ x : ℝ, x ∈ interval a b → f x ≠ 0)
  (hf : continuous_on f (interval a b)) :
  interval_integrable (λ x, (f x)⁻¹) μ a b :=
by simpa only [one_div] using interval_integrable_one_div h hf

@[simp]
lemma interval_integrable_exp : interval_integrable exp μ a b :=
continuous_exp.interval_integrable a b

@[simp]
lemma interval_integrable_sin : interval_integrable sin μ a b :=
continuous_sin.interval_integrable a b

@[simp]
lemma interval_integrable_cos : interval_integrable cos μ a b :=
continuous_cos.interval_integrable a b

lemma interval_integrable_one_div_one_add_sq : interval_integrable (λ x:ℝ, 1 / (1 + x^2)) μ a b :=
begin
  refine (continuous_const.div _ (λ x, _)).interval_integrable a b,
  { continuity },
  { nlinarith },
end

@[simp]
lemma interval_integrable_inv_one_add_sq : interval_integrable (λ x:ℝ, (1 + x^2)⁻¹) μ a b :=
by simpa only [one_div] using interval_integrable_one_div_one_add_sq

end interval_integral

open interval_integral

@[simp]
lemma integral_pow (n : ℕ) : ∫ x in a..b, x ^ n = (b^(n+1) - a^(n+1)) / (n + 1) :=
begin
  have hderiv : deriv (λ x : ℝ, x^(n + 1) / (n + 1)) = λ x, x ^ n,
  { have hne : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast nat.succ_ne_zero n,
    ext,
    simp [mul_div_assoc, mul_div_cancel' _ hne] },
  rw integral_deriv_eq_sub' _ hderiv;
  norm_num [div_sub_div_same, continuous_on_pow],
end

@[simp]
lemma integral_id : ∫ x in a..b, x = (b^2 - a^2) / 2 :=
by simpa using integral_pow 1

@[simp]
lemma integral_one : ∫ x in a..b, (1:ℝ) = b - a :=
by simp

@[simp]
lemma integral_exp : ∫ x in a..b, exp x = exp b - exp a :=
by rw integral_deriv_eq_sub'; norm_num [continuous_on_exp]

@[simp]
lemma integral_inv (h : (0:ℝ) ∉ interval a b) : ∫ x in a..b, x⁻¹ = log (b / a) :=
begin
  have h' := λ x hx, ne_of_mem_of_not_mem hx h,
  rw [integral_deriv_eq_sub' _ deriv_log' (λ x hx, differentiable_at_log (h' x hx))
        (continuous_on_inv'.mono (subset_compl_singleton_iff.mpr h)),
      log_div (h' b right_mem_interval) (h' a left_mem_interval)],
end

@[simp]
lemma integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) : ∫ x in a..b, x⁻¹ = log (b / a) :=
integral_inv $ not_mem_interval_of_lt ha hb

@[simp]
lemma integral_inv_of_neg (ha : a < 0) (hb : b < 0) : ∫ x in a..b, x⁻¹ = log (b / a) :=
integral_inv $ not_mem_interval_of_gt ha hb

lemma integral_one_div (h : (0:ℝ) ∉ interval a b) : ∫ x : ℝ in a..b, 1/x = log (b / a) :=
by simp only [one_div, integral_inv h]

lemma integral_one_div_of_pos (ha : 0 < a) (hb : 0 < b) : ∫ x : ℝ in a..b, 1/x = log (b / a) :=
by simp only [one_div, integral_inv_of_pos ha hb]

lemma integral_one_div_of_neg (ha : a < 0) (hb : b < 0) : ∫ x : ℝ in a..b, 1/x = log (b / a) :=
by simp only [one_div, integral_inv_of_neg ha hb]

@[simp]
lemma integral_sin : ∫ x in a..b, sin x = cos a - cos b :=
by rw integral_deriv_eq_sub' (λ x, -cos x); norm_num [continuous_on_sin]

lemma integral_sin_pow_aux (n : ℕ) : ∫ x in 0..π, sin x ^ (n + 2) =
  ((n + 1) * ∫ x in 0..π, sin x ^ n) - (n + 1) * ∫ x in 0..π, sin x ^ (n + 2) :=
begin
  have hv : ∀ x ∈ interval 0 π, has_deriv_at (-cos) (sin x) x,
  { intros, convert (has_deriv_at_cos x).neg, rw neg_neg },
  have hu : ∀ x ∈ interval 0 π, has_deriv_at (λ x, sin x ^ (n + 1)) ((n + 1) * cos x * sin x ^ n) x,
  { intros,
    convert (has_deriv_at_pow (n + 1) (sin x)).comp x (has_deriv_at_sin x) using 1,
    simp [mul_right_comm], },
  calc ∫ (x : ℝ) in 0..π, sin x ^ (n + 2)
      = ∫ (x : ℝ) in 0..π, sin x ^ (n + 1) * sin x : by { congr, ext, ring_nf }
  ... = ∫ (x : ℝ) in 0..π, cos x * (λ (x : ℝ), (↑n + 1) * cos x * sin x ^ n) x : by
  { simp [integral_mul_deriv_eq_deriv_mul hu hv (by continuity : continuous _).continuous_on
      (by continuity : continuous _).continuous_on] }
  ... = (↑n + 1) * ∫ (x : ℝ) in 0..π, cos x ^ 2 * sin x ^ n : by
  { rw ← integral_const_mul, congr, ext, simp only, ring }
  ... = (↑n + 1) * ∫ (x : ℝ) in 0..π, sin x ^ n - sin x ^ (n + 2) : by
  { simp [integral_const_mul, cos_square', sub_mul, ← pow_add, add_comm] }
  ... = _ - _ : by { rw [integral_sub, mul_sub],
    { exact ((continuous_pow n).comp continuous_sin).interval_integrable 0 π },
    { exact ((continuous_pow (n + 2)).comp continuous_sin).interval_integrable 0 π } },
end

lemma integral_sin_pow_succ_succ (n : ℕ) :
  ∫ x in 0..π, sin x ^ (n + 2) = (n + 1) / (n + 2) * ∫ x in 0..π, sin x ^ n :=
begin
  have : (n:ℝ) + 2 ≠ 0 := by exact_mod_cast nat.succ_ne_zero n.succ,
  field_simp,
  convert eq_sub_iff_add_eq.mp (integral_sin_pow_aux n),
  ring,
end

theorem integral_sin_pow_odd (n : ℕ) :
  ∫ x in 0..π, sin x ^ (2 * n + 1) = 2 * ∏ i in finset.range n, (2 * i + 2) / (2 * i + 3) :=
begin
  induction n with k ih,
  { norm_num },
  rw [finset.prod_range_succ_comm, mul_left_comm, ← ih, nat.mul_succ, integral_sin_pow_succ_succ],
  norm_cast,
end

theorem integral_sin_pow_even (n : ℕ) :
  ∫ x in 0..π, sin x ^ (2 * n) = π * ∏ i in finset.range n, (2 * i + 1) / (2 * i + 2) :=
begin
  induction n with k ih,
  { norm_num },
  rw [finset.prod_range_succ_comm, mul_left_comm, ← ih, nat.mul_succ, integral_sin_pow_succ_succ],
  norm_cast,
end

lemma integral_sin_pow_pos (n : ℕ) : 0 < ∫ x in 0..π, sin x ^ n :=
begin
  rcases nat.even_or_odd' n with ⟨k, h, h⟩;
  simp only [h, integral_sin_pow_even, integral_sin_pow_odd];
  refine mul_pos (by norm_num [pi_pos]) (finset.prod_pos (λ n hn, div_pos _ _));
  norm_cast;
  linarith,
end

@[simp]
lemma integral_cos : ∫ x in a..b, cos x = sin b - sin a :=
by rw integral_deriv_eq_sub'; norm_num [continuous_on_cos]

lemma integral_cos_sq_sub_sin_sq :
  ∫ x in a..b, cos x ^ 2 - sin x ^ 2 = sin b * cos b - sin a * cos a :=
by simpa only [pow_two, sub_eq_add_neg, neg_mul_eq_mul_neg] using integral_deriv_mul_eq_sub
  (λ x hx, has_deriv_at_sin x) (λ x hx, has_deriv_at_cos x) continuous_on_cos continuous_on_sin.neg

@[simp]
lemma integral_inv_one_add_sq : ∫ x : ℝ in a..b, (1 + x^2)⁻¹ = arctan b - arctan a :=
begin
  simp only [← one_div],
  refine integral_deriv_eq_sub' _ _ _ (continuous_const.div _ (λ x, _)).continuous_on,
  { norm_num },
  { norm_num },
  { continuity },
  { nlinarith },
end

lemma integral_one_div_one_add_sq : ∫ x : ℝ in a..b, 1 / (1 + x^2) = arctan b - arctan a :=
by simp

open measure_theory

@[simp]
lemma integral_cos_sq : ∫ x in a..b, cos x ^ 2 = (sin (2 * b) - sin (2 * a)) / 4 + (b - a) / 2 :=
begin
  have : interval_integrable (λ x : ℝ, cos (2*x)) volume a b,
  { apply interval_integrable.comp; continuity },
  simp [cos_square, this, integral_comp_mul_left],
  ring,
end

@[simp]
lemma integral_sin_sq : ∫ x in a..b, sin x ^ 2 = (sin (2 * a) - sin (2 * b)) / 4 + (b - a) / 2 :=
begin
  simp [sin_square, interval_integrable.comp (continuous_pow 2) continuous_cos],
  ring,
end
