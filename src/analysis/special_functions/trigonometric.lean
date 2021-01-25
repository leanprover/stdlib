/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import analysis.special_functions.exp_log
import data.set.intervals.infinite
import algebra.quadratic_discriminant
import ring_theory.polynomial.chebyshev.defs

/-!
# Trigonometric functions

## Main definitions

This file contains the following definitions:
* π, arcsin, arccos, arctan
* argument of a complex number
* logarithm on complex numbers

## Main statements

Many basic inequalities on trigonometric functions are established.

The continuity and differentiability of the usual trigonometric functions are proved, and their
derivatives are computed.

* `polynomial.chebyshev₁_complex_cos`: the `n`-th Chebyshev polynomial evaluates on `complex.cos θ`
  to the value `n * complex.cos θ`.

## Tags

log, sin, cos, tan, arcsin, arccos, arctan, angle, argument
-/

noncomputable theory
open_locale classical topological_space filter
open set filter

namespace complex

/-- The complex sine function is everywhere differentiable, with the derivative `cos x`. -/
lemma has_deriv_at_sin (x : ℂ) : has_deriv_at sin (cos x) x :=
begin
  simp only [cos, div_eq_mul_inv],
  convert ((((has_deriv_at_id x).neg.mul_const I).cexp.sub
    ((has_deriv_at_id x).mul_const I).cexp).mul_const I).mul_const (2:ℂ)⁻¹,
  simp only [function.comp, id],
  rw [sub_mul, mul_assoc, mul_assoc, I_mul_I, neg_one_mul, neg_neg, mul_one, one_mul, mul_assoc,
      I_mul_I, mul_neg_one, sub_neg_eq_add, add_comm]
end

lemma times_cont_diff_sin {n} : times_cont_diff ℂ n sin :=
(((times_cont_diff_neg.mul times_cont_diff_const).cexp.sub
  (times_cont_diff_id.mul times_cont_diff_const).cexp).mul times_cont_diff_const).div_const

lemma differentiable_sin : differentiable ℂ sin :=
λx, (has_deriv_at_sin x).differentiable_at

lemma differentiable_at_sin {x : ℂ} : differentiable_at ℂ sin x :=
differentiable_sin x

@[simp] lemma deriv_sin : deriv sin = cos :=
funext $ λ x, (has_deriv_at_sin x).deriv

lemma continuous_sin : continuous sin :=
differentiable_sin.continuous

lemma continuous_on_sin {s : set ℂ} : continuous_on sin s := continuous_sin.continuous_on

lemma measurable_sin : measurable sin := continuous_sin.measurable

/-- The complex cosine function is everywhere differentiable, with the derivative `-sin x`. -/
lemma has_deriv_at_cos (x : ℂ) : has_deriv_at cos (-sin x) x :=
begin
  simp only [sin, div_eq_mul_inv, neg_mul_eq_neg_mul],
  convert (((has_deriv_at_id x).mul_const I).cexp.add
    ((has_deriv_at_id x).neg.mul_const I).cexp).mul_const (2:ℂ)⁻¹,
  simp only [function.comp, id],
  ring
end

lemma times_cont_diff_cos {n} : times_cont_diff ℂ n cos :=
((times_cont_diff_id.mul times_cont_diff_const).cexp.add
  (times_cont_diff_neg.mul times_cont_diff_const).cexp).div_const

lemma differentiable_cos : differentiable ℂ cos :=
λx, (has_deriv_at_cos x).differentiable_at

lemma differentiable_at_cos {x : ℂ} : differentiable_at ℂ cos x :=
differentiable_cos x

lemma deriv_cos {x : ℂ} : deriv cos x = -sin x :=
(has_deriv_at_cos x).deriv

@[simp] lemma deriv_cos' : deriv cos = (λ x, -sin x) :=
funext $ λ x, deriv_cos

lemma continuous_cos : continuous cos :=
differentiable_cos.continuous

lemma continuous_on_cos {s : set ℂ} : continuous_on cos s := continuous_cos.continuous_on

lemma measurable_cos : measurable cos := continuous_cos.measurable

/-- The complex hyperbolic sine function is everywhere differentiable, with the derivative
`cosh x`. -/
lemma has_deriv_at_sinh (x : ℂ) : has_deriv_at sinh (cosh x) x :=
begin
  simp only [cosh, div_eq_mul_inv],
  convert ((has_deriv_at_exp x).sub (has_deriv_at_id x).neg.cexp).mul_const (2:ℂ)⁻¹,
  rw [id, mul_neg_one, sub_eq_add_neg, neg_neg]
end

lemma times_cont_diff_sinh {n} : times_cont_diff ℂ n sinh :=
(times_cont_diff_exp.sub times_cont_diff_neg.cexp).div_const

lemma differentiable_sinh : differentiable ℂ sinh :=
λx, (has_deriv_at_sinh x).differentiable_at

lemma differentiable_at_sinh {x : ℂ} : differentiable_at ℂ sinh x :=
differentiable_sinh x

@[simp] lemma deriv_sinh : deriv sinh = cosh :=
funext $ λ x, (has_deriv_at_sinh x).deriv

lemma continuous_sinh : continuous sinh :=
differentiable_sinh.continuous

lemma measurable_sinh : measurable sinh := continuous_sinh.measurable

/-- The complex hyperbolic cosine function is everywhere differentiable, with the derivative
`sinh x`. -/
lemma has_deriv_at_cosh (x : ℂ) : has_deriv_at cosh (sinh x) x :=
begin
  simp only [sinh, div_eq_mul_inv],
  convert ((has_deriv_at_exp x).add (has_deriv_at_id x).neg.cexp).mul_const (2:ℂ)⁻¹,
  rw [id, mul_neg_one, sub_eq_add_neg]
end

lemma times_cont_diff_cosh {n} : times_cont_diff ℂ n cosh :=
(times_cont_diff_exp.add times_cont_diff_neg.cexp).div_const

lemma differentiable_cosh : differentiable ℂ cosh :=
λx, (has_deriv_at_cosh x).differentiable_at

lemma differentiable_at_cosh {x : ℂ} : differentiable_at ℂ cos x :=
differentiable_cos x

@[simp] lemma deriv_cosh : deriv cosh = sinh :=
funext $ λ x, (has_deriv_at_cosh x).deriv

lemma continuous_cosh : continuous cosh :=
differentiable_cosh.continuous

lemma measurable_cosh : measurable cosh := continuous_cosh.measurable

end complex

section
/-! ### Simp lemmas for derivatives of `λ x, complex.cos (f x)` etc., `f : ℂ → ℂ` -/

variables {f : ℂ → ℂ} {f' x : ℂ} {s : set ℂ}

/-! #### `complex.cos` -/

lemma measurable.ccos {α : Type*} [measurable_space α] {f : α → ℂ} (hf : measurable f) :
  measurable (λ x, complex.cos (f x)) :=
complex.measurable_cos.comp hf

lemma has_deriv_at.ccos (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.cos (f x)) (- complex.sin (f x) * f') x :=
(complex.has_deriv_at_cos (f x)).comp x hf

lemma has_deriv_within_at.ccos (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.cos (f x)) (- complex.sin (f x) * f') s x :=
(complex.has_deriv_at_cos (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_ccos (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.cos (f x)) s x = - complex.sin (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.ccos.deriv_within hxs

@[simp] lemma deriv_ccos (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.cos (f x)) x = - complex.sin (f x) * (deriv f x) :=
hc.has_deriv_at.ccos.deriv

/-! #### `complex.sin` -/

lemma measurable.csin {α : Type*} [measurable_space α] {f : α → ℂ} (hf : measurable f) :
  measurable (λ x, complex.sin (f x)) :=
complex.measurable_sin.comp hf

lemma has_deriv_at.csin (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.sin (f x)) (complex.cos (f x) * f') x :=
(complex.has_deriv_at_sin (f x)).comp x hf

lemma has_deriv_within_at.csin (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.sin (f x)) (complex.cos (f x) * f') s x :=
(complex.has_deriv_at_sin (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_csin (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.sin (f x)) s x = complex.cos (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.csin.deriv_within hxs

@[simp] lemma deriv_csin (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.sin (f x)) x = complex.cos (f x) * (deriv f x) :=
hc.has_deriv_at.csin.deriv

/-! #### `complex.cosh` -/

lemma measurable.ccosh {α : Type*} [measurable_space α] {f : α → ℂ} (hf : measurable f) :
  measurable (λ x, complex.cosh (f x)) :=
complex.measurable_cosh.comp hf

lemma has_deriv_at.ccosh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.cosh (f x)) (complex.sinh (f x) * f') x :=
(complex.has_deriv_at_cosh (f x)).comp x hf

lemma has_deriv_within_at.ccosh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.cosh (f x)) (complex.sinh (f x) * f') s x :=
(complex.has_deriv_at_cosh (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_ccosh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.cosh (f x)) s x = complex.sinh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.ccosh.deriv_within hxs

@[simp] lemma deriv_ccosh (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.cosh (f x)) x = complex.sinh (f x) * (deriv f x) :=
hc.has_deriv_at.ccosh.deriv

/-! #### `complex.sinh` -/

lemma measurable.csinh {α : Type*} [measurable_space α] {f : α → ℂ} (hf : measurable f) :
  measurable (λ x, complex.sinh (f x)) :=
complex.measurable_sinh.comp hf

lemma has_deriv_at.csinh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.sinh (f x)) (complex.cosh (f x) * f') x :=
(complex.has_deriv_at_sinh (f x)).comp x hf

lemma has_deriv_within_at.csinh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.sinh (f x)) (complex.cosh (f x) * f') s x :=
(complex.has_deriv_at_sinh (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_csinh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.sinh (f x)) s x = complex.cosh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.csinh.deriv_within hxs

@[simp] lemma deriv_csinh (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.sinh (f x)) x = complex.cosh (f x) * (deriv f x) :=
hc.has_deriv_at.csinh.deriv

end

section
/-! ### Simp lemmas for derivatives of `λ x, complex.cos (f x)` etc., `f : E → ℂ` -/

variables {E : Type*} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : E →L[ℂ] ℂ}
  {x : E} {s : set E}

/-! #### `complex.cos` -/

lemma has_fderiv_at.ccos (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.cos (f x)) (- complex.sin (f x) • f') x :=
(complex.has_deriv_at_cos (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.ccos (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.cos (f x)) (- complex.sin (f x) • f') s x :=
(complex.has_deriv_at_cos (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.ccos (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.cos (f x)) s x :=
hf.has_fderiv_within_at.ccos.differentiable_within_at

@[simp] lemma differentiable_at.ccos (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.cos (f x)) x :=
hc.has_fderiv_at.ccos.differentiable_at

lemma differentiable_on.ccos (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.cos (f x)) s :=
λx h, (hc x h).ccos

@[simp] lemma differentiable.ccos (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.cos (f x)) :=
λx, (hc x).ccos

lemma fderiv_within_ccos (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  fderiv_within ℂ (λx, complex.cos (f x)) s x = - complex.sin (f x) • (fderiv_within ℂ f s x) :=
hf.has_fderiv_within_at.ccos.fderiv_within hxs

@[simp] lemma fderiv_ccos (hc : differentiable_at ℂ f x) :
  fderiv ℂ (λx, complex.cos (f x)) x = - complex.sin (f x) • (fderiv ℂ f x) :=
hc.has_fderiv_at.ccos.fderiv

lemma times_cont_diff.ccos {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.cos (f x)) :=
complex.times_cont_diff_cos.comp h

lemma times_cont_diff_at.ccos {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.cos (f x)) x :=
complex.times_cont_diff_cos.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.ccos {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.cos (f x)) s :=
complex.times_cont_diff_cos.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.ccos {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.cos (f x)) s x :=
complex.times_cont_diff_cos.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `complex.sin` -/

lemma has_fderiv_at.csin (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.sin (f x)) (complex.cos (f x) • f') x :=
(complex.has_deriv_at_sin (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.csin (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.sin (f x)) (complex.cos (f x) • f') s x :=
(complex.has_deriv_at_sin (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.csin (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.sin (f x)) s x :=
hf.has_fderiv_within_at.csin.differentiable_within_at

@[simp] lemma differentiable_at.csin (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.sin (f x)) x :=
hc.has_fderiv_at.csin.differentiable_at

lemma differentiable_on.csin (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.sin (f x)) s :=
λx h, (hc x h).csin

@[simp] lemma differentiable.csin (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.sin (f x)) :=
λx, (hc x).csin

lemma fderiv_within_csin (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  fderiv_within ℂ (λx, complex.sin (f x)) s x = complex.cos (f x) • (fderiv_within ℂ f s x) :=
hf.has_fderiv_within_at.csin.fderiv_within hxs

@[simp] lemma fderiv_csin (hc : differentiable_at ℂ f x) :
  fderiv ℂ (λx, complex.sin (f x)) x = complex.cos (f x) • (fderiv ℂ f x) :=
hc.has_fderiv_at.csin.fderiv

lemma times_cont_diff.csin {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.sin (f x)) :=
complex.times_cont_diff_sin.comp h

lemma times_cont_diff_at.csin {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.sin (f x)) x :=
complex.times_cont_diff_sin.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.csin {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.sin (f x)) s :=
complex.times_cont_diff_sin.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.csin {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.sin (f x)) s x :=
complex.times_cont_diff_sin.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `complex.cosh` -/

lemma has_fderiv_at.ccosh (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.cosh (f x)) (complex.sinh (f x) • f') x :=
(complex.has_deriv_at_cosh (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.ccosh (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.cosh (f x)) (complex.sinh (f x) • f') s x :=
(complex.has_deriv_at_cosh (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.ccosh (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.cosh (f x)) s x :=
hf.has_fderiv_within_at.ccosh.differentiable_within_at

@[simp] lemma differentiable_at.ccosh (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.cosh (f x)) x :=
hc.has_fderiv_at.ccosh.differentiable_at

lemma differentiable_on.ccosh (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.cosh (f x)) s :=
λx h, (hc x h).ccosh

@[simp] lemma differentiable.ccosh (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.cosh (f x)) :=
λx, (hc x).ccosh

lemma fderiv_within_ccosh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  fderiv_within ℂ (λx, complex.cosh (f x)) s x = complex.sinh (f x) • (fderiv_within ℂ f s x) :=
hf.has_fderiv_within_at.ccosh.fderiv_within hxs

@[simp] lemma fderiv_ccosh (hc : differentiable_at ℂ f x) :
  fderiv ℂ (λx, complex.cosh (f x)) x = complex.sinh (f x) • (fderiv ℂ f x) :=
hc.has_fderiv_at.ccosh.fderiv

lemma times_cont_diff.ccosh {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.cosh (f x)) :=
complex.times_cont_diff_cosh.comp h

lemma times_cont_diff_at.ccosh {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.cosh (f x)) x :=
complex.times_cont_diff_cosh.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.ccosh {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.cosh (f x)) s :=
complex.times_cont_diff_cosh.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.ccosh {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.cosh (f x)) s x :=
complex.times_cont_diff_cosh.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `complex.sinh` -/

lemma has_fderiv_at.csinh (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.sinh (f x)) (complex.cosh (f x) • f') x :=
(complex.has_deriv_at_sinh (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.csinh (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.sinh (f x)) (complex.cosh (f x) • f') s x :=
(complex.has_deriv_at_sinh (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.csinh (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.sinh (f x)) s x :=
hf.has_fderiv_within_at.csinh.differentiable_within_at

@[simp] lemma differentiable_at.csinh (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.sinh (f x)) x :=
hc.has_fderiv_at.csinh.differentiable_at

lemma differentiable_on.csinh (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.sinh (f x)) s :=
λx h, (hc x h).csinh

@[simp] lemma differentiable.csinh (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.sinh (f x)) :=
λx, (hc x).csinh

lemma fderiv_within_csinh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  fderiv_within ℂ (λx, complex.sinh (f x)) s x = complex.cosh (f x) • (fderiv_within ℂ f s x) :=
hf.has_fderiv_within_at.csinh.fderiv_within hxs

@[simp] lemma fderiv_csinh (hc : differentiable_at ℂ f x) :
  fderiv ℂ (λx, complex.sinh (f x)) x = complex.cosh (f x) • (fderiv ℂ f x) :=
hc.has_fderiv_at.csinh.fderiv

lemma times_cont_diff.csinh {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.sinh (f x)) :=
complex.times_cont_diff_sinh.comp h

lemma times_cont_diff_at.csinh {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.sinh (f x)) x :=
complex.times_cont_diff_sinh.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.csinh {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.sinh (f x)) s :=
complex.times_cont_diff_sinh.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.csinh {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.sinh (f x)) s x :=
complex.times_cont_diff_sinh.times_cont_diff_at.comp_times_cont_diff_within_at x hf

end

namespace real

variables {x y z : ℝ}

lemma has_deriv_at_sin (x : ℝ) : has_deriv_at sin (cos x) x :=
(complex.has_deriv_at_sin x).real_of_complex

lemma times_cont_diff_sin {n} : times_cont_diff ℝ n sin :=
complex.times_cont_diff_sin.real_of_complex

lemma differentiable_sin : differentiable ℝ sin :=
λx, (has_deriv_at_sin x).differentiable_at

lemma differentiable_at_sin : differentiable_at ℝ sin x :=
differentiable_sin x

@[simp] lemma deriv_sin : deriv sin = cos :=
funext $ λ x, (has_deriv_at_sin x).deriv

lemma continuous_sin : continuous sin :=
differentiable_sin.continuous

lemma measurable_sin : measurable sin := continuous_sin.measurable

lemma has_deriv_at_cos (x : ℝ) : has_deriv_at cos (-sin x) x :=
(complex.has_deriv_at_cos x).real_of_complex

lemma times_cont_diff_cos {n} : times_cont_diff ℝ n cos :=
complex.times_cont_diff_cos.real_of_complex

lemma differentiable_cos : differentiable ℝ cos :=
λx, (has_deriv_at_cos x).differentiable_at

lemma differentiable_at_cos : differentiable_at ℝ cos x :=
differentiable_cos x

lemma deriv_cos : deriv cos x = - sin x :=
(has_deriv_at_cos x).deriv

@[simp] lemma deriv_cos' : deriv cos = (λ x, - sin x) :=
funext $ λ _, deriv_cos

lemma continuous_cos : continuous cos :=
differentiable_cos.continuous

lemma continuous_on_cos {s} : continuous_on cos s := continuous_cos.continuous_on

lemma measurable_cos : measurable cos := continuous_cos.measurable

lemma has_deriv_at_sinh (x : ℝ) : has_deriv_at sinh (cosh x) x :=
(complex.has_deriv_at_sinh x).real_of_complex

lemma times_cont_diff_sinh {n} : times_cont_diff ℝ n sinh :=
complex.times_cont_diff_sinh.real_of_complex

lemma differentiable_sinh : differentiable ℝ sinh :=
λx, (has_deriv_at_sinh x).differentiable_at

lemma differentiable_at_sinh : differentiable_at ℝ sinh x :=
differentiable_sinh x

@[simp] lemma deriv_sinh : deriv sinh = cosh :=
funext $ λ x, (has_deriv_at_sinh x).deriv

lemma continuous_sinh : continuous sinh :=
differentiable_sinh.continuous

lemma measurable_sinh : measurable sinh := continuous_sinh.measurable

lemma has_deriv_at_cosh (x : ℝ) : has_deriv_at cosh (sinh x) x :=
(complex.has_deriv_at_cosh x).real_of_complex

lemma times_cont_diff_cosh {n} : times_cont_diff ℝ n cosh :=
complex.times_cont_diff_cosh.real_of_complex

lemma differentiable_cosh : differentiable ℝ cosh :=
λx, (has_deriv_at_cosh x).differentiable_at

lemma differentiable_at_cosh : differentiable_at ℝ cosh x :=
differentiable_cosh x

@[simp] lemma deriv_cosh : deriv cosh = sinh :=
funext $ λ x, (has_deriv_at_cosh x).deriv

lemma continuous_cosh : continuous cosh :=
differentiable_cosh.continuous

lemma measurable_cosh : measurable cosh := continuous_cosh.measurable

/-- `sinh` is strictly monotone. -/
lemma sinh_strict_mono : strict_mono sinh :=
strict_mono_of_deriv_pos differentiable_sinh (by { rw [real.deriv_sinh], exact cosh_pos })

end real

section
/-! ### Simp lemmas for derivatives of `λ x, real.cos (f x)` etc., `f : ℝ → ℝ` -/

variables {f : ℝ → ℝ} {f' x : ℝ} {s : set ℝ}

/-! #### `real.cos` -/

lemma measurable.cos {α : Type*} [measurable_space α] {f : α → ℝ}  (hf : measurable f) :
  measurable (λ x, real.cos (f x)) :=
real.measurable_cos.comp hf

lemma has_deriv_at.cos (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.cos (f x)) (- real.sin (f x) * f') x :=
(real.has_deriv_at_cos (f x)).comp x hf

lemma has_deriv_within_at.cos (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.cos (f x)) (- real.sin (f x) * f') s x :=
(real.has_deriv_at_cos (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_cos (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.cos (f x)) s x = - real.sin (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.cos.deriv_within hxs

@[simp] lemma deriv_cos (hc : differentiable_at ℝ f x) :
  deriv (λx, real.cos (f x)) x = - real.sin (f x) * (deriv f x) :=
hc.has_deriv_at.cos.deriv

/-! #### `real.sin` -/

lemma measurable.sin {α : Type*} [measurable_space α] {f : α → ℝ}  (hf : measurable f) :
  measurable (λ x, real.sin (f x)) :=
real.measurable_sin.comp hf

lemma has_deriv_at.sin (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.sin (f x)) (real.cos (f x) * f') x :=
(real.has_deriv_at_sin (f x)).comp x hf

lemma has_deriv_within_at.sin (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.sin (f x)) (real.cos (f x) * f') s x :=
(real.has_deriv_at_sin (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_sin (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.sin (f x)) s x = real.cos (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.sin.deriv_within hxs

@[simp] lemma deriv_sin (hc : differentiable_at ℝ f x) :
  deriv (λx, real.sin (f x)) x = real.cos (f x) * (deriv f x) :=
hc.has_deriv_at.sin.deriv

/-! #### `real.cosh` -/

lemma measurable.cosh {α : Type*} [measurable_space α] {f : α → ℝ}  (hf : measurable f) :
  measurable (λ x, real.cosh (f x)) :=
real.measurable_cosh.comp hf

lemma has_deriv_at.cosh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.cosh (f x)) (real.sinh (f x) * f') x :=
(real.has_deriv_at_cosh (f x)).comp x hf

lemma has_deriv_within_at.cosh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.cosh (f x)) (real.sinh (f x) * f') s x :=
(real.has_deriv_at_cosh (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_cosh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.cosh (f x)) s x = real.sinh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.cosh.deriv_within hxs

@[simp] lemma deriv_cosh (hc : differentiable_at ℝ f x) :
  deriv (λx, real.cosh (f x)) x = real.sinh (f x) * (deriv f x) :=
hc.has_deriv_at.cosh.deriv

/-! #### `real.sinh` -/

lemma measurable.sinh {α : Type*} [measurable_space α] {f : α → ℝ}  (hf : measurable f) :
  measurable (λ x, real.sinh (f x)) :=
real.measurable_sinh.comp hf

lemma has_deriv_at.sinh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.sinh (f x)) (real.cosh (f x) * f') x :=
(real.has_deriv_at_sinh (f x)).comp x hf

lemma has_deriv_within_at.sinh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.sinh (f x)) (real.cosh (f x) * f') s x :=
(real.has_deriv_at_sinh (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_sinh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.sinh (f x)) s x = real.cosh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.sinh.deriv_within hxs

@[simp] lemma deriv_sinh (hc : differentiable_at ℝ f x) :
  deriv (λx, real.sinh (f x)) x = real.cosh (f x) * (deriv f x) :=
hc.has_deriv_at.sinh.deriv

end

section

/-! ### Simp lemmas for derivatives of `λ x, real.cos (f x)` etc., `f : E → ℝ` -/

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ}
  {x : E} {s : set E}

/-! #### `real.cos` -/

lemma has_fderiv_at.cos (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.cos (f x)) (- real.sin (f x) • f') x :=
(real.has_deriv_at_cos (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.cos (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.cos (f x)) (- real.sin (f x) • f') s x :=
(real.has_deriv_at_cos (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.cos (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.cos (f x)) s x :=
hf.has_fderiv_within_at.cos.differentiable_within_at

@[simp] lemma differentiable_at.cos (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.cos (f x)) x :=
hc.has_fderiv_at.cos.differentiable_at

lemma differentiable_on.cos (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.cos (f x)) s :=
λx h, (hc x h).cos

@[simp] lemma differentiable.cos (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.cos (f x)) :=
λx, (hc x).cos

lemma fderiv_within_cos (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.cos (f x)) s x = - real.sin (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.cos.fderiv_within hxs

@[simp] lemma fderiv_cos (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.cos (f x)) x = - real.sin (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.cos.fderiv

lemma times_cont_diff.cos {n} (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.cos (f x)) :=
real.times_cont_diff_cos.comp h

lemma times_cont_diff_at.cos {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.cos (f x)) x :=
real.times_cont_diff_cos.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.cos {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.cos (f x)) s :=
real.times_cont_diff_cos.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.cos {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.cos (f x)) s x :=
real.times_cont_diff_cos.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `real.sin` -/

lemma has_fderiv_at.sin (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.sin (f x)) (real.cos (f x) • f') x :=
(real.has_deriv_at_sin (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.sin (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.sin (f x)) (real.cos (f x) • f') s x :=
(real.has_deriv_at_sin (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.sin (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.sin (f x)) s x :=
hf.has_fderiv_within_at.sin.differentiable_within_at

@[simp] lemma differentiable_at.sin (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.sin (f x)) x :=
hc.has_fderiv_at.sin.differentiable_at

lemma differentiable_on.sin (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.sin (f x)) s :=
λx h, (hc x h).sin

@[simp] lemma differentiable.sin (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.sin (f x)) :=
λx, (hc x).sin

lemma fderiv_within_sin (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.sin (f x)) s x = real.cos (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.sin.fderiv_within hxs

@[simp] lemma fderiv_sin (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.sin (f x)) x = real.cos (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.sin.fderiv

lemma times_cont_diff.sin {n} (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.sin (f x)) :=
real.times_cont_diff_sin.comp h

lemma times_cont_diff_at.sin {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.sin (f x)) x :=
real.times_cont_diff_sin.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.sin {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.sin (f x)) s :=
real.times_cont_diff_sin.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.sin {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.sin (f x)) s x :=
real.times_cont_diff_sin.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `real.cosh` -/

lemma has_fderiv_at.cosh (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.cosh (f x)) (real.sinh (f x) • f') x :=
(real.has_deriv_at_cosh (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.cosh (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.cosh (f x)) (real.sinh (f x) • f') s x :=
(real.has_deriv_at_cosh (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.cosh (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.cosh (f x)) s x :=
hf.has_fderiv_within_at.cosh.differentiable_within_at

@[simp] lemma differentiable_at.cosh (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.cosh (f x)) x :=
hc.has_fderiv_at.cosh.differentiable_at

lemma differentiable_on.cosh (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.cosh (f x)) s :=
λx h, (hc x h).cosh

@[simp] lemma differentiable.cosh (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.cosh (f x)) :=
λx, (hc x).cosh

lemma fderiv_within_cosh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.cosh (f x)) s x = real.sinh (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.cosh.fderiv_within hxs

@[simp] lemma fderiv_cosh (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.cosh (f x)) x = real.sinh (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.cosh.fderiv

lemma times_cont_diff.cosh {n} (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.cosh (f x)) :=
real.times_cont_diff_cosh.comp h

lemma times_cont_diff_at.cosh {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.cosh (f x)) x :=
real.times_cont_diff_cosh.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.cosh {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.cosh (f x)) s :=
real.times_cont_diff_cosh.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.cosh {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.cosh (f x)) s x :=
real.times_cont_diff_cosh.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `real.sinh` -/

lemma has_fderiv_at.sinh (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.sinh (f x)) (real.cosh (f x) • f') x :=
(real.has_deriv_at_sinh (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.sinh (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.sinh (f x)) (real.cosh (f x) • f') s x :=
(real.has_deriv_at_sinh (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.sinh (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.sinh (f x)) s x :=
hf.has_fderiv_within_at.sinh.differentiable_within_at

@[simp] lemma differentiable_at.sinh (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.sinh (f x)) x :=
hc.has_fderiv_at.sinh.differentiable_at

lemma differentiable_on.sinh (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.sinh (f x)) s :=
λx h, (hc x h).sinh

@[simp] lemma differentiable.sinh (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.sinh (f x)) :=
λx, (hc x).sinh

lemma fderiv_within_sinh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.sinh (f x)) s x = real.cosh (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.sinh.fderiv_within hxs

@[simp] lemma fderiv_sinh (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.sinh (f x)) x = real.cosh (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.sinh.fderiv

lemma times_cont_diff.sinh {n} (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.sinh (f x)) :=
real.times_cont_diff_sinh.comp h

lemma times_cont_diff_at.sinh {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.sinh (f x)) x :=
real.times_cont_diff_sinh.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.sinh {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.sinh (f x)) s :=
real.times_cont_diff_sinh.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.sinh {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.sinh (f x)) s x :=
real.times_cont_diff_sinh.times_cont_diff_at.comp_times_cont_diff_within_at x hf

end

namespace real

lemma exists_cos_eq_zero : 0 ∈ cos '' Icc (1:ℝ) 2 :=
intermediate_value_Icc' (by norm_num) continuous_on_cos
  ⟨le_of_lt cos_two_neg, le_of_lt cos_one_pos⟩

/-- The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2], from
which one can derive all its properties. For explicit bounds on π, see `data.real.pi`. -/
noncomputable def pi : ℝ := 2 * classical.some exists_cos_eq_zero

localized "notation `π` := real.pi" in real

@[simp] lemma cos_pi_div_two : cos (π / 2) = 0 :=
by rw [pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).2

lemma one_le_pi_div_two : (1 : ℝ) ≤ π / 2 :=
by rw [pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).1.1

lemma pi_div_two_le_two : π / 2 ≤ 2 :=
by rw [pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).1.2

lemma two_le_pi : (2 : ℝ) ≤ π :=
(div_le_div_right (show (0 : ℝ) < 2, by norm_num)).1
  (by rw div_self (@two_ne_zero' ℝ _ _ _); exact one_le_pi_div_two)

lemma pi_le_four : π ≤ 4 :=
(div_le_div_right (show (0 : ℝ) < 2, by norm_num)).1
  (calc π / 2 ≤ 2 : pi_div_two_le_two
    ... = 4 / 2 : by norm_num)

lemma pi_pos : 0 < π :=
lt_of_lt_of_le (by norm_num) two_le_pi

lemma pi_ne_zero : π ≠ 0 :=
ne_of_gt pi_pos

lemma pi_div_two_pos : 0 < π / 2 :=
half_pos pi_pos

lemma two_pi_pos : 0 < 2 * π :=
by linarith [pi_pos]

@[simp] lemma sin_pi : sin π = 0 :=
by rw [← mul_div_cancel_left π (@two_ne_zero ℝ _ _), two_mul, add_div,
    sin_add, cos_pi_div_two]; simp

@[simp] lemma cos_pi : cos π = -1 :=
by rw [← mul_div_cancel_left π (@two_ne_zero ℝ _ _), mul_div_assoc,
    cos_two_mul, cos_pi_div_two];
  simp [bit0, pow_add]

@[simp] lemma sin_two_pi : sin (2 * π) = 0 :=
by simp [two_mul, sin_add]

@[simp] lemma cos_two_pi : cos (2 * π) = 1 :=
by simp [two_mul, cos_add]

lemma sin_add_pi (x : ℝ) : sin (x + π) = -sin x :=
by simp [sin_add]

lemma sin_add_two_pi (x : ℝ) : sin (x + 2 * π) = sin x :=
by simp [sin_add_pi, sin_add, sin_two_pi, cos_two_pi]

lemma cos_add_two_pi (x : ℝ) : cos (x + 2 * π) = cos x :=
by simp [cos_add, cos_two_pi, sin_two_pi]

lemma sin_pi_sub (x : ℝ) : sin (π - x) = sin x :=
by simp [sub_eq_add_neg, sin_add]

lemma cos_add_pi (x : ℝ) : cos (x + π) = -cos x :=
by simp [cos_add]

lemma cos_pi_sub (x : ℝ) : cos (π - x) = -cos x :=
by simp [sub_eq_add_neg, cos_add]

lemma sin_pos_of_pos_of_lt_pi {x : ℝ} (h0x : 0 < x) (hxp : x < π) : 0 < sin x :=
if hx2 : x ≤ 2 then sin_pos_of_pos_of_le_two h0x hx2
else
  have (2 : ℝ) + 2 = 4, from rfl,
  have π - x ≤ 2, from sub_le_iff_le_add.2
    (le_trans pi_le_four (this ▸ add_le_add_left (le_of_not_ge hx2) _)),
  sin_pi_sub x ▸ sin_pos_of_pos_of_le_two (sub_pos.2 hxp) this

lemma sin_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 π) : 0 < sin x :=
sin_pos_of_pos_of_lt_pi hx.1 hx.2

lemma sin_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ Icc 0 π) : 0 ≤ sin x :=
begin
  rw ← closure_Ioo pi_pos at hx,
  exact closure_lt_subset_le continuous_const continuous_sin
    (closure_mono (λ y, sin_pos_of_mem_Ioo) hx)
end

lemma sin_nonneg_of_nonneg_of_le_pi {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π) : 0 ≤ sin x :=
sin_nonneg_of_mem_Icc ⟨h0x, hxp⟩

lemma sin_neg_of_neg_of_neg_pi_lt {x : ℝ} (hx0 : x < 0) (hpx : -π < x) : sin x < 0 :=
neg_pos.1 $ sin_neg x ▸ sin_pos_of_pos_of_lt_pi (neg_pos.2 hx0) (neg_lt.1 hpx)

lemma sin_nonpos_of_nonnpos_of_neg_pi_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -π ≤ x) : sin x ≤ 0 :=
neg_nonneg.1 $ sin_neg x ▸ sin_nonneg_of_nonneg_of_le_pi (neg_nonneg.2 hx0) (neg_le.1 hpx)

@[simp] lemma sin_pi_div_two : sin (π / 2) = 1 :=
have sin (π / 2) = 1 ∨ sin (π / 2) = -1 :=
by simpa [pow_two, mul_self_eq_one_iff] using sin_sq_add_cos_sq (π / 2),
this.resolve_right
  (λ h, (show ¬(0 : ℝ) < -1, by norm_num) $
    h ▸ sin_pos_of_pos_of_lt_pi pi_div_two_pos (half_lt_self pi_pos))

lemma sin_add_pi_div_two (x : ℝ) : sin (x + π / 2) = cos x :=
by simp [sin_add]

lemma sin_sub_pi_div_two (x : ℝ) : sin (x - π / 2) = -cos x :=
by simp [sub_eq_add_neg, sin_add]

lemma sin_pi_div_two_sub (x : ℝ) : sin (π / 2 - x) = cos x :=
by simp [sub_eq_add_neg, sin_add]

lemma cos_add_pi_div_two (x : ℝ) : cos (x + π / 2) = -sin x :=
by simp [cos_add]

lemma cos_sub_pi_div_two (x : ℝ) : cos (x - π / 2) = sin x :=
by simp [sub_eq_add_neg, cos_add]

lemma cos_pi_div_two_sub (x : ℝ) : cos (π / 2 - x) = sin x :=
by rw [← cos_neg, neg_sub, cos_sub_pi_div_two]

lemma cos_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) : 0 < cos x :=
sin_add_pi_div_two x ▸ sin_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma cos_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) : 0 ≤ cos x :=
sin_add_pi_div_two x ▸ sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma cos_neg_of_pi_div_two_lt_of_lt {x : ℝ} (hx₁ : π / 2 < x) (hx₂ : x < π + π / 2) : cos x < 0 :=
neg_pos.1 $ cos_pi_sub x ▸ cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

lemma cos_nonpos_of_pi_div_two_le_of_le {x : ℝ} (hx₁ : π / 2 ≤ x) (hx₂ : x ≤ π + π / 2) :
  cos x ≤ 0 :=
neg_nonneg.1 $ cos_pi_sub x ▸ cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

lemma sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
by induction n; simp [add_mul, sin_add, *]

lemma sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
by cases n; simp [add_mul, sin_add, *, sin_nat_mul_pi]

lemma cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
by induction n; simp [*, mul_add, cos_add, add_mul, cos_two_pi, sin_two_pi]

lemma cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
by cases n; simp only [cos_nat_mul_two_pi, int.of_nat_eq_coe,
  int.neg_succ_of_nat_coe, int.cast_coe_nat, int.cast_neg,
  (neg_mul_eq_neg_mul _ _).symm, cos_neg]

lemma cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 :=
by simp [cos_add, sin_add, cos_int_mul_two_pi]

lemma sin_eq_zero_iff_of_lt_of_lt {x : ℝ} (hx₁ : -π < x) (hx₂ : x < π) :
  sin x = 0 ↔ x = 0 :=
⟨λ h, le_antisymm
    (le_of_not_gt (λ h0, lt_irrefl (0 : ℝ) $
      calc 0 < sin x : sin_pos_of_pos_of_lt_pi h0 hx₂
        ... = 0 : h))
    (le_of_not_gt (λ h0, lt_irrefl (0 : ℝ) $
      calc 0 = sin x : h.symm
        ... < 0 : sin_neg_of_neg_of_neg_pi_lt h0 hx₁)),
  λ h, by simp [h]⟩

lemma sin_eq_zero_iff {x : ℝ} : sin x = 0 ↔ ∃ n : ℤ, (n : ℝ) * π = x :=
⟨λ h, ⟨⌊x / π⌋, le_antisymm (sub_nonneg.1 (sub_floor_div_mul_nonneg _ pi_pos))
  (sub_nonpos.1 $ le_of_not_gt $ λ h₃,
    (sin_pos_of_pos_of_lt_pi h₃ (sub_floor_div_mul_lt _ pi_pos)).ne
    (by simp [sub_eq_add_neg, sin_add, h, sin_int_mul_pi]))⟩,
  λ ⟨n, hn⟩, hn ▸ sin_int_mul_pi _⟩

lemma sin_ne_zero_iff {x : ℝ} : sin x ≠ 0 ↔ ∀ n : ℤ, (n : ℝ) * π ≠ x :=
by rw [← not_exists, not_iff_not, sin_eq_zero_iff]

lemma sin_eq_zero_iff_cos_eq {x : ℝ} : sin x = 0 ↔ cos x = 1 ∨ cos x = -1 :=
by rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq x,
    pow_two, pow_two, ← sub_eq_iff_eq_add, sub_self];
  exact ⟨λ h, by rw [h, mul_zero], eq_zero_of_mul_self_eq_zero ∘ eq.symm⟩

lemma cos_eq_one_iff (x : ℝ) : cos x = 1 ↔ ∃ n : ℤ, (n : ℝ) * (2 * π) = x :=
⟨λ h, let ⟨n, hn⟩ := sin_eq_zero_iff.1 (sin_eq_zero_iff_cos_eq.2 (or.inl h)) in
    ⟨n / 2, (int.mod_two_eq_zero_or_one n).elim
      (λ hn0, by rwa [← mul_assoc, ← @int.cast_two ℝ, ← int.cast_mul, int.div_mul_cancel
        ((int.dvd_iff_mod_eq_zero _ _).2 hn0)])
      (λ hn1, by rw [← int.mod_add_div n 2, hn1, int.cast_add, int.cast_one, add_mul,
          one_mul, add_comm, mul_comm (2 : ℤ), int.cast_mul, mul_assoc, int.cast_two] at hn;
        rw [← hn, cos_int_mul_two_pi_add_pi] at h;
        exact absurd h (by norm_num))⟩,
  λ ⟨n, hn⟩, hn ▸ cos_int_mul_two_pi _⟩

lemma cos_eq_one_iff_of_lt_of_lt {x : ℝ} (hx₁ : -(2 * π) < x) (hx₂ : x < 2 * π) :
  cos x = 1 ↔ x = 0 :=
⟨λ h,
    begin
      rcases (cos_eq_one_iff _).1 h with ⟨n, rfl⟩,
      rw [mul_lt_iff_lt_one_left two_pi_pos] at hx₂,
      rw [neg_lt, neg_mul_eq_neg_mul, mul_lt_iff_lt_one_left two_pi_pos] at hx₁,
      norm_cast at hx₁ hx₂,
      obtain rfl : n = 0, by omega,
      simp
    end,
  λ h, by simp [h]⟩

lemma cos_lt_cos_of_nonneg_of_le_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π / 2)
  (hxy : x < y) :
  cos y < cos x :=
begin
  rw [← sub_lt_zero, cos_sub_cos],
  have : 0 < sin ((y + x) / 2),
  { refine sin_pos_of_pos_of_lt_pi _ _; linarith },
  have : 0 < sin ((y - x) / 2),
  { refine sin_pos_of_pos_of_lt_pi _ _; linarith },
  nlinarith,
end

lemma cos_lt_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x < y) :
  cos y < cos x :=
match (le_total x (π / 2) : x ≤ π / 2 ∨ π / 2 ≤ x), le_total y (π / 2) with
| or.inl hx, or.inl hy := cos_lt_cos_of_nonneg_of_le_pi_div_two hx₁ hy hxy
| or.inl hx, or.inr hy := (lt_or_eq_of_le hx).elim
  (λ hx, calc cos y ≤ 0 : cos_nonpos_of_pi_div_two_le_of_le hy (by linarith [pi_pos])
    ... < cos x : cos_pos_of_mem_Ioo ⟨by linarith, hx⟩)
  (λ hx, calc cos y < 0 : cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [pi_pos])
    ... = cos x : by rw [hx, cos_pi_div_two])
| or.inr hx, or.inl hy := by linarith
| or.inr hx, or.inr hy := neg_lt_neg_iff.1 (by rw [← cos_pi_sub, ← cos_pi_sub];
  apply cos_lt_cos_of_nonneg_of_le_pi_div_two; linarith)
end

lemma strict_mono_decr_on_cos : strict_mono_decr_on cos (Icc 0 π) :=
λ x hx y hy hxy, cos_lt_cos_of_nonneg_of_le_pi hx.1 hy.2 hxy

lemma cos_le_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x ≤ y) :
  cos y ≤ cos x :=
(strict_mono_decr_on_cos.le_iff_le ⟨hx₁.trans hxy, hy₂⟩ ⟨hx₁, hxy.trans hy₂⟩).2 hxy

lemma sin_lt_sin_of_lt_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x)
  (hy₂ : y ≤ π / 2) (hxy : x < y) : sin x < sin y :=
by rw [← cos_sub_pi_div_two, ← cos_sub_pi_div_two, ← cos_neg (x - _), ← cos_neg (y - _)];
  apply cos_lt_cos_of_nonneg_of_le_pi; linarith

lemma strict_mono_incr_on_sin : strict_mono_incr_on sin (Icc (-(π / 2)) (π / 2)) :=
λ x hx y hy hxy, sin_lt_sin_of_lt_of_le_pi_div_two hx.1 hy.2 hxy

lemma sin_le_sin_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x)
  (hy₂ : y ≤ π / 2) (hxy : x ≤ y) : sin x ≤ sin y :=
(strict_mono_incr_on_sin.le_iff_le ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩).2 hxy

lemma inj_on_sin : inj_on sin (Icc (-(π / 2)) (π / 2)) :=
strict_mono_incr_on_sin.inj_on

lemma inj_on_cos : inj_on cos (Icc 0 π) := strict_mono_decr_on_cos.inj_on

lemma surj_on_sin : surj_on sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) :=
by simpa only [sin_neg, sin_pi_div_two]
  using intermediate_value_Icc (neg_le_self pi_div_two_pos.le) continuous_sin.continuous_on

lemma surj_on_cos : surj_on cos (Icc 0 π) (Icc (-1) 1) :=
by simpa only [cos_zero, cos_pi]
  using intermediate_value_Icc' pi_pos.le continuous_cos.continuous_on

lemma sin_mem_Icc (x : ℝ) : sin x ∈ Icc (-1 : ℝ) 1 := ⟨neg_one_le_sin x, sin_le_one x⟩

lemma cos_mem_Icc (x : ℝ) : cos x ∈ Icc (-1 : ℝ) 1 := ⟨neg_one_le_cos x, cos_le_one x⟩

lemma maps_to_sin (s : set ℝ) : maps_to sin s (Icc (-1 : ℝ) 1) := λ x _, sin_mem_Icc x

lemma maps_to_cos (s : set ℝ) : maps_to cos s (Icc (-1 : ℝ) 1) := λ x _, cos_mem_Icc x

lemma bij_on_sin : bij_on sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) :=
⟨maps_to_sin _, inj_on_sin, surj_on_sin⟩

lemma bij_on_cos : bij_on cos (Icc 0 π) (Icc (-1) 1) :=
⟨maps_to_cos _, inj_on_cos, surj_on_cos⟩

@[simp] lemma range_cos : range cos = (Icc (-1) 1 : set ℝ) :=
subset.antisymm (range_subset_iff.2 cos_mem_Icc) surj_on_cos.subset_range

@[simp] lemma range_sin : range sin = (Icc (-1) 1 : set ℝ) :=
subset.antisymm (range_subset_iff.2 sin_mem_Icc) surj_on_sin.subset_range

lemma range_cos_infinite : (range real.cos).infinite :=
by { rw real.range_cos, exact Icc.infinite (by norm_num) }

lemma range_sin_infinite : (range real.sin).infinite :=
by { rw real.range_sin, exact Icc.infinite (by norm_num) }

lemma sin_lt {x : ℝ} (h : 0 < x) : sin x < x :=
begin
  cases le_or_gt x 1 with h' h',
  { have hx : abs x = x := abs_of_nonneg (le_of_lt h),
    have : abs x ≤ 1, rwa [hx],
    have := sin_bound this, rw [abs_le] at this,
    have := this.2, rw [sub_le_iff_le_add', hx] at this,
    apply lt_of_le_of_lt this, rw [sub_add], apply lt_of_lt_of_le _ (le_of_eq (sub_zero x)),
    apply sub_lt_sub_left, rw [sub_pos, div_eq_mul_inv (x ^ 3)], apply mul_lt_mul',
    { rw [pow_succ x 3], refine le_trans _ (le_of_eq (one_mul _)),
      rw mul_le_mul_right, exact h', apply pow_pos h },
    norm_num, norm_num, apply pow_pos h },
  exact lt_of_le_of_lt (sin_le_one x) h'
end

/- note 1: this inequality is not tight, the tighter inequality is sin x > x - x ^ 3 / 6.
   note 2: this is also true for x > 1, but it's nontrivial for x just above 1. -/
lemma sin_gt_sub_cube {x : ℝ} (h : 0 < x) (h' : x ≤ 1) : x - x ^ 3 / 4 < sin x :=
begin
  have hx : abs x = x := abs_of_nonneg (le_of_lt h),
  have : abs x ≤ 1, rwa [hx],
  have := sin_bound this, rw [abs_le] at this,
  have := this.1, rw [le_sub_iff_add_le, hx] at this,
  refine lt_of_lt_of_le _ this,
  rw [add_comm, sub_add, sub_neg_eq_add], apply sub_lt_sub_left,
  apply add_lt_of_lt_sub_left,
  rw (show x ^ 3 / 4 - x ^ 3 / 6 = x ^ 3 * 12⁻¹,
    by simp [div_eq_mul_inv, ← mul_sub]; norm_num),
  apply mul_lt_mul',
  { rw [pow_succ x 3], refine le_trans _ (le_of_eq (one_mul _)),
    rw mul_le_mul_right, exact h', apply pow_pos h },
  norm_num, norm_num, apply pow_pos h
end

section cos_div_pow_two

variable (x : ℝ)

/-- the series `sqrt_two_add_series x n` is `sqrt(2 + sqrt(2 + ... ))` with `n` square roots,
  starting with `x`. We define it here because `cos (pi / 2 ^ (n+1)) = sqrt_two_add_series 0 n / 2`
-/
@[simp, pp_nodot] noncomputable def sqrt_two_add_series (x : ℝ) : ℕ → ℝ
| 0     := x
| (n+1) := sqrt (2 + sqrt_two_add_series n)

lemma sqrt_two_add_series_zero : sqrt_two_add_series x 0 = x := by simp
lemma sqrt_two_add_series_one : sqrt_two_add_series 0 1 = sqrt 2 := by simp
lemma sqrt_two_add_series_two : sqrt_two_add_series 0 2 = sqrt (2 + sqrt 2) := by simp

lemma sqrt_two_add_series_zero_nonneg : ∀(n : ℕ), 0 ≤ sqrt_two_add_series 0 n
| 0     := le_refl 0
| (n+1) := sqrt_nonneg _

lemma sqrt_two_add_series_nonneg {x : ℝ} (h : 0 ≤ x) : ∀(n : ℕ), 0 ≤ sqrt_two_add_series x n
| 0     := h
| (n+1) := sqrt_nonneg _

lemma sqrt_two_add_series_lt_two : ∀(n : ℕ), sqrt_two_add_series 0 n < 2
| 0     := by norm_num
| (n+1) :=
  begin
    refine lt_of_lt_of_le _ (le_of_eq $ sqrt_sqr $ le_of_lt zero_lt_two),
    rw [sqrt_two_add_series, sqrt_lt, ← lt_sub_iff_add_lt'],
    { refine (sqrt_two_add_series_lt_two n).trans_le _, norm_num },
    { exact add_nonneg zero_le_two (sqrt_two_add_series_zero_nonneg n) }
  end

lemma sqrt_two_add_series_succ (x : ℝ) :
  ∀(n : ℕ), sqrt_two_add_series x (n+1) = sqrt_two_add_series (sqrt (2 + x)) n
| 0     := rfl
| (n+1) := by rw [sqrt_two_add_series, sqrt_two_add_series_succ, sqrt_two_add_series]

lemma sqrt_two_add_series_monotone_left {x y : ℝ} (h : x ≤ y) :
  ∀(n : ℕ), sqrt_two_add_series x n ≤ sqrt_two_add_series y n
| 0     := h
| (n+1) :=
  begin
    rw [sqrt_two_add_series, sqrt_two_add_series],
    exact sqrt_le_sqrt (add_le_add_left (sqrt_two_add_series_monotone_left _) _)
  end

@[simp] lemma cos_pi_over_two_pow : ∀(n : ℕ), cos (pi / 2 ^ (n+1)) = sqrt_two_add_series 0 n / 2
| 0     := by simp
| (n+1) :=
  begin
    have : (2 : ℝ) ≠ 0 := two_ne_zero,
    symmetry, rw [div_eq_iff_mul_eq this], symmetry,
    rw [sqrt_two_add_series, sqrt_eq_iff_sqr_eq, mul_pow, cos_square, ←mul_div_assoc,
      nat.add_succ, pow_succ, mul_div_mul_left _ _ this, cos_pi_over_two_pow, add_mul],
    congr, { norm_num },
    rw [mul_comm, pow_two, mul_assoc, ←mul_div_assoc, mul_div_cancel_left, ←mul_div_assoc,
        mul_div_cancel_left]; try { exact this },
    apply add_nonneg, norm_num, apply sqrt_two_add_series_zero_nonneg, norm_num,
    apply le_of_lt, apply cos_pos_of_mem_Ioo ⟨_, _⟩,
    { transitivity (0 : ℝ), rw neg_lt_zero, apply pi_div_two_pos,
      apply div_pos pi_pos, apply pow_pos, norm_num },
    apply div_lt_div' (le_refl pi) _ pi_pos _,
    refine lt_of_le_of_lt (le_of_eq (pow_one _).symm) _,
    apply pow_lt_pow, norm_num, apply nat.succ_lt_succ, apply nat.succ_pos, all_goals {norm_num}
  end

lemma sin_square_pi_over_two_pow (n : ℕ) :
  sin (pi / 2 ^ (n+1)) ^ 2 = 1 - (sqrt_two_add_series 0 n / 2) ^ 2 :=
by rw [sin_square, cos_pi_over_two_pow]

lemma sin_square_pi_over_two_pow_succ (n : ℕ) :
  sin (pi / 2 ^ (n+2)) ^ 2 = 1 / 2 - sqrt_two_add_series 0 n / 4 :=
begin
  rw [sin_square_pi_over_two_pow, sqrt_two_add_series, div_pow, sqr_sqrt, add_div, ←sub_sub],
  congr, norm_num, norm_num, apply add_nonneg, norm_num, apply sqrt_two_add_series_zero_nonneg,
end

@[simp] lemma sin_pi_over_two_pow_succ (n : ℕ) :
  sin (pi / 2 ^ (n+2)) = sqrt (2 - sqrt_two_add_series 0 n) / 2 :=
begin
  symmetry, rw [div_eq_iff_mul_eq], symmetry,
  rw [sqrt_eq_iff_sqr_eq, mul_pow, sin_square_pi_over_two_pow_succ, sub_mul],
  { congr, norm_num, rw [mul_comm], convert mul_div_cancel' _ _, norm_num, norm_num },
  { rw [sub_nonneg], apply le_of_lt, apply sqrt_two_add_series_lt_two },
  apply le_of_lt, apply mul_pos, apply sin_pos_of_pos_of_lt_pi,
  { apply div_pos pi_pos, apply pow_pos, norm_num },
  refine lt_of_lt_of_le _ (le_of_eq (div_one _)), rw [div_lt_div_left],
  refine lt_of_le_of_lt (le_of_eq (pow_zero 2).symm) _,
  apply pow_lt_pow, norm_num, apply nat.succ_pos, apply pi_pos,
  apply pow_pos, all_goals {norm_num}
end

@[simp] lemma cos_pi_div_four : cos (pi / 4) = sqrt 2 / 2 :=
by { transitivity cos (pi / 2 ^ 2), congr, norm_num, simp }

@[simp] lemma sin_pi_div_four : sin (pi / 4) = sqrt 2 / 2 :=
by { transitivity sin (pi / 2 ^ 2), congr, norm_num, simp }

@[simp] lemma cos_pi_div_eight : cos (pi / 8) = sqrt (2 + sqrt 2) / 2 :=
by { transitivity cos (pi / 2 ^ 3), congr, norm_num, simp }

@[simp] lemma sin_pi_div_eight : sin (pi / 8) = sqrt (2 - sqrt 2) / 2 :=
by { transitivity sin (pi / 2 ^ 3), congr, norm_num, simp }

@[simp] lemma cos_pi_div_sixteen : cos (pi / 16) = sqrt (2 + sqrt (2 + sqrt 2)) / 2 :=
by { transitivity cos (pi / 2 ^ 4), congr, norm_num, simp }

@[simp] lemma sin_pi_div_sixteen : sin (pi / 16) = sqrt (2 - sqrt (2 + sqrt 2)) / 2 :=
by { transitivity sin (pi / 2 ^ 4), congr, norm_num, simp }

@[simp] lemma cos_pi_div_thirty_two : cos (pi / 32) = sqrt (2 + sqrt (2 + sqrt (2 + sqrt 2))) / 2 :=
by { transitivity cos (pi / 2 ^ 5), congr, norm_num, simp }

@[simp] lemma sin_pi_div_thirty_two : sin (pi / 32) = sqrt (2 - sqrt (2 + sqrt (2 + sqrt 2))) / 2 :=
by { transitivity sin (pi / 2 ^ 5), congr, norm_num, simp }

-- This section is also a convenient location for other explicit values of `sin` and `cos`.

/-- The cosine of `π / 3` is `1 / 2`. -/
@[simp] lemma cos_pi_div_three : cos (π / 3) = 1 / 2 :=
begin
  have h₁ : (2 * cos (π / 3) - 1) ^ 2 * (2 * cos (π / 3) + 2) = 0,
  { have : cos (3 * (π / 3)) = cos π := by { congr' 1, ring },
    linarith [cos_pi, cos_three_mul (π / 3)] },
  cases mul_eq_zero.mp h₁ with h h,
  { linarith [pow_eq_zero h] },
  { have : cos π < cos (π / 3),
    { refine cos_lt_cos_of_nonneg_of_le_pi _ rfl.ge _;
      linarith [pi_pos] },
    linarith [cos_pi] }
end

/-- The square of the cosine of `π / 6` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
lemma square_cos_pi_div_six : cos (π / 6) ^ 2 = 3 / 4 :=
begin
  have h1 : cos (π / 6) ^ 2 = 1 / 2 + 1 / 2 / 2,
  { convert cos_square (π / 6),
    have h2 : 2 * (π / 6) = π / 3 := by cancel_denoms,
    rw [h2, cos_pi_div_three] },
  rw ← sub_eq_zero at h1 ⊢,
  convert h1 using 1,
  ring
end

/-- The cosine of `π / 6` is `√3 / 2`. -/
@[simp] lemma cos_pi_div_six : cos (π / 6) = (sqrt 3) / 2 :=
begin
  suffices : sqrt 3 = cos (π / 6) * 2,
  { field_simp [(by norm_num : 0 ≠ 2)], exact this.symm },
  rw sqrt_eq_iff_sqr_eq,
  { have h1 := (mul_right_inj' (by norm_num : (4:ℝ) ≠ 0)).mpr square_cos_pi_div_six,
    rw ← sub_eq_zero at h1 ⊢,
    convert h1 using 1,
    ring },
  { norm_num },
  { have : 0 < cos (π / 6) := by { apply cos_pos_of_mem_Ioo; split; linarith [pi_pos] },
    linarith },
end

/-- The sine of `π / 6` is `1 / 2`. -/
@[simp] lemma sin_pi_div_six : sin (π / 6) = 1 / 2 :=
begin
  rw [← cos_pi_div_two_sub, ← cos_pi_div_three],
  congr,
  ring
end

/-- The square of the sine of `π / 3` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
lemma square_sin_pi_div_three : sin (π / 3) ^ 2 = 3 / 4 :=
begin
  rw [← cos_pi_div_two_sub, ← square_cos_pi_div_six],
  congr,
  ring
end

/-- The sine of `π / 3` is `√3 / 2`. -/
@[simp] lemma sin_pi_div_three : sin (π / 3) = (sqrt 3) / 2 :=
begin
  rw [← cos_pi_div_two_sub, ← cos_pi_div_six],
  congr,
  ring
end

end cos_div_pow_two

/-- The type of angles -/
def angle : Type :=
quotient_add_group.quotient (add_subgroup.gmultiples (2 * π))

namespace angle

instance angle.add_comm_group : add_comm_group angle :=
quotient_add_group.add_comm_group _

instance : inhabited angle := ⟨0⟩

instance angle.has_coe : has_coe ℝ angle :=
⟨quotient.mk'⟩

@[simp] lemma coe_zero : ↑(0 : ℝ) = (0 : angle) := rfl
@[simp] lemma coe_add (x y : ℝ) : ↑(x + y : ℝ) = (↑x + ↑y : angle) := rfl
@[simp] lemma coe_neg (x : ℝ) : ↑(-x : ℝ) = -(↑x : angle) := rfl
@[simp] lemma coe_sub (x y : ℝ) : ↑(x - y : ℝ) = (↑x - ↑y : angle) :=
by rw [sub_eq_add_neg, sub_eq_add_neg, coe_add, coe_neg]

@[simp, norm_cast] lemma coe_nat_mul_eq_nsmul (x : ℝ) (n : ℕ) :
  ↑((n : ℝ) * x) = n •ℕ (↑x : angle) :=
by simpa using add_monoid_hom.map_nsmul ⟨coe, coe_zero, coe_add⟩ _ _
@[simp, norm_cast] lemma coe_int_mul_eq_gsmul (x : ℝ) (n : ℤ) :
  ↑((n : ℝ) * x : ℝ) = n •ℤ (↑x : angle) :=
by simpa using add_monoid_hom.map_gsmul ⟨coe, coe_zero, coe_add⟩ _ _

@[simp] lemma coe_two_pi : ↑(2 * π : ℝ) = (0 : angle) :=
quotient.sound' ⟨-1, show (-1 : ℤ) •ℤ (2 * π) = _, by rw [neg_one_gsmul, add_zero]⟩

lemma angle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : angle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k :=
by simp only [quotient_add_group.eq, add_subgroup.gmultiples_eq_closure,
  add_subgroup.mem_closure_singleton, gsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]

theorem cos_eq_iff_eq_or_eq_neg {θ ψ : ℝ} : cos θ = cos ψ ↔ (θ : angle) = ψ ∨ (θ : angle) = -ψ :=
begin
  split,
  { intro Hcos,
    rw [← sub_eq_zero, cos_sub_cos, mul_eq_zero, mul_eq_zero, neg_eq_zero,
        eq_false_intro two_ne_zero, false_or, sin_eq_zero_iff, sin_eq_zero_iff] at Hcos,
    rcases Hcos with ⟨n, hn⟩ | ⟨n, hn⟩,
    { right,
      rw [eq_div_iff_mul_eq (@two_ne_zero ℝ _ _), ← sub_eq_iff_eq_add] at hn,
      rw [← hn, coe_sub, eq_neg_iff_add_eq_zero, sub_add_cancel, mul_assoc,
          coe_int_mul_eq_gsmul, mul_comm, coe_two_pi, gsmul_zero] },
    { left,
      rw [eq_div_iff_mul_eq (@two_ne_zero ℝ _ _), eq_sub_iff_add_eq] at hn,
      rw [← hn, coe_add, mul_assoc,
          coe_int_mul_eq_gsmul, mul_comm, coe_two_pi, gsmul_zero, zero_add] },
    apply_instance, },
  { rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub],
    rintro (⟨k, H⟩ | ⟨k, H⟩),
    rw [← sub_eq_zero_iff_eq, cos_sub_cos, H, mul_assoc 2 π k,
        mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_comm π _, sin_int_mul_pi, mul_zero],
    rw [← sub_eq_zero_iff_eq, cos_sub_cos, ← sub_neg_eq_add, H, mul_assoc 2 π k,
        mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_comm π _, sin_int_mul_pi, mul_zero,
        zero_mul] }
end

theorem sin_eq_iff_eq_or_add_eq_pi {θ ψ : ℝ} :
  sin θ = sin ψ ↔ (θ : angle) = ψ ∨ (θ : angle) + ψ = π :=
begin
  split,
  { intro Hsin, rw [← cos_pi_div_two_sub, ← cos_pi_div_two_sub] at Hsin,
    cases cos_eq_iff_eq_or_eq_neg.mp Hsin with h h,
    { left, rw [coe_sub, coe_sub] at h, exact sub_right_inj.1 h },
      right, rw [coe_sub, coe_sub, eq_neg_iff_add_eq_zero, add_sub,
      sub_add_eq_add_sub, ← coe_add, add_halves, sub_sub, sub_eq_zero] at h,
    exact h.symm },
  { rw [angle_eq_iff_two_pi_dvd_sub, ←eq_sub_iff_add_eq, ←coe_sub, angle_eq_iff_two_pi_dvd_sub],
    rintro (⟨k, H⟩ | ⟨k, H⟩),
    rw [← sub_eq_zero_iff_eq, sin_sub_sin, H, mul_assoc 2 π k,
        mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_comm π _, sin_int_mul_pi, mul_zero, zero_mul],
    have H' : θ + ψ = (2 * k) * π + π := by rwa [←sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add,
      mul_assoc, mul_comm π _, ←mul_assoc] at H,
    rw [← sub_eq_zero_iff_eq, sin_sub_sin, H', add_div, mul_assoc 2 _ π,
        mul_div_cancel_left _ (@two_ne_zero ℝ _ _), cos_add_pi_div_two, sin_int_mul_pi, neg_zero,
        mul_zero] }
end

theorem cos_sin_inj {θ ψ : ℝ} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (θ : angle) = ψ :=
begin
  cases cos_eq_iff_eq_or_eq_neg.mp Hcos with hc hc, { exact hc },
  cases sin_eq_iff_eq_or_add_eq_pi.mp Hsin with hs hs, { exact hs },
  rw [eq_neg_iff_add_eq_zero, hs] at hc,
  cases quotient.exact' hc with n hn, change n •ℤ _ = _ at hn,
  rw [← neg_one_mul, add_zero, ← sub_eq_zero_iff_eq, gsmul_eq_mul, ← mul_assoc, ← sub_mul,
      mul_eq_zero, eq_false_intro (ne_of_gt pi_pos), or_false, sub_neg_eq_add,
      ← int.cast_zero, ← int.cast_one, ← int.cast_bit0, ← int.cast_mul, ← int.cast_add,
      int.cast_inj] at hn,
  have : (n * 2 + 1) % (2:ℤ) = 0 % (2:ℤ) := congr_arg (%(2:ℤ)) hn,
  rw [add_comm, int.add_mul_mod_self] at this,
  exact absurd this one_ne_zero
end

end angle

/-- `real.sin` as an `order_iso` between `[-(π / 2), π / 2]` and `[-1, 1]`. -/
def sin_order_iso : Icc (-(π / 2)) (π / 2) ≃o Icc (-1:ℝ) 1 :=
(strict_mono_incr_on_sin.order_iso _ _).trans $ order_iso.set_congr _ _ bij_on_sin.image_eq

@[simp] lemma coe_sin_order_iso_apply (x : Icc (-(π / 2)) (π / 2)) :
  (sin_order_iso x : ℝ) = sin x := rfl

lemma sin_order_iso_apply (x : Icc (-(π / 2)) (π / 2)) :
  sin_order_iso x = ⟨sin x, sin_mem_Icc x⟩ := rfl

/-- Inverse of the `sin` function, returns values in the range `-π / 2 ≤ arcsin x ≤ π / 2`.
It defaults to `-π / 2` on `(-∞, -1)` and to `π / 2` to `(1, ∞)`. -/
@[pp_nodot] noncomputable def arcsin : ℝ → ℝ :=
coe ∘ Icc_extend (neg_le_self zero_le_one) sin_order_iso.symm

lemma arcsin_mem_Icc (x : ℝ) : arcsin x ∈ Icc (-(π / 2)) (π / 2) := subtype.coe_prop _

@[simp] lemma range_arcsin : range arcsin = Icc (-(π / 2)) (π / 2) :=
by { rw [arcsin, range_comp coe], simp [Icc] }

lemma arcsin_le_pi_div_two (x : ℝ) : arcsin x ≤ π / 2 := (arcsin_mem_Icc x).2

lemma neg_pi_div_two_le_arcsin (x : ℝ) : -(π / 2) ≤ arcsin x := (arcsin_mem_Icc x).1

lemma arcsin_proj_Icc (x : ℝ) :
  arcsin (proj_Icc (-1) 1 (neg_le_self $ @zero_le_one ℝ _) x) = arcsin x :=
by rw [arcsin, function.comp_app, Icc_extend_coe, function.comp_app, Icc_extend]

lemma sin_arcsin' {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : sin (arcsin x) = x :=
by simpa [arcsin, Icc_extend_of_mem _ _ hx, -order_iso.apply_symm_apply]
  using subtype.ext_iff.1 (sin_order_iso.apply_symm_apply ⟨x, hx⟩)

lemma sin_arcsin {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : sin (arcsin x) = x :=
sin_arcsin' ⟨hx₁, hx₂⟩

lemma arcsin_sin' {x : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) : arcsin (sin x) = x :=
inj_on_sin (arcsin_mem_Icc _) hx $ by rw [sin_arcsin (neg_one_le_sin _) (sin_le_one _)]

lemma arcsin_sin {x : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) : arcsin (sin x) = x :=
arcsin_sin' ⟨hx₁, hx₂⟩

lemma strict_mono_incr_on_arcsin : strict_mono_incr_on arcsin (Icc (-1) 1) :=
(subtype.strict_mono_coe _).comp_strict_mono_incr_on $
  sin_order_iso.symm.strict_mono.strict_mono_incr_on_Icc_extend _

lemma monotone_arcsin : monotone arcsin :=
(subtype.mono_coe _).comp $ sin_order_iso.symm.monotone.Icc_extend _

lemma inj_on_arcsin : inj_on arcsin (Icc (-1) 1) := strict_mono_incr_on_arcsin.inj_on

lemma arcsin_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) :
  arcsin x = arcsin y ↔ x = y :=
inj_on_arcsin.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

lemma continuous_arcsin : continuous arcsin :=
continuous_subtype_coe.comp sin_order_iso.symm.continuous.Icc_extend

lemma continuous_at_arcsin {x : ℝ} : continuous_at arcsin x :=
continuous_arcsin.continuous_at

lemma arcsin_eq_of_sin_eq {x y : ℝ} (h₁ : sin x = y) (h₂ : x ∈ Icc (-(π / 2)) (π / 2)) :
  arcsin y = x :=
begin
  subst y,
  exact inj_on_sin (arcsin_mem_Icc _) h₂ (sin_arcsin' (sin_mem_Icc x))
end

@[simp] lemma arcsin_zero : arcsin 0 = 0 :=
arcsin_eq_of_sin_eq sin_zero ⟨neg_nonpos.2 pi_div_two_pos.le, pi_div_two_pos.le⟩

@[simp] lemma arcsin_one : arcsin 1 = π / 2 :=
arcsin_eq_of_sin_eq sin_pi_div_two $ right_mem_Icc.2 (neg_le_self pi_div_two_pos.le)

lemma arcsin_of_one_le {x : ℝ} (hx : 1 ≤ x) : arcsin x = π / 2 :=
by rw [← arcsin_proj_Icc, proj_Icc_of_right_le _ hx, subtype.coe_mk, arcsin_one]

lemma arcsin_neg_one : arcsin (-1) = -(π / 2) :=
arcsin_eq_of_sin_eq (by rw [sin_neg, sin_pi_div_two]) $
  left_mem_Icc.2 (neg_le_self pi_div_two_pos.le)

lemma arcsin_of_le_neg_one {x : ℝ} (hx : x ≤ -1) : arcsin x = -(π / 2) :=
by rw [← arcsin_proj_Icc, proj_Icc_of_le_left _ hx, subtype.coe_mk, arcsin_neg_one]

@[simp] lemma arcsin_neg (x : ℝ) : arcsin (-x) = -arcsin x :=
begin
  cases le_total x (-1) with hx₁ hx₁,
  { rw [arcsin_of_le_neg_one hx₁, neg_neg, arcsin_of_one_le (le_neg.2 hx₁)] },
  cases le_total 1 x with hx₂ hx₂,
  { rw [arcsin_of_one_le hx₂, arcsin_of_le_neg_one (neg_le_neg hx₂)] },
  refine arcsin_eq_of_sin_eq _ _,
  { rw [sin_neg, sin_arcsin hx₁ hx₂] },
  { exact ⟨neg_le_neg (arcsin_le_pi_div_two _), neg_le.2 (neg_pi_div_two_le_arcsin _)⟩ }
end

lemma arcsin_le_iff_le_sin {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-(π / 2)) (π / 2)) :
  arcsin x ≤ y ↔ x ≤ sin y :=
by rw [← arcsin_sin' hy, strict_mono_incr_on_arcsin.le_iff_le hx (sin_mem_Icc _), arcsin_sin' hy]

lemma arcsin_le_iff_le_sin' {x y : ℝ} (hy : y ∈ Ico (-(π / 2)) (π / 2)) :
  arcsin x ≤ y ↔ x ≤ sin y :=
begin
  cases le_total x (-1) with hx₁ hx₁,
  { simp [arcsin_of_le_neg_one hx₁, hy.1, hx₁.trans (neg_one_le_sin _)] },
  cases lt_or_le 1 x with hx₂ hx₂,
  { simp [arcsin_of_one_le hx₂.le, hy.2.not_le, (sin_le_one y).trans_lt hx₂] },
  exact arcsin_le_iff_le_sin ⟨hx₁, hx₂⟩ (mem_Icc_of_Ico hy)
end

lemma le_arcsin_iff_sin_le {x y : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) (hy : y ∈ Icc (-1 : ℝ) 1) :
  x ≤ arcsin y ↔ sin x ≤ y :=
by rw [← neg_le_neg_iff, ← arcsin_neg,
  arcsin_le_iff_le_sin ⟨neg_le_neg hy.2, neg_le.2 hy.1⟩ ⟨neg_le_neg hx.2, neg_le.2 hx.1⟩,
  sin_neg, neg_le_neg_iff]

lemma le_arcsin_iff_sin_le' {x y : ℝ} (hx : x ∈ Ioc (-(π / 2)) (π / 2)) :
  x ≤ arcsin y ↔ sin x ≤ y :=
by rw [← neg_le_neg_iff, ← arcsin_neg, arcsin_le_iff_le_sin' ⟨neg_le_neg hx.2, neg_lt.2 hx.1⟩,
  sin_neg, neg_le_neg_iff]

lemma arcsin_lt_iff_lt_sin {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-(π / 2)) (π / 2)) :
  arcsin x < y ↔ x < sin y :=
not_le.symm.trans $ (not_congr $ le_arcsin_iff_sin_le hy hx).trans not_le

lemma arcsin_lt_iff_lt_sin' {x y : ℝ} (hy : y ∈ Ioc (-(π / 2)) (π / 2)) :
  arcsin x < y ↔ x < sin y :=
not_le.symm.trans $ (not_congr $ le_arcsin_iff_sin_le' hy).trans not_le

lemma lt_arcsin_iff_sin_lt {x y : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) (hy : y ∈ Icc (-1 : ℝ) 1) :
  x < arcsin y ↔ sin x < y :=
not_le.symm.trans $ (not_congr $ arcsin_le_iff_le_sin hy hx).trans not_le

lemma lt_arcsin_iff_sin_lt' {x y : ℝ} (hx : x ∈ Ico (-(π / 2)) (π / 2)) :
  x < arcsin y ↔ sin x < y :=
not_le.symm.trans $ (not_congr $ arcsin_le_iff_le_sin' hx).trans not_le

lemma arcsin_eq_iff_eq_sin {x y : ℝ} (hy : y ∈ Ioo (-(π / 2)) (π / 2)) :
  arcsin x = y ↔ x = sin y :=
by simp only [le_antisymm_iff, arcsin_le_iff_le_sin' (mem_Ico_of_Ioo hy),
  le_arcsin_iff_sin_le' (mem_Ioc_of_Ioo hy)]

@[simp] lemma arcsin_nonneg {x : ℝ} : 0 ≤ arcsin x ↔ 0 ≤ x :=
(le_arcsin_iff_sin_le' ⟨neg_lt_zero.2 pi_div_two_pos, pi_div_two_pos.le⟩).trans $ by rw [sin_zero]

@[simp] lemma arcsin_nonpos {x : ℝ} : arcsin x ≤ 0 ↔ x ≤ 0 :=
neg_nonneg.symm.trans $ arcsin_neg x ▸ arcsin_nonneg.trans neg_nonneg

@[simp] lemma arcsin_eq_zero_iff {x : ℝ} : arcsin x = 0 ↔ x = 0 :=
by simp [le_antisymm_iff]

@[simp] lemma zero_eq_arcsin_iff {x} : 0 = arcsin x ↔ x = 0 :=
eq_comm.trans arcsin_eq_zero_iff

@[simp] lemma arcsin_pos {x : ℝ} : 0 < arcsin x ↔ 0 < x :=
lt_iff_lt_of_le_iff_le arcsin_nonpos

@[simp] lemma arcsin_lt_zero {x : ℝ} : arcsin x < 0 ↔ x < 0 :=
lt_iff_lt_of_le_iff_le arcsin_nonneg

@[simp] lemma arcsin_lt_pi_div_two {x : ℝ} : arcsin x < π / 2 ↔ x < 1 :=
(arcsin_lt_iff_lt_sin' (right_mem_Ioc.2 $ neg_lt_self pi_div_two_pos)).trans $
  by rw sin_pi_div_two

@[simp] lemma neg_pi_div_two_lt_arcsin {x : ℝ} : -(π / 2) < arcsin x ↔ -1 < x :=
(lt_arcsin_iff_sin_lt' $ left_mem_Ico.2 $ neg_lt_self pi_div_two_pos).trans $
  by rw [sin_neg, sin_pi_div_two]

@[simp] lemma arcsin_eq_pi_div_two {x : ℝ} : arcsin x = π / 2 ↔ 1 ≤ x :=
⟨λ h, not_lt.1 $ λ h', (arcsin_lt_pi_div_two.2 h').ne h, arcsin_of_one_le⟩

@[simp] lemma pi_div_two_eq_arcsin {x} : π / 2 = arcsin x ↔ 1 ≤ x :=
eq_comm.trans arcsin_eq_pi_div_two

@[simp] lemma pi_div_two_le_arcsin {x} : π / 2 ≤ arcsin x ↔ 1 ≤ x :=
(arcsin_le_pi_div_two x).le_iff_eq.trans pi_div_two_eq_arcsin

@[simp] lemma arcsin_eq_neg_pi_div_two {x : ℝ} : arcsin x = -(π / 2) ↔ x ≤ -1 :=
⟨λ h, not_lt.1 $ λ h', (neg_pi_div_two_lt_arcsin.2 h').ne' h, arcsin_of_le_neg_one⟩

@[simp] lemma neg_pi_div_two_eq_arcsin {x} : -(π / 2) = arcsin x ↔ x ≤ -1 :=
eq_comm.trans arcsin_eq_neg_pi_div_two

@[simp] lemma arcsin_le_neg_pi_div_two {x} : arcsin x ≤ -(π / 2) ↔ x ≤ -1 :=
(neg_pi_div_two_le_arcsin x).le_iff_eq.trans arcsin_eq_neg_pi_div_two

lemma maps_to_sin_Ioo : maps_to sin (Ioo (-(π / 2)) (π / 2)) (Ioo (-1) 1) :=
λ x h, by rwa [mem_Ioo, ← arcsin_lt_pi_div_two, ← neg_pi_div_two_lt_arcsin,
  arcsin_sin h.1.le h.2.le]

/-- `real.sin` as a `local_homeomorph` between `(-π / 2, π / 2)` and `(-1, 1)`. -/
@[simp] def sin_local_homeomorph : local_homeomorph ℝ ℝ :=
{ to_fun := sin,
  inv_fun := arcsin,
  source := Ioo (-(π / 2)) (π / 2),
  target := Ioo (-1) 1,
  map_source' := maps_to_sin_Ioo,
  map_target' := λ y hy, ⟨neg_pi_div_two_lt_arcsin.2 hy.1, arcsin_lt_pi_div_two.2 hy.2⟩,
  left_inv' := λ x hx, arcsin_sin hx.1.le hx.2.le,
  right_inv' := λ y hy, sin_arcsin hy.1.le hy.2.le,
  open_source := is_open_Ioo,
  open_target := is_open_Ioo,
  continuous_to_fun := continuous_sin.continuous_on,
  continuous_inv_fun := continuous_arcsin.continuous_on }

lemma cos_arcsin_nonneg (x : ℝ) : 0 ≤ cos (arcsin x) :=
cos_nonneg_of_mem_Icc ⟨neg_pi_div_two_le_arcsin _, arcsin_le_pi_div_two _⟩

lemma cos_arcsin {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arcsin x) = sqrt (1 - x ^ 2) :=
have sin (arcsin x) ^ 2 + cos (arcsin x) ^ 2 = 1 := sin_sq_add_cos_sq (arcsin x),
begin
  rw [← eq_sub_iff_add_eq', ← sqrt_inj (pow_two_nonneg _) (sub_nonneg.2 (sin_sq_le_one (arcsin x))),
    pow_two, sqrt_mul_self (cos_arcsin_nonneg _)] at this,
  rw [this, sin_arcsin hx₁ hx₂],
end

lemma deriv_arcsin_aux {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
  has_deriv_at arcsin (1 / sqrt (1 - x ^ 2)) x ∧ times_cont_diff_at ℝ ⊤ arcsin x :=
begin
  cases h₁.lt_or_lt with h₁ h₁,
  { have : 1 - x ^ 2 < 0, by nlinarith [h₁],
    rw [sqrt_eq_zero'.2 this.le, div_zero],
    have : arcsin =ᶠ[𝓝 x] λ _, -(π / 2) :=
      (gt_mem_nhds h₁).mono (λ y hy, arcsin_of_le_neg_one hy.le),
    exact ⟨(has_deriv_at_const _ _).congr_of_eventually_eq this,
      times_cont_diff_at_const.congr_of_eventually_eq this⟩ },
  cases h₂.lt_or_lt with h₂ h₂,
  { have : 0 < sqrt (1 - x ^ 2) := sqrt_pos.2 (by nlinarith [h₁, h₂]),
    simp only [← cos_arcsin h₁.le h₂.le, one_div] at this ⊢,
    exact ⟨sin_local_homeomorph.has_deriv_at_symm ⟨h₁, h₂⟩ this.ne' (has_deriv_at_sin _),
      sin_local_homeomorph.times_cont_diff_at_symm_deriv this.ne' ⟨h₁, h₂⟩
        (has_deriv_at_sin _) times_cont_diff_sin.times_cont_diff_at⟩ },
  { have : 1 - x ^ 2 < 0, by nlinarith [h₂],
    rw [sqrt_eq_zero'.2 this.le, div_zero],
    have : arcsin =ᶠ[𝓝 x] λ _, π / 2 := (lt_mem_nhds h₂).mono (λ y hy, arcsin_of_one_le hy.le),
    exact ⟨(has_deriv_at_const _ _).congr_of_eventually_eq this,
      times_cont_diff_at_const.congr_of_eventually_eq this⟩ }
end

lemma has_deriv_at_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
  has_deriv_at arcsin (1 / sqrt (1 - x ^ 2)) x :=
(deriv_arcsin_aux h₁ h₂).1

lemma times_cont_diff_at_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) {n : with_top ℕ} :
  times_cont_diff_at ℝ n arcsin x :=
(deriv_arcsin_aux h₁ h₂).2.of_le le_top

lemma has_deriv_within_at_arcsin_Ici {x : ℝ} (h : x ≠ -1) :
  has_deriv_within_at arcsin (1 / sqrt (1 - x ^ 2)) (Ici x) x :=
begin
  rcases em (x = 1) with (rfl|h'),
  { convert (has_deriv_within_at_const _ _ (π / 2)).congr _ _;
      simp [arcsin_of_one_le] { contextual := tt } },
  { exact (has_deriv_at_arcsin h h').has_deriv_within_at }
end

lemma has_deriv_within_at_arcsin_Iic {x : ℝ} (h : x ≠ 1) :
  has_deriv_within_at arcsin (1 / sqrt (1 - x ^ 2)) (Iic x) x :=
begin
  rcases em (x = -1) with (rfl|h'),
  { convert (has_deriv_within_at_const _ _ (-(π / 2))).congr _ _;
      simp [arcsin_of_le_neg_one] { contextual := tt } },
  { exact (has_deriv_at_arcsin h' h).has_deriv_within_at }
end

lemma differentiable_within_at_arcsin_Ici {x : ℝ} :
  differentiable_within_at ℝ arcsin (Ici x) x ↔ x ≠ -1 :=
begin
  refine ⟨_, λ h, (has_deriv_within_at_arcsin_Ici h).differentiable_within_at⟩,
  rintro h rfl,
  have : sin ∘ arcsin =ᶠ[𝓝[Ici (-1:ℝ)] (-1)] id,
  { filter_upwards [Icc_mem_nhds_within_Ici ⟨le_rfl, neg_lt_self (@zero_lt_one ℝ _ _)⟩],
    exact λ x, sin_arcsin' },
  have := h.has_deriv_within_at.sin.congr_of_eventually_eq this.symm (by simp),
  simpa using (unique_diff_on_Ici _ _ left_mem_Ici).eq_deriv _ this (has_deriv_within_at_id _ _)
end

lemma differentiable_within_at_arcsin_Iic {x : ℝ} :
  differentiable_within_at ℝ arcsin (Iic x) x ↔ x ≠ 1 :=
begin
  refine ⟨λ h, _, λ h, (has_deriv_within_at_arcsin_Iic h).differentiable_within_at⟩,
  rw [← neg_neg x, ← image_neg_Ici] at h,
  have := (h.comp (-x) differentiable_within_at_id.neg (maps_to_image _ _)).neg,
  simpa [(∘), differentiable_within_at_arcsin_Ici] using this
end

lemma differentiable_at_arcsin {x : ℝ} :
  differentiable_at ℝ arcsin x ↔ x ≠ -1 ∧ x ≠ 1 :=
⟨λ h, ⟨differentiable_within_at_arcsin_Ici.1 h.differentiable_within_at,
  differentiable_within_at_arcsin_Iic.1 h.differentiable_within_at⟩,
  λ h, (has_deriv_at_arcsin h.1 h.2).differentiable_at⟩

@[simp] lemma deriv_arcsin : deriv arcsin = λ x, 1 / sqrt (1 - x ^ 2) :=
begin
  funext x,
  by_cases h : x ≠ -1 ∧ x ≠ 1,
  { exact (has_deriv_at_arcsin h.1 h.2).deriv },
  { rw [deriv_zero_of_not_differentiable_at (mt differentiable_at_arcsin.1 h)],
    simp only [not_and_distrib, ne.def, not_not] at h,
    rcases h with (rfl|rfl); simp }
end

lemma differentiable_on_arcsin : differentiable_on ℝ arcsin {-1, 1}ᶜ :=
λ x hx, (differentiable_at_arcsin.2
  ⟨λ h, hx (or.inl h), λ h, hx (or.inr h)⟩).differentiable_within_at

lemma times_cont_diff_on_arcsin {n : with_top ℕ} :
  times_cont_diff_on ℝ n arcsin {-1, 1}ᶜ :=
λ x hx, (times_cont_diff_at_arcsin (mt or.inl hx) (mt or.inr hx)).times_cont_diff_within_at

lemma times_cont_diff_at_arcsin_iff {x : ℝ} {n : with_top ℕ} :
  times_cont_diff_at ℝ n arcsin x ↔ n = 0 ∨ (x ≠ -1 ∧ x ≠ 1) :=
⟨λ h, or_iff_not_imp_left.2 $ λ hn, differentiable_at_arcsin.1 $ h.differentiable_at $
  with_top.one_le_iff_pos.2 (pos_iff_ne_zero.2 hn),
  λ h, h.elim (λ hn, hn.symm ▸ (times_cont_diff_zero.2 continuous_arcsin).times_cont_diff_at) $
    λ hx, times_cont_diff_at_arcsin hx.1 hx.2⟩

lemma measurable_arcsin : measurable arcsin := continuous_arcsin.measurable

/-- Inverse of the `cos` function, returns values in the range `0 ≤ arccos x` and `arccos x ≤ π`.
  If the argument is not between `-1` and `1` it defaults to `π / 2` -/
@[pp_nodot] noncomputable def arccos (x : ℝ) : ℝ :=
π / 2 - arcsin x

lemma arccos_eq_pi_div_two_sub_arcsin (x : ℝ) : arccos x = π / 2 - arcsin x := rfl

lemma arcsin_eq_pi_div_two_sub_arccos (x : ℝ) : arcsin x = π / 2 - arccos x :=
by simp [arccos]

lemma arccos_le_pi (x : ℝ) : arccos x ≤ π :=
by unfold arccos; linarith [neg_pi_div_two_le_arcsin x]

lemma arccos_nonneg (x : ℝ) : 0 ≤ arccos x :=
by unfold arccos; linarith [arcsin_le_pi_div_two x]

lemma cos_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arccos x) = x :=
by rw [arccos, cos_pi_div_two_sub, sin_arcsin hx₁ hx₂]

lemma arccos_cos {x : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π) : arccos (cos x) = x :=
by rw [arccos, ← sin_pi_div_two_sub, arcsin_sin]; simp [sub_eq_add_neg]; linarith

lemma strict_mono_decr_on_arccos : strict_mono_decr_on arccos (Icc (-1) 1) :=
λ x hx y hy h, sub_lt_sub_left (strict_mono_incr_on_arcsin hx hy h) _

lemma arccos_inj_on : inj_on arccos (Icc (-1) 1) := strict_mono_decr_on_arccos.inj_on

lemma arccos_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) :
  arccos x = arccos y ↔ x = y :=
arccos_inj_on.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

@[simp] lemma arccos_zero : arccos 0 = π / 2 := by simp [arccos]

@[simp] lemma arccos_one : arccos 1 = 0 := by simp [arccos]

@[simp] lemma arccos_neg_one : arccos (-1) = π := by simp [arccos, add_halves]

@[simp] lemma arccos_eq_zero {x} : arccos x = 0 ↔ 1 ≤ x :=
by simp [arccos, sub_eq_zero]

@[simp] lemma arccos_eq_pi_div_two {x} : arccos x = π / 2 ↔ x = 0 :=
by simp [arccos, sub_eq_iff_eq_add]

@[simp] lemma arccos_eq_pi {x} : arccos x = π ↔ x ≤ -1 :=
by rw [arccos, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', div_two_sub_self, neg_pi_div_two_eq_arcsin]

lemma arccos_neg (x : ℝ) : arccos (-x) = π - arccos x :=
by rw [← add_halves π, arccos, arcsin_neg, arccos, add_sub_assoc, sub_sub_self, sub_neg_eq_add]

lemma sin_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : sin (arccos x) = sqrt (1 - x ^ 2) :=
by rw [arccos_eq_pi_div_two_sub_arcsin, sin_pi_div_two_sub, cos_arcsin hx₁ hx₂]

lemma continuous_arccos : continuous arccos := continuous_const.sub continuous_arcsin

lemma has_deriv_at_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
  has_deriv_at arccos (-(1 / sqrt (1 - x ^ 2))) x :=
(has_deriv_at_arcsin h₁ h₂).const_sub (π / 2)

lemma times_cont_diff_at_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) {n : with_top ℕ} :
  times_cont_diff_at ℝ n arccos x :=
times_cont_diff_at_const.sub (times_cont_diff_at_arcsin h₁ h₂)

lemma has_deriv_within_at_arccos_Ici {x : ℝ} (h : x ≠ -1) :
  has_deriv_within_at arccos (-(1 / sqrt (1 - x ^ 2))) (Ici x) x :=
(has_deriv_within_at_arcsin_Ici h).const_sub _

lemma has_deriv_within_at_arccos_Iic {x : ℝ} (h : x ≠ 1) :
  has_deriv_within_at arccos (-(1 / sqrt (1 - x ^ 2))) (Iic x) x :=
(has_deriv_within_at_arcsin_Iic h).const_sub _

lemma differentiable_within_at_arccos_Ici {x : ℝ} :
  differentiable_within_at ℝ arccos (Ici x) x ↔ x ≠ -1 :=
(differentiable_within_at_const_sub_iff _).trans differentiable_within_at_arcsin_Ici

lemma differentiable_within_at_arccos_Iic {x : ℝ} :
  differentiable_within_at ℝ arccos (Iic x) x ↔ x ≠ 1 :=
(differentiable_within_at_const_sub_iff _).trans differentiable_within_at_arcsin_Iic

lemma differentiable_at_arccos {x : ℝ} :
  differentiable_at ℝ arccos x ↔ x ≠ -1 ∧ x ≠ 1 :=
(differentiable_at_const_sub_iff _).trans differentiable_at_arcsin

@[simp] lemma deriv_arccos : deriv arccos = λ x, -(1 / sqrt (1 - x ^ 2)) :=
funext $ λ x, (deriv_const_sub _).trans $ by simp only [deriv_arcsin]

lemma differentiable_on_arccos : differentiable_on ℝ arccos {-1, 1}ᶜ :=
differentiable_on_arcsin.const_sub _

lemma times_cont_diff_on_arccos {n : with_top ℕ} :
  times_cont_diff_on ℝ n arccos {-1, 1}ᶜ :=
times_cont_diff_on_const.sub times_cont_diff_on_arcsin

lemma times_cont_diff_at_arccos_iff {x : ℝ} {n : with_top ℕ} :
  times_cont_diff_at ℝ n arccos x ↔ n = 0 ∨ (x ≠ -1 ∧ x ≠ 1) :=
by refine iff.trans ⟨λ h, _, λ h, _⟩ times_cont_diff_at_arcsin_iff;
  simpa [arccos] using (@times_cont_diff_at_const _ _ _ _ _ _ _ _ _ _ (π / 2)).sub h

lemma measurable_arccos : measurable arccos := continuous_arccos.measurable

@[simp] lemma tan_pi_div_four : tan (π / 4) = 1 :=
begin
  rw [tan_eq_sin_div_cos, cos_pi_div_four, sin_pi_div_four],
  have h : (sqrt 2) / 2 > 0 := by cancel_denoms,
  exact div_self (ne_of_gt h),
end

@[simp] lemma tan_pi_div_two : tan (π / 2) = 0 := by simp [tan_eq_sin_div_cos]

lemma tan_pos_of_pos_of_lt_pi_div_two {x : ℝ} (h0x : 0 < x) (hxp : x < π / 2) : 0 < tan x :=
by rw tan_eq_sin_div_cos; exact div_pos (sin_pos_of_pos_of_lt_pi h0x (by linarith))
  (cos_pos_of_mem_Ioo ⟨by linarith, hxp⟩)

lemma tan_nonneg_of_nonneg_of_le_pi_div_two {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π / 2) : 0 ≤ tan x :=
match lt_or_eq_of_le h0x, lt_or_eq_of_le hxp with
| or.inl hx0, or.inl hxp := le_of_lt (tan_pos_of_pos_of_lt_pi_div_two hx0 hxp)
| or.inl hx0, or.inr hxp := by simp [hxp, tan_eq_sin_div_cos]
| or.inr hx0, _          := by simp [hx0.symm]
end

lemma tan_neg_of_neg_of_pi_div_two_lt {x : ℝ} (hx0 : x < 0) (hpx : -(π / 2) < x) : tan x < 0 :=
neg_pos.1 (tan_neg x ▸ tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [pi_pos]))

lemma tan_nonpos_of_nonpos_of_neg_pi_div_two_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -(π / 2) ≤ x) :
  tan x ≤ 0 :=
neg_nonneg.1 (tan_neg x ▸ tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith))

lemma tan_lt_tan_of_nonneg_of_lt_pi_div_two {x y : ℝ}
  (hx₁ : 0 ≤ x) (hy₂ : y < π / 2) (hxy : x < y) :
  tan x < tan y :=
begin
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos],
  exact div_lt_div
    (sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (le_of_lt hy₂) hxy)
    (cos_le_cos_of_nonneg_of_le_pi hx₁ (by linarith) (le_of_lt hxy))
    (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
    (cos_pos_of_mem_Ioo ⟨by linarith, hy₂⟩)
end

lemma tan_lt_tan_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x)
 (hy₂ : y < π / 2) (hxy : x < y) : tan x < tan y :=
match le_total x 0, le_total y 0 with
| or.inl hx0, or.inl hy0 := neg_lt_neg_iff.1 $ by rw [← tan_neg, ← tan_neg]; exact
  tan_lt_tan_of_nonneg_of_lt_pi_div_two (neg_nonneg.2 hy0)
    (neg_lt.2 hx₁) (neg_lt_neg hxy)
| or.inl hx0, or.inr hy0 := (lt_or_eq_of_le hy0).elim
  (λ hy0, calc tan x ≤ 0 : tan_nonpos_of_nonpos_of_neg_pi_div_two_le hx0 (le_of_lt hx₁)
    ... < tan y : tan_pos_of_pos_of_lt_pi_div_two hy0 hy₂)
  (λ hy0, by rw [← hy0, tan_zero]; exact
    tan_neg_of_neg_of_pi_div_two_lt (hy0.symm ▸ hxy) hx₁)
| or.inr hx0, or.inl hy0 := by linarith
| or.inr hx0, or.inr hy0 := tan_lt_tan_of_nonneg_of_lt_pi_div_two hx0 hy₂ hxy
end

lemma strict_mono_incr_on_tan : strict_mono_incr_on tan (Ioo (-(π / 2)) (π / 2)) :=
λ x hx y hy, tan_lt_tan_of_lt_of_lt_pi_div_two hx.1 hy.2

lemma inj_on_tan : inj_on tan (Ioo (-(π / 2)) (π / 2)) :=
strict_mono_incr_on_tan.inj_on

lemma tan_inj_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
  (hy₁ : -(π / 2) < y) (hy₂ : y < π / 2) (hxy : tan x = tan y) : x = y :=
inj_on_tan ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ hxy

end real

namespace complex

open_locale real

/-- `arg` returns values in the range (-π, π], such that for `x ≠ 0`,
  `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
  `arg 0` defaults to `0` -/
noncomputable def arg (x : ℂ) : ℝ :=
if 0 ≤ x.re
then real.arcsin (x.im / x.abs)
else if 0 ≤ x.im
then real.arcsin ((-x).im / x.abs) + π
else real.arcsin ((-x).im / x.abs) - π

lemma arg_le_pi (x : ℂ) : arg x ≤ π :=
if hx₁ : 0 ≤ x.re
then by rw [arg, if_pos hx₁];
  exact le_trans (real.arcsin_le_pi_div_two _) (le_of_lt (half_lt_self real.pi_pos))
else
  if hx₂ : 0 ≤ x.im
  then by rw [arg, if_neg hx₁, if_pos hx₂, ← le_sub_iff_add_le, sub_self, real.arcsin_nonpos,
    neg_im, neg_div, neg_nonpos];
        exact div_nonneg hx₂ (abs_nonneg _)
  else by rw [arg, if_neg hx₁, if_neg hx₂];
      exact sub_le_iff_le_add.2 (le_trans (real.arcsin_le_pi_div_two _)
        (by linarith [real.pi_pos]))

lemma neg_pi_lt_arg (x : ℂ) : -π < arg x :=
if hx₁ : 0 ≤ x.re
then by rw [arg, if_pos hx₁];
  exact lt_of_lt_of_le (neg_lt_neg (half_lt_self real.pi_pos)) (real.neg_pi_div_two_le_arcsin _)
else
  have hx : x ≠ 0, from λ h, by simpa [h, lt_irrefl] using hx₁,
  if hx₂ : 0 ≤ x.im
  then by rw [arg, if_neg hx₁, if_pos hx₂, ← sub_lt_iff_lt_add];
    exact (lt_of_lt_of_le (by linarith [real.pi_pos]) (real.neg_pi_div_two_le_arcsin _))
  else by rw [arg, if_neg hx₁, if_neg hx₂, lt_sub_iff_add_lt, neg_add_self, real.arcsin_pos,
    neg_im];
      exact div_pos (neg_pos.2 (lt_of_not_ge hx₂)) (abs_pos.2 hx)

lemma arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg {x : ℂ} (hxr : x.re < 0) (hxi : 0 ≤ x.im) :
  arg x = arg (-x) + π :=
have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos],
by rw [arg, arg, if_neg (not_le.2 hxr), if_pos this, if_pos hxi, abs_neg]

lemma arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg {x : ℂ} (hxr : x.re < 0) (hxi : x.im < 0) :
  arg x = arg (-x) - π :=
have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos],
by rw [arg, arg, if_neg (not_le.2 hxr), if_neg (not_le.2 hxi), if_pos this, abs_neg]

@[simp] lemma arg_zero : arg 0 = 0 :=
by simp [arg, le_refl]

@[simp] lemma arg_one : arg 1 = 0 :=
by simp [arg, zero_le_one]

@[simp] lemma arg_neg_one : arg (-1) = π :=
by simp [arg, le_refl, not_le.2 (@zero_lt_one ℝ _ _)]

@[simp] lemma arg_I : arg I = π / 2 :=
by simp [arg, le_refl]

@[simp] lemma arg_neg_I : arg (-I) = -(π / 2) :=
by simp [arg, le_refl]

lemma sin_arg (x : ℂ) : real.sin (arg x) = x.im / x.abs :=
by unfold arg; split_ifs;
  simp [sub_eq_add_neg, arg, real.sin_arcsin (abs_le.1 (abs_im_div_abs_le_one x)).1
    (abs_le.1 (abs_im_div_abs_le_one x)).2, real.sin_add, neg_div, real.arcsin_neg,
    real.sin_neg]

private lemma cos_arg_of_re_nonneg {x : ℂ} (hx : x ≠ 0) (hxr : 0 ≤ x.re) :
  real.cos (arg x) = x.re / x.abs :=
have 0 ≤ 1 - (x.im / abs x) ^ 2,
  from sub_nonneg.2 $ by rw [pow_two, ← _root_.abs_mul_self, _root_.abs_mul, ← pow_two];
  exact pow_le_one _ (_root_.abs_nonneg _) (abs_im_div_abs_le_one _),
by rw [eq_div_iff_mul_eq (mt abs_eq_zero.1 hx), ← real.mul_self_sqrt (abs_nonneg x),
    arg, if_pos hxr, real.cos_arcsin (abs_le.1 (abs_im_div_abs_le_one x)).1
    (abs_le.1 (abs_im_div_abs_le_one x)).2, ← real.sqrt_mul (abs_nonneg _), ← real.sqrt_mul this,
    sub_mul, div_pow, ← pow_two, div_mul_cancel _ (pow_ne_zero 2 (mt abs_eq_zero.1 hx)),
    one_mul, pow_two, mul_self_abs, norm_sq_apply, pow_two, add_sub_cancel, real.sqrt_mul_self hxr]

lemma cos_arg {x : ℂ} (hx : x ≠ 0) : real.cos (arg x) = x.re / x.abs :=
if hxr : 0 ≤ x.re then cos_arg_of_re_nonneg hx hxr
else
  have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos] using hxr,
  if hxi : 0 ≤ x.im
  then have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos] using hxr,
    by rw [arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg (not_le.1 hxr) hxi, real.cos_add_pi,
        cos_arg_of_re_nonneg (neg_ne_zero.2 hx) this];
      simp [neg_div]
  else by rw [arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg (not_le.1 hxr) (not_le.1 hxi)];
    simp [sub_eq_add_neg, real.cos_add, neg_div, cos_arg_of_re_nonneg (neg_ne_zero.2 hx) this]

lemma tan_arg {x : ℂ} : real.tan (arg x) = x.im / x.re :=
begin
  by_cases h : x = 0,
  { simp only [h, zero_div, complex.zero_im, complex.arg_zero, real.tan_zero, complex.zero_re] },
  rw [real.tan_eq_sin_div_cos, sin_arg, cos_arg h,
      div_div_div_cancel_right _ (mt abs_eq_zero.1 h)]
end

lemma arg_cos_add_sin_mul_I {x : ℝ} (hx₁ : -π < x) (hx₂ : x ≤ π) :
  arg (cos x + sin x * I) = x :=
if hx₃ : -(π / 2) ≤ x ∧ x ≤ π / 2
then
  have hx₄ : 0 ≤ (cos x + sin x * I).re,
    by simp; exact real.cos_nonneg_of_mem_Icc hx₃,
  by rw [arg, if_pos hx₄];
    simp [abs_cos_add_sin_mul_I, sin_of_real_re, real.arcsin_sin hx₃.1 hx₃.2]
else if hx₄ : x < -(π / 2)
then
  have hx₅ : ¬0 ≤ (cos x + sin x * I).re :=
    suffices ¬ 0 ≤ real.cos x, by simpa,
    not_le.2 $ by rw ← real.cos_neg;
      apply real.cos_neg_of_pi_div_two_lt_of_lt; linarith,
  have hx₆ : ¬0 ≤ (cos ↑x + sin ↑x * I).im :=
    suffices real.sin x < 0, by simpa,
    by apply real.sin_neg_of_neg_of_neg_pi_lt; linarith,
  suffices -π + -real.arcsin (real.sin x) = x,
    by rw [arg, if_neg hx₅, if_neg hx₆];
    simpa [sub_eq_add_neg, add_comm, abs_cos_add_sin_mul_I, sin_of_real_re],
  by rw [← real.arcsin_neg, ← real.sin_add_pi, real.arcsin_sin]; try {simp [add_left_comm]};
    linarith
else
  have hx₅ : π / 2 < x, by cases not_and_distrib.1 hx₃; linarith,
  have hx₆ : ¬0 ≤ (cos x + sin x * I).re :=
    suffices ¬0 ≤ real.cos x, by simpa,
    not_le.2 $ by apply real.cos_neg_of_pi_div_two_lt_of_lt; linarith,
  have hx₇ : 0 ≤ (cos x + sin x * I).im :=
    suffices 0 ≤ real.sin x, by simpa,
    by apply real.sin_nonneg_of_nonneg_of_le_pi; linarith,
  suffices π - real.arcsin (real.sin x) = x,
    by rw [arg, if_neg hx₆, if_pos hx₇];
      simpa [sub_eq_add_neg, add_comm, abs_cos_add_sin_mul_I, sin_of_real_re],
  by rw [← real.sin_pi_sub, real.arcsin_sin]; simp [sub_eq_add_neg]; linarith

lemma arg_eq_arg_iff {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
  arg x = arg y ↔ (abs y / abs x : ℂ) * x = y :=
have hax : abs x ≠ 0, from (mt abs_eq_zero.1 hx),
have hay : abs y ≠ 0, from (mt abs_eq_zero.1 hy),
⟨λ h,
  begin
    have hcos := congr_arg real.cos h,
    rw [cos_arg hx, cos_arg hy, div_eq_div_iff hax hay] at hcos,
    have hsin := congr_arg real.sin h,
    rw [sin_arg, sin_arg, div_eq_div_iff hax hay] at hsin,
    apply complex.ext,
    { rw [mul_re, ← of_real_div, of_real_re, of_real_im, zero_mul, sub_zero, mul_comm,
        ← mul_div_assoc, hcos, mul_div_cancel _ hax] },
    { rw [mul_im, ← of_real_div, of_real_re, of_real_im, zero_mul, add_zero,
        mul_comm, ← mul_div_assoc, hsin, mul_div_cancel _ hax] }
  end,
λ h,
  have hre : abs (y / x) * x.re = y.re,
    by rw ← of_real_div at h;
      simpa [-of_real_div] using congr_arg re h,
  have hre' : abs (x / y) * y.re = x.re,
    by rw [← hre, abs_div, abs_div, ← mul_assoc, div_mul_div,
      mul_comm (abs _), div_self (mul_ne_zero hay hax), one_mul],
  have him : abs (y / x) * x.im = y.im,
    by rw ← of_real_div at h;
      simpa [-of_real_div] using congr_arg im h,
  have him' : abs (x / y) * y.im = x.im,
    by rw [← him, abs_div, abs_div, ← mul_assoc, div_mul_div,
      mul_comm (abs _), div_self (mul_ne_zero hay hax), one_mul],
  have hxya : x.im / abs x = y.im / abs y,
    by rw [← him, abs_div, mul_comm, ← mul_div_comm, mul_div_cancel_left _ hay],
  have hnxya : (-x).im / abs x = (-y).im / abs y,
    by rw [neg_im, neg_im, neg_div, neg_div, hxya],
  if hxr : 0 ≤ x.re
  then
    have hyr : 0 ≤ y.re, from hre ▸ mul_nonneg (abs_nonneg _) hxr,
    by simp [arg, *] at *
  else
    have hyr : ¬ 0 ≤ y.re, from λ hyr, hxr $ hre' ▸ mul_nonneg (abs_nonneg _) hyr,
    if hxi : 0 ≤ x.im
    then
      have hyi : 0 ≤ y.im, from him ▸ mul_nonneg (abs_nonneg _) hxi,
      by simp [arg, *] at *
    else
      have hyi : ¬ 0 ≤ y.im, from λ hyi, hxi $ him' ▸ mul_nonneg (abs_nonneg _) hyi,
      by simp [arg, *] at *⟩

lemma arg_real_mul (x : ℂ) {r : ℝ} (hr : 0 < r) : arg (r * x) = arg x :=
if hx : x = 0 then by simp [hx]
else (arg_eq_arg_iff (mul_ne_zero (of_real_ne_zero.2 (ne_of_lt hr).symm) hx) hx).2 $
  by rw [abs_mul, abs_of_nonneg (le_of_lt hr), ← mul_assoc,
    of_real_mul, mul_comm (r : ℂ), ← div_div_eq_div_mul,
    div_mul_cancel _ (of_real_ne_zero.2 (ne_of_lt hr).symm),
    div_self (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), one_mul]

lemma ext_abs_arg {x y : ℂ} (h₁ : x.abs = y.abs) (h₂ : x.arg = y.arg) : x = y :=
if hy : y = 0 then by simp * at *
else have hx : x ≠ 0, from λ hx, by simp [*, eq_comm] at *,
  by rwa [arg_eq_arg_iff hx hy, h₁, div_self (of_real_ne_zero.2 (mt abs_eq_zero.1 hy)), one_mul]
    at h₂

lemma arg_of_real_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arg x = 0 :=
by simp [arg, hx]

lemma arg_of_real_of_neg {x : ℝ} (hx : x < 0) : arg x = π :=
by rw [arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg, ← of_real_neg, arg_of_real_of_nonneg];
  simp [*, le_iff_eq_or_lt, lt_neg]

/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0`-/
@[pp_nodot] noncomputable def log (x : ℂ) : ℂ := x.abs.log + arg x * I

lemma log_re (x : ℂ) : x.log.re = x.abs.log := by simp [log]

lemma log_im (x : ℂ) : x.log.im = x.arg := by simp [log]

lemma exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x :=
by rw [log, exp_add_mul_I, ← of_real_sin, sin_arg, ← of_real_cos, cos_arg hx,
  ← of_real_exp, real.exp_log (abs_pos.2 hx), mul_add, of_real_div, of_real_div,
  mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), ← mul_assoc,
  mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), re_add_im]

lemma range_exp : range exp = {x | x ≠ 0} :=
set.ext $ λ x, ⟨by { rintro ⟨x, rfl⟩, exact exp_ne_zero x }, λ hx, ⟨log x, exp_log hx⟩⟩

lemma exp_inj_of_neg_pi_lt_of_le_pi {x y : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π)
  (hy₁ : - π < y.im) (hy₂ : y.im ≤ π) (hxy : exp x = exp y) : x = y :=
by rw [exp_eq_exp_re_mul_sin_add_cos, exp_eq_exp_re_mul_sin_add_cos y] at hxy;
  exact complex.ext
    (real.exp_injective $
      by simpa [abs_mul, abs_cos_add_sin_mul_I] using congr_arg complex.abs hxy)
    (by simpa [(of_real_exp _).symm, - of_real_exp, arg_real_mul _ (real.exp_pos _),
      arg_cos_add_sin_mul_I hx₁ hx₂, arg_cos_add_sin_mul_I hy₁ hy₂] using congr_arg arg hxy)

lemma log_exp {x : ℂ} (hx₁ : -π < x.im) (hx₂: x.im ≤ π) : log (exp x) = x :=
exp_inj_of_neg_pi_lt_of_le_pi
  (by rw log_im; exact neg_pi_lt_arg _)
  (by rw log_im; exact arg_le_pi _)
  hx₁ hx₂ (by rw [exp_log (exp_ne_zero _)])

lemma of_real_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x :=
complex.ext
  (by rw [log_re, of_real_re, abs_of_nonneg hx])
  (by rw [of_real_im, log_im, arg_of_real_of_nonneg hx])

lemma log_of_real_re (x : ℝ) : (log (x : ℂ)).re = real.log x := by simp [log_re]

@[simp] lemma log_zero : log 0 = 0 := by simp [log]

@[simp] lemma log_one : log 1 = 0 := by simp [log]

lemma log_neg_one : log (-1) = π * I := by simp [log]

lemma log_I : log I = π / 2 * I := by simp [log]

lemma log_neg_I : log (-I) = -(π / 2) * I := by simp [log]

lemma exists_pow_nat_eq (x : ℂ) {n : ℕ} (hn : 0 < n) : ∃ z, z ^ n = x :=
begin
  by_cases hx : x = 0,
  { use 0, simp only [hx, zero_pow_eq_zero, hn] },
  { use exp (log x / n),
    rw [← exp_nat_mul, mul_div_cancel', exp_log hx],
    exact_mod_cast (pos_iff_ne_zero.mp hn) }
end

lemma exists_eq_mul_self (x : ℂ) : ∃ z, x = z * z :=
begin
  obtain ⟨z, rfl⟩ := exists_pow_nat_eq x zero_lt_two,
  exact ⟨z, pow_two z⟩
end

lemma two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 :=
by norm_num [real.pi_ne_zero, I_ne_zero]

lemma exp_eq_one_iff {x : ℂ} : exp x = 1 ↔ ∃ n : ℤ, x = n * ((2 * π) * I) :=
have real.exp (x.re) * real.cos (x.im) = 1 → real.cos x.im ≠ -1,
  from λ h₁ h₂, begin
    rw [h₂, mul_neg_eq_neg_mul_symm, mul_one, neg_eq_iff_neg_eq] at h₁,
    have := real.exp_pos x.re,
    rw ← h₁ at this,
    exact absurd this (by norm_num)
  end,
calc exp x = 1 ↔ (exp x).re = 1 ∧ (exp x).im = 0 : by simp [complex.ext_iff]
  ... ↔ real.cos x.im = 1 ∧ real.sin x.im = 0 ∧ x.re = 0 :
    begin
      rw exp_eq_exp_re_mul_sin_add_cos,
      simp [complex.ext_iff, cos_of_real_re, sin_of_real_re, exp_of_real_re,
        real.exp_ne_zero],
      split; finish [real.sin_eq_zero_iff_cos_eq]
    end
  ... ↔ (∃ n : ℤ, ↑n * (2 * π) = x.im) ∧ (∃ n : ℤ, ↑n * π = x.im) ∧ x.re = 0 :
    by rw [real.sin_eq_zero_iff, real.cos_eq_one_iff]
  ... ↔ ∃ n : ℤ, x = n * ((2 * π) * I) :
    ⟨λ ⟨⟨n, hn⟩, ⟨m, hm⟩, h⟩, ⟨n, by simp [complex.ext_iff, hn.symm, h]⟩,
      λ ⟨n, hn⟩, ⟨⟨n, by simp [hn]⟩, ⟨2 * n, by simp [hn, mul_comm, mul_assoc, mul_left_comm]⟩,
        by simp [hn]⟩⟩

lemma exp_eq_exp_iff_exp_sub_eq_one {x y : ℂ} : exp x = exp y ↔ exp (x - y) = 1 :=
by rw [exp_sub, div_eq_one_iff_eq (exp_ne_zero _)]

lemma exp_eq_exp_iff_exists_int {x y : ℂ} : exp x = exp y ↔ ∃ n : ℤ, x = y + n * ((2 * π) * I) :=
by simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']

@[simp] lemma cos_pi_div_two : cos (π / 2) = 0 :=
calc cos (π / 2) = real.cos (π / 2) : by rw [of_real_cos]; simp
... = 0 : by simp

@[simp] lemma sin_pi_div_two : sin (π / 2) = 1 :=
calc sin (π / 2) = real.sin (π / 2) : by rw [of_real_sin]; simp
... = 1 : by simp

@[simp] lemma sin_pi : sin π = 0 :=
by rw [← of_real_sin, real.sin_pi]; simp

@[simp] lemma cos_pi : cos π = -1 :=
by rw [← of_real_cos, real.cos_pi]; simp

@[simp] lemma sin_two_pi : sin (2 * π) = 0 :=
by simp [two_mul, sin_add]

@[simp] lemma cos_two_pi : cos (2 * π) = 1 :=
by simp [two_mul, cos_add]

lemma sin_add_pi (x : ℂ) : sin (x + π) = -sin x :=
by simp [sin_add]

lemma sin_add_two_pi (x : ℂ) : sin (x + 2 * π) = sin x :=
by simp [sin_add_pi, sin_add, sin_two_pi, cos_two_pi]

lemma cos_add_two_pi (x : ℂ) : cos (x + 2 * π) = cos x :=
by simp [cos_add, cos_two_pi, sin_two_pi]

lemma sin_pi_sub (x : ℂ) : sin (π - x) = sin x :=
by simp [sub_eq_add_neg, sin_add]

lemma cos_add_pi (x : ℂ) : cos (x + π) = -cos x :=
by simp [cos_add]

lemma cos_pi_sub (x : ℂ) : cos (π - x) = -cos x :=
by simp [sub_eq_add_neg, cos_add]

lemma sin_add_pi_div_two (x : ℂ) : sin (x + π / 2) = cos x :=
by simp [sin_add]

lemma sin_sub_pi_div_two (x : ℂ) : sin (x - π / 2) = -cos x :=
by simp [sub_eq_add_neg, sin_add]

lemma sin_pi_div_two_sub (x : ℂ) : sin (π / 2 - x) = cos x :=
by simp [sub_eq_add_neg, sin_add]

lemma cos_add_pi_div_two (x : ℂ) : cos (x + π / 2) = -sin x :=
by simp [cos_add]

lemma cos_sub_pi_div_two (x : ℂ) : cos (x - π / 2) = sin x :=
by simp [sub_eq_add_neg, cos_add]

lemma cos_pi_div_two_sub (x : ℂ) : cos (π / 2 - x) = sin x :=
by rw [← cos_neg, neg_sub, cos_sub_pi_div_two]

lemma sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
by induction n; simp [add_mul, sin_add, *]

lemma sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
by cases n; simp [add_mul, sin_add, *, sin_nat_mul_pi]

lemma cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
by induction n; simp [*, mul_add, cos_add, add_mul, cos_two_pi, sin_two_pi]

lemma cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
by cases n; simp only [cos_nat_mul_two_pi, int.of_nat_eq_coe,
  int.neg_succ_of_nat_coe, int.cast_coe_nat, int.cast_neg,
  (neg_mul_eq_neg_mul _ _).symm, cos_neg]

lemma cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 :=
by simp [cos_add, sin_add, cos_int_mul_two_pi]

lemma exp_pi_mul_I : exp (π * I) = -1 :=
by rw exp_mul_I; simp

theorem cos_eq_zero_iff {θ : ℂ} : cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * π / 2 :=
begin
  have h : (exp (θ * I) + exp (-θ * I)) / 2 = 0 ↔ exp (2 * θ * I) = -1,
  { rw [@div_eq_iff _ _ (exp (θ * I) + exp (-θ * I)) 2 0 two_ne_zero', zero_mul,
      add_eq_zero_iff_eq_neg, neg_eq_neg_one_mul, ← div_eq_iff (exp_ne_zero _), ← exp_sub],
    field_simp only, congr' 3, ring },
  rw [cos, h, ← exp_pi_mul_I, exp_eq_exp_iff_exists_int, mul_right_comm],
  refine exists_congr (λ x, _),
  refine (iff_of_eq $ congr_arg _ _).trans (mul_right_inj' $ mul_ne_zero two_ne_zero' I_ne_zero),
  ring,
end

theorem cos_ne_zero_iff {θ : ℂ} : cos θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ (2 * k + 1) * π / 2 :=
by rw [← not_exists, not_iff_not, cos_eq_zero_iff]

theorem sin_eq_zero_iff {θ : ℂ} : sin θ = 0 ↔ ∃ k : ℤ, θ = k * π :=
begin
  rw [← complex.cos_sub_pi_div_two, cos_eq_zero_iff],
  split,
  { rintros ⟨k, hk⟩,
    use k + 1,
    field_simp [eq_add_of_sub_eq hk],
    ring },
  { rintros ⟨k, rfl⟩,
    use k - 1,
    field_simp,
    ring }
end

theorem sin_ne_zero_iff {θ : ℂ} : sin θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ k * π :=
by rw [← not_exists, not_iff_not, sin_eq_zero_iff]

lemma sin_eq_zero_iff_cos_eq {z : ℂ} : sin z = 0 ↔ cos z = 1 ∨ cos z = -1 :=
by rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq, pow_two, pow_two, ← sub_eq_iff_eq_add, sub_self];
  exact ⟨λ h, by rw [h, mul_zero], eq_zero_of_mul_self_eq_zero ∘ eq.symm⟩

lemma tan_eq_zero_iff {θ : ℂ} : tan θ = 0 ↔ ∃ k : ℤ, θ = k * π / 2 :=
begin
  have h := (sin_two_mul θ).symm,
  rw mul_assoc at h,
  rw [tan, div_eq_zero_iff, ← mul_eq_zero, ← zero_mul ((1/2):ℂ), mul_one_div,
      cancel_factors.cancel_factors_eq_div h two_ne_zero', mul_comm],
  simpa only [zero_div, zero_mul, ne.def, not_false_iff] with field_simps using sin_eq_zero_iff,
end

lemma tan_ne_zero_iff {θ : ℂ} : tan θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ k * π / 2 :=
by rw [← not_exists, not_iff_not, tan_eq_zero_iff]

lemma tan_int_mul_pi_div_two (n : ℤ) : tan (n * π/2) = 0 :=
tan_eq_zero_iff.mpr (by use n)

lemma tan_int_mul_pi (n : ℤ) : tan (n * π) = 0 :=
by rw tan_eq_zero_iff; use (2*n); field_simp [mul_comm ((n:ℂ)*(π:ℂ)) 2, ← mul_assoc]

lemma cos_eq_cos_iff {x y : ℂ} :
  cos x = cos y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x :=
calc cos x = cos y ↔ cos x - cos y = 0 : sub_eq_zero.symm
... ↔ -2 * sin((x + y)/2) * sin((x - y)/2) = 0 : by rw cos_sub_cos
... ↔ sin((x + y)/2) = 0 ∨ sin((x - y)/2) = 0 : by simp [(by norm_num : (2:ℂ) ≠ 0)]
... ↔ sin((x - y)/2) = 0 ∨ sin((x + y)/2) = 0 : or.comm
... ↔ (∃ k : ℤ, y = 2 * k * π + x) ∨ (∃ k :ℤ, y = 2 * k * π - x) :
begin
  apply or_congr;
    field_simp [sin_eq_zero_iff, (by norm_num : -(2:ℂ) ≠ 0), eq_sub_iff_add_eq',
      sub_eq_iff_eq_add, mul_comm (2:ℂ), mul_right_comm _ (2:ℂ)],
  split; { rintros ⟨k, rfl⟩, use -k, simp, },
end
... ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x : exists_or_distrib.symm

lemma sin_eq_sin_iff {x y : ℂ} :
  sin x = sin y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = (2 * k + 1) * π - x :=
begin
  simp only [← complex.cos_sub_pi_div_two, cos_eq_cos_iff, sub_eq_iff_eq_add],
  refine exists_congr (λ k, or_congr _ _); refine eq.congr rfl _; field_simp; ring
end

lemma tan_add {x y : ℂ}
  (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2)
     ∨ ((∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y = (2 * l + 1) * π / 2)) :
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
begin
  rcases h with ⟨h1, h2⟩ | ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩,
  { rw [tan, sin_add, cos_add,
        ← div_div_div_cancel_right (sin x * cos y + cos x * sin y)
            (mul_ne_zero (cos_ne_zero_iff.mpr h1) (cos_ne_zero_iff.mpr h2)),
        add_div, sub_div],
    simp only [←div_mul_div, ←tan, mul_one, one_mul,
              div_self (cos_ne_zero_iff.mpr h1), div_self (cos_ne_zero_iff.mpr h2)] },
  { obtain ⟨t, hx, hy, hxy⟩ := ⟨tan_int_mul_pi_div_two, t (2*k+1), t (2*l+1), t (2*k+1+(2*l+1))⟩,
    simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, hx, hy] at hx hy hxy,
    rw [hx, hy, add_zero, zero_div,
        mul_div_assoc, mul_div_assoc, ← add_mul (2*(k:ℂ)+1) (2*l+1) (π/2), ← mul_div_assoc, hxy] },
end

lemma tan_add' {x y : ℂ}
  (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2)) :
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
tan_add (or.inl h)

lemma tan_two_mul {z : ℂ} : tan (2 * z) = 2 * tan z / (1 - tan z ^ 2) :=
begin
  by_cases h : ∀ k : ℤ, z ≠ (2 * k + 1) * π / 2,
  { rw [two_mul, two_mul, pow_two, tan_add (or.inl ⟨h, h⟩)] },
  { rw not_forall_not at h,
    rw [two_mul, two_mul, pow_two, tan_add (or.inr ⟨h, h⟩)] },
end

lemma tan_add_mul_I {x y : ℂ}
  (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y * I ≠ (2 * l + 1) * π / 2)
     ∨ ((∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y * I = (2 * l + 1) * π / 2)) :
  tan (x + y*I) = (tan x + tanh y * I) / (1 - tan x * tanh y * I) :=
by rw [tan_add h, tan_mul_I, mul_assoc]

lemma tan_eq {z : ℂ}
  (h : ((∀ k : ℤ, (z.re:ℂ) ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, (z.im:ℂ) * I ≠ (2 * l + 1) * π / 2)
     ∨ ((∃ k : ℤ, (z.re:ℂ) = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, (z.im:ℂ) * I = (2 * l + 1) * π / 2)) :
  tan z = (tan z.re + tanh z.im * I) / (1 - tan z.re * tanh z.im * I) :=
by convert tan_add_mul_I h; exact (re_add_im z).symm

lemma has_deriv_at_tan {x : ℂ} (h : cos x ≠ 0) :
  has_deriv_at tan (1 / (cos x)^2) x :=
begin
  convert has_deriv_at.div (has_deriv_at_sin x) (has_deriv_at_cos x) h,
  rw ← sin_sq_add_cos_sq x,
  ring,
end

lemma tendsto_abs_tan_of_cos_eq_zero {x : ℂ} (hx : cos x = 0) :
  tendsto (λ x, abs (tan x)) (𝓝[{x}ᶜ] x) at_top :=
begin
  simp_rw [tan_eq_sin_div_cos, abs_div, div_eq_mul_inv],
  have A : sin x ≠ 0 := λ h, by simpa [*, pow_two] using sin_sq_add_cos_sq x,
  have B : tendsto cos (𝓝[{x}ᶜ] (x)) (𝓝[{0}ᶜ] 0),
  { refine tendsto_inf.2 ⟨tendsto.mono_left _ inf_le_left, tendsto_principal.2 _⟩,
    exacts [continuous_cos.tendsto' x 0 hx,
      hx ▸ (has_deriv_at_cos _).eventually_ne (neg_ne_zero.2 A)] },
  exact continuous_sin.continuous_within_at.norm.mul_at_top (norm_pos_iff.2 A) 
    (tendsto.inv_tendsto_zero $ tendsto_norm_nhds_within_zero.comp B),
end

lemma tendsto_abs_tan_at_top (k : ℤ) :
  tendsto (λ x, abs (tan x)) (𝓝[{(2 * k + 1) * π / 2}ᶜ] ((2 * k + 1) * π / 2)) at_top :=
tendsto_abs_tan_of_cos_eq_zero $ cos_eq_zero_iff.2 ⟨k, rfl⟩

@[simp] lemma continuous_at_tan {x : ℂ} : continuous_at tan x ↔ cos x ≠ 0 :=
begin
  refine ⟨λ hc h₀, _, λ h, (has_deriv_at_tan h).continuous_at⟩,
  exact not_tendsto_nhds_of_tendsto_at_top (tendsto_abs_tan_of_cos_eq_zero h₀) _
    (hc.norm.tendsto.mono_left inf_le_left)
end

@[simp] lemma differentiable_at_tan {x : ℂ} : differentiable_at ℂ tan x ↔ cos x ≠ 0:=
⟨λ h, continuous_at_tan.1 h.continuous_at, λ h, (has_deriv_at_tan h).differentiable_at⟩

@[simp] lemma deriv_tan (x : ℂ) : deriv tan x = 1 / (cos x)^2 :=
if h : cos x = 0 then
  have ¬differentiable_at ℂ tan x := mt differentiable_at_tan.1 (not_not.2 h),
  by simp [deriv_zero_of_not_differentiable_at this, h, pow_two]
else (has_deriv_at_tan h).deriv

lemma continuous_on_tan : continuous_on tan {x | cos x ≠ 0} :=
continuous_on_sin.div continuous_on_cos $ λ x, id

lemma continuous_tan : continuous (λ x : {x | cos x ≠ 0}, tan x) :=
continuous_on_iff_continuous_restrict.1 continuous_on_tan

@[simp] lemma times_cont_diff_at_tan {x : ℂ} {n : with_top ℕ} :
  times_cont_diff_at ℂ n tan x ↔ cos x ≠ 0 :=
⟨λ h, continuous_at_tan.1 h.continuous_at,
  times_cont_diff_sin.times_cont_diff_at.div times_cont_diff_cos.times_cont_diff_at⟩

lemma cos_eq_iff_quadratic {z w : ℂ} :
  cos z = w ↔ (exp (z * I)) ^ 2 - 2 * w * exp (z * I) + 1 = 0 :=
begin
  rw ← sub_eq_zero,
  field_simp [cos, exp_neg, exp_ne_zero],
  refine eq.congr _ rfl,
  ring
end

lemma cos_surjective : function.surjective cos :=
begin
  intro x,
  obtain ⟨w, w₀, hw⟩ : ∃ w ≠ 0, 1 * w * w + (-2 * x) * w + 1 = 0,
  { rcases exists_quadratic_eq_zero one_ne_zero (exists_eq_mul_self _) with ⟨w, hw⟩,
    refine ⟨w, _, hw⟩,
    rintro rfl,
    simpa only [zero_add, one_ne_zero, mul_zero] using hw },
  refine ⟨log w / I, cos_eq_iff_quadratic.2 _⟩,
  rw [div_mul_cancel _ I_ne_zero, exp_log w₀],
  convert hw,
  ring
end

@[simp] lemma range_cos : range cos = set.univ :=
cos_surjective.range_eq

lemma sin_surjective : function.surjective sin :=
begin
  intro x,
  rcases cos_surjective x with ⟨z, rfl⟩,
  exact ⟨z + π / 2, sin_add_pi_div_two z⟩
end

@[simp] lemma range_sin : range sin = set.univ :=
sin_surjective.range_eq

end complex

section chebyshev₁

open polynomial complex

/-- the `n`-th Chebyshev polynomial evaluates on `cos θ` to the value `cos (n * θ)`. -/
lemma chebyshev₁_complex_cos (θ : ℂ) :
  ∀ n, (chebyshev₁ ℂ n).eval (cos θ) = cos (n * θ)
| 0       := by simp only [chebyshev₁_zero, eval_one, nat.cast_zero, zero_mul, cos_zero]
| 1       := by simp only [eval_X, one_mul, chebyshev₁_one, nat.cast_one]
| (n + 2) :=
begin
  simp only [eval_X, eval_one, chebyshev₁_add_two, eval_sub, eval_bit0, nat.cast_succ, eval_mul],
  rw [chebyshev₁_complex_cos (n + 1), chebyshev₁_complex_cos n],
  have aux : sin θ * sin θ = 1 - cos θ * cos θ,
  { rw ← sin_sq_add_cos_sq θ, ring, },
  simp only [nat.cast_add, nat.cast_one, add_mul, cos_add, one_mul, sin_add, mul_assoc, aux],
  ring,
end

/-- `cos (n * θ)` is equal to the `n`-th Chebyshev polynomial evaluated on `cos θ`. -/
lemma cos_nat_mul (n : ℕ) (θ : ℂ) :
  cos (n * θ) = (chebyshev₁ ℂ n).eval (cos θ) :=
(chebyshev₁_complex_cos θ n).symm

end chebyshev₁

namespace real
open_locale real

lemma tan_add {x y : ℝ}
  (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2)
     ∨ ((∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y = (2 * l + 1) * π / 2)) :
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
by simpa only [← complex.of_real_inj, complex.of_real_sub, complex.of_real_add, complex.of_real_div,
              complex.of_real_mul, complex.of_real_tan]
    using @complex.tan_add (x:ℂ) (y:ℂ) (by convert h; norm_cast)

lemma tan_add' {x y : ℝ}
  (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2)) :
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
tan_add (or.inl h)

lemma tan_two_mul {x:ℝ} : tan (2 * x) = 2 * tan x / (1 - tan x ^ 2) :=
by simpa only [← complex.of_real_inj, complex.of_real_sub, complex.of_real_div, complex.of_real_pow,
              complex.of_real_mul, complex.of_real_tan, complex.of_real_bit0, complex.of_real_one]
    using complex.tan_two_mul

theorem cos_eq_zero_iff {θ : ℝ} : cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * π / 2 :=
by exact_mod_cast @complex.cos_eq_zero_iff θ

theorem cos_ne_zero_iff {θ : ℝ} : cos θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ (2 * k + 1) * π / 2 :=
by rw [← not_exists, not_iff_not, cos_eq_zero_iff]

lemma tan_ne_zero_iff {θ : ℝ} : tan θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ k * π / 2 :=
by rw [← complex.of_real_ne_zero, complex.of_real_tan, complex.tan_ne_zero_iff]; norm_cast

lemma tan_eq_zero_iff {θ : ℝ} : tan θ = 0 ↔ ∃ k : ℤ, θ = k * π / 2 :=
by rw [← not_iff_not, not_exists, ← ne, tan_ne_zero_iff]

lemma tan_int_mul_pi_div_two (n : ℤ) : tan (n * π/2) = 0 :=
tan_eq_zero_iff.mpr (by use n)

lemma tan_int_mul_pi (n : ℤ) : tan (n * π) = 0 :=
by rw tan_eq_zero_iff; use (2*n); field_simp [mul_comm ((n:ℝ)*(π:ℝ)) 2, ← mul_assoc]

lemma cos_eq_cos_iff {x y : ℝ} :
  cos x = cos y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x :=
by exact_mod_cast @complex.cos_eq_cos_iff x y

lemma sin_eq_sin_iff {x y : ℝ} :
  sin x = sin y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = (2 * k + 1) * π - x :=
by exact_mod_cast @complex.sin_eq_sin_iff x y

lemma has_deriv_at_tan {x : ℝ} (h : cos x ≠ 0) :
  has_deriv_at tan (1 / (cos x)^2) x :=
by exact_mod_cast (complex.has_deriv_at_tan (by exact_mod_cast h)).real_of_complex

lemma tendsto_abs_tan_of_cos_eq_zero {x : ℝ} (hx : cos x = 0) :
  tendsto (λ x, abs (tan x)) (𝓝[{x}ᶜ] x) at_top :=
begin
  have hx : complex.cos x = 0, by exact_mod_cast hx,
  simp only [← complex.abs_of_real, complex.of_real_tan],
  refine (complex.tendsto_abs_tan_of_cos_eq_zero hx).comp _,
  refine tendsto.inf complex.continuous_of_real.continuous_at _,
  exact tendsto_principal_principal.2 (λ y, mt complex.of_real_inj.1)
end

lemma tendsto_abs_tan_at_top (k : ℤ) :
  tendsto (λ x, abs (tan x)) (𝓝[{(2 * k + 1) * π / 2}ᶜ] ((2 * k + 1) * π / 2)) at_top :=
tendsto_abs_tan_of_cos_eq_zero $ cos_eq_zero_iff.2 ⟨k, rfl⟩

lemma continuous_at_tan {x : ℝ} : continuous_at tan x ↔ cos x ≠ 0 :=
begin
  refine ⟨λ hc h₀, _, λ h, (has_deriv_at_tan h).continuous_at⟩,
  exact not_tendsto_nhds_of_tendsto_at_top (tendsto_abs_tan_of_cos_eq_zero h₀) _
    (hc.norm.tendsto.mono_left inf_le_left)
end

lemma differentiable_at_tan {x : ℝ} : differentiable_at ℝ tan x ↔ cos x ≠ 0 :=
⟨λ h, continuous_at_tan.1 h.continuous_at, λ h, (has_deriv_at_tan h).differentiable_at⟩

@[simp] lemma deriv_tan (x : ℝ) : deriv tan x = 1 / (cos x)^2 :=
if h : cos x = 0 then
  have ¬differentiable_at ℝ tan x := mt differentiable_at_tan.1 (not_not.2 h),
  by simp [deriv_zero_of_not_differentiable_at this, h, pow_two]
else (has_deriv_at_tan h).deriv

@[simp] lemma times_cont_diff_at_tan {n x} : times_cont_diff_at ℝ n tan x ↔ cos x ≠ 0 :=
⟨λ h, continuous_at_tan.1 h.continuous_at,
  λ h, (complex.times_cont_diff_at_tan.2 $ by exact_mod_cast h).real_of_complex⟩

lemma continuous_on_tan : continuous_on tan {x | cos x ≠ 0} :=
λ x hx, (continuous_at_tan.2 hx).continuous_within_at

lemma has_deriv_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π/2):ℝ) (π/2)) :
  has_deriv_at tan (1 / (cos x)^2) x :=
has_deriv_at_tan (cos_pos_of_mem_Ioo h).ne'

lemma differentiable_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π/2):ℝ) (π/2)) :
  differentiable_at ℝ tan x :=
(has_deriv_at_tan_of_mem_Ioo h).differentiable_at

lemma continuous_on_tan_Ioo : continuous_on tan (Ioo (-(π/2)) (π/2)) :=
λ x hx, (differentiable_at_tan_of_mem_Ioo hx).continuous_at.continuous_within_at

lemma tendsto_sin_pi_div_two : tendsto sin (𝓝[Iio (π/2)] (π/2)) (𝓝 1) :=
by { convert continuous_sin.continuous_within_at, simp }

lemma tendsto_cos_pi_div_two : tendsto cos (𝓝[Iio (π/2)] (π/2)) (𝓝[Ioi 0] 0) :=
begin
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
  { convert continuous_cos.continuous_within_at, simp },
  { filter_upwards [Ioo_mem_nhds_within_Iio (right_mem_Ioc.mpr (norm_num.lt_neg_pos
      _ _ pi_div_two_pos pi_div_two_pos))] λ x hx, cos_pos_of_mem_Ioo hx },
end

lemma tendsto_tan_pi_div_two : tendsto tan (𝓝[Iio (π/2)] (π/2)) at_top :=
begin
  convert (tendsto.inv_tendsto_zero tendsto_cos_pi_div_two).at_top_mul (by norm_num)
            tendsto_sin_pi_div_two,
  simp only [pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]
end

lemma tendsto_sin_neg_pi_div_two : tendsto sin (𝓝[Ioi (-(π/2))] (-(π/2))) (𝓝 (-1)) :=
by { convert continuous_sin.continuous_within_at, simp }

lemma tendsto_cos_neg_pi_div_two : tendsto cos (𝓝[Ioi (-(π/2))] (-(π/2))) (𝓝[Ioi 0] 0) :=
begin
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
  { convert continuous_cos.continuous_within_at, simp },
  { filter_upwards [Ioo_mem_nhds_within_Ioi (left_mem_Ico.mpr (norm_num.lt_neg_pos
      _ _ pi_div_two_pos pi_div_two_pos))] λ x hx, cos_pos_of_mem_Ioo hx },
end

lemma tendsto_tan_neg_pi_div_two : tendsto tan (𝓝[Ioi (-(π/2))] (-(π/2))) at_bot :=
begin
  convert (tendsto.inv_tendsto_zero tendsto_cos_neg_pi_div_two).at_top_mul_neg (by norm_num)
            tendsto_sin_neg_pi_div_two,
  simp only [pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]
end

lemma surj_on_tan : surj_on tan (Ioo (-(π / 2)) (π / 2)) univ :=
have _ := neg_lt_self pi_div_two_pos,
continuous_on_tan_Ioo.surj_on_of_tendsto (nonempty_Ioo.2 this)
  (by simp [tendsto_tan_neg_pi_div_two, this]) (by simp [tendsto_tan_pi_div_two, this])

lemma tan_surjective : function.surjective tan :=
λ x, surj_on_tan.subset_range trivial

lemma image_tan_Ioo : tan '' (Ioo (-(π / 2)) (π / 2)) = univ :=
univ_subset_iff.1 surj_on_tan

/-- `real.tan` as an `order_iso` between `(-(π / 2), π / 2)` and `ℝ`. -/
def tan_order_iso : Ioo (-(π / 2)) (π / 2) ≃o ℝ :=
(strict_mono_incr_on_tan.order_iso _ _).trans $ (order_iso.set_congr _ _ image_tan_Ioo).trans
  order_iso.set.univ

/-- Inverse of the `tan` function, returns values in the range `-π / 2 < arctan x` and
`arctan x < π / 2` -/
@[pp_nodot] noncomputable def arctan (x : ℝ) : ℝ :=
tan_order_iso.symm x

@[simp] lemma tan_arctan (x : ℝ) : tan (arctan x) = x :=
tan_order_iso.apply_symm_apply x

lemma arctan_mem_Ioo (x : ℝ) : arctan x ∈ Ioo (-(π / 2)) (π / 2) :=
subtype.coe_prop _

lemma arctan_tan {x : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2) : arctan (tan x) = x :=
subtype.ext_iff.1 $ tan_order_iso.symm_apply_apply ⟨x, hx₁, hx₂⟩

lemma cos_arctan_pos (x : ℝ) : 0 < cos (arctan x) :=
cos_pos_of_mem_Ioo $ arctan_mem_Ioo x

lemma cos_sq_arctan (x : ℝ) : cos (arctan x) ^ 2 = 1 / (1 + x ^ 2) :=
by rw [one_div, ← inv_one_add_tan_sq (cos_arctan_pos x).ne', tan_arctan]

lemma sin_arctan (x : ℝ) : sin (arctan x) = x / sqrt (1 + x ^ 2) :=
by rw [← tan_div_sqrt_one_add_tan_sq (cos_arctan_pos x), tan_arctan]

lemma cos_arctan (x : ℝ) : cos (arctan x) = 1 / sqrt (1 + x ^ 2) :=
by rw [one_div, ← inv_sqrt_one_add_tan_sq (cos_arctan_pos x), tan_arctan]

lemma arctan_lt_pi_div_two (x : ℝ) : arctan x < π / 2 :=
(arctan_mem_Ioo x).2

lemma neg_pi_div_two_lt_arctan (x : ℝ) : -(π / 2) < arctan x :=
(arctan_mem_Ioo x).1

lemma arctan_eq_arcsin (x : ℝ) : arctan x = arcsin (x / sqrt (1 + x ^ 2)) :=
eq.symm $ arcsin_eq_of_sin_eq (sin_arctan x) (mem_Icc_of_Ioo $ arctan_mem_Ioo x)

@[simp] lemma arctan_zero : arctan 0 = 0 :=
by simp [arctan_eq_arcsin]

lemma arctan_eq_of_tan_eq {x y : ℝ} (h : tan x = y) (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
  arctan y = x :=
inj_on_tan (arctan_mem_Ioo _) hx (by rw [tan_arctan, h])

@[simp] lemma arctan_one : arctan 1 = π / 4 :=
arctan_eq_of_tan_eq tan_pi_div_four $ by split; linarith [pi_pos]

@[simp] lemma arctan_neg (x : ℝ) : arctan (-x) = - arctan x :=
by simp [arctan_eq_arcsin, neg_div]

lemma continuous_arctan : continuous arctan :=
continuous_subtype_coe.comp tan_order_iso.to_homeomorph.continuous_inv_fun

lemma continuous_at_arctan {x : ℝ} : continuous_at arctan x := continuous_arctan.continuous_at

/-- `real.tan` as a `local_homeomorph` between `(-(π / 2), π / 2)` and the whole line. -/
def tan_local_homeomorph : local_homeomorph ℝ ℝ :=
{ to_fun := tan,
  inv_fun := arctan,
  source := Ioo (-(π / 2)) (π / 2),
  target := univ,
  map_source' := maps_to_univ _ _,
  map_target' := λ y hy, arctan_mem_Ioo y,
  left_inv' := λ x hx, arctan_tan hx.1 hx.2,
  right_inv' := λ y hy, tan_arctan y,
  open_source := is_open_Ioo,
  open_target := is_open_univ,
  continuous_to_fun := continuous_on_tan_Ioo,
  continuous_inv_fun := continuous_arctan.continuous_on }

@[simp] lemma coe_tan_local_homeomorph : ⇑tan_local_homeomorph = tan := rfl
@[simp] lemma coe_tan_local_homeomorph_symm : ⇑tan_local_homeomorph.symm = arctan := rfl

lemma has_deriv_at_arctan (x : ℝ) : has_deriv_at arctan (1 / (1 + x^2)) x :=
have A : cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne',
by simpa [cos_sq_arctan]
  using tan_local_homeomorph.has_deriv_at_symm trivial (by simpa) (has_deriv_at_tan A)

lemma differentiable_at_arctan (x : ℝ) : differentiable_at ℝ arctan x :=
(has_deriv_at_arctan x).differentiable_at

lemma differentiable_arctan : differentiable ℝ arctan := differentiable_at_arctan

@[simp] lemma deriv_arctan : deriv arctan = (λ x, 1 / (1 + x^2)) :=
funext $ λ x, (has_deriv_at_arctan x).deriv

lemma times_cont_diff_arctan {n : with_top ℕ} : times_cont_diff ℝ n arctan :=
times_cont_diff_iff_times_cont_diff_at.2 $ λ x,
have cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne',
tan_local_homeomorph.times_cont_diff_at_symm_deriv (by simpa) trivial (has_deriv_at_tan this)
  (times_cont_diff_at_tan.2 this)

lemma measurable_arctan : measurable arctan := continuous_arctan.measurable

end real

section
/-!
### Lemmas for derivatives of the composition of `real.arctan` with a differentiable function

In this section we register lemmas for the derivatives of the composition of `real.arctan` with a
differentiable function, for standalone use and use with `simp`. -/

open real

lemma measurable.arctan {α : Type*} [measurable_space α] {f : α → ℝ} (hf : measurable f) :
  measurable (λ x, arctan (f x)) :=
measurable_arctan.comp hf

section deriv

variables {f : ℝ → ℝ} {f' x : ℝ} {s : set ℝ}

lemma has_deriv_at.arctan (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) * f') x :=
(real.has_deriv_at_arctan (f x)).comp x hf

lemma has_deriv_within_at.arctan (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) * f') s x :=
(real.has_deriv_at_arctan (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_arctan (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λ x, arctan (f x)) s x = (1 / (1 + (f x)^2)) * (deriv_within f s x) :=
hf.has_deriv_within_at.arctan.deriv_within hxs

@[simp] lemma deriv_arctan (hc : differentiable_at ℝ f x) :
  deriv (λ x, arctan (f x)) x = (1 / (1 + (f x)^2)) * (deriv f x) :=
hc.has_deriv_at.arctan.deriv

end deriv

section fderiv

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
  {s : set E} {n : with_top ℕ}

lemma has_fderiv_at.arctan (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) • f') x :=
(has_deriv_at_arctan (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.arctan (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) • f') s x :=
(has_deriv_at_arctan (f x)).comp_has_fderiv_within_at x hf

lemma fderiv_within_arctan (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λ x, arctan (f x)) s x = (1 / (1 + (f x)^2)) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.arctan.fderiv_within hxs

@[simp] lemma fderiv_arctan (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λ x, arctan (f x)) x = (1 / (1 + (f x)^2)) • (fderiv ℝ f x) :=
hc.has_fderiv_at.arctan.fderiv

lemma differentiable_within_at.arctan (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.arctan (f x)) s x :=
hf.has_fderiv_within_at.arctan.differentiable_within_at

@[simp] lemma differentiable_at.arctan (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λ x, arctan (f x)) x :=
hc.has_fderiv_at.arctan.differentiable_at

lemma differentiable_on.arctan (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λ x, arctan (f x)) s :=
λ x h, (hc x h).arctan

@[simp] lemma differentiable.arctan (hc : differentiable ℝ f) :
  differentiable ℝ (λ x, arctan (f x)) :=
λ x, (hc x).arctan

lemma times_cont_diff_at.arctan (h : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, arctan (f x)) x :=
times_cont_diff_arctan.times_cont_diff_at.comp x h

lemma times_cont_diff.arctan (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, arctan (f x)) :=
times_cont_diff_arctan.comp h

lemma times_cont_diff_within_at.arctan (h : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, arctan (f x)) s x :=
times_cont_diff_arctan.comp_times_cont_diff_within_at h

lemma times_cont_diff_on.arctan (h : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, arctan (f x)) s :=
times_cont_diff_arctan.comp_times_cont_diff_on h

end fderiv
end
