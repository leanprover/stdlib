/-
Copyright (c) 2021 James Arthur, Benjamin Davidson, Andrew Souther. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Benjamin Davidson, Andrew Souther
-/
import measure_theory.interval_integral
import analysis.special_functions.sqrt

/-!
# Freek № 9: The Area of a Circle

In this file we show that the area of a disc with nonnegative radius `r` is `π * r^2`. The main
tools our proof uses are `volume_region_between_eq_integral`, which allows us to represent the area
of the disc as an integral, and `interval_integral.integral_eq_sub_of_has_deriv_at'_of_le`, the
second fundamental theorem of calculus.

We begin by defining `disc` in `ℝ × ℝ`, then show that `disc` can be represented as the
`region_between` two functions.

Though not necessary for the main proof, we nonetheless choose to include a proof of the
measurability of the disc in order to convince the reader that the set whose volume we will be
calculating is indeed measurable and our result is therefore meaningful.

In the main proof, `area_disc`, we use `volume_region_between_eq_integral` followed by
`interval_integral.integral_of_le` to reduce our goal to a single `interval_integral`:
  `∫ (x : ℝ) in -r..r, 2 * sqrt (r ^ 2 - x ^ 2) = π * r ^ 2`.
After disposing of the trivial case `r = 0`, we show that `λ x, 2 * sqrt (r ^ 2 - x ^ 2)` is equal
to the derivative of `λ x, r ^ 2 * arcsin (x / r) + x * sqrt (r ^ 2 - x ^ 2)` everywhere on
`Ioo (-r) r` and that those two functions are continuous, then apply the second fundamental theorem
of calculus with those facts. Some simple algebra then completes the proof.

Note that we choose to define `disc` as a set of points in `ℝ ⨯ ℝ`. This is admittedly not ideal; it
would be more natural to define `disc` as a `metric.ball` in `euclidean_space ℝ (fin 2)` (as well as
to provide a more general proof in higher dimensions). However, our proof indirectly relies on a
number of theorems (particularly `measure_theory.measure.prod_apply`) which do not yet exist for
Euclidean space, thus forcing us to use this less-preferable definition. As `measure_theory.pi`
continues to develop, it should eventually become possible to redefine `disc` and extend our proof
to the n-ball.
-/

open set real measure_theory interval_integral
open_locale real nnreal

/-- A disc of radius `r` is defined as the collection of points `(p.1, p.2)` in `ℝ × ℝ` such that
  `p.1 ^ 2 + p.2 ^ 2 < r ^ 2`.
  Note that this definition is not equivalent to `metric.ball (0 : ℝ × ℝ) r`. This was done
  intentionally because `dist` in `ℝ × ℝ` is defined as the uniform norm, making the `metric.ball`
  in `ℝ × ℝ` a square, not a disc.
  See the module docstring for an explanation of why we don't define the disc in Euclidean space. -/
def disc (r : ℝ) := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}

variable (r : ℝ≥0)

/-- A disc of radius `r` can be represented as the region between the two curves
  `λ x, - sqrt (r ^ 2 - x ^ 2)` and `λ x, sqrt (r ^ 2 - x ^ 2)`. -/
lemma disc_eq_region_between :
  disc r = region_between (λ x, -sqrt (r^2 - x^2)) (λ x, sqrt (r^2 - x^2)) (Ioc (-r) r) :=
begin
  ext p,
  simp only [disc, region_between, mem_set_of_eq, mem_Ioo, mem_Ioc, pi.neg_apply],
  split;
  intro h,
  { cases abs_lt_of_sq_lt_sq' (lt_of_add_lt_of_nonneg_left h (sq_nonneg p.2)) r.2,
    rw [add_comm, ← lt_sub_iff_add_lt] at h,
    exact ⟨⟨left, right.le⟩, sq_lt.mp h⟩ },
  { rw [add_comm, ← lt_sub_iff_add_lt],
    exact sq_lt.mpr h.2 },
end

/-- The disc is a `measurable_set`. -/
theorem measurable_set_disc : measurable_set (disc r) :=
by apply measurable_set_lt; apply continuous.measurable; continuity

/-- **Area of a Circle**: The area of a disc with radius `r` is `π * r ^ 2`. -/
theorem area_disc : volume (disc r) = nnreal.pi * r ^ 2 :=
begin
  let f := λ x, sqrt (r ^ 2 - x ^ 2),
  let F := λ x, (r:ℝ) ^ 2 * arcsin (r⁻¹ * x) + x * sqrt (r ^ 2 - x ^ 2),
  have hf : continuous f := by continuity,
  suffices : ∫ x in -r..r, 2 * f x = nnreal.pi * r ^ 2,
  { have h : integrable_on f (Ioc (-r) r) :=
      hf.integrable_on_Icc.mono_set Ioc_subset_Icc_self,
    calc  volume (disc r)
        = volume (region_between (λ x, -f x) f (Ioc (-r) r)) : by rw disc_eq_region_between
    ... = ennreal.of_real (∫ x in Ioc (-r:ℝ) r, (f - has_neg.neg ∘ f) x) :
          volume_region_between_eq_integral
            h.neg h measurable_set_Ioc (λ x hx, neg_le_self (sqrt_nonneg _))
    ... = ennreal.of_real (∫ x in (-r:ℝ)..r, 2 * f x) : by simp [two_mul, integral_of_le]
    ... = nnreal.pi * r ^ 2 : by rw_mod_cast [this, ← ennreal.coe_nnreal_eq], },
  obtain ⟨hle, (heq | hlt)⟩ := ⟨nnreal.coe_nonneg r, hle.eq_or_lt⟩, { simp [← heq] },
  have hderiv : ∀ x ∈ Ioo (-r:ℝ) r, has_deriv_at F (2 * f x) x,
  { rintros x ⟨hx1, hx2⟩,
    convert ((has_deriv_at_const x ((r:ℝ)^2)).mul ((has_deriv_at_arcsin _ _).comp x
      ((has_deriv_at_const x (r:ℝ)⁻¹).mul (has_deriv_at_id' x)))).add
        ((has_deriv_at_id' x).mul (((has_deriv_at_id' x).pow.const_sub ((r:ℝ)^2)).sqrt _)),
    { have h : sqrt (1 - x ^ 2 / r ^ 2) * r = sqrt (r ^ 2 - x ^ 2),
      { rw [← sqrt_sq hle, ← sqrt_mul, sub_mul, sqrt_sq hle, div_mul_eq_mul_div_comm,
            div_self (pow_ne_zero 2 hlt.ne'), one_mul, mul_one],
        simpa [sqrt_sq hle, div_le_one (pow_pos hlt 2)] using sq_le_sq' hx1.le hx2.le },
      field_simp,
      rw [h, mul_left_comm, ← sq, neg_mul_eq_mul_neg, mul_div_mul_left (-x^2) _ two_ne_zero,
          add_left_comm, div_add_div_same, tactic.ring.add_neg_eq_sub, div_sqrt, two_mul] },
    { suffices : -(1:ℝ) < r⁻¹ * x, by exact this.ne',
      calc -(1:ℝ) = r⁻¹ * -r : by simp [hlt.ne']
              ... < r⁻¹ * x : by nlinarith [inv_pos.mpr hlt] },
    { suffices : (r:ℝ)⁻¹ * x < 1, by exact this.ne,
      calc (r:ℝ)⁻¹ * x < r⁻¹ * r : by nlinarith [inv_pos.mpr hlt]
                   ... = 1 : inv_mul_cancel hlt.ne' },
    { nlinarith } },
  have hcont := (by continuity : continuous F).continuous_on,
  calc  ∫ x in -r..r, 2 * f x
      = F r - F (-r) : integral_eq_sub_of_has_deriv_at_of_le (neg_le_self r.2)
                         hcont hderiv (continuous_const.mul hf).continuous_on.interval_integrable
  ... = nnreal.pi * r ^ 2 : by norm_num [F, inv_mul_cancel hlt.ne', ← mul_div_assoc, mul_comm π],
end
