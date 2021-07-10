/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import measure_theory.regular
import topology.semicontinuous
import measure_theory.bochner_integration
import topology.instances.ereal

/-!
# Vitali-Carathéodory theorem

Vitali-Carathéodory theorem asserts the following. Consider an integrable function `f : α → ℝ` on
a space with a regular measure. Then there exists a function `g : α → ereal` such that `f x < g x`
everywhere, `g` is lower semicontinuous, and the integral of `g` is arbitrarily close to that of
`f`. This theorem is proved in this file, as `exists_lt_lower_semicontinuous_integral_lt`.

Symmetrically, there exists `g < f` which is upper semicontinuous, with integral arbitrarily close
to that of `f`. It follows from the previous statement applied to `-f`. It is formalized under
the name `exists_upper_semicontinuous_lt_integral_gt`.

The most classical version of Vitali-Carathéodory theorem only ensures a large inequality
`f x ≤ g x`. For applications to the fundamental theorem of calculus, though, the strict inequality
`f x < g x` is important. Therefore, we prove the stronger version with strict inequalities in this
file. There is a price to pay: we require that the measure is `σ`-finite, which is not necessary for
the classical Vitali-Carathéodory theorem. Since this is satisfied in all applications, this is
not a real problem.

## Sketch of proof

Decomposing `f` as the difference of its positive and negative parts, it suffices to show that a
positive function can be bounded from above by a lower semicontinuous function, and from below
by an upper semicontinuous function, with integrals close to that of `f`.

For the bound from above, write `f` as a series `∑' n, cₙ * indicator (sₙ)` of simple functions.
Then, approximate `sₙ` by a larger open set `uₙ` with measure very close to that of `sₙ` (this is
possible by regularity of the measure), and set `g = ∑' n, cₙ * indicator (uₙ)`. It is
lower semicontinuous as a series of lower semicontinuous functions, and its integral is arbitrarily
close to that of `f`.

For the bound from below, use finitely many terms in the series, and approximate `sₙ` from inside by
a closed set `Fₙ`. Then `∑ n < N, cₙ * indicator (Fₙ)` is bounded from above by `f`, it is
upper semicontinuous as a finite sum of upper semicontinuous functions, and its integral is
arbitrarily close to that of `f`.

The main pain point in the implementation is that one needs to jump between the spaces `ℝ`, `ℝ≥0`,
`ℝ≥0∞` and `ereal` (and be careful that addition is not well behaved on `ereal`), and between
`lintegral` and `integral`.

We first show the bound from above for simple functions and the nonnegative integral
(this is the main nontrivial mathematical point), then deduce it for general nonnegative functions,
first for the nonnegative integral and then for the Bochner integral.

Then we follow the same steps for the lower bound.

Finally, we glue them together to obtain the main statement
`exists_lt_lower_semicontinuous_integral_lt`.

## References

[Rudin, *Real and Complex Analysis* (Theorem 2.24)][rudin2006real]

-/

open_locale ennreal nnreal

open measure_theory measure_theory.measure

variables {α : Type*} [topological_space α] [measurable_space α] [borel_space α] (μ : measure α)
  [weakly_regular μ]

namespace measure_theory

local infixr ` →ₛ `:25 := simple_func

/-! ### Lower semicontinuous upper bound for nonnegative functions -/

/-- Given a simple function `f` with values in `ℝ≥0`, there exists a lower semicontinuous
function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma simple_func.exists_le_lower_semicontinuous_lintegral_ge :
  ∀ (f : α →ₛ ℝ≥0) {ε : ℝ≥0∞} (εpos : 0 < ε),
  ∃ g : α → ℝ≥0, (∀ x, f x ≤ g x) ∧ lower_semicontinuous g ∧
    (∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ + ε) :=
begin
  refine simple_func.induction _ _,
  { assume c s hs ε εpos,
    let f := simple_func.piecewise s hs (simple_func.const α c) (simple_func.const α 0),
    by_cases h : ∫⁻ x, f x ∂μ = ⊤,
    { refine ⟨λ x, c, λ x, _, lower_semicontinuous_const,
             by simp only [ennreal.top_add, le_top, h]⟩,
      simp only [simple_func.coe_const, simple_func.const_zero, simple_func.coe_zero,
        set.piecewise_eq_indicator, simple_func.coe_piecewise],
      exact set.indicator_le_self _ _ _ },
    by_cases hc : c = 0,
    { refine ⟨λ x, 0, _, lower_semicontinuous_const, _⟩,
      { simp only [hc, set.indicator_zero', pi.zero_apply, simple_func.const_zero, implies_true_iff,
          eq_self_iff_true, simple_func.coe_zero, set.piecewise_eq_indicator,
          simple_func.coe_piecewise, le_zero_iff] },
      { simp only [lintegral_const, zero_mul, zero_le, ennreal.coe_zero] } },
    have : μ s < μ s + ε / c,
    { have : (0 : ℝ≥0∞) < ε / c := ennreal.div_pos_iff.2 ⟨εpos.ne', ennreal.coe_ne_top⟩,
      simpa using (ennreal.add_lt_add_iff_left _).2 this,
      simpa only [hs, hc, lt_top_iff_ne_top, true_and, simple_func.coe_const, function.const_apply,
        lintegral_const, ennreal.coe_indicator, set.univ_inter, ennreal.coe_ne_top,
        measurable_set.univ, with_top.mul_eq_top_iff, simple_func.const_zero, or_false,
        lintegral_indicator, ennreal.coe_eq_zero, ne.def, not_false_iff, simple_func.coe_zero,
        set.piecewise_eq_indicator, simple_func.coe_piecewise, false_and, restrict_apply] using h },
    obtain ⟨u, u_open, su, μu⟩ : ∃ u, is_open u ∧ s ⊆ u ∧ μ u < μ s + ε / c :=
      hs.exists_is_open_lt_of_lt _ this,
    refine ⟨set.indicator u (λ x, c), λ x, _, u_open.lower_semicontinuous_indicator (zero_le _), _⟩,
    { simp only [simple_func.coe_const, simple_func.const_zero, simple_func.coe_zero,
        set.piecewise_eq_indicator, simple_func.coe_piecewise],
      exact set.indicator_le_indicator_of_subset su (λ x, zero_le _) _ },
    { suffices : (c : ℝ≥0∞) * μ u ≤ c * μ s + ε, by
        simpa only [hs, u_open.measurable_set, simple_func.coe_const, function.const_apply,
          lintegral_const, ennreal.coe_indicator, set.univ_inter, measurable_set.univ,
          simple_func.const_zero, lintegral_indicator, simple_func.coe_zero,
          set.piecewise_eq_indicator, simple_func.coe_piecewise, restrict_apply],
      calc (c : ℝ≥0∞) * μ u ≤ c * (μ s + ε / c) : ennreal.mul_le_mul (le_refl _) μu.le
      ... = c * μ s + ε :
        begin
          simp_rw [mul_add],
          rw ennreal.mul_div_cancel' _ ennreal.coe_ne_top,
          simpa using hc,
        end } },
  { assume f₁ f₂ H h₁ h₂ ε εpos,
    rcases h₁ (ennreal.half_pos εpos) with ⟨g₁, f₁_le_g₁, g₁cont, g₁int⟩,
    rcases h₂ (ennreal.half_pos εpos) with ⟨g₂, f₂_le_g₂, g₂cont, g₂int⟩,
    refine ⟨λ x, g₁ x + g₂ x, λ x, add_le_add (f₁_le_g₁ x) (f₂_le_g₂ x), g₁cont.add g₂cont, _⟩,
    simp only [simple_func.coe_add, ennreal.coe_add, pi.add_apply],
    rw [lintegral_add f₁.measurable.coe_nnreal_ennreal f₂.measurable.coe_nnreal_ennreal,
        lintegral_add g₁cont.measurable.coe_nnreal_ennreal g₂cont.measurable.coe_nnreal_ennreal],
    convert add_le_add g₁int g₂int using 1,
    conv_lhs { rw ← ennreal.add_halves ε },
    abel }
end

open simple_func (eapprox_diff tsum_eapprox_diff)

/-- Given a measurable function `f` with values in `ℝ≥0`, there exists a lower semicontinuous
function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma exists_le_lower_semicontinuous_lintegral_ge
  (f : α → ℝ≥0∞) (hf : measurable f) {ε : ℝ≥0∞} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, f x ≤ g x) ∧ lower_semicontinuous g ∧ (∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ + ε) :=
begin
  rcases ennreal.exists_pos_sum_of_encodable' εpos ℕ with ⟨δ, δpos, hδ⟩,
  have : ∀ n, ∃ g : α → ℝ≥0, (∀ x, simple_func.eapprox_diff f n x ≤ g x) ∧ lower_semicontinuous g ∧
    (∫⁻ x, g x ∂μ ≤ ∫⁻ x, simple_func.eapprox_diff f n x ∂μ + δ n) :=
  λ n, simple_func.exists_le_lower_semicontinuous_lintegral_ge μ
    (simple_func.eapprox_diff f n) (δpos n),
  choose g f_le_g gcont hg using this,
  refine ⟨λ x, (∑' n, g n x), λ x, _, _, _⟩,
  { rw ← tsum_eapprox_diff f hf,
    exact ennreal.tsum_le_tsum (λ n, ennreal.coe_le_coe.2 (f_le_g n x)) },
  { apply lower_semicontinuous_tsum (λ n, _),
    exact ennreal.continuous_coe.comp_lower_semicontinuous (gcont n)
      (λ x y hxy, ennreal.coe_le_coe.2 hxy) },
  { calc ∫⁻ x, ∑' (n : ℕ), g n x ∂μ
    = ∑' n, ∫⁻ x, g n x ∂μ :
      by rw lintegral_tsum (λ n, (gcont n).measurable.coe_nnreal_ennreal)
    ... ≤ ∑' n, (∫⁻ x, eapprox_diff f n x ∂μ + δ n) : ennreal.tsum_le_tsum hg
    ... = ∑' n, (∫⁻ x, eapprox_diff f n x ∂μ) + ∑' n, δ n : ennreal.tsum_add
    ... ≤ ∫⁻ (x : α), f x ∂μ + ε :
      begin
        refine add_le_add _ hδ.le,
        rw [← lintegral_tsum],
        { simp_rw [tsum_eapprox_diff f hf, le_refl] },
        { assume n, exact (simple_func.measurable _).coe_nnreal_ennreal }
      end }
end

/-- Given a measurable function `f` with values in `ℝ≥0` in a sigma-finite space, there exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma exists_lt_lower_semicontinuous_lintegral_ge [sigma_finite μ]
  (f : α → ℝ≥0) (fmeas : measurable f) {ε : ℝ≥0} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, (f x : ℝ≥0∞) < g x) ∧ lower_semicontinuous g ∧
    (∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ + ε) :=
begin
  rcases exists_integrable_pos_of_sigma_finite μ (nnreal.half_pos εpos) with ⟨w, wpos, wmeas, wint⟩,
  let f' := λ x, ((f x + w x : ℝ≥0) : ℝ≥0∞),
  rcases exists_le_lower_semicontinuous_lintegral_ge μ f' (fmeas.add wmeas).coe_nnreal_ennreal
    (ennreal.coe_pos.2 (nnreal.half_pos εpos)) with ⟨g, le_g, gcont, gint⟩,
  refine ⟨g, λ x, _, gcont, _⟩,
  { calc (f x : ℝ≥0∞) < f' x : by simpa [← ennreal.coe_lt_coe] using add_lt_add_left (wpos x) (f x)
    ... ≤ g x : le_g x },
  { calc ∫⁻ (x : α), g x ∂μ
        ≤ ∫⁻ (x : α), f x + w x ∂μ + (ε / 2 : ℝ≥0) : gint
    ... = ∫⁻ (x : α), f x ∂ μ + ∫⁻ (x : α), w x ∂ μ + (ε / 2 : ℝ≥0) :
      by rw lintegral_add fmeas.coe_nnreal_ennreal wmeas.coe_nnreal_ennreal
    ... ≤ ∫⁻ (x : α), f x ∂ μ + (ε / 2 : ℝ≥0) + (ε / 2 : ℝ≥0) :
      add_le_add_right (add_le_add_left wint.le _) _
    ... = ∫⁻ (x : α), f x ∂μ + ε : by rw [add_assoc, ← ennreal.coe_add, nnreal.add_halves] },
end

/-- Given an almost everywhere measurable function `f` with values in `ℝ≥0` in a sigma-finite space,
there exists a lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma exists_lt_lower_semicontinuous_lintegral_ge_of_ae_measurable [sigma_finite μ]
  (f : α → ℝ≥0) (fmeas : ae_measurable f μ) {ε : ℝ≥0} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, (f x : ℝ≥0∞) < g x) ∧ lower_semicontinuous g ∧
    (∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ + ε) :=
begin
  rcases exists_lt_lower_semicontinuous_lintegral_ge μ (fmeas.mk f) fmeas.measurable_mk
    (nnreal.half_pos εpos) with ⟨g0, f_lt_g0, g0_cont, g0_int⟩,
  rcases exists_measurable_superset_of_null fmeas.ae_eq_mk with ⟨s, hs, smeas, μs⟩,
  rcases exists_le_lower_semicontinuous_lintegral_ge μ (s.indicator (λ x, ∞))
    (measurable_const.indicator smeas) (ennreal.half_pos (ennreal.coe_pos.2 εpos)) with
    ⟨g1, le_g1, g1_cont, g1_int⟩,
  refine ⟨λ x, g0 x + g1 x, λ x, _, g0_cont.add g1_cont, _⟩,
  { by_cases h : x ∈ s,
    { have := le_g1 x,
      simp only [h, set.indicator_of_mem, top_le_iff] at this,
      simp [this] },
    { have : f x = fmeas.mk f x,
        by { rw set.compl_subset_comm at hs, exact hs h },
      rw this,
      exact (f_lt_g0 x).trans_le le_self_add } },
  { calc ∫⁻ x, g0 x + g1 x ∂μ =  ∫⁻ x, g0 x ∂μ + ∫⁻ x, g1 x ∂μ :
      lintegral_add g0_cont.measurable g1_cont.measurable
    ... ≤ (∫⁻ x, f x ∂μ + ε / 2) + (0 + ε / 2) :
      begin
        refine add_le_add _ _,
        { convert g0_int using 2,
          { exact lintegral_congr_ae (fmeas.ae_eq_mk.fun_comp _) },
          { simp only [ennreal.coe_div, ennreal.coe_one, ennreal.coe_bit0, ne.def, not_false_iff,
              bit0_eq_zero, one_ne_zero], } },
        { convert g1_int,
          simp only [smeas, μs, lintegral_const, set.univ_inter, measurable_set.univ,
            lintegral_indicator, mul_zero, restrict_apply] }
      end
    ... = ∫⁻ x, f x ∂μ + ε : by simp only [add_assoc, ennreal.add_halves, zero_add] }
end

variable {μ}

/-- Given an integrable function `f` with values in `ℝ≥0` in a sigma-finite space, there exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma exists_lt_lower_semicontinuous_integral_gt_nnreal [sigma_finite μ] (f : α → ℝ≥0)
  (fint : integrable (λ x, (f x : ℝ)) μ) {ε : ℝ} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, (f x : ℝ≥0∞) < g x) ∧ lower_semicontinuous g ∧ (∀ᵐ x ∂ μ, g x < ⊤)
  ∧ (integrable (λ x, (g x).to_real) μ) ∧ (∫ x, (g x).to_real ∂μ < ∫ x, f x ∂μ + ε) :=
begin
  have fmeas : ae_measurable f μ,
    by { convert fint.ae_measurable.real_to_nnreal, ext1 x, simp only [real.to_nnreal_coe] },
  let δ : ℝ≥0 := ⟨ε/2, (half_pos εpos).le⟩,
  have δpos : 0 < δ := half_pos εpos,
  have int_f_lt_top : ∫⁻ (a : α), (f a) ∂μ < ∞ :=
    has_finite_integral_iff_of_nnreal.1 fint.has_finite_integral,
  rcases exists_lt_lower_semicontinuous_lintegral_ge_of_ae_measurable μ f fmeas δpos
    with ⟨g, f_lt_g, gcont, gint⟩,
  have gint_lt : ∫⁻ (x : α), g x ∂μ < ∞ := gint.trans_lt (by simpa using int_f_lt_top),
  have g_lt_top : ∀ᵐ (x : α) ∂μ, g x < ∞ := ae_lt_top gcont.measurable gint_lt,
  have Ig : ∫⁻ (a : α), ennreal.of_real (g a).to_real ∂μ = ∫⁻ (a : α), g a ∂μ,
  { apply lintegral_congr_ae,
    filter_upwards [g_lt_top],
    assume x hx,
    simp only [hx.ne, ennreal.of_real_to_real, ne.def, not_false_iff] },
  refine ⟨g, f_lt_g, gcont, g_lt_top, _, _⟩,
  { refine ⟨gcont.measurable.ennreal_to_real.ae_measurable, _⟩,
    simp [has_finite_integral_iff_norm, real.norm_eq_abs, abs_of_nonneg],
    convert gint_lt using 1 },
  { rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae],
    { calc
      ennreal.to_real (∫⁻ (a : α), ennreal.of_real (g a).to_real ∂μ)
          = ennreal.to_real (∫⁻ (a : α), g a ∂μ) : by congr' 1
      ... ≤ ennreal.to_real (∫⁻ (a : α), f a ∂μ + δ) :
        begin
          apply ennreal.to_real_mono _ gint,
          simpa using int_f_lt_top.ne,
        end
      ... = ennreal.to_real (∫⁻ (a : α), f a ∂μ) + δ :
        by rw [ennreal.to_real_add int_f_lt_top.ne ennreal.coe_ne_top, ennreal.coe_to_real]
      ... < ennreal.to_real (∫⁻ (a : α), f a ∂μ) + ε :
        add_lt_add_left (by simp [δ, half_lt_self εpos]) _
      ... = (∫⁻ (a : α), ennreal.of_real ↑(f a) ∂μ).to_real + ε :
        by simp },
    { apply filter.eventually_of_forall (λ x, _), simp },
    { exact fmeas.coe_nnreal_real, },
    { apply filter.eventually_of_forall (λ x, _), simp },
    { apply gcont.measurable.ennreal_to_real.ae_measurable } }
end


/-! ### Upper semicontinuous lower bound for nonnegative functions -/

/-- Given a simple function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma simple_func.exists_upper_semicontinuous_le_lintegral_le :
  ∀ (f : α →ₛ ℝ≥0) (int_f : ∫⁻ x, f x ∂μ < ∞) {ε : ℝ≥0∞} (εpos : 0 < ε),
  ∃ g : α → ℝ≥0, (∀ x, g x ≤ f x) ∧ upper_semicontinuous g ∧ (∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ + ε) :=
begin
  refine simple_func.induction _ _,
  { assume c s hs int_f ε εpos,
    let f := simple_func.piecewise s hs (simple_func.const α c) (simple_func.const α 0),
    by_cases hc : c = 0,
    { refine ⟨λ x, 0, _, upper_semicontinuous_const, _⟩,
      { simp only [hc, set.indicator_zero', pi.zero_apply, simple_func.const_zero, implies_true_iff,
          eq_self_iff_true, simple_func.coe_zero, set.piecewise_eq_indicator,
          simple_func.coe_piecewise, le_zero_iff] },
      { simp only [hc, set.indicator_zero', lintegral_const, zero_mul, pi.zero_apply,
         simple_func.const_zero, zero_add, zero_le', simple_func.coe_zero,
         set.piecewise_eq_indicator, ennreal.coe_zero, simple_func.coe_piecewise, εpos.le] } },
    have μs_lt_top : μ s < ∞,
      by simpa only [hs, hc, lt_top_iff_ne_top, true_and, simple_func.coe_const, or_false,
        lintegral_const, ennreal.coe_indicator, set.univ_inter, ennreal.coe_ne_top, restrict_apply
        measurable_set.univ, with_top.mul_eq_top_iff, simple_func.const_zero, function.const_apply,
        lintegral_indicator, ennreal.coe_eq_zero, ne.def, not_false_iff, simple_func.coe_zero,
        set.piecewise_eq_indicator, simple_func.coe_piecewise, false_and] using int_f,
    have : (0 : ℝ≥0∞) < ε / c := ennreal.div_pos_iff.2 ⟨εpos.ne', ennreal.coe_ne_top⟩,
    obtain ⟨F, F_closed, Fs, μF⟩ : ∃ F, is_closed F ∧ F ⊆ s ∧ μ s < μ F + ε / c :=
      hs.exists_lt_is_closed_of_lt_top_of_pos μs_lt_top this,
    refine ⟨set.indicator F (λ x, c), λ x, _,
      F_closed.upper_semicontinuous_indicator (zero_le _), _⟩,
    { simp only [simple_func.coe_const, simple_func.const_zero, simple_func.coe_zero,
        set.piecewise_eq_indicator, simple_func.coe_piecewise],
      exact set.indicator_le_indicator_of_subset Fs (λ x, zero_le _) _ },
    { suffices : (c : ℝ≥0∞) * μ s ≤ c * μ F + ε,
        by simpa only [hs, F_closed.measurable_set, simple_func.coe_const, function.const_apply,
          lintegral_const, ennreal.coe_indicator, set.univ_inter, measurable_set.univ,
          simple_func.const_zero, lintegral_indicator, simple_func.coe_zero,
          set.piecewise_eq_indicator, simple_func.coe_piecewise, restrict_apply],
      calc (c : ℝ≥0∞) * μ s ≤ c * (μ F + ε / c) : ennreal.mul_le_mul (le_refl _) μF.le
      ... = c * μ F + ε :
        begin
          simp_rw [mul_add],
          rw ennreal.mul_div_cancel' _ ennreal.coe_ne_top,
          simpa using hc,
        end } },
  { assume f₁ f₂ H h₁ h₂ f_int ε εpos,
    have A : ∫⁻ (x : α), f₁ x ∂μ + ∫⁻ (x : α), f₂ x ∂μ < ⊤,
    { rw ← lintegral_add f₁.measurable.coe_nnreal_ennreal f₂.measurable.coe_nnreal_ennreal,
      simpa only [simple_func.coe_add, ennreal.coe_add, pi.add_apply] using f_int },
    rcases h₁ (ennreal.add_lt_top.1 A).1 (ennreal.half_pos εpos) with ⟨g₁, f₁_le_g₁, g₁cont, g₁int⟩,
    rcases h₂ (ennreal.add_lt_top.1 A).2 (ennreal.half_pos εpos) with ⟨g₂, f₂_le_g₂, g₂cont, g₂int⟩,
    refine ⟨λ x, g₁ x + g₂ x, λ x, add_le_add (f₁_le_g₁ x) (f₂_le_g₂ x), g₁cont.add g₂cont, _⟩,
    simp only [simple_func.coe_add, ennreal.coe_add, pi.add_apply],
    rw [lintegral_add f₁.measurable.coe_nnreal_ennreal f₂.measurable.coe_nnreal_ennreal,
        lintegral_add g₁cont.measurable.coe_nnreal_ennreal g₂cont.measurable.coe_nnreal_ennreal],
    convert add_le_add g₁int g₂int using 1,
    conv_lhs { rw ← ennreal.add_halves ε },
    abel }
end

/-- Given an integrable function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma exists_upper_semicontinuous_le_lintegral_le
  (f : α → ℝ≥0) (int_f : ∫⁻ x, f x ∂μ < ∞) {ε : ℝ≥0∞} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0, (∀ x, g x ≤ f x) ∧ upper_semicontinuous g ∧ (∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ + ε) :=
begin
  obtain ⟨fs, fs_le_f, int_fs⟩ : ∃ (fs : α →ₛ ℝ≥0), (∀ x, fs x ≤ f x) ∧
    (∫⁻ x, f x ∂μ ≤ ∫⁻ x, fs x ∂μ + ε/2) :=
  begin
    have := ennreal.lt_add_right int_f (ennreal.half_pos εpos),
    conv_rhs at this { rw lintegral_eq_nnreal (λ x, (f x : ℝ≥0∞)) μ },
    erw ennreal.bsupr_add at this; [skip, exact ⟨0, λ x, by simp⟩],
    simp only [lt_supr_iff] at this,
    rcases this with ⟨fs, fs_le_f, int_fs⟩,
    refine ⟨fs, λ x, by simpa only [ennreal.coe_le_coe] using fs_le_f x, _⟩,
    convert int_fs.le,
    rw ← simple_func.lintegral_eq_lintegral,
    refl
  end,
  have int_fs_lt_top : ∫⁻ x, fs x ∂μ < ∞,
  { apply lt_of_le_of_lt (lintegral_mono (λ x, _)) int_f,
    simpa only [ennreal.coe_le_coe] using fs_le_f x },
  obtain ⟨g, g_le_fs, gcont, gint⟩ : ∃ g : α → ℝ≥0,
    (∀ x, g x ≤ fs x) ∧ upper_semicontinuous g ∧ (∫⁻ x, fs x ∂μ ≤ ∫⁻ x, g x ∂μ + ε/2) :=
  fs.exists_upper_semicontinuous_le_lintegral_le int_fs_lt_top (ennreal.half_pos εpos),
  refine ⟨g, λ x, (g_le_fs x).trans (fs_le_f x), gcont, _⟩,
  calc ∫⁻ x, f x ∂μ ≤ ∫⁻ x, fs x ∂μ + ε / 2 : int_fs
  ... ≤ (∫⁻ x, g x ∂μ + ε / 2) + ε / 2 : add_le_add gint (le_refl _)
  ... = ∫⁻ x, g x ∂μ + ε : by rw [add_assoc, ennreal.add_halves]
end

/-- Given an integrable function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma exists_upper_semicontinuous_le_integral_le (f : α → ℝ≥0)
  (fint : integrable (λ x, (f x : ℝ)) μ) {ε : ℝ} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0, (∀ x, g x ≤ f x) ∧ upper_semicontinuous g ∧ (integrable (λ x, (g x : ℝ)) μ)
  ∧ (∫ x, (f x : ℝ) ∂μ - ε ≤ ∫ x, g x ∂μ) :=
begin
  let δ : ℝ≥0 := ⟨ε, εpos.le⟩,
  have δpos : (0 : ℝ≥0∞) < δ := ennreal.coe_lt_coe.2 εpos,
  have If : ∫⁻ x, f x ∂ μ < ∞ := has_finite_integral_iff_of_nnreal.1 fint.has_finite_integral,
  rcases exists_upper_semicontinuous_le_lintegral_le f If δpos with ⟨g, gf, gcont, gint⟩,
  have Ig : ∫⁻ x, g x ∂ μ < ∞,
  { apply lt_of_le_of_lt (lintegral_mono (λ x, _)) If,
    simpa using gf x },
  refine ⟨g, gf, gcont, _, _⟩,
  { refine integrable.mono fint gcont.measurable.coe_nnreal_real.ae_measurable _,
    exact filter.eventually_of_forall (λ x, by simp [gf x]) },
  { rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae],
    { rw sub_le_iff_le_add,
      convert ennreal.to_real_mono _ gint,
      { simp, },
      { rw ennreal.to_real_add Ig.ne ennreal.coe_ne_top, simp },
      { simpa using Ig.ne } },
    { apply filter.eventually_of_forall, simp },
    { exact gcont.measurable.coe_nnreal_real.ae_measurable },
    { apply filter.eventually_of_forall, simp },
    { exact fint.ae_measurable } }
end

/-! ### Vitali-Carathéodory theorem -/

/-- Vitali-Carathéodory theorem: given an integrable real function `f`, there exists an integrable
function `g > f` which is lower semicontinuous, with integral arbitrarily close to that of `f`.
This function has to be `ereal`-valued in general. -/
lemma exists_lt_lower_semicontinuous_integral_lt [sigma_finite μ]
  (f : α → ℝ) (hf : integrable f μ) {ε : ℝ} (εpos : 0 < ε) :
  ∃ g : α → ereal, (∀ x, (f x : ereal) < g x) ∧ lower_semicontinuous g ∧
  (integrable (λ x, ereal.to_real (g x)) μ) ∧ (∀ᵐ x ∂ μ, g x < ⊤) ∧
  (∫ x, ereal.to_real (g x) ∂μ < ∫ x, f x ∂μ + ε) :=
begin
  let δ : ℝ≥0 := ⟨ε/2, (half_pos εpos).le⟩,
  have δpos : 0 < δ := half_pos εpos,
  let fp : α → ℝ≥0 := λ x, real.to_nnreal (f x),
  have int_fp : integrable (λ x, (fp x : ℝ)) μ := hf.real_to_nnreal,
  rcases exists_lt_lower_semicontinuous_integral_gt_nnreal fp int_fp δpos
    with ⟨gp, fp_lt_gp, gpcont, gp_lt_top, gp_integrable, gpint⟩,
  let fm : α → ℝ≥0 := λ x, real.to_nnreal (-f x),
  have int_fm : integrable (λ x, (fm x : ℝ)) μ := hf.neg.real_to_nnreal,
  rcases exists_upper_semicontinuous_le_integral_le fm int_fm δpos
    with ⟨gm, gm_le_fm, gmcont, gm_integrable, gmint⟩,
  let g : α → ereal := λ x, (gp x : ereal) - (gm x),
  have ae_g : ∀ᵐ x ∂ μ, (g x).to_real = (gp x : ereal).to_real - (gm x : ereal).to_real,
  { filter_upwards [gp_lt_top],
    assume x hx,
    rw ereal.to_real_sub;
    simp [hx.ne] },
  refine ⟨g, _, _, _, _, _⟩,
  show integrable (λ x, ereal.to_real (g x)) μ,
  { rw integrable_congr ae_g,
    convert gp_integrable.sub gm_integrable,
    ext x,
    simp },
  show ∫ (x : α), (g x).to_real ∂μ < ∫ (x : α), f x ∂μ + ε, from calc
    ∫ (x : α), (g x).to_real ∂μ = ∫ (x : α), ereal.to_real (gp x) - ereal.to_real (gm x) ∂μ :
      integral_congr_ae ae_g
    ... = ∫ (x : α), ereal.to_real (gp x) ∂ μ - ∫ (x : α), gm x ∂μ :
      begin
        simp only [ereal.to_real_coe_ennreal, ennreal.coe_to_real, coe_coe],
        exact integral_sub gp_integrable gm_integrable,
      end
    ... < ∫ (x : α), ↑(fp x) ∂μ + ↑δ - ∫ (x : α), gm x ∂μ :
      begin
        apply sub_lt_sub_right,
        convert gpint,
        simp only [ereal.to_real_coe_ennreal],
      end
    ... ≤ ∫ (x : α), ↑(fp x) ∂μ + ↑δ - (∫ (x : α), fm x ∂μ - δ) :
      sub_le_sub_left gmint _
    ... = ∫ (x : α), f x ∂μ + 2 * δ :
      by { simp_rw [integral_eq_integral_pos_part_sub_integral_neg_part hf, fp, fm], ring }
    ... = ∫ (x : α), f x ∂μ + ε :
      by { congr' 1, field_simp [δ, mul_comm] },
  show ∀ᵐ (x : α) ∂μ, g x < ⊤,
  { filter_upwards [gp_lt_top],
    assume x hx,
    simp [g, ereal.sub_eq_add_neg, lt_top_iff_ne_top, lt_top_iff_ne_top.1 hx] },
  show ∀ x, (f x : ereal) < g x,
  { assume x,
    rw ereal.coe_real_ereal_eq_coe_to_nnreal_sub_coe_to_nnreal (f x),
    refine ereal.sub_lt_sub_of_lt_of_le _ _ _ _,
    { simp only [ereal.coe_ennreal_lt_coe_ennreal_iff, coe_coe], exact (fp_lt_gp x) },
    { simp only [ennreal.coe_le_coe, ereal.coe_ennreal_le_coe_ennreal_iff, coe_coe],
      exact (gm_le_fm x) },
    { simp only [ereal.coe_ennreal_ne_bot, ne.def, not_false_iff, coe_coe] },
    { simp only [ereal.coe_nnreal_ne_top, ne.def, not_false_iff, coe_coe] } },
  show lower_semicontinuous g,
  { apply lower_semicontinuous.add',
    { exact continuous_coe_ennreal_ereal.comp_lower_semicontinuous gpcont
        (λ x y hxy, ereal.coe_ennreal_le_coe_ennreal_iff.2 hxy) },
    { apply ereal.continuous_neg.comp_upper_semicontinuous_antimono _
        (λ x y hxy, ereal.neg_le_neg_iff.2 hxy),
      dsimp,
      apply continuous_coe_ennreal_ereal.comp_upper_semicontinuous _
        (λ x y hxy, ereal.coe_ennreal_le_coe_ennreal_iff.2 hxy),
      exact ennreal.continuous_coe.comp_upper_semicontinuous gmcont
        (λ x y hxy, ennreal.coe_le_coe.2 hxy) },
    { assume x,
      exact ereal.continuous_at_add (by simp) (by simp) } }
end

/-- Vitali-Carathéodory theorem: given an integrable real function `f`, there exists an integrable
function `g < f` which is upper semicontinuous, with integral arbitrarily close to that of `f`.
This function has to be `ereal`-valued in general. -/
lemma exists_upper_semicontinuous_lt_integral_gt [sigma_finite μ]
  (f : α → ℝ) (hf : integrable f μ) {ε : ℝ} (εpos : 0 < ε) :
  ∃ g : α → ereal, (∀ x, (g x : ereal) < f x) ∧ upper_semicontinuous g ∧
  (integrable (λ x, ereal.to_real (g x)) μ) ∧ (∀ᵐ x ∂μ, ⊥ < g x) ∧
  (∫ x, f x ∂μ < ∫ x, ereal.to_real (g x) ∂μ + ε) :=
begin
  rcases exists_lt_lower_semicontinuous_integral_lt (λ x, - f x) hf.neg εpos
    with ⟨g, g_lt_f, gcont, g_integrable, g_lt_top, gint⟩,
  refine ⟨λ x, - g x, _, _, _, _, _⟩,
  { exact  λ x, ereal.neg_lt_iff_neg_lt.1 (by simpa only [ereal.coe_neg] using g_lt_f x) },
  { exact ereal.continuous_neg.comp_lower_semicontinuous_antimono gcont
      (λ x y hxy, ereal.neg_le_neg_iff.2 hxy) },
  { convert g_integrable.neg,
    ext x,
    simp },
  { simpa [bot_lt_iff_ne_bot, lt_top_iff_ne_top] using g_lt_top },
  { simp_rw [integral_neg, lt_neg_add_iff_add_lt] at gint,
    rw add_comm at gint,
    simpa [integral_neg] using gint }
end

end measure_theory
