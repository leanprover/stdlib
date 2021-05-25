/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import measure_theory.regular
import topology.semicontinuous
import measure_theory.bochner_integration
import topology.instances.ereal

open_locale ennreal nnreal

open measure_theory
open measure_theory.measure

variables {α : Type*} [topological_space α] [measurable_space α] [borel_space α] {μ : measure α}
  [weakly_regular μ]

/-- Given an integrable function `f`, there exists a lower semicontinuous function `g ≥ f` with
integral arbitrarily close to that of `f`. -/
lemma ennreal.exists_le_lower_semicontinuous
  (f : α → ℝ≥0∞) (hf : measurable f) (ε : ℝ≥0∞) (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, f x ≤ g x) ∧ lower_semicontinuous g ∧ (∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ + ε) :=
begin
  by_cases int_f : ∫⁻ x, f x ∂μ = ∞,
  { refine ⟨λ x, ∞, λ x, le_top, lower_semicontinuous_const, by simp [int_f]⟩ },
  sorry
end

lemma ennreal.exists_lt_lower_semicontinuous [sigma_finite μ]
  (ε : ℝ≥0) (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0, (∀ x, 0 < g x) ∧ measurable g ∧ (∫⁻ x, g x ∂μ ≤ ε) :=
begin
  set δ := ε / 2 with hδ,
  have δpos : 0 < δ := nnreal.half_pos εpos,
  let a : ℝ≥0 := 2⁻¹,
  have a_pos : 0 < a, by simp [a],
  have a_lt_one : a < 1 := nnreal.two_inv_lt_one,
  let s := spanning_sets μ,
  let g := λ x, ∑' n, (set.indicator (s n) (λ x, δ * a^n / (max 1 (μ (s n)).to_nnreal)) x),
  have A : summable (λ (n : ℕ), δ * a^n) := (nnreal.summable_geometric a_lt_one).mul_left _,
  have B : summable (λ (n : ℕ), δ * a^n / (max 1 (μ (s n)).to_nnreal)),
  { apply nnreal.summable_of_le (λ n, _) A,
    rw nnreal.div_le_iff (ne_of_gt (zero_lt_one.trans_le (le_max_left _ _))),
    conv_lhs { rw ← mul_one (δ * a^n) },
    exact mul_le_mul (le_refl _) (le_max_left _ _) bot_le bot_le },
  have C : ∀ x, summable (λ n, set.indicator (s n) (λ x, δ * a^n / (max 1 (μ (s n)).to_nnreal)) x),
  { assume x,
    apply nnreal.summable_of_le (λ n, _) B,
    simp only [set.indicator],
    split_ifs,
    { exact le_refl _ },
    { exact bot_le } },
  refine ⟨g, λ x, _, _, _⟩,
  { have Z := tsum_pos,

  }

end


/-- Given an integrable function `f` in a sigma-finite space, there exists a lower semicontinuous
function `g > f` with integral arbitrarily close to that of `f`. -/
lemma ennreal.exists_lt_lower_semicontinuous [sigma_finite μ]
  (f : α → ℝ≥0) (hf : measurable f) (ε : ℝ≥0∞) (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, (f x : ℝ≥0∞) < g x) ∧ lower_semicontinuous g ∧
    (∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ + ε) :=
begin
  by_cases int_f : ∫⁻ x, f x ∂μ = ∞,
  { refine ⟨λ x, ∞, λ x, ennreal.coe_lt_top, lower_semicontinuous_const, by simp [int_f]⟩ },
  sorry
end


/-- Given an integrable function `f`, there exists an upper semicontinuous function `g ≤ f` with
integral arbitrarily close to that of `f`. -/
lemma ennreal.exists_upper_semicontinuous_le
  (f : α → ℝ≥0∞) (hf : measurable f) (int_f : ∫⁻ x, f x ∂μ < ∞) (ε : ℝ≥0∞) (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, g x ≤ f x) ∧ lower_semicontinuous g ∧ (∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ + ε) :=
begin
  sorry
end

lemma real.exists_le_lower_semicontinuous
  (f : α → ℝ) (hf : integrable f μ) (ε : ℝ) (εpos : 0 < ε) :
  ∃ g : α → ereal, (∀ x, (f x : ereal) ≤ g x) ∧ lower_semicontinuous g ∧
  (∀ᵐ x ∂ μ, g x < ⊤) ∧
  (∫ x, ereal.to_real (g x) ∂μ ≤ ∫ x, f x ∂μ + ε) :=
begin
  sorry
end



end measure_theory
