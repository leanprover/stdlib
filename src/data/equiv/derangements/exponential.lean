/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson, Patrick Massot
-/
import analysis.complex.basic
import data.complex.exponential
import data.equiv.derangements.finite
import topology.metric_space.cau_seq_filter

open filter
open finset

open_locale big_operators
open_locale topological_space

-- TODO move this out of "data" to somewhere else

-- TODO i suspect this already exists somewhere, or something similar
lemma complex.tendsto_iff_real (u : ℕ → ℝ) (x : ℝ) :
  tendsto (λ n, u n) at_top (𝓝 x) ↔
  tendsto (λ n, (u n : ℂ)) at_top (𝓝 (x : ℂ)) :=
begin
  split,
  { exact λ h, (complex.continuous_of_real.tendsto x).comp h },
  { exact λ h, (complex.continuous_re.tendsto x).comp h },
end

-- TODO what's the appropriate place for these lemmas?
lemma complex.tendsto_exp_series (z : ℂ) :
  tendsto (λ n, ∑ k in range n, z^k / k.factorial) at_top (𝓝 z.exp) :=
begin
  convert z.exp'.tendsto_limit,
  unfold complex.exp,
end

lemma real.tendsto_exp_series (x : ℝ) :
  tendsto (λ n, ∑ k in range n, x^k / k.factorial) at_top (𝓝 x.exp) :=
begin
  rw complex.tendsto_iff_real,
  convert complex.tendsto_exp_series x; simp,
end

theorem num_derangements_tendsto_e :
  tendsto (λ n, (num_derangements n : ℝ) / n.factorial) at_top
  (𝓝 (real.exp (-1))) :=
begin
  -- useful shorthand function
  let s : ℕ → ℝ := λ n, ∑ k in finset.range n, (-1 : ℝ)^k / k.factorial,
  -- this isn't entirely obvious, since we have to ensure that desc_fac and factorial interact in
  -- the right way, e.g. that k stays less than n
  have : ∀ n : ℕ, (num_derangements n : ℝ) / n.factorial = s(n+1),
  { intro n,
    rw num_derangements_sum,
    push_cast,
    rw finset.sum_div,
    refine finset.sum_congr (refl _) _,
    intros k hk,
    have h_le : k ≤ n := finset.mem_range_succ_iff.mp hk,
    rw [nat.desc_fac_eq_div, nat.add_sub_cancel' h_le],
    push_cast [nat.factorial_dvd_factorial h_le],
    field_simp [nat.factorial_ne_zero],
    ring,
  },
  simp_rw this,
  -- now we shift the function by 1, and use the power series lemma
  rw tendsto_add_at_top_iff_nat 1,
  exact real.tendsto_exp_series (-1),
end
