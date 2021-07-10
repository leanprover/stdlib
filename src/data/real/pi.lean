/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Benjamin Davidson
-/
import analysis.special_functions.integrals
/-!
# Pi

This file contains lemmas which establish bounds on or approximations of `real.pi`. Notably, these
include `pi_gt_sqrt_two_add_series` and `pi_lt_sqrt_two_add_series`, which bound `π` using series;
numerical bounds on `π` such as `pi_gt_314`and `pi_lt_315` (more precise versions are given, too);
and exact (infinite) formulas involving `π`, such as `tendsto_sum_pi_div_four`, Leibniz's
series for `π`, and `tendsto_prod_pi_div_two`, the Wallis product for `π`.
-/

open_locale real
namespace real

lemma pi_gt_sqrt_two_add_series (n : ℕ) : 2 ^ (n+1) * sqrt (2 - sqrt_two_add_series 0 n) < π :=
begin
  have : sqrt (2 - sqrt_two_add_series 0 n) / 2 * 2 ^ (n+2) < π,
  { rw [← lt_div_iff, ←sin_pi_over_two_pow_succ], apply sin_lt, apply div_pos pi_pos,
    all_goals { apply pow_pos, norm_num } },
  apply lt_of_le_of_lt (le_of_eq _) this,
  rw [pow_succ _ (n+1), ←mul_assoc, div_mul_cancel, mul_comm], norm_num
end

lemma pi_lt_sqrt_two_add_series (n : ℕ) :
  π < 2 ^ (n+1) * sqrt (2 - sqrt_two_add_series 0 n) + 1 / 4 ^ n :=
begin
  have : π < (sqrt (2 - sqrt_two_add_series 0 n) / 2 + 1 / (2 ^ n) ^ 3 / 4) * 2 ^ (n+2),
  { rw [← div_lt_iff, ← sin_pi_over_two_pow_succ],
    refine lt_of_lt_of_le (lt_add_of_sub_right_lt (sin_gt_sub_cube _ _)) _,
    { apply div_pos pi_pos, apply pow_pos, norm_num },
    { rw div_le_iff',
      { refine le_trans pi_le_four _,
        simp only [show ((4 : ℝ) = 2 ^ 2), by norm_num, mul_one],
        apply pow_le_pow, norm_num, apply le_add_of_nonneg_left, apply nat.zero_le },
        { apply pow_pos, norm_num }},
    apply add_le_add_left, rw div_le_div_right,
    rw [le_div_iff, ←mul_pow],
    refine le_trans _ (le_of_eq (one_pow 3)), apply pow_le_pow_of_le_left,
    { apply le_of_lt, apply mul_pos, apply div_pos pi_pos, apply pow_pos, norm_num, apply pow_pos,
      norm_num },
    rw ← le_div_iff,
    refine le_trans ((div_le_div_right _).mpr pi_le_four) _, apply pow_pos, norm_num,
    rw [pow_succ, pow_succ, ←mul_assoc, ←div_div_eq_div_mul],
    convert le_refl _,
    all_goals { repeat {apply pow_pos}, norm_num }},
  apply lt_of_lt_of_le this (le_of_eq _), rw [add_mul], congr' 1,
  { rw [pow_succ _ (n+1), ←mul_assoc, div_mul_cancel, mul_comm], norm_num },
  rw [pow_succ, ←pow_mul, mul_comm n 2, pow_mul, show (2 : ℝ) ^ 2 = 4, by norm_num, pow_succ,
      pow_succ, ←mul_assoc (2 : ℝ), show (2 : ℝ) * 2 = 4, by norm_num, ←mul_assoc, div_mul_cancel,
      mul_comm ((2 : ℝ) ^ n), ←div_div_eq_div_mul, div_mul_cancel],
  apply pow_ne_zero, norm_num, norm_num
end

/-- From an upper bound on `sqrt_two_add_series 0 n = 2 cos (π / 2 ^ (n+1))` of the form
`sqrt_two_add_series 0 n ≤ 2 - (a / 2 ^ (n + 1)) ^ 2)`, one can deduce the lower bound `a < π`
thanks to basic trigonometric inequalities as expressed in `pi_gt_sqrt_two_add_series`. -/
theorem pi_lower_bound_start (n : ℕ) {a}
  (h : sqrt_two_add_series ((0:ℕ) / (1:ℕ)) n ≤ 2 - (a / 2 ^ (n + 1)) ^ 2) : a < π :=
begin
  refine lt_of_le_of_lt _ (pi_gt_sqrt_two_add_series n), rw [mul_comm],
  refine (div_le_iff (pow_pos (by norm_num) _ : (0 : ℝ) < _)).mp (le_sqrt_of_sq_le _),
  rwa [le_sub, show (0:ℝ) = (0:ℕ)/(1:ℕ), by rw [nat.cast_zero, zero_div]],
end

lemma sqrt_two_add_series_step_up (c d : ℕ) {a b n : ℕ} {z : ℝ}
  (hz : sqrt_two_add_series (c/d) n ≤ z) (hb : 0 < b) (hd : 0 < d)
  (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) : sqrt_two_add_series (a/b) (n+1) ≤ z :=
begin
  refine le_trans _ hz, rw sqrt_two_add_series_succ, apply sqrt_two_add_series_monotone_left,
  have hb' : 0 < (b:ℝ) := nat.cast_pos.2 hb,
  have hd' : 0 < (d:ℝ) := nat.cast_pos.2 hd,
  rw [sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg), div_pow,
    add_div_eq_mul_add_div _ _ (ne_of_gt hb'), div_le_div_iff hb' (pow_pos hd' _)],
  exact_mod_cast h
end

/-- Create a proof of `a < π` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `sqrt 2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`sqrt (2 + r i) ≤ r(i+1)`, where `r 0 = 0` and `sqrt (2 - r n) ≥ a/2^(n+1)`. -/
meta def pi_lower_bound (l : list ℚ) : tactic unit :=
do let n := l.length,
  tactic.apply `(@pi_lower_bound_start %%(reflect n)),
  l.mmap' (λ r, do
    let a := r.num.to_nat, let b := r.denom,
    (() <$ tactic.apply `(@sqrt_two_add_series_step_up %%(reflect a) %%(reflect b)));
    [tactic.skip, `[norm_num1], `[norm_num1], `[norm_num1]]),
  `[simp only [sqrt_two_add_series, nat.cast_bit0, nat.cast_bit1, nat.cast_one, nat.cast_zero]],
  `[norm_num1]

/-- From a lower bound on `sqrt_two_add_series 0 n = 2 cos (π / 2 ^ (n+1))` of the form
`2 - ((a - 1 / 4 ^ n) / 2 ^ (n + 1)) ^ 2 ≤ sqrt_two_add_series 0 n`, one can deduce the upper bound
`π < a` thanks to basic trigonometric formulas as expressed in `pi_lt_sqrt_two_add_series`. -/
theorem pi_upper_bound_start (n : ℕ) {a}
  (h : 2 - ((a - 1 / 4 ^ n) / 2 ^ (n + 1)) ^ 2 ≤ sqrt_two_add_series ((0:ℕ) / (1:ℕ)) n)
  (h₂ : 1 / 4 ^ n ≤ a) : π < a :=
begin
  refine lt_of_lt_of_le (pi_lt_sqrt_two_add_series n) _,
  rw [← le_sub_iff_add_le, ← le_div_iff', sqrt_le_left, sub_le],
  { rwa [nat.cast_zero, zero_div] at h },
  { exact div_nonneg (sub_nonneg.2 h₂) (pow_nonneg (le_of_lt zero_lt_two) _) },
  { exact pow_pos zero_lt_two _ }
end

lemma sqrt_two_add_series_step_down (a b : ℕ) {c d n : ℕ} {z : ℝ}
  (hz : z ≤ sqrt_two_add_series (a/b) n) (hb : 0 < b) (hd : 0 < d)
  (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) : z ≤ sqrt_two_add_series (c/d) (n+1) :=
begin
  apply le_trans hz, rw sqrt_two_add_series_succ, apply sqrt_two_add_series_monotone_left,
  apply le_sqrt_of_sq_le,
  have hb' : 0 < (b:ℝ) := nat.cast_pos.2 hb,
  have hd' : 0 < (d:ℝ) := nat.cast_pos.2 hd,
  rw [div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hd'), div_le_div_iff (pow_pos hb' _) hd'],
  exact_mod_cast h
end

/-- Create a proof of `π < a` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `sqrt 2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`sqrt (2 + r i) ≥ r(i+1)`, where `r 0 = 0` and `sqrt (2 - r n) ≥ (a - 1/4^n) / 2^(n+1)`. -/
meta def pi_upper_bound (l : list ℚ) : tactic unit :=
do let n := l.length,
  (() <$ tactic.apply `(@pi_upper_bound_start %%(reflect n))); [pure (), `[norm_num1]],
  l.mmap' (λ r, do
    let a := r.num.to_nat, let b := r.denom,
    (() <$ tactic.apply `(@sqrt_two_add_series_step_down %%(reflect a) %%(reflect b)));
    [pure (), `[norm_num1], `[norm_num1], `[norm_num1]]),
  `[simp only [sqrt_two_add_series, nat.cast_bit0, nat.cast_bit1, nat.cast_one, nat.cast_zero]],
  `[norm_num]

lemma pi_gt_three : 3 < π := by pi_lower_bound [23/16]

lemma pi_gt_314 : 3.14 < π := by pi_lower_bound [99/70, 874/473, 1940/989, 1447/727]

lemma pi_lt_315 : π < 3.15 := by pi_upper_bound [140/99, 279/151, 51/26, 412/207]

lemma pi_gt_31415 : 3.1415 < π := by pi_lower_bound [
  11482/8119, 5401/2923, 2348/1197, 11367/5711, 25705/12868, 23235/11621]

lemma pi_lt_31416 : π < 3.1416 := by pi_upper_bound [
  4756/3363, 101211/54775, 505534/257719, 83289/41846,
  411278/205887, 438142/219137, 451504/225769, 265603/132804, 849938/424971]

lemma pi_gt_3141592 : 3.141592 < π := by pi_lower_bound [
  11482/8119, 7792/4217, 54055/27557, 949247/476920, 3310126/1657059,
  2635492/1318143, 1580265/790192, 1221775/610899, 3612247/1806132, 849943/424972]

lemma pi_lt_3141593 : π < 3.141593 := by pi_upper_bound [
  27720/19601, 56935/30813, 49359/25163, 258754/130003, 113599/56868, 1101994/551163,
  8671537/4336095, 3877807/1938940, 52483813/26242030, 56946167/28473117, 23798415/11899211]


/-! ### Leibniz's Series for Pi -/

open filter set
open_locale classical big_operators topological_space
local notation `|`x`|` := abs x

/-- This theorem establishes **Leibniz's series for `π`**: The alternating sum of the reciprocals
  of the odd numbers is `π/4`. Note that this is a conditionally rather than absolutely convergent
  series. The main tool that this proof uses is the Mean Value Theorem (specifically avoiding the
  Fundamental Theorem of Calculus).

  Intuitively, the theorem holds because Leibniz's series is the Taylor series of `arctan x`
  centered about `0` and evaluated at the value `x = 1`. Therefore, much of this proof consists of
  reasoning about a function
    `f := arctan x - ∑ i in finset.range k, (-(1:ℝ))^i * x^(2*i+1) / (2*i+1)`,
  the difference between `arctan` and the `k`-th partial sum of its Taylor series. Some ingenuity is
  required due to the fact that the Taylor series is not absolutely convergent at `x = 1`.

  This proof requires a bound on `f 1`, the key idea being that `f 1` can be split as the sum of
  `f 1 - f u` and `f u`, where `u` is a sequence of values in [0,1], carefully chosen such that
  each of these two terms can be controlled (in different ways).

  We begin the proof by (1) introducing that sequence `u` and then proving that another sequence
  constructed from `u` tends to `0` at `+∞`. After (2) converting the limit in our goal to an
  inequality, we (3) introduce the auxiliary function `f` defined above. Next, we (4) compute the
  derivative of `f`, denoted by `f'`, first generally and then on each of two subintervals of [0,1].
  We then (5) prove a bound for `f'`, again both generally as well as on each of the two
  subintervals. Finally, we (6) apply the Mean Value Theorem twice, obtaining bounds on `f 1 - f u`
  and `f u - f 0` from the bounds on `f'` (note that `f 0 = 0`). -/
theorem tendsto_sum_pi_div_four :
  tendsto (λ k, ∑ i in finset.range k, ((-(1:ℝ))^i / (2*i+1))) at_top (𝓝 (π/4)) :=
begin
  rw [tendsto_iff_norm_tendsto_zero, ← tendsto_zero_iff_norm_tendsto_zero],
  -- (1) We introduce a useful sequence `u` of values in [0,1], then prove that another sequence
  --     constructed from `u` tends to `0` at `+∞`
  let u := λ k : ℕ, (k:nnreal) ^ (-1 / (2 * (k:ℝ) + 1)),
  have H : tendsto (λ k : ℕ, (1:ℝ) - (u k) + (u k) ^ (2 * (k:ℝ) + 1)) at_top (𝓝 0),
  { convert (((tendsto_rpow_div_mul_add (-1) 2 1 two_ne_zero.symm).neg.const_add 1).add
      tendsto_inv_at_top_zero).comp tendsto_coe_nat_at_top_at_top,
    { ext k,
      simp only [nnreal.coe_nat_cast, function.comp_app, nnreal.coe_rpow],
      rw [← rpow_mul (nat.cast_nonneg k) ((-1)/(2*(k:ℝ)+1)) (2*(k:ℝ)+1),
         @div_mul_cancel _ _ _ (2*(k:ℝ)+1)
            (by { norm_cast, simp only [nat.succ_ne_zero, not_false_iff] }), rpow_neg_one k,
          sub_eq_add_neg] },
    { simp only [add_zero, add_right_neg] } },
  -- (2) We convert the limit in our goal to an inequality
  refine squeeze_zero_norm _ H,
  intro k,
  -- Since `k` is now fixed, we henceforth denote `u k` as `U`
  let U := u k,
  -- (3) We introduce an auxiliary function `f`
  let b := λ (i:ℕ) x, (-(1:ℝ))^i * x^(2*i+1) / (2*i+1),
  let f := λ x, arctan x - (∑ i in finset.range k, b i x),
  suffices f_bound : |f 1 - f 0| ≤ (1:ℝ) - U + U ^ (2 * (k:ℝ) + 1),
  { rw ← norm_neg,
    convert f_bound,
    simp only [f], simp [b] },
  -- We show that `U` is indeed in [0,1]
  have hU1 : (U:ℝ) ≤ 1,
  { by_cases hk : k = 0,
    { simpa only [U, hk] using zero_rpow_le_one _ },
    { exact rpow_le_one_of_one_le_of_nonpos (by { norm_cast, exact nat.succ_le_iff.mpr
        (nat.pos_of_ne_zero hk) }) (le_of_lt (@div_neg_of_neg_of_pos _ _ (-(1:ℝ)) (2*k+1)
          (neg_neg_iff_pos.mpr zero_lt_one) (by { norm_cast, exact nat.succ_pos' }))) } },
  have hU2 := nnreal.coe_nonneg U,
  -- (4) We compute the derivative of `f`, denoted by `f'`
  let f' := λ x : ℝ, (-x^2) ^ k / (1 + x^2),
  have has_deriv_at_f : ∀ x, has_deriv_at f (f' x) x,
  { intro x,
    have has_deriv_at_b : ∀ i ∈ finset.range k, (has_deriv_at (b i) ((-x^2)^i) x),
    { intros i hi,
      convert has_deriv_at.const_mul ((-1:ℝ)^i / (2*i+1)) (@has_deriv_at.pow _ _ _ _ _ (2*i+1)
        (has_deriv_at_id x)),
      { ext y,
        simp only [b, id.def],
        ring },
      { simp only [nat.add_succ_sub_one, add_zero, mul_one, id.def, nat.cast_bit0, nat.cast_add,
                  nat.cast_one, nat.cast_mul],
        rw [← mul_assoc, @div_mul_cancel _ _ _ (2*(i:ℝ)+1) (by { norm_cast, linarith }),
            pow_mul x 2 i, ← mul_pow (-1) (x^2) i],
        ring_nf } },
    convert (has_deriv_at_arctan x).sub (has_deriv_at.sum has_deriv_at_b),
    have g_sum :=
      @geom_sum_eq _ _ (-x^2) ((neg_nonpos.mpr (sq_nonneg x)).trans_lt zero_lt_one).ne k,
    simp only [geom_sum, f'] at g_sum ⊢,
    rw [g_sum, ← neg_add' (x^2) 1, add_comm (x^2) 1, sub_eq_add_neg, neg_div', neg_div_neg_eq],
    ring },
  have hderiv1 : ∀ x ∈ Icc (U:ℝ) 1, has_deriv_within_at f (f' x) (Icc (U:ℝ) 1) x :=
    λ x hx, (has_deriv_at_f x).has_deriv_within_at,
  have hderiv2 : ∀ x ∈ Icc 0 (U:ℝ), has_deriv_within_at f (f' x) (Icc 0 (U:ℝ)) x :=
    λ x hx, (has_deriv_at_f x).has_deriv_within_at,
  -- (5) We prove a general bound for `f'` and then more precise bounds on each of two subintervals
  have f'_bound : ∀ x ∈ Icc (-1:ℝ) 1, |f' x| ≤ |x|^(2*k),
  { intros x hx,
    rw [abs_div, is_absolute_value.abv_pow abs (-x^2) k, abs_neg, is_absolute_value.abv_pow abs x 2,
       tactic.ring_exp.pow_e_pf_exp rfl rfl],
    refine div_le_of_nonneg_of_le_mul (abs_nonneg _) (pow_nonneg (abs_nonneg _) _) _,
    refine le_mul_of_one_le_right (pow_nonneg (abs_nonneg _) _) _,
    rw abs_of_nonneg ((add_nonneg zero_le_one (sq_nonneg x)) : (0 : ℝ) ≤ _),
    exact (le_add_of_nonneg_right (sq_nonneg x) : (1 : ℝ) ≤ _) },
  have hbound1 : ∀ x ∈ Ico (U:ℝ) 1, |f' x| ≤ 1,
  { rintros x ⟨hx_left, hx_right⟩,
    have hincr := pow_le_pow_of_le_left (le_trans hU2 hx_left) (le_of_lt hx_right) (2*k),
    rw [one_pow (2*k), ← abs_of_nonneg (le_trans hU2 hx_left)] at hincr,
    rw ← abs_of_nonneg (le_trans hU2 hx_left) at hx_right,
    linarith [f'_bound x (mem_Icc.mpr (abs_le.mp (le_of_lt hx_right)))] },
  have hbound2 : ∀ x ∈ Ico 0 (U:ℝ), |f' x| ≤ U ^ (2*k),
  { rintros x ⟨hx_left, hx_right⟩,
    have hincr := pow_le_pow_of_le_left hx_left (le_of_lt hx_right) (2*k),
    rw ← abs_of_nonneg hx_left at hincr hx_right,
    rw ← abs_of_nonneg hU2 at hU1 hx_right,
    linarith [f'_bound x (mem_Icc.mpr (abs_le.mp (le_trans (le_of_lt hx_right) hU1)))] },
  -- (6) We twice apply the Mean Value Theorem to obtain bounds on `f` from the bounds on `f'`
  have mvt1 :=
    norm_image_sub_le_of_norm_deriv_le_segment' hderiv1 hbound1 _ (right_mem_Icc.mpr hU1),
  have mvt2 :=
    norm_image_sub_le_of_norm_deriv_le_segment' hderiv2 hbound2 _ (right_mem_Icc.mpr hU2),
  -- The following algebra is enough to complete the proof
  calc |f 1 - f 0| = |(f 1 - f U) + (f U - f 0)| : by ring_nf
               ... ≤ 1 * (1-U) + U^(2*k) * (U - 0) : le_trans (abs_add (f 1 - f U) (f U - f 0))
                                                      (add_le_add mvt1 mvt2)
               ... = 1 - U + U^(2*k) * U : by ring
               ... = 1 - (u k) + (u k)^(2*(k:ℝ)+1) : by { rw [← pow_succ' (U:ℝ) (2*k)], norm_cast },
end

/-! ### The Wallis Product for Pi -/

open finset interval_integral

lemma integral_sin_pow_div_tendsto_one :
  tendsto (λ k, (∫ x in 0..π, sin x ^ (2 * k + 1)) / ∫ x in 0..π, sin x ^ (2 * k)) at_top (𝓝 1) :=
begin
  have h₃ : ∀ n, (∫ x in 0..π, sin x ^ (2 * n + 1)) / ∫ x in 0..π, sin x ^ (2 * n) ≤ 1 :=
    λ n, (div_le_one (integral_sin_pow_pos _)).mpr (integral_sin_pow_antimono _),
  have h₄ :
    ∀ n, (∫ x in 0..π, sin x ^ (2 * n + 1)) / ∫ x in 0..π, sin x ^ (2 * n) ≥ 2 * n / (2 * n + 1),
  { rintro ⟨n⟩,
    { have : 0 ≤ (1 + 1) / π, exact div_nonneg (by norm_num) pi_pos.le,
      simp [this] },
    calc (∫ x in 0..π, sin x ^ (2 * n.succ + 1)) / ∫ x in 0..π, sin x ^ (2 * n.succ) ≥
      (∫ x in 0..π, sin x ^ (2 * n.succ + 1)) / ∫ x in 0..π, sin x ^ (2 * n + 1) :
      by { refine div_le_div (integral_sin_pow_pos _).le (le_refl _) (integral_sin_pow_pos _) _,
        convert integral_sin_pow_antimono (2 * n + 1) using 1 }
    ... = 2 * ↑(n.succ) / (2 * ↑(n.succ) + 1) :
      by { rw div_eq_iff (integral_sin_pow_pos (2 * n + 1)).ne',
           convert integral_sin_pow (2 * n + 1), simp with field_simps, norm_cast } },
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ (λ n, (h₄ n).le) (λ n, (h₃ n)),
  { refine metric.tendsto_at_top.mpr (λ ε hε, ⟨nat_ceil (1 / ε), λ n hn, _⟩),
    have h : (2:ℝ) * n / (2 * n + 1) - 1 = -1 / (2 * n + 1),
    { conv_lhs { congr, skip, rw ← @div_self _ _ ((2:ℝ) * n + 1) (by { norm_cast, linarith }), },
      rw [← sub_div, ← sub_sub, sub_self, zero_sub] },
    have hpos : (0:ℝ) < 2 * n + 1, { norm_cast, norm_num },
    rw [dist_eq, h, abs_div, abs_neg, abs_one, abs_of_pos hpos, one_div_lt hpos hε],
    calc 1 / ε ≤ nat_ceil (1 / ε) : le_nat_ceil _
          ... ≤ n : by exact_mod_cast hn.le
          ... < 2 * n + 1 : by { norm_cast, linarith } },
  { exact tendsto_const_nhds },
end

/-- This theorem establishes the Wallis Product for `π`. Our proof is largely about analyzing
  the behavior of the ratio of the integral of `sin x ^ n` as `n → ∞`.
  See: https://en.wikipedia.org/wiki/Wallis_product

  The proof can be broken down into two pieces.
  (Pieces involving general properties of the integral of `sin x ^n` can be found
  in `analysis.special_functions.integrals`.) First, we use integration by parts to obtain a
  recursive formula for `∫ x in 0..π, sin x ^ (n + 2)` in terms of `∫ x in 0..π, sin x ^ n`.
  From this we can obtain closed form products of `∫ x in 0..π, sin x ^ (2 * n)` and
  `∫ x in 0..π, sin x ^ (2 * n + 1)` via induction. Next, we study the behavior of the ratio
  `∫ (x : ℝ) in 0..π, sin x ^ (2 * k + 1)) / ∫ (x : ℝ) in 0..π, sin x ^ (2 * k)` and prove that
  it converges to one using the squeeze theorem. The final product for `π` is obtained after some
  algebraic manipulation. -/
theorem tendsto_prod_pi_div_two :
  tendsto (λ k, ∏ i in range k,
    (((2:ℝ) * i + 2) / (2 * i + 1)) * ((2 * i + 2) / (2 * i + 3))) at_top (𝓝 (π/2)) :=
begin
  suffices h : tendsto (λ k, 2 / π  * ∏ i in range k,
    (((2:ℝ) * i + 2) / (2 * i + 1)) * ((2 * i + 2) / (2 * i + 3))) at_top (𝓝 1),
  { have := tendsto.const_mul (π / 2) h,
    have h : π / 2 ≠ 0, norm_num [pi_ne_zero],
    simp only [← mul_assoc, ← @inv_div _ _ π 2, mul_inv_cancel h, one_mul, mul_one] at this,
    exact this },
  have h : (λ (k : ℕ), (2:ℝ) / π * ∏ (i : ℕ) in range k,
    ((2 * i + 2) / (2 * i + 1)) * ((2 * i + 2) / (2 * i + 3))) =
  λ k, (2 * ∏ i in range k,
    (2 * i + 2) / (2 * i + 3)) / (π * ∏ (i : ℕ) in range k, (2 * i + 1) / (2 * i + 2)),
  { funext,
    have h : ∏ (i : ℕ) in range k, ((2:ℝ) * ↑i + 2) / (2 * ↑i + 1) =
      1 / (∏ (i : ℕ) in range k, (2 * ↑i + 1) / (2 * ↑i + 2)),
    { rw [one_div, ← finset.prod_inv_distrib'],
      refine prod_congr rfl (λ x hx, _),
      field_simp },
    rw [prod_mul_distrib, h],
    field_simp },
  simp only [h, ← integral_sin_pow_even, ← integral_sin_pow_odd],
  exact integral_sin_pow_div_tendsto_one,
end

end real
