/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.extend_deriv
import analysis.calculus.iterated_deriv
import analysis.special_functions.exp_log
import analysis.normed_space.inner_product
import topology.algebra.polynomial

/-!
# Infinitely smooth bump function

In this file we construct several infinitely smooth functions with properties that an analytic
function cannot have:

* `exp_neg_inv_glue` is equal to zero for `x ≤ 0` and is strictly positive otherwise; it is given by
  `x ↦ exp (-1/x)` for `x > 0`;
* `smooth_transition` is equal to zero for `x ≤ 0` and is equal to one for `x ≥ 1`; it is given by
  `exp_neg_inv_glue x / (exp_neg_inv_glue x + exp_neg_inv_glue (1 - x))`;
* `smooth_bump_function` is equal to one on the closed ball of radius `1` and is equal to `0`
  outside of the open ball of radius `2`.
-/

noncomputable theory
open_locale classical topological_space

open polynomial real filter set

/-- `exp_neg_inv_glue` is the real function given by `x ↦ exp (-1/x)` for `x > 0` and `0`
for `x ≤ 0`. It is a basic building block to construct smooth partitions of unity. Its main property
is that it vanishes for `x ≤ 0`, it is positive for `x > 0`, and the junction between the two
behaviors is flat enough to retain smoothness. The fact that this function is `C^∞` is proved in
`exp_neg_inv_glue.smooth`. -/
def exp_neg_inv_glue (x : ℝ) : ℝ := if x ≤ 0 then 0 else exp (-x⁻¹)

namespace exp_neg_inv_glue

/-- Our goal is to prove that `exp_neg_inv_glue` is `C^∞`. For this, we compute its successive
derivatives for `x > 0`. The `n`-th derivative is of the form `P_aux n (x) exp(-1/x) / x^(2 n)`,
where `P_aux n` is computed inductively. -/
noncomputable def P_aux : ℕ → polynomial ℝ
| 0 := 1
| (n+1) := X^2 * (P_aux n).derivative  + (1 - C ↑(2 * n) * X) * (P_aux n)

/-- Formula for the `n`-th derivative of `exp_neg_inv_glue`, as an auxiliary function `f_aux`. -/
def f_aux (n : ℕ) (x : ℝ) : ℝ :=
if x ≤ 0 then 0 else (P_aux n).eval x * exp (-x⁻¹) / x^(2 * n)

/-- The `0`-th auxiliary function `f_aux 0` coincides with `exp_neg_inv_glue`, by definition. -/
lemma f_aux_zero_eq : f_aux 0 = exp_neg_inv_glue :=
begin
   ext x,
   by_cases h : x ≤ 0,
   { simp [exp_neg_inv_glue, f_aux, h] },
   { simp [h, exp_neg_inv_glue, f_aux, ne_of_gt (not_le.1 h), P_aux] }
end

/-- For positive values, the derivative of the `n`-th auxiliary function `f_aux n`
(given in this statement in unfolded form) is the `n+1`-th auxiliary function, since
the polynomial `P_aux (n+1)` was chosen precisely to ensure this. -/
lemma f_aux_deriv (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
  has_deriv_at (λx, (P_aux n).eval x * exp (-x⁻¹) / x^(2 * n))
    ((P_aux (n+1)).eval x * exp (-x⁻¹) / x^(2 * (n + 1))) x :=
begin
  have A : ∀k:ℕ, 2 * (k + 1) - 1 = 2 * k + 1,
  { assume k,
    rw nat.sub_eq_iff_eq_add,
    { ring },
    { simpa [mul_add] using add_le_add (zero_le (2 * k)) one_le_two } },
  convert (((P_aux n).has_deriv_at x).mul
               (((has_deriv_at_exp _).comp x (has_deriv_at_inv hx).neg))).div
            (has_deriv_at_pow (2 * n) x) (pow_ne_zero _ hx) using 1,
  field_simp [hx, P_aux],
  -- `ring_exp` can't solve `p ∨ q` goal generated by `mul_eq_mul_right_iff`
  cases n; simp [nat.succ_eq_add_one, A, -mul_eq_mul_right_iff]; ring_exp
end

/-- For positive values, the derivative of the `n`-th auxiliary function `f_aux n`
is the `n+1`-th auxiliary function. -/
lemma f_aux_deriv_pos (n : ℕ) (x : ℝ) (hx : 0 < x) :
  has_deriv_at (f_aux n) ((P_aux (n+1)).eval x * exp (-x⁻¹) / x^(2 * (n + 1))) x :=
begin
  apply (f_aux_deriv n x (ne_of_gt hx)).congr_of_eventually_eq,
  filter_upwards [lt_mem_nhds hx],
  assume y hy,
  simp [f_aux, hy.not_le]
end

/-- To get differentiability at `0` of the auxiliary functions, we need to know that their limit
is `0`, to be able to apply general differentiability extension theorems. This limit is checked in
this lemma. -/
lemma f_aux_limit (n : ℕ) :
  tendsto (λx, (P_aux n).eval x * exp (-x⁻¹) / x^(2 * n)) (𝓝[Ioi 0] 0) (𝓝 0) :=
begin
  have A : tendsto (λx, (P_aux n).eval x) (𝓝[Ioi 0] 0) (𝓝 ((P_aux n).eval 0)) :=
  (P_aux n).continuous_within_at,
  have B : tendsto (λx, exp (-x⁻¹) / x^(2 * n)) (𝓝[Ioi 0] 0) (𝓝 0),
  { convert (tendsto_pow_mul_exp_neg_at_top_nhds_0 (2 * n)).comp tendsto_inv_zero_at_top,
    ext x,
    field_simp },
  convert A.mul B;
  simp [mul_div_assoc]
end

/-- Deduce from the limiting behavior at `0` of its derivative and general differentiability
extension theorems that the auxiliary function `f_aux n` is differentiable at `0`,
with derivative `0`. -/
lemma f_aux_deriv_zero (n : ℕ) : has_deriv_at (f_aux n) 0 0 :=
begin
  -- we check separately differentiability on the left and on the right
  have A : has_deriv_within_at (f_aux n) (0 : ℝ) (Iic 0) 0,
  { apply (has_deriv_at_const (0 : ℝ) (0 : ℝ)).has_deriv_within_at.congr,
    { assume y hy,
      simp at hy,
      simp [f_aux, hy] },
    { simp [f_aux, le_refl] } },
  have B : has_deriv_within_at (f_aux n) (0 : ℝ) (Ici 0) 0,
  { have diff : differentiable_on ℝ (f_aux n) (Ioi 0) :=
      λx hx, (f_aux_deriv_pos n x hx).differentiable_at.differentiable_within_at,
    -- next line is the nontrivial bit of this proof, appealing to differentiability
    -- extension results.
    apply has_deriv_at_interval_left_endpoint_of_tendsto_deriv diff _ self_mem_nhds_within,
    { refine (f_aux_limit (n+1)).congr' _,
      apply mem_sets_of_superset self_mem_nhds_within (λx hx, _),
      simp [(f_aux_deriv_pos n x hx).deriv] },
    { have : f_aux n 0 = 0, by simp [f_aux, le_refl],
      simp only [continuous_within_at, this],
      refine (f_aux_limit n).congr' _,
      apply mem_sets_of_superset self_mem_nhds_within (λx hx, _),
      have : ¬(x ≤ 0), by simpa using hx,
      simp [f_aux, this] } },
  simpa using A.union B,
end

/-- At every point, the auxiliary function `f_aux n` has a derivative which is
equal to `f_aux (n+1)`. -/
lemma f_aux_has_deriv_at (n : ℕ) (x : ℝ) : has_deriv_at (f_aux n) (f_aux (n+1) x) x :=
begin
  -- check separately the result for `x < 0`, where it is trivial, for `x > 0`, where it is done
  -- in `f_aux_deriv_pos`, and for `x = 0`, done in
  -- `f_aux_deriv_zero`.
  rcases lt_trichotomy x 0 with hx|hx|hx,
  { have : f_aux (n+1) x = 0, by simp [f_aux, le_of_lt hx],
    rw this,
    apply (has_deriv_at_const x (0 : ℝ)).congr_of_eventually_eq,
    filter_upwards [gt_mem_nhds hx],
    assume y hy,
    simp [f_aux, hy.le] },
  { have : f_aux (n + 1) 0 = 0, by simp [f_aux, le_refl],
    rw [hx, this],
    exact f_aux_deriv_zero n },
  { have : f_aux (n+1) x = (P_aux (n+1)).eval x * exp (-x⁻¹) / x^(2 * (n+1)),
      by simp [f_aux, not_le_of_gt hx],
    rw this,
    exact f_aux_deriv_pos n x hx },
end

/-- The successive derivatives of the auxiliary function `f_aux 0` are the
functions `f_aux n`, by induction. -/
lemma f_aux_iterated_deriv (n : ℕ) : iterated_deriv n (f_aux 0) = f_aux n :=
begin
  induction n with n IH,
  { simp },
  { simp [iterated_deriv_succ, IH],
    ext x,
    exact (f_aux_has_deriv_at n x).deriv }
end

/-- The function `exp_neg_inv_glue` is smooth. -/
protected theorem times_cont_diff {n} : times_cont_diff ℝ n exp_neg_inv_glue :=
begin
  rw ← f_aux_zero_eq,
  apply times_cont_diff_of_differentiable_iterated_deriv (λ m hm, _),
  rw f_aux_iterated_deriv m,
  exact λ x, (f_aux_has_deriv_at m x).differentiable_at
end

/-- The function `exp_neg_inv_glue` vanishes on `(-∞, 0]`. -/
lemma zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : exp_neg_inv_glue x = 0 :=
by simp [exp_neg_inv_glue, hx]

/-- The function `exp_neg_inv_glue` is positive on `(0, +∞)`. -/
lemma pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < exp_neg_inv_glue x :=
by simp [exp_neg_inv_glue, not_le.2 hx, exp_pos]

/-- The function exp_neg_inv_glue` is nonnegative. -/
lemma nonneg (x : ℝ) : 0 ≤ exp_neg_inv_glue x :=
begin
  cases le_or_gt x 0,
  { exact ge_of_eq (zero_of_nonpos h) },
  { exact le_of_lt (pos_of_pos h) }
end

end exp_neg_inv_glue

/-- An infinitely smooth function `f : ℝ → ℝ` such that `f x = 0` for `x ≤ 0`,
`f x = 1` for `1 ≤ x`, and `0 < f x < 1` for `0 < x < 1`. -/
def smooth_transition (x : ℝ) : ℝ :=
exp_neg_inv_glue x / (exp_neg_inv_glue x + exp_neg_inv_glue (1 - x))

namespace smooth_transition

variables {x : ℝ}

open exp_neg_inv_glue

lemma pos_denom (x) : 0 < exp_neg_inv_glue x + exp_neg_inv_glue (1 - x) :=
((@zero_lt_one ℝ _ _).lt_or_lt x).elim
  (λ hx, add_pos_of_pos_of_nonneg (pos_of_pos hx) (nonneg _))
  (λ hx, add_pos_of_nonneg_of_pos (nonneg _) (pos_of_pos $ sub_pos.2 hx))

lemma one_of_one_le (h : 1 ≤ x) : smooth_transition x = 1 :=
(div_eq_one_iff_eq $ (pos_denom x).ne').2 $ by rw [zero_of_nonpos (sub_nonpos.2 h), add_zero]

lemma zero_of_nonpos (h : x ≤ 0) : smooth_transition x = 0 :=
by rw [smooth_transition, zero_of_nonpos h, zero_div]

lemma le_one (x : ℝ) : smooth_transition x ≤ 1 :=
(div_le_one (pos_denom x)).2 $ le_add_of_nonneg_right (nonneg _)

lemma nonneg (x : ℝ) : 0 ≤ smooth_transition x :=
div_nonneg (exp_neg_inv_glue.nonneg _) (pos_denom x).le

lemma lt_one_of_lt_one (h : x < 1) : smooth_transition x < 1 :=
(div_lt_one $ pos_denom x).2 $ lt_add_of_pos_right _ $ pos_of_pos $ sub_pos.2 h

lemma pos_of_pos (h : 0 < x) : 0 < smooth_transition x :=
div_pos (exp_neg_inv_glue.pos_of_pos h) (pos_denom x)

protected lemma times_cont_diff {n} : times_cont_diff ℝ n smooth_transition :=
exp_neg_inv_glue.times_cont_diff.div
  (exp_neg_inv_glue.times_cont_diff.add $ exp_neg_inv_glue.times_cont_diff.comp $
    times_cont_diff_const.sub times_cont_diff_id) $
  λ x, (pos_denom x).ne'

protected lemma times_cont_diff_at {x n} : times_cont_diff_at ℝ n smooth_transition x :=
smooth_transition.times_cont_diff.times_cont_diff_at

end smooth_transition

variables {E : Type*}

/-- Let `x` be a point of a real inner product space; let `0 < r < R` be real numbers.
Then `smooth_bump_function x r R` is a function `E → ℝ` with the following properties:

- `smooth_bump_function x r R` is infinitely smooth on `E`;
- `smooth_bump_function x r R` is equal to `1` on `closed_ball x r`;
- `0 < smooth_bump_function x r R y < 1` if `r < dist y x < R`;
- `smooth_bump_function x r R y = 0` if `R ≤ dist y x.

We define this function for any `x`, `r`, and `R`  -/
def smooth_bump_function [inner_product_space ℝ E] (x : E) (r R : ℝ) (y : E) : ℝ :=
smooth_transition ((R - dist y x) / (R - r))

namespace smooth_bump_function

variables [inner_product_space ℝ E] {r R : ℝ} {x y : E}

open smooth_transition metric

lemma one_of_mem_closed_ball (hy : y ∈ closed_ball x r) (hrR : r < R) :
  smooth_bump_function x r R y = 1 :=
one_of_one_le $ (one_le_div (sub_pos.2 hrR)).2 $ sub_le_sub_left hy _

lemma nonneg : 0 ≤ smooth_bump_function x r R y :=
nonneg _

lemma le_one : smooth_bump_function x r R y ≤ 1 :=
le_one _

lemma pos_of_mem_ball (hx : y ∈ ball x R) (hrR : r < R) :
  0 < smooth_bump_function x r R y :=
pos_of_pos $ div_pos (sub_pos.2 hx) (sub_pos.2 hrR)

lemma lt_one_of_lt_dist (h : r < dist y x) (hrR : r < R) : smooth_bump_function x r R y < 1 :=
lt_one_of_lt_one $ (div_lt_one (sub_pos.2 hrR)).2 $ sub_lt_sub_left h _

lemma zero_of_le_dist (hx : R ≤ dist y x) (hrR : r ≤ R) : smooth_bump_function x r R y = 0 :=
zero_of_nonpos $ div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hx) (sub_nonneg.2 hrR)

lemma support_eq (hrR : r < R) :
  function.support (smooth_bump_function x r R : E → ℝ) = metric.ball x R :=
begin
  ext y,
  suffices : smooth_bump_function x r R y ≠ 0 ↔ dist y x < R, by simpa [function.mem_support],
  cases lt_or_le (dist y x) R with hx hx,
  { simp [hx, (pos_of_mem_ball hx hrR).ne'] },
  { simp [hx.not_lt, zero_of_le_dist hx hrR.le] }
end

lemma eventually_eq_one_of_mem_ball (h : y ∈ ball x r) (hrR : r < R) :
  smooth_bump_function x r R =ᶠ[𝓝 y] (λ _, 1) :=
((is_open_lt (continuous_id.dist continuous_const) continuous_const).eventually_mem h).mono $
  λ z hz, one_of_mem_closed_ball (le_of_lt hz) hrR

lemma eventually_eq_one (h0 : 0 < r) (hrR : r < R) :
  smooth_bump_function x r R =ᶠ[𝓝 (x : E)] (λ _, 1) :=
eventually_eq_one_of_mem_ball (mem_ball_self h0) hrR

protected lemma times_cont_diff_at (h0 : 0 < r) (hrR : r < R) {n} :
  times_cont_diff_at ℝ n (smooth_bump_function x r R) y :=
begin
  rcases em (y = x) with rfl|hx,
  { exact times_cont_diff_at_const.congr_of_eventually_eq (eventually_eq_one h0 hrR) },
  { exact smooth_transition.times_cont_diff_at.comp y
      (times_cont_diff_at.div_const $ times_cont_diff_at_const.sub $
        times_cont_diff_at_id.dist times_cont_diff_at_const hx) }
end

protected lemma times_cont_diff (h0 : 0 < r) (hrR : r < R) {n} :
  times_cont_diff ℝ n (smooth_bump_function x r R) :=
times_cont_diff_iff_times_cont_diff_at.2 $ λ y, smooth_bump_function.times_cont_diff_at h0 hrR

protected lemma times_cont_diff_within_at (h0 : 0 < r) (hrR : r < R) {s n} :
  times_cont_diff_within_at ℝ n (smooth_bump_function x r R) s y :=
(smooth_bump_function.times_cont_diff_at h0 hrR).times_cont_diff_within_at

end smooth_bump_function

open function finite_dimensional metric

/-- If `E` is a finite dimensional normed space over `ℝ`, then for any point `x : E` and its
neighborhood `s` there exists an infinitely smooth function with the following properties:

* `f y = 1` in a neighborhood of `x`;
* `f y = 0` outside of `s`;
*  moreover, `closure (support f) ⊆ s` and `closure (support f)` is a compact set;
* `f y ∈ [0, 1]` for all `y`.
-/
lemma exists_times_cont_diff_bump_function_of_mem_nhds [normed_group E] [normed_space ℝ E]
  [finite_dimensional ℝ E] {x : E} {s : set E} (hs : s ∈ 𝓝 x) :
  ∃ f : E → ℝ, f =ᶠ[𝓝 x] 1 ∧ (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧ times_cont_diff ℝ ⊤ f ∧
    is_compact (closure $ support f) ∧ closure (support f) ⊆ s :=
begin
  have e : E ≃L[ℝ] euclidean_space ℝ (fin $ findim ℝ E) :=
    continuous_linear_equiv.of_findim_eq findim_euclidean_space_fin.symm,
  rcases locally_compact_space.local_compact_nhds _ _ hs with ⟨K, hxK, hKs, hKc⟩,
  rw [← e.symm_map_nhds_eq, mem_map] at hxK,
  obtain ⟨R, hR₀, hR⟩ : ∃ R > 0, ∀ y ∈ ball (e x) R, e.symm y ∈ K, from mem_nhds_iff.1 hxK,
  have Hpos : 0 < R / 2 := half_pos hR₀,
  have Hlt : R / 2 < R := half_lt_self hR₀,
  have : support (smooth_bump_function (e x) (R / 2) R ∘ e) ⊆ K,
  { intros y hy,
    rw [support_comp_eq_preimage, smooth_bump_function.support_eq Hlt] at hy,
    simpa only [e.symm_apply_apply] using (hR _ hy) },
  exact ⟨smooth_bump_function (e x) (R / 2) R ∘ e,
    e.continuous_at.eventually (smooth_bump_function.eventually_eq_one Hpos Hlt),
    λ y, ⟨smooth_bump_function.nonneg, smooth_bump_function.le_one⟩,
    (smooth_bump_function.times_cont_diff Hpos Hlt).comp e.times_cont_diff,
    compact_closure_of_subset_compact hKc this,
    subset.trans (closure_minimal this hKc.is_closed) hKs⟩
end
