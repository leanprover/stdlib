/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/

import measure_theory.borel_space

/-!
# Derivative is measurable

In this file we prove that the derivative of any function with complete codomain is a measurable
function. Namely, we prove:

* `is_measurable_set_of_differentiable_at`: the set `{x | differentiable_at 𝕜 f x}` is measurable;
* `measurable_fderiv`: the function `fderiv 𝕜 f` is measurable;
* `measurable_fderiv_apply_const`: for a fixed vector `y`, the function `λ x, fderiv 𝕜 f x y`
  is measurable;
* `measurable_deriv`: the function `deriv f` is measurable (for `f : 𝕜 → F`).

## Implementation

We give a proof that avoids second-countability issues, by expressing the differentiability set
as a function of open sets in the following way. Define `A (L, r, ε)` to be the set of points
where, on a ball of radius roughly `r` around `x`, the function is uniformly approximated by the
linear map `L`, up to `ε r`. It is an open set.
Let also `B (L, r, s, ε) = A (L, r, ε) ∩ A (L, s, ε)`: we require that at two possibly different
scales `r` and `s`, the function is well approximated by the linear map `L`. It is also open.

We claim that the differentiability set of `f` is exactly
`D = ⋂ ε > 0, ⋃ δ > 0, ⋂ r, s < δ, ⋃ L, B (L, r, s, ε)`.
In other words, for any `ε > 0`, we require that there is a size `δ` such that, for any two scales
below this size, the function is well approximated by a linear map, common to the two scales.

The set `⋃ L, B (L, r, s, ε)` is open, as a union of open sets. Converting the intersections and
unions to countable ones (using real numbers of the form `2 ^ (-n)`), it follows that the
differentiability set is measurable.

To prove the claim, there are two inclusions. One is trivial: if the function is differentiable
at `x`, then `x` belongs to `D` (just take `L` to be the derivative, and use that the
differentiability exactly says that the map is well approximated by `L`). This is proved in
`mem_A_of_differentiable` and `differentiable_set_subset_D`.

For the other direction, the difficulty is that `L` in the union may depend on `ε, r, s`. The key
point is that, in fact, it doesn't depend too much on them. First, if `x` belongs both to
`A (L, r, ε)` and `A (L', r, ε)`, then `L` and `L'` have to be close on a shell, and thus
`∥L - L'∥` is bounded by `ε` (see `norm_sub_le_of_mem_A`). Assume now `x ∈ D`. If one has two maps
`L` and `L'` such that `x` belongs to `A (L, r, ε)` and to `A (L', r', ε')`, one deduces that `L` is
close to `L'` by arguing as follows. Consider another scale `s` smaller than `r` and `r'`. Take a
linear map `L₁` that approximates `f` around `x` both at scales `r` and `s` w.r.t. `ε` (it exists as
`x` belongs to `D`). Take also `L₂` that approximates `f` around `x` both at scales `r'` and `s`
w.r.t. `ε'`. Then `L₁` is close to `L` (as they are close on a shell of radius `r`), and `L₂` is
close to `L₁` (as they are close on a shell of radius `s`), and `L'` is close to `L₂` (as they are
close on a shell of radius `r'`). It follows that `L` is close to `L'`, as we claimed.

It follows that the different approximating linear maps that show up form a Cauchy sequence when
`ε` tends to `0`. When the target space is complete, this sequence converges, to a limit `f'`.
With the same kind of arguments, one checks that `f` is differentiable with derivative `f'`.

To show that the derivative itself is measurable, add in the definition of `B` and `D` a set
`K` of continuous linear maps to which `L` should belong. Then, when `K` is complete, the set `D K`
is exactly the set of points where `f` is differentiable with a derivative in `K`.

## Tags

derivative, measurable function, Borel σ-algebra
-/

noncomputable theory

open set metric asymptotics filter continuous_linear_map
open topological_space (second_countable_topology)
open_locale topological_space

namespace continuous_linear_map

variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜]
  [normed_group E] [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F]

instance : measurable_space (E →L[𝕜] F) := borel _

instance : borel_space (E →L[𝕜] F) := ⟨rfl⟩

lemma measurable_apply [measurable_space F] [borel_space F] (x : E) :
  measurable (λ f : E →L[𝕜] F, f x) :=
(apply 𝕜 F x).continuous.measurable

lemma measurable_apply' [measurable_space E] [opens_measurable_space E]
  [measurable_space F] [borel_space F] :
  measurable (λ (x : E) (f : E →L[𝕜] F), f x) :=
measurable_pi_lambda _ $ λ f, f.measurable

lemma measurable_apply₂ [measurable_space E] [opens_measurable_space E]
  [second_countable_topology E] [second_countable_topology (E →L[𝕜] F)]
  [measurable_space F] [borel_space F] :
  measurable (λ p : (E →L[𝕜] F) × E, p.1 p.2) :=
is_bounded_bilinear_map_apply.continuous.measurable

lemma measurable_coe [measurable_space F] [borel_space F] :
  measurable (λ (f : E →L[𝕜] F) (x : E), f x) :=
measurable_pi_lambda _ measurable_apply

end continuous_linear_map

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variables {f : E → F} (K : set (E →L[𝕜] F))

namespace fderiv_measurable_aux

/-- The set `A f L r ε` is the set of points `x` around which the function `f` is well approximated
at scale `r` by the linear map `L`, up to an error `ε`. We tweak the definition to make sure that
this is an open set.-/
def A (f : E → F) (L : E →L[𝕜] F) (r ε : ℝ) : set E :=
{x | ∃ r' ∈ Ioc (r/2) r, ∀ y z ∈ ball x r', ∥f z - f y - L (z-y)∥ ≤ ε * r}

/-- The set `B f K r s ε` is the set of points `x` around which there exists a continuous linear map
`L` belonging to `K` (a given set of continuous linear maps) that approximates well the
function `f` (up to an error `ε`), simultaneously at scales `r` and `s`. -/
def B (f : E → F) (K : set (E →L[𝕜] F)) (r s ε : ℝ) : set E :=
⋃ (L ∈ K), (A f L r ε) ∩ (A f L s ε)

/-- The set `D f K` is a complicated set constructed using countable intersections and unions. Its
main use is that, when `K` is complete, it is exactly the set of points where `f` is differentiable,
with a derivative in `K`. -/
def D (f : E → F) (K : set (E →L[𝕜] F)) : set E :=
⋂ (e : ℕ), ⋃ (n : ℕ), ⋂ (p ≥ n) (q ≥ n), B f K ((1/2) ^ p) ((1/2) ^ q) ((1/2) ^ e)

lemma is_open_A (L : E →L[𝕜] F) (r ε : ℝ) : is_open (A f L r ε) :=
begin
  rw metric.is_open_iff,
  rintros x ⟨r', r'_mem, hr'⟩,
  obtain ⟨s, s_gt, s_lt⟩ : ∃ (s : ℝ), r / 2 < s ∧ s < r' := exists_between r'_mem.1,
  have : s ∈ Ioc (r/2) r := ⟨s_gt, le_of_lt (s_lt.trans_le r'_mem.2)⟩,
  refine ⟨r' - s, by linarith, λ x' hx', ⟨s, this, _⟩⟩,
  have B : ball x' s ⊆ ball x r' := ball_subset (le_of_lt hx'),
  assume y z hy hz,
  exact hr' y z (B hy) (B hz)
end

lemma is_open_B {K : set (E →L[𝕜] F)} {r s ε : ℝ} : is_open (B f K r s ε) :=
by simp [B, is_open_Union, is_open_inter, is_open_A]

lemma A_mono (L : E →L[𝕜] F) (r : ℝ) {ε δ : ℝ} (h : ε ≤ δ) :
  A f L r ε ⊆ A f L r δ :=
begin
  rintros x ⟨r', r'r, hr'⟩,
  refine ⟨r', r'r, λ y z hy hz, _⟩,
  apply le_trans (hr' y z hy hz),
  apply mul_le_mul_of_nonneg_right h,
  linarith [mem_ball.1 hy, r'r.2, @dist_nonneg _ _ y x],
end

lemma le_of_mem_A {r ε : ℝ} {L : E →L[𝕜] F} {x : E} (hx : x ∈ A f L r ε)
  {y z : E} (hy : y ∈ closed_ball x (r/2)) (hz : z ∈ closed_ball x (r/2)) :
  ∥f z - f y - L (z-y)∥ ≤ ε * r :=
begin
  rcases hx with ⟨r', r'mem, hr'⟩,
  exact hr' _ _ (lt_of_le_of_lt (mem_closed_ball.1 hy) r'mem.1)
    (lt_of_le_of_lt (mem_closed_ball.1 hz) r'mem.1)
end

lemma mem_A_of_differentiable {ε : ℝ} (hε : 0 < ε) {x : E} (hx : differentiable_at 𝕜 f x) :
  ∃ R > 0, ∀ r ∈ Ioo (0 : ℝ) R, x ∈ A f (fderiv 𝕜 f x) r ε :=
begin
  have := hx.has_fderiv_at,
  simp only [has_fderiv_at, has_fderiv_at_filter, is_o_iff] at this,
  rcases eventually_nhds_iff_ball.1 (this (half_pos hε)) with ⟨R, R_pos, hR⟩,
  refine ⟨R, R_pos, λ r hr, _⟩,
  have : r ∈ Ioc (r/2) r := ⟨half_lt_self hr.1, le_refl _⟩,
  refine ⟨r, this, λ y z hy hz, _⟩,
  calc  ∥f z - f y - (fderiv 𝕜 f x) (z - y)∥
      = ∥(f z - f x - (fderiv 𝕜 f x) (z - x)) - (f y - f x - (fderiv 𝕜 f x) (y - x))∥ :
    by { congr' 1, simp only [continuous_linear_map.map_sub], abel }
  ... ≤ ∥(f z - f x - (fderiv 𝕜 f x) (z - x))∥ + ∥f y - f x - (fderiv 𝕜 f x) (y - x)∥ :
    norm_sub_le _ _
  ... ≤ ε / 2 * ∥z - x∥ + ε / 2 * ∥y - x∥ :
    add_le_add (hR _ (lt_trans (mem_ball.1 hz) hr.2)) (hR _ (lt_trans (mem_ball.1 hy) hr.2))
  ... ≤ ε / 2 * r + ε / 2 * r :
    add_le_add
      (mul_le_mul_of_nonneg_left (le_of_lt (mem_ball_iff_norm.1 hz)) (le_of_lt (half_pos hε)))
      (mul_le_mul_of_nonneg_left (le_of_lt (mem_ball_iff_norm.1 hy)) (le_of_lt (half_pos hε)))
  ... = ε * r : by ring
end

lemma norm_sub_le_of_mem_A {c : 𝕜} (hc : 1 < ∥c∥)
  {r ε : ℝ} (hε : 0 < ε) (hr : 0 < r) {x : E} {L₁ L₂ : E →L[𝕜] F}
  (h₁ : x ∈ A f L₁ r ε) (h₂ : x ∈ A f L₂ r ε) : ∥L₁ - L₂∥ ≤ 4 * ∥c∥ * ε :=
begin
  have : 0 ≤ 4 * ∥c∥ * ε :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (norm_nonneg _)) hε.le,
  apply op_norm_le_of_shell (half_pos hr) this hc,
  assume y ley ylt,
  rw [div_div_eq_div_mul,
      div_le_iff' (mul_pos (by norm_num : (0 : ℝ) < 2) (zero_lt_one.trans hc))] at ley,
  calc ∥(L₁ - L₂) y∥
        = ∥(f (x + y) - f x - L₂ ((x + y) - x)) - (f (x + y) - f x - L₁ ((x + y) - x))∥ : by simp
    ... ≤ ∥(f (x + y) - f x - L₂ ((x + y) - x))∥ + ∥(f (x + y) - f x - L₁ ((x + y) - x))∥ :
      norm_sub_le _ _
    ... ≤ ε * r + ε * r :
      begin
        apply add_le_add,
        { apply le_of_mem_A h₂,
          { simp only [le_of_lt (half_pos hr), mem_closed_ball, dist_self] },
          { simp only [dist_eq_norm, add_sub_cancel', mem_closed_ball, ylt.le], } },
        { apply le_of_mem_A h₁,
          { simp only [le_of_lt (half_pos hr), mem_closed_ball, dist_self] },
          { simp only [dist_eq_norm, add_sub_cancel', mem_closed_ball, ylt.le] } },
      end
    ... = 2 * ε * r : by ring
    ... ≤ 2 * ε * (2 * ∥c∥ * ∥y∥) : mul_le_mul_of_nonneg_left ley (mul_nonneg (by norm_num) hε.le)
    ... = 4 * ∥c∥ * ε * ∥y∥ : by ring
end

/-- Easy inclusion: a differentiability point with derivative in `K` belongs to `D f K`. -/
lemma differentiable_set_subset_D : {x | differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ K} ⊆ D f K :=
begin
  assume x hx,
  rw [D, mem_Inter],
  assume e,
  have : (0 : ℝ) < (1/2) ^ e := pow_pos (by norm_num) _,
  rcases mem_A_of_differentiable this hx.1 with ⟨R, R_pos, hR⟩,
  obtain ⟨n, hn⟩ : ∃ (n : ℕ), (1/2) ^ n < R :=
    exists_pow_lt_of_lt_one R_pos (by norm_num : (1 : ℝ)/2 < 1),
  simp only [mem_Union, mem_Inter, B, mem_inter_eq],
  refine ⟨n, λ p hp q hq, ⟨fderiv 𝕜 f x, hx.2, ⟨_, _⟩⟩⟩;
  { refine hR _ ⟨pow_pos (by norm_num) _, lt_of_le_of_lt _ hn⟩,
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by assumption) }
end

/-- Harder inclusion: at a point in `D f K`, the function `f` has a derivative, in `K`. -/
lemma D_subset_differentiable_set {K : set (E →L[𝕜] F)} (hK : is_complete K) :
  D f K ⊆ {x | differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ K} :=
begin
  have P : ∀ {n : ℕ}, (0 : ℝ) < (1/2) ^ n := pow_pos (by norm_num),
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  have cpos : 0 < ∥c∥ := lt_trans zero_lt_one hc,
  assume x hx,
  have : ∀ (e : ℕ), ∃ (n : ℕ), ∀ p q, n ≤ p → n ≤ q → ∃ L ∈ K,
    x ∈ A f L ((1/2) ^ p) ((1/2) ^ e) ∩ A f L ((1/2) ^ q) ((1/2) ^ e),
  { assume e,
    have := mem_Inter.1 hx e,
    rcases mem_Union.1 this with ⟨n, hn⟩,
    refine ⟨n, λ p q hp hq, _⟩,
    simp only [mem_Inter, ge_iff_le] at hn,
    rcases mem_Union.1 (hn p hp q hq) with ⟨L, hL⟩,
    exact ⟨L, mem_Union.1 hL⟩, },
  /- Recast the assumptions: for each `e`, there exist `n e` and linear maps `L e p q` in `K`
  such that, for `p, q ≥ n e`, then `f` is well approximated by `L e p q` at scale `2 ^ (-p)` and
  `2 ^ (-q)`, with an error `2 ^ (-e)`. -/
  choose! n L hn using this,
  /- All the operators `L e p q` that show up are close to each other. To prove this, we argue
    that `L e p q` is close to `L e p r` (where `r` is large enough), as both approximate `f` at
    scale `2 ^(- p)`. And `L e p r` is close to `L e' p' r` as both approximate `f` at scale
    `2 ^ (- r)`. And `L e' p' r` is close to `L e' p' q'` as both approximate `f` at scale
    `2 ^ (- p')`. -/
  have M : ∀ e p q e' p' q', n e ≤ p → n e ≤ q → n e' ≤ p' → n e' ≤ q' → e ≤ e' →
    ∥L e p q - L e' p' q'∥ ≤ 12 * ∥c∥ * (1/2) ^ e,
  { assume e p q e' p' q' hp hq hp' hq' he',
    let r := max (n e) (n e'),
    have I : ((1:ℝ)/2)^e' ≤ (1/2)^e := pow_le_pow_of_le_one (by norm_num) (by norm_num) he',
    have J1 : ∥L e p q - L e p r∥ ≤ 4 * ∥c∥ * (1/2)^e,
    { have I1 : x ∈ A f (L e p q) ((1 / 2) ^ p) ((1/2)^e) :=
        (hn e p q hp hq).2.1,
      have I2 : x ∈ A f (L e p r) ((1 / 2) ^ p) ((1/2)^e) :=
        (hn e p r hp (le_max_left _ _)).2.1,
      exact norm_sub_le_of_mem_A hc P P I1 I2 },
    have J2 : ∥L e p r - L e' p' r∥ ≤ 4 * ∥c∥ * (1/2)^e,
    { have I1 : x ∈ A f (L e p r) ((1 / 2) ^ r) ((1/2)^e) :=
        (hn e p r hp (le_max_left _ _)).2.2,
      have I2 : x ∈ A f (L e' p' r) ((1 / 2) ^ r) ((1/2)^e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.2,
      exact norm_sub_le_of_mem_A hc P P I1 (A_mono _ _ I I2) },
    have J3 : ∥L e' p' r - L e' p' q'∥ ≤ 4 * ∥c∥ * (1/2)^e,
    { have I1 : x ∈ A f (L e' p' r) ((1 / 2) ^ p') ((1/2)^e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.1,
      have I2 : x ∈ A f (L e' p' q') ((1 / 2) ^ p') ((1/2)^e') :=
        (hn e' p' q' hp' hq').2.1,
      exact norm_sub_le_of_mem_A hc P P (A_mono _ _ I I1) (A_mono _ _ I I2) },
    calc ∥L e p q - L e' p' q'∥
          = ∥(L e p q - L e p r) + (L e p r - L e' p' r) + (L e' p' r - L e' p' q')∥ :
        by { congr' 1, abel }
      ... ≤ ∥L e p q - L e p r∥ + ∥L e p r - L e' p' r∥ + ∥L e' p' r - L e' p' q'∥ :
        le_trans (norm_add_le _ _) (add_le_add_right (norm_add_le _ _) _)
      ... ≤ 4 * ∥c∥ * (1/2)^e + 4 * ∥c∥ * (1/2)^e + 4 * ∥c∥ * (1/2)^e :
        by apply_rules [add_le_add]
      ... = 12 * ∥c∥ * (1/2)^e : by ring },
  /- For definiteness, use `L0 e = L e (n e) (n e)`, to have a single sequence. We claim that this
  is a Cauchy sequence. -/
  let L0 : ℕ → (E →L[𝕜] F) := λ e, L e (n e) (n e),
  have : cauchy_seq L0,
  { rw cauchy_seq_iff',
    assume ε εpos,
    obtain ⟨e, he⟩ : ∃ (e : ℕ), (1/2) ^ e < ε / (12 * ∥c∥) :=
      exists_pow_lt_of_lt_one (div_pos εpos (mul_pos (by norm_num) cpos)) (by norm_num),
    refine ⟨e, λ e' he', _⟩,
    rw [dist_comm, dist_eq_norm],
    calc ∥L0 e - L0 e'∥
          ≤ 12 * ∥c∥ * (1/2)^e : M _ _ _ _ _ _ (le_refl _) (le_refl _) (le_refl _) (le_refl _) he'
      ... < 12 * ∥c∥ * (ε / (12 * ∥c∥)) :
        mul_lt_mul' (le_refl _) he (le_of_lt P) (mul_pos (by norm_num) cpos)
      ... = ε : by { field_simp [(by norm_num : (12 : ℝ) ≠ 0), ne_of_gt cpos], ring } },
  /- As it is Cauchy, the sequence `L0` converges, to a limit `f'` in `K`.-/
  obtain ⟨f', f'K, hf'⟩ : ∃ f' ∈ K, tendsto L0 at_top (𝓝 f') :=
    cauchy_seq_tendsto_of_is_complete hK (λ e, (hn e (n e) (n e) (le_refl _) (le_refl _)).1) this,
  have Lf' : ∀ e p, n e ≤ p → ∥L e (n e) p - f'∥ ≤ 12 * ∥c∥ * (1/2)^e,
  { assume e p hp,
    apply le_of_tendsto (tendsto_const_nhds.sub hf').norm,
    rw eventually_at_top,
    exact ⟨e, λ e' he', M _ _ _ _ _ _ (le_refl _) hp (le_refl _) (le_refl _) he'⟩ },
  /- Let us show that `f` has derivative `f'` at `x`. -/
  have : has_fderiv_at f f' x,
  { simp only [has_fderiv_at_iff_is_o_nhds_zero, is_o_iff],
    /- to get an approximation with a precision `ε`, we will replace `f` with `L e (n e) m` for
    some large enough `e` (yielding a small error by uniform approximation). As one can vary `m`,
    this makes it possible to cover all scales, and thus to obtain a good linear approximation in
    the whole ball of radius `(1/2)^(n e)`. -/
    assume ε εpos,
    have pos : 0 < 4 + 12 * ∥c∥ :=
      add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg (by norm_num) (norm_nonneg _)),
    obtain ⟨e, he⟩ : ∃ (e : ℕ), (1 / 2) ^ e < ε / (4 + 12 * ∥c∥) :=
      exists_pow_lt_of_lt_one (div_pos εpos pos) (by norm_num),
    rw eventually_nhds_iff_ball,
    refine ⟨(1/2) ^ (n e + 1), P, λ y hy, _⟩,
    -- We need to show that `f (x + y) - f x - f' y` is small. For this, we will work at scale
    -- `k` where `k` is chosen with `∥y∥ ∼ 2 ^ (-k)`.
    by_cases y_pos : y = 0, {simp [y_pos] },
    have yzero : 0 < ∥y∥ := norm_pos_iff.mpr y_pos,
    have y_lt : ∥y∥ < (1/2) ^ (n e + 1), by simpa using mem_ball_iff_norm.1 hy,
    have yone : ∥y∥ ≤ 1 :=
      le_trans (y_lt.le) (pow_le_one _ (by norm_num) (by norm_num)),
    -- define the scale `k`.
    obtain ⟨k, hk, h'k⟩ : ∃ (k : ℕ), (1/2) ^ (k + 1) < ∥y∥ ∧ ∥y∥ ≤ (1/2) ^ k :=
      exists_nat_pow_near_of_lt_one yzero yone (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (1 : ℝ)/2 < 1),
    -- the scale is large enough (as `y` is small enough)
    have k_gt : n e < k,
    { have : ((1:ℝ)/2) ^ (k + 1) < (1/2) ^ (n e + 1) := lt_trans hk y_lt,
      rw pow_lt_pow_iff_of_lt_one (by norm_num : (0 : ℝ) < 1/2) (by norm_num) at this,
      linarith },
    set m := k - 1 with hl,
    have m_ge : n e ≤ m := nat.le_pred_of_lt k_gt,
    have km : k = m + 1 := (nat.succ_pred_eq_of_pos (lt_of_le_of_lt (zero_le _) k_gt)).symm,
    rw km at hk h'k,
    -- `f` is well approximated by `L e (n e) k` at the relevant scale
    -- (in fact, we use `m = k - 1` instead of `k` because of the precise definition of `A`).
    have J1 : ∥f (x + y) - f x - L e (n e) m ((x + y) - x)∥ ≤ (1/2) ^ e * (1/2) ^ m,
    { apply le_of_mem_A (hn e (n e) m (le_refl _) m_ge).2.2,
      { simp only [mem_closed_ball, dist_self],
        exact div_nonneg (le_of_lt P) (zero_le_two) },
      { simp [dist_eq_norm],
        convert h'k,
        field_simp,
        ring_exp } },
    have J2 : ∥f (x + y) - f x - L e (n e) m y∥ ≤ 4 * (1/2) ^ e * ∥y∥ := calc
      ∥f (x + y) - f x - L e (n e) m y∥ ≤ (1/2) ^ e * (1/2) ^ m :
        by simpa only [add_sub_cancel'] using J1
      ... = 4 * (1/2) ^ e * (1/2) ^ (m + 2) : by { field_simp, ring_exp }
      ... ≤ 4 * (1/2) ^ e * ∥y∥ :
        mul_le_mul_of_nonneg_left (le_of_lt hk) (mul_nonneg (by norm_num) (le_of_lt P)),
    -- use the previous estimates to see that `f (x + y) - f x - f' y` is small.
    calc ∥f (x + y) - f x - f' y∥
        = ∥(f (x + y) - f x - L e (n e) m y) + (L e (n e) m - f') y∥ :
      by { congr' 1, simp, abel }
    ... ≤ ∥f (x + y) - f x - L e (n e) m y∥ + ∥(L e (n e) m - f') y∥ :
      norm_add_le _ _
    ... ≤ 4 * (1/2) ^ e * ∥y∥ + 12 * ∥c∥ * (1/2) ^ e * ∥y∥ :
      add_le_add J2
        (le_trans (le_op_norm _ _) (mul_le_mul_of_nonneg_right (Lf' _ _ m_ge) (norm_nonneg _)))
    ... = (4 + 12 * ∥c∥) * ∥y∥ * (1/2) ^ e : by ring
    ... ≤ (4 + 12 * ∥c∥) * ∥y∥ * (ε / (4 + 12 * ∥c∥)) :
      mul_le_mul_of_nonneg_left he.le
        (mul_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (norm_nonneg _)))
          (norm_nonneg _))
    ... = ε * ∥y∥ : by { field_simp [ne_of_gt pos], ring } },
  rw ← this.fderiv at f'K,
  exact ⟨this.differentiable_at, f'K⟩
end

theorem differentiable_set_eq_D (hK : is_complete K) :
  {x | differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ K} = D f K :=
subset.antisymm (differentiable_set_subset_D _) (D_subset_differentiable_set hK)

end fderiv_measurable_aux

open fderiv_measurable_aux

variables [measurable_space E] [opens_measurable_space E]
variables (𝕜 f)

/-- The set of differentiability points of a function, with derivative in a given complete set,
is Borel-measurable. -/
theorem is_measurable_set_of_differentiable_at_of_is_complete
  {K : set (E →L[𝕜] F)} (hK : is_complete K) :
  is_measurable {x | differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ K} :=
by simp [differentiable_set_eq_D K hK, D, is_open_B.is_measurable, is_measurable.Inter_Prop,
         is_measurable.Inter, is_measurable.Union]

variable [complete_space F]

/-- The set of differentiability points of a function taking values in a complete space is
Borel-measurable. -/
theorem is_measurable_set_of_differentiable_at :
  is_measurable {x | differentiable_at 𝕜 f x} :=
begin
  have : is_complete (univ : set (E →L[𝕜] F)) := complete_univ,
  convert is_measurable_set_of_differentiable_at_of_is_complete 𝕜 f this,
  simp
end

lemma measurable_fderiv : measurable (fderiv 𝕜 f) :=
begin
  refine measurable_of_is_closed (λ s hs, _),
  have : fderiv 𝕜 f ⁻¹' s = {x | differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ s} ∪
    {x | (0 : E →L[𝕜] F) ∈ s} ∩ {x | ¬differentiable_at 𝕜 f x} :=
    set.ext (λ x, mem_preimage.trans fderiv_mem_iff),
  rw this,
  exact (is_measurable_set_of_differentiable_at_of_is_complete _ _ hs.is_complete).union
    ((is_measurable.const _).inter (is_measurable_set_of_differentiable_at _ _).compl)
end

lemma measurable_fderiv_apply_const [measurable_space F] [borel_space F] (y : E) :
  measurable (λ x, fderiv 𝕜 f x y) :=
(continuous_linear_map.measurable_apply y).comp (measurable_fderiv 𝕜 f)

variable {𝕜}

lemma measurable_deriv [measurable_space 𝕜] [opens_measurable_space 𝕜] [measurable_space F]
  [borel_space F] (f : 𝕜 → F) : measurable (deriv f) :=
by simpa only [fderiv_deriv] using measurable_fderiv_apply_const 𝕜 f 1
