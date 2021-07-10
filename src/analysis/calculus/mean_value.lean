/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.calculus.local_extr
import analysis.convex.topology
import data.complex.is_R_or_C

/-!
# The mean value inequality and equalities

In this file we prove the following facts:

* `convex.norm_image_sub_le_of_norm_deriv_le` : if `f` is differentiable on a convex set `s`
  and the norm of its derivative is bounded by `C`, then `f` is Lipschitz continuous on `s` with
  constant `C`; also a variant in which what is bounded by `C` is the norm of the difference of the
  derivative from a fixed linear map. This lemma and its versions are formulated using `is_R_or_C`,
  so they work both for real and complex derivatives.

* `image_le_of*`, `image_norm_le_of_*` : several similar lemmas deducing `f x ≤ B x` or
  `∥f x∥ ≤ B x` from upper estimates on `f'` or `∥f'∥`, respectively. These lemmas differ by
  their assumptions:

  * `of_liminf_*` lemmas assume that limit inferior of some ratio is less than `B' x`;
  * `of_deriv_right_*`, `of_norm_deriv_right_*` lemmas assume that the right derivative
    or its norm is less than `B' x`;
  * `of_*_lt_*` lemmas assume a strict inequality whenever `f x = B x` or `∥f x∥ = B x`;
  * `of_*_le_*` lemmas assume a non-strict inequality everywhere on `[a, b)`;
  * name of a lemma ends with `'` if (1) it assumes that `B` is continuous on `[a, b]`
    and has a right derivative at every point of `[a, b)`, and (2) the lemma has
    a counterpart assuming that `B` is differentiable everywhere on `ℝ`

* `norm_image_sub_le_*_segment` : if derivative of `f` on `[a, b]` is bounded above
  by a constant `C`, then `∥f x - f a∥ ≤ C * ∥x - a∥`; several versions deal with
  right derivative and derivative within `[a, b]` (`has_deriv_within_at` or `deriv_within`).

* `convex.is_const_of_fderiv_within_eq_zero` : if a function has derivative `0` on a convex set `s`,
  then it is a constant on `s`.

* `exists_ratio_has_deriv_at_eq_ratio_slope` and `exists_ratio_deriv_eq_ratio_slope` :
  Cauchy's Mean Value Theorem.

* `exists_has_deriv_at_eq_slope` and `exists_deriv_eq_slope` : Lagrange's Mean Value Theorem.

* `domain_mvt` : Lagrange's Mean Value Theorem, applied to a segment in a convex domain.

* `convex.image_sub_lt_mul_sub_of_deriv_lt`, `convex.mul_sub_lt_image_sub_of_lt_deriv`,
  `convex.image_sub_le_mul_sub_of_deriv_le`, `convex.mul_sub_le_image_sub_of_le_deriv`,
  if `∀ x, C (</≤/>/≥) (f' x)`, then `C * (y - x) (</≤/>/≥) (f y - f x)` whenever `x < y`.

* `convex.mono_of_deriv_nonneg`, `convex.antimono_of_deriv_nonpos`,
  `convex.strict_mono_of_deriv_pos`, `convex.strict_antimono_of_deriv_neg` :
  if the derivative of a function is non-negative/non-positive/positive/negative, then
  the function is monotone/monotonically decreasing/strictly monotone/strictly monotonically
  decreasing.

* `convex_on_of_deriv_mono`, `convex_on_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.

* `strict_fderiv_of_cont_diff` : a C^1 function over the reals is strictly differentiable.  (This
  is a corollary of the mean value inequality.)
-/


variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F]

open metric set asymptotics continuous_linear_map filter
open_locale classical topological_space nnreal

/-! ### One-dimensional fencing inequalities -/

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
lemma image_le_of_liminf_slope_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  -- `hf'` actually says `liminf (z - x)⁻¹ * (f z - f x) ≤ f' x`
  (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r →
    ∃ᶠ z in 𝓝[Ioi x] x, (z - x)⁻¹ * (f z - f x) < r)
  {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ici x) x)
  (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
begin
  change Icc a b ⊆ {x | f x ≤ B x},
  set s := {x | f x ≤ B x} ∩ Icc a b,
  have A : continuous_on (λ x, (f x, B x)) (Icc a b), from hf.prod hB,
  have : is_closed s,
  { simp only [s, inter_comm],
    exact A.preimage_closed_of_closed is_closed_Icc order_closed_topology.is_closed_le' },
  apply this.Icc_subset_of_forall_exists_gt ha,
  rintros x ⟨hxB : f x ≤ B x, xab⟩ y hy,
  cases hxB.lt_or_eq with hxB hxB,
  { -- If `f x < B x`, then all we need is continuity of both sides
    refine nonempty_of_mem_sets (inter_mem_sets _ (Ioc_mem_nhds_within_Ioi ⟨le_rfl, hy⟩)),
    have : ∀ᶠ x in 𝓝[Icc a b] x, f x < B x,
      from A x (Ico_subset_Icc_self xab)
        (is_open.mem_nhds (is_open_lt continuous_fst continuous_snd) hxB),
    have : ∀ᶠ x in 𝓝[Ioi x] x, f x < B x,
      from nhds_within_le_of_mem (Icc_mem_nhds_within_Ioi xab) this,
    exact this.mono (λ y, le_of_lt) },
  { rcases exists_between (bound x xab hxB) with ⟨r, hfr, hrB⟩,
    specialize hf' x xab r hfr,
    have HB : ∀ᶠ z in 𝓝[Ioi x] x, r < (z - x)⁻¹ * (B z - B x),
      from (has_deriv_within_at_iff_tendsto_slope' $ lt_irrefl x).1
        (hB' x xab).Ioi_of_Ici (Ioi_mem_nhds hrB),
    obtain ⟨z, ⟨hfz, hzB⟩, hz⟩ :
      ∃ z, ((z - x)⁻¹ * (f z - f x) < r ∧ r < (z - x)⁻¹ * (B z - B x)) ∧ z ∈ Ioc x y,
      from ((hf'.and_eventually HB).and_eventually (Ioc_mem_nhds_within_Ioi ⟨le_rfl, hy⟩)).exists,
    refine ⟨z, _, hz⟩,
    have := (hfz.trans hzB).le,
    rwa [mul_le_mul_left (inv_pos.2 $ sub_pos.2 hz.1), hxB, sub_le_sub_iff_right] at this }
end

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
lemma image_le_of_liminf_slope_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  -- `hf'` actually says `liminf (z - x)⁻¹ * (f z - f x) ≤ f' x`
  (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r →
    ∃ᶠ z in 𝓝[Ioi x] x, (z - x)⁻¹ * (f z - f x) < r)
  {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ x, has_deriv_at B (B' x) x)
  (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
image_le_of_liminf_slope_right_lt_deriv_boundary' hf hf' ha
  (λ x hx, (hB x).continuous_at.continuous_within_at)
  (λ x hx, (hB x).has_deriv_within_at) bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by `B'`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
lemma image_le_of_liminf_slope_right_le_deriv_boundary {f : ℝ → ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ici x) x)
  -- `bound` actually says `liminf (z - x)⁻¹ * (f z - f x) ≤ B' x`
  (bound : ∀ x ∈ Ico a b, ∀ r, B' x < r →
    ∃ᶠ z in 𝓝[Ioi x] x, (z - x)⁻¹ * (f z - f x) < r) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
begin
  have Hr : ∀ x ∈ Icc a b, ∀ r > 0, f x ≤ B x + r * (x - a),
  { intros x hx r hr,
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hf bound,
    { rwa [sub_self, mul_zero, add_zero] },
    { exact hB.add (continuous_on_const.mul
        (continuous_id.continuous_on.sub continuous_on_const)) },
    { assume x hx,
      exact (hB' x hx).add (((has_deriv_within_at_id x (Ici x)).sub_const a).const_mul r) },
    { assume x hx _,
      rw [mul_one],
      exact (lt_add_iff_pos_right _).2 hr },
    exact hx },
  assume x hx,
  have : continuous_within_at (λ r, B x + r * (x - a)) (Ioi 0) 0,
    from continuous_within_at_const.add (continuous_within_at_id.mul continuous_within_at_const),
  convert continuous_within_at_const.closure_le _ this (Hr x hx); simp
end

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
lemma image_le_of_deriv_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ici x) x)
  {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ici x) x)
  (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
image_le_of_liminf_slope_right_lt_deriv_boundary' hf
  (λ x hx r hr, (hf' x hx).liminf_right_slope_le hr) ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
lemma image_le_of_deriv_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ici x) x)
  {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ x, has_deriv_at B (B' x) x)
  (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
image_le_of_deriv_right_lt_deriv_boundary' hf hf' ha
  (λ x hx, (hB x).continuous_at.continuous_within_at)
  (λ x hx, (hB x).has_deriv_within_at) bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x ≤ B' x` on `[a, b)`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
lemma image_le_of_deriv_right_le_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ici x) x)
  {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ici x) x)
  (bound : ∀ x ∈ Ico a b, f' x ≤ B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB' $
assume x hx r hr, (hf' x hx).liminf_right_slope_le (lt_of_le_of_lt (bound x hx) hr)

/-! ### Vector-valued functions `f : ℝ → E` -/

section

variables {f : ℝ → E} {a b : ℝ}

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `B` has right derivative at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(∥f z∥ - ∥f x∥) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. -/
lemma image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary {E : Type*} [normed_group E]
  {f : ℝ → E} {f' : ℝ → ℝ} (hf : continuous_on f (Icc a b))
  -- `hf'` actually says `liminf ∥z - x∥⁻¹ * (∥f z∥ - ∥f x∥) ≤ f' x`
  (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r →
    ∃ᶠ z in 𝓝[Ioi x] x, (z - x)⁻¹ * (∥f z∥ - ∥f x∥) < r)
  {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ici x) x)
  (bound : ∀ x ∈ Ico a b, ∥f x∥ = B x → f' x < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_le_of_liminf_slope_right_lt_deriv_boundary' (continuous_norm.comp_continuous_on hf) hf'
    ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* the norm of `f'` is strictly less than `B'` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
lemma image_norm_le_of_norm_deriv_right_lt_deriv_boundary' {f' : ℝ → E}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ici x) x)
  {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ici x) x)
  (bound : ∀ x ∈ Ico a b, ∥f x∥ = B x → ∥f' x∥ < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary hf
  (λ x hx r hr, (hf' x hx).liminf_right_slope_norm_le hr) ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* the norm of `f'` is strictly less than `B'` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
lemma image_norm_le_of_norm_deriv_right_lt_deriv_boundary {f' : ℝ → E}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ici x) x)
  {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : ∀ x, has_deriv_at B (B' x) x)
  (bound : ∀ x ∈ Ico a b, ∥f x∥ = B x → ∥f' x∥ < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hf hf' ha
  (λ x hx, (hB x).continuous_at.continuous_within_at)
  (λ x hx, (hB x).has_deriv_within_at) bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* we have `∥f' x∥ ≤ B x` everywhere on `[a, b)`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
lemma image_norm_le_of_norm_deriv_right_le_deriv_boundary' {f' : ℝ → E}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ici x) x)
  {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : continuous_on B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, has_deriv_within_at B (B' x) (Ici x) x)
  (bound : ∀ x ∈ Ico a b, ∥f' x∥ ≤ B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_le_of_liminf_slope_right_le_deriv_boundary (continuous_norm.comp_continuous_on hf) ha hB hB' $
  (λ x hx r hr, (hf' x hx).liminf_right_slope_norm_le (lt_of_le_of_lt (bound x hx) hr))

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* we have `∥f' x∥ ≤ B x` everywhere on `[a, b)`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
lemma image_norm_le_of_norm_deriv_right_le_deriv_boundary {f' : ℝ → E}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ici x) x)
  {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a) (hB : ∀ x, has_deriv_at B (B' x) x)
  (bound : ∀ x ∈ Ico a b, ∥f' x∥ ≤ B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha
  (λ x hx, (hB x).continuous_at.continuous_within_at)
  (λ x hx, (hB x).has_deriv_within_at) bound

/-- A function on `[a, b]` with the norm of the right derivative bounded by `C`
satisfies `∥f x - f a∥ ≤ C * (x - a)`. -/
theorem norm_image_sub_le_of_norm_deriv_right_le_segment {f' : ℝ → E} {C : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ici x) x)
  (bound : ∀x ∈ Ico a b, ∥f' x∥ ≤ C) :
  ∀ x ∈ Icc a b, ∥f x - f a∥ ≤ C * (x - a) :=
begin
  let g := λ x, f x - f a,
  have hg : continuous_on g (Icc a b), from hf.sub continuous_on_const,
  have hg' : ∀ x ∈ Ico a b, has_deriv_within_at g (f' x) (Ici x) x,
  { assume x hx,
    simpa using (hf' x hx).sub (has_deriv_within_at_const _ _ _) },
  let B := λ x, C * (x - a),
  have hB : ∀ x, has_deriv_at B C x,
  { assume x,
    simpa using (has_deriv_at_const x C).mul ((has_deriv_at_id x).sub (has_deriv_at_const x a)) },
  convert image_norm_le_of_norm_deriv_right_le_deriv_boundary hg hg' _ hB bound,
  simp only [g, B], rw [sub_self, norm_zero, sub_self, mul_zero]
end

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `∥f x - f a∥ ≤ C * (x - a)`, `has_deriv_within_at`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment' {f' : ℝ → E} {C : ℝ}
  (hf : ∀ x ∈ Icc a b, has_deriv_within_at f (f' x) (Icc a b) x)
  (bound : ∀x ∈ Ico a b, ∥f' x∥ ≤ C) :
  ∀ x ∈ Icc a b, ∥f x - f a∥ ≤ C * (x - a) :=
begin
  refine norm_image_sub_le_of_norm_deriv_right_le_segment
    (λ x hx, (hf x hx).continuous_within_at) (λ x hx, _) bound,
  exact (hf x $ Ico_subset_Icc_self hx).nhds_within (Icc_mem_nhds_within_Ici hx)
end

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `∥f x - f a∥ ≤ C * (x - a)`, `deriv_within`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment {C : ℝ} (hf : differentiable_on ℝ f (Icc a b))
  (bound : ∀x ∈ Ico a b, ∥deriv_within f (Icc a b) x∥ ≤ C) :
  ∀ x ∈ Icc a b, ∥f x - f a∥ ≤ C * (x - a) :=
begin
  refine norm_image_sub_le_of_norm_deriv_le_segment' _ bound,
  exact λ x hx, (hf x  hx).has_deriv_within_at
end

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `∥f 1 - f 0∥ ≤ C`, `has_deriv_within_at`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01' {f' : ℝ → E} {C : ℝ}
  (hf : ∀ x ∈ Icc (0:ℝ) 1, has_deriv_within_at f (f' x) (Icc (0:ℝ) 1) x)
  (bound : ∀x ∈ Ico (0:ℝ) 1, ∥f' x∥ ≤ C) :
  ∥f 1 - f 0∥ ≤ C :=
by simpa only [sub_zero, mul_one]
  using norm_image_sub_le_of_norm_deriv_le_segment' hf bound 1 (right_mem_Icc.2 zero_le_one)

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `∥f 1 - f 0∥ ≤ C`, `deriv_within` version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01 {C : ℝ}
  (hf : differentiable_on ℝ f (Icc (0:ℝ) 1))
  (bound : ∀x ∈ Ico (0:ℝ) 1, ∥deriv_within f (Icc (0:ℝ) 1) x∥ ≤ C) :
  ∥f 1 - f 0∥ ≤ C :=
by simpa only [sub_zero, mul_one]
  using norm_image_sub_le_of_norm_deriv_le_segment hf bound 1 (right_mem_Icc.2 zero_le_one)

theorem constant_of_has_deriv_right_zero (hcont : continuous_on f (Icc a b))
  (hderiv : ∀ x ∈ Ico a b, has_deriv_within_at f 0 (Ici x) x) :
  ∀ x ∈ Icc a b, f x = f a :=
by simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using
  λ x hx, norm_image_sub_le_of_norm_deriv_right_le_segment
    hcont hderiv (λ y hy, by rw norm_le_zero_iff) x hx

theorem constant_of_deriv_within_zero (hdiff : differentiable_on ℝ f (Icc a b))
  (hderiv : ∀ x ∈ Ico a b, deriv_within f (Icc a b) x = 0) :
  ∀ x ∈ Icc a b, f x = f a :=
begin
  have H : ∀ x ∈ Ico a b, ∥deriv_within f (Icc a b) x∥ ≤ 0 :=
    by simpa only [norm_le_zero_iff] using λ x hx, hderiv x hx,
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using
    λ x hx, norm_image_sub_le_of_norm_deriv_le_segment hdiff H x hx,
end

variables {f' g : ℝ → E}

/-- If two continuous functions on `[a, b]` have the same right derivative and are equal at `a`,
  then they are equal everywhere on `[a, b]`. -/
theorem eq_of_has_deriv_right_eq
  (derivf : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ici x) x)
  (derivg : ∀ x ∈ Ico a b, has_deriv_within_at g (f' x) (Ici x) x)
  (fcont : continuous_on f (Icc a b)) (gcont : continuous_on g (Icc a b))
  (hi : f a = g a) :
  ∀ y ∈ Icc a b, f y = g y :=
begin
  simp only [← @sub_eq_zero _ _ (f _)] at hi ⊢,
  exact hi ▸ constant_of_has_deriv_right_zero (fcont.sub gcont)
    (λ y hy, by simpa only [sub_self] using (derivf y hy).sub (derivg y hy)),
end

/-- If two differentiable functions on `[a, b]` have the same derivative within `[a, b]` everywhere
  on `[a, b)` and are equal at `a`, then they are equal everywhere on `[a, b]`. -/
theorem eq_of_deriv_within_eq (fdiff : differentiable_on ℝ f (Icc a b))
  (gdiff : differentiable_on ℝ g (Icc a b))
  (hderiv : eq_on (deriv_within f (Icc a b)) (deriv_within g (Icc a b)) (Ico a b))
  (hi : f a = g a) :
  ∀ y ∈ Icc a b, f y = g y :=
begin
  have A : ∀ y ∈ Ico a b, has_deriv_within_at f (deriv_within f (Icc a b) y) (Ici y) y :=
    λ y hy, (fdiff y (mem_Icc_of_Ico hy)).has_deriv_within_at.nhds_within
      (Icc_mem_nhds_within_Ici hy),
  have B : ∀ y ∈ Ico a b, has_deriv_within_at g (deriv_within g (Icc a b) y) (Ici y) y :=
    λ y hy, (gdiff y (mem_Icc_of_Ico hy)).has_deriv_within_at.nhds_within
      (Icc_mem_nhds_within_Ici hy),
  exact eq_of_has_deriv_right_eq A (λ y hy, (hderiv hy).symm ▸ B y hy) fdiff.continuous_on
    gdiff.continuous_on hi
end

end

/-!
### Vector-valued functions `f : E → G`

Theorems in this section work both for real and complex differentiable functions. We use assumptions
`[is_R_or_C 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 G]` to achieve this result. For the domain `E` we
also assume `[normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E]` to have a notion of a `convex` set. In both
interesting cases `𝕜 = ℝ` and `𝕜 = ℂ` the assumption `[is_scalar_tower ℝ 𝕜 E]` is satisfied
automatically. -/

section

variables {𝕜 G : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E] [is_scalar_tower ℝ 𝕜 E]
  [normed_group G] [normed_space 𝕜 G] {f : E → G} {C : ℝ} {s : set E} {x y : E}
  {f' : E → E →L[𝕜] G} {φ : E →L[𝕜] G}

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`, then
the function is `C`-Lipschitz. Version with `has_fderiv_within`. -/
theorem convex.norm_image_sub_le_of_norm_has_fderiv_within_le
  (hf : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x) (bound : ∀x∈s, ∥f' x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
begin
  letI : normed_space ℝ G := restrict_scalars.normed_space ℝ 𝕜 G,
  letI : is_scalar_tower ℝ 𝕜 G := restrict_scalars.is_scalar_tower _ _ _,
  /- By composition with `t ↦ x + t • (y-x)`, we reduce to a statement for functions defined
  on `[0,1]`, for which it is proved in `norm_image_sub_le_of_norm_deriv_le_segment`.
  We just have to check the differentiability of the composition and bounds on its derivative,
  which is straightforward but tedious for lack of automation. -/
  have C0 : 0 ≤ C := le_trans (norm_nonneg _) (bound x xs),
  set g : ℝ → E := λ t, x + t • (y - x),
  have Dg : ∀ t, has_deriv_at g (y-x) t,
  { assume t,
    simpa only [one_smul] using ((has_deriv_at_id t).smul_const (y - x)).const_add x },
  have segm : Icc 0 1 ⊆ g ⁻¹' s,
  { rw [← image_subset_iff, ← segment_eq_image'],
    apply hs.segment_subset xs ys },
  have : f x = f (g 0), by { simp only [g], rw [zero_smul, add_zero] },
  rw this,
  have : f y = f (g 1), by { simp only [g], rw [one_smul, add_sub_cancel'_right] },
  rw this,
  have D2: ∀ t ∈ Icc (0:ℝ) 1, has_deriv_within_at (f ∘ g) (f' (g t) (y - x)) (Icc 0 1) t,
  { intros t ht,
    have : has_fderiv_within_at f ((f' (g t)).restrict_scalars ℝ) s (g t),
      from hf (g t) (segm ht),
    exact this.comp_has_deriv_within_at _ (Dg t).has_deriv_within_at segm },
  apply norm_image_sub_le_of_norm_deriv_le_segment_01' D2,
  refine λ t ht, le_of_op_norm_le _ _ _,
  exact bound (g t) (segm $ Ico_subset_Icc_self ht)
end

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `has_fderiv_within` and
`lipschitz_on_with`. -/
theorem convex.lipschitz_on_with_of_norm_has_fderiv_within_le
  (hf : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x) (bound : ∀x∈s, ∥f' x∥ ≤ C)
  (hs : convex s) : lipschitz_on_with (real.to_nnreal C) f s :=
begin
  rw lipschitz_on_with_iff_norm_sub_le,
  intros x x_in y y_in,
  convert hs.norm_image_sub_le_of_norm_has_fderiv_within_le hf bound y_in x_in,
  exact real.coe_to_nnreal C ((norm_nonneg $ f' x).trans $ bound x x_in)
end

/-- The mean value theorem on a convex set: if the derivative of a function within this set is
bounded by `C`, then the function is `C`-Lipschitz. Version with `fderiv_within`. -/
theorem convex.norm_image_sub_le_of_norm_fderiv_within_le
  (hf : differentiable_on 𝕜 f s) (bound : ∀x∈s, ∥fderiv_within 𝕜 f s x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
hs.norm_image_sub_le_of_norm_has_fderiv_within_le (λ x hx, (hf x hx).has_fderiv_within_at)
bound xs ys

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderiv_within` and
`lipschitz_on_with`. -/
theorem convex.lipschitz_on_with_of_norm_fderiv_within_le
  (hf : differentiable_on 𝕜 f s) (bound : ∀x∈s, ∥fderiv_within 𝕜 f s x∥ ≤ C)
  (hs : convex s) : lipschitz_on_with (real.to_nnreal C) f s:=
hs.lipschitz_on_with_of_norm_has_fderiv_within_le (λ x hx, (hf x hx).has_fderiv_within_at) bound

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`,
then the function is `C`-Lipschitz. Version with `fderiv`. -/
theorem convex.norm_image_sub_le_of_norm_fderiv_le
  (hf : ∀ x ∈ s, differentiable_at 𝕜 f x) (bound : ∀x∈s, ∥fderiv 𝕜 f x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
hs.norm_image_sub_le_of_norm_has_fderiv_within_le
(λ x hx, (hf x hx).has_fderiv_at.has_fderiv_within_at) bound xs ys

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderiv` and `lipschitz_on_with`. -/
theorem convex.lipschitz_on_with_of_norm_fderiv_le
  (hf : ∀ x ∈ s, differentiable_at 𝕜 f x) (bound : ∀x∈s, ∥fderiv 𝕜 f x∥ ≤ C)
  (hs : convex s) : lipschitz_on_with (real.to_nnreal C) f s :=
hs.lipschitz_on_with_of_norm_has_fderiv_within_le
(λ x hx, (hf x hx).has_fderiv_at.has_fderiv_within_at) bound

/-- Variant of the mean value inequality on a convex set, using a bound on the difference between
the derivative and a fixed linear map, rather than a bound on the derivative itself. Version with
`has_fderiv_within`. -/
theorem convex.norm_image_sub_le_of_norm_has_fderiv_within_le'
  (hf : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x) (bound : ∀x∈s, ∥f' x - φ∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x - φ (y - x)∥ ≤ C * ∥y - x∥ :=
begin
  /- We subtract `φ` to define a new function `g` for which `g' = 0`, for which the previous theorem
  applies, `convex.norm_image_sub_le_of_norm_has_fderiv_within_le`. Then, we just need to glue
  together the pieces, expressing back `f` in terms of `g`. -/
  let g := λy, f y - φ y,
  have hg : ∀ x ∈ s, has_fderiv_within_at g (f' x - φ) s x :=
    λ x xs, (hf x xs).sub φ.has_fderiv_within_at,
  calc ∥f y - f x - φ (y - x)∥ = ∥f y - f x - (φ y - φ x)∥ : by simp
  ... = ∥(f y - φ y) - (f x - φ x)∥ : by abel
  ... = ∥g y - g x∥ : by simp
  ... ≤ C * ∥y - x∥ : convex.norm_image_sub_le_of_norm_has_fderiv_within_le hg bound hs xs ys,
end

/-- Variant of the mean value inequality on a convex set. Version with `fderiv_within`. -/
theorem convex.norm_image_sub_le_of_norm_fderiv_within_le'
  (hf : differentiable_on 𝕜 f s) (bound : ∀x∈s, ∥fderiv_within 𝕜 f s x - φ∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x - φ (y - x)∥ ≤ C * ∥y - x∥ :=
hs.norm_image_sub_le_of_norm_has_fderiv_within_le' (λ x hx, (hf x hx).has_fderiv_within_at)
bound xs ys

/-- Variant of the mean value inequality on a convex set. Version with `fderiv`. -/
theorem convex.norm_image_sub_le_of_norm_fderiv_le'
  (hf : ∀ x ∈ s, differentiable_at 𝕜 f x) (bound : ∀x∈s, ∥fderiv 𝕜 f x - φ∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x - φ (y - x)∥ ≤ C * ∥y - x∥ :=
hs.norm_image_sub_le_of_norm_has_fderiv_within_le'
(λ x hx, (hf x hx).has_fderiv_at.has_fderiv_within_at) bound xs ys

/-- If a function has zero Fréchet derivative at every point of a convex set,
then it is a constant on this set. -/
theorem convex.is_const_of_fderiv_within_eq_zero (hs : convex s) (hf : differentiable_on 𝕜 f s)
  (hf' : ∀ x ∈ s, fderiv_within 𝕜 f s x = 0) (hx : x ∈ s) (hy : y ∈ s) :
  f x = f y :=
have bound : ∀ x ∈ s, ∥fderiv_within 𝕜 f s x∥ ≤ 0,
  from λ x hx, by simp only [hf' x hx, norm_zero],
by simpa only [(dist_eq_norm _ _).symm, zero_mul, dist_le_zero, eq_comm]
  using hs.norm_image_sub_le_of_norm_fderiv_within_le hf bound hx hy

theorem is_const_of_fderiv_eq_zero (hf : differentiable 𝕜 f) (hf' : ∀ x, fderiv 𝕜 f x = 0)
  (x y : E) :
  f x = f y :=
convex_univ.is_const_of_fderiv_within_eq_zero hf.differentiable_on
  (λ x _, by rw fderiv_within_univ; exact hf' x) trivial trivial

end

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `has_deriv_within`. -/
theorem convex.norm_image_sub_le_of_norm_has_deriv_within_le
  {f f' : ℝ → F} {C : ℝ} {s : set ℝ} {x y : ℝ}
  (hf : ∀ x ∈ s, has_deriv_within_at f (f' x) s x) (bound : ∀x∈s, ∥f' x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
convex.norm_image_sub_le_of_norm_has_fderiv_within_le (λ x hx, (hf x hx).has_fderiv_within_at)
(λ x hx, le_trans (by simp) (bound x hx)) hs xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `has_deriv_within` and `lipschitz_on_with`. -/
theorem convex.lipschitz_on_with_of_norm_has_deriv_within_le
  {f f' : ℝ → F} {C : ℝ} {s : set ℝ} (hs : convex s)
  (hf : ∀ x ∈ s, has_deriv_within_at f (f' x) s x) (bound : ∀x∈s, ∥f' x∥ ≤ C) :
  lipschitz_on_with (real.to_nnreal C) f s :=
convex.lipschitz_on_with_of_norm_has_fderiv_within_le (λ x hx, (hf x hx).has_fderiv_within_at)
(λ x hx, le_trans (by simp) (bound x hx)) hs

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function within
this set is bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv_within` -/
theorem convex.norm_image_sub_le_of_norm_deriv_within_le
  {f : ℝ → F} {C : ℝ} {s : set ℝ} {x y : ℝ}
  (hf : differentiable_on ℝ f s) (bound : ∀x∈s, ∥deriv_within f s x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
hs.norm_image_sub_le_of_norm_has_deriv_within_le (λ x hx, (hf x hx).has_deriv_within_at)
bound xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `deriv_within` and `lipschitz_on_with`. -/
theorem convex.lipschitz_on_with_of_norm_deriv_within_le
  {f : ℝ → F} {C : ℝ} {s : set ℝ} (hs : convex s)
  (hf : differentiable_on ℝ f s) (bound : ∀x∈s, ∥deriv_within f s x∥ ≤ C) :
  lipschitz_on_with (real.to_nnreal C) f s :=
hs.lipschitz_on_with_of_norm_has_deriv_within_le (λ x hx, (hf x hx).has_deriv_within_at) bound

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv`. -/
theorem convex.norm_image_sub_le_of_norm_deriv_le {f : ℝ → F} {C : ℝ} {s : set ℝ} {x y : ℝ}
  (hf : ∀ x ∈ s, differentiable_at ℝ f x) (bound : ∀x∈s, ∥deriv f x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
hs.norm_image_sub_le_of_norm_has_deriv_within_le
(λ x hx, (hf x hx).has_deriv_at.has_deriv_within_at) bound xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `deriv` and `lipschitz_on_with`. -/
theorem convex.lipschitz_on_with_of_norm_deriv_le {f : ℝ → F} {C : ℝ} {s : set ℝ}
  (hf : ∀ x ∈ s, differentiable_at ℝ f x) (bound : ∀x∈s, ∥deriv f x∥ ≤ C)
  (hs : convex s) : lipschitz_on_with (real.to_nnreal C) f s :=
hs.lipschitz_on_with_of_norm_has_deriv_within_le
(λ x hx, (hf x hx).has_deriv_at.has_deriv_within_at) bound

/-! ### Functions `[a, b] → ℝ`. -/

section interval

-- Declare all variables here to make sure they come in a correct order
variables (f f' : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hfc : continuous_on f (Icc a b))
  (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hfd : differentiable_on ℝ f (Ioo a b))
  (g g' : ℝ → ℝ) (hgc : continuous_on g (Icc a b)) (hgg' : ∀ x ∈ Ioo a b, has_deriv_at g (g' x) x)
  (hgd : differentiable_on ℝ g (Ioo a b))

include hab hfc hff' hgc hgg'

/-- Cauchy's **Mean Value Theorem**, `has_deriv_at` version. -/
lemma exists_ratio_has_deriv_at_eq_ratio_slope :
  ∃ c ∈ Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c :=
begin
  let h := λ x, (g b - g a) * f x - (f b - f a) * g x,
  have hI : h a = h b,
  { simp only [h], ring },
  let h' := λ x, (g b - g a) * f' x - (f b - f a) * g' x,
  have hhh' : ∀ x ∈ Ioo a b, has_deriv_at h (h' x) x,
    from λ x hx, ((hff' x hx).const_mul (g b - g a)).sub ((hgg' x hx).const_mul (f b - f a)),
  have hhc : continuous_on h (Icc a b),
    from (continuous_on_const.mul hfc).sub (continuous_on_const.mul hgc),
  rcases exists_has_deriv_at_eq_zero h h' hab hhc hI hhh' with ⟨c, cmem, hc⟩,
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩
end

omit hfc hgc

/-- Cauchy's **Mean Value Theorem**, extended `has_deriv_at` version. -/
lemma exists_ratio_has_deriv_at_eq_ratio_slope' {lfa lga lfb lgb : ℝ}
  (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hgg' : ∀ x ∈ Ioo a b, has_deriv_at g (g' x) x)
  (hfa : tendsto f (𝓝[Ioi a] a) (𝓝 lfa)) (hga : tendsto g (𝓝[Ioi a] a) (𝓝 lga))
  (hfb : tendsto f (𝓝[Iio b] b) (𝓝 lfb)) (hgb : tendsto g (𝓝[Iio b] b) (𝓝 lgb)) :
  ∃ c ∈ Ioo a b, (lgb - lga) * (f' c) = (lfb - lfa) * (g' c) :=
begin
  let h := λ x, (lgb - lga) * f x - (lfb - lfa) * g x,
  have hha : tendsto h (𝓝[Ioi a] a) (𝓝 $ lgb * lfa - lfb * lga),
  { have : tendsto h (𝓝[Ioi a] a)(𝓝 $ (lgb - lga) * lfa - (lfb - lfa) * lga) :=
      (tendsto_const_nhds.mul hfa).sub (tendsto_const_nhds.mul hga),
    convert this using 2,
    ring },
  have hhb : tendsto h (𝓝[Iio b] b) (𝓝 $ lgb * lfa - lfb * lga),
  { have : tendsto h (𝓝[Iio b] b)(𝓝 $ (lgb - lga) * lfb - (lfb - lfa) * lgb) :=
      (tendsto_const_nhds.mul hfb).sub (tendsto_const_nhds.mul hgb),
    convert this using 2,
    ring },
  let h' := λ x, (lgb - lga) * f' x - (lfb - lfa) * g' x,
  have hhh' : ∀ x ∈ Ioo a b, has_deriv_at h (h' x) x,
  { intros x hx,
    exact ((hff' x hx).const_mul _ ).sub (((hgg' x hx)).const_mul _) },
  rcases exists_has_deriv_at_eq_zero' hab hha hhb hhh' with ⟨c, cmem, hc⟩,
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩
end

include hfc

omit hgg'

/-- Lagrange's Mean Value Theorem, `has_deriv_at` version -/
lemma exists_has_deriv_at_eq_slope : ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) :=
begin
  rcases exists_ratio_has_deriv_at_eq_ratio_slope f f' hab hfc hff'
    id 1 continuous_id.continuous_on (λ x hx, has_deriv_at_id x) with ⟨c, cmem, hc⟩,
  use [c, cmem],
  simp only [_root_.id, pi.one_apply, mul_one] at hc,
  rw [← hc, mul_div_cancel_left],
  exact ne_of_gt (sub_pos.2 hab)
end

omit hff'

/-- Cauchy's Mean Value Theorem, `deriv` version. -/
lemma exists_ratio_deriv_eq_ratio_slope :
  ∃ c ∈ Ioo a b, (g b - g a) * (deriv f c) = (f b - f a) * (deriv g c) :=
exists_ratio_has_deriv_at_eq_ratio_slope f (deriv f) hab hfc
  (λ x hx, ((hfd x hx).differentiable_at $ is_open.mem_nhds is_open_Ioo hx).has_deriv_at)
  g (deriv g) hgc $
    λ x hx, ((hgd x hx).differentiable_at $ is_open.mem_nhds is_open_Ioo hx).has_deriv_at

omit hfc

/-- Cauchy's Mean Value Theorem, extended `deriv` version. -/
lemma exists_ratio_deriv_eq_ratio_slope' {lfa lga lfb lgb : ℝ}
  (hdf : differentiable_on ℝ f $ Ioo a b) (hdg : differentiable_on ℝ g $ Ioo a b)
  (hfa : tendsto f (𝓝[Ioi a] a) (𝓝 lfa)) (hga : tendsto g (𝓝[Ioi a] a) (𝓝 lga))
  (hfb : tendsto f (𝓝[Iio b] b) (𝓝 lfb)) (hgb : tendsto g (𝓝[Iio b] b) (𝓝 lgb)) :
  ∃ c ∈ Ioo a b, (lgb - lga) * (deriv f c) = (lfb - lfa) * (deriv g c) :=
exists_ratio_has_deriv_at_eq_ratio_slope' _ _ hab _ _
  (λ x hx, ((hdf x hx).differentiable_at $ Ioo_mem_nhds hx.1 hx.2).has_deriv_at)
  (λ x hx, ((hdg x hx).differentiable_at $ Ioo_mem_nhds hx.1 hx.2).has_deriv_at)
  hfa hga hfb hgb

/-- Lagrange's **Mean Value Theorem**, `deriv` version. -/
lemma exists_deriv_eq_slope : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
exists_has_deriv_at_eq_slope f (deriv f) hab hfc
  (λ x hx, ((hfd x hx).differentiable_at $ is_open.mem_nhds is_open_Ioo hx).has_deriv_at)

end interval

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C < f'`, then
`f` grows faster than `C * x` on `D`, i.e., `C * (y - x) < f y - f x` whenever `x, y ∈ D`,
`x < y`. -/
theorem convex.mul_sub_lt_image_sub_of_lt_deriv {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  {C} (hf'_gt : ∀ x ∈ interior D, C < deriv f x) :
  ∀ x y ∈ D, x < y → C * (y - x) < f y - f x :=
begin
  assume x y hx hy hxy,
  have hxyD : Icc x y ⊆ D, from hD.ord_connected.out hx hy,
  have hxyD' : Ioo x y ⊆ interior D,
    from subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩,
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x),
    from exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD'),
  have : C < (f y - f x) / (y - x), by { rw [← ha], exact hf'_gt _ (hxyD' a_mem) },
  exact (lt_div_iff (sub_pos.2 hxy)).1 this
end

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C < f'`, then `f` grows faster than
`C * x`, i.e., `C * (y - x) < f y - f x` whenever `x < y`. -/
theorem mul_sub_lt_image_sub_of_lt_deriv {f : ℝ → ℝ} (hf : differentiable ℝ f)
  {C} (hf'_gt : ∀ x, C < deriv f x) ⦃x y⦄ (hxy : x < y) :
  C * (y - x) < f y - f x :=
convex_univ.mul_sub_lt_image_sub_of_lt_deriv hf.continuous.continuous_on hf.differentiable_on
  (λ x _, hf'_gt x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C ≤ f'`, then
`f` grows at least as fast as `C * x` on `D`, i.e., `C * (y - x) ≤ f y - f x` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem convex.mul_sub_le_image_sub_of_le_deriv {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  {C} (hf'_ge : ∀ x ∈ interior D, C ≤ deriv f x) :
  ∀ x y ∈ D, x ≤ y → C * (y - x) ≤ f y - f x :=
begin
  assume x y hx hy hxy,
  cases eq_or_lt_of_le hxy with hxy' hxy', by rw [hxy', sub_self, sub_self, mul_zero],
  have hxyD : Icc x y ⊆ D, from hD.ord_connected.out hx hy,
  have hxyD' : Ioo x y ⊆ interior D,
    from subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩,
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x),
    from exists_deriv_eq_slope f hxy' (hf.mono hxyD) (hf'.mono hxyD'),
  have : C ≤ (f y - f x) / (y - x), by { rw [← ha], exact hf'_ge _ (hxyD' a_mem) },
  exact (le_div_iff (sub_pos.2 hxy')).1 this
end

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C ≤ f'`, then `f` grows at least as fast
as `C * x`, i.e., `C * (y - x) ≤ f y - f x` whenever `x ≤ y`. -/
theorem mul_sub_le_image_sub_of_le_deriv {f : ℝ → ℝ} (hf : differentiable ℝ f)
  {C} (hf'_ge : ∀ x, C ≤ deriv f x) ⦃x y⦄ (hxy : x ≤ y) :
  C * (y - x) ≤ f y - f x :=
convex_univ.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuous_on hf.differentiable_on
  (λ x _, hf'_ge x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' < C`, then
`f` grows slower than `C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x, y ∈ D`,
`x < y`. -/
theorem convex.image_sub_lt_mul_sub_of_deriv_lt {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  {C} (lt_hf' : ∀ x ∈ interior D, deriv f x < C) :
  ∀ x y ∈ D, x < y → f y - f x < C * (y - x) :=
begin
  assume x y hx hy hxy,
  have hf'_gt : ∀ x ∈ interior D, -C < deriv (λ y, -f y) x,
  { assume x hx,
    rw [deriv.neg, neg_lt_neg_iff],
    exact lt_hf' x hx },
  simpa [-neg_lt_neg_iff]
    using neg_lt_neg (hD.mul_sub_lt_image_sub_of_lt_deriv hf.neg hf'.neg hf'_gt x y hx hy hxy)
end

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' < C`, then `f` grows slower than
`C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x < y`. -/
theorem image_sub_lt_mul_sub_of_deriv_lt {f : ℝ → ℝ} (hf : differentiable ℝ f)
  {C} (lt_hf' : ∀ x, deriv f x < C) ⦃x y⦄ (hxy : x < y) :
  f y - f x < C * (y - x) :=
convex_univ.image_sub_lt_mul_sub_of_deriv_lt hf.continuous.continuous_on hf.differentiable_on
  (λ x _, lt_hf' x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' ≤ C`, then
`f` grows at most as fast as `C * x` on `D`, i.e., `f y - f x ≤ C * (y - x)` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem convex.image_sub_le_mul_sub_of_deriv_le {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  {C} (le_hf' : ∀ x ∈ interior D, deriv f x ≤ C) :
  ∀ x y ∈ D, x ≤ y → f y - f x ≤ C * (y - x) :=
begin
  assume x y hx hy hxy,
  have hf'_ge : ∀ x ∈ interior D, -C ≤ deriv (λ y, -f y) x,
  { assume x hx,
    rw [deriv.neg, neg_le_neg_iff],
    exact le_hf' x hx },
  simpa [-neg_le_neg_iff]
    using neg_le_neg (hD.mul_sub_le_image_sub_of_le_deriv hf.neg hf'.neg hf'_ge x y hx hy hxy)
end

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' ≤ C`, then `f` grows at most as fast
as `C * x`, i.e., `f y - f x ≤ C * (y - x)` whenever `x ≤ y`. -/
theorem image_sub_le_mul_sub_of_deriv_le {f : ℝ → ℝ} (hf : differentiable ℝ f)
  {C} (le_hf' : ∀ x, deriv f x ≤ C) ⦃x y⦄ (hxy : x ≤ y) :
  f y - f x ≤ C * (y - x) :=
convex_univ.image_sub_le_mul_sub_of_deriv_le hf.continuous.continuous_on hf.differentiable_on
  (λ x _, le_hf' x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is positive, then
`f` is a strictly monotonically increasing function on `D`. -/
theorem convex.strict_mono_of_deriv_pos {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_pos : ∀ x ∈ interior D, 0 < deriv f x) :
  ∀ x y ∈ D, x < y → f x < f y :=
by simpa only [zero_mul, sub_pos] using hD.mul_sub_lt_image_sub_of_lt_deriv hf hf' hf'_pos

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is positive, then
`f` is a strictly monotonically increasing function. -/
theorem strict_mono_of_deriv_pos {f : ℝ → ℝ} (hf : differentiable ℝ f)
  (hf'_pos : ∀ x, 0 < deriv f x) :
  strict_mono f :=
λ x y hxy, convex_univ.strict_mono_of_deriv_pos hf.continuous.continuous_on hf.differentiable_on
  (λ x _, hf'_pos x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonnegative, then
`f` is a monotonically increasing function on `D`. -/
theorem convex.mono_of_deriv_nonneg {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_nonneg : ∀ x ∈ interior D, 0 ≤ deriv f x) :
  ∀ x y ∈ D, x ≤ y → f x ≤ f y :=
by simpa only [zero_mul, sub_nonneg] using hD.mul_sub_le_image_sub_of_le_deriv hf hf' hf'_nonneg

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonnegative, then
`f` is a monotonically increasing function. -/
theorem mono_of_deriv_nonneg {f : ℝ → ℝ} (hf : differentiable ℝ f) (hf' : ∀ x, 0 ≤ deriv f x) :
  monotone f :=
λ x y hxy, convex_univ.mono_of_deriv_nonneg hf.continuous.continuous_on hf.differentiable_on
  (λ x _, hf' x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is negative, then
`f` is a strictly monotonically decreasing function on `D`. -/
theorem convex.strict_antimono_of_deriv_neg {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_neg : ∀ x ∈ interior D, deriv f x < 0) :
  ∀ x y ∈ D, x < y → f y < f x :=
by simpa only [zero_mul, sub_lt_zero] using hD.image_sub_lt_mul_sub_of_deriv_lt hf hf' hf'_neg

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is negative, then
`f` is a strictly monotonically decreasing function. -/
theorem strict_antimono_of_deriv_neg {f : ℝ → ℝ} (hf : differentiable ℝ f)
  (hf' : ∀ x, deriv f x < 0) :
  ∀ ⦃x y⦄, x < y → f y < f x :=
λ x y hxy, convex_univ.strict_antimono_of_deriv_neg hf.continuous.continuous_on hf.differentiable_on
  (λ x _, hf' x) x y trivial trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonpositive, then
`f` is a monotonically decreasing function on `D`. -/
theorem convex.antimono_of_deriv_nonpos {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_nonpos : ∀ x ∈ interior D, deriv f x ≤ 0) :
  ∀ x y ∈ D, x ≤ y → f y ≤ f x :=
by simpa only [zero_mul, sub_nonpos] using hD.image_sub_le_mul_sub_of_deriv_le hf hf' hf'_nonpos

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonpositive, then
`f` is a monotonically decreasing function. -/
theorem antimono_of_deriv_nonpos {f : ℝ → ℝ} (hf : differentiable ℝ f) (hf' : ∀ x, deriv f x ≤ 0) :
  ∀ ⦃x y⦄, x ≤ y → f y ≤ f x :=
λ x y hxy, convex_univ.antimono_of_deriv_nonpos hf.continuous.continuous_on hf.differentiable_on
  (λ x _, hf' x) x y trivial trivial hxy

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is monotone on the interior, then `f` is convex on `D`. -/
theorem convex_on_of_deriv_mono {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_mono : ∀ x y ∈ interior D, x ≤ y → deriv f x ≤ deriv f y) :
  convex_on D f :=
convex_on_real_of_slope_mono_adjacent hD
begin
  intros x y z hx hz hxy hyz,
  -- First we prove some trivial inclusions
  have hxzD : Icc x z ⊆ D, from hD.ord_connected.out hx hz,
  have hxyD : Icc x y ⊆ D, from subset.trans (Icc_subset_Icc_right $ le_of_lt hyz) hxzD,
  have hxyD' : Ioo x y ⊆ interior D,
    from subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩,
  have hyzD : Icc y z ⊆ D, from subset.trans (Icc_subset_Icc_left $ le_of_lt hxy) hxzD,
  have hyzD' : Ioo y z ⊆ interior D,
    from subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hyzD⟩,
  -- Then we apply MVT to both `[x, y]` and `[y, z]`
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x),
    from exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD'),
  obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b = (f z - f y) / (z - y),
    from exists_deriv_eq_slope f hyz (hf.mono hyzD) (hf'.mono hyzD'),
  rw [← ha, ← hb],
  exact hf'_mono a b (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (le_of_lt $ lt_trans hay hyb)
end

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is antimonotone on the interior, then `f` is concave on `D`. -/
theorem concave_on_of_deriv_antimono {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_mono : ∀ x y ∈ interior D, x ≤ y → deriv f y ≤ deriv f x) :
  concave_on D f :=
begin
  have : ∀ x y ∈ interior D, x ≤ y → deriv (-f) x ≤ deriv (-f) y,
  { intros x y hx hy hxy,
    convert neg_le_neg (hf'_mono x y hx hy hxy);
    convert deriv.neg },
  exact (neg_convex_on_iff D f).mp (convex_on_of_deriv_mono hD
    hf.neg hf'.neg this),
end

/-- If a function `f` is differentiable and `f'` is monotone on `ℝ` then `f` is convex. -/
theorem convex_on_univ_of_deriv_mono {f : ℝ → ℝ} (hf : differentiable ℝ f)
  (hf'_mono : monotone (deriv f)) : convex_on univ f :=
convex_on_of_deriv_mono convex_univ hf.continuous.continuous_on hf.differentiable_on
  (λ x y _ _ h, hf'_mono h)

/-- If a function `f` is differentiable and `f'` is antimonotone on `ℝ` then `f` is concave. -/
theorem concave_on_univ_of_deriv_antimono {f : ℝ → ℝ} (hf : differentiable ℝ f)
  (hf'_antimono : ∀⦃a b⦄, a ≤ b → (deriv f) b ≤ (deriv f) a) : concave_on univ f :=
concave_on_of_deriv_antimono convex_univ hf.continuous.continuous_on hf.differentiable_on
  (λ x y _ _ h, hf'_antimono h)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`. -/
theorem convex_on_of_deriv2_nonneg {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'' : differentiable_on ℝ (deriv f) (interior D))
  (hf''_nonneg : ∀ x ∈ interior D, 0 ≤ (deriv^[2] f x)) :
  convex_on D f :=
convex_on_of_deriv_mono hD hf hf' $
assume x y hx hy hxy,
hD.interior.mono_of_deriv_nonneg hf''.continuous_on (by rwa [interior_interior])
  (by rwa [interior_interior]) _ _ hx hy hxy

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`. -/
theorem concave_on_of_deriv2_nonpos {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'' : differentiable_on ℝ (deriv f) (interior D))
  (hf''_nonpos : ∀ x ∈ interior D, (deriv^[2] f x) ≤ 0) :
  concave_on D f :=
concave_on_of_deriv_antimono hD hf hf' $
assume x y hx hy hxy,
hD.interior.antimono_of_deriv_nonpos hf''.continuous_on (by rwa [interior_interior])
  (by rwa [interior_interior]) _ _ hx hy hxy

/-- If a function `f` is twice differentiable on a open convex set `D ⊆ ℝ` and
`f''` is nonnegative on `D`, then `f` is convex on `D`. -/
theorem convex_on_open_of_deriv2_nonneg {D : set ℝ} (hD : convex D) (hD₂ : is_open D) {f : ℝ → ℝ}
  (hf' : differentiable_on ℝ f D) (hf'' : differentiable_on ℝ (deriv f) D)
  (hf''_nonneg : ∀ x ∈ D, 0 ≤ (deriv^[2] f x)) : convex_on D f :=
convex_on_of_deriv2_nonneg hD hf'.continuous_on (by simpa [hD₂.interior_eq] using hf')
  (by simpa [hD₂.interior_eq] using hf'') (by simpa [hD₂.interior_eq] using hf''_nonneg)

/-- If a function `f` is twice differentiable on a open convex set `D ⊆ ℝ` and
`f''` is nonpositive on `D`, then `f` is concave on `D`. -/
theorem concave_on_open_of_deriv2_nonpos {D : set ℝ} (hD : convex D) (hD₂ : is_open D) {f : ℝ → ℝ}
  (hf' : differentiable_on ℝ f D) (hf'' : differentiable_on ℝ (deriv f) D)
  (hf''_nonpos : ∀ x ∈ D, (deriv^[2] f x) ≤ 0) : concave_on D f :=
concave_on_of_deriv2_nonpos hD hf'.continuous_on (by simpa [hD₂.interior_eq] using hf')
  (by simpa [hD₂.interior_eq] using hf'') (by simpa [hD₂.interior_eq] using hf''_nonpos)

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonnegative on `ℝ`,
then `f` is convex on `ℝ`. -/
theorem convex_on_univ_of_deriv2_nonneg {f : ℝ → ℝ} (hf' : differentiable ℝ f)
  (hf'' : differentiable ℝ (deriv f)) (hf''_nonneg : ∀ x, 0 ≤ (deriv^[2] f x)) :
  convex_on univ f :=
convex_on_open_of_deriv2_nonneg convex_univ is_open_univ hf'.differentiable_on
  hf''.differentiable_on (λ x _, hf''_nonneg x)

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonpositive on `ℝ`,
then `f` is concave on `ℝ`. -/
theorem concave_on_univ_of_deriv2_nonpos {f : ℝ → ℝ} (hf' : differentiable ℝ f)
  (hf'' : differentiable ℝ (deriv f)) (hf''_nonpos : ∀ x, (deriv^[2] f x) ≤ 0) :
  concave_on univ f :=
concave_on_open_of_deriv2_nonpos convex_univ is_open_univ hf'.differentiable_on
  hf''.differentiable_on (λ x _, hf''_nonpos x)

/-! ### Functions `f : E → ℝ` -/

/-- Lagrange's Mean Value Theorem, applied to convex domains. -/
theorem domain_mvt
  {f : E → ℝ} {s : set E} {x y : E} {f' : E → (E →L[ℝ] ℝ)}
  (hf : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x) (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) :
  ∃ z ∈ segment x y, f y - f x = f' z (y - x) :=
begin
  have hIccIoo := @Ioo_subset_Icc_self ℝ _ 0 1,
-- parametrize segment
  set g : ℝ → E := λ t, x + t • (y - x),
  have hseg : ∀ t ∈ Icc (0:ℝ) 1, g t ∈ segment x y,
  { rw segment_eq_image',
    simp only [mem_image, and_imp, add_right_inj],
    intros t ht, exact ⟨t, ht, rfl⟩ },
  have hseg' : Icc 0 1 ⊆ g ⁻¹' s,
  { rw ← image_subset_iff, unfold image, change ∀ _, _,
    intros z Hz, rw mem_set_of_eq at Hz, rcases Hz with ⟨t, Ht, hgt⟩,
    rw ← hgt, exact hs.segment_subset xs ys (hseg t Ht) },
-- derivative of pullback of f under parametrization
  have hfg: ∀ t ∈ Icc (0:ℝ) 1, has_deriv_within_at (f ∘ g)
    ((f' (g t) : E → ℝ) (y-x)) (Icc (0:ℝ) 1) t,
  { intros t Ht,
    have hg : has_deriv_at g (y-x) t,
    { have := ((has_deriv_at_id t).smul_const (y - x)).const_add x,
      rwa one_smul at this },
    exact (hf (g t) $ hseg' Ht).comp_has_deriv_within_at _ hg.has_deriv_within_at hseg' },
-- apply 1-variable mean value theorem to pullback
  have hMVT : ∃ (t ∈ Ioo (0:ℝ) 1), ((f' (g t) : E → ℝ) (y-x)) = (f (g 1) - f (g 0)) / (1 - 0),
  { refine exists_has_deriv_at_eq_slope (f ∘ g) _ (by norm_num) _ _,
    { unfold continuous_on,
      exact λ t Ht, (hfg t Ht).continuous_within_at },
    { refine λ t Ht, (hfg t $ hIccIoo Ht).has_deriv_at _,
      refine _root_.mem_nhds_iff.mpr _,
      use (Ioo (0:ℝ) 1),
      refine ⟨hIccIoo, _, Ht⟩,
      simp [real.Ioo_eq_ball, is_open_ball] } },
-- reinterpret on domain
  rcases hMVT with ⟨t, Ht, hMVT'⟩,
  use g t, refine ⟨hseg t $ hIccIoo Ht, _⟩,
  simp [g, hMVT'],
end


section is_R_or_C

/-!
### Vector-valued functions `f : E → F`.  Strict differentiability.

A `C^1` function is strictly differentiable, when the field is `ℝ` or `ℂ`. This follows from the
mean value inequality on balls, which is a particular case of the above results after restricting
the scalars to `ℝ`. Note that it does not make sense to talk of a convex set over `ℂ`, but balls
make sense and are enough. Many formulations of the mean value inequality could be generalized to
balls over `ℝ` or `ℂ`. For now, we only include the ones that we need.
-/

variables {𝕜 : Type*} [is_R_or_C 𝕜] {G : Type*} [normed_group G] [normed_space 𝕜 G]
  {H : Type*} [normed_group H] [normed_space 𝕜 H] {f : G → H} {f' : G → G →L[𝕜] H} {x : G}

/-- Over the reals or the complexes, a continuously differentiable function is strictly
differentiable. -/
lemma has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at
  (hder : ∀ᶠ y in 𝓝 x, has_fderiv_at f (f' y) y) (hcont : continuous_at f' x) :
  has_strict_fderiv_at f (f' x) x :=
begin
-- turn little-o definition of strict_fderiv into an epsilon-delta statement
  refine is_o_iff.mpr (λ c hc, metric.eventually_nhds_iff_ball.mpr _),
-- the correct ε is the modulus of continuity of f'
  rcases metric.mem_nhds_iff.mp (inter_mem_sets hder (hcont $ ball_mem_nhds _ hc)) with ⟨ε, ε0, hε⟩,
  refine ⟨ε, ε0, _⟩,
-- simplify formulas involving the product E × E
  rintros ⟨a, b⟩ h,
  rw [← ball_prod_same, prod_mk_mem_set_prod_eq] at h,
-- exploit the choice of ε as the modulus of continuity of f'
  have hf' : ∀ x' ∈ ball x ε, ∥f' x' - f' x∥ ≤ c,
  { intros x' H', rw ← dist_eq_norm, exact le_of_lt (hε H').2 },
-- apply mean value theorem
  letI : normed_space ℝ G := restrict_scalars.normed_space ℝ 𝕜 G,
  letI : is_scalar_tower ℝ 𝕜 G := restrict_scalars.is_scalar_tower _ _ _,
  refine (convex_ball _ _).norm_image_sub_le_of_norm_has_fderiv_within_le' _ hf' h.2 h.1,
  exact λ y hy, (hε hy).1.has_fderiv_within_at
end

/-- Over the reals or the complexes, a continuously differentiable function is strictly
differentiable. -/
lemma has_strict_deriv_at_of_has_deriv_at_of_continuous_at {f f' : 𝕜 → G} {x : 𝕜}
  (hder : ∀ᶠ y in 𝓝 x, has_deriv_at f (f' y) y) (hcont : continuous_at f' x) :
  has_strict_deriv_at f (f' x) x :=
has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at (hder.mono (λ y hy, hy.has_fderiv_at)) $
  (smul_rightL 𝕜 _ _ 1).continuous.continuous_at.comp hcont

end is_R_or_C
