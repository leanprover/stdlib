/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.local_extr
import topology.algebra.ordered.extend_from
import analysis.calculus.deriv
import topology.algebra.polynomial

/-!
# Local extrema of smooth functions

## Main definitions

In a real normed space `E` we define `pos_tangent_cone_at (s : set E) (x : E)`.
This would be the same as `tangent_cone_at ℝ≥0 s x` if we had a theory of normed semifields.
This set is used in the proof of Fermat's Theorem (see below), and can be used to formalize
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) and/or
[Karush–Kuhn–Tucker conditions](https://en.wikipedia.org/wiki/Karush–Kuhn–Tucker_conditions).

## Main statements

For each theorem name listed below,
we also prove similar theorems for `min`, `extr` (if applicable)`,
and `(f)deriv` instead of `has_fderiv`.

* `is_local_max_on.has_fderiv_within_at_nonpos` : `f' y ≤ 0` whenever `a` is a local maximum
  of `f` on `s`, `f` has derivative `f'` at `a` within `s`, and `y` belongs to the positive tangent
  cone of `s` at `a`.

* `is_local_max_on.has_fderiv_within_at_eq_zero` : In the settings of the previous theorem, if both
  `y` and `-y` belong to the positive tangent cone, then `f' y = 0`.

* `is_local_max.has_fderiv_at_eq_zero` :
  [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points)),
  the derivative of a differentiable function at a local extremum point equals zero.

* `exists_has_deriv_at_eq_zero` :
  [Rolle's Theorem](https://en.wikipedia.org/wiki/Rolle's_theorem): given a function `f` continuous
  on `[a, b]` and differentiable on `(a, b)`, there exists `c ∈ (a, b)` such that `f' c = 0`.

## Implementation notes

For each mathematical fact we prove several versions of its formalization:

* for maxima and minima;
* using `has_fderiv*`/`has_deriv*` or `fderiv*`/`deriv*`.

For the `fderiv*`/`deriv*` versions we omit the differentiability condition whenever it is possible
due to the fact that `fderiv` and `deriv` are defined to be zero for non-differentiable functions.

## References

* [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points));
* [Rolle's Theorem](https://en.wikipedia.org/wiki/Rolle's_theorem);
* [Tangent cone](https://en.wikipedia.org/wiki/Tangent_cone);

## Tags

local extremum, Fermat's Theorem, Rolle's Theorem
-/

universes u v

open filter set
open_locale topological_space classical

section module

variables {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E}
  {f' : E →L[ℝ] ℝ}

/-- "Positive" tangent cone to `s` at `x`; the only difference from `tangent_cone_at`
is that we require `c n → ∞` instead of `∥c n∥ → ∞`. One can think about `pos_tangent_cone_at`
as `tangent_cone_at nnreal` but we have no theory of normed semifields yet. -/
def pos_tangent_cone_at (s : set E) (x : E) : set E :=
{y : E | ∃(c : ℕ → ℝ) (d : ℕ → E), (∀ᶠ n in at_top, x + d n ∈ s) ∧
  (tendsto c at_top at_top) ∧ (tendsto (λn, c n • d n) at_top (𝓝 y))}

lemma pos_tangent_cone_at_mono : monotone (λ s, pos_tangent_cone_at s a) :=
begin
  rintros s t hst y ⟨c, d, hd, hc, hcd⟩,
  exact ⟨c, d, mem_sets_of_superset hd $ λ h hn, hst hn, hc, hcd⟩
end

lemma mem_pos_tangent_cone_at_of_segment_subset {s : set E} {x y : E} (h : segment x y ⊆ s) :
  y - x ∈ pos_tangent_cone_at s x :=
begin
  let c := λn:ℕ, (2:ℝ)^n,
  let d := λn:ℕ, (c n)⁻¹ • (y-x),
  refine ⟨c, d, filter.univ_mem_sets' (λn, h _),
    tendsto_pow_at_top_at_top_of_one_lt one_lt_two, _⟩,
  show x + d n ∈ segment x y,
  { rw segment_eq_image',
    refine ⟨(c n)⁻¹, ⟨_, _⟩, rfl⟩,
    exacts [inv_nonneg.2 (pow_nonneg zero_le_two _),
      inv_le_one (one_le_pow_of_one_le one_le_two _)] },
  show tendsto (λ n, c n • d n) at_top (𝓝 (y - x)),
  { convert tendsto_const_nhds, ext n,
    simp only [d, smul_smul],
    rw [mul_inv_cancel, one_smul],
    exact pow_ne_zero _ two_ne_zero }
end

lemma mem_pos_tangent_cone_at_of_segment_subset' {s : set E} {x y : E} (h : segment x (x + y) ⊆ s) :
  y ∈ pos_tangent_cone_at s x :=
by simpa only [add_sub_cancel'] using mem_pos_tangent_cone_at_of_segment_subset h

lemma pos_tangent_cone_at_univ : pos_tangent_cone_at univ a = univ :=
eq_univ_of_forall $ λ x, mem_pos_tangent_cone_at_of_segment_subset' (subset_univ _)

/-- If `f` has a local max on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
lemma is_local_max_on.has_fderiv_within_at_nonpos {s : set E} (h : is_local_max_on f s a)
  (hf : has_fderiv_within_at f f' s a) {y} (hy : y ∈ pos_tangent_cone_at s a) :
  f' y ≤ 0 :=
begin
  rcases hy with ⟨c, d, hd, hc, hcd⟩,
  have hc' : tendsto (λ n, ∥c n∥) at_top at_top,
    from tendsto_at_top_mono (λ n, le_abs_self _) hc,
  refine le_of_tendsto (hf.lim at_top hd hc' hcd) _,
  replace hd : tendsto (λ n, a + d n) at_top (𝓝[s] (a + 0)),
  from tendsto_inf.2 ⟨tendsto_const_nhds.add (tangent_cone_at.lim_zero _ hc' hcd),
    by rwa tendsto_principal⟩,
  rw [add_zero] at hd,
  replace h : ∀ᶠ n in at_top, f (a + d n) ≤ f a, from mem_map.1 (hd h),
  replace hc : ∀ᶠ n in at_top, 0 ≤ c n, from mem_map.1 (hc (mem_at_top (0:ℝ))),
  filter_upwards [h, hc],
  simp only [smul_eq_mul, mem_preimage, subset_def],
  assume n hnf hn,
  exact mul_nonpos_of_nonneg_of_nonpos hn (sub_nonpos.2 hnf)
end

/-- If `f` has a local max on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `f' y ≤ 0`. -/
lemma is_local_max_on.fderiv_within_nonpos {s : set E} (h : is_local_max_on f s a)
  {y} (hy : y ∈ pos_tangent_cone_at s a) :
  (fderiv_within ℝ f s a : E → ℝ) y ≤ 0 :=
if hf : differentiable_within_at ℝ f s a
then h.has_fderiv_within_at_nonpos hf.has_fderiv_within_at hy
else by { rw fderiv_within_zero_of_not_differentiable_within_at hf, refl }

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
lemma is_local_max_on.has_fderiv_within_at_eq_zero {s : set E} (h : is_local_max_on f s a)
  (hf : has_fderiv_within_at f f' s a) {y} (hy : y ∈ pos_tangent_cone_at s a)
  (hy' : -y ∈ pos_tangent_cone_at s a) :
  f' y = 0 :=
le_antisymm (h.has_fderiv_within_at_nonpos hf hy) $
  by simpa using h.has_fderiv_within_at_nonpos hf hy'

/-- If `f` has a local max on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
lemma is_local_max_on.fderiv_within_eq_zero {s : set E} (h : is_local_max_on f s a)
  {y} (hy : y ∈ pos_tangent_cone_at s a) (hy' : -y ∈ pos_tangent_cone_at s a) :
  (fderiv_within ℝ f s a : E → ℝ) y = 0 :=
if hf : differentiable_within_at ℝ f s a
then h.has_fderiv_within_at_eq_zero hf.has_fderiv_within_at hy hy'
else by { rw fderiv_within_zero_of_not_differentiable_within_at hf, refl }

/-- If `f` has a local min on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `0 ≤ f' y`. -/
lemma is_local_min_on.has_fderiv_within_at_nonneg {s : set E} (h : is_local_min_on f s a)
  (hf : has_fderiv_within_at f f' s a) {y} (hy : y ∈ pos_tangent_cone_at s a) :
  0 ≤ f' y :=
by simpa using h.neg.has_fderiv_within_at_nonpos hf.neg hy

/-- If `f` has a local min on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `0 ≤ f' y`. -/
lemma is_local_min_on.fderiv_within_nonneg {s : set E} (h : is_local_min_on f s a)
  {y} (hy : y ∈ pos_tangent_cone_at s a) :
  (0:ℝ) ≤ (fderiv_within ℝ f s a : E → ℝ) y :=
if hf : differentiable_within_at ℝ f s a
then h.has_fderiv_within_at_nonneg hf.has_fderiv_within_at hy
else by { rw [fderiv_within_zero_of_not_differentiable_within_at hf], refl }

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
lemma is_local_min_on.has_fderiv_within_at_eq_zero {s : set E} (h : is_local_min_on f s a)
  (hf : has_fderiv_within_at f f' s a) {y} (hy : y ∈ pos_tangent_cone_at s a)
  (hy' : -y ∈ pos_tangent_cone_at s a) :
  f' y = 0 :=
by simpa using h.neg.has_fderiv_within_at_eq_zero hf.neg hy hy'

/-- If `f` has a local min on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
lemma is_local_min_on.fderiv_within_eq_zero {s : set E} (h : is_local_min_on f s a)
  {y} (hy : y ∈ pos_tangent_cone_at s a) (hy' : -y ∈ pos_tangent_cone_at s a) :
  (fderiv_within ℝ f s a : E → ℝ) y = 0 :=
if hf : differentiable_within_at ℝ f s a
then h.has_fderiv_within_at_eq_zero hf.has_fderiv_within_at hy hy'
else by { rw fderiv_within_zero_of_not_differentiable_within_at hf, refl }

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
lemma is_local_min.has_fderiv_at_eq_zero (h : is_local_min f a) (hf : has_fderiv_at f f' a) :
  f' = 0 :=
begin
  ext y,
  apply (h.on univ).has_fderiv_within_at_eq_zero hf.has_fderiv_within_at;
    rw pos_tangent_cone_at_univ; apply mem_univ
end

/-- Fermat's Theorem: the derivative of a function at a local minimum equals zero. -/
lemma is_local_min.fderiv_eq_zero (h : is_local_min f a) : fderiv ℝ f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_fderiv_at_eq_zero hf.has_fderiv_at
else fderiv_zero_of_not_differentiable_at hf

/-- Fermat's Theorem: the derivative of a function at a local maximum equals zero. -/
lemma is_local_max.has_fderiv_at_eq_zero (h : is_local_max f a) (hf : has_fderiv_at f f' a) :
  f' = 0 :=
neg_eq_zero.1 $ h.neg.has_fderiv_at_eq_zero hf.neg

/-- Fermat's Theorem: the derivative of a function at a local maximum equals zero. -/
lemma is_local_max.fderiv_eq_zero (h : is_local_max f a) : fderiv ℝ f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_fderiv_at_eq_zero hf.has_fderiv_at
else fderiv_zero_of_not_differentiable_at hf

/-- Fermat's Theorem: the derivative of a function at a local extremum equals zero. -/
lemma is_local_extr.has_fderiv_at_eq_zero (h : is_local_extr f a) :
  has_fderiv_at f f' a → f' = 0 :=
h.elim is_local_min.has_fderiv_at_eq_zero is_local_max.has_fderiv_at_eq_zero

/-- Fermat's Theorem: the derivative of a function at a local extremum equals zero. -/
lemma is_local_extr.fderiv_eq_zero (h : is_local_extr f a) : fderiv ℝ f a = 0 :=
h.elim is_local_min.fderiv_eq_zero is_local_max.fderiv_eq_zero

end module

section real

variables {f : ℝ → ℝ} {f' : ℝ} {a b : ℝ}

/-- Fermat's Theorem: the derivative of a function at a local minimum equals zero. -/
lemma is_local_min.has_deriv_at_eq_zero (h : is_local_min f a) (hf : has_deriv_at f f' a) :
  f' = 0 :=
by simpa using continuous_linear_map.ext_iff.1
  (h.has_fderiv_at_eq_zero (has_deriv_at_iff_has_fderiv_at.1 hf)) 1

/-- Fermat's Theorem: the derivative of a function at a local minimum equals zero. -/
lemma is_local_min.deriv_eq_zero (h : is_local_min f a) : deriv f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_deriv_at_eq_zero hf.has_deriv_at
else deriv_zero_of_not_differentiable_at hf

/-- Fermat's Theorem: the derivative of a function at a local maximum equals zero. -/
lemma is_local_max.has_deriv_at_eq_zero (h : is_local_max f a) (hf : has_deriv_at f f' a) :
  f' = 0 :=
neg_eq_zero.1 $ h.neg.has_deriv_at_eq_zero hf.neg

/-- Fermat's Theorem: the derivative of a function at a local maximum equals zero. -/
lemma is_local_max.deriv_eq_zero (h : is_local_max f a) : deriv f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_deriv_at_eq_zero hf.has_deriv_at
else deriv_zero_of_not_differentiable_at hf

/-- Fermat's Theorem: the derivative of a function at a local extremum equals zero. -/
lemma is_local_extr.has_deriv_at_eq_zero (h : is_local_extr f a) :
  has_deriv_at f f' a → f' = 0 :=
h.elim is_local_min.has_deriv_at_eq_zero is_local_max.has_deriv_at_eq_zero

/-- Fermat's Theorem: the derivative of a function at a local extremum equals zero. -/
lemma is_local_extr.deriv_eq_zero (h : is_local_extr f a) : deriv f a = 0 :=
h.elim is_local_min.deriv_eq_zero is_local_max.deriv_eq_zero

end real

section Rolle

variables (f f' : ℝ → ℝ) {a b : ℝ}

/-- A continuous function on a closed interval with `f a = f b` takes either its maximum
or its minimum value at a point in the interior of the interval. -/
lemma exists_Ioo_extr_on_Icc (hab : a < b) (hfc : continuous_on f (Icc a b)) (hfI : f a = f b) :
  ∃ c ∈ Ioo a b, is_extr_on f (Icc a b) c :=
begin
  have ne : (Icc a b).nonempty, from nonempty_Icc.2 (le_of_lt hab),
  -- Consider absolute min and max points
  obtain ⟨c, cmem, cle⟩ : ∃ c ∈ Icc a b, ∀ x ∈ Icc a b, f c ≤ f x,
    from is_compact_Icc.exists_forall_le ne hfc,
  obtain ⟨C, Cmem, Cge⟩ : ∃ C ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f C,
    from is_compact_Icc.exists_forall_ge ne hfc,
  by_cases hc : f c = f a,
  { by_cases hC : f C = f a,
    { have : ∀ x ∈ Icc a b, f x = f a,
        from λ x hx, le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx),
      -- `f` is a constant, so we can take any point in `Ioo a b`
      rcases exists_between hab with ⟨c', hc'⟩,
      refine ⟨c', hc', or.inl _⟩,
      assume x hx,
      rw [mem_set_of_eq, this x hx, ← hC],
      exact Cge c' ⟨le_of_lt hc'.1, le_of_lt hc'.2⟩ },
    { refine ⟨C, ⟨lt_of_le_of_ne Cmem.1 $ mt _ hC, lt_of_le_of_ne Cmem.2 $ mt _ hC⟩, or.inr Cge⟩,
      exacts [λ h, by rw h, λ h, by rw [h, hfI]] } },
  { refine ⟨c, ⟨lt_of_le_of_ne cmem.1 $ mt _ hc, lt_of_le_of_ne cmem.2 $ mt _ hc⟩, or.inl cle⟩,
      exacts [λ h, by rw h, λ h, by rw [h, hfI]] }
end

/-- A continuous function on a closed interval with `f a = f b` has a local extremum at some
point of the corresponding open interval. -/
lemma exists_local_extr_Ioo (hab : a < b) (hfc : continuous_on f (Icc a b)) (hfI : f a = f b) :
  ∃ c ∈ Ioo a b, is_local_extr f c :=
let ⟨c, cmem, hc⟩ := exists_Ioo_extr_on_Icc f hab hfc hfI
in ⟨c, cmem, hc.is_local_extr $ Icc_mem_nhds cmem.1 cmem.2⟩

/-- **Rolle's Theorem** `has_deriv_at` version -/
lemma exists_has_deriv_at_eq_zero (hab : a < b) (hfc : continuous_on f (Icc a b)) (hfI : f a = f b)
  (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) :
  ∃ c ∈ Ioo a b, f' c = 0 :=
let ⟨c, cmem, hc⟩ := exists_local_extr_Ioo f hab hfc hfI in
  ⟨c, cmem, hc.has_deriv_at_eq_zero $ hff' c cmem⟩

/-- **Rolle's Theorem** `deriv` version -/
lemma exists_deriv_eq_zero (hab : a < b) (hfc : continuous_on f (Icc a b)) (hfI : f a = f b) :
  ∃ c ∈ Ioo a b, deriv f c = 0 :=
let ⟨c, cmem, hc⟩ := exists_local_extr_Ioo f hab hfc hfI in
  ⟨c, cmem, hc.deriv_eq_zero⟩

variables {f f'} {l : ℝ}

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has derivative `f'`
on `(a, b)` and has the same limit `l` at `𝓝[Ioi a] a` and `𝓝[Iio b] b`, then `f' c = 0`
for some `c ∈ (a, b)`.  -/
lemma exists_has_deriv_at_eq_zero' (hab : a < b)
  (hfa : tendsto f (𝓝[Ioi a] a) (𝓝 l)) (hfb : tendsto f (𝓝[Iio b] b) (𝓝 l))
  (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) :
  ∃ c ∈ Ioo a b, f' c = 0 :=
begin
  have : continuous_on f (Ioo a b) := λ x hx, (hff' x hx).continuous_at.continuous_within_at,
  have hcont := continuous_on_Icc_extend_from_Ioo hab this hfa hfb,
  obtain ⟨c, hc, hcextr⟩ : ∃ c ∈ Ioo a b, is_local_extr (extend_from (Ioo a b) f) c,
  { apply exists_local_extr_Ioo _ hab hcont,
    rw eq_lim_at_right_extend_from_Ioo hab hfb,
    exact eq_lim_at_left_extend_from_Ioo hab hfa },
  use [c, hc],
  apply (hcextr.congr _).has_deriv_at_eq_zero (hff' c hc),
  rw eventually_eq_iff_exists_mem,
  exact ⟨Ioo a b, Ioo_mem_nhds hc.1 hc.2, extend_from_extends this⟩
end

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has the same limit
`l` at `𝓝[Ioi a] a` and `𝓝[Iio b] b`, then `deriv f c = 0` for some `c ∈ (a, b)`. This version
does not require differentiability of `f` because we define `deriv f c = 0` whenever `f` is not
differentiable at `c`. -/
lemma exists_deriv_eq_zero' (hab : a < b)
  (hfa : tendsto f (𝓝[Ioi a] a) (𝓝 l)) (hfb : tendsto f (𝓝[Iio b] b) (𝓝 l)) :
  ∃ c ∈ Ioo a b, deriv f c = 0 :=
classical.by_cases
  (assume h : ∀ x ∈ Ioo a b, differentiable_at ℝ f x,
    show ∃ c ∈ Ioo a b, deriv f c = 0,
      from exists_has_deriv_at_eq_zero' hab hfa hfb (λ x hx, (h x hx).has_deriv_at))
  (assume h : ¬∀ x ∈ Ioo a b, differentiable_at ℝ f x,
    have h : ∃ x, x ∈ Ioo a b ∧ ¬differentiable_at ℝ f x, by { push_neg at h, exact h },
      let ⟨c, hc, hcdiff⟩ := h in ⟨c, hc, deriv_zero_of_not_differentiable_at hcdiff⟩)

end Rolle

namespace polynomial

lemma card_root_set_le_derivative {F : Type*} [field F] [algebra F ℝ] (p : polynomial F) :
  fintype.card (p.root_set ℝ) ≤ fintype.card (p.derivative.root_set ℝ) + 1 :=
begin
  haveI : char_zero F :=
    (ring_hom.char_zero_iff (algebra_map F ℝ).injective).mpr (by apply_instance),
  by_cases hp : p = 0,
  { simp_rw [hp, derivative_zero, root_set_zero, set.empty_card', zero_le_one] },
  by_cases hp' : p.derivative = 0,
  { rw eq_C_of_nat_degree_eq_zero (nat_degree_eq_zero_of_derivative_eq_zero hp'),
    simp_rw [root_set_C, set.empty_card', zero_le] },
  simp_rw [root_set_def, finset.coe_sort_coe, fintype.card_coe],
  refine finset.card_le_of_interleaved (λ x y hx hy hxy, _),
  rw [←finset.mem_coe, ←root_set_def, mem_root_set hp] at hx hy,
  obtain ⟨z, hz1, hz2⟩ := exists_deriv_eq_zero (λ x : ℝ, aeval x p) hxy
    p.continuous_aeval.continuous_on (hx.trans hy.symm),
  refine ⟨z, _, hz1⟩,
  rw [←finset.mem_coe, ←root_set_def, mem_root_set hp', ←hz2],
  simp_rw [aeval_def, ←eval_map, polynomial.deriv, derivative_map],
end

end polynomial
