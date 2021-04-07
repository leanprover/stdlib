/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/
import analysis.calculus.fderiv
import analysis.specific_limits
import data.polynomial.derivative

/-!

# One-dimensional derivatives

This file defines the derivative of a function `f : 𝕜 → F` where `𝕜` is a
normed field and `F` is a normed space over this field. The derivative of
such a function `f` at a point `x` is given by an element `f' : F`.

The theory is developed analogously to the [Fréchet
derivatives](./fderiv.lean). We first introduce predicates defined in terms
of the corresponding predicates for Fréchet derivatives:

 - `has_deriv_at_filter f f' x L` states that the function `f` has the
    derivative `f'` at the point `x` as `x` goes along the filter `L`.

 - `has_deriv_within_at f f' s x` states that the function `f` has the
    derivative `f'` at the point `x` within the subset `s`.

 - `has_deriv_at f f' x` states that the function `f` has the derivative `f'`
    at the point `x`.

 - `has_strict_deriv_at f f' x` states that the function `f` has the derivative `f'`
    at the point `x` in the sense of strict differentiability, i.e.,
   `f y - f z = (y - z) • f' + o (y - z)` as `y, z → x`.

For the last two notions we also define a functional version:

  - `deriv_within f s x` is a derivative of `f` at `x` within `s`. If the
    derivative does not exist, then `deriv_within f s x` equals zero.

  - `deriv f x` is a derivative of `f` at `x`. If the derivative does not
    exist, then `deriv f x` equals zero.

The theorems `fderiv_within_deriv_within` and `fderiv_deriv` show that the
one-dimensional derivatives coincide with the general Fréchet derivatives.

We also show the existence and compute the derivatives of:
  - constants
  - the identity function
  - linear maps
  - addition
  - sum of finitely many functions
  - negation
  - subtraction
  - multiplication
  - inverse `x → x⁻¹`
  - multiplication of two functions in `𝕜 → 𝕜`
  - multiplication of a function in `𝕜 → 𝕜` and of a function in `𝕜 → E`
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜`
  - composition of a function in `F → E` with a function in `𝕜 → F`
  - inverse function (assuming that it exists; the inverse function theorem is in `inverse.lean`)
  - division
  - polynomials

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `has_deriv_at`'s easier,
and they more frequently lead to the desired result.

We set up the simplifier so that it can compute the derivative of simple functions. For instance,
```lean
example (x : ℝ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simp, ring }
```

## Implementation notes

Most of the theorems are direct restatements of the corresponding theorems
for Fréchet derivatives.

The strategy to construct simp lemmas that give the simplifier the possibility to compute
derivatives is the same as the one for differentiability statements, as explained in `fderiv.lean`.
See the explanations there.
-/

universes u v w
noncomputable theory
open_locale classical topological_space big_operators filter ennreal
open filter asymptotics set
open continuous_linear_map (smul_right smul_right_one_eq_iff)


variables {𝕜 : Type u} [nondiscrete_normed_field 𝕜]

section
variables {F : Type v} [normed_group F] [normed_space 𝕜 F]
variables {E : Type w} [normed_group E] [normed_space 𝕜 E]

/--
`f` has the derivative `f'` at the point `x` as `x` goes along the filter `L`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges along the filter `L`.
-/
def has_deriv_at_filter (f : 𝕜 → F) (f' : F) (x : 𝕜) (L : filter 𝕜) :=
has_fderiv_at_filter f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') x L

/--
`f` has the derivative `f'` at the point `x` within the subset `s`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def has_deriv_within_at (f : 𝕜 → F) (f' : F) (s : set 𝕜) (x : 𝕜) :=
has_deriv_at_filter f f' x (𝓝[s] x)

/--
`f` has the derivative `f'` at the point `x`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x`.
-/
def has_deriv_at (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
has_deriv_at_filter f f' x (𝓝 x)

/-- `f` has the derivative `f'` at the point `x` in the sense of strict differentiability.

That is, `f y - f z = (y - z) • f' + o(y - z)` as `y, z → x`. -/
def has_strict_deriv_at (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
has_strict_fderiv_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') x

/--
Derivative of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_within_at f f' s x`), then
`f x' = f x + (x' - x) • deriv_within f s x + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def deriv_within (f : 𝕜 → F) (s : set 𝕜) (x : 𝕜) :=
fderiv_within 𝕜 f s x 1

/--
Derivative of `f` at the point `x`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_at f f' x`), then
`f x' = f x + (x' - x) • deriv f x + o(x' - x)` where `x'` converges to `x`.
-/
def deriv (f : 𝕜 → F) (x : 𝕜) :=
fderiv 𝕜 f x 1

variables {f f₀ f₁ g : 𝕜 → F}
variables {f' f₀' f₁' g' : F}
variables {x : 𝕜}
variables {s t : set 𝕜}
variables {L L₁ L₂ : filter 𝕜}

/-- Expressing `has_fderiv_at_filter f f' x L` in terms of `has_deriv_at_filter` -/
lemma has_fderiv_at_filter_iff_has_deriv_at_filter {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at_filter f f' x L ↔ has_deriv_at_filter f (f' 1) x L :=
by simp [has_deriv_at_filter]

lemma has_fderiv_at_filter.has_deriv_at_filter {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at_filter f f' x L → has_deriv_at_filter f (f' 1) x L :=
has_fderiv_at_filter_iff_has_deriv_at_filter.mp

/-- Expressing `has_fderiv_within_at f f' s x` in terms of `has_deriv_within_at` -/
lemma has_fderiv_within_at_iff_has_deriv_within_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_within_at f f' s x ↔ has_deriv_within_at f (f' 1) s x :=
has_fderiv_at_filter_iff_has_deriv_at_filter

/-- Expressing `has_deriv_within_at f f' s x` in terms of `has_fderiv_within_at` -/
lemma has_deriv_within_at_iff_has_fderiv_within_at {f' : F} :
  has_deriv_within_at f f' s x ↔
  has_fderiv_within_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
iff.rfl

lemma has_fderiv_within_at.has_deriv_within_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_within_at f f' s x → has_deriv_within_at f (f' 1) s x :=
has_fderiv_within_at_iff_has_deriv_within_at.mp

lemma has_deriv_within_at.has_fderiv_within_at {f' : F} :
  has_deriv_within_at f f' s x → has_fderiv_within_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
has_deriv_within_at_iff_has_fderiv_within_at.mp

/-- Expressing `has_fderiv_at f f' x` in terms of `has_deriv_at` -/
lemma has_fderiv_at_iff_has_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at f f' x ↔ has_deriv_at f (f' 1) x :=
has_fderiv_at_filter_iff_has_deriv_at_filter

lemma has_fderiv_at.has_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at f f' x → has_deriv_at f (f' 1) x :=
has_fderiv_at_iff_has_deriv_at.mp

lemma has_strict_fderiv_at_iff_has_strict_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_strict_fderiv_at f f' x ↔ has_strict_deriv_at f (f' 1) x :=
by simp [has_strict_deriv_at, has_strict_fderiv_at]

protected lemma has_strict_fderiv_at.has_strict_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_strict_fderiv_at f f' x → has_strict_deriv_at f (f' 1) x :=
has_strict_fderiv_at_iff_has_strict_deriv_at.mp

lemma has_strict_deriv_at_iff_has_strict_fderiv_at :
  has_strict_deriv_at f f' x ↔ has_strict_fderiv_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
iff.rfl

alias has_strict_deriv_at_iff_has_strict_fderiv_at ↔ has_strict_deriv_at.has_strict_fderiv_at _

/-- Expressing `has_deriv_at f f' x` in terms of `has_fderiv_at` -/
lemma has_deriv_at_iff_has_fderiv_at {f' : F} :
  has_deriv_at f f' x ↔
  has_fderiv_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
iff.rfl

alias has_deriv_at_iff_has_fderiv_at ↔ has_deriv_at.has_fderiv_at _

lemma deriv_within_zero_of_not_differentiable_within_at
  (h : ¬ differentiable_within_at 𝕜 f s x) : deriv_within f s x = 0 :=
by { unfold deriv_within, rw fderiv_within_zero_of_not_differentiable_within_at, simp, assumption }

lemma deriv_zero_of_not_differentiable_at (h : ¬ differentiable_at 𝕜 f x) : deriv f x = 0 :=
by { unfold deriv, rw fderiv_zero_of_not_differentiable_at, simp, assumption }

theorem unique_diff_within_at.eq_deriv (s : set 𝕜) (H : unique_diff_within_at 𝕜 s x)
  (h : has_deriv_within_at f f' s x) (h₁ : has_deriv_within_at f f₁' s x) : f' = f₁' :=
smul_right_one_eq_iff.mp $ unique_diff_within_at.eq H h h₁

theorem has_deriv_at_filter_iff_tendsto :
  has_deriv_at_filter f f' x L ↔
  tendsto (λ x' : 𝕜, ∥x' - x∥⁻¹ * ∥f x' - f x - (x' - x) • f'∥) L (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_deriv_within_at_iff_tendsto : has_deriv_within_at f f' s x ↔
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - (x' - x) • f'∥) (𝓝[s] x) (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_deriv_at_iff_tendsto : has_deriv_at f f' x ↔
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - (x' - x) • f'∥) (𝓝 x) (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_strict_deriv_at.has_deriv_at (h : has_strict_deriv_at f f' x) :
  has_deriv_at f f' x :=
h.has_fderiv_at

/-- If the domain has dimension one, then Fréchet derivative is equivalent to the classical
definition with a limit. In this version we have to take the limit along the subset `-{x}`,
because for `y=x` the slope equals zero due to the convention `0⁻¹=0`. -/
lemma has_deriv_at_filter_iff_tendsto_slope {x : 𝕜} {L : filter 𝕜} :
  has_deriv_at_filter f f' x L ↔
    tendsto (λ y, (y - x)⁻¹ • (f y - f x)) (L ⊓ 𝓟 {x}ᶜ) (𝓝 f') :=
begin
  conv_lhs { simp only [has_deriv_at_filter_iff_tendsto, (normed_field.norm_inv _).symm,
    (norm_smul _ _).symm, tendsto_zero_iff_norm_tendsto_zero.symm] },
  conv_rhs { rw [← nhds_translation f', tendsto_comap_iff] },
  refine (tendsto_inf_principal_nhds_iff_of_forall_eq $ by simp).symm.trans (tendsto_congr' _),
  refine (eventually_principal.2 $ λ z hz, _).filter_mono inf_le_right,
  simp only [(∘)],
  rw [smul_sub, ← mul_smul, inv_mul_cancel (sub_ne_zero.2 hz), one_smul]
end

lemma has_deriv_within_at_iff_tendsto_slope :
  has_deriv_within_at f f' s x ↔
    tendsto (λ y, (y - x)⁻¹ • (f y - f x)) (𝓝[s \ {x}] x) (𝓝 f') :=
begin
  simp only [has_deriv_within_at, nhds_within, diff_eq, inf_assoc.symm, inf_principal.symm],
  exact has_deriv_at_filter_iff_tendsto_slope
end

lemma has_deriv_within_at_iff_tendsto_slope' (hs : x ∉ s) :
  has_deriv_within_at f f' s x ↔
    tendsto (λ y, (y - x)⁻¹ • (f y - f x)) (𝓝[s] x) (𝓝 f') :=
begin
  convert ← has_deriv_within_at_iff_tendsto_slope,
  exact diff_singleton_eq_self hs
end

lemma has_deriv_at_iff_tendsto_slope :
  has_deriv_at f f' x ↔
    tendsto (λ y, (y - x)⁻¹ • (f y - f x)) (𝓝[{x}ᶜ] x) (𝓝 f') :=
has_deriv_at_filter_iff_tendsto_slope

@[simp] lemma has_deriv_within_at_diff_singleton :
  has_deriv_within_at f f' (s \ {x}) x ↔ has_deriv_within_at f f' s x :=
by simp only [has_deriv_within_at_iff_tendsto_slope, sdiff_idem]

@[simp] lemma has_deriv_within_at_Ioi_iff_Ici [partial_order 𝕜] :
  has_deriv_within_at f f' (Ioi x) x ↔ has_deriv_within_at f f' (Ici x) x :=
by rw [← Ici_diff_left, has_deriv_within_at_diff_singleton]

alias has_deriv_within_at_Ioi_iff_Ici ↔
  has_deriv_within_at.Ici_of_Ioi has_deriv_within_at.Ioi_of_Ici

@[simp] lemma has_deriv_within_at_Iio_iff_Iic [partial_order 𝕜] :
  has_deriv_within_at f f' (Iio x) x ↔ has_deriv_within_at f f' (Iic x) x :=
by rw [← Iic_diff_right, has_deriv_within_at_diff_singleton]

alias has_deriv_within_at_Iio_iff_Iic ↔
  has_deriv_within_at.Iic_of_Iio has_deriv_within_at.Iio_of_Iic

theorem has_deriv_at_iff_is_o_nhds_zero : has_deriv_at f f' x ↔
  is_o (λh, f (x + h) - f x - h • f') (λh, h) (𝓝 0) :=
has_fderiv_at_iff_is_o_nhds_zero

theorem has_deriv_at_filter.mono (h : has_deriv_at_filter f f' x L₂) (hst : L₁ ≤ L₂) :
  has_deriv_at_filter f f' x L₁ :=
has_fderiv_at_filter.mono h hst

theorem has_deriv_within_at.mono (h : has_deriv_within_at f f' t x) (hst : s ⊆ t) :
  has_deriv_within_at f f' s x :=
has_fderiv_within_at.mono h hst

theorem has_deriv_at.has_deriv_at_filter (h : has_deriv_at f f' x) (hL : L ≤ 𝓝 x) :
  has_deriv_at_filter f f' x L :=
has_fderiv_at.has_fderiv_at_filter h hL

theorem has_deriv_at.has_deriv_within_at
  (h : has_deriv_at f f' x) : has_deriv_within_at f f' s x :=
has_fderiv_at.has_fderiv_within_at h

lemma has_deriv_within_at.differentiable_within_at (h : has_deriv_within_at f f' s x) :
  differentiable_within_at 𝕜 f s x :=
has_fderiv_within_at.differentiable_within_at h

lemma has_deriv_at.differentiable_at (h : has_deriv_at f f' x) : differentiable_at 𝕜 f x :=
has_fderiv_at.differentiable_at h

@[simp] lemma has_deriv_within_at_univ : has_deriv_within_at f f' univ x ↔ has_deriv_at f f' x :=
has_fderiv_within_at_univ

theorem has_deriv_at.unique
  (h₀ : has_deriv_at f f₀' x) (h₁ : has_deriv_at f f₁' x) : f₀' = f₁' :=
smul_right_one_eq_iff.mp $ h₀.has_fderiv_at.unique h₁

lemma has_deriv_within_at_inter' (h : t ∈ 𝓝[s] x) :
  has_deriv_within_at f f' (s ∩ t) x ↔ has_deriv_within_at f f' s x :=
has_fderiv_within_at_inter' h

lemma has_deriv_within_at_inter (h : t ∈ 𝓝 x) :
  has_deriv_within_at f f' (s ∩ t) x ↔ has_deriv_within_at f f' s x :=
has_fderiv_within_at_inter h

lemma has_deriv_within_at.union (hs : has_deriv_within_at f f' s x)
  (ht : has_deriv_within_at f f' t x) :
  has_deriv_within_at f f' (s ∪ t) x :=
begin
  simp only [has_deriv_within_at, nhds_within_union],
  exact hs.join ht,
end

lemma has_deriv_within_at.nhds_within (h : has_deriv_within_at f f' s x)
  (ht : s ∈ 𝓝[t] x) : has_deriv_within_at f f' t x :=
(has_deriv_within_at_inter' ht).1 (h.mono (inter_subset_right _ _))

lemma has_deriv_within_at.has_deriv_at (h : has_deriv_within_at f f' s x) (hs : s ∈ 𝓝 x) :
  has_deriv_at f f' x :=
has_fderiv_within_at.has_fderiv_at h hs

lemma differentiable_within_at.has_deriv_within_at (h : differentiable_within_at 𝕜 f s x) :
  has_deriv_within_at f (deriv_within f s x) s x :=
show has_fderiv_within_at _ _ _ _, by { convert h.has_fderiv_within_at, simp [deriv_within] }

lemma differentiable_at.has_deriv_at (h : differentiable_at 𝕜 f x) : has_deriv_at f (deriv f x) x :=
show has_fderiv_at _ _ _, by { convert h.has_fderiv_at, simp [deriv] }

lemma has_deriv_at.deriv (h : has_deriv_at f f' x) : deriv f x = f' :=
h.differentiable_at.has_deriv_at.unique h

lemma has_deriv_within_at.deriv_within
  (h : has_deriv_within_at f f' s x) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within f s x = f' :=
hxs.eq_deriv _ h.differentiable_within_at.has_deriv_within_at h

lemma fderiv_within_deriv_within : (fderiv_within 𝕜 f s x : 𝕜 → F) 1 = deriv_within f s x :=
rfl

lemma deriv_within_fderiv_within :
  smul_right (1 : 𝕜 →L[𝕜] 𝕜) (deriv_within f s x) = fderiv_within 𝕜 f s x :=
by simp [deriv_within]

lemma fderiv_deriv : (fderiv 𝕜 f x : 𝕜 → F) 1 = deriv f x :=
rfl

lemma deriv_fderiv :
  smul_right (1 : 𝕜 →L[𝕜] 𝕜) (deriv f x) = fderiv 𝕜 f x :=
by simp [deriv]

lemma differentiable_at.deriv_within (h : differentiable_at 𝕜 f x)
  (hxs : unique_diff_within_at 𝕜 s x) : deriv_within f s x = deriv f x :=
by { unfold deriv_within deriv, rw h.fderiv_within hxs }

lemma deriv_within_subset (st : s ⊆ t) (ht : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f t x) :
  deriv_within f s x = deriv_within f t x :=
((differentiable_within_at.has_deriv_within_at h).mono st).deriv_within ht

@[simp] lemma deriv_within_univ : deriv_within f univ = deriv f :=
by { ext, unfold deriv_within deriv, rw fderiv_within_univ }

lemma deriv_within_inter (ht : t ∈ 𝓝 x) (hs : unique_diff_within_at 𝕜 s x) :
  deriv_within f (s ∩ t) x = deriv_within f s x :=
by { unfold deriv_within, rw fderiv_within_inter ht hs }

lemma deriv_within_of_open (hs : is_open s) (hx : x ∈ s) :
  deriv_within f s x = deriv f x :=
by { unfold deriv_within, rw fderiv_within_of_open hs hx, refl }

section congr
/-! ### Congruence properties of derivatives -/

theorem filter.eventually_eq.has_deriv_at_filter_iff
  (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x) (h₁ : f₀' = f₁') :
  has_deriv_at_filter f₀ f₀' x L ↔ has_deriv_at_filter f₁ f₁' x L :=
h₀.has_fderiv_at_filter_iff hx (by simp [h₁])

lemma has_deriv_at_filter.congr_of_eventually_eq (h : has_deriv_at_filter f f' x L)
  (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) : has_deriv_at_filter f₁ f' x L :=
by rwa hL.has_deriv_at_filter_iff hx rfl

lemma has_deriv_within_at.congr_mono (h : has_deriv_within_at f f' s x) (ht : ∀x ∈ t, f₁ x = f x)
  (hx : f₁ x = f x) (h₁ : t ⊆ s) : has_deriv_within_at f₁ f' t x :=
has_fderiv_within_at.congr_mono h ht hx h₁

lemma has_deriv_within_at.congr (h : has_deriv_within_at f f' s x) (hs : ∀x ∈ s, f₁ x = f x)
  (hx : f₁ x = f x) : has_deriv_within_at f₁ f' s x :=
h.congr_mono hs hx (subset.refl _)

lemma has_deriv_within_at.congr_of_eventually_eq (h : has_deriv_within_at f f' s x)
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : has_deriv_within_at f₁ f' s x :=
has_deriv_at_filter.congr_of_eventually_eq h h₁ hx

lemma has_deriv_within_at.congr_of_eventually_eq_of_mem (h : has_deriv_within_at f f' s x)
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : has_deriv_within_at f₁ f' s x :=
h.congr_of_eventually_eq h₁ (h₁.eq_of_nhds_within hx)

lemma has_deriv_at.congr_of_eventually_eq (h : has_deriv_at f f' x)
  (h₁ : f₁ =ᶠ[𝓝 x] f) : has_deriv_at f₁ f' x :=
has_deriv_at_filter.congr_of_eventually_eq h h₁ (mem_of_nhds h₁ : _)

lemma filter.eventually_eq.deriv_within_eq (hs : unique_diff_within_at 𝕜 s x)
  (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  deriv_within f₁ s x = deriv_within f s x :=
by { unfold deriv_within, rw hL.fderiv_within_eq hs hx }

lemma deriv_within_congr (hs : unique_diff_within_at 𝕜 s x)
  (hL : ∀y∈s, f₁ y = f y) (hx : f₁ x = f x) :
  deriv_within f₁ s x = deriv_within f s x :=
by { unfold deriv_within, rw fderiv_within_congr hs hL hx }

lemma filter.eventually_eq.deriv_eq (hL : f₁ =ᶠ[𝓝 x] f) : deriv f₁ x = deriv f x :=
by { unfold deriv, rwa filter.eventually_eq.fderiv_eq }

end congr

section id
/-! ### Derivative of the identity -/
variables (s x L)

theorem has_deriv_at_filter_id : has_deriv_at_filter id 1 x L :=
(has_fderiv_at_filter_id x L).has_deriv_at_filter

theorem has_deriv_within_at_id : has_deriv_within_at id 1 s x :=
has_deriv_at_filter_id _ _

theorem has_deriv_at_id : has_deriv_at id 1 x :=
has_deriv_at_filter_id _ _

theorem has_deriv_at_id' : has_deriv_at (λ (x : 𝕜), x) 1 x :=
has_deriv_at_filter_id _ _

theorem has_strict_deriv_at_id : has_strict_deriv_at id 1 x :=
(has_strict_fderiv_at_id x).has_strict_deriv_at

lemma deriv_id : deriv id x = 1 :=
has_deriv_at.deriv (has_deriv_at_id x)

@[simp] lemma deriv_id' : deriv (@id 𝕜) = λ _, 1 :=
funext deriv_id

@[simp] lemma deriv_id'' : deriv (λ x : 𝕜, x) x = 1 :=
deriv_id x

lemma deriv_within_id (hxs : unique_diff_within_at 𝕜 s x) : deriv_within id s x = 1 :=
(has_deriv_within_at_id x s).deriv_within hxs

end id

section const
/-! ### Derivative of constant functions -/
variables (c : F) (s x L)

theorem has_deriv_at_filter_const : has_deriv_at_filter (λ x, c) 0 x L :=
(has_fderiv_at_filter_const c x L).has_deriv_at_filter

theorem has_strict_deriv_at_const : has_strict_deriv_at (λ x, c) 0 x :=
(has_strict_fderiv_at_const c x).has_strict_deriv_at

theorem has_deriv_within_at_const : has_deriv_within_at (λ x, c) 0 s x :=
has_deriv_at_filter_const _ _ _

theorem has_deriv_at_const : has_deriv_at (λ x, c) 0 x :=
has_deriv_at_filter_const _ _ _

lemma deriv_const : deriv (λ x, c) x = 0 :=
has_deriv_at.deriv (has_deriv_at_const x c)

@[simp] lemma deriv_const' : deriv (λ x:𝕜, c) = λ x, 0 :=
funext (λ x, deriv_const x c)

lemma deriv_within_const (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (λ x, c) s x = 0 :=
(has_deriv_within_at_const _ _ _).deriv_within hxs

end const

section continuous_linear_map
/-! ### Derivative of continuous linear maps -/
variables (e : 𝕜 →L[𝕜] F)

protected lemma continuous_linear_map.has_deriv_at_filter : has_deriv_at_filter e (e 1) x L :=
e.has_fderiv_at_filter.has_deriv_at_filter

protected lemma continuous_linear_map.has_strict_deriv_at : has_strict_deriv_at e (e 1) x :=
e.has_strict_fderiv_at.has_strict_deriv_at

protected lemma continuous_linear_map.has_deriv_at : has_deriv_at e (e 1) x :=
e.has_deriv_at_filter

protected lemma continuous_linear_map.has_deriv_within_at : has_deriv_within_at e (e 1) s x :=
e.has_deriv_at_filter

@[simp] protected lemma continuous_linear_map.deriv : deriv e x = e 1 :=
e.has_deriv_at.deriv

protected lemma continuous_linear_map.deriv_within (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within e s x = e 1 :=
e.has_deriv_within_at.deriv_within hxs

end continuous_linear_map

section linear_map
/-! ### Derivative of bundled linear maps -/
variables (e : 𝕜 →ₗ[𝕜] F)

protected lemma linear_map.has_deriv_at_filter : has_deriv_at_filter e (e 1) x L :=
e.to_continuous_linear_map₁.has_deriv_at_filter

protected lemma linear_map.has_strict_deriv_at : has_strict_deriv_at e (e 1) x :=
e.to_continuous_linear_map₁.has_strict_deriv_at

protected lemma linear_map.has_deriv_at : has_deriv_at e (e 1) x :=
e.has_deriv_at_filter

protected lemma linear_map.has_deriv_within_at : has_deriv_within_at e (e 1) s x :=
e.has_deriv_at_filter

@[simp] protected lemma linear_map.deriv : deriv e x = e 1 :=
e.has_deriv_at.deriv

protected lemma linear_map.deriv_within (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within e s x = e 1 :=
e.has_deriv_within_at.deriv_within hxs

end linear_map

section analytic

variables {p : formal_multilinear_series 𝕜 𝕜 F} {r : ℝ≥0∞}

protected lemma has_fpower_series_at.has_strict_deriv_at (h : has_fpower_series_at f p x) :
  has_strict_deriv_at f (p 1 (λ _, 1)) x :=
h.has_strict_fderiv_at.has_strict_deriv_at

protected lemma has_fpower_series_at.has_deriv_at (h : has_fpower_series_at f p x) :
  has_deriv_at f (p 1 (λ _, 1)) x :=
h.has_strict_deriv_at.has_deriv_at

protected lemma has_fpower_series_at.deriv (h : has_fpower_series_at f p x) :
  deriv f x = p 1 (λ _, 1) :=
h.has_deriv_at.deriv

end analytic

section add
/-! ### Derivative of the sum of two functions -/

theorem has_deriv_at_filter.add
  (hf : has_deriv_at_filter f f' x L) (hg : has_deriv_at_filter g g' x L) :
  has_deriv_at_filter (λ y, f y + g y) (f' + g') x L :=
by simpa using (hf.add hg).has_deriv_at_filter

theorem has_strict_deriv_at.add
  (hf : has_strict_deriv_at f f' x) (hg : has_strict_deriv_at g g' x) :
  has_strict_deriv_at (λ y, f y + g y) (f' + g') x :=
by simpa using (hf.add hg).has_strict_deriv_at

theorem has_deriv_within_at.add
  (hf : has_deriv_within_at f f' s x) (hg : has_deriv_within_at g g' s x) :
  has_deriv_within_at (λ y, f y + g y) (f' + g') s x :=
hf.add hg

theorem has_deriv_at.add
  (hf : has_deriv_at f f' x) (hg : has_deriv_at g g' x) :
  has_deriv_at (λ x, f x + g x) (f' + g') x :=
hf.add hg

lemma deriv_within_add (hxs : unique_diff_within_at 𝕜 s x)
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  deriv_within (λy, f y + g y) s x = deriv_within f s x + deriv_within g s x :=
(hf.has_deriv_within_at.add hg.has_deriv_within_at).deriv_within hxs

@[simp] lemma deriv_add
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  deriv (λy, f y + g y) x = deriv f x + deriv g x :=
(hf.has_deriv_at.add hg.has_deriv_at).deriv

theorem has_deriv_at_filter.add_const
  (hf : has_deriv_at_filter f f' x L) (c : F) :
  has_deriv_at_filter (λ y, f y + c) f' x L :=
add_zero f' ▸ hf.add (has_deriv_at_filter_const x L c)

theorem has_deriv_within_at.add_const
  (hf : has_deriv_within_at f f' s x) (c : F) :
  has_deriv_within_at (λ y, f y + c) f' s x :=
hf.add_const c

theorem has_deriv_at.add_const
  (hf : has_deriv_at f f' x) (c : F) :
  has_deriv_at (λ x, f x + c) f' x :=
hf.add_const c

lemma deriv_within_add_const (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  deriv_within (λy, f y + c) s x = deriv_within f s x :=
by simp only [deriv_within, fderiv_within_add_const hxs]

lemma deriv_add_const (c : F) : deriv (λy, f y + c) x = deriv f x :=
by simp only [deriv, fderiv_add_const]

theorem has_deriv_at_filter.const_add (c : F) (hf : has_deriv_at_filter f f' x L) :
  has_deriv_at_filter (λ y, c + f y) f' x L :=
zero_add f' ▸ (has_deriv_at_filter_const x L c).add hf

theorem has_deriv_within_at.const_add (c : F) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ y, c + f y) f' s x :=
hf.const_add c

theorem has_deriv_at.const_add (c : F) (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, c + f x) f' x :=
hf.const_add c

lemma deriv_within_const_add (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  deriv_within (λy, c + f y) s x = deriv_within f s x :=
by simp only [deriv_within, fderiv_within_const_add hxs]

lemma deriv_const_add (c : F)  : deriv (λy, c + f y) x = deriv f x :=
by simp only [deriv, fderiv_const_add]

end add

section sum
/-! ### Derivative of a finite sum of functions -/

open_locale big_operators

variables {ι : Type*} {u : finset ι} {A : ι → (𝕜 → F)} {A' : ι → F}

theorem has_deriv_at_filter.sum (h : ∀ i ∈ u, has_deriv_at_filter (A i) (A' i) x L) :
  has_deriv_at_filter (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x L :=
by simpa [continuous_linear_map.sum_apply] using (has_fderiv_at_filter.sum h).has_deriv_at_filter

theorem has_strict_deriv_at.sum (h : ∀ i ∈ u, has_strict_deriv_at (A i) (A' i) x) :
  has_strict_deriv_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x :=
by simpa [continuous_linear_map.sum_apply] using (has_strict_fderiv_at.sum h).has_strict_deriv_at

theorem has_deriv_within_at.sum (h : ∀ i ∈ u, has_deriv_within_at (A i) (A' i) s x) :
  has_deriv_within_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) s x :=
has_deriv_at_filter.sum h

theorem has_deriv_at.sum (h : ∀ i ∈ u, has_deriv_at (A i) (A' i) x) :
  has_deriv_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x :=
has_deriv_at_filter.sum h

lemma deriv_within_sum (hxs : unique_diff_within_at 𝕜 s x)
  (h : ∀ i ∈ u, differentiable_within_at 𝕜 (A i) s x) :
  deriv_within (λ y, ∑ i in u, A i y) s x = ∑ i in u, deriv_within (A i) s x :=
(has_deriv_within_at.sum (λ i hi, (h i hi).has_deriv_within_at)).deriv_within hxs

@[simp] lemma deriv_sum (h : ∀ i ∈ u, differentiable_at 𝕜 (A i) x) :
  deriv (λ y, ∑ i in u, A i y) x = ∑ i in u, deriv (A i) x :=
(has_deriv_at.sum (λ i hi, (h i hi).has_deriv_at)).deriv

end sum

section pi

/-! ### Derivatives of functions `f : 𝕜 → Π i, E i` -/

variables {ι : Type*} [fintype ι] {E' : ι → Type*} [Π i, normed_group (E' i)]
  [Π i, normed_space 𝕜 (E' i)] {φ : 𝕜 → Π i, E' i} {φ' : Π i, E' i}

@[simp] lemma has_strict_deriv_at_pi :
  has_strict_deriv_at φ φ' x ↔ ∀ i, has_strict_deriv_at (λ x, φ x i) (φ' i) x :=
has_strict_fderiv_at_pi'

@[simp] lemma has_deriv_at_filter_pi :
  has_deriv_at_filter φ φ' x L ↔
    ∀ i, has_deriv_at_filter (λ x, φ x i) (φ' i) x L :=
has_fderiv_at_filter_pi'

lemma has_deriv_at_pi :
  has_deriv_at φ φ' x ↔ ∀ i, has_deriv_at (λ x, φ x i) (φ' i) x:=
has_deriv_at_filter_pi

lemma has_deriv_within_at_pi :
  has_deriv_within_at φ φ' s x ↔ ∀ i, has_deriv_within_at (λ x, φ x i) (φ' i) s x:=
has_deriv_at_filter_pi

lemma deriv_within_pi (h : ∀ i, differentiable_within_at 𝕜 (λ x, φ x i) s x)
  (hs : unique_diff_within_at 𝕜 s x) :
  deriv_within φ s x = λ i, deriv_within (λ x, φ x i) s x :=
(has_deriv_within_at_pi.2 (λ i, (h i).has_deriv_within_at)).deriv_within hs

lemma deriv_pi (h : ∀ i, differentiable_at 𝕜 (λ x, φ x i) x) :
  deriv φ x = λ i, deriv (λ x, φ x i) x :=
(has_deriv_at_pi.2 (λ i, (h i).has_deriv_at)).deriv

end pi

section mul_vector
/-! ### Derivative of the multiplication of a scalar function and a vector function -/
variables {c : 𝕜 → 𝕜} {c' : 𝕜}

theorem has_deriv_within_at.smul
  (hc : has_deriv_within_at c c' s x) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ y, c y • f y) (c x • f' + c' • f x) s x :=
by simpa using (has_fderiv_within_at.smul hc hf).has_deriv_within_at

theorem has_deriv_at.smul
  (hc : has_deriv_at c c' x) (hf : has_deriv_at f f' x) :
  has_deriv_at (λ y, c y • f y) (c x • f' + c' • f x) x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.smul hf
end

theorem has_strict_deriv_at.smul
  (hc : has_strict_deriv_at c c' x) (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ y, c y • f y) (c x • f' + c' • f x) x :=
by simpa using (hc.smul hf).has_strict_deriv_at

lemma deriv_within_smul (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hf : differentiable_within_at 𝕜 f s x) :
  deriv_within (λ y, c y • f y) s x = c x • deriv_within f s x + (deriv_within c s x) • f x :=
(hc.has_deriv_within_at.smul hf.has_deriv_within_at).deriv_within hxs

lemma deriv_smul (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) :
  deriv (λ y, c y • f y) x = c x • deriv f x + (deriv c x) • f x :=
(hc.has_deriv_at.smul hf.has_deriv_at).deriv

theorem has_deriv_within_at.smul_const
  (hc : has_deriv_within_at c c' s x) (f : F) :
  has_deriv_within_at (λ y, c y • f) (c' • f) s x :=
begin
  have := hc.smul (has_deriv_within_at_const x s f),
  rwa [smul_zero, zero_add] at this
end

theorem has_deriv_at.smul_const
  (hc : has_deriv_at c c' x) (f : F) :
  has_deriv_at (λ y, c y • f) (c' • f) x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.smul_const f
end

lemma deriv_within_smul_const (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (f : F) :
  deriv_within (λ y, c y • f) s x = (deriv_within c s x) • f :=
(hc.has_deriv_within_at.smul_const f).deriv_within hxs

lemma deriv_smul_const (hc : differentiable_at 𝕜 c x) (f : F) :
  deriv (λ y, c y • f) x = (deriv c x) • f :=
(hc.has_deriv_at.smul_const f).deriv

theorem has_deriv_within_at.const_smul
  (c : 𝕜) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ y, c • f y) (c • f') s x :=
begin
  convert (has_deriv_within_at_const x s c).smul hf,
  rw [zero_smul, add_zero]
end

theorem has_deriv_at.const_smul (c : 𝕜) (hf : has_deriv_at f f' x) :
  has_deriv_at (λ y, c • f y) (c • f') x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hf.const_smul c
end

lemma deriv_within_const_smul (hxs : unique_diff_within_at 𝕜 s x)
  (c : 𝕜) (hf : differentiable_within_at 𝕜 f s x) :
  deriv_within (λ y, c • f y) s x = c • deriv_within f s x :=
(hf.has_deriv_within_at.const_smul c).deriv_within hxs

lemma deriv_const_smul (c : 𝕜) (hf : differentiable_at 𝕜 f x) :
  deriv (λ y, c • f y) x = c • deriv f x :=
(hf.has_deriv_at.const_smul c).deriv

end mul_vector

section neg
/-! ### Derivative of the negative of a function -/

theorem has_deriv_at_filter.neg (h : has_deriv_at_filter f f' x L) :
  has_deriv_at_filter (λ x, -f x) (-f') x L :=
by simpa using h.neg.has_deriv_at_filter

theorem has_deriv_within_at.neg (h : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, -f x) (-f') s x :=
h.neg

theorem has_deriv_at.neg (h : has_deriv_at f f' x) : has_deriv_at (λ x, -f x) (-f') x :=
h.neg

theorem has_strict_deriv_at.neg (h : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, -f x) (-f') x :=
by simpa using h.neg.has_strict_deriv_at

lemma deriv_within.neg (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λy, -f y) s x = - deriv_within f s x :=
by simp only [deriv_within, fderiv_within_neg hxs, continuous_linear_map.neg_apply]

lemma deriv.neg : deriv (λy, -f y) x = - deriv f x :=
by simp only [deriv, fderiv_neg, continuous_linear_map.neg_apply]

@[simp] lemma deriv.neg' : deriv (λy, -f y) = (λ x, - deriv f x) :=
funext $ λ x, deriv.neg

end neg

section neg2
/-! ### Derivative of the negation function (i.e `has_neg.neg`) -/

variables (s x L)

theorem has_deriv_at_filter_neg : has_deriv_at_filter has_neg.neg (-1) x L :=
has_deriv_at_filter.neg $ has_deriv_at_filter_id _ _

theorem has_deriv_within_at_neg : has_deriv_within_at has_neg.neg (-1) s x :=
has_deriv_at_filter_neg _ _

theorem has_deriv_at_neg : has_deriv_at has_neg.neg (-1) x :=
has_deriv_at_filter_neg _ _

theorem has_deriv_at_neg' : has_deriv_at (λ x, -x) (-1) x :=
has_deriv_at_filter_neg _ _

theorem has_strict_deriv_at_neg : has_strict_deriv_at has_neg.neg (-1) x :=
has_strict_deriv_at.neg $ has_strict_deriv_at_id _

lemma deriv_neg : deriv has_neg.neg x = -1 :=
has_deriv_at.deriv (has_deriv_at_neg x)

@[simp] lemma deriv_neg' : deriv (has_neg.neg : 𝕜 → 𝕜) = λ _, -1 :=
funext deriv_neg

@[simp] lemma deriv_neg'' : deriv (λ x : 𝕜, -x) x = -1 :=
deriv_neg x

lemma deriv_within_neg (hxs : unique_diff_within_at 𝕜 s x) : deriv_within has_neg.neg s x = -1 :=
(has_deriv_within_at_neg x s).deriv_within hxs

lemma differentiable_neg : differentiable 𝕜 (has_neg.neg : 𝕜 → 𝕜) :=
differentiable.neg differentiable_id

lemma differentiable_on_neg : differentiable_on 𝕜 (has_neg.neg : 𝕜 → 𝕜) s :=
differentiable_on.neg differentiable_on_id

end neg2

section sub
/-! ### Derivative of the difference of two functions -/

theorem has_deriv_at_filter.sub
  (hf : has_deriv_at_filter f f' x L) (hg : has_deriv_at_filter g g' x L) :
  has_deriv_at_filter (λ x, f x - g x) (f' - g') x L :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem has_deriv_within_at.sub
  (hf : has_deriv_within_at f f' s x) (hg : has_deriv_within_at g g' s x) :
  has_deriv_within_at (λ x, f x - g x) (f' - g') s x :=
hf.sub hg

theorem has_deriv_at.sub
  (hf : has_deriv_at f f' x) (hg : has_deriv_at g g' x) :
  has_deriv_at (λ x, f x - g x) (f' - g') x :=
hf.sub hg

theorem has_strict_deriv_at.sub
  (hf : has_strict_deriv_at f f' x) (hg : has_strict_deriv_at g g' x) :
  has_strict_deriv_at (λ x, f x - g x) (f' - g') x :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma deriv_within_sub (hxs : unique_diff_within_at 𝕜 s x)
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  deriv_within (λy, f y - g y) s x = deriv_within f s x - deriv_within g s x :=
(hf.has_deriv_within_at.sub hg.has_deriv_within_at).deriv_within hxs

@[simp] lemma deriv_sub
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  deriv (λ y, f y - g y) x = deriv f x - deriv g x :=
(hf.has_deriv_at.sub hg.has_deriv_at).deriv

theorem has_deriv_at_filter.is_O_sub (h : has_deriv_at_filter f f' x L) :
  is_O (λ x', f x' - f x) (λ x', x' - x) L :=
has_fderiv_at_filter.is_O_sub h

theorem has_deriv_at_filter.sub_const
  (hf : has_deriv_at_filter f f' x L) (c : F) :
  has_deriv_at_filter (λ x, f x - c) f' x L :=
by simpa only [sub_eq_add_neg] using hf.add_const (-c)

theorem has_deriv_within_at.sub_const
  (hf : has_deriv_within_at f f' s x) (c : F) :
  has_deriv_within_at (λ x, f x - c) f' s x :=
hf.sub_const c

theorem has_deriv_at.sub_const
  (hf : has_deriv_at f f' x) (c : F) :
  has_deriv_at (λ x, f x - c) f' x :=
hf.sub_const c

lemma deriv_within_sub_const (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  deriv_within (λy, f y - c) s x = deriv_within f s x :=
by simp only [deriv_within, fderiv_within_sub_const hxs]

lemma deriv_sub_const (c : F) : deriv (λ y, f y - c) x = deriv f x :=
by simp only [deriv, fderiv_sub_const]

theorem has_deriv_at_filter.const_sub (c : F) (hf : has_deriv_at_filter f f' x L) :
  has_deriv_at_filter (λ x, c - f x) (-f') x L :=
by simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem has_deriv_within_at.const_sub (c : F) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, c - f x) (-f') s x :=
hf.const_sub c

theorem has_strict_deriv_at.const_sub (c : F) (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, c - f x) (-f') x :=
by simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem has_deriv_at.const_sub (c : F) (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, c - f x) (-f') x :=
hf.const_sub c

lemma deriv_within_const_sub (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  deriv_within (λy, c - f y) s x = -deriv_within f s x :=
by simp [deriv_within, fderiv_within_const_sub hxs]

lemma deriv_const_sub (c : F) : deriv (λ y, c - f y) x = -deriv f x :=
by simp only [← deriv_within_univ, deriv_within_const_sub unique_diff_within_at_univ]

end sub

section continuous
/-! ### Continuity of a function admitting a derivative -/

theorem has_deriv_at_filter.tendsto_nhds
  (hL : L ≤ 𝓝 x) (h : has_deriv_at_filter f f' x L) :
  tendsto f L (𝓝 (f x)) :=
h.tendsto_nhds hL

theorem has_deriv_within_at.continuous_within_at
  (h : has_deriv_within_at f f' s x) : continuous_within_at f s x :=
has_deriv_at_filter.tendsto_nhds inf_le_left h

theorem has_deriv_at.continuous_at (h : has_deriv_at f f' x) : continuous_at f x :=
has_deriv_at_filter.tendsto_nhds (le_refl _) h

end continuous

section cartesian_product
/-! ### Derivative of the cartesian product of two functions -/

variables {G : Type w} [normed_group G] [normed_space 𝕜 G]
variables {f₂ : 𝕜 → G} {f₂' : G}

lemma has_deriv_at_filter.prod
  (hf₁ : has_deriv_at_filter f₁ f₁' x L) (hf₂ : has_deriv_at_filter f₂ f₂' x L) :
  has_deriv_at_filter (λ x, (f₁ x, f₂ x)) (f₁', f₂') x L :=
show has_fderiv_at_filter _ _ _ _,
by convert has_fderiv_at_filter.prod hf₁ hf₂

lemma has_deriv_within_at.prod
  (hf₁ : has_deriv_within_at f₁ f₁' s x) (hf₂ : has_deriv_within_at f₂ f₂' s x) :
  has_deriv_within_at (λ x, (f₁ x, f₂ x)) (f₁', f₂') s x :=
hf₁.prod hf₂

lemma has_deriv_at.prod (hf₁ : has_deriv_at f₁ f₁' x) (hf₂ : has_deriv_at f₂ f₂' x) :
  has_deriv_at (λ x, (f₁ x, f₂ x)) (f₁', f₂') x :=
hf₁.prod hf₂

end cartesian_product

section composition
/-!
### Derivative of the composition of a vector function and a scalar function

We use `scomp` in lemmas on composition of vector valued and scalar valued functions, and `comp`
in lemmas on composition of scalar valued functions, in analogy for `smul` and `mul` (and also
because the `comp` version with the shorter name will show up much more often in applications).
The formula for the derivative involves `smul` in `scomp` lemmas, which can be reduced to
usual multiplication in `comp` lemmas.
-/

variables {h h₁ h₂ : 𝕜 → 𝕜} {h' h₁' h₂' : 𝕜}
/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/
variable (x)

theorem has_deriv_at_filter.scomp
  (hg : has_deriv_at_filter g g' (h x) (L.map h))
  (hh : has_deriv_at_filter h h' x L) :
  has_deriv_at_filter (g ∘ h) (h' • g') x L :=
by simpa using (hg.comp x hh).has_deriv_at_filter

theorem has_deriv_within_at.scomp {t : set 𝕜}
  (hg : has_deriv_within_at g g' t (h x))
  (hh : has_deriv_within_at h h' s x) (hst : s ⊆ h ⁻¹' t) :
  has_deriv_within_at (g ∘ h) (h' • g') s x :=
has_deriv_at_filter.scomp _ (has_deriv_at_filter.mono hg $
  hh.continuous_within_at.tendsto_nhds_within hst) hh

/-- The chain rule. -/
theorem has_deriv_at.scomp
  (hg : has_deriv_at g g' (h x)) (hh : has_deriv_at h h' x) :
  has_deriv_at (g ∘ h) (h' • g') x :=
(hg.mono hh.continuous_at).scomp x hh

theorem has_strict_deriv_at.scomp
  (hg : has_strict_deriv_at g g' (h x)) (hh : has_strict_deriv_at h h' x) :
  has_strict_deriv_at (g ∘ h) (h' • g') x :=
by simpa using (hg.comp x hh).has_strict_deriv_at

theorem has_deriv_at.scomp_has_deriv_within_at
  (hg : has_deriv_at g g' (h x)) (hh : has_deriv_within_at h h' s x) :
  has_deriv_within_at (g ∘ h) (h' • g') s x :=
begin
  rw ← has_deriv_within_at_univ at hg,
  exact has_deriv_within_at.scomp x hg hh subset_preimage_univ
end

lemma deriv_within.scomp
  (hg : differentiable_within_at 𝕜 g t (h x)) (hh : differentiable_within_at 𝕜 h s x)
  (hs : s ⊆ h ⁻¹' t) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (g ∘ h) s x = deriv_within h s x • deriv_within g t (h x) :=
begin
  apply has_deriv_within_at.deriv_within _ hxs,
  exact has_deriv_within_at.scomp x (hg.has_deriv_within_at) (hh.has_deriv_within_at) hs
end

lemma deriv.scomp
  (hg : differentiable_at 𝕜 g (h x)) (hh : differentiable_at 𝕜 h x) :
  deriv (g ∘ h) x = deriv h x • deriv g (h x) :=
begin
  apply has_deriv_at.deriv,
  exact has_deriv_at.scomp x hg.has_deriv_at hh.has_deriv_at
end

/-! ### Derivative of the composition of a scalar and vector functions -/

theorem has_deriv_at_filter.comp_has_fderiv_at_filter {f : E → 𝕜} {f' : E →L[𝕜] 𝕜} (x)
  {L : filter E} (hh₁ : has_deriv_at_filter h₁ h₁' (f x) (L.map f))
  (hf : has_fderiv_at_filter f f' x L) :
  has_fderiv_at_filter (h₁ ∘ f) (h₁' • f') x L :=
by { convert has_fderiv_at_filter.comp x hh₁ hf, ext x, simp [mul_comm] }

theorem has_strict_deriv_at.comp_has_strict_fderiv_at {f : E → 𝕜} {f' : E →L[𝕜] 𝕜} (x)
  (hh₁ : has_strict_deriv_at h₁ h₁' (f x)) (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (h₁ ∘ f) (h₁' • f') x :=
by { rw has_strict_deriv_at at hh₁, convert hh₁.comp x hf, ext x, simp [mul_comm] }

theorem has_deriv_at.comp_has_fderiv_at {f : E → 𝕜} {f' : E →L[𝕜] 𝕜} (x)
  (hh₁ : has_deriv_at h₁ h₁' (f x)) (hf : has_fderiv_at f f' x) :
  has_fderiv_at (h₁ ∘ f) (h₁' • f') x :=
(hh₁.mono hf.continuous_at).comp_has_fderiv_at_filter x hf

theorem has_deriv_at.comp_has_fderiv_within_at {f : E → 𝕜} {f' : E →L[𝕜] 𝕜} {s} (x)
  (hh₁ : has_deriv_at h₁ h₁' (f x)) (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (h₁ ∘ f) (h₁' • f') s x :=
(hh₁.mono hf.continuous_within_at).comp_has_fderiv_at_filter x hf

theorem has_deriv_within_at.comp_has_fderiv_within_at {f : E → 𝕜} {f' : E →L[𝕜] 𝕜} {s t} (x)
  (hh₁ : has_deriv_within_at h₁ h₁' t (f x)) (hf : has_fderiv_within_at f f' s x)
  (hst : maps_to f s t) :
  has_fderiv_within_at (h₁ ∘ f) (h₁' • f') s x :=
(has_deriv_at_filter.mono hh₁ $
  hf.continuous_within_at.tendsto_nhds_within hst).comp_has_fderiv_at_filter x hf

/-! ### Derivative of the composition of two scalar functions -/

theorem has_deriv_at_filter.comp
  (hh₁ : has_deriv_at_filter h₁ h₁' (h₂ x) (L.map h₂))
  (hh₂ : has_deriv_at_filter h₂ h₂' x L) :
  has_deriv_at_filter (h₁ ∘ h₂) (h₁' * h₂') x L :=
by { rw mul_comm, exact hh₁.scomp x hh₂ }

theorem has_deriv_within_at.comp {t : set 𝕜}
  (hh₁ : has_deriv_within_at h₁ h₁' t (h₂ x))
  (hh₂ : has_deriv_within_at h₂ h₂' s x) (hst : s ⊆ h₂ ⁻¹' t) :
  has_deriv_within_at (h₁ ∘ h₂) (h₁' * h₂') s x :=
by { rw mul_comm, exact hh₁.scomp x hh₂ hst, }

/-- The chain rule. -/
theorem has_deriv_at.comp
  (hh₁ : has_deriv_at h₁ h₁' (h₂ x)) (hh₂ : has_deriv_at h₂ h₂' x) :
  has_deriv_at (h₁ ∘ h₂) (h₁' * h₂') x :=
(hh₁.mono hh₂.continuous_at).comp x hh₂

theorem has_strict_deriv_at.comp
  (hh₁ : has_strict_deriv_at h₁ h₁' (h₂ x)) (hh₂ : has_strict_deriv_at h₂ h₂' x) :
  has_strict_deriv_at (h₁ ∘ h₂) (h₁' * h₂') x :=
by { rw mul_comm, exact hh₁.scomp x hh₂ }

theorem has_deriv_at.comp_has_deriv_within_at
  (hh₁ : has_deriv_at h₁ h₁' (h₂ x)) (hh₂ : has_deriv_within_at h₂ h₂' s x) :
  has_deriv_within_at (h₁ ∘ h₂) (h₁' * h₂') s x :=
begin
  rw ← has_deriv_within_at_univ at hh₁,
  exact has_deriv_within_at.comp x hh₁ hh₂ subset_preimage_univ
end

lemma deriv_within.comp
  (hh₁ : differentiable_within_at 𝕜 h₁ t (h₂ x)) (hh₂ : differentiable_within_at 𝕜 h₂ s x)
  (hs : s ⊆ h₂ ⁻¹' t) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (h₁ ∘ h₂) s x = deriv_within h₁ t (h₂ x) * deriv_within h₂ s x :=
begin
  apply has_deriv_within_at.deriv_within _ hxs,
  exact has_deriv_within_at.comp x (hh₁.has_deriv_within_at) (hh₂.has_deriv_within_at) hs
end

lemma deriv.comp
  (hh₁ : differentiable_at 𝕜 h₁ (h₂ x)) (hh₂ : differentiable_at 𝕜 h₂ x) :
  deriv (h₁ ∘ h₂) x = deriv h₁ (h₂ x) * deriv h₂ x :=
begin
  apply has_deriv_at.deriv,
  exact has_deriv_at.comp x hh₁.has_deriv_at hh₂.has_deriv_at
end

protected lemma has_deriv_at_filter.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
  (hf : has_deriv_at_filter f f' x L) (hL : tendsto f L L) (hx : f x = x) (n : ℕ) :
  has_deriv_at_filter (f^[n]) (f'^n) x L :=
begin
  have := hf.iterate hL hx n,
  rwa [continuous_linear_map.smul_right_one_pow] at this
end

protected lemma has_deriv_at.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
  (hf : has_deriv_at f f' x) (hx : f x = x) (n : ℕ) :
  has_deriv_at (f^[n]) (f'^n) x :=
begin
  have := has_fderiv_at.iterate hf hx n,
  rwa [continuous_linear_map.smul_right_one_pow] at this
end

protected lemma has_deriv_within_at.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
  (hf : has_deriv_within_at f f' s x) (hx : f x = x) (hs : maps_to f s s) (n : ℕ) :
  has_deriv_within_at (f^[n]) (f'^n) s x :=
begin
  have := has_fderiv_within_at.iterate hf hx hs n,
  rwa [continuous_linear_map.smul_right_one_pow] at this
end

protected lemma has_strict_deriv_at.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
  (hf : has_strict_deriv_at f f' x) (hx : f x = x) (n : ℕ) :
  has_strict_deriv_at (f^[n]) (f'^n) x :=
begin
  have := hf.iterate hx n,
  rwa [continuous_linear_map.smul_right_one_pow] at this
end

end composition

section composition_vector
/-! ### Derivative of the composition of a function between vector spaces and a function on `𝕜` -/

variables {l : F → E} {l' : F →L[𝕜] E}
variable (x)

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative within a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem has_fderiv_within_at.comp_has_deriv_within_at {t : set F}
  (hl : has_fderiv_within_at l l' t (f x)) (hf : has_deriv_within_at f f' s x) (hst : s ⊆ f ⁻¹' t) :
  has_deriv_within_at (l ∘ f) (l' (f')) s x :=
begin
  rw has_deriv_within_at_iff_has_fderiv_within_at,
  convert has_fderiv_within_at.comp x hl hf hst,
  ext,
  simp
end

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem has_fderiv_at.comp_has_deriv_at
  (hl : has_fderiv_at l l' (f x)) (hf : has_deriv_at f f' x) :
  has_deriv_at (l ∘ f) (l' (f')) x :=
begin
  rw has_deriv_at_iff_has_fderiv_at,
  convert has_fderiv_at.comp x hl hf,
  ext,
  simp
end

theorem has_fderiv_at.comp_has_deriv_within_at
  (hl : has_fderiv_at l l' (f x)) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (l ∘ f) (l' (f')) s x :=
begin
  rw ← has_fderiv_within_at_univ at hl,
  exact has_fderiv_within_at.comp_has_deriv_within_at x hl hf subset_preimage_univ
end

lemma fderiv_within.comp_deriv_within {t : set F}
  (hl : differentiable_within_at 𝕜 l t (f x)) (hf : differentiable_within_at 𝕜 f s x)
  (hs : s ⊆ f ⁻¹' t) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (l ∘ f) s x = (fderiv_within 𝕜 l t (f x) : F → E) (deriv_within f s x) :=
begin
  apply has_deriv_within_at.deriv_within _ hxs,
  exact (hl.has_fderiv_within_at).comp_has_deriv_within_at x (hf.has_deriv_within_at) hs
end

lemma fderiv.comp_deriv
  (hl : differentiable_at 𝕜 l (f x)) (hf : differentiable_at 𝕜 f x) :
  deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F → E) (deriv f x) :=
begin
  apply has_deriv_at.deriv _,
  exact (hl.has_fderiv_at).comp_has_deriv_at x (hf.has_deriv_at)
end

end composition_vector

section mul
/-! ### Derivative of the multiplication of two scalar functions -/
variables {c d : 𝕜 → 𝕜} {c' d' : 𝕜}

theorem has_deriv_within_at.mul
  (hc : has_deriv_within_at c c' s x) (hd : has_deriv_within_at d d' s x) :
  has_deriv_within_at (λ y, c y * d y) (c' * d x + c x * d') s x :=
begin
  convert hc.smul hd using 1,
  rw [smul_eq_mul, smul_eq_mul, add_comm]
end

theorem has_deriv_at.mul (hc : has_deriv_at c c' x) (hd : has_deriv_at d d' x) :
  has_deriv_at (λ y, c y * d y) (c' * d x + c x * d') x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.mul hd
end

theorem has_strict_deriv_at.mul
  (hc : has_strict_deriv_at c c' x) (hd : has_strict_deriv_at d d' x) :
  has_strict_deriv_at (λ y, c y * d y) (c' * d x + c x * d') x :=
begin
  convert hc.smul hd using 1,
  rw [smul_eq_mul, smul_eq_mul, add_comm]
end

lemma deriv_within_mul (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) :
  deriv_within (λ y, c y * d y) s x = deriv_within c s x * d x + c x * deriv_within d s x :=
(hc.has_deriv_within_at.mul hd.has_deriv_within_at).deriv_within hxs

@[simp] lemma deriv_mul (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) :
  deriv (λ y, c y * d y) x = deriv c x * d x + c x * deriv d x :=
(hc.has_deriv_at.mul hd.has_deriv_at).deriv

theorem has_deriv_within_at.mul_const (hc : has_deriv_within_at c c' s x) (d : 𝕜) :
  has_deriv_within_at (λ y, c y * d) (c' * d) s x :=
begin
  convert hc.mul (has_deriv_within_at_const x s d),
  rw [mul_zero, add_zero]
end

theorem has_deriv_at.mul_const (hc : has_deriv_at c c' x) (d : 𝕜) :
  has_deriv_at (λ y, c y * d) (c' * d) x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.mul_const d
end

theorem has_strict_deriv_at.mul_const (hc : has_strict_deriv_at c c' x) (d : 𝕜) :
  has_strict_deriv_at (λ y, c y * d) (c' * d) x :=
begin
  convert hc.mul (has_strict_deriv_at_const x d),
  rw [mul_zero, add_zero]
end

lemma deriv_within_mul_const (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (d : 𝕜) :
  deriv_within (λ y, c y * d) s x = deriv_within c s x * d :=
(hc.has_deriv_within_at.mul_const d).deriv_within hxs

lemma deriv_mul_const (hc : differentiable_at 𝕜 c x) (d : 𝕜) :
  deriv (λ y, c y * d) x = deriv c x * d :=
(hc.has_deriv_at.mul_const d).deriv

theorem has_deriv_within_at.const_mul (c : 𝕜) (hd : has_deriv_within_at d d' s x) :
  has_deriv_within_at (λ y, c * d y) (c * d') s x :=
begin
  convert (has_deriv_within_at_const x s c).mul hd,
  rw [zero_mul, zero_add]
end

theorem has_deriv_at.const_mul (c : 𝕜) (hd : has_deriv_at d d' x) :
  has_deriv_at (λ y, c * d y) (c * d') x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hd.const_mul c
end

theorem has_strict_deriv_at.const_mul (c : 𝕜) (hd : has_strict_deriv_at d d' x) :
  has_strict_deriv_at (λ y, c * d y) (c * d') x :=
begin
  convert (has_strict_deriv_at_const _ _).mul hd,
  rw [zero_mul, zero_add]
end

lemma deriv_within_const_mul (hxs : unique_diff_within_at 𝕜 s x)
  (c : 𝕜) (hd : differentiable_within_at 𝕜 d s x) :
  deriv_within (λ y, c * d y) s x = c * deriv_within d s x :=
(hd.has_deriv_within_at.const_mul c).deriv_within hxs

lemma deriv_const_mul (c : 𝕜) (hd : differentiable_at 𝕜 d x) :
  deriv (λ y, c * d y) x = c * deriv d x :=
(hd.has_deriv_at.const_mul c).deriv

end mul

section inverse
/-! ### Derivative of `x ↦ x⁻¹` -/

theorem has_strict_deriv_at_inv (hx : x ≠ 0) : has_strict_deriv_at has_inv.inv (-(x^2)⁻¹) x :=
begin
  suffices : is_o (λ p : 𝕜 × 𝕜, (p.1 - p.2) * ((x * x)⁻¹ - (p.1 * p.2)⁻¹))
    (λ (p : 𝕜 × 𝕜), (p.1 - p.2) * 1) (𝓝 (x, x)),
  { refine this.congr' _ (eventually_of_forall $ λ _, mul_one _),
    refine eventually.mono (mem_nhds_sets (is_open_ne.prod is_open_ne) ⟨hx, hx⟩) _,
    rintro ⟨y, z⟩ ⟨hy, hz⟩,
    simp only [mem_set_of_eq] at hy hz, -- hy : y ≠ 0, hz : z ≠ 0
    field_simp [hx, hy, hz], ring, },
  refine (is_O_refl (λ p : 𝕜 × 𝕜, p.1 - p.2) _).mul_is_o ((is_o_one_iff _).2 _),
  rw [← sub_self (x * x)⁻¹],
  exact tendsto_const_nhds.sub ((continuous_mul.tendsto (x, x)).inv' $ mul_ne_zero hx hx)
end

theorem has_deriv_at_inv (x_ne_zero : x ≠ 0) :
  has_deriv_at (λy, y⁻¹) (-(x^2)⁻¹) x :=
(has_strict_deriv_at_inv x_ne_zero).has_deriv_at

theorem has_deriv_within_at_inv (x_ne_zero : x ≠ 0) (s : set 𝕜) :
  has_deriv_within_at (λx, x⁻¹) (-(x^2)⁻¹) s x :=
(has_deriv_at_inv x_ne_zero).has_deriv_within_at

lemma differentiable_at_inv (x_ne_zero : x ≠ 0) :
  differentiable_at 𝕜 (λx, x⁻¹) x :=
(has_deriv_at_inv x_ne_zero).differentiable_at

lemma differentiable_within_at_inv (x_ne_zero : x ≠ 0) :
  differentiable_within_at 𝕜 (λx, x⁻¹) s x :=
(differentiable_at_inv x_ne_zero).differentiable_within_at

lemma differentiable_on_inv : differentiable_on 𝕜 (λx:𝕜, x⁻¹) {x | x ≠ 0} :=
λx hx, differentiable_within_at_inv hx

@[simp] lemma differentiable_at_inv_iff : differentiable_at 𝕜 (λx:𝕜, x⁻¹) x ↔ x ≠ 0 :=
⟨λ h, normed_field.continuous_at_inv_iff.1 h.continuous_at, differentiable_at_inv⟩

@[simp] lemma deriv_inv : deriv (λx, x⁻¹) x = -(x^2)⁻¹ :=
if hx : x = 0 then
  by { rw [deriv_zero_of_not_differentiable_at (mt differentiable_at_inv_iff.1 (not_not.2 hx)), hx],
       simp }
else (has_deriv_at_inv hx).deriv

lemma deriv_within_inv (x_ne_zero : x ≠ 0) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, x⁻¹) s x = -(x^2)⁻¹ :=
begin
  rw differentiable_at.deriv_within (differentiable_at_inv x_ne_zero) hxs,
  exact deriv_inv
end

lemma has_fderiv_at_inv (x_ne_zero : x ≠ 0) :
  has_fderiv_at (λx, x⁻¹) (smul_right (1 : 𝕜 →L[𝕜] 𝕜) (-(x^2)⁻¹) : 𝕜 →L[𝕜] 𝕜) x :=
has_deriv_at_inv x_ne_zero

lemma has_fderiv_within_at_inv (x_ne_zero : x ≠ 0) :
  has_fderiv_within_at (λx, x⁻¹) (smul_right (1 : 𝕜 →L[𝕜] 𝕜) (-(x^2)⁻¹) : 𝕜 →L[𝕜] 𝕜) s x :=
(has_fderiv_at_inv x_ne_zero).has_fderiv_within_at

lemma fderiv_inv (x_ne_zero : x ≠ 0) :
  fderiv 𝕜 (λx, x⁻¹) x = smul_right (1 : 𝕜 →L[𝕜] 𝕜) (-(x^2)⁻¹) :=
(has_fderiv_at_inv x_ne_zero).fderiv

lemma fderiv_within_inv (x_ne_zero : x ≠ 0) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λx, x⁻¹) s x = smul_right (1 : 𝕜 →L[𝕜] 𝕜) (-(x^2)⁻¹) :=
begin
  rw differentiable_at.fderiv_within (differentiable_at_inv x_ne_zero) hxs,
  exact fderiv_inv x_ne_zero
end

variables {c : 𝕜 → 𝕜} {c' : 𝕜}

lemma has_deriv_within_at.inv
  (hc : has_deriv_within_at c c' s x) (hx : c x ≠ 0) :
  has_deriv_within_at (λ y, (c y)⁻¹) (- c' / (c x)^2) s x :=
begin
  convert (has_deriv_at_inv hx).comp_has_deriv_within_at x hc,
  field_simp
end

lemma has_deriv_at.inv (hc : has_deriv_at c c' x) (hx : c x ≠ 0) :
  has_deriv_at (λ y, (c y)⁻¹) (- c' / (c x)^2) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hc.inv hx
end

lemma differentiable_within_at.inv (hc : differentiable_within_at 𝕜 c s x) (hx : c x ≠ 0) :
  differentiable_within_at 𝕜 (λx, (c x)⁻¹) s x :=
(hc.has_deriv_within_at.inv hx).differentiable_within_at

@[simp] lemma differentiable_at.inv (hc : differentiable_at 𝕜 c x) (hx : c x ≠ 0) :
  differentiable_at 𝕜 (λx, (c x)⁻¹) x :=
(hc.has_deriv_at.inv hx).differentiable_at

lemma differentiable_on.inv (hc : differentiable_on 𝕜 c s) (hx : ∀ x ∈ s, c x ≠ 0) :
  differentiable_on 𝕜 (λx, (c x)⁻¹) s :=
λx h, (hc x h).inv (hx x h)

@[simp] lemma differentiable.inv (hc : differentiable 𝕜 c) (hx : ∀ x, c x ≠ 0) :
  differentiable 𝕜 (λx, (c x)⁻¹) :=
λx, (hc x).inv (hx x)

lemma deriv_within_inv' (hc : differentiable_within_at 𝕜 c s x) (hx : c x ≠ 0)
  (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, (c x)⁻¹) s x = - (deriv_within c s x) / (c x)^2 :=
(hc.has_deriv_within_at.inv hx).deriv_within hxs

@[simp] lemma deriv_inv' (hc : differentiable_at 𝕜 c x) (hx : c x ≠ 0) :
  deriv (λx, (c x)⁻¹) x = - (deriv c x) / (c x)^2 :=
(hc.has_deriv_at.inv hx).deriv

end inverse

section division
/-! ### Derivative of `x ↦ c x / d x` -/

variables {c d : 𝕜 → 𝕜} {c' d' : 𝕜}

lemma has_deriv_within_at.div
  (hc : has_deriv_within_at c c' s x) (hd : has_deriv_within_at d d' s x) (hx : d x ≠ 0) :
  has_deriv_within_at (λ y, c y / d y) ((c' * d x - c x * d') / (d x)^2) s x :=
begin
  convert hc.mul ((has_deriv_at_inv hx).comp_has_deriv_within_at x hd),
  { simp only [div_eq_mul_inv] },
  { field_simp, ring }
end

lemma has_strict_deriv_at.div (hc : has_strict_deriv_at c c' x) (hd : has_strict_deriv_at d d' x)
  (hx : d x ≠ 0) :
  has_strict_deriv_at (λ y, c y / d y) ((c' * d x - c x * d') / (d x)^2) x :=
begin
  convert hc.mul ((has_strict_deriv_at_inv hx).comp x hd),
  { simp only [div_eq_mul_inv] },
  { field_simp, ring }
end

lemma has_deriv_at.div (hc : has_deriv_at c c' x) (hd : has_deriv_at d d' x) (hx : d x ≠ 0) :
  has_deriv_at (λ y, c y / d y) ((c' * d x - c x * d') / (d x)^2) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hc.div hd hx
end

lemma differentiable_within_at.div
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) (hx : d x ≠ 0) :
  differentiable_within_at 𝕜 (λx, c x / d x) s x :=
((hc.has_deriv_within_at).div (hd.has_deriv_within_at) hx).differentiable_within_at

@[simp] lemma differentiable_at.div
  (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) (hx : d x ≠ 0) :
  differentiable_at 𝕜 (λx, c x / d x) x :=
((hc.has_deriv_at).div (hd.has_deriv_at) hx).differentiable_at

lemma differentiable_on.div
  (hc : differentiable_on 𝕜 c s) (hd : differentiable_on 𝕜 d s) (hx : ∀ x ∈ s, d x ≠ 0) :
  differentiable_on 𝕜 (λx, c x / d x) s :=
λx h, (hc x h).div (hd x h) (hx x h)

@[simp] lemma differentiable.div
  (hc : differentiable 𝕜 c) (hd : differentiable 𝕜 d) (hx : ∀ x, d x ≠ 0) :
differentiable 𝕜 (λx, c x / d x) :=
λx, (hc x).div (hd x) (hx x)

lemma deriv_within_div
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) (hx : d x ≠ 0)
  (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, c x / d x) s x
    = ((deriv_within c s x) * d x - c x * (deriv_within d s x)) / (d x)^2 :=
((hc.has_deriv_within_at).div (hd.has_deriv_within_at) hx).deriv_within hxs

@[simp] lemma deriv_div
  (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) (hx : d x ≠ 0) :
  deriv (λx, c x / d x) x = ((deriv c x) * d x - c x * (deriv d x)) / (d x)^2 :=
((hc.has_deriv_at).div (hd.has_deriv_at) hx).deriv

lemma differentiable_within_at.div_const (hc : differentiable_within_at 𝕜 c s x) {d : 𝕜} :
  differentiable_within_at 𝕜 (λx, c x / d) s x :=
by simp [div_eq_inv_mul, differentiable_within_at.const_mul, hc]

@[simp] lemma differentiable_at.div_const (hc : differentiable_at 𝕜 c x) {d : 𝕜} :
  differentiable_at 𝕜 (λ x, c x / d) x :=
by simpa only [div_eq_mul_inv] using (hc.has_deriv_at.mul_const d⁻¹).differentiable_at

lemma differentiable_on.div_const (hc : differentiable_on 𝕜 c s) {d : 𝕜} :
  differentiable_on 𝕜 (λx, c x / d) s :=
by simp [div_eq_inv_mul, differentiable_on.const_mul, hc]

@[simp] lemma differentiable.div_const (hc : differentiable 𝕜 c) {d : 𝕜} :
  differentiable 𝕜 (λx, c x / d) :=
by simp [div_eq_inv_mul, differentiable.const_mul, hc]

lemma deriv_within_div_const (hc : differentiable_within_at 𝕜 c s x) {d : 𝕜}
  (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, c x / d) s x = (deriv_within c s x) / d :=
by simp [div_eq_inv_mul, deriv_within_const_mul, hc, hxs]

@[simp] lemma deriv_div_const (hc : differentiable_at 𝕜 c x) {d : 𝕜} :
  deriv (λx, c x / d) x = (deriv c x) / d :=
by simp [div_eq_inv_mul, deriv_const_mul, hc]

end division

theorem has_strict_deriv_at.has_strict_fderiv_at_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜}
  (hf : has_strict_deriv_at f f' x) (hf' : f' ≠ 0) :
  has_strict_fderiv_at f
    (continuous_linear_equiv.units_equiv_aut 𝕜 (units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
hf

theorem has_deriv_at.has_fderiv_at_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜}
  (hf : has_deriv_at f f' x) (hf' : f' ≠ 0) :
  has_fderiv_at f
    (continuous_linear_equiv.units_equiv_aut 𝕜 (units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
hf

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem has_strict_deriv_at.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜}
  (hg : continuous_at g a) (hf : has_strict_deriv_at f f' (g a)) (hf' : f' ≠ 0)
  (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
  has_strict_deriv_at g f'⁻¹ a :=
(hf.has_strict_fderiv_at_equiv hf').of_local_left_inverse hg hfg

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has a
nonzero derivative `f'` at `f.symm a` in the strict sense, then `f.symm` has the derivative `f'⁻¹`
at `a` in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
lemma local_homeomorph.has_strict_deriv_at_symm (f : local_homeomorph 𝕜 𝕜) {a f' : 𝕜}
  (ha : a ∈ f.target) (hf' : f' ≠ 0) (htff' : has_strict_deriv_at f f' (f.symm a)) :
  has_strict_deriv_at f.symm f'⁻¹ a :=
htff'.of_local_left_inverse (f.symm.continuous_at ha) hf' (f.eventually_right_inverse ha)

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem has_deriv_at.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜}
  (hg : continuous_at g a) (hf : has_deriv_at f f' (g a)) (hf' : f' ≠ 0)
  (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
  has_deriv_at g f'⁻¹ a :=
(hf.has_fderiv_at_equiv hf').of_local_left_inverse hg hfg

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
nonzero derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
lemma local_homeomorph.has_deriv_at_symm (f : local_homeomorph 𝕜 𝕜) {a f' : 𝕜}
  (ha : a ∈ f.target) (hf' : f' ≠ 0) (htff' : has_deriv_at f f' (f.symm a)) :
  has_deriv_at f.symm f'⁻¹ a :=
htff'.of_local_left_inverse (f.symm.continuous_at ha) hf' (f.eventually_right_inverse ha)

lemma has_deriv_at.eventually_ne (h : has_deriv_at f f' x) (hf' : f' ≠ 0) :
  ∀ᶠ z in 𝓝[{x}ᶜ] x, f z ≠ f x :=
(has_deriv_at_iff_has_fderiv_at.1 h).eventually_ne
  ⟨∥f'∥⁻¹, λ z, by field_simp [norm_smul, mt norm_eq_zero.1 hf']⟩

theorem not_differentiable_within_at_of_local_left_inverse_has_deriv_within_at_zero
  {f g : 𝕜 → 𝕜} {a : 𝕜} {s t : set 𝕜} (ha : a ∈ s) (hsu : unique_diff_within_at 𝕜 s a)
  (hf : has_deriv_within_at f 0 t (g a)) (hst : maps_to g s t) (hfg : f ∘ g =ᶠ[𝓝[s] a] id) :
  ¬differentiable_within_at 𝕜 g s a :=
begin
  intro hg,
  have := (hf.comp a hg.has_deriv_within_at hst).congr_of_eventually_eq_of_mem hfg.symm ha,
  simpa using hsu.eq_deriv _ this (has_deriv_within_at_id _ _)
end

theorem not_differentiable_at_of_local_left_inverse_has_deriv_at_zero
  {f g : 𝕜 → 𝕜} {a : 𝕜} (hf : has_deriv_at f 0 (g a)) (hfg : f ∘ g =ᶠ[𝓝 a] id) :
  ¬differentiable_at 𝕜 g a :=
begin
  intro hg,
  have := (hf.comp a hg.has_deriv_at).congr_of_eventually_eq hfg.symm,
  simpa using this.unique (has_deriv_at_id a)
end

end

namespace polynomial
/-! ### Derivative of a polynomial -/

variables {x : 𝕜} {s : set 𝕜}
variable (p : polynomial 𝕜)

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected lemma has_strict_deriv_at (x : 𝕜) :
  has_strict_deriv_at (λx, p.eval x) (p.derivative.eval x) x :=
begin
  apply p.induction_on,
  { simp [has_strict_deriv_at_const] },
  { assume p q hp hq,
    convert hp.add hq;
    simp },
  { assume n a h,
    convert h.mul (has_strict_deriv_at_id x),
    { ext y, simp [pow_add, mul_assoc] },
    { simp [pow_add], ring } }
end

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected lemma has_deriv_at (x : 𝕜) : has_deriv_at (λx, p.eval x) (p.derivative.eval x) x :=
(p.has_strict_deriv_at x).has_deriv_at

protected theorem has_deriv_within_at (x : 𝕜) (s : set 𝕜) :
  has_deriv_within_at (λx, p.eval x) (p.derivative.eval x) s x :=
(p.has_deriv_at x).has_deriv_within_at

protected lemma differentiable_at : differentiable_at 𝕜 (λx, p.eval x) x :=
(p.has_deriv_at x).differentiable_at

protected lemma differentiable_within_at : differentiable_within_at 𝕜 (λx, p.eval x) s x :=
p.differentiable_at.differentiable_within_at

protected lemma differentiable : differentiable 𝕜 (λx, p.eval x) :=
λx, p.differentiable_at

protected lemma differentiable_on : differentiable_on 𝕜 (λx, p.eval x) s :=
p.differentiable.differentiable_on

@[simp] protected lemma deriv : deriv (λx, p.eval x) x = p.derivative.eval x :=
(p.has_deriv_at x).deriv

protected lemma deriv_within (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, p.eval x) s x = p.derivative.eval x :=
begin
  rw differentiable_at.deriv_within p.differentiable_at hxs,
  exact p.deriv
end

protected lemma has_fderiv_at (x : 𝕜) :
  has_fderiv_at (λx, p.eval x) (smul_right (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) x :=
p.has_deriv_at x

protected lemma has_fderiv_within_at (x : 𝕜) :
  has_fderiv_within_at (λx, p.eval x) (smul_right (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) s x :=
(p.has_fderiv_at x).has_fderiv_within_at

@[simp] protected lemma fderiv :
  fderiv 𝕜 (λx, p.eval x) x = smul_right (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
(p.has_fderiv_at x).fderiv

protected lemma fderiv_within (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λx, p.eval x) s x = smul_right (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
(p.has_fderiv_within_at x).fderiv_within hxs

end polynomial

section pow
/-! ### Derivative of `x ↦ x^n` for `n : ℕ` -/
variables {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜}
variable {n : ℕ }

lemma has_strict_deriv_at_pow (n : ℕ) (x : 𝕜) :
  has_strict_deriv_at (λx, x^n) ((n : 𝕜) * x^(n-1)) x :=
begin
  convert (polynomial.C (1 : 𝕜) * (polynomial.X)^n).has_strict_deriv_at x,
  { simp },
  { rw [polynomial.derivative_C_mul_X_pow], simp }
end

lemma has_deriv_at_pow (n : ℕ) (x : 𝕜) : has_deriv_at (λx, x^n) ((n : 𝕜) * x^(n-1)) x :=
(has_strict_deriv_at_pow n x).has_deriv_at

theorem has_deriv_within_at_pow (n : ℕ) (x : 𝕜) (s : set 𝕜) :
  has_deriv_within_at (λx, x^n) ((n : 𝕜) * x^(n-1)) s x :=
(has_deriv_at_pow n x).has_deriv_within_at

lemma differentiable_at_pow : differentiable_at 𝕜 (λx, x^n) x :=
(has_deriv_at_pow n x).differentiable_at

lemma differentiable_within_at_pow : differentiable_within_at 𝕜 (λx, x^n) s x :=
differentiable_at_pow.differentiable_within_at

lemma differentiable_pow : differentiable 𝕜 (λx:𝕜, x^n) :=
λx, differentiable_at_pow

lemma differentiable_on_pow : differentiable_on 𝕜 (λx, x^n) s :=
differentiable_pow.differentiable_on

lemma deriv_pow : deriv (λx, x^n) x = (n : 𝕜) * x^(n-1) :=
(has_deriv_at_pow n x).deriv

@[simp] lemma deriv_pow' : deriv (λx, x^n) = λ x, (n : 𝕜) * x^(n-1) :=
funext $ λ x, deriv_pow

lemma deriv_within_pow (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, x^n) s x = (n : 𝕜) * x^(n-1) :=
(has_deriv_within_at_pow n x s).deriv_within hxs

lemma iter_deriv_pow' {k : ℕ} :
  deriv^[k] (λx:𝕜, x^n) = λ x, (∏ i in finset.range k, (n - i) : ℕ) * x^(n-k) :=
begin
  induction k with k ihk,
  { simp only [one_mul, finset.prod_range_zero, function.iterate_zero_apply, nat.sub_zero,
      nat.cast_one] },
  { simp only [function.iterate_succ_apply', ihk, finset.prod_range_succ],
    ext x,
    rw [((has_deriv_at_pow (n - k) x).const_mul _).deriv, nat.cast_mul, mul_left_comm, mul_assoc,
      nat.succ_eq_add_one, nat.sub_sub] }
end

lemma iter_deriv_pow {k : ℕ} :
  deriv^[k] (λx:𝕜, x^n) x = (∏ i in finset.range k, (n - i) : ℕ) * x^(n-k) :=
congr_fun iter_deriv_pow' x

lemma has_deriv_within_at.pow (hc : has_deriv_within_at c c' s x) :
  has_deriv_within_at (λ y, (c y)^n) ((n : 𝕜) * (c x)^(n-1) * c') s x :=
(has_deriv_at_pow n (c x)).comp_has_deriv_within_at x hc

lemma has_deriv_at.pow (hc : has_deriv_at c c' x) :
  has_deriv_at (λ y, (c y)^n) ((n : 𝕜) * (c x)^(n-1) * c') x :=
by { rw ← has_deriv_within_at_univ at *, exact hc.pow }

lemma differentiable_within_at.pow (hc : differentiable_within_at 𝕜 c s x) :
  differentiable_within_at 𝕜 (λx, (c x)^n) s x :=
hc.has_deriv_within_at.pow.differentiable_within_at

@[simp] lemma differentiable_at.pow (hc : differentiable_at 𝕜 c x) :
  differentiable_at 𝕜 (λx, (c x)^n) x :=
hc.has_deriv_at.pow.differentiable_at

lemma differentiable_on.pow (hc : differentiable_on 𝕜 c s) :
  differentiable_on 𝕜 (λx, (c x)^n) s :=
λx h, (hc x h).pow

@[simp] lemma differentiable.pow (hc : differentiable 𝕜 c) :
  differentiable 𝕜 (λx, (c x)^n) :=
λx, (hc x).pow

lemma deriv_within_pow' (hc : differentiable_within_at 𝕜 c s x)
  (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, (c x)^n) s x = (n : 𝕜) * (c x)^(n-1) * (deriv_within c s x) :=
hc.has_deriv_within_at.pow.deriv_within hxs

@[simp] lemma deriv_pow'' (hc : differentiable_at 𝕜 c x) :
  deriv (λx, (c x)^n) x = (n : 𝕜) * (c x)^(n-1) * (deriv c x) :=
hc.has_deriv_at.pow.deriv

end pow

section fpow
/-! ### Derivative of `x ↦ x^m` for `m : ℤ` -/
variables {x : 𝕜} {s : set 𝕜}
variable {m : ℤ}

lemma has_strict_deriv_at_fpow (m : ℤ) (hx : x ≠ 0 ∨ 0 ≤ m) :
  has_strict_deriv_at (λx, x^m) ((m : 𝕜) * x^(m-1)) x :=
begin
  have : ∀ m : ℤ, 0 < m → has_strict_deriv_at (λx, x^m) ((m:𝕜) * x^(m-1)) x,
  { assume m hm,
    lift m to ℕ using (le_of_lt hm),
    simp only [fpow_of_nat, int.cast_coe_nat],
    convert has_strict_deriv_at_pow _ _ using 2,
    rw [← int.coe_nat_one, ← int.coe_nat_sub, fpow_coe_nat],
    norm_cast at hm,
    exact nat.succ_le_of_lt hm },
  rcases lt_trichotomy m 0 with hm|hm|hm,
  { have hm' : ¬(0 ≤ m) := by simp [hm],
    have hx' : x ≠ 0 := hx.elim id (λ h, absurd h hm'),
    have := (has_strict_deriv_at_inv _).scomp _ (this (-m) (neg_pos.2 hm));
      [skip, exact fpow_ne_zero_of_ne_zero hx' _],
    simp only [(∘), fpow_neg, one_div, inv_inv', smul_eq_mul] at this,
    convert this using 1,
    rw [pow_two, mul_inv', inv_inv', int.cast_neg, ← neg_mul_eq_neg_mul, neg_mul_neg,
      ← fpow_add hx', mul_assoc, ← fpow_add hx'], congr, abel },
  { simp only [hm, fpow_zero, int.cast_zero, zero_mul, has_strict_deriv_at_const] },
  { exact this m hm }
end

lemma has_deriv_at_fpow (m : ℤ) (hx : x ≠ 0 ∨ 0 ≤ m) :
  has_deriv_at (λx, x^m) ((m : 𝕜) * x^(m-1)) x :=
(has_strict_deriv_at_fpow m hx).has_deriv_at

theorem has_deriv_within_at_fpow (m : ℤ) (hx : x ≠ 0 ∨ 0 ≤ m) (s : set 𝕜) :
  has_deriv_within_at (λx, x^m) ((m : 𝕜) * x^(m-1)) s x :=
(has_deriv_at_fpow m hx).has_deriv_within_at

lemma differentiable_at_fpow (hx : x ≠ 0 ∨ 0 ≤ m) : differentiable_at 𝕜 (λx, x^m) x :=
(has_deriv_at_fpow m hx).differentiable_at

lemma differentiable_within_at_fpow (hx : x ≠ 0 ∨ 0 ≤ m) :
  differentiable_within_at 𝕜 (λx, x^m) s x :=
(differentiable_at_fpow hx).differentiable_within_at

lemma differentiable_on_fpow (hs : (0:𝕜) ∉ s) : differentiable_on 𝕜 (λx, x^m) s :=
λ x hxs, differentiable_within_at_fpow (or.inl (λ hx, hs $ hx ▸ hxs))

@[simp] lemma differentiable_at_fpow_iff : differentiable_at 𝕜 (λx:𝕜, x^m) x ↔ (x ≠ 0 ∨ 0 ≤ m) :=
⟨λ h, normed_field.continuous_at_fpow_iff.1 h.continuous_at, differentiable_at_fpow⟩

@[simp] lemma deriv_fpow : deriv (λx, x^m) x = (m : 𝕜) * x^(m-1) :=
if hx : x ≠ 0 ∨ 0 ≤ m then
  (has_deriv_at_fpow m hx).deriv
else
  begin
    rw deriv_zero_of_not_differentiable_at (mt differentiable_at_fpow_iff.1 (hx)),
    push_neg at hx,
    have hm : m - 1 ≠ 0 := by linarith [hx.2],
    simp [hx.1, zero_fpow _ hm]
  end

lemma deriv_within_fpow (hxs : unique_diff_within_at 𝕜 s x) (hx : x ≠ 0) :
  deriv_within (λx, x^m) s x = (m : 𝕜) * x^(m-1) :=
(has_deriv_within_at_fpow m (or.inl hx) s).deriv_within hxs

lemma iter_deriv_fpow {k : ℕ} (hx : x ≠ 0) :
  deriv^[k] (λx:𝕜, x^m) x = (∏ i in finset.range k, (m - i) : ℤ) * x^(m-k) :=
begin
  induction k with k ihk generalizing x hx,
  { simp only [one_mul, finset.prod_range_zero, function.iterate_zero_apply, int.coe_nat_zero,
      sub_zero, int.cast_one] },
  { rw [function.iterate_succ', finset.prod_range_succ, int.cast_mul, mul_assoc, mul_left_comm,
      int.coe_nat_succ, ← sub_sub, ← ((has_deriv_at_fpow _ (or.inl hx)).const_mul _).deriv],
    exact filter.eventually_eq.deriv_eq (eventually.mono (mem_nhds_sets is_open_ne hx) @ihk) }
end

end fpow

/-! ### Upper estimates on liminf and limsup -/

section real

variables {f : ℝ → ℝ} {f' : ℝ} {s : set ℝ} {x : ℝ} {r : ℝ}

lemma has_deriv_within_at.limsup_slope_le (hf : has_deriv_within_at f f' s x) (hr : f' < r) :
  ∀ᶠ z in 𝓝[s \ {x}] x, (z - x)⁻¹ * (f z - f x) < r :=
has_deriv_within_at_iff_tendsto_slope.1 hf (mem_nhds_sets is_open_Iio hr)

lemma has_deriv_within_at.limsup_slope_le' (hf : has_deriv_within_at f f' s x)
  (hs : x ∉ s) (hr : f' < r) :
  ∀ᶠ z in 𝓝[s] x, (z - x)⁻¹ * (f z - f x) < r :=
(has_deriv_within_at_iff_tendsto_slope' hs).1 hf (mem_nhds_sets is_open_Iio hr)

lemma has_deriv_within_at.liminf_right_slope_le
  (hf : has_deriv_within_at f f' (Ici x) x) (hr : f' < r) :
  ∃ᶠ z in 𝓝[Ioi x] x, (z - x)⁻¹ * (f z - f x) < r :=
(hf.Ioi_of_Ici.limsup_slope_le' (lt_irrefl x) hr).frequently

end real

section real_space

open metric

variables {E : Type u} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {f' : E} {s : set ℝ}
  {x r : ℝ}

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ∥f'∥` the ratio
`∥f z - f x∥ / ∥z - x∥` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `∥f'∥`. -/
lemma has_deriv_within_at.limsup_norm_slope_le
  (hf : has_deriv_within_at f f' s x) (hr : ∥f'∥ < r) :
  ∀ᶠ z in 𝓝[s] x, ∥z - x∥⁻¹ * ∥f z - f x∥ < r :=
begin
  have hr₀ : 0 < r, from lt_of_le_of_lt (norm_nonneg f') hr,
  have A : ∀ᶠ z in 𝓝[s \ {x}] x, ∥(z - x)⁻¹ • (f z - f x)∥ ∈ Iio r,
    from (has_deriv_within_at_iff_tendsto_slope.1 hf).norm (mem_nhds_sets is_open_Iio hr),
  have B : ∀ᶠ z in 𝓝[{x}] x, ∥(z - x)⁻¹ • (f z - f x)∥ ∈ Iio r,
    from mem_sets_of_superset self_mem_nhds_within
      (singleton_subset_iff.2 $ by simp [hr₀]),
  have C := mem_sup_sets.2 ⟨A, B⟩,
  rw [← nhds_within_union, diff_union_self, nhds_within_union, mem_sup_sets] at C,
  filter_upwards [C.1],
  simp only [norm_smul, mem_Iio, normed_field.norm_inv],
  exact λ _, id
end

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ∥f'∥` the ratio
`(∥f z∥ - ∥f x∥) / ∥z - x∥` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `∥f'∥`.

This lemma is a weaker version of `has_deriv_within_at.limsup_norm_slope_le`
where `∥f z∥ - ∥f x∥` is replaced by `∥f z - f x∥`. -/
lemma has_deriv_within_at.limsup_slope_norm_le
  (hf : has_deriv_within_at f f' s x) (hr : ∥f'∥ < r) :
  ∀ᶠ z in 𝓝[s] x, ∥z - x∥⁻¹ * (∥f z∥ - ∥f x∥) < r :=
begin
  apply (hf.limsup_norm_slope_le hr).mono,
  assume z hz,
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_sub_norm_le _ _) _) hz,
  exact inv_nonneg.2 (norm_nonneg _)
end

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ∥f'∥` the ratio
`∥f z - f x∥ / ∥z - x∥` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `∥f'∥`. See also `has_deriv_within_at.limsup_norm_slope_le`
for a stronger version using limit superior and any set `s`. -/
lemma has_deriv_within_at.liminf_right_norm_slope_le
  (hf : has_deriv_within_at f f' (Ici x) x) (hr : ∥f'∥ < r) :
  ∃ᶠ z in 𝓝[Ioi x] x, ∥z - x∥⁻¹ * ∥f z - f x∥ < r :=
(hf.Ioi_of_Ici.limsup_norm_slope_le hr).frequently

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ∥f'∥` the ratio
`(∥f z∥ - ∥f x∥) / (z - x)` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `∥f'∥`.

See also

* `has_deriv_within_at.limsup_norm_slope_le` for a stronger version using
  limit superior and any set `s`;
* `has_deriv_within_at.liminf_right_norm_slope_le` for a stronger version using
  `∥f z - f x∥` instead of `∥f z∥ - ∥f x∥`. -/
lemma has_deriv_within_at.liminf_right_slope_norm_le
  (hf : has_deriv_within_at f f' (Ici x) x) (hr : ∥f'∥ < r) :
  ∃ᶠ z in 𝓝[Ioi x] x, (z - x)⁻¹ * (∥f z∥ - ∥f x∥) < r :=
begin
  have := (hf.Ioi_of_Ici.limsup_slope_norm_le hr).frequently,
  refine this.mp (eventually.mono self_mem_nhds_within _),
  assume z hxz hz,
  rwa [real.norm_eq_abs, abs_of_pos (sub_pos_of_lt hxz)] at hz
end

end real_space
