/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.mean_value
import analysis.calculus.formal_multilinear_series

/-!
# Higher differentiability

A function is `C^1` on a domain if it is differentiable there, and its derivative is continuous.
By induction, it is `C^n` if it is `C^{n-1}` and its (n-1)-th derivative is `C^1` there or,
equivalently, if it is `C^1` and its derivative is `C^{n-1}`.
Finally, it is `C^∞` if it is `C^n` for all n.

We formalize these notions by defining iteratively the `n+1`-th derivative of a function as the
derivative of the `n`-th derivative. It is called `iterated_fderiv 𝕜 n f x` where `𝕜` is the
field, `n` is the number of iterations, `f` is the function and `x` is the point, and it is given
as an `n`-multilinear map. We also define a version `iterated_fderiv_within` relative to a domain,
as well as predicates `times_cont_diff_within_at`, `times_cont_diff_at`, `times_cont_diff_on` and
`times_cont_diff` saying that the function is `C^n` within a set at a point, at a point, on a set
and on the whole space respectively.

To avoid the issue of choice when choosing a derivative in sets where the derivative is not
necessarily unique, `times_cont_diff_on` is not defined directly in terms of the
regularity of the specific choice `iterated_fderiv_within 𝕜 n f s` inside `s`, but in terms of the
existence of a nice sequence of derivatives, expressed with a predicate
`has_ftaylor_series_up_to_on`.

We prove basic properties of these notions.

## Main definitions and results
Let `f : E → F` be a map between normed vector spaces over a nondiscrete normed field `𝕜`.

* `has_ftaylor_series_up_to n f p`: expresses that the formal multilinear series `p` is a sequence
  of iterated derivatives of `f`, up to the `n`-th term (where `n` is a natural number or `∞`).
* `has_ftaylor_series_up_to_on n f p s`: same thing, but inside a set `s`. The notion of derivative
  is now taken inside `s`. In particular, derivatives don't have to be unique.
* `times_cont_diff 𝕜 n f`: expresses that `f` is `C^n`, i.e., it admits a Taylor series up to
  rank `n`.
* `times_cont_diff_on 𝕜 n f s`: expresses that `f` is `C^n` in `s`.
* `times_cont_diff_at 𝕜 n f x`: expresses that `f` is `C^n` around `x`.
* `times_cont_diff_within_at 𝕜 n f s x`: expresses that `f` is `C^n` around `x` within the set `s`.
* `iterated_fderiv_within 𝕜 n f s x` is an `n`-th derivative of `f` over the field `𝕜` on the
  set `s` at the point `x`. It is a continuous multilinear map from `E^n` to `F`, defined as a
  derivative within `s` of `iterated_fderiv_within 𝕜 (n-1) f s` if one exists, and `0` otherwise.
* `iterated_fderiv 𝕜 n f x` is the `n`-th derivative of `f` over the field `𝕜` at the point `x`.
  It is a continuous multilinear map from `E^n` to `F`, defined as a derivative of
  `iterated_fderiv 𝕜 (n-1) f` if one exists, and `0` otherwise.

In sets of unique differentiability, `times_cont_diff_on 𝕜 n f s` can be expressed in terms of the
properties of `iterated_fderiv_within 𝕜 m f s` for `m ≤ n`. In the whole space,
`times_cont_diff 𝕜 n f` can be expressed in terms of the properties of `iterated_fderiv 𝕜 m f`
for `m ≤ n`.

We also prove that the usual operations (addition, multiplication, difference, composition, and
so on) preserve `C^n` functions.

## Implementation notes

The definitions in this file are designed to work on any field `𝕜`. They are sometimes slightly more
complicated than the naive definitions one would guess from the intuition over the real or complex
numbers, but they are designed to circumvent the lack of gluing properties and partitions of unity
in general. In the usual situations, they coincide with the usual definitions.

### Definition of `C^n` functions in domains

One could define `C^n` functions in a domain `s` by fixing an arbitrary choice of derivatives (this
is what we do with `iterated_fderiv_within`) and requiring that all these derivatives up to `n` are
continuous. If the derivative is not unique, this could lead to strange behavior like two `C^n`
functions `f` and `g` on `s` whose sum is not `C^n`. A better definition is thus to say that a
function is `C^n` inside `s` if it admits a sequence of derivatives up to `n` inside `s`.

This definition still has the problem that a function which is locally `C^n` would not need to
be `C^n`, as different choices of sequences of derivatives around different points might possibly
not be glued together to give a globally defined sequence of derivatives. (Note that this issue
can not happen over reals, thanks to partition of unity, but the behavior over a general field is
not so clear, and we want a definition for general fields). Also, there are locality
problems for the order parameter: one could image a function which, for each `n`, has a nice
sequence of derivatives up to order `n`, but they do not coincide for varying `n` and can therefore
not be  glued to give rise to an infinite sequence of derivatives. This would give a function
which is `C^n` for all `n`, but not `C^∞`. We solve this issue by putting locality conditions
in space and order in our definition of `times_cont_diff_within_at` and `times_cont_diff_on`.
The resulting definition is slightly more complicated to work with (in fact not so much), but it
gives rise to completely satisfactory theorems.

For instance, with this definition, a real function which is `C^m` (but not better) on `(-1/m, 1/m)`
for each natural `m` is by definition `C^∞` at `0`.

There is another issue with the definition of `times_cont_diff_within_at 𝕜 n f s x`. We can
require the existence and good behavior of derivatives up to order `n` on a neighborhood of `x`
within `s`. However, this does not imply continuity or differentiability within `s` of the function
at `x` when `x` does not belong to `s`. Therefore, we require such existence and good behavior on
a neighborhood of `x` within `s ∪ {x}` (which appears as `insert x s` in this file).

### Side of the composition, and universe issues

With a naïve direct definition, the `n`-th derivative of a function belongs to the space
`E →L[𝕜] (E →L[𝕜] (E ... F)...)))` where there are n iterations of `E →L[𝕜]`. This space
may also be seen as the space of continuous multilinear functions on `n` copies of `E` with
values in `F`, by uncurrying. This is the point of view that is usually adopted in textbooks,
and that we also use. This means that the definition and the first proofs are slightly involved,
as one has to keep track of the uncurrying operation. The uncurrying can be done from the
left or from the right, amounting to defining the `n+1`-th derivative either as the derivative of
the `n`-th derivative, or as the `n`-th derivative of the derivative.
For proofs, it would be more convenient to use the latter approach (from the right),
as it means to prove things at the `n+1`-th step we only need to understand well enough the
derivative in `E →L[𝕜] F` (contrary to the approach from the left, where one would need to know
enough on the `n`-th derivative to deduce things on the `n+1`-th derivative).

However, the definition from the right leads to a universe polymorphism problem: if we define
`iterated_fderiv 𝕜 (n + 1) f x = iterated_fderiv 𝕜 n (fderiv 𝕜 f) x` by induction, we need to
generalize over all spaces (as `f` and `fderiv 𝕜 f` don't take values in the same space). It is
only possible to generalize over all spaces in some fixed universe in an inductive definition.
For `f : E → F`, then `fderiv 𝕜 f` is a map `E → (E →L[𝕜] F)`. Therefore, the definition will only
work if `F` and `E →L[𝕜] F` are in the same universe.

This issue does not appear with the definition from the left, where one does not need to generalize
over all spaces. Therefore, we use the definition from the left. This means some proofs later on
become a little bit more complicated: to prove that a function is `C^n`, the most efficient approach
is to exhibit a formula for its `n`-th derivative and prove it is continuous (contrary to the
inductive approach where one would prove smoothness statements without giving a formula for the
derivative). In the end, this approach is still satisfactory as it is good to have formulas for the
iterated derivatives in various constructions.

One point where we depart from this explicit approach is in the proof of smoothness of a
composition: there is a formula for the `n`-th derivative of a composition (Faà di Bruno's formula),
but it is very complicated and barely usable, while the inductive proof is very simple. Thus, we
give the inductive proof. As explained above, it works by generalizing over the target space, hence
it only works well if all spaces belong to the same universe. To get the general version, we lift
things to a common universe using a trick.

### Variables management

The textbook definitions and proofs use various identifications and abuse of notations, for instance
when saying that the natural space in which the derivative lives, i.e.,
`E →L[𝕜] (E →L[𝕜] ( ... →L[𝕜] F))`, is the same as a space of multilinear maps. When doing things
formally, we need to provide explicit maps for these identifications, and chase some diagrams to see
everything is compatible with the identifications. In particular, one needs to check that taking the
derivative and then doing the identification, or first doing the identification and then taking the
derivative, gives the same result. The key point for this is that taking the derivative commutes
with continuous linear equivalences. Therefore, we need to implement all our identifications with
continuous linear equivs.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `⊤ : with_top ℕ` with `∞`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

noncomputable theory
open_locale classical big_operators

local notation `∞` := (⊤ : with_top ℕ)

universes u v w

local attribute [instance, priority 1001]
normed_group.to_add_comm_group normed_space.to_semimodule add_comm_group.to_add_comm_monoid

open set fin
open_locale topological_space

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]
{s s₁ t u : set E} {f f₁ : E → F} {g : F → G} {x : E} {c : F}
{b : E × F → G}

/-! ### Functions with a Taylor series on a domain -/

variable {p : E → formal_multilinear_series 𝕜 E F}

/-- `has_ftaylor_series_up_to_on n f p s` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_within_at` but for higher order derivatives. -/
structure has_ftaylor_series_up_to_on (n : with_top ℕ)
  (f : E → F) (p : E → formal_multilinear_series 𝕜 E F) (s : set E) : Prop :=
(zero_eq       : ∀ x ∈ s, (p x 0).uncurry0 = f x)
(fderiv_within : ∀ (m : ℕ) (hm : (m : with_top ℕ) < n), ∀ x ∈ s,
   has_fderiv_within_at (λ y, p y m) (p x m.succ).curry_left s x)
(cont          : ∀ (m : ℕ) (hm : (m : with_top ℕ) ≤ n), continuous_on (λ x, p x m) s)

lemma has_ftaylor_series_up_to_on.zero_eq' {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) {x : E} (hx : x ∈ s) :
  p x 0 = (continuous_multilinear_curry_fin0 𝕜 E F).symm (f x) :=
by { rw ← h.zero_eq x hx, symmetry, exact continuous_multilinear_map.uncurry0_curry0 _ }

/-- If two functions coincide on a set `s`, then a Taylor series for the first one is as well a
Taylor series for the second one. -/
lemma has_ftaylor_series_up_to_on.congr {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) (h₁ : ∀ x ∈ s, f₁ x = f x) :
  has_ftaylor_series_up_to_on n f₁ p s :=
begin
  refine ⟨λ x hx, _, h.fderiv_within, h.cont⟩,
  rw h₁ x hx,
  exact h.zero_eq x hx
end

lemma has_ftaylor_series_up_to_on.mono {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) {t : set E} (hst : t ⊆ s) :
  has_ftaylor_series_up_to_on n f p t :=
⟨λ x hx, h.zero_eq x (hst hx),
λ m hm x hx, (h.fderiv_within m hm x (hst hx)).mono hst,
λ m hm, (h.cont m hm).mono hst⟩

lemma has_ftaylor_series_up_to_on.of_le {m n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) (hmn : m ≤ n) :
  has_ftaylor_series_up_to_on m f p s :=
⟨h.zero_eq,
λ k hk x hx, h.fderiv_within k (lt_of_lt_of_le hk hmn) x hx,
λ k hk, h.cont k (le_trans hk hmn)⟩

lemma has_ftaylor_series_up_to_on.continuous_on {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) : continuous_on f s :=
begin
  have := (h.cont 0 bot_le).congr (λ x hx, (h.zero_eq' hx).symm),
  rwa continuous_linear_equiv.comp_continuous_on_iff at this
end

lemma has_ftaylor_series_up_to_on_zero_iff :
  has_ftaylor_series_up_to_on 0 f p s ↔ continuous_on f s ∧ (∀ x ∈ s, (p x 0).uncurry0 = f x) :=
begin
  refine ⟨λ H, ⟨H.continuous_on, H.zero_eq⟩,
          λ H, ⟨H.2, λ m hm, false.elim (not_le.2 hm bot_le), _⟩⟩,
  assume m hm,
  have : (m : with_top ℕ) = ((0 : ℕ) : with_bot ℕ) := le_antisymm hm bot_le,
  rw with_top.coe_eq_coe at this,
  rw this,
  have : ∀ x ∈ s, p x 0 = (continuous_multilinear_curry_fin0 𝕜 E F).symm (f x),
    by { assume x hx, rw ← H.2 x hx, symmetry, exact continuous_multilinear_map.uncurry0_curry0 _ },
  rw [continuous_on_congr this, continuous_linear_equiv.comp_continuous_on_iff],
  exact H.1
end

lemma has_ftaylor_series_up_to_on_top_iff :
  (has_ftaylor_series_up_to_on ∞ f p s) ↔ (∀ (n : ℕ), has_ftaylor_series_up_to_on n f p s) :=
begin
  split,
  { assume H n, exact H.of_le le_top },
  { assume H,
    split,
    { exact (H 0).zero_eq },
    { assume m hm,
      apply (H m.succ).fderiv_within m (with_top.coe_lt_coe.2 (lt_add_one m)) },
    { assume m hm,
      apply (H m).cont m (le_refl _) } }
end

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
lemma has_ftaylor_series_up_to_on.has_fderiv_within_at {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) (hx : x ∈ s) :
  has_fderiv_within_at f (continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) s x :=
begin
  have A : ∀ y ∈ s, f y = (continuous_multilinear_curry_fin0 𝕜 E F) (p y 0),
  { assume y hy, rw ← h.zero_eq y hy, refl },
  suffices H : has_fderiv_within_at
      (λ y, continuous_multilinear_curry_fin0 𝕜 E F (p y 0))
      (continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) s x,
    by exact H.congr A (A x hx),
  rw continuous_linear_equiv.comp_has_fderiv_within_at_iff',
  have : ((0 : ℕ) : with_top ℕ) < n :=
    lt_of_lt_of_le (with_top.coe_lt_coe.2 nat.zero_lt_one) hn,
  convert h.fderiv_within _ this x hx,
  ext y v,
  change (p x 1) (snoc 0 y) = (p x 1) (cons y v),
  unfold_coes,
  congr' with i,
  rw unique.eq_default i,
  refl
end

lemma has_ftaylor_series_up_to_on.differentiable_on {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) : differentiable_on 𝕜 f s :=
λ x hx, (h.has_fderiv_within_at hn hx).differentiable_within_at

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p` is a Taylor series up to `n`, and
`p (n + 1)` is a derivative of `p n`. -/
theorem has_ftaylor_series_up_to_on_succ_iff_left {n : ℕ} :
  has_ftaylor_series_up_to_on (n + 1) f p s ↔
  has_ftaylor_series_up_to_on n f p s
  ∧ (∀ x ∈ s, has_fderiv_within_at (λ y, p y n) (p x n.succ).curry_left s x)
  ∧ continuous_on (λ x, p x (n + 1)) s :=
begin
  split,
  { assume h,
    exact ⟨h.of_le (with_top.coe_le_coe.2 (nat.le_succ n)),
           h.fderiv_within _ (with_top.coe_lt_coe.2 (lt_add_one n)),
           h.cont (n + 1) (le_refl _)⟩ },
  { assume h,
    split,
    { exact h.1.zero_eq },
    { assume m hm,
      by_cases h' : m < n,
      { exact h.1.fderiv_within m (with_top.coe_lt_coe.2 h') },
      { have : m = n := nat.eq_of_lt_succ_of_not_lt (with_top.coe_lt_coe.1 hm) h',
        rw this,
        exact h.2.1 } },
    { assume m hm,
      by_cases h' : m ≤ n,
      { apply h.1.cont m (with_top.coe_le_coe.2 h') },
      { have : m = (n + 1) := le_antisymm (with_top.coe_le_coe.1 hm) (not_le.1 h'),
        rw this,
        exact h.2.2 } } }
end

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem has_ftaylor_series_up_to_on_succ_iff_right {n : ℕ} :
  has_ftaylor_series_up_to_on ((n + 1) : ℕ) f p s ↔
  (∀ x ∈ s, (p x 0).uncurry0 = f x)
  ∧ (∀ x ∈ s, has_fderiv_within_at (λ y, p y 0) (p x 1).curry_left s x)
  ∧ has_ftaylor_series_up_to_on n
    (λ x, continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) (λ x, (p x).shift) s :=
begin
  split,
  { assume H,
    refine ⟨H.zero_eq, H.fderiv_within 0 (with_top.coe_lt_coe.2 (nat.succ_pos n)), _⟩,
    split,
    { assume x hx, refl },
    { assume m (hm : (m : with_top ℕ) < n) x (hx : x ∈ s),
      have A : (m.succ : with_top ℕ) < n.succ,
        by { rw with_top.coe_lt_coe at ⊢ hm, exact nat.lt_succ_iff.mpr hm },
      change has_fderiv_within_at
        ((continuous_multilinear_curry_right_equiv' 𝕜 m E F).symm
           ∘ (λ (y : E), p y m.succ))
        (p x m.succ.succ).curry_right.curry_left s x,
      rw continuous_linear_equiv.comp_has_fderiv_within_at_iff',
      convert H.fderiv_within _ A x hx,
      ext y v,
      change (p x m.succ.succ) (snoc (cons y (init v)) (v (last _)))
        = (p x (nat.succ (nat.succ m))) (cons y v),
      rw [← cons_snoc_eq_snoc_cons, snoc_init_self] },
    { assume m (hm : (m : with_top ℕ) ≤ n),
      have A : (m.succ : with_top ℕ) ≤ n.succ,
        by { rw with_top.coe_le_coe at ⊢ hm, exact nat.pred_le_iff.mp hm },
      change continuous_on ((continuous_multilinear_curry_right_equiv' 𝕜 m E F).symm
           ∘ (λ (y : E), p y m.succ)) s,
      rw continuous_linear_equiv.comp_continuous_on_iff,
      exact H.cont _ A } },
  { rintros ⟨Hzero_eq, Hfderiv_zero, Htaylor⟩,
    split,
    { exact Hzero_eq },
    { assume m (hm : (m : with_top ℕ) < n.succ) x (hx : x ∈ s),
      cases m,
      { exact Hfderiv_zero x hx },
      { have A : (m : with_top ℕ) < n,
          by { rw with_top.coe_lt_coe at hm ⊢, exact nat.lt_of_succ_lt_succ hm },
        have : has_fderiv_within_at ((continuous_multilinear_curry_right_equiv' 𝕜 m E F).symm
           ∘ (λ (y : E), p y m.succ)) ((p x).shift m.succ).curry_left s x :=
          Htaylor.fderiv_within _ A x hx,
        rw continuous_linear_equiv.comp_has_fderiv_within_at_iff' at this,
        convert this,
        ext y v,
        change (p x (nat.succ (nat.succ m))) (cons y v)
          = (p x m.succ.succ) (snoc (cons y (init v)) (v (last _))),
        rw [← cons_snoc_eq_snoc_cons, snoc_init_self] } },
    { assume m (hm : (m : with_top ℕ) ≤ n.succ),
      cases m,
      { have : differentiable_on 𝕜 (λ x, p x 0) s :=
          λ x hx, (Hfderiv_zero x hx).differentiable_within_at,
        exact this.continuous_on },
      { have A : (m : with_top ℕ) ≤ n,
          by { rw with_top.coe_le_coe at hm ⊢, exact nat.lt_succ_iff.mp hm },
        have : continuous_on ((continuous_multilinear_curry_right_equiv' 𝕜 m E F).symm
           ∘ (λ (y : E), p y m.succ)) s :=
        Htaylor.cont _ A,
        rwa continuous_linear_equiv.comp_continuous_on_iff at this } } }
end

/-! ### Smooth functions within a set around a point -/

variable (𝕜)

/-- A function is continuously differentiable up to order `n` within a set `s` at a point `x` if
it admits continuous derivatives up to order `n` in a neighborhood of `x` in `s ∪ {x}`.
For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).

For instance, a real function which is `C^m` on `(-1/m, 1/m)` for each natural `m`, but not
better, is `C^∞` at `0` within `univ`.
-/
def times_cont_diff_within_at (n : with_top ℕ) (f : E → F) (s : set E) (x : E) :=
∀ (m : ℕ), (m : with_top ℕ) ≤ n →
  ∃ u ∈ 𝓝[insert x s] x, ∃ p : E → formal_multilinear_series 𝕜 E F,
    has_ftaylor_series_up_to_on m f p u

variable {𝕜}

lemma times_cont_diff_within_at_nat {n : ℕ} :
  times_cont_diff_within_at 𝕜 n f s x ↔
  ∃ u ∈ 𝓝[insert x s] x, ∃ p : E → formal_multilinear_series 𝕜 E F,
  has_ftaylor_series_up_to_on n f p u :=
⟨λ H, H n (le_refl _), λ ⟨u, hu, p, hp⟩ m hm, ⟨u, hu, p, hp.of_le hm⟩⟩

lemma times_cont_diff_within_at.of_le {m n : with_top ℕ}
  (h : times_cont_diff_within_at 𝕜 n f s x) (hmn : m ≤ n) :
  times_cont_diff_within_at 𝕜 m f s x :=
λ k hk, h k (le_trans hk hmn)

lemma times_cont_diff_within_at_iff_forall_nat_le {n : with_top ℕ} :
  times_cont_diff_within_at 𝕜 n f s x ↔ ∀ m : ℕ, ↑m ≤ n → times_cont_diff_within_at 𝕜 m f s x :=
⟨λ H m hm, H.of_le hm, λ H m hm, H m hm _ le_rfl⟩

lemma times_cont_diff_within_at_top :
  times_cont_diff_within_at 𝕜 ∞ f s x ↔ ∀ (n : ℕ), times_cont_diff_within_at 𝕜 n f s x :=
times_cont_diff_within_at_iff_forall_nat_le.trans $ by simp only [forall_prop_of_true, le_top]

lemma times_cont_diff_within_at.continuous_within_at {n : with_top ℕ}
  (h : times_cont_diff_within_at 𝕜 n f s x) : continuous_within_at f s x :=
begin
  rcases h 0 bot_le with ⟨u, hu, p, H⟩,
  rw [mem_nhds_within_insert] at hu,
  exact (H.continuous_on.continuous_within_at hu.1).mono_of_mem hu.2
end

lemma times_cont_diff_within_at.congr_of_eventually_eq {n : with_top ℕ}
  (h : times_cont_diff_within_at 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  times_cont_diff_within_at 𝕜 n f₁ s x :=
λ m hm, let ⟨u, hu, p, H⟩ := h m hm in
⟨{x ∈ u | f₁ x = f x}, filter.inter_mem_sets hu (mem_nhds_within_insert.2 ⟨hx, h₁⟩), p,
  (H.mono (sep_subset _ _)).congr (λ _, and.right)⟩

lemma times_cont_diff_within_at.congr_of_eventually_eq' {n : with_top ℕ}
  (h : times_cont_diff_within_at 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
  times_cont_diff_within_at 𝕜 n f₁ s x :=
h.congr_of_eventually_eq h₁ $ h₁.self_of_nhds_within hx

lemma filter.eventually_eq.times_cont_diff_within_at_iff {n : with_top ℕ}
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  times_cont_diff_within_at 𝕜 n f₁ s x ↔ times_cont_diff_within_at 𝕜 n f s x :=
⟨λ H, times_cont_diff_within_at.congr_of_eventually_eq H h₁.symm hx.symm,
λ H, H.congr_of_eventually_eq h₁ hx⟩

lemma times_cont_diff_within_at.congr {n : with_top ℕ}
  (h : times_cont_diff_within_at 𝕜 n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
  times_cont_diff_within_at 𝕜 n f₁ s x :=
h.congr_of_eventually_eq (filter.eventually_eq_of_mem self_mem_nhds_within h₁) hx

lemma times_cont_diff_within_at.mono_of_mem {n : with_top ℕ}
  (h : times_cont_diff_within_at 𝕜 n f s x) {t : set E} (hst : s ∈ 𝓝[t] x) :
  times_cont_diff_within_at 𝕜 n f t x :=
begin
  assume m hm,
  rcases h m hm with ⟨u, hu, p, H⟩,
  exact ⟨u, nhds_within_le_of_mem (insert_mem_nhds_within_insert hst) hu, p, H⟩
end

lemma times_cont_diff_within_at.mono {n : with_top ℕ}
  (h : times_cont_diff_within_at 𝕜 n f s x) {t : set E} (hst : t ⊆ s) :
  times_cont_diff_within_at 𝕜 n f t x :=
h.mono_of_mem $ filter.mem_sets_of_superset self_mem_nhds_within hst

lemma times_cont_diff_within_at.congr_nhds {n : with_top ℕ}
  (h : times_cont_diff_within_at 𝕜 n f s x) {t : set E} (hst : 𝓝[s] x = 𝓝[t] x) :
  times_cont_diff_within_at 𝕜 n f t x :=
h.mono_of_mem $ hst ▸ self_mem_nhds_within

lemma times_cont_diff_within_at_congr_nhds {n : with_top ℕ} {t : set E} (hst : 𝓝[s] x = 𝓝[t] x) :
  times_cont_diff_within_at 𝕜 n f s x ↔ times_cont_diff_within_at 𝕜 n f t x :=
⟨λ h, h.congr_nhds hst, λ h, h.congr_nhds hst.symm⟩

lemma times_cont_diff_within_at_inter' {n : with_top ℕ} (h : t ∈ 𝓝[s] x) :
  times_cont_diff_within_at 𝕜 n f (s ∩ t) x ↔ times_cont_diff_within_at 𝕜 n f s x :=
times_cont_diff_within_at_congr_nhds $ eq.symm $ nhds_within_restrict'' _ h

lemma times_cont_diff_within_at_inter {n : with_top ℕ} (h : t ∈ 𝓝 x) :
  times_cont_diff_within_at 𝕜 n f (s ∩ t) x ↔ times_cont_diff_within_at 𝕜 n f s x :=
times_cont_diff_within_at_inter' (mem_nhds_within_of_mem_nhds h)

/-- If a function is `C^n` within a set at a point, with `n ≥ 1`, then it is differentiable
within this set at this point. -/
lemma times_cont_diff_within_at.differentiable_within_at' {n : with_top ℕ}
  (h : times_cont_diff_within_at 𝕜 n f s x) (hn : 1 ≤ n) :
  differentiable_within_at 𝕜 f (insert x s) x :=
begin
  rcases h 1 hn with ⟨u, hu, p, H⟩,
  rcases mem_nhds_within.1 hu with ⟨t, t_open, xt, tu⟩,
  rw inter_comm at tu,
  have := ((H.mono tu).differentiable_on (le_refl _)) x ⟨mem_insert x s, xt⟩,
  exact (differentiable_within_at_inter (mem_nhds_sets t_open xt)).1 this,
end

lemma times_cont_diff_within_at.differentiable_within_at {n : with_top ℕ}
  (h : times_cont_diff_within_at 𝕜 n f s x) (hn : 1 ≤ n) :
  differentiable_within_at 𝕜 f s x :=
(h.differentiable_within_at' hn).mono  (subset_insert x s)

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem times_cont_diff_within_at_succ_iff_has_fderiv_within_at {n : ℕ} :
  times_cont_diff_within_at 𝕜 ((n + 1) : ℕ) f s x
  ↔ ∃ u ∈ 𝓝[insert x s] x, ∃ f' : E → (E →L[𝕜] F),
    (∀ x ∈ u, has_fderiv_within_at f (f' x) u x) ∧ (times_cont_diff_within_at 𝕜 n f' u x) :=
begin
  split,
  { assume h,
    rcases h n.succ (le_refl _) with ⟨u, hu, p, Hp⟩,
    refine ⟨u, hu, λ y, (continuous_multilinear_curry_fin1 𝕜 E F) (p y 1),
      λ y hy, Hp.has_fderiv_within_at (with_top.coe_le_coe.2 (nat.le_add_left 1 n)) hy, _⟩,
    assume m hm,
    refine ⟨u, _, λ (y : E), (p y).shift, _⟩,
    { convert self_mem_nhds_within,
      have : x ∈ insert x s, by simp,
      exact (insert_eq_of_mem (mem_of_mem_nhds_within this hu)) },
    { rw has_ftaylor_series_up_to_on_succ_iff_right at Hp,
      exact Hp.2.2.of_le hm } },
  { rintros ⟨u, hu, f', f'_eq_deriv, Hf'⟩,
    rw times_cont_diff_within_at_nat,
    rcases Hf' n (le_refl _) with ⟨v, hv, p', Hp'⟩,
    refine ⟨v ∩ u, _, λ x, (p' x).unshift (f x), _⟩,
    { apply filter.inter_mem_sets _ hu,
      apply nhds_within_le_of_mem hu,
      exact nhds_within_mono _ (subset_insert x u) hv },
    { rw has_ftaylor_series_up_to_on_succ_iff_right,
      refine ⟨λ y hy, rfl, λ y hy, _, _⟩,
      { change has_fderiv_within_at (λ (z : E), (continuous_multilinear_curry_fin0 𝕜 E F).symm (f z))
          ((formal_multilinear_series.unshift (p' y) (f y) 1).curry_left) (v ∩ u) y,
        rw continuous_linear_equiv.comp_has_fderiv_within_at_iff',
        convert (f'_eq_deriv y hy.2).mono (inter_subset_right v u),
        rw ← Hp'.zero_eq y hy.1,
        ext z,
        change ((p' y 0) (init (@cons 0 (λ i, E) z 0))) (@cons 0 (λ i, E) z 0 (last 0))
          = ((p' y 0) 0) z,
        unfold_coes,
        congr },
      { convert (Hp'.mono (inter_subset_left v u)).congr (λ x hx, Hp'.zero_eq x hx.1),
        { ext x y,
          change p' x 0 (init (@snoc 0 (λ i : fin 1, E) 0 y)) y = p' x 0 0 y,
          rw init_snoc },
        { ext x k v y,
          change p' x k (init (@snoc k (λ i : fin k.succ, E) v y))
            (@snoc k (λ i : fin k.succ, E) v y (last k)) = p' x k v y,
          rw [snoc_last, init_snoc] } } } }
end

/-! ### Smooth functions within a set -/

variable (𝕜)

/-- A function is continuously differentiable up to `n` on `s` if, for any point `x` in `s`, it
admits continuous derivatives up to order `n` on a neighborhood of `x` in `s`.

For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
-/
definition times_cont_diff_on (n : with_top ℕ) (f : E → F) (s : set E) :=
∀ x ∈ s, times_cont_diff_within_at 𝕜 n f s x

variable {𝕜}

lemma times_cont_diff_on.times_cont_diff_within_at {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hx : x ∈ s) :
  times_cont_diff_within_at 𝕜 n f s x :=
h x hx

lemma times_cont_diff_within_at.times_cont_diff_on {n : with_top ℕ} {m : ℕ}
  (hm : (m : with_top ℕ) ≤ n) (h : times_cont_diff_within_at 𝕜 n f s x) :
  ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ times_cont_diff_on 𝕜 m f u :=
begin
  rcases h m hm with ⟨u, u_nhd, p, hp⟩,
  refine ⟨u ∩ insert x s, filter.inter_mem_sets u_nhd self_mem_nhds_within,
    inter_subset_right _ _, _⟩,
  assume y hy m' hm',
  refine ⟨u ∩ insert x s, _, p, (hp.mono (inter_subset_left _ _)).of_le hm'⟩,
  convert self_mem_nhds_within,
  exact insert_eq_of_mem hy
end

lemma times_cont_diff_on.of_le {m n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hmn : m ≤ n) :
  times_cont_diff_on 𝕜 m f s :=
λ x hx, (h x hx).of_le hmn

lemma times_cont_diff_on_iff_forall_nat_le {n : with_top ℕ} :
  times_cont_diff_on 𝕜 n f s ↔ ∀ m : ℕ, ↑m ≤ n → times_cont_diff_on 𝕜 m f s :=
⟨λ H m hm, H.of_le hm, λ H x hx m hm, H m hm x hx m le_rfl⟩

lemma times_cont_diff_on_top :
  times_cont_diff_on 𝕜 ∞ f s ↔ ∀ (n : ℕ), times_cont_diff_on 𝕜 n f s :=
times_cont_diff_on_iff_forall_nat_le.trans $ by simp only [le_top, forall_prop_of_true]

lemma times_cont_diff_on_all_iff_nat :
  (∀ n, times_cont_diff_on 𝕜 n f s) ↔ (∀ n : ℕ, times_cont_diff_on 𝕜 n f s) :=
begin
  refine ⟨λ H n, H n, _⟩,
  rintro H (_|n),
  exacts [times_cont_diff_on_top.2 H, H n]
end

lemma times_cont_diff_on.continuous_on {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) : continuous_on f s :=
λ x hx, (h x hx).continuous_within_at

lemma times_cont_diff_on.congr {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (h₁ : ∀ x ∈ s, f₁ x = f x) :
  times_cont_diff_on 𝕜 n f₁ s :=
λ x hx, (h x hx).congr h₁ (h₁ x hx)

lemma times_cont_diff_on_congr {n : with_top ℕ} (h₁ : ∀ x ∈ s, f₁ x = f x) :
  times_cont_diff_on 𝕜 n f₁ s ↔ times_cont_diff_on 𝕜 n f s :=
⟨λ H, H.congr (λ x hx, (h₁ x hx).symm), λ H, H.congr h₁⟩

lemma times_cont_diff_on.mono {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) {t : set E} (hst : t ⊆ s) :
  times_cont_diff_on 𝕜 n f t :=
λ x hx, (h x (hst hx)).mono hst

lemma times_cont_diff_on.congr_mono {n : with_top ℕ}
  (hf : times_cont_diff_on 𝕜 n f s) (h₁ : ∀ x ∈ s₁, f₁ x = f x) (hs : s₁ ⊆ s) :
  times_cont_diff_on 𝕜 n f₁ s₁ :=
(hf.mono hs).congr h₁

/-- If a function is `C^n` on a set with `n ≥ 1`, then it is differentiable there. -/
lemma times_cont_diff_on.differentiable_on {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hn : 1 ≤ n) : differentiable_on 𝕜 f s :=
λ x hx, (h x hx).differentiable_within_at hn

/-- If a function is `C^n` around each point in a set, then it is `C^n` on the set. -/
lemma times_cont_diff_on_of_locally_times_cont_diff_on {n : with_top ℕ}
  (h : ∀ x ∈ s, ∃u, is_open u ∧ x ∈ u ∧ times_cont_diff_on 𝕜 n f (s ∩ u)) :
  times_cont_diff_on 𝕜 n f s :=
begin
  assume x xs,
  rcases h x xs with ⟨u, u_open, xu, hu⟩,
  apply (times_cont_diff_within_at_inter _).1 (hu x ⟨xs, xu⟩),
  exact mem_nhds_sets u_open xu
end

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem times_cont_diff_on_succ_iff_has_fderiv_within_at {n : ℕ} :
  times_cont_diff_on 𝕜 ((n + 1) : ℕ) f s
  ↔ ∀ x ∈ s, ∃ u ∈ 𝓝[insert x s] x, ∃ f' : E → (E →L[𝕜] F),
    (∀ x ∈ u, has_fderiv_within_at f (f' x) u x) ∧ (times_cont_diff_on 𝕜 n f' u) :=
begin
  split,
  { assume h x hx,
    rcases (h x hx) n.succ (le_refl _) with ⟨u, hu, p, Hp⟩,
    refine ⟨u, hu, λ y, (continuous_multilinear_curry_fin1 𝕜 E F) (p y 1),
      λ y hy, Hp.has_fderiv_within_at (with_top.coe_le_coe.2 (nat.le_add_left 1 n)) hy, _⟩,
    rw has_ftaylor_series_up_to_on_succ_iff_right at Hp,
    assume z hz m hm,
    refine ⟨u, _, λ (x : E), (p x).shift, Hp.2.2.of_le hm⟩,
    convert self_mem_nhds_within,
    exact insert_eq_of_mem hz, },
  { assume h x hx,
    rw times_cont_diff_within_at_succ_iff_has_fderiv_within_at,
    rcases h x hx with ⟨u, u_nhbd, f', hu, hf'⟩,
    have : x ∈ u := mem_of_mem_nhds_within (mem_insert _ _) u_nhbd,
    exact ⟨u, u_nhbd, f', hu, hf' x this⟩ }
end

/-! ### Iterated derivative within a set -/
variable (𝕜)

/--
The `n`-th derivative of a function along a set, defined inductively by saying that the `n+1`-th
derivative of `f` is the derivative of the `n`-th derivative of `f` along this set, together with
an uncurrying step to see it as a multilinear map in `n+1` variables..
-/
noncomputable def iterated_fderiv_within (n : ℕ) (f : E → F) (s : set E) :
  E → (E [×n]→L[𝕜] F) :=
nat.rec_on n
  (λ x, continuous_multilinear_map.curry0 𝕜 E (f x))
  (λ n rec x, continuous_linear_map.uncurry_left (fderiv_within 𝕜 rec s x))

/-- Formal Taylor series associated to a function within a set. -/
def ftaylor_series_within (f : E → F) (s : set E) (x : E) : formal_multilinear_series 𝕜 E F :=
λ n, iterated_fderiv_within 𝕜 n f s x

variable {𝕜}

@[simp] lemma iterated_fderiv_within_zero_apply (m : (fin 0) → E) :
  (iterated_fderiv_within 𝕜 0 f s x : ((fin 0) →  E) → F) m = f x := rfl

lemma iterated_fderiv_within_zero_eq_comp :
  iterated_fderiv_within 𝕜 0 f s = (continuous_multilinear_curry_fin0 𝕜 E F).symm ∘ f := rfl

lemma iterated_fderiv_within_succ_apply_left {n : ℕ} (m : fin (n + 1) → E):
  (iterated_fderiv_within 𝕜 (n + 1) f s x : (fin (n + 1) → E) → F) m
  = (fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n f s) s x : E → (E [×n]→L[𝕜] F)) (m 0) (tail m) := rfl

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
lemma iterated_fderiv_within_succ_eq_comp_left {n : ℕ} :
  iterated_fderiv_within 𝕜 (n + 1) f s =
  (continuous_multilinear_curry_left_equiv 𝕜 (λ(i : fin (n + 1)), E) F)
    ∘ (fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n f s) s) := rfl

theorem iterated_fderiv_within_succ_apply_right {n : ℕ}
  (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) (m : fin (n + 1) → E) :
  (iterated_fderiv_within 𝕜 (n + 1) f s x : (fin (n + 1) → E) → F) m
    = iterated_fderiv_within 𝕜 n (λy, fderiv_within 𝕜 f s y) s x (init m) (m (last n)) :=
begin
  induction n with n IH generalizing x,
  { rw [iterated_fderiv_within_succ_eq_comp_left, iterated_fderiv_within_zero_eq_comp,
        iterated_fderiv_within_zero_apply,
        function.comp_apply, continuous_linear_equiv.comp_fderiv_within _ (hs x hx)],
    refl },
  { let I := continuous_multilinear_curry_right_equiv' 𝕜 n E F,
    have A : ∀ y ∈ s, iterated_fderiv_within 𝕜 n.succ f s y
        = (I ∘ (iterated_fderiv_within 𝕜 n (λy, fderiv_within 𝕜 f s y) s)) y,
      by { assume y hy, ext m, rw @IH m y hy, refl },
    calc
    (iterated_fderiv_within 𝕜 (n+2) f s x : (fin (n+2) → E) → F) m =
    (fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n.succ f s) s x
              : E → (E [×(n + 1)]→L[𝕜] F)) (m 0) (tail m) : rfl
    ... = (fderiv_within 𝕜 (I ∘ (iterated_fderiv_within 𝕜 n (fderiv_within 𝕜 f s) s)) s x
              : E → (E [×(n + 1)]→L[𝕜] F)) (m 0) (tail m) :
      by rw fderiv_within_congr (hs x hx) A (A x hx)
    ... = (I ∘ fderiv_within 𝕜 ((iterated_fderiv_within 𝕜 n (fderiv_within 𝕜 f s) s)) s x
              : E → (E [×(n + 1)]→L[𝕜] F)) (m 0) (tail m) :
      by { rw continuous_linear_equiv.comp_fderiv_within _ (hs x hx), refl }
    ... = (fderiv_within 𝕜 ((iterated_fderiv_within 𝕜 n (λ y, fderiv_within 𝕜 f s y) s)) s x
              : E → (E [×n]→L[𝕜] (E →L[𝕜] F))) (m 0) (init (tail m)) ((tail m) (last n)) : rfl
    ... = iterated_fderiv_within 𝕜 (nat.succ n) (λ y, fderiv_within 𝕜 f s y) s x
              (init m) (m (last (n + 1))) :
      by { rw [iterated_fderiv_within_succ_apply_left, tail_init_eq_init_tail], refl } }
end

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
lemma iterated_fderiv_within_succ_eq_comp_right {n : ℕ} (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) :
  iterated_fderiv_within 𝕜 (n + 1) f s x =
  ((continuous_multilinear_curry_right_equiv' 𝕜 n E F)
    ∘ (iterated_fderiv_within 𝕜 n (λy, fderiv_within 𝕜 f s y) s)) x :=
by { ext m, rw iterated_fderiv_within_succ_apply_right hs hx, refl }

@[simp] lemma iterated_fderiv_within_one_apply
  (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) (m : (fin 1) → E) :
  (iterated_fderiv_within 𝕜 1 f s x : ((fin 1) → E) → F) m
  = (fderiv_within 𝕜 f s x : E → F) (m 0) :=
by { rw [iterated_fderiv_within_succ_apply_right hs hx, iterated_fderiv_within_zero_apply], refl }

/-- If two functions coincide on a set `s` of unique differentiability, then their iterated
differentials within this set coincide. -/
lemma iterated_fderiv_within_congr {n : ℕ}
  (hs : unique_diff_on 𝕜 s) (hL : ∀y∈s, f₁ y = f y) (hx : x ∈ s) :
  iterated_fderiv_within 𝕜 n f₁ s x = iterated_fderiv_within 𝕜 n f s x :=
begin
  induction n with n IH generalizing x,
  { ext m, simp [hL x hx] },
  { have : fderiv_within 𝕜 (λ y, iterated_fderiv_within 𝕜 n f₁ s y) s x
           = fderiv_within 𝕜 (λ y, iterated_fderiv_within 𝕜 n f s y) s x :=
      fderiv_within_congr (hs x hx) (λ y hy, IH hy) (IH hx),
    ext m,
    rw [iterated_fderiv_within_succ_apply_left, iterated_fderiv_within_succ_apply_left, this] }
end

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with an open set containing `x`. -/
lemma iterated_fderiv_within_inter_open {n : ℕ} (hu : is_open u)
  (hs : unique_diff_on 𝕜 (s ∩ u)) (hx : x ∈ s ∩ u) :
  iterated_fderiv_within 𝕜 n f (s ∩ u) x = iterated_fderiv_within 𝕜 n f s x :=
begin
  induction n with n IH generalizing x,
  { ext m, simp },
  { have A : fderiv_within 𝕜 (λ y, iterated_fderiv_within 𝕜 n f (s ∩ u) y) (s ∩ u) x
           = fderiv_within 𝕜 (λ y, iterated_fderiv_within 𝕜 n f s y) (s ∩ u) x :=
      fderiv_within_congr (hs x hx) (λ y hy, IH hy) (IH hx),
    have B : fderiv_within 𝕜 (λ y, iterated_fderiv_within 𝕜 n f s y) (s ∩ u) x
           = fderiv_within 𝕜 (λ y, iterated_fderiv_within 𝕜 n f s y) s x :=
      fderiv_within_inter (mem_nhds_sets hu hx.2)
        ((unique_diff_within_at_inter (mem_nhds_sets hu hx.2)).1 (hs x hx)),
    ext m,
    rw [iterated_fderiv_within_succ_apply_left, iterated_fderiv_within_succ_apply_left, A, B] }
end

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x` within `s`. -/
lemma iterated_fderiv_within_inter' {n : ℕ}
  (hu : u ∈ 𝓝[s] x) (hs : unique_diff_on 𝕜 s) (xs : x ∈ s) :
  iterated_fderiv_within 𝕜 n f (s ∩ u) x = iterated_fderiv_within 𝕜 n f s x :=
begin
  obtain ⟨v, v_open, xv, vu⟩ : ∃ v, is_open v ∧ x ∈ v ∧ v ∩ s ⊆ u := mem_nhds_within.1 hu,
  have A : (s ∩ u) ∩ v = s ∩ v,
  { apply subset.antisymm (inter_subset_inter (inter_subset_left _ _) (subset.refl _)),
    exact λ y ⟨ys, yv⟩, ⟨⟨ys, vu ⟨yv, ys⟩⟩, yv⟩ },
  have : iterated_fderiv_within 𝕜 n f (s ∩ v) x = iterated_fderiv_within 𝕜 n f s x :=
    iterated_fderiv_within_inter_open v_open (hs.inter v_open) ⟨xs, xv⟩,
  rw ← this,
  have : iterated_fderiv_within 𝕜 n f ((s ∩ u) ∩ v) x = iterated_fderiv_within 𝕜 n f (s ∩ u) x,
  { refine iterated_fderiv_within_inter_open v_open  _ ⟨⟨xs, vu ⟨xv, xs⟩⟩, xv⟩,
    rw A,
    exact hs.inter v_open },
  rw A at this,
  rw ← this
end

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x`. -/
lemma iterated_fderiv_within_inter {n : ℕ}
  (hu : u ∈ 𝓝 x) (hs : unique_diff_on 𝕜 s) (xs : x ∈ s) :
  iterated_fderiv_within 𝕜 n f (s ∩ u) x = iterated_fderiv_within 𝕜 n f s x :=
iterated_fderiv_within_inter' (mem_nhds_within_of_mem_nhds hu) hs xs

@[simp] lemma times_cont_diff_on_zero :
  times_cont_diff_on 𝕜 0 f s ↔ continuous_on f s :=
begin
  refine ⟨λ H, H.continuous_on, λ H, _⟩,
  assume x hx m hm,
  have : (m : with_top ℕ) = 0 := le_antisymm hm bot_le,
  rw this,
  refine ⟨insert x s, self_mem_nhds_within, ftaylor_series_within 𝕜 f s, _⟩,
  rw has_ftaylor_series_up_to_on_zero_iff,
  exact ⟨by rwa insert_eq_of_mem hx, λ x hx, by simp [ftaylor_series_within]⟩
end

lemma times_cont_diff_within_at_zero (hx : x ∈ s) :
  times_cont_diff_within_at 𝕜 0 f s x ↔ ∃ u ∈ 𝓝[s] x, continuous_on f (s ∩ u) :=
begin
  split,
  { intros h,
    obtain ⟨u, H, p, hp⟩ := h 0 (by norm_num),
    refine ⟨u, _, _⟩,
    { simpa [hx] using H },
    { simp only [with_top.coe_zero, has_ftaylor_series_up_to_on_zero_iff] at hp,
      exact hp.1.mono (inter_subset_right s u) } },
  { rintros ⟨u, H, hu⟩,
    rw ← times_cont_diff_within_at_inter' H,
    have h' : x ∈ s ∩ u := ⟨hx, mem_of_mem_nhds_within hx H⟩,
    exact (times_cont_diff_on_zero.mpr hu).times_cont_diff_within_at h' }
end

/-- On a set with unique differentiability, any choice of iterated differential has to coincide
with the one we have chosen in `iterated_fderiv_within 𝕜 m f s`. -/
theorem has_ftaylor_series_up_to_on.eq_ftaylor_series_of_unique_diff_on {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s)
  {m : ℕ} (hmn : (m : with_top ℕ) ≤ n) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) :
  p x m = iterated_fderiv_within 𝕜 m f s x :=
begin
  induction m with m IH generalizing x,
  { rw [h.zero_eq' hx, iterated_fderiv_within_zero_eq_comp] },
  { have A : (m : with_top ℕ) < n := lt_of_lt_of_le (with_top.coe_lt_coe.2 (lt_add_one m)) hmn,
    have : has_fderiv_within_at (λ (y : E), iterated_fderiv_within 𝕜 m f s y)
      (continuous_multilinear_map.curry_left (p x (nat.succ m))) s x :=
    (h.fderiv_within m A x hx).congr (λ y hy, (IH (le_of_lt A) hy).symm) (IH (le_of_lt A) hx).symm,
    rw [iterated_fderiv_within_succ_eq_comp_left, function.comp_apply, this.fderiv_within (hs x hx)],
    exact (continuous_multilinear_map.uncurry_curry_left _).symm }
end

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem times_cont_diff_on.ftaylor_series_within {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) :
  has_ftaylor_series_up_to_on n f (ftaylor_series_within 𝕜 f s) s :=
begin
  split,
  { assume x hx,
    simp only [ftaylor_series_within, continuous_multilinear_map.uncurry0_apply,
               iterated_fderiv_within_zero_apply] },
  { assume m hm x hx,
    rcases (h x hx) m.succ (with_top.add_one_le_of_lt hm) with ⟨u, hu, p, Hp⟩,
    rw insert_eq_of_mem hx at hu,
    rcases mem_nhds_within.1 hu with ⟨o, o_open, xo, ho⟩,
    rw inter_comm at ho,
    have : p x m.succ = ftaylor_series_within 𝕜 f s x m.succ,
    { change p x m.succ = iterated_fderiv_within 𝕜 m.succ f s x,
      rw ← iterated_fderiv_within_inter (mem_nhds_sets o_open xo) hs hx,
      exact (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on (le_refl _)
        (hs.inter o_open) ⟨hx, xo⟩ },
    rw [← this, ← has_fderiv_within_at_inter (mem_nhds_sets o_open xo)],
    have A : ∀ y ∈ s ∩ o, p y m = ftaylor_series_within 𝕜 f s y m,
    { rintros y ⟨hy, yo⟩,
      change p y m = iterated_fderiv_within 𝕜 m f s y,
      rw ← iterated_fderiv_within_inter (mem_nhds_sets o_open yo) hs hy,
      exact (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on (with_top.coe_le_coe.2 (nat.le_succ m))
        (hs.inter o_open) ⟨hy, yo⟩ },
    exact ((Hp.mono ho).fderiv_within m (with_top.coe_lt_coe.2 (lt_add_one m)) x ⟨hx, xo⟩).congr
      (λ y hy, (A y hy).symm) (A x ⟨hx, xo⟩).symm },
  { assume m hm,
    apply continuous_on_of_locally_continuous_on,
    assume x hx,
    rcases h x hx m hm with ⟨u, hu, p, Hp⟩,
    rcases mem_nhds_within.1 hu with ⟨o, o_open, xo, ho⟩,
    rw insert_eq_of_mem hx at ho,
    rw inter_comm at ho,
    refine ⟨o, o_open, xo, _⟩,
    have A : ∀ y ∈ s ∩ o, p y m = ftaylor_series_within 𝕜 f s y m,
    { rintros y ⟨hy, yo⟩,
      change p y m = iterated_fderiv_within 𝕜 m f s y,
      rw ← iterated_fderiv_within_inter (mem_nhds_sets o_open yo) hs hy,
      exact (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on (le_refl _)
        (hs.inter o_open) ⟨hy, yo⟩ },
    exact ((Hp.mono ho).cont m (le_refl _)).congr (λ y hy, (A y hy).symm) }
end

lemma times_cont_diff_on_of_continuous_on_differentiable_on {n : with_top ℕ}
  (Hcont : ∀ (m : ℕ), (m : with_top ℕ) ≤ n →
    continuous_on (λ x, iterated_fderiv_within 𝕜 m f s x) s)
  (Hdiff : ∀ (m : ℕ), (m : with_top ℕ) < n →
    differentiable_on 𝕜 (λ x, iterated_fderiv_within 𝕜 m f s x) s) :
  times_cont_diff_on 𝕜 n f s :=
begin
  assume x hx m hm,
  rw insert_eq_of_mem hx,
  refine ⟨s, self_mem_nhds_within, ftaylor_series_within 𝕜 f s, _⟩,
  split,
  { assume y hy,
    simp only [ftaylor_series_within, continuous_multilinear_map.uncurry0_apply,
                iterated_fderiv_within_zero_apply] },
  { assume k hk y hy,
    convert (Hdiff k (lt_of_lt_of_le hk hm) y hy).has_fderiv_within_at,
    simp only [ftaylor_series_within, iterated_fderiv_within_succ_eq_comp_left,
                continuous_linear_equiv.coe_apply, function.comp_app, coe_fn_coe_base],
    exact continuous_linear_map.curry_uncurry_left _ },
  { assume k hk,
    exact Hcont k (le_trans hk hm) }
end

lemma times_cont_diff_on_of_differentiable_on {n : with_top ℕ}
  (h : ∀(m : ℕ), (m : with_top ℕ) ≤ n → differentiable_on 𝕜 (iterated_fderiv_within 𝕜 m f s) s) :
  times_cont_diff_on 𝕜 n f s :=
times_cont_diff_on_of_continuous_on_differentiable_on
  (λ m hm, (h m hm).continuous_on) (λ m hm, (h m (le_of_lt hm)))

lemma times_cont_diff_on.continuous_on_iterated_fderiv_within {n : with_top ℕ} {m : ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hmn : (m : with_top ℕ) ≤ n) (hs : unique_diff_on 𝕜 s) :
  continuous_on (iterated_fderiv_within 𝕜 m f s) s :=
(h.ftaylor_series_within hs).cont m hmn

lemma times_cont_diff_on.differentiable_on_iterated_fderiv_within {n : with_top ℕ} {m : ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hmn : (m : with_top ℕ) < n) (hs : unique_diff_on 𝕜 s) :
  differentiable_on 𝕜 (iterated_fderiv_within 𝕜 m f s) s :=
λ x hx, ((h.ftaylor_series_within hs).fderiv_within m hmn x hx).differentiable_within_at

lemma times_cont_diff_on_iff_continuous_on_differentiable_on {n : with_top ℕ}
  (hs : unique_diff_on 𝕜 s) :
  times_cont_diff_on 𝕜 n f s ↔
  (∀ (m : ℕ), (m : with_top ℕ) ≤ n →
    continuous_on (λ x, iterated_fderiv_within 𝕜 m f s x) s)
  ∧ (∀ (m : ℕ), (m : with_top ℕ) < n →
    differentiable_on 𝕜 (λ x, iterated_fderiv_within 𝕜 m f s x) s) :=
begin
  split,
  { assume h,
    split,
    { assume m hm, exact h.continuous_on_iterated_fderiv_within hm hs },
    { assume m hm, exact h.differentiable_on_iterated_fderiv_within hm hs } },
  { assume h,
    exact times_cont_diff_on_of_continuous_on_differentiable_on h.1 h.2 }
end

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (expressed with `fderiv_within`) is `C^n`. -/
theorem times_cont_diff_on_succ_iff_fderiv_within {n : ℕ} (hs : unique_diff_on 𝕜 s) :
  times_cont_diff_on 𝕜 ((n + 1) : ℕ) f s ↔
  differentiable_on 𝕜 f s ∧ times_cont_diff_on 𝕜 n (λ y, fderiv_within 𝕜 f s y) s :=
begin
  split,
  { assume H,
    refine ⟨H.differentiable_on (with_top.coe_le_coe.2 (nat.le_add_left 1 n)), λ x hx, _⟩,
    rcases times_cont_diff_within_at_succ_iff_has_fderiv_within_at.1 (H x hx)
      with ⟨u, hu, f', hff', hf'⟩,
    rcases mem_nhds_within.1 hu with ⟨o, o_open, xo, ho⟩,
    rw [inter_comm, insert_eq_of_mem hx] at ho,
    have := hf'.mono ho,
    rw times_cont_diff_within_at_inter' (mem_nhds_within_of_mem_nhds (mem_nhds_sets o_open xo))
      at this,
    apply this.congr_of_eventually_eq' _ hx,
    have : o ∩ s ∈ 𝓝[s] x := mem_nhds_within.2 ⟨o, o_open, xo, subset.refl _⟩,
    rw inter_comm at this,
    apply filter.eventually_eq_of_mem this (λ y hy, _),
    have A : fderiv_within 𝕜 f (s ∩ o) y = f' y :=
      ((hff' y (ho hy)).mono ho).fderiv_within (hs.inter o_open y hy),
    rwa fderiv_within_inter (mem_nhds_sets o_open hy.2) (hs y hy.1) at A, },
  { rintros ⟨hdiff, h⟩ x hx,
    rw [times_cont_diff_within_at_succ_iff_has_fderiv_within_at, insert_eq_of_mem hx],
    exact ⟨s, self_mem_nhds_within, fderiv_within 𝕜 f s,
      λ y hy, (hdiff y hy).has_fderiv_within_at, h x hx⟩ }
end

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (expressed with `fderiv`) is `C^n`. -/
theorem times_cont_diff_on_succ_iff_fderiv_of_open {n : ℕ} (hs : is_open s) :
  times_cont_diff_on 𝕜 ((n + 1) : ℕ) f s ↔
  differentiable_on 𝕜 f s ∧ times_cont_diff_on 𝕜 n (λ y, fderiv 𝕜 f y) s :=
begin
  rw times_cont_diff_on_succ_iff_fderiv_within hs.unique_diff_on,
  congr' 2,
  rw ← iff_iff_eq,
  apply times_cont_diff_on_congr,
  assume x hx,
  exact fderiv_within_of_open hs hx
end

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (expressed with `fderiv_within`) is `C^∞`. -/
theorem times_cont_diff_on_top_iff_fderiv_within (hs : unique_diff_on 𝕜 s) :
  times_cont_diff_on 𝕜 ∞ f s ↔
  differentiable_on 𝕜 f s ∧ times_cont_diff_on 𝕜 ∞ (λ y, fderiv_within 𝕜 f s y) s :=
begin
  split,
  { assume h,
    refine ⟨h.differentiable_on le_top, _⟩,
    apply times_cont_diff_on_top.2 (λ n, ((times_cont_diff_on_succ_iff_fderiv_within hs).1 _).2),
    exact h.of_le le_top },
  { assume h,
    refine times_cont_diff_on_top.2 (λ n, _),
    have A : (n : with_top ℕ) ≤ ∞ := le_top,
    apply ((times_cont_diff_on_succ_iff_fderiv_within hs).2 ⟨h.1, h.2.of_le A⟩).of_le,
    exact with_top.coe_le_coe.2 (nat.le_succ n) }
end

/-- A function is `C^∞` on an open domain if and only if it is differentiable there, and its
derivative (expressed with `fderiv`) is `C^∞`. -/
theorem times_cont_diff_on_top_iff_fderiv_of_open (hs : is_open s) :
  times_cont_diff_on 𝕜 ∞ f s ↔
  differentiable_on 𝕜 f s ∧ times_cont_diff_on 𝕜 ∞ (λ y, fderiv 𝕜 f y) s :=
begin
  rw times_cont_diff_on_top_iff_fderiv_within hs.unique_diff_on,
  congr' 2,
  rw ← iff_iff_eq,
  apply times_cont_diff_on_congr,
  assume x hx,
  exact fderiv_within_of_open hs hx
end

lemma times_cont_diff_on.fderiv_within {m n : with_top ℕ}
  (hf : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hmn : m + 1 ≤ n) :
  times_cont_diff_on 𝕜 m (λ y, fderiv_within 𝕜 f s y) s :=
begin
  cases m,
  { change ∞ + 1 ≤ n at hmn,
    have : n = ∞, by simpa using hmn,
    rw this at hf,
    exact ((times_cont_diff_on_top_iff_fderiv_within hs).1 hf).2 },
  { change (m.succ : with_top ℕ) ≤ n at hmn,
    exact ((times_cont_diff_on_succ_iff_fderiv_within hs).1 (hf.of_le hmn)).2 }
end

lemma times_cont_diff_on.fderiv_of_open {m n : with_top ℕ}
  (hf : times_cont_diff_on 𝕜 n f s) (hs : is_open s) (hmn : m + 1 ≤ n) :
  times_cont_diff_on 𝕜 m (λ y, fderiv 𝕜 f y) s :=
(hf.fderiv_within hs.unique_diff_on hmn).congr (λ x hx, (fderiv_within_of_open hs hx).symm)

lemma times_cont_diff_on.continuous_on_fderiv_within {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hn : 1 ≤ n) :
  continuous_on (λ x, fderiv_within 𝕜 f s x) s :=
((times_cont_diff_on_succ_iff_fderiv_within hs).1 (h.of_le hn)).2.continuous_on

lemma times_cont_diff_on.continuous_on_fderiv_of_open {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hs : is_open s) (hn : 1 ≤ n) :
  continuous_on (λ x, fderiv 𝕜 f x) s :=
((times_cont_diff_on_succ_iff_fderiv_of_open hs).1 (h.of_le hn)).2.continuous_on

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
lemma times_cont_diff_on.continuous_on_fderiv_within_apply
  {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hn : 1 ≤ n) :
  continuous_on (λp : E × E, (fderiv_within 𝕜 f s p.1 : E → F) p.2) (set.prod s univ) :=
begin
  have A : continuous (λq : (E →L[𝕜] F) × E, q.1 q.2) := is_bounded_bilinear_map_apply.continuous,
  have B : continuous_on (λp : E × E, (fderiv_within 𝕜 f s p.1, p.2)) (set.prod s univ),
  { apply continuous_on.prod _ continuous_snd.continuous_on,
    exact continuous_on.comp (h.continuous_on_fderiv_within hs hn) continuous_fst.continuous_on
      (prod_subset_preimage_fst _ _) },
  exact A.comp_continuous_on B
end

/-! ### Functions with a Taylor series on the whole space -/

/-- `has_ftaylor_series_up_to n f p` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_at` but for higher order derivatives. -/
structure has_ftaylor_series_up_to (n : with_top ℕ)
  (f : E → F) (p : E → formal_multilinear_series 𝕜 E F) : Prop :=
(zero_eq : ∀ x, (p x 0).uncurry0 = f x)
(fderiv  : ∀ (m : ℕ) (hm : (m : with_top ℕ) < n), ∀ x,
    has_fderiv_at (λ y, p y m) (p x m.succ).curry_left x)
(cont    : ∀ (m : ℕ) (hm : (m : with_top ℕ) ≤ n), continuous (λ x, p x m))

lemma has_ftaylor_series_up_to.zero_eq' {n : with_top ℕ}
  (h : has_ftaylor_series_up_to n f p) (x : E) :
  p x 0 = (continuous_multilinear_curry_fin0 𝕜 E F).symm (f x) :=
by { rw ← h.zero_eq x, symmetry, exact continuous_multilinear_map.uncurry0_curry0 _ }

lemma has_ftaylor_series_up_to_on_univ_iff {n : with_top ℕ} :
  has_ftaylor_series_up_to_on n f p univ ↔ has_ftaylor_series_up_to n f p :=
begin
  split,
  { assume H,
    split,
    { exact λ x, H.zero_eq x (mem_univ x) },
    { assume m hm x,
      rw ← has_fderiv_within_at_univ,
      exact H.fderiv_within m hm x (mem_univ x) },
    { assume m hm,
      rw continuous_iff_continuous_on_univ,
      exact H.cont m hm } },
  { assume H,
    split,
    { exact λ x hx, H.zero_eq x },
    { assume m hm x hx,
      rw has_fderiv_within_at_univ,
      exact H.fderiv m hm x },
    { assume m hm,
      rw ← continuous_iff_continuous_on_univ,
      exact H.cont m hm } }
end

lemma has_ftaylor_series_up_to.has_ftaylor_series_up_to_on {n : with_top ℕ}
  (h : has_ftaylor_series_up_to n f p) (s : set E) :
  has_ftaylor_series_up_to_on n f p s :=
(has_ftaylor_series_up_to_on_univ_iff.2 h).mono (subset_univ _)

lemma has_ftaylor_series_up_to.of_le {m n : with_top ℕ}
  (h : has_ftaylor_series_up_to n f p) (hmn : m ≤ n) :
  has_ftaylor_series_up_to m f p :=
by { rw ← has_ftaylor_series_up_to_on_univ_iff at h ⊢, exact h.of_le hmn }

lemma has_ftaylor_series_up_to.continuous {n : with_top ℕ}
  (h : has_ftaylor_series_up_to n f p) : continuous f :=
begin
  rw ← has_ftaylor_series_up_to_on_univ_iff at h,
  rw continuous_iff_continuous_on_univ,
  exact h.continuous_on
end

lemma has_ftaylor_series_up_to_zero_iff :
  has_ftaylor_series_up_to 0 f p ↔ continuous f ∧ (∀ x, (p x 0).uncurry0 = f x) :=
by simp [has_ftaylor_series_up_to_on_univ_iff.symm, continuous_iff_continuous_on_univ,
         has_ftaylor_series_up_to_on_zero_iff]

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
lemma has_ftaylor_series_up_to.has_fderiv_at {n : with_top ℕ}
  (h : has_ftaylor_series_up_to n f p) (hn : 1 ≤ n) (x : E) :
  has_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) x :=
begin
  rw [← has_fderiv_within_at_univ],
  exact (has_ftaylor_series_up_to_on_univ_iff.2 h).has_fderiv_within_at hn (mem_univ _)
end

lemma has_ftaylor_series_up_to.differentiable {n : with_top ℕ}
  (h : has_ftaylor_series_up_to n f p) (hn : 1 ≤ n) : differentiable 𝕜 f :=
λ x, (h.has_fderiv_at hn x).differentiable_at

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem has_ftaylor_series_up_to_succ_iff_right {n : ℕ} :
  has_ftaylor_series_up_to ((n + 1) : ℕ) f p ↔
  (∀ x, (p x 0).uncurry0 = f x)
  ∧ (∀ x, has_fderiv_at (λ y, p y 0) (p x 1).curry_left x)
  ∧ has_ftaylor_series_up_to n
    (λ x, continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) (λ x, (p x).shift) :=
by simp [has_ftaylor_series_up_to_on_succ_iff_right, has_ftaylor_series_up_to_on_univ_iff.symm,
         -add_comm, -with_zero.coe_add]

/-! ### Smooth functions at a point -/

variable (𝕜)

/-- A function is continuously differentiable up to `n` at a point `x` if, for any integer `k ≤ n`,
there is a neighborhood of `x` where `f` admits derivatives up to order `n`, which are continuous.
-/
def times_cont_diff_at (n : with_top ℕ) (f : E → F) (x : E) :=
times_cont_diff_within_at 𝕜 n f univ x

variable {𝕜}

theorem times_cont_diff_within_at_univ {n : with_top ℕ} :
  times_cont_diff_within_at 𝕜 n f univ x ↔ times_cont_diff_at 𝕜 n f x :=
iff.rfl

lemma times_cont_diff_at_top :
  times_cont_diff_at 𝕜 ∞ f x ↔ ∀ (n : ℕ), times_cont_diff_at 𝕜 n f x :=
by simp [← times_cont_diff_within_at_univ, times_cont_diff_within_at_top]

lemma times_cont_diff_at.times_cont_diff_within_at {n : with_top ℕ}
  (h : times_cont_diff_at 𝕜 n f x) : times_cont_diff_within_at 𝕜 n f s x :=
h.mono (subset_univ _)

lemma times_cont_diff_within_at.times_cont_diff_at {n : with_top ℕ}
  (h : times_cont_diff_within_at 𝕜 n f s x) (hx : s ∈ 𝓝 x) :
  times_cont_diff_at 𝕜 n f x :=
by rwa [times_cont_diff_at, ← times_cont_diff_within_at_inter hx, univ_inter]

lemma times_cont_diff_at.congr_of_eventually_eq {n : with_top ℕ}
  (h : times_cont_diff_at 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) :
  times_cont_diff_at 𝕜 n f₁ x :=
h.congr_of_eventually_eq' (by rwa nhds_within_univ) (mem_univ x)

lemma times_cont_diff_at.of_le {m n : with_top ℕ}
  (h : times_cont_diff_at 𝕜 n f x) (hmn : m ≤ n) :
  times_cont_diff_at 𝕜 m f x :=
h.of_le hmn

lemma times_cont_diff_at.continuous_at {n : with_top ℕ}
  (h : times_cont_diff_at 𝕜 n f x) : continuous_at f x :=
by simpa [continuous_within_at_univ] using h.continuous_within_at

/-- If a function is `C^n` with `n ≥ 1` at a point, then it is differentiable there. -/
lemma times_cont_diff_at.differentiable_at {n : with_top ℕ}
  (h : times_cont_diff_at 𝕜 n f x) (hn : 1 ≤ n) : differentiable_at 𝕜 f x :=
by simpa [hn, differentiable_within_at_univ] using h.differentiable_within_at

/-- A function is `C^(n + 1)` at a point iff locally, it has a derivative which is `C^n`. -/
theorem times_cont_diff_at_succ_iff_has_fderiv_at {n : ℕ} :
  times_cont_diff_at 𝕜 ((n + 1) : ℕ) f x
  ↔ (∃ f' : E → (E →L[𝕜] F), (∃ u ∈ 𝓝 x, (∀ x ∈ u, has_fderiv_at f (f' x) x))
      ∧ (times_cont_diff_at 𝕜 n f' x)) :=
begin
  rw [← times_cont_diff_within_at_univ, times_cont_diff_within_at_succ_iff_has_fderiv_within_at],
  simp only [nhds_within_univ, exists_prop, mem_univ, insert_eq_of_mem],
  split,
  { rintros ⟨u, H, f', h_fderiv, h_times_cont_diff⟩,
    rcases mem_nhds_sets_iff.mp H with ⟨t, htu, ht, hxt⟩,
    refine ⟨f', ⟨t, _⟩, h_times_cont_diff.times_cont_diff_at H⟩,
    refine ⟨mem_nhds_sets_iff.mpr ⟨t, subset.rfl, ht, hxt⟩, _⟩,
    intros y hyt,
    refine (h_fderiv y (htu hyt)).has_fderiv_at _,
    exact mem_nhds_sets_iff.mpr ⟨t, htu, ht, hyt⟩ },
  { rintros ⟨f', ⟨u, H, h_fderiv⟩, h_times_cont_diff⟩,
    refine ⟨u, H, f', _, h_times_cont_diff.times_cont_diff_within_at⟩,
    intros x hxu,
    exact (h_fderiv x hxu).has_fderiv_within_at }
end

/-! ### Smooth functions -/

variable (𝕜)

/-- A function is continuously differentiable up to `n` if it admits derivatives up to
order `n`, which are continuous. Contrary to the case of definitions in domains (where derivatives
might not be unique) we do not need to localize the definition in space or time.
-/
definition times_cont_diff (n : with_top ℕ) (f : E → F)  :=
∃ p : E → formal_multilinear_series 𝕜 E F, has_ftaylor_series_up_to n f p

variable {𝕜}

theorem times_cont_diff_on_univ {n : with_top ℕ} :
  times_cont_diff_on 𝕜 n f univ ↔ times_cont_diff 𝕜 n f :=
begin
  split,
  { assume H,
    use ftaylor_series_within 𝕜 f univ,
    rw ← has_ftaylor_series_up_to_on_univ_iff,
    exact H.ftaylor_series_within unique_diff_on_univ },
  { rintros ⟨p, hp⟩ x hx m hm,
    exact ⟨univ, filter.univ_sets _, p, (hp.has_ftaylor_series_up_to_on univ).of_le hm⟩ }
end

lemma times_cont_diff_iff_times_cont_diff_at {n : with_top ℕ} :
  times_cont_diff 𝕜 n f ↔ ∀ x, times_cont_diff_at 𝕜 n f x :=
by simp [← times_cont_diff_on_univ, times_cont_diff_on, times_cont_diff_at]

lemma times_cont_diff.times_cont_diff_at {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) :
  times_cont_diff_at 𝕜 n f x :=
times_cont_diff_iff_times_cont_diff_at.1 h x

lemma times_cont_diff.times_cont_diff_within_at {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) :
  times_cont_diff_within_at 𝕜 n f s x :=
h.times_cont_diff_at.times_cont_diff_within_at

lemma times_cont_diff_top :
  times_cont_diff 𝕜 ∞ f ↔ ∀ (n : ℕ), times_cont_diff 𝕜 n f :=
by simp [times_cont_diff_on_univ.symm, times_cont_diff_on_top]

lemma times_cont_diff_all_iff_nat :
  (∀ n, times_cont_diff 𝕜 n f) ↔ (∀ n : ℕ, times_cont_diff 𝕜 n f) :=
by simp only [← times_cont_diff_on_univ, times_cont_diff_on_all_iff_nat]

lemma times_cont_diff.times_cont_diff_on {n : with_top ℕ}
  (h : times_cont_diff 𝕜 n f) : times_cont_diff_on 𝕜 n f s :=
(times_cont_diff_on_univ.2 h).mono (subset_univ _)

@[simp] lemma times_cont_diff_zero :
  times_cont_diff 𝕜 0 f ↔ continuous f :=
begin
  rw [← times_cont_diff_on_univ, continuous_iff_continuous_on_univ],
  exact times_cont_diff_on_zero
end

lemma times_cont_diff_at_zero :
  times_cont_diff_at 𝕜 0 f x ↔ ∃ u ∈ 𝓝 x, continuous_on f u :=
by { rw ← times_cont_diff_within_at_univ, simp [times_cont_diff_within_at_zero, nhds_within_univ] }

lemma times_cont_diff.of_le {m n : with_top ℕ}
  (h : times_cont_diff 𝕜 n f) (hmn : m ≤ n) :
  times_cont_diff 𝕜 m f :=
times_cont_diff_on_univ.1 $ (times_cont_diff_on_univ.2 h).of_le hmn

lemma times_cont_diff.continuous {n : with_top ℕ}
  (h : times_cont_diff 𝕜 n f) : continuous f :=
times_cont_diff_zero.1 (h.of_le bot_le)

/-- If a function is `C^n` with `n ≥ 1`, then it is differentiable. -/
lemma times_cont_diff.differentiable {n : with_top ℕ}
  (h : times_cont_diff 𝕜 n f) (hn : 1 ≤ n) : differentiable 𝕜 f :=
differentiable_on_univ.1 $ (times_cont_diff_on_univ.2 h).differentiable_on hn


/-! ### Iterated derivative -/

variable (𝕜)

/-- The `n`-th derivative of a function, as a multilinear map, defined inductively. -/
noncomputable def iterated_fderiv (n : ℕ) (f : E → F) :
  E → (E [×n]→L[𝕜] F) :=
nat.rec_on n
  (λ x, continuous_multilinear_map.curry0 𝕜 E (f x))
  (λ n rec x, continuous_linear_map.uncurry_left (fderiv 𝕜 rec x))

/-- Formal Taylor series associated to a function within a set. -/
def ftaylor_series (f : E → F) (x : E) : formal_multilinear_series 𝕜 E F :=
λ n, iterated_fderiv 𝕜 n f x

variable {𝕜}

@[simp] lemma iterated_fderiv_zero_apply (m : (fin 0) → E) :
  (iterated_fderiv 𝕜 0 f x : ((fin 0) →  E) → F) m = f x := rfl

lemma iterated_fderiv_zero_eq_comp :
  iterated_fderiv 𝕜 0 f = (continuous_multilinear_curry_fin0 𝕜 E F).symm ∘ f := rfl

lemma iterated_fderiv_succ_apply_left {n : ℕ} (m : fin (n + 1) → E):
  (iterated_fderiv 𝕜 (n + 1) f x : (fin (n + 1) → E) → F) m
  = (fderiv 𝕜 (iterated_fderiv 𝕜 n f) x : E → (E [×n]→L[𝕜] F)) (m 0) (tail m) := rfl

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
lemma iterated_fderiv_succ_eq_comp_left {n : ℕ} :
  iterated_fderiv 𝕜 (n + 1) f =
  (continuous_multilinear_curry_left_equiv 𝕜 (λ(i : fin (n + 1)), E) F)
    ∘ (fderiv 𝕜 (iterated_fderiv 𝕜 n f)) := rfl

lemma iterated_fderiv_within_univ {n : ℕ} :
  iterated_fderiv_within 𝕜 n f univ = iterated_fderiv 𝕜 n f :=
begin
  induction n with n IH,
  { ext x, simp },
  { ext x m,
    rw [iterated_fderiv_succ_apply_left, iterated_fderiv_within_succ_apply_left, IH,
        fderiv_within_univ] }
end

lemma ftaylor_series_within_univ :
  ftaylor_series_within 𝕜 f univ = ftaylor_series 𝕜 f :=
begin
  ext1 x, ext1 n,
  change iterated_fderiv_within 𝕜 n f univ x = iterated_fderiv 𝕜 n f x,
  rw iterated_fderiv_within_univ
end

theorem iterated_fderiv_succ_apply_right {n : ℕ} (m : fin (n + 1) → E) :
  (iterated_fderiv 𝕜 (n + 1) f x : (fin (n + 1) → E) → F) m
    = iterated_fderiv 𝕜 n (λy, fderiv 𝕜 f y) x (init m) (m (last n)) :=
begin
  rw [← iterated_fderiv_within_univ, ← iterated_fderiv_within_univ, ← fderiv_within_univ],
  exact iterated_fderiv_within_succ_apply_right unique_diff_on_univ (mem_univ _) _
end

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
lemma iterated_fderiv_succ_eq_comp_right {n : ℕ} :
  iterated_fderiv 𝕜 (n + 1) f x =
  ((continuous_multilinear_curry_right_equiv' 𝕜 n E F)
    ∘ (iterated_fderiv 𝕜 n (λy, fderiv 𝕜 f y))) x :=
by { ext m, rw iterated_fderiv_succ_apply_right, refl }

@[simp] lemma iterated_fderiv_one_apply (m : (fin 1) → E) :
  (iterated_fderiv 𝕜 1 f x : ((fin 1) → E) → F) m
  = (fderiv 𝕜 f x : E → F) (m 0) :=
by { rw [iterated_fderiv_succ_apply_right, iterated_fderiv_zero_apply], refl }

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem times_cont_diff_on_iff_ftaylor_series {n : with_top ℕ} :
  times_cont_diff 𝕜 n f ↔ has_ftaylor_series_up_to n f (ftaylor_series 𝕜 f) :=
begin
  split,
  { rw [← times_cont_diff_on_univ, ← has_ftaylor_series_up_to_on_univ_iff,
        ← ftaylor_series_within_univ],
    exact λ h, times_cont_diff_on.ftaylor_series_within h unique_diff_on_univ },
  { assume h, exact ⟨ftaylor_series 𝕜 f, h⟩ }
end

lemma times_cont_diff_iff_continuous_differentiable {n : with_top ℕ} :
  times_cont_diff 𝕜 n f ↔
  (∀ (m : ℕ), (m : with_top ℕ) ≤ n → continuous (λ x, iterated_fderiv 𝕜 m f x))
  ∧ (∀ (m : ℕ), (m : with_top ℕ) < n → differentiable 𝕜 (λ x, iterated_fderiv 𝕜 m f x)) :=
by simp [times_cont_diff_on_univ.symm, continuous_iff_continuous_on_univ,
    differentiable_on_univ.symm, iterated_fderiv_within_univ,
    times_cont_diff_on_iff_continuous_on_differentiable_on unique_diff_on_univ]

lemma times_cont_diff_of_differentiable_iterated_fderiv {n : with_top ℕ}
  (h : ∀(m : ℕ), (m : with_top ℕ) ≤ n → differentiable 𝕜 (iterated_fderiv 𝕜 m f)) :
  times_cont_diff 𝕜 n f :=
times_cont_diff_iff_continuous_differentiable.2
⟨λ m hm, (h m hm).continuous, λ m hm, (h m (le_of_lt hm))⟩

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative is `C^n`. -/
theorem times_cont_diff_succ_iff_fderiv {n : ℕ} :
  times_cont_diff 𝕜 ((n + 1) : ℕ) f ↔
  differentiable 𝕜 f ∧ times_cont_diff 𝕜 n (λ y, fderiv 𝕜 f y) :=
by simp [times_cont_diff_on_univ.symm, differentiable_on_univ.symm, fderiv_within_univ.symm,
         - fderiv_within_univ, times_cont_diff_on_succ_iff_fderiv_within unique_diff_on_univ,
         -with_zero.coe_add, -add_comm]

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative is `C^∞`. -/
theorem times_cont_diff_top_iff_fderiv :
  times_cont_diff 𝕜 ∞ f ↔
  differentiable 𝕜 f ∧ times_cont_diff 𝕜 ∞ (λ y, fderiv 𝕜 f y) :=
begin
  simp [times_cont_diff_on_univ.symm, differentiable_on_univ.symm, fderiv_within_univ.symm,
        - fderiv_within_univ],
  rw times_cont_diff_on_top_iff_fderiv_within unique_diff_on_univ,
end

lemma times_cont_diff.continuous_fderiv {n : with_top ℕ}
  (h : times_cont_diff 𝕜 n f) (hn : 1 ≤ n) :
  continuous (λ x, fderiv 𝕜 f x) :=
((times_cont_diff_succ_iff_fderiv).1 (h.of_le hn)).2.continuous

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
lemma times_cont_diff.continuous_fderiv_apply {n : with_top ℕ}
  (h : times_cont_diff 𝕜 n f) (hn : 1 ≤ n) :
  continuous (λp : E × E, (fderiv 𝕜 f p.1 : E → F) p.2) :=
begin
  have A : continuous (λq : (E →L[𝕜] F) × E, q.1 q.2) := is_bounded_bilinear_map_apply.continuous,
  have B : continuous (λp : E × E, (fderiv 𝕜 f p.1, p.2)),
  { apply continuous.prod_mk _ continuous_snd,
    exact continuous.comp (h.continuous_fderiv hn) continuous_fst },
  exact A.comp B
end

/-! ### Constants -/

lemma iterated_fderiv_within_zero_fun {n : ℕ} :
  iterated_fderiv 𝕜 n (λ x : E, (0 : F)) = 0 :=
begin
  induction n with n IH,
  { ext m, simp },
  { ext x m,
    rw [iterated_fderiv_succ_apply_left, IH],
    change (fderiv 𝕜 (λ (x : E), (0 : (E [×n]→L[𝕜] F))) x : E → (E [×n]→L[𝕜] F)) (m 0) (tail m) = _,
    rw fderiv_const,
    refl }
end

lemma times_cont_diff_zero_fun {n : with_top ℕ} :
  times_cont_diff 𝕜 n (λ x : E, (0 : F)) :=
begin
  apply times_cont_diff_of_differentiable_iterated_fderiv (λm hm, _),
  rw iterated_fderiv_within_zero_fun,
  apply differentiable_const (0 : (E [×m]→L[𝕜] F))
end

/--
Constants are `C^∞`.
-/
lemma times_cont_diff_const {n : with_top ℕ} {c : F} : times_cont_diff 𝕜 n (λx : E, c) :=
begin
  suffices h : times_cont_diff 𝕜 ∞ (λx : E, c), by exact h.of_le le_top,
  rw times_cont_diff_top_iff_fderiv,
  refine ⟨differentiable_const c, _⟩,
  rw fderiv_const,
  exact times_cont_diff_zero_fun
end

lemma times_cont_diff_on_const {n : with_top ℕ} {c : F} {s : set E} :
  times_cont_diff_on 𝕜 n (λx : E, c) s :=
times_cont_diff_const.times_cont_diff_on

lemma times_cont_diff_at_const {n : with_top ℕ} {c : F} :
  times_cont_diff_at 𝕜 n (λx : E, c) x :=
times_cont_diff_const.times_cont_diff_at

lemma times_cont_diff_within_at_const {n : with_top ℕ} {c : F} :
  times_cont_diff_within_at 𝕜 n (λx : E, c) s x :=
times_cont_diff_at_const.times_cont_diff_within_at

@[nontriviality] lemma times_cont_diff_of_subsingleton [subsingleton F] {n : with_top ℕ} :
  times_cont_diff 𝕜 n f :=
by { rw [subsingleton.elim f (λ _, 0)], exact times_cont_diff_const }

@[nontriviality] lemma times_cont_diff_at_of_subsingleton [subsingleton F] {n : with_top ℕ} :
  times_cont_diff_at 𝕜 n f x :=
by { rw [subsingleton.elim f (λ _, 0)], exact times_cont_diff_at_const }

@[nontriviality] lemma times_cont_diff_within_at_of_subsingleton [subsingleton F] {n : with_top ℕ} :
  times_cont_diff_within_at 𝕜 n f s x :=
by { rw [subsingleton.elim f (λ _, 0)], exact times_cont_diff_within_at_const }

@[nontriviality] lemma times_cont_diff_on_of_subsingleton [subsingleton F] {n : with_top ℕ} :
  times_cont_diff_on 𝕜 n f s :=
by { rw [subsingleton.elim f (λ _, 0)], exact times_cont_diff_on_const }

/-! ### Linear functions -/

/--
Unbundled bounded linear functions are `C^∞`.
-/
lemma is_bounded_linear_map.times_cont_diff {n : with_top ℕ} (hf : is_bounded_linear_map 𝕜 f) :
  times_cont_diff 𝕜 n f :=
begin
  suffices h : times_cont_diff 𝕜 ∞ f, by exact h.of_le le_top,
  rw times_cont_diff_top_iff_fderiv,
  refine ⟨hf.differentiable, _⟩,
  simp [hf.fderiv],
  exact times_cont_diff_const
end

lemma continuous_linear_map.times_cont_diff {n : with_top ℕ} (f : E →L[𝕜] F) :
  times_cont_diff 𝕜 n f :=
f.is_bounded_linear_map.times_cont_diff

/--
The first projection in a product is `C^∞`.
-/
lemma times_cont_diff_fst {n : with_top ℕ} : times_cont_diff 𝕜 n (prod.fst : E × F → E) :=
is_bounded_linear_map.times_cont_diff is_bounded_linear_map.fst

/--
The first projection on a domain in a product is `C^∞`.
-/
lemma times_cont_diff_on_fst {s : set (E×F)} {n : with_top ℕ} :
  times_cont_diff_on 𝕜 n (prod.fst : E × F → E) s :=
times_cont_diff.times_cont_diff_on times_cont_diff_fst

/--
The first projection at a point in a product is `C^∞`.
-/
lemma times_cont_diff_at_fst {p : E × F} {n : with_top ℕ} :
  times_cont_diff_at 𝕜 n (prod.fst : E × F → E) p :=
times_cont_diff_fst.times_cont_diff_at

/--
The first projection within a domain at a point in a product is `C^∞`.
-/
lemma times_cont_diff_within_at_fst {s : set (E × F)} {p : E × F} {n : with_top ℕ} :
  times_cont_diff_within_at 𝕜 n (prod.fst : E × F → E) s p :=
times_cont_diff_fst.times_cont_diff_within_at

/--
The second projection in a product is `C^∞`.
-/
lemma times_cont_diff_snd {n : with_top ℕ} : times_cont_diff 𝕜 n (prod.snd : E × F → F) :=
is_bounded_linear_map.times_cont_diff is_bounded_linear_map.snd

/--
The second projection on a domain in a product is `C^∞`.
-/
lemma times_cont_diff_on_snd {s : set (E×F)} {n : with_top ℕ} :
  times_cont_diff_on 𝕜 n (prod.snd : E × F → F) s :=
times_cont_diff.times_cont_diff_on times_cont_diff_snd

/--
The second projection at a point in a product is `C^∞`.
-/
lemma times_cont_diff_at_snd {p : E × F} {n : with_top ℕ} :
  times_cont_diff_at 𝕜 n (prod.snd : E × F → F) p :=
times_cont_diff_snd.times_cont_diff_at

/--
The second projection within a domain at a point in a product is `C^∞`.
-/
lemma times_cont_diff_within_at_snd {s : set (E × F)} {p : E × F} {n : with_top ℕ} :
  times_cont_diff_within_at 𝕜 n (prod.snd : E × F → F) s p :=
times_cont_diff_snd.times_cont_diff_within_at

/--
The identity is `C^∞`.
-/
lemma times_cont_diff_id {n : with_top ℕ} : times_cont_diff 𝕜 n (id : E → E) :=
is_bounded_linear_map.id.times_cont_diff

lemma times_cont_diff_within_at_id {n : with_top ℕ} {s x} :
  times_cont_diff_within_at 𝕜 n (id : E → E) s x :=
times_cont_diff_id.times_cont_diff_within_at

lemma times_cont_diff_at_id {n : with_top ℕ} {x} :
  times_cont_diff_at 𝕜 n (id : E → E) x :=
times_cont_diff_id.times_cont_diff_at

lemma times_cont_diff_on_id {n : with_top ℕ} {s} :
  times_cont_diff_on 𝕜 n (id : E → E) s :=
times_cont_diff_id.times_cont_diff_on

/--
Bilinear functions are `C^∞`.
-/
lemma is_bounded_bilinear_map.times_cont_diff {n : with_top ℕ} (hb : is_bounded_bilinear_map 𝕜 b) :
  times_cont_diff 𝕜 n b :=
begin
  suffices h : times_cont_diff 𝕜 ∞ b, by exact h.of_le le_top,
  rw times_cont_diff_top_iff_fderiv,
  refine ⟨hb.differentiable, _⟩,
  simp [hb.fderiv],
  exact hb.is_bounded_linear_map_deriv.times_cont_diff
end

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `g ∘ f` admits a Taylor
series whose `k`-th term is given by `g ∘ (p k)`. -/
lemma has_ftaylor_series_up_to_on.continuous_linear_map_comp {n : with_top ℕ} (g : F →L[𝕜] G)
  (hf : has_ftaylor_series_up_to_on n f p s) :
  has_ftaylor_series_up_to_on n (g ∘ f) (λ x k, g.comp_continuous_multilinear_map (p x k)) s :=
begin
  split,
  { assume x hx, simp [(hf.zero_eq x hx).symm] },
  { assume m hm x hx,
    let A : (E [×m]→L[𝕜] F) → (E [×m]→L[𝕜] G) := λ f, g.comp_continuous_multilinear_map f,
    have hA : is_bounded_linear_map 𝕜 A :=
      is_bounded_bilinear_map_comp_multilinear.is_bounded_linear_map_right _,
    have := hf.fderiv_within m hm x hx,
    convert has_fderiv_at.comp_has_fderiv_within_at x (hA.has_fderiv_at) this },
  { assume m hm,
    let A : (E [×m]→L[𝕜] F) → (E [×m]→L[𝕜] G) :=
      λ f, g.comp_continuous_multilinear_map f,
    have hA : is_bounded_linear_map 𝕜 A :=
      is_bounded_bilinear_map_comp_multilinear.is_bounded_linear_map_right _,
    exact hA.continuous.comp_continuous_on (hf.cont m hm) }
end

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
lemma times_cont_diff_within_at.continuous_linear_map_comp {n : with_top ℕ} (g : F →L[𝕜] G)
  (hf : times_cont_diff_within_at 𝕜 n f s x) :
  times_cont_diff_within_at 𝕜 n (g ∘ f) s x :=
begin
  assume m hm,
  rcases hf m hm with ⟨u, hu, p, hp⟩,
  exact ⟨u, hu, _, hp.continuous_linear_map_comp g⟩,
end

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
lemma times_cont_diff_at.continuous_linear_map_comp {n : with_top ℕ} (g : F →L[𝕜] G)
  (hf : times_cont_diff_at 𝕜 n f x) :
  times_cont_diff_at 𝕜 n (g ∘ f) x :=
times_cont_diff_within_at.continuous_linear_map_comp g hf

/-- Composition by continuous linear maps on the left preserves `C^n` functions on domains. -/
lemma times_cont_diff_on.continuous_linear_map_comp {n : with_top ℕ} (g : F →L[𝕜] G)
  (hf : times_cont_diff_on 𝕜 n f s) :
  times_cont_diff_on 𝕜 n (g ∘ f) s :=
λ x hx, (hf x hx).continuous_linear_map_comp g

/-- Composition by continuous linear maps on the left preserves `C^n` functions. -/
lemma times_cont_diff.continuous_linear_map_comp {n : with_top ℕ} {f : E → F} (g : F →L[𝕜] G)
  (hf : times_cont_diff 𝕜 n f) : times_cont_diff 𝕜 n (λx, g (f x)) :=
times_cont_diff_on_univ.1 $ times_cont_diff_on.continuous_linear_map_comp
  _ (times_cont_diff_on_univ.2 hf)

/-- Composition by continuous linear equivs on the left respects higher differentiability on
domains. -/
lemma continuous_linear_equiv.comp_times_cont_diff_within_at_iff
  {n : with_top ℕ} (e : F ≃L[𝕜] G) :
  times_cont_diff_within_at 𝕜 n (e ∘ f) s x ↔ times_cont_diff_within_at 𝕜 n f s x :=
begin
  split,
  { assume H,
    have : f = e.symm ∘ (e ∘ f),
      by { ext y, simp only [function.comp_app], rw e.symm_apply_apply (f y) },
    rw this,
    exact H.continuous_linear_map_comp _ },
  { assume H,
    exact H.continuous_linear_map_comp _ }
end

/-- Composition by continuous linear equivs on the left respects higher differentiability on
domains. -/
lemma continuous_linear_equiv.comp_times_cont_diff_on_iff
  {n : with_top ℕ} (e : F ≃L[𝕜] G) :
  times_cont_diff_on 𝕜 n (e ∘ f) s ↔ times_cont_diff_on 𝕜 n f s :=
by simp [times_cont_diff_on, e.comp_times_cont_diff_within_at_iff]

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `f ∘ g` admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term is given by `p k (g v₁, ..., g vₖ)` . -/
lemma has_ftaylor_series_up_to_on.comp_continuous_linear_map {n : with_top ℕ}
  (hf : has_ftaylor_series_up_to_on n f p s) (g : G →L[𝕜] E) :
  has_ftaylor_series_up_to_on n (f ∘ g)
    (λ x k, (p (g x) k).comp_continuous_linear_map (λ _, g)) (g ⁻¹' s) :=
begin
  let A : Π m : ℕ, (E [×m]→L[𝕜] F) → (G [×m]→L[𝕜] F) :=
    λ m h, h.comp_continuous_linear_map (λ _, g),
  have hA : ∀ m, is_bounded_linear_map 𝕜 (A m) :=
    λ m, is_bounded_linear_map_continuous_multilinear_map_comp_linear g,
  split,
  { assume x hx,
    simp only [(hf.zero_eq (g x) hx).symm, function.comp_app],
    change p (g x) 0 (λ (i : fin 0), g 0) = p (g x) 0 0,
    rw continuous_linear_map.map_zero,
    refl },
  { assume m hm x hx,
    convert ((hA m).has_fderiv_at).comp_has_fderiv_within_at x
      ((hf.fderiv_within m hm (g x) hx).comp x (g.has_fderiv_within_at) (subset.refl _)),
    ext y v,
    change p (g x) (nat.succ m) (g ∘ (cons y v)) = p (g x) m.succ (cons (g y) (g ∘ v)),
    rw comp_cons },
  { assume m hm,
    exact (hA m).continuous.comp_continuous_on
      ((hf.cont m hm).comp g.continuous.continuous_on (subset.refl _)) }
end

/-- Composition by continuous linear maps on the right preserves `C^n` functions at a point on
a domain. -/
lemma times_cont_diff_within_at.comp_continuous_linear_map {n : with_top ℕ} {x : G}
  (g : G →L[𝕜] E) (hf : times_cont_diff_within_at 𝕜 n f s (g x)) :
  times_cont_diff_within_at 𝕜 n (f ∘ g) (g ⁻¹' s) x :=
begin
  assume m hm,
  rcases hf m hm with ⟨u, hu, p, hp⟩,
  refine ⟨g ⁻¹' u, _, _, hp.comp_continuous_linear_map g⟩,
  apply continuous_within_at.preimage_mem_nhds_within',
  { exact g.continuous.continuous_within_at },
  { apply nhds_within_mono (g x) _ hu,
    rw image_insert_eq,
    exact insert_subset_insert (image_preimage_subset g s) }
end

/-- Composition by continuous linear maps on the right preserves `C^n` functions on domains. -/
lemma times_cont_diff_on.comp_continuous_linear_map {n : with_top ℕ}
  (hf : times_cont_diff_on 𝕜 n f s) (g : G →L[𝕜] E) :
  times_cont_diff_on 𝕜 n (f ∘ g) (g ⁻¹' s) :=
λ x hx, (hf (g x) hx).comp_continuous_linear_map g

/-- Composition by continuous linear maps on the right preserves `C^n` functions. -/
lemma times_cont_diff.comp_continuous_linear_map {n : with_top ℕ} {f : E → F} {g : G →L[𝕜] E}
  (hf : times_cont_diff 𝕜 n f) : times_cont_diff 𝕜 n (f ∘ g) :=
times_cont_diff_on_univ.1 $
times_cont_diff_on.comp_continuous_linear_map (times_cont_diff_on_univ.2 hf) _

/-- Composition by continuous linear equivs on the right respects higher differentiability at a
point in a domain. -/
lemma continuous_linear_equiv.times_cont_diff_within_at_comp_iff {n : with_top ℕ} (e : G ≃L[𝕜] E) :
  times_cont_diff_within_at 𝕜 n (f ∘ e) (e ⁻¹' s) (e.symm x) ↔
  times_cont_diff_within_at 𝕜 n f s x :=
begin
  split,
  { assume H,
    have A : f = (f ∘ e) ∘ e.symm,
      by { ext y, simp only [function.comp_app], rw e.apply_symm_apply y },
    have B : e.symm ⁻¹' (e ⁻¹' s) = s,
      by { rw [← preimage_comp, e.self_comp_symm], refl },
    rw [A, ← B],
    exact H.comp_continuous_linear_map _},
  { assume H,
    have : x = e (e.symm x), by simp,
    rw this at H,
    exact H.comp_continuous_linear_map _ },
end


/-- Composition by continuous linear equivs on the right respects higher differentiability on
domains. -/
lemma continuous_linear_equiv.times_cont_diff_on_comp_iff {n : with_top ℕ} (e : G ≃L[𝕜] E) :
  times_cont_diff_on 𝕜 n (f ∘ e) (e ⁻¹' s) ↔ times_cont_diff_on 𝕜 n f s :=
begin
  refine ⟨λ H, _, λ H, H.comp_continuous_linear_map _⟩,
  have A : f = (f ∘ e) ∘ e.symm,
    by { ext y, simp only [function.comp_app], rw e.apply_symm_apply y },
  have B : e.symm ⁻¹' (e ⁻¹' s) = s,
    by { rw [← preimage_comp, e.self_comp_symm], refl },
  rw [A, ← B],
  exact H.comp_continuous_linear_map _
end

/-- If two functions `f` and `g` admit Taylor series `p` and `q` in a set `s`, then the cartesian
product of `f` and `g` admits the cartesian product of `p` and `q` as a Taylor series. -/
lemma has_ftaylor_series_up_to_on.prod {n : with_top ℕ} (hf : has_ftaylor_series_up_to_on n f p s)
  {g : E → G} {q : E → formal_multilinear_series 𝕜 E G} (hg : has_ftaylor_series_up_to_on n g q s) :
  has_ftaylor_series_up_to_on n (λ y, (f y, g y)) (λ y k, (p y k).prod (q y k)) s :=
begin
  split,
  { assume x hx, rw [← hf.zero_eq x hx, ← hg.zero_eq x hx], refl },
  { assume m hm x hx,
    let A : (E [×m]→L[𝕜] F) × (E [×m]→L[𝕜] G) → (E [×m]→L[𝕜] (F × G)) := λ p, p.1.prod p.2,
    have hA : is_bounded_linear_map 𝕜 A := is_bounded_linear_map_prod_multilinear,
    convert hA.has_fderiv_at.comp_has_fderiv_within_at x
      ((hf.fderiv_within m hm x hx).prod (hg.fderiv_within m hm x hx)) },
  { assume m hm,
    let A : (E [×m]→L[𝕜] F) × (E [×m]→L[𝕜] G) → (E [×m]→L[𝕜] (F × G)) := λ p, p.1.prod p.2,
    have hA : is_bounded_linear_map 𝕜 A := is_bounded_linear_map_prod_multilinear,
    exact hA.continuous.comp_continuous_on ((hf.cont m hm).prod (hg.cont m hm)) }
end

/-- The cartesian product of `C^n` functions at a point in a domain is `C^n`. -/
lemma times_cont_diff_within_at.prod {n : with_top ℕ} {s : set E} {f : E → F} {g : E → G}
  (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g s x) :
  times_cont_diff_within_at 𝕜 n (λx:E, (f x, g x)) s x :=
begin
  assume m hm,
  rcases hf m hm with ⟨u, hu, p, hp⟩,
  rcases hg m hm with ⟨v, hv, q, hq⟩,
  exact ⟨u ∩ v, filter.inter_mem_sets hu hv, _,
        (hp.mono (inter_subset_left u v)).prod (hq.mono (inter_subset_right u v))⟩
end

/-- The cartesian product of `C^n` functions on domains is `C^n`. -/
lemma times_cont_diff_on.prod {n : with_top ℕ} {s : set E} {f : E → F} {g : E → G}
  (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) :
  times_cont_diff_on 𝕜 n (λx:E, (f x, g x)) s :=
λ x hx, (hf x hx).prod (hg x hx)

/-- The cartesian product of `C^n` functions at a point is `C^n`. -/
lemma times_cont_diff_at.prod {n : with_top ℕ} {f : E → F} {g : E → G}
  (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g x) :
  times_cont_diff_at 𝕜 n (λx:E, (f x, g x)) x :=
times_cont_diff_within_at_univ.1 $ times_cont_diff_within_at.prod (times_cont_diff_within_at_univ.2 hf)
  (times_cont_diff_within_at_univ.2 hg)

/--
The cartesian product of `C^n` functions is `C^n`.
-/
lemma times_cont_diff.prod {n : with_top ℕ} {f : E → F} {g : E → G}
  (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) :
  times_cont_diff 𝕜 n (λx:E, (f x, g x)) :=
times_cont_diff_on_univ.1 $ times_cont_diff_on.prod (times_cont_diff_on_univ.2 hf)
  (times_cont_diff_on_univ.2 hg)

/-!
### Composition of `C^n` functions

We show that the composition of `C^n` functions is `C^n`. One way to prove it would be to write
the `n`-th derivative of the composition (this is Faà di Bruno's formula) and check its continuity,
but this is very painful. Instead, we go for a simple inductive proof. Assume it is done for `n`.
Then, to check it for `n+1`, one needs to check that the derivative of `g ∘ f` is `C^n`, i.e.,
that `Dg(f x) ⬝ Df(x)` is `C^n`. The term `Dg (f x)` is the composition of two `C^n` functions, so
it is `C^n` by the inductive assumption. The term `Df(x)` is also `C^n`. Then, the matrix
multiplication is the application of a bilinear map (which is `C^∞`, and therefore `C^n`) to
`x ↦ (Dg(f x), Df x)`. As the composition of two `C^n` maps, it is again `C^n`, and we are done.

There is a subtlety in this argument: we apply the inductive assumption to functions on other Banach
spaces. In maths, one would say: prove by induction over `n` that, for all `C^n` maps between all
pairs of Banach spaces, their composition is `C^n`. In Lean, this is fine as long as the spaces
stay in the same universe. This is not the case in the above argument: if `E` lives in universe `u`
and `F` lives in universe `v`, then linear maps from `E` to `F` (to which the derivative of `f`
belongs) is in universe `max u v`. If one could quantify over finitely many universes, the above
proof would work fine, but this is not the case. One could still write the proof considering spaces
in any universe in `u, v, w, max u v, max v w, max u v w`, but it would be extremely tedious and
lead to a lot of duplication. Instead, we formulate the above proof when all spaces live in the same
universe (where everything is fine), and then we deduce the general result by lifting all our spaces
to a common universe. We use the trick that any space `H` is isomorphic through a continuous linear
equiv to `continuous_multilinear_map (λ (i : fin 0), E × F × G) H` to change the universe level,
and then argue that composing with such a linear equiv does not change the fact of being `C^n`,
which we have already proved previously.
-/

/-- Auxiliary lemma proving that the composition of `C^n` functions on domains is `C^n` when all
spaces live in the same universe. Use instead `times_cont_diff_on.comp` which removes the universe
assumption (but is deduced from this one). -/
private lemma times_cont_diff_on.comp_same_univ
  {Eu : Type u} [normed_group Eu] [normed_space 𝕜 Eu]
  {Fu : Type u} [normed_group Fu] [normed_space 𝕜 Fu]
  {Gu : Type u} [normed_group Gu] [normed_space 𝕜 Gu]
  {n : with_top ℕ} {s : set Eu} {t : set Fu} {g : Fu → Gu} {f : Eu → Fu}
  (hg : times_cont_diff_on 𝕜 n g t) (hf : times_cont_diff_on 𝕜 n f s) (st : s ⊆ f ⁻¹' t) :
  times_cont_diff_on 𝕜 n (g ∘ f) s :=
begin
  unfreezingI { induction n using with_top.nat_induction with n IH Itop generalizing Eu Fu Gu },
  { rw times_cont_diff_on_zero at hf hg ⊢,
    exact continuous_on.comp hg hf st },
  { rw times_cont_diff_on_succ_iff_has_fderiv_within_at at hg ⊢,
    assume x hx,
    rcases (times_cont_diff_on_succ_iff_has_fderiv_within_at.1 hf) x hx
      with ⟨u, hu, f', hf', f'_diff⟩,
    rcases hg (f x) (st hx) with ⟨v, hv, g', hg', g'_diff⟩,
    rw insert_eq_of_mem hx at hu ⊢,
    have xu : x ∈ u := mem_of_mem_nhds_within hx hu,
    let w := s ∩ (u ∩ f⁻¹' v),
    have wv : w ⊆ f ⁻¹' v := λ y hy, hy.2.2,
    have wu : w ⊆ u := λ y hy, hy.2.1,
    have ws : w ⊆ s := λ y hy, hy.1,
    refine ⟨w, _, λ y, (g' (f y)).comp (f' y), _, _⟩,
    show w ∈ 𝓝[s] x,
    { apply filter.inter_mem_sets self_mem_nhds_within,
      apply filter.inter_mem_sets hu,
      apply continuous_within_at.preimage_mem_nhds_within',
      { rw ← continuous_within_at_inter' hu,
        exact (hf' x xu).differentiable_within_at.continuous_within_at.mono
          (inter_subset_right _ _) },
      { apply nhds_within_mono _ _ hv,
        exact subset.trans (image_subset_iff.mpr st) (subset_insert (f x) t) } },
    show ∀ y ∈ w,
      has_fderiv_within_at (g ∘ f) ((g' (f y)).comp (f' y)) w y,
    { rintros y ⟨ys, yu, yv⟩,
      exact (hg' (f y) yv).comp y ((hf' y yu).mono wu) wv },
    show times_cont_diff_on 𝕜 n (λ y, (g' (f y)).comp (f' y)) w,
    { have A : times_cont_diff_on 𝕜 n (λ y, g' (f y)) w :=
        IH g'_diff ((hf.of_le (with_top.coe_le_coe.2 (nat.le_succ n))).mono ws) wv,
      have B : times_cont_diff_on 𝕜 n f' w := f'_diff.mono wu,
      have C : times_cont_diff_on 𝕜 n (λ y, (f' y, g' (f y))) w :=
        times_cont_diff_on.prod B A,
      have D : times_cont_diff_on 𝕜 n (λ(p : (Eu →L[𝕜] Fu) × (Fu →L[𝕜] Gu)), p.2.comp p.1) univ :=
        is_bounded_bilinear_map_comp.times_cont_diff.times_cont_diff_on,
      exact IH D C (subset_univ _) } },
  { rw times_cont_diff_on_top at hf hg ⊢,
    assume n,
    apply Itop n (hg n) (hf n) st }
end

/-- The composition of `C^n` functions on domains is `C^n`. -/
lemma times_cont_diff_on.comp
  {n : with_top ℕ} {s : set E} {t : set F} {g : F → G} {f : E → F}
  (hg : times_cont_diff_on 𝕜 n g t) (hf : times_cont_diff_on 𝕜 n f s) (st : s ⊆ f ⁻¹' t) :
  times_cont_diff_on 𝕜 n (g ∘ f) s :=
begin
  /- we lift all the spaces to a common universe, as we have already proved the result in this
  situation. For the lift, we use the trick that `H` is isomorphic through a
  continuous linear equiv to `continuous_multilinear_map 𝕜 (λ (i : fin 0), (E × F × G)) H`, and
  continuous linear equivs respect smoothness classes. -/
  let Eu := continuous_multilinear_map 𝕜 (λ (i : fin 0), (E × F × G)) E,
  letI : normed_group Eu := by apply_instance,
  letI : normed_space 𝕜 Eu := by apply_instance,
  let Fu := continuous_multilinear_map 𝕜 (λ (i : fin 0), (E × F × G)) F,
  letI : normed_group Fu := by apply_instance,
  letI : normed_space 𝕜 Fu := by apply_instance,
  let Gu := continuous_multilinear_map 𝕜 (λ (i : fin 0), (E × F × G)) G,
  letI : normed_group Gu := by apply_instance,
  letI : normed_space 𝕜 Gu := by apply_instance,
  -- declare the isomorphisms
  let isoE : Eu ≃L[𝕜] E := continuous_multilinear_curry_fin0 𝕜 (E × F × G) E,
  let isoF : Fu ≃L[𝕜] F := continuous_multilinear_curry_fin0 𝕜 (E × F × G) F,
  let isoG : Gu ≃L[𝕜] G := continuous_multilinear_curry_fin0 𝕜 (E × F × G) G,
  -- lift the functions to the new spaces, check smoothness there, and then go back.
  let fu : Eu → Fu := (isoF.symm ∘ f) ∘ isoE,
  have fu_diff : times_cont_diff_on 𝕜 n fu (isoE ⁻¹' s),
    by rwa [isoE.times_cont_diff_on_comp_iff, isoF.symm.comp_times_cont_diff_on_iff],
  let gu : Fu → Gu := (isoG.symm ∘ g) ∘ isoF,
  have gu_diff : times_cont_diff_on 𝕜 n gu (isoF ⁻¹' t),
    by rwa [isoF.times_cont_diff_on_comp_iff, isoG.symm.comp_times_cont_diff_on_iff],
  have main : times_cont_diff_on 𝕜 n (gu ∘ fu) (isoE ⁻¹' s),
  { apply times_cont_diff_on.comp_same_univ gu_diff fu_diff,
    assume y hy,
    simp only [fu, continuous_linear_equiv.coe_apply, function.comp_app, mem_preimage],
    rw isoF.apply_symm_apply (f (isoE y)),
    exact st hy },
  have : gu ∘ fu = (isoG.symm ∘ (g ∘ f)) ∘ isoE,
  { ext y,
    simp only [function.comp_apply, gu, fu],
    rw isoF.apply_symm_apply (f (isoE y)) },
  rwa [this, isoE.times_cont_diff_on_comp_iff, isoG.symm.comp_times_cont_diff_on_iff] at main
end

/-- The composition of `C^n` functions on domains is `C^n`. -/
lemma times_cont_diff_on.comp'
  {n : with_top ℕ} {s : set E} {t : set F} {g : F → G} {f : E → F}
  (hg : times_cont_diff_on 𝕜 n g t) (hf : times_cont_diff_on 𝕜 n f s) :
  times_cont_diff_on 𝕜 n (g ∘ f) (s ∩ f⁻¹' t) :=
hg.comp (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

/-- The composition of a `C^n` function on a domain with a `C^n` function is `C^n`. -/
lemma times_cont_diff.comp_times_cont_diff_on {n : with_top ℕ} {s : set E} {g : F → G} {f : E → F}
  (hg : times_cont_diff 𝕜 n g) (hf : times_cont_diff_on 𝕜 n f s) :
  times_cont_diff_on 𝕜 n (g ∘ f) s :=
(times_cont_diff_on_univ.2 hg).comp hf subset_preimage_univ

/-- The composition of `C^n` functions is `C^n`. -/
lemma times_cont_diff.comp {n : with_top ℕ} {g : F → G} {f : E → F}
  (hg : times_cont_diff 𝕜 n g) (hf : times_cont_diff 𝕜 n f) :
  times_cont_diff 𝕜 n (g ∘ f) :=
times_cont_diff_on_univ.1 $ times_cont_diff_on.comp (times_cont_diff_on_univ.2 hg)
  (times_cont_diff_on_univ.2 hf) (subset_univ _)

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
lemma times_cont_diff_within_at.comp
  {n : with_top ℕ} {s : set E} {t : set F} {g : F → G} {f : E → F} (x : E)
  (hg : times_cont_diff_within_at 𝕜 n g t (f x))
  (hf : times_cont_diff_within_at 𝕜 n f s x) (st : s ⊆ f ⁻¹' t) :
  times_cont_diff_within_at 𝕜 n (g ∘ f) s x :=
begin
  assume m hm,
  rcases hg.times_cont_diff_on hm with ⟨u, u_nhd, ut, hu⟩,
  rcases hf.times_cont_diff_on hm with ⟨v, v_nhd, vs, hv⟩,
  have xmem : x ∈ f ⁻¹' u ∩ v :=
    ⟨(mem_of_mem_nhds_within (mem_insert (f x) _) u_nhd : _),
    mem_of_mem_nhds_within (mem_insert x s) v_nhd⟩,
  have : f ⁻¹' u ∈ 𝓝[insert x s] x,
  { apply hf.continuous_within_at.insert_self.preimage_mem_nhds_within',
    apply nhds_within_mono _ _ u_nhd,
    rw image_insert_eq,
    exact insert_subset_insert (image_subset_iff.mpr st) },
  have Z := ((hu.comp (hv.mono (inter_subset_right (f ⁻¹' u) v)) (inter_subset_left _ _))
    .times_cont_diff_within_at) xmem m (le_refl _),
  have : 𝓝[f ⁻¹' u ∩ v] x = 𝓝[insert x s] x,
  { have A : f ⁻¹' u ∩ v = (insert x s) ∩ (f ⁻¹' u ∩ v),
    { apply subset.antisymm _ (inter_subset_right _ _),
      rintros y ⟨hy1, hy2⟩,
      simp [hy1, hy2, vs hy2] },
    rw [A, ← nhds_within_restrict''],
    exact filter.inter_mem_sets this v_nhd },
  rwa [insert_eq_of_mem xmem, this] at Z,
end

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
lemma times_cont_diff_within_at.comp' {n : with_top ℕ} {s : set E} {t : set F} {g : F → G}
  {f : E → F} (x : E)
  (hg : times_cont_diff_within_at 𝕜 n g t (f x)) (hf : times_cont_diff_within_at 𝕜 n f s x) :
  times_cont_diff_within_at 𝕜 n (g ∘ f) (s ∩ f⁻¹' t) x :=
hg.comp x (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

lemma times_cont_diff_at.comp_times_cont_diff_within_at {n} (x : E)
  (hg : times_cont_diff_at 𝕜 n g (f x)) (hf : times_cont_diff_within_at 𝕜 n f s x) :
  times_cont_diff_within_at 𝕜 n (g ∘ f) s x :=
hg.comp x hf (maps_to_univ _ _)

/-- The composition of `C^n` functions at points is `C^n`. -/
lemma times_cont_diff_at.comp {n : with_top ℕ} (x : E)
  (hg : times_cont_diff_at 𝕜 n g (f x))
  (hf : times_cont_diff_at 𝕜 n f x) :
  times_cont_diff_at 𝕜 n (g ∘ f) x :=
hg.comp x hf subset_preimage_univ

lemma times_cont_diff.comp_times_cont_diff_within_at
  {n : with_top ℕ} {g : F → G} {f : E → F} (h : times_cont_diff 𝕜 n g)
  (hf : times_cont_diff_within_at 𝕜 n f t x) :
  times_cont_diff_within_at 𝕜 n (g ∘ f) t x :=
begin
  have : times_cont_diff_within_at 𝕜 n g univ (f x) :=
    h.times_cont_diff_at.times_cont_diff_within_at,
  exact this.comp x hf (subset_univ _),
end

lemma times_cont_diff.comp_times_cont_diff_at
  {n : with_top ℕ} {g : F → G} {f : E → F} (x : E)
  (hg : times_cont_diff 𝕜 n g)
  (hf : times_cont_diff_at 𝕜 n f x) :
  times_cont_diff_at 𝕜 n (g ∘ f) x :=
hg.comp_times_cont_diff_within_at hf

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
lemma times_cont_diff_on_fderiv_within_apply {m n : with_top  ℕ} {s : set E}
  {f : E → F} (hf : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hmn : m + 1 ≤ n) :
  times_cont_diff_on 𝕜 m (λp : E × E, (fderiv_within 𝕜 f s p.1 : E →L[𝕜] F) p.2)
  (set.prod s (univ : set E)) :=
begin
  have A : times_cont_diff 𝕜 m (λp : (E →L[𝕜] F) × E, p.1 p.2),
  { apply is_bounded_bilinear_map.times_cont_diff,
    exact is_bounded_bilinear_map_apply },
  have B : times_cont_diff_on 𝕜 m
    (λ (p : E × E), ((fderiv_within 𝕜 f s p.fst), p.snd)) (set.prod s univ),
  { apply times_cont_diff_on.prod _ _,
    { have I : times_cont_diff_on 𝕜 m (λ (x : E), fderiv_within 𝕜 f s x) s :=
        hf.fderiv_within hs hmn,
      have J : times_cont_diff_on 𝕜 m (λ (x : E × E), x.1) (set.prod s univ) :=
        times_cont_diff_fst.times_cont_diff_on,
      exact times_cont_diff_on.comp I J (prod_subset_preimage_fst _ _) },
    { apply times_cont_diff.times_cont_diff_on _ ,
      apply is_bounded_linear_map.snd.times_cont_diff } },
  exact A.comp_times_cont_diff_on B
end

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
lemma times_cont_diff.times_cont_diff_fderiv_apply {n m : with_top ℕ} {f : E → F}
  (hf : times_cont_diff 𝕜 n f) (hmn : m + 1 ≤ n) :
  times_cont_diff 𝕜 m (λp : E × E, (fderiv 𝕜 f p.1 : E →L[𝕜] F) p.2) :=
begin
  rw ← times_cont_diff_on_univ at ⊢ hf,
  rw [← fderiv_within_univ, ← univ_prod_univ],
  exact times_cont_diff_on_fderiv_within_apply hf unique_diff_on_univ hmn
end

/-! ### Sum of two functions -/

/- The sum is smooth. -/
lemma times_cont_diff_add {n : with_top ℕ} :
  times_cont_diff 𝕜 n (λp : F × F, p.1 + p.2) :=
(is_bounded_linear_map.fst.add is_bounded_linear_map.snd).times_cont_diff

/-- The sum of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
lemma times_cont_diff_within_at.add {n : with_top ℕ} {s : set E} {f g : E → F}
  (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g s x) :
  times_cont_diff_within_at 𝕜 n (λx, f x + g x) s x :=
times_cont_diff_add.times_cont_diff_within_at.comp x (hf.prod hg) subset_preimage_univ

/-- The sum of two `C^n` functions at a point is `C^n` at this point. -/
lemma times_cont_diff_at.add {n : with_top ℕ} {f g : E → F}
  (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g x) :
  times_cont_diff_at 𝕜 n (λx, f x + g x) x :=
by rw [← times_cont_diff_within_at_univ] at *; exact hf.add hg

/-- The sum of two `C^n`functions is `C^n`. -/
lemma times_cont_diff.add {n : with_top ℕ} {f g : E → F}
  (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) :
  times_cont_diff 𝕜 n (λx, f x + g x) :=
times_cont_diff_add.comp (hf.prod hg)

/-- The sum of two `C^n` functions on a domain is `C^n`. -/
lemma times_cont_diff_on.add {n : with_top ℕ} {s : set E} {f g : E → F}
  (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) :
  times_cont_diff_on 𝕜 n (λx, f x + g x) s :=
λ x hx, (hf x hx).add (hg x hx)

/-! ### Negative -/

/- The negative is smooth. -/
lemma times_cont_diff_neg {n : with_top ℕ} :
  times_cont_diff 𝕜 n (λp : F, -p) :=
is_bounded_linear_map.id.neg.times_cont_diff

/-- The negative of a `C^n` function within a domain at a point is `C^n` within this domain at
this point. -/
lemma times_cont_diff_within_at.neg {n : with_top ℕ} {s : set E} {f : E → F}
  (hf : times_cont_diff_within_at 𝕜 n f s x) : times_cont_diff_within_at 𝕜 n (λx, -f x) s x :=
times_cont_diff_neg.times_cont_diff_within_at.comp x hf subset_preimage_univ

/-- The negative of a `C^n` function at a point is `C^n` at this point. -/
lemma times_cont_diff_at.neg {n : with_top ℕ} {f : E → F}
  (hf : times_cont_diff_at 𝕜 n f x) : times_cont_diff_at 𝕜 n (λx, -f x) x :=
by rw ← times_cont_diff_within_at_univ at *; exact hf.neg

/-- The negative of a `C^n`function is `C^n`. -/
lemma times_cont_diff.neg {n : with_top ℕ} {f : E → F} (hf : times_cont_diff 𝕜 n f) :
  times_cont_diff 𝕜 n (λx, -f x) :=
times_cont_diff_neg.comp hf

/-- The negative of a `C^n` function on a domain is `C^n`. -/
lemma times_cont_diff_on.neg {n : with_top ℕ} {s : set E} {f : E → F}
  (hf : times_cont_diff_on 𝕜 n f s) : times_cont_diff_on 𝕜 n (λx, -f x) s :=
λ x hx, (hf x hx).neg

/-! ### Subtraction -/

/-- The difference of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
lemma times_cont_diff_within_at.sub {n : with_top ℕ} {s : set E} {f g : E → F}
  (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g s x) :
  times_cont_diff_within_at 𝕜 n (λx, f x - g x) s x :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions at a point is `C^n` at this point. -/
lemma times_cont_diff_at.sub {n : with_top ℕ} {f g : E → F}
  (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g x) :
  times_cont_diff_at 𝕜 n (λx, f x - g x) x :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions on a domain is `C^n`. -/
lemma times_cont_diff_on.sub {n : with_top ℕ} {s : set E} {f g : E → F}
  (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) :
  times_cont_diff_on 𝕜 n (λx, f x - g x) s :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions is `C^n`. -/
lemma times_cont_diff.sub {n : with_top ℕ} {f g : E → F}
  (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) : times_cont_diff 𝕜 n (λx, f x - g x) :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

/-! ### Sum of finitely many functions -/

lemma times_cont_diff_within_at.sum
  {ι : Type*} {f : ι → E → F} {s : finset ι} {n : with_top ℕ} {t : set E} {x : E}
  (h : ∀ i ∈ s, times_cont_diff_within_at 𝕜 n (λ x, f i x) t x) :
  times_cont_diff_within_at 𝕜 n (λ x, (∑ i in s, f i x)) t x :=
begin
  classical,
  induction s using finset.induction_on with i s is IH,
  { simp [times_cont_diff_within_at_const] },
  { simp only [is, finset.sum_insert, not_false_iff],
    exact (h _ (finset.mem_insert_self i s)).add (IH (λ j hj, h _ (finset.mem_insert_of_mem hj))) }
end

lemma times_cont_diff_at.sum
  {ι : Type*} {f : ι → E → F} {s : finset ι} {n : with_top ℕ} {x : E}
  (h : ∀ i ∈ s, times_cont_diff_at 𝕜 n (λ x, f i x) x) :
  times_cont_diff_at 𝕜 n (λ x, (∑ i in s, f i x)) x :=
by rw [← times_cont_diff_within_at_univ] at *; exact times_cont_diff_within_at.sum h

lemma times_cont_diff_on.sum
  {ι : Type*} {f : ι → E → F} {s : finset ι} {n : with_top ℕ} {t : set E}
  (h : ∀ i ∈ s, times_cont_diff_on 𝕜 n (λ x, f i x) t) :
  times_cont_diff_on 𝕜 n (λ x, (∑ i in s, f i x)) t :=
λ x hx, times_cont_diff_within_at.sum (λ i hi, h i hi x hx)

lemma times_cont_diff.sum
  {ι : Type*} {f : ι → E → F} {s : finset ι} {n : with_top ℕ}
  (h : ∀ i ∈ s, times_cont_diff 𝕜 n (λ x, f i x)) :
  times_cont_diff 𝕜 n (λ x, (∑ i in s, f i x)) :=
by simp [← times_cont_diff_on_univ] at *; exact times_cont_diff_on.sum h

/-! ### Product of two functions -/

/- The product is smooth. -/
lemma times_cont_diff_mul {n : with_top ℕ} :
  times_cont_diff 𝕜 n (λ p : 𝕜 × 𝕜, p.1 * p.2) :=
is_bounded_bilinear_map_mul.times_cont_diff

/-- The product of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
lemma times_cont_diff_within_at.mul {n : with_top ℕ} {s : set E} {f g : E → 𝕜}
  (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g s x) :
  times_cont_diff_within_at 𝕜 n (λ x, f x * g x) s x :=
times_cont_diff_mul.times_cont_diff_within_at.comp x (hf.prod hg) subset_preimage_univ

/-- The product of two `C^n` functions at a point is `C^n` at this point. -/
lemma times_cont_diff_at.mul {n : with_top ℕ} {f g : E → 𝕜}
  (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g x) :
  times_cont_diff_at 𝕜 n (λ x, f x * g x) x :=
by rw [← times_cont_diff_within_at_univ] at *; exact hf.mul hg

/-- The product of two `C^n` functions on a domain is `C^n`. -/
lemma times_cont_diff_on.mul {n : with_top ℕ} {s : set E} {f g : E → 𝕜}
  (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) :
  times_cont_diff_on 𝕜 n (λ x, f x * g x) s :=
λ x hx, (hf x hx).mul (hg x hx)

/-- The product of two `C^n`functions is `C^n`. -/
lemma times_cont_diff.mul {n : with_top ℕ} {f g : E → 𝕜}
  (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) :
  times_cont_diff 𝕜 n (λ x, f x * g x) :=
times_cont_diff_mul.comp (hf.prod hg)

lemma times_cont_diff_within_at.div_const {f : E → 𝕜} {n} {c : 𝕜}
  (hf : times_cont_diff_within_at 𝕜 n f s x) :
  times_cont_diff_within_at 𝕜 n (λ x, f x / c) s x :=
by simp only [div_eq_mul_inv, hf.mul times_cont_diff_within_at_const]

lemma times_cont_diff_at.div_const {f : E → 𝕜} {n} {c : 𝕜} (hf : times_cont_diff_at 𝕜 n f x) :
  times_cont_diff_at 𝕜 n (λ x, f x / c) x :=
by simp only [div_eq_mul_inv, hf.mul times_cont_diff_at_const]

lemma times_cont_diff_on.div_const {f : E → 𝕜} {n} {c : 𝕜} (hf : times_cont_diff_on 𝕜 n f s) :
  times_cont_diff_on 𝕜 n (λ x, f x / c) s :=
by simp only [div_eq_mul_inv, hf.mul times_cont_diff_on_const]

lemma times_cont_diff.div_const {f : E → 𝕜} {n} {c : 𝕜} (hf : times_cont_diff 𝕜 n f) :
  times_cont_diff 𝕜 n (λ x, f x / c) :=
by simp only [div_eq_mul_inv, hf.mul times_cont_diff_const]

lemma times_cont_diff.pow {n : with_top ℕ} {f : E → 𝕜}
  (hf : times_cont_diff 𝕜 n f) :
  ∀ m : ℕ, times_cont_diff 𝕜 n (λ x, (f x) ^ m)
| 0 := by simpa using times_cont_diff_const
| (m + 1) := hf.mul (times_cont_diff.pow m)

/-! ### Scalar multiplication -/

/- The scalar multiplication is smooth. -/
lemma times_cont_diff_smul {n : with_top ℕ} :
  times_cont_diff 𝕜 n (λ p : 𝕜 × F, p.1 • p.2) :=
is_bounded_bilinear_map_smul.times_cont_diff

/-- The scalar multiplication of two `C^n` functions within a set at a point is `C^n` within this
set at this point. -/
lemma times_cont_diff_within_at.smul {n : with_top ℕ} {s : set E} {f : E → 𝕜} {g : E → F}
  (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g s x) :
  times_cont_diff_within_at 𝕜 n (λ x, f x • g x) s x :=
times_cont_diff_smul.times_cont_diff_within_at.comp x (hf.prod hg) subset_preimage_univ

/-- The scalar multiplication of two `C^n` functions at a point is `C^n` at this point. -/
lemma times_cont_diff_at.smul {n : with_top ℕ} {f : E → 𝕜} {g : E → F}
  (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g x) :
  times_cont_diff_at 𝕜 n (λ x, f x • g x) x :=
by rw [← times_cont_diff_within_at_univ] at *; exact hf.smul hg

/-- The scalar multiplication of two `C^n` functions is `C^n`. -/
lemma times_cont_diff.smul {n : with_top ℕ} {f : E → 𝕜} {g : E → F}
  (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) :
  times_cont_diff 𝕜 n (λ x, f x • g x) :=
times_cont_diff_smul.comp (hf.prod hg)

/-- The scalar multiplication of two `C^n` functions on a domain is `C^n`. -/
lemma times_cont_diff_on.smul {n : with_top ℕ} {s : set E} {f : E → 𝕜} {g : E → F}
  (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) :
  times_cont_diff_on 𝕜 n (λ x, f x • g x) s :=
λ x hx, (hf x hx).smul (hg x hx)

/-! ### Cartesian product of two functions-/

section prod_map
variables {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{n : with_top ℕ}

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
lemma times_cont_diff_within_at.prod_map'
  {s : set E} {t : set E'} {f : E → F} {g : E' → F'} {p : E × E'}
  (hf : times_cont_diff_within_at 𝕜 n f s p.1) (hg : times_cont_diff_within_at 𝕜 n g t p.2) :
  times_cont_diff_within_at 𝕜 n (prod.map f g) (set.prod s t) p :=
(hf.comp p times_cont_diff_within_at_fst (prod_subset_preimage_fst _ _)).prod
  (hg.comp p times_cont_diff_within_at_snd (prod_subset_preimage_snd _ _))

lemma times_cont_diff_within_at.prod_map
  {s : set E} {t : set E'} {f : E → F} {g : E' → F'} {x : E} {y : E'}
  (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g t y) :
  times_cont_diff_within_at 𝕜 n (prod.map f g) (set.prod s t) (x, y) :=
times_cont_diff_within_at.prod_map' hf hg

/-- The product map of two `C^n` functions on a set is `C^n` on the product set. -/
lemma times_cont_diff_on.prod_map {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {F' : Type*} [normed_group F'] [normed_space 𝕜 F']
  {s : set E} {t : set E'} {n : with_top ℕ} {f : E → F} {g : E' → F'}
  (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g t) :
  times_cont_diff_on 𝕜 n (prod.map f g) (set.prod s t) :=
(hf.comp times_cont_diff_on_fst (prod_subset_preimage_fst _ _)).prod
  (hg.comp (times_cont_diff_on_snd) (prod_subset_preimage_snd _ _))

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
lemma times_cont_diff_at.prod_map {f : E → F} {g : E' → F'} {x : E} {y : E'}
  (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g y) :
  times_cont_diff_at 𝕜 n (prod.map f g) (x, y) :=
begin
  rw times_cont_diff_at at *,
  convert hf.prod_map hg,
  simp only [univ_prod_univ]
end

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
lemma times_cont_diff_at.prod_map' {f : E → F} {g : E' → F'} {p : E × E'}
  (hf : times_cont_diff_at 𝕜 n f p.1) (hg : times_cont_diff_at 𝕜 n g p.2) :
  times_cont_diff_at 𝕜 n (prod.map f g) p :=
begin
  rcases p,
  exact times_cont_diff_at.prod_map hf hg
end

/-- The product map of two `C^n` functions is `C^n`. -/
lemma times_cont_diff.prod_map
  {f : E → F} {g : E' → F'}
  (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) :
  times_cont_diff 𝕜 n (prod.map f g) :=
begin
  rw times_cont_diff_iff_times_cont_diff_at at *,
  exact λ ⟨x, y⟩, (hf x).prod_map (hg y)
end

end prod_map

/-! ### Inversion in a complete normed algebra -/

section algebra_inverse
variables (𝕜) {R : Type*} [normed_ring R] [normed_algebra 𝕜 R]
open normed_ring continuous_linear_map ring

/-- In a complete normed algebra, the operation of inversion is `C^n`, for all `n`, at each
invertible element.  The proof is by induction, bootstrapping using an identity expressing the
derivative of inversion as a bilinear map of inversion itself. -/
lemma times_cont_diff_at_ring_inverse [complete_space R] {n : with_top ℕ} (x : units R) :
  times_cont_diff_at 𝕜 n ring.inverse (x : R) :=
begin
  induction n using with_top.nat_induction with n IH Itop,
  { intros m hm,
    refine ⟨{y : R | is_unit y}, _, _⟩,
    { simp [nhds_within_univ],
      exact x.nhds },
    { use (ftaylor_series_within 𝕜 inverse univ),
      rw [le_antisymm hm bot_le, has_ftaylor_series_up_to_on_zero_iff],
      split,
      { rintros _ ⟨x', hx'⟩,
        rw ← hx',
        exact (inverse_continuous_at x').continuous_within_at },
      { simp [ftaylor_series_within] } } },
  { apply times_cont_diff_at_succ_iff_has_fderiv_at.mpr,
    refine ⟨λ (x : R), - lmul_left_right 𝕜 R (inverse x, inverse x), _, _⟩,
    { refine ⟨{y : R | is_unit y}, x.nhds, _⟩,
      intros y hy,
      cases mem_set_of_eq.mp hy with y' hy',
      rw [← hy', units.inverse_eq],
      exact @has_fderiv_at_ring_inverse 𝕜 _ _ _ _ _ y' },
    { exact (lmul_left_right_is_bounded_bilinear 𝕜 R).times_cont_diff.neg.comp_times_cont_diff_at
        (x : R) (IH.prod IH) } },
  { exact times_cont_diff_at_top.mpr Itop }
end

variables (𝕜) {𝕜' : Type*} [normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] [complete_space 𝕜']

lemma times_cont_diff_at_inv {x : 𝕜'} (hx : x ≠ 0) {n} :
  times_cont_diff_at 𝕜 n has_inv.inv x :=
by simpa only [inverse_eq_has_inv] using times_cont_diff_at_ring_inverse 𝕜 (units.mk0 x hx)

lemma times_cont_diff_on_inv {n} : times_cont_diff_on 𝕜 n (has_inv.inv : 𝕜' → 𝕜') {0}ᶜ :=
λ x hx, (times_cont_diff_at_inv 𝕜 hx).times_cont_diff_within_at

variable {𝕜}

-- TODO: the next few lemmas don't need `𝕜` or `𝕜'` to be complete
-- A good way to show this is to generalize `times_cont_diff_at_ring_inverse` to the setting
-- of a function `f` such that `∀ᶠ x in 𝓝 a, x * f x = 1`.

lemma times_cont_diff_within_at.inv {f : E → 𝕜'} {n} (hf : times_cont_diff_within_at 𝕜 n f s x)
  (hx : f x ≠ 0) :
  times_cont_diff_within_at 𝕜 n (λ x, (f x)⁻¹) s x :=
(times_cont_diff_at_inv 𝕜 hx).comp_times_cont_diff_within_at x hf

lemma times_cont_diff_at.inv {f : E → 𝕜'} {n} (hf : times_cont_diff_at 𝕜 n f x) (hx : f x ≠ 0) :
  times_cont_diff_at 𝕜 n (λ x, (f x)⁻¹) x :=
hf.inv hx

-- TODO: generalize to `f g : E → 𝕜'`
lemma times_cont_diff_within_at.div [complete_space 𝕜] {f g : E → 𝕜} {n}
  (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g s x)
  (hx : g x ≠ 0) :
  times_cont_diff_within_at 𝕜 n (λ x, f x / g x) s x :=
by simpa only [div_eq_mul_inv] using hf.mul (hg.inv hx)

lemma times_cont_diff_at.div [complete_space 𝕜] {f g : E → 𝕜} {n}
  (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g x)
  (hx : g x ≠ 0) :
  times_cont_diff_at 𝕜 n (λ x, f x / g x) x :=
hf.div hg hx

lemma times_cont_diff.div [complete_space 𝕜] {f g : E → 𝕜} {n}
  (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g)
  (h0 : ∀ x, g x ≠ 0) :
  times_cont_diff 𝕜 n (λ x, f x / g x) :=
begin
  simp only [times_cont_diff_iff_times_cont_diff_at] at *,
  exact λ x, (hf x).div (hg x) (h0 x)
end

end algebra_inverse

/-! ### Inversion of continuous linear maps between Banach spaces -/

section map_inverse
open continuous_linear_map

/-- At a continuous linear equivalence `e : E ≃L[𝕜] F` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
lemma times_cont_diff_at_map_inverse [complete_space E] {n : with_top ℕ} (e : E ≃L[𝕜] F) :
  times_cont_diff_at 𝕜 n inverse (e : E →L[𝕜] F) :=
begin
  nontriviality E,
  -- first, we use the lemma `to_ring_inverse` to rewrite in terms of `ring.inverse` in the ring
  -- `E →L[𝕜] E`
  let O₁ : (E →L[𝕜] E) → (F →L[𝕜] E) := λ f, f.comp (e.symm : (F →L[𝕜] E)),
  let O₂ : (E →L[𝕜] F) → (E →L[𝕜] E) := λ f, (e.symm : (F →L[𝕜] E)).comp f,
  have : continuous_linear_map.inverse = O₁ ∘ ring.inverse ∘ O₂ :=
    funext (to_ring_inverse e),
  rw this,
  -- `O₁` and `O₂` are `times_cont_diff`, so we reduce to proving that `ring.inverse` is `times_cont_diff`
  have h₁ : times_cont_diff 𝕜 n O₁,
    from is_bounded_bilinear_map_comp.times_cont_diff.comp
      (times_cont_diff_const.prod times_cont_diff_id),
  have h₂ : times_cont_diff 𝕜 n O₂,
    from is_bounded_bilinear_map_comp.times_cont_diff.comp
      (times_cont_diff_id.prod times_cont_diff_const),
  refine h₁.times_cont_diff_at.comp _ (times_cont_diff_at.comp _ _ h₂.times_cont_diff_at),
  convert times_cont_diff_at_ring_inverse 𝕜 (1 : units (E →L[𝕜] E)),
  simp [O₂, one_def]
end

end map_inverse

section function_inverse
open continuous_linear_map

/-- If `f` is a local homeomorphism and the point `a` is in its target, and if `f` is `n` times
continuously differentiable at `f.symm a`, and if the derivative at `f.symm a` is a continuous linear
equivalence, then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem local_homeomorph.times_cont_diff_at_symm [complete_space E] {n : with_top ℕ}
  (f : local_homeomorph E F) {f₀' : E ≃L[𝕜] F} {a : F} (ha : a ∈ f.target)
  (hf₀' : has_fderiv_at f (f₀' : E →L[𝕜] F) (f.symm a)) (hf : times_cont_diff_at 𝕜 n f (f.symm a)) :
  times_cont_diff_at 𝕜 n f.symm a :=
begin
  -- We prove this by induction on `n`
  induction n using with_top.nat_induction with n IH Itop,
  { rw times_cont_diff_at_zero,
    exact ⟨f.target, mem_nhds_sets f.open_target ha, f.continuous_inv_fun⟩ },
  { obtain ⟨f', ⟨u, hu, hff'⟩, hf'⟩ := times_cont_diff_at_succ_iff_has_fderiv_at.mp hf,
    apply times_cont_diff_at_succ_iff_has_fderiv_at.mpr,
    -- For showing `n.succ` times continuous differentiability (the main inductive step), it
    -- suffices to produce the derivative and show that it is `n` times continuously differentiable
    have eq_f₀' : f' (f.symm a) = f₀',
    { exact has_fderiv_at_unique (hff' (f.symm a) (mem_of_nhds hu)) hf₀' },
    -- This follows by a bootstrapping formula expressing the derivative as a function of `f` itself
    refine ⟨inverse ∘ f' ∘ f.symm, _, _⟩,
    { -- We first check that the derivative of `f` is that formula
      have h_nhds : {y : E | ∃ (e : E ≃L[𝕜] F), ↑e = f' y} ∈ 𝓝 ((f.symm) a),
      { have hf₀' := f₀'.nhds,
        rw ← eq_f₀' at hf₀',
        exact hf'.continuous_at.preimage_mem_nhds hf₀' },
      obtain ⟨t, htu, ht, htf⟩ := mem_nhds_sets_iff.mp (filter.inter_mem_sets hu h_nhds),
      use f.target ∩ (f.symm) ⁻¹' t,
      refine ⟨mem_nhds_sets _ _, _⟩,
      { exact f.preimage_open_of_open_symm ht },
      { exact mem_inter ha (mem_preimage.mpr htf) },
      intros x hx,
      obtain ⟨hxu, e, he⟩ := htu hx.2,
      have h_deriv : has_fderiv_at f ↑e ((f.symm) x),
      { rw he,
        exact hff' (f.symm x) hxu },
      convert f.has_fderiv_at_symm hx.1 h_deriv,
      simp [← he] },
    { -- Then we check that the formula, being a composition of `times_cont_diff` pieces, is
      -- itself `times_cont_diff`
      have h_deriv₁ : times_cont_diff_at 𝕜 n inverse (f' (f.symm a)),
      { rw eq_f₀',
        exact times_cont_diff_at_map_inverse _ },
      have h_deriv₂ : times_cont_diff_at 𝕜 n f.symm a,
      { refine IH (hf.of_le _),
        norm_cast,
        exact nat.le_succ n },
      exact (h_deriv₁.comp _ hf').comp _ h_deriv₂ } },
  { refine times_cont_diff_at_top.mpr _,
    intros n,
    exact Itop n (times_cont_diff_at_top.mp hf n) }
end

/-- Let `f` be a local homeomorphism of a nondiscrete normed field, let `a` be a point in its
target. if `f` is `n` times continuously differentiable at `f.symm a`, and if the derivative at
`f.symm a` is nonzero, then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem local_homeomorph.times_cont_diff_at_symm_deriv [complete_space 𝕜] {n : with_top ℕ}
  (f : local_homeomorph 𝕜 𝕜) {f₀' a : 𝕜} (h₀ : f₀' ≠ 0) (ha : a ∈ f.target)
  (hf₀' : has_deriv_at f f₀' (f.symm a)) (hf : times_cont_diff_at 𝕜 n f (f.symm a)) :
  times_cont_diff_at 𝕜 n f.symm a :=
f.times_cont_diff_at_symm ha (hf₀'.has_fderiv_at_equiv h₀) hf

end function_inverse

section real
/-!
### Results over `ℝ`
  The results in this section rely on the Mean Value Theorem, and therefore hold only over `ℝ` (and
  its extension fields such as `ℂ`).
-/

variables
{E' : Type*} [normed_group E'] [normed_space ℝ E']
{F' : Type*} [normed_group F'] [normed_space ℝ F']

/-- If a function has a Taylor series at order at least 1, then at points in the interior of the
    domain of definition, the term of order 1 of this series is a strict derivative of `f`. -/
lemma has_ftaylor_series_up_to_on.has_strict_fderiv_at
  {s : set E'} {f : E' → F'} {x : E'} {p : E' → formal_multilinear_series ℝ E' F'} {n : with_top ℕ}
  (hf : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) (hs : s ∈ 𝓝 x) :
  has_strict_fderiv_at f ((continuous_multilinear_curry_fin1 ℝ E' F') (p x 1)) x :=
begin
  let f' := λ x, (continuous_multilinear_curry_fin1 ℝ E' F') (p x 1),
  have hf' : ∀ x, x ∈ s → has_fderiv_within_at f (f' x) s x :=
    λ x, has_ftaylor_series_up_to_on.has_fderiv_within_at hf hn,
  have hcont : continuous_on f' s :=
    (continuous_multilinear_curry_fin1 ℝ E' F').continuous.comp_continuous_on (hf.cont 1 hn),
  exact strict_fderiv_of_cont_diff hf' hcont hs,
end

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
lemma times_cont_diff_at.has_strict_fderiv_at {f : E' → F'} {x : E'} {n : with_top ℕ}
  (hf : times_cont_diff_at ℝ n f x) (hn : 1 ≤ n) :
  has_strict_fderiv_at f (fderiv ℝ f x) x :=
begin
  rcases hf 1 hn with ⟨u, H, p, hp⟩,
  simp only [nhds_within_univ, mem_univ, insert_eq_of_mem] at H,
  have := hp.has_strict_fderiv_at (by norm_num) H,
  convert this,
  exact this.has_fderiv_at.fderiv
end

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
lemma times_cont_diff_at.has_strict_fderiv_at'
  {f : E' → F'} {f' : E' →L[ℝ] F'} {x : E'}
  {n : with_top ℕ} (hf : times_cont_diff_at ℝ n f x) (hf' : has_fderiv_at f f' x) (hn : 1 ≤ n) :
  has_strict_fderiv_at f f' x :=
by simpa only [hf'.fderiv] using hf.has_strict_fderiv_at hn

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
lemma times_cont_diff.has_strict_fderiv_at
  {f : E' → F'} {x : E'} {n : with_top ℕ} (hf : times_cont_diff ℝ n f) (hn : 1 ≤ n) :
  has_strict_fderiv_at f (fderiv ℝ f x) x :=
hf.times_cont_diff_at.has_strict_fderiv_at hn

end real

section deriv
/-!
### One dimension

All results up to now have been expressed in terms of the general Fréchet derivative `fderiv`. For
maps defined on the field, the one-dimensional derivative `deriv` is often easier to use. In this
paragraph, we reformulate some higher smoothness results in terms of `deriv`.
-/

variables {f₂ : 𝕜 → F} {s₂ : set 𝕜}
open continuous_linear_map (smul_right)

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (formulated with `deriv_within`) is `C^n`. -/
theorem times_cont_diff_on_succ_iff_deriv_within {n : ℕ} (hs : unique_diff_on 𝕜 s₂) :
  times_cont_diff_on 𝕜 ((n + 1) : ℕ) f₂ s₂ ↔
  differentiable_on 𝕜 f₂ s₂ ∧ times_cont_diff_on 𝕜 n (deriv_within f₂ s₂) s₂ :=
begin
  rw times_cont_diff_on_succ_iff_fderiv_within hs,
  congr' 2,
  rw ← iff_iff_eq,
  split,
  { assume h,
    have : deriv_within f₂ s₂ = (λ u : 𝕜 →L[𝕜] F, u 1) ∘ (fderiv_within 𝕜 f₂ s₂),
      by { ext x, refl },
    simp only [this],
    apply times_cont_diff.comp_times_cont_diff_on _ h,
    exact (is_bounded_bilinear_map_apply.is_bounded_linear_map_left _).times_cont_diff },
  { assume h,
    have : fderiv_within 𝕜 f₂ s₂ = (λ u, smul_right 1 u) ∘ (λ x, deriv_within f₂ s₂ x),
      by { ext x, simp [deriv_within] },
    simp only [this],
    apply times_cont_diff.comp_times_cont_diff_on _ h,
    exact (is_bounded_bilinear_map_smul_right.is_bounded_linear_map_right _).times_cont_diff }
end

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (formulated with `deriv`) is `C^n`. -/
theorem times_cont_diff_on_succ_iff_deriv_of_open {n : ℕ} (hs : is_open s₂) :
  times_cont_diff_on 𝕜 ((n + 1) : ℕ) f₂ s₂ ↔
  differentiable_on 𝕜 f₂ s₂ ∧ times_cont_diff_on 𝕜 n (deriv f₂) s₂ :=
begin
  rw times_cont_diff_on_succ_iff_deriv_within hs.unique_diff_on,
  congr' 2,
  rw ← iff_iff_eq,
  apply times_cont_diff_on_congr,
  assume x hx,
  exact deriv_within_of_open hs hx
end

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (formulated with `deriv_within`) is `C^∞`. -/
theorem times_cont_diff_on_top_iff_deriv_within (hs : unique_diff_on 𝕜 s₂) :
  times_cont_diff_on 𝕜 ∞ f₂ s₂ ↔
  differentiable_on 𝕜 f₂ s₂ ∧ times_cont_diff_on 𝕜 ∞ (deriv_within f₂ s₂) s₂ :=
begin
  split,
  { assume h,
    refine ⟨h.differentiable_on le_top, _⟩,
    apply times_cont_diff_on_top.2 (λ n, ((times_cont_diff_on_succ_iff_deriv_within hs).1 _).2),
    exact h.of_le le_top },
  { assume h,
    refine times_cont_diff_on_top.2 (λ n, _),
    have A : (n : with_top ℕ) ≤ ∞ := le_top,
    apply ((times_cont_diff_on_succ_iff_deriv_within hs).2 ⟨h.1, h.2.of_le A⟩).of_le,
    exact with_top.coe_le_coe.2 (nat.le_succ n) }
end

/-- A function is `C^∞` on an open domain if and only if it is differentiable
there, and its derivative (formulated with `deriv`) is `C^∞`. -/
theorem times_cont_diff_on_top_iff_deriv_of_open (hs : is_open s₂) :
  times_cont_diff_on 𝕜 ∞ f₂ s₂ ↔
  differentiable_on 𝕜 f₂ s₂ ∧ times_cont_diff_on 𝕜 ∞ (deriv f₂) s₂ :=
begin
  rw times_cont_diff_on_top_iff_deriv_within hs.unique_diff_on,
  congr' 2,
  rw ← iff_iff_eq,
  apply times_cont_diff_on_congr,
  assume x hx,
  exact deriv_within_of_open hs hx
end

lemma times_cont_diff_on.deriv_within {m n : with_top ℕ}
  (hf : times_cont_diff_on 𝕜 n f₂ s₂) (hs : unique_diff_on 𝕜 s₂) (hmn : m + 1 ≤ n) :
  times_cont_diff_on 𝕜 m (deriv_within f₂ s₂) s₂ :=
begin
  cases m,
  { change ∞ + 1 ≤ n at hmn,
    have : n = ∞, by simpa using hmn,
    rw this at hf,
    exact ((times_cont_diff_on_top_iff_deriv_within hs).1 hf).2 },
  { change (m.succ : with_top ℕ) ≤ n at hmn,
    exact ((times_cont_diff_on_succ_iff_deriv_within hs).1 (hf.of_le hmn)).2 }
end

lemma times_cont_diff_on.deriv_of_open {m n : with_top ℕ}
  (hf : times_cont_diff_on 𝕜 n f₂ s₂) (hs : is_open s₂) (hmn : m + 1 ≤ n) :
  times_cont_diff_on 𝕜 m (deriv f₂) s₂ :=
(hf.deriv_within hs.unique_diff_on hmn).congr (λ x hx, (deriv_within_of_open hs hx).symm)

lemma times_cont_diff_on.continuous_on_deriv_within {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f₂ s₂) (hs : unique_diff_on 𝕜 s₂) (hn : 1 ≤ n) :
  continuous_on (deriv_within f₂ s₂) s₂ :=
((times_cont_diff_on_succ_iff_deriv_within hs).1 (h.of_le hn)).2.continuous_on

lemma times_cont_diff_on.continuous_on_deriv_of_open {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f₂ s₂) (hs : is_open s₂) (hn : 1 ≤ n) :
  continuous_on (deriv f₂) s₂ :=
((times_cont_diff_on_succ_iff_deriv_of_open hs).1 (h.of_le hn)).2.continuous_on

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative is `C^n`. -/
theorem times_cont_diff_succ_iff_deriv {n : ℕ} :
  times_cont_diff 𝕜 ((n + 1) : ℕ) f₂ ↔
    differentiable 𝕜 f₂ ∧ times_cont_diff 𝕜 n (deriv f₂) :=
by simp only [← times_cont_diff_on_univ, times_cont_diff_on_succ_iff_deriv_of_open, is_open_univ,
  differentiable_on_univ]

end deriv

section restrict_scalars
/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is `n` times continuously differentiable over `ℂ`, then it is `n` times continuously
differentiable over `ℝ`. In this paragraph, we give variants of this statement, in the general
situation where `ℂ` and `ℝ` are replaced respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra
over `𝕜`.
-/

variables (𝕜) {𝕜' : Type*} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
variables [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E]
variables [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F]
variables {p' : E → formal_multilinear_series 𝕜' E F} {n : with_top ℕ}

lemma has_ftaylor_series_up_to_on.restrict_scalars
  (h : has_ftaylor_series_up_to_on n f p' s) :
  has_ftaylor_series_up_to_on n f (λ x, (p' x).restrict_scalars 𝕜) s :=
{ zero_eq := λ x hx, h.zero_eq x hx,
  fderiv_within :=
    begin
      intros m hm x hx,
      convert ((continuous_multilinear_map.restrict_scalars_linear 𝕜).has_fderiv_at)
        .comp_has_fderiv_within_at _ ((h.fderiv_within m hm x hx).restrict_scalars 𝕜),
    end,
  cont := λ m hm, continuous_multilinear_map.continuous_restrict_scalars.comp_continuous_on
    (h.cont m hm) }

lemma times_cont_diff_within_at.restrict_scalars (h : times_cont_diff_within_at 𝕜' n f s x) :
  times_cont_diff_within_at 𝕜 n f s x :=
begin
  intros m hm,
  rcases h m hm with ⟨u, u_mem, p', hp'⟩,
  exact ⟨u, u_mem, _, hp'.restrict_scalars _⟩
end

lemma times_cont_diff_on.restrict_scalars (h : times_cont_diff_on 𝕜' n f s) :
  times_cont_diff_on 𝕜 n f s :=
λ x hx, (h x hx).restrict_scalars _

lemma times_cont_diff_at.restrict_scalars (h : times_cont_diff_at 𝕜' n f x) :
  times_cont_diff_at 𝕜 n f x :=
times_cont_diff_within_at_univ.1 $ h.times_cont_diff_within_at.restrict_scalars _

lemma times_cont_diff.restrict_scalars (h : times_cont_diff 𝕜' n f) :
  times_cont_diff 𝕜 n f :=
times_cont_diff_iff_times_cont_diff_at.2 $ λ x, h.times_cont_diff_at.restrict_scalars _

end restrict_scalars
