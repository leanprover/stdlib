/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.times_cont_diff

/-!
# One-dimensional iterated derivatives

We define the `n`-th derivative of a function `f : 𝕜 → F` as a function
`iterated_deriv n f : 𝕜 → F`, as well as a version on domains `iterated_deriv_within n f s : 𝕜 → F`,
and prove their basic properties.

## Main definitions and results

Let `𝕜` be a nondiscrete normed field, and `F` a normed vector space over `𝕜`. Let `f : 𝕜 → F`.

* `iterated_deriv n f` is the `n`-th derivative of `f`, seen as a function from `𝕜` to `F`.
  It is defined as the `n`-th Fréchet derivative (which is a multilinear map) applied to the
  vector `(1, ..., 1)`, to take advantage of all the existing framework, but we show that it
  coincides with the naive iterative definition.
* `iterated_deriv_eq_iterate` states that the `n`-th derivative of `f` is obtained by starting
  from `f` and differentiating it `n` times.
* `iterated_deriv_within n f s` is the `n`-th derivative of `f` within the domain `s`. It only
  behaves well when `s` has the unique derivative property.
* `iterated_deriv_within_eq_iterate` states that the `n`-th derivative of `f` in the domain `s` is
  obtained by starting from `f` and differentiating it `n` times within `s`. This only holds when
  `s` has the unique derivative property.

## Implementation details

The results are deduced from the corresponding results for the more general (multilinear) iterated
Fréchet derivative. For this, we write `iterated_deriv n f` as the composition of
`iterated_fderiv 𝕜 n f` and a continuous linear equiv. As continuous linear equivs respect
differentiability and commute with differentiation, this makes it possible to prove readily that
the derivative of the `n`-th derivative is the `n+1`-th derivative in `iterated_deriv_within_succ`,
by translating the corresponding result `iterated_fderiv_within_succ_apply_left` for the
iterated Fréchet derivative.
-/

noncomputable theory
open_locale classical topological_space big_operators
open filter asymptotics set


variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

/-- The `n`-th iterated derivative of a function from `𝕜` to `F`, as a function from `𝕜` to `F`. -/
def iterated_deriv (n : ℕ) (f : 𝕜 → F) (x : 𝕜) : F :=
(iterated_fderiv 𝕜 n f x : ((fin n) → 𝕜) → F) (λ(i : fin n), 1)

/-- The `n`-th iterated derivative of a function from `𝕜` to `F` within a set `s`, as a function
from `𝕜` to `F`. -/
def iterated_deriv_within (n : ℕ) (f : 𝕜 → F) (s : set 𝕜) (x : 𝕜) : F :=
(iterated_fderiv_within 𝕜 n f s x : ((fin n) → 𝕜) → F) (λ(i : fin n), 1)

variables {n : ℕ} {f : 𝕜 → F} {s : set 𝕜} {x : 𝕜}

lemma iterated_deriv_within_univ :
  iterated_deriv_within n f univ = iterated_deriv n f :=
by { ext x, rw [iterated_deriv_within, iterated_deriv, iterated_fderiv_within_univ] }

/-! ### Properties of the iterated derivative within a set -/

lemma iterated_deriv_within_eq_iterated_fderiv_within :
  iterated_deriv_within n f s x
  = (iterated_fderiv_within 𝕜 n f s x : ((fin n) → 𝕜) → F) (λ(i : fin n), 1) := rfl

/-- Write the iterated derivative as the composition of a continuous linear equiv and the iterated
Fréchet derivative -/
lemma iterated_deriv_within_eq_equiv_comp :
  iterated_deriv_within n f s
  = (continuous_multilinear_map.pi_field_equiv 𝕜 (fin n) F).symm ∘
    (iterated_fderiv_within 𝕜 n f s) :=
by { ext x, refl }

/-- Write the iterated Fréchet derivative as the composition of a continuous linear equiv and the
iterated derivative. -/
lemma iterated_fderiv_within_eq_equiv_comp :
  iterated_fderiv_within 𝕜 n f s
  = (continuous_multilinear_map.pi_field_equiv 𝕜 (fin n) F) ∘ (iterated_deriv_within n f s) :=
begin
  rw [iterated_deriv_within_eq_equiv_comp, ← function.comp.assoc,
      continuous_linear_equiv.self_comp_symm],
  refl
end

/-- The `n`-th Fréchet derivative applied to a vector `(m 0, ..., m (n-1))` is the derivative
multiplied by the product of the `m i`s. -/
lemma iterated_fderiv_within_apply_eq_iterated_deriv_within_mul_prod {m : (fin n) → 𝕜} :
  (iterated_fderiv_within 𝕜 n f s x : ((fin n) → 𝕜) → F) m
  = (∏ i, m i) • iterated_deriv_within n f s x :=
begin
  rw [iterated_deriv_within_eq_iterated_fderiv_within, ← continuous_multilinear_map.map_smul_univ],
  simp
end

@[simp] lemma iterated_deriv_within_zero :
  iterated_deriv_within 0 f s = f :=
by { ext x, simp [iterated_deriv_within] }

@[simp] lemma iterated_deriv_within_one (hs : unique_diff_on 𝕜 s) {x : 𝕜} (hx : x ∈ s):
  iterated_deriv_within 1 f s x = deriv_within f s x :=
by { simp [iterated_deriv_within, iterated_fderiv_within_one_apply hs hx], refl }

/-- If the first `n` derivatives within a set of a function are continuous, and its first `n-1`
derivatives are differentiable, then the function is `C^n`. This is not an equivalence in general,
but this is an equivalence when the set has unique derivatives, see
`times_cont_diff_on_iff_continuous_on_differentiable_on_deriv`. -/
lemma times_cont_diff_on_of_continuous_on_differentiable_on_deriv {n : with_top ℕ}
  (Hcont : ∀ (m : ℕ), (m : with_top ℕ) ≤ n →
    continuous_on (λ x, iterated_deriv_within m f s x) s)
  (Hdiff : ∀ (m : ℕ), (m : with_top ℕ) < n →
    differentiable_on 𝕜 (λ x, iterated_deriv_within m f s x) s) :
  times_cont_diff_on 𝕜 n f s :=
begin
  apply times_cont_diff_on_of_continuous_on_differentiable_on,
  { simpa [iterated_fderiv_within_eq_equiv_comp, continuous_linear_equiv.comp_continuous_on_iff] },
  { simpa [iterated_fderiv_within_eq_equiv_comp,
      continuous_linear_equiv.comp_differentiable_on_iff] }
end

/-- To check that a function is `n` times continuously differentiable, it suffices to check that its
first `n` derivatives are differentiable. This is slightly too strong as the condition we
require on the `n`-th derivative is differentiability instead of continuity, but it has the
advantage of avoiding the discussion of continuity in the proof (and for `n = ∞` this is optimal).
-/
lemma times_cont_diff_on_of_differentiable_on_deriv {n : with_top ℕ}
  (h : ∀(m : ℕ), (m : with_top ℕ) ≤ n → differentiable_on 𝕜 (iterated_deriv_within m f s) s) :
  times_cont_diff_on 𝕜 n f s :=
begin
  apply times_cont_diff_on_of_differentiable_on,
  simpa [iterated_fderiv_within_eq_equiv_comp,
    continuous_linear_equiv.comp_differentiable_on_iff, -coe_fn_coe_base],
end

/-- On a set with unique derivatives, a `C^n` function has derivatives up to `n` which are
continuous. -/
lemma times_cont_diff_on.continuous_on_iterated_deriv_within {n : with_top ℕ} {m : ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hmn : (m : with_top ℕ) ≤ n) (hs : unique_diff_on 𝕜 s) :
  continuous_on (iterated_deriv_within m f s) s :=
begin
  simp [iterated_deriv_within_eq_equiv_comp, continuous_linear_equiv.comp_continuous_on_iff,
    -coe_fn_coe_base],
  exact h.continuous_on_iterated_fderiv_within hmn hs
end

/-- On a set with unique derivatives, a `C^n` function has derivatives less than `n` which are
differentiable. -/
lemma times_cont_diff_on.differentiable_on_iterated_deriv_within {n : with_top ℕ} {m : ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hmn : (m : with_top ℕ) < n) (hs : unique_diff_on 𝕜 s) :
  differentiable_on 𝕜 (iterated_deriv_within m f s) s :=
begin
  simp [iterated_deriv_within_eq_equiv_comp, continuous_linear_equiv.comp_differentiable_on_iff,
    -coe_fn_coe_base],
  exact h.differentiable_on_iterated_fderiv_within hmn hs
end

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative on sets with unique derivatives. -/
lemma times_cont_diff_on_iff_continuous_on_differentiable_on_deriv {n : with_top ℕ}
  (hs : unique_diff_on 𝕜 s) :
  times_cont_diff_on 𝕜 n f s ↔
  (∀m:ℕ, (m : with_top ℕ) ≤ n → continuous_on (iterated_deriv_within m f s) s)
  ∧ (∀m:ℕ, (m : with_top ℕ) < n → differentiable_on 𝕜 (iterated_deriv_within m f s) s) :=
by simp only [times_cont_diff_on_iff_continuous_on_differentiable_on hs,
  iterated_fderiv_within_eq_equiv_comp, continuous_linear_equiv.comp_continuous_on_iff,
  continuous_linear_equiv.comp_differentiable_on_iff]

/-- The `n+1`-th iterated derivative within a set with unique derivatives can be obtained by
differentiating the `n`-th iterated derivative. -/
lemma iterated_deriv_within_succ {x : 𝕜} (hxs : unique_diff_within_at 𝕜 s x) :
  iterated_deriv_within (n + 1) f s x = deriv_within (iterated_deriv_within n f s) s x :=
begin
  rw [iterated_deriv_within_eq_iterated_fderiv_within, iterated_fderiv_within_succ_apply_left,
      iterated_fderiv_within_eq_equiv_comp, continuous_linear_equiv.comp_fderiv_within _ hxs,
      deriv_within],
  change ((continuous_multilinear_map.mk_pi_field 𝕜 (fin n)
    ((fderiv_within 𝕜 (iterated_deriv_within n f s) s x : 𝕜 → F) 1)) : (fin n → 𝕜 ) → F)
    (λ (i : fin n), 1)
    = (fderiv_within 𝕜 (iterated_deriv_within n f s) s x : 𝕜 → F) 1,
  simp
end

/-- The `n`-th iterated derivative within a set with unique derivatives can be obtained by
iterating `n` times the differentiation operation. -/
lemma iterated_deriv_within_eq_iterate {x : 𝕜} (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) :
  iterated_deriv_within n f s x = ((λ (g : 𝕜 → F), deriv_within g s)^[n]) f x :=
begin
  induction n with n IH generalizing x,
  { simp },
  { rw [iterated_deriv_within_succ (hs x hx), function.iterate_succ'],
    exact deriv_within_congr (hs x hx) (λ y hy, IH hy) (IH hx) }
end

/-- The `n+1`-th iterated derivative within a set with unique derivatives can be obtained by
taking the `n`-th derivative of the derivative. -/
lemma iterated_deriv_within_succ' {x : 𝕜} (hxs : unique_diff_on 𝕜 s) (hx : x ∈ s) :
  iterated_deriv_within (n + 1) f s x = (iterated_deriv_within n (deriv_within f s) s) x :=
by { rw [iterated_deriv_within_eq_iterate hxs hx, iterated_deriv_within_eq_iterate hxs hx], refl }


/-! ### Properties of the iterated derivative on the whole space -/

lemma iterated_deriv_eq_iterated_fderiv :
  iterated_deriv n f x
  = (iterated_fderiv 𝕜 n f x : ((fin n) → 𝕜) → F) (λ(i : fin n), 1) := rfl

/-- Write the iterated derivative as the composition of a continuous linear equiv and the iterated
Fréchet derivative -/
lemma iterated_deriv_eq_equiv_comp :
  iterated_deriv n f
  = (continuous_multilinear_map.pi_field_equiv 𝕜 (fin n) F).symm ∘ (iterated_fderiv 𝕜 n f) :=
by { ext x, refl }

/-- Write the iterated Fréchet derivative as the composition of a continuous linear equiv and the
iterated derivative. -/
lemma iterated_fderiv_eq_equiv_comp :
  iterated_fderiv 𝕜 n f
  = (continuous_multilinear_map.pi_field_equiv 𝕜 (fin n) F) ∘ (iterated_deriv n f) :=
begin
  rw [iterated_deriv_eq_equiv_comp, ← function.comp.assoc,
      continuous_linear_equiv.self_comp_symm],
  refl
end

/-- The `n`-th Fréchet derivative applied to a vector `(m 0, ..., m (n-1))` is the derivative
multiplied by the product of the `m i`s. -/
lemma iterated_fderiv_apply_eq_iterated_deriv_mul_prod {m : (fin n) → 𝕜} :
  (iterated_fderiv 𝕜 n f x : ((fin n) → 𝕜) → F) m = (∏ i, m i) • iterated_deriv n f x :=
by { rw [iterated_deriv_eq_iterated_fderiv, ← continuous_multilinear_map.map_smul_univ], simp }

@[simp] lemma iterated_deriv_zero :
  iterated_deriv 0 f = f :=
by { ext x, simp [iterated_deriv] }

@[simp] lemma iterated_deriv_one :
  iterated_deriv 1 f = deriv f :=
by { ext x, simp [iterated_deriv], refl }

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative. -/
lemma times_cont_diff_iff_iterated_deriv {n : with_top ℕ} :
  times_cont_diff 𝕜 n f ↔
(∀m:ℕ, (m : with_top ℕ) ≤ n → continuous (iterated_deriv m f))
∧ (∀m:ℕ, (m : with_top ℕ) < n → differentiable 𝕜 (iterated_deriv m f)) :=
by simp only [times_cont_diff_iff_continuous_differentiable, iterated_fderiv_eq_equiv_comp,
  continuous_linear_equiv.comp_continuous_iff,
  continuous_linear_equiv.comp_differentiable_iff]

/-- To check that a function is `n` times continuously differentiable, it suffices to check that its
first `n` derivatives are differentiable. This is slightly too strong as the condition we
require on the `n`-th derivative is differentiability instead of continuity, but it has the
advantage of avoiding the discussion of continuity in the proof (and for `n = ∞` this is optimal).
-/
lemma times_cont_diff_of_differentiable_iterated_deriv {n : with_top ℕ}
  (h : ∀(m : ℕ), (m : with_top ℕ) ≤ n → differentiable 𝕜 (iterated_deriv m f)) :
  times_cont_diff 𝕜 n f :=
times_cont_diff_iff_iterated_deriv.2
  ⟨λ m hm, (h m hm).continuous, λ m hm, (h m (le_of_lt hm))⟩

lemma times_cont_diff.continuous_iterated_deriv {n : with_top ℕ} (m : ℕ)
  (h : times_cont_diff 𝕜 n f) (hmn : (m : with_top ℕ) ≤ n) :
  continuous (iterated_deriv m f) :=
(times_cont_diff_iff_iterated_deriv.1 h).1 m hmn

lemma times_cont_diff.differentiable_iterated_deriv {n : with_top ℕ} (m : ℕ)
  (h : times_cont_diff 𝕜 n f) (hmn : (m : with_top ℕ) < n) :
  differentiable 𝕜 (iterated_deriv m f) :=
(times_cont_diff_iff_iterated_deriv.1 h).2 m hmn

/-- The `n+1`-th iterated derivative can be obtained by differentiating the `n`-th
iterated derivative. -/
lemma iterated_deriv_succ : iterated_deriv (n + 1) f = deriv (iterated_deriv n f) :=
begin
  ext x,
  rw [← iterated_deriv_within_univ, ← iterated_deriv_within_univ, ← deriv_within_univ],
  exact iterated_deriv_within_succ unique_diff_within_at_univ,
end

/-- The `n`-th iterated derivative can be obtained by iterating `n` times the
differentiation operation. -/
lemma iterated_deriv_eq_iterate : iterated_deriv n f = (deriv^[n]) f :=
begin
  ext x,
  rw [← iterated_deriv_within_univ],
  convert iterated_deriv_within_eq_iterate unique_diff_on_univ (mem_univ x),
  simp [deriv_within_univ]
end

/-- The `n+1`-th iterated derivative can be obtained by taking the `n`-th derivative of the
derivative. -/
lemma iterated_deriv_succ' : iterated_deriv (n + 1) f = iterated_deriv n (deriv f) :=
by { rw [iterated_deriv_eq_iterate, iterated_deriv_eq_iterate], refl }
