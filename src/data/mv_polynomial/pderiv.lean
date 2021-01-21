/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/

import data.mv_polynomial.variables
import tactic.ring

/-!
# Partial derivatives of polynomials

This file defines the notion of the formal *partial derivative* of a polynomial,
the derivative with respect to a single variable.
This derivative is not connected to the notion of derivative from analysis.
It is based purely on the polynomial exponents and coefficients.

## Main declarations

* `mv_polynomial.pderiv i p` : the partial derivative of `p` with respect to `i`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_ring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

-/

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra
open_locale big_operators

universes u
variables {R : Type u}

namespace mv_polynomial
variables {σ : Type*} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

section pderiv

variables {R} [comm_semiring R]

/-- `pderiv i p` is the partial derivative of `p` with respect to `i` -/
def pderiv (i : σ) : mv_polynomial σ R →ₗ[R] mv_polynomial σ R :=
{ to_fun := λ p, p.sum (λ A B, monomial (A - single i 1) (B * (A i))),
  map_smul' := begin
    intros c x,
    rw [sum_smul_index', smul_sum],
    { simp_rw [monomial, smul_single, smul_eq_mul, mul_assoc] },
    { intros s,
      simp only [monomial_zero, zero_mul] }
  end,
  map_add' := λ f g, sum_add_index (by simp only [monomial_zero, forall_const, zero_mul])
    (by simp only [add_mul, forall_const, eq_self_iff_true, monomial_add]), }

@[simp]
lemma pderiv_monomial {i : σ} :
  pderiv i (monomial s a) = monomial (s - single i 1) (a * (s i)) :=
by simp only [pderiv, monomial_zero, sum_monomial, zero_mul, linear_map.coe_mk]

@[simp]
lemma pderiv_C {i : σ} : pderiv i (C a) = 0 :=
suffices pderiv i (monomial 0 a) = 0, by simpa,
by simp only [monomial_zero, pderiv_monomial, nat.cast_zero, mul_zero, zero_apply]

lemma pderiv_eq_zero_of_not_mem_vars {i : σ} {f : mv_polynomial σ R} (h : i ∉ f.vars) :
  pderiv i f = 0 :=
begin
  change (pderiv i) f = 0,
  rw [f.as_sum, linear_map.map_sum],
  apply finset.sum_eq_zero,
  intros x H,
  simp [mem_support_not_mem_vars_zero H h],
end

lemma pderiv_monomial_single {i : σ} {n : ℕ} :
  pderiv i (monomial (single i n) a) = monomial (single i (n-1)) (a * n) :=
by simp

private lemma monomial_sub_single_one_add {i : σ} {s' : σ →₀ ℕ} :
  monomial (s - single i 1 + s') (a * (s i) * a') =
    monomial (s + s' - single i 1) (a * (s i) * a') :=
by by_cases h : s i = 0; simp [h, sub_single_one_add]

private lemma monomial_add_sub_single_one {i : σ} {s' : σ →₀ ℕ} :
  monomial (s + (s' - single i 1)) (a * (a' * (s' i))) =
    monomial (s + s' - single i 1) (a * (a' * (s' i))) :=
by by_cases h : s' i = 0; simp [h, add_sub_single_one]

lemma pderiv_monomial_mul {i : σ} {s' : σ →₀ ℕ} :
  pderiv i (monomial s a * monomial s' a') =
    pderiv i (monomial s a) * monomial s' a' + monomial s a * pderiv i (monomial s' a') :=
begin
  simp [monomial_sub_single_one_add, monomial_add_sub_single_one],
  congr,
  ring,
end

@[simp]
lemma pderiv_mul {i : σ} {f g : mv_polynomial σ R} :
  pderiv i (f * g) = pderiv i f * g + f * pderiv i g :=
begin
  apply induction_on' f,
  { apply induction_on' g,
    { intros u r u' r', exact pderiv_monomial_mul },
    { intros p q hp hq u r,
      rw [mul_add, linear_map.map_add, hp, hq, mul_add, linear_map.map_add],
      ring } },
  { intros p q hp hq,
    simp [add_mul, hp, hq],
    ring, }
end

@[simp]
lemma pderiv_C_mul {f : mv_polynomial σ R} {i : σ} :
  pderiv i (C a * f) = C a * pderiv i f :=
by convert linear_map.map_smul (pderiv i) a f; rw C_mul'

end pderiv

end mv_polynomial
