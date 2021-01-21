/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import analysis.special_functions.trigonometric
import ring_theory.localization
import data.zmod.basic

/-!
# Chebyshev polynomials

The Chebyshev polynomials are two families of polynomials indexed by `ℕ`,
with integral coefficients.
In this file, we only consider Chebyshev polynomials of the first kind.

## Main declarations

* `polynomial.chebyshev₁_mul`, the `(m * n)`-th Chebyshev polynomial is the composition
  of the `m`-th and `n`-th Chebyshev polynomials.
* `polynomial.lambdashev_mul`, the `(m * n)`-th lambdashev polynomial is the composition
  of the `m`-th and `n`-th lambdashev polynomials.
* `polynomial.lambdashev_char_p`, for a prime number `p`, the `p`-th lambdashev polynomial
  is congruent to `X ^ p` modulo `p`.

## Implementation details

Since Chebyshev polynomials have interesting behaviour over the complex numbers and modulo `p`,
we define them to have coefficients in an arbitrary commutative ring, even though
technically `ℤ` would suffice.
The benefit of allowing arbitrary coefficient rings, is that the statements afterwards are clean,
and do not have `map (int.cast_ring_hom R)` interfering all the time.


-/

noncomputable theory

namespace polynomial
open complex
variables (R S : Type*) [comm_ring R] [comm_ring S]

/-- The `(m * n)`-th Chebyshev polynomial is the composition of the `m`-th and `n`-th -/
lemma chebyshev₁_mul (m n : ℕ) :
  chebyshev₁ R (m * n) = (chebyshev₁ R m).comp (chebyshev₁ R n) :=
begin
  simp only [← map_comp, ← map_chebyshev₁ (int.cast_ring_hom R)],
  congr' 1,
  apply map_injective (int.cast_ring_hom ℂ) int.cast_injective,
  simp only [map_comp, map_chebyshev₁],
  apply polynomial.funext,
  intro z,
  obtain ⟨θ, rfl⟩ := cos_surjective z,
  simp only [chebyshev₁_complex_cos, nat.cast_mul, eval_comp, mul_assoc],
end

section lambdashev
/-!

### A Lambda structure on `polynomial ℤ`

Mathlib doesn't currently know what a Lambda ring is.
But once it does, we can endow `polynomial ℤ` with a Lambda structure
in terms of the `lambdashev` polynomials defined below.
There is exactly one other Lambda structure on `polynomial ℤ` in terms of binomial polynomials.

-/

variables {R}

lemma lambdashev_eval_add_inv (x y : R) (h : x * y = 1) :
  ∀ n, (lambdashev R n).eval (x + y) = x ^ n + y ^ n
| 0       := by simp only [bit0, eval_one, eval_add, pow_zero, lambdashev_zero]
| 1       := by simp only [eval_X, lambdashev_one, pow_one]
| (n + 2) :=
begin
  simp only [eval_sub, eval_mul, lambdashev_eval_add_inv, eval_X, lambdashev_add_two],
  conv_lhs { simp only [pow_succ, add_mul, mul_add, h, ← mul_assoc, mul_comm y x, one_mul] },
  ring_exp
end

variables (R)

lemma lambdashev_eq_chebyshev₁ [invertible (2 : R)] :
  ∀ n, lambdashev R n = 2 * (chebyshev₁ R n).comp (C (⅟2) * X)
| 0       := by simp only [chebyshev₁_zero, mul_one, one_comp, lambdashev_zero]
| 1       := by rw [lambdashev_one, chebyshev₁_one, X_comp, ← mul_assoc, ← C_1, ← C_bit0, ← C_mul,
                    mul_inv_of_self, C_1, one_mul]
| (n + 2) :=
begin
  simp only [lambdashev_add_two, chebyshev₁_add_two, lambdashev_eq_chebyshev₁ (n + 1),
    lambdashev_eq_chebyshev₁ n, sub_comp, mul_comp, add_comp, X_comp, bit0_comp, one_comp],
  simp only [← C_1, ← C_bit0, ← mul_assoc, ← C_mul, mul_inv_of_self],
  rw [C_1, one_mul],
  ring
end

lemma chebyshev₁_eq_lambdashev [invertible (2 : R)] (n : ℕ) :
  chebyshev₁ R n = C (⅟2) * (lambdashev R n).comp (2 * X) :=
begin
  rw lambdashev_eq_chebyshev₁,
  simp only [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_1, ← C_bit0, ← C_mul],
  rw [inv_of_mul_self, C_1, one_mul, one_mul, comp_X]
end

/-- the `(m * n)`-th lambdashev polynomial is the composition of the `m`-th and `n`-th -/
lemma lambdashev_mul (m n : ℕ) :
  lambdashev R (m * n) = (lambdashev R m).comp (lambdashev R n) :=
begin
  simp only [← map_lambdashev (int.cast_ring_hom R), ← map_comp],
  congr' 1,
  apply map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [map_lambdashev, map_comp, lambdashev_eq_chebyshev₁, chebyshev₁_mul, two_mul,
    ← add_comp],
  simp only [← two_mul, ← comp_assoc],
  apply eval₂_congr rfl rfl,
  rw [comp_assoc],
  apply eval₂_congr rfl _ rfl,
  rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_1, ← C_bit0, ← C_mul,
      inv_of_mul_self, C_1, one_mul]
end

lemma lambdashev_comp_comm (m n : ℕ) :
  (lambdashev R m).comp (lambdashev R n) = (lambdashev R n).comp (lambdashev R m) :=
by rw [← lambdashev_mul, mul_comm, lambdashev_mul]

lemma lambdashev_zmod_p (p : ℕ) [fact p.prime] :
  lambdashev (zmod p) p = X ^ p :=
begin
  -- Recall that `lambdashev_eval_add_inv` characterises `lambdashev R p`
  -- as a polynomial that maps `x + x⁻¹` to `x ^ p + (x⁻¹) ^ p`.
  -- Since `X ^ p` also satisfies this property in characteristic `p`,
  -- we can use a variant on `polynomial.funext` to conclude that these polynomials are equal.
  -- For this argument, we need an arbitrary infinite field of characteristic `p`.
  obtain ⟨K, _, _, H⟩ : ∃ (K : Type) [field K], by exactI ∃ [char_p K p], infinite K,
  { let K := fraction_ring (polynomial (zmod p)),
    let f : zmod p →+* K := (fraction_ring.of _).to_map.comp C,
    haveI : char_p K p := by { rw ← f.char_p_iff_char_p, apply_instance },
    haveI : infinite K :=
    by { apply infinite.of_injective _ (fraction_ring.of _).injective, apply_instance },
    refine ⟨K, _, _, _⟩; apply_instance },
  resetI,
  apply map_injective (zmod.cast_hom (dvd_refl p) K) (ring_hom.injective _),
  rw [map_lambdashev, map_pow, map_X],
  apply eq_of_infinite_eval_eq,
  -- The two polynomials agree on all `x` of the form `x = y + y⁻¹`.
  apply @set.infinite_mono _ {x : K | ∃ y, x = y + y⁻¹ ∧ y ≠ 0},
  { rintro _ ⟨x, rfl, hx⟩,
    simp only [eval_X, eval_pow, set.mem_set_of_eq, @add_pow_char K _ p,
      lambdashev_eval_add_inv _ _ (mul_inv_cancel hx)] },
  -- Now we need to show that the set of such `x` is infinite.
  -- If the set is finite, then we will show that `K` is also finite.
  { intro h,
    rw ← set.infinite_univ_iff at H,
    apply H,
    -- To each `x` of the form `x = y + y⁻¹`
    -- we `bind` the set of `y` that solve the equation `x = y + y⁻¹`.
    -- For every `x`, that set is finite (since it is governed by a quadratic equation).
    -- For the moment, we claim that all these sets together cover `K`.
    suffices : (set.univ : set K) =
      {x : K | ∃ (y : K), x = y + y⁻¹ ∧ y ≠ 0} >>= (λ x, {y | x = y + y⁻¹ ∨ y = 0}),
    { rw this, clear this,
      apply set.finite_bind h,
      rintro x hx,
      -- The following quadratic polynomial has as solutions the `y` for which `x = y + y⁻¹`.
      let φ : polynomial K := X ^ 2 - C x * X + 1,
      have hφ : φ ≠ 0,
      { intro H,
        have : φ.eval 0 = 0, by rw [H, eval_zero],
        simpa [eval_X, eval_one, eval_pow, eval_sub, sub_zero, eval_add,
          eval_mul, mul_zero, pow_two, zero_add, one_ne_zero] },
      classical,
      convert (φ.roots ∪ {0}).to_finset.finite_to_set using 1,
      ext1 y,
      simp only [multiset.mem_to_finset, set.mem_set_of_eq, finset.mem_coe, multiset.mem_union,
        mem_roots hφ, is_root, eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C, eval_one,
        multiset.mem_singleton, multiset.singleton_eq_singleton],
      by_cases hy : y = 0,
      { simp only [hy, eq_self_iff_true, or_true] },
      apply or_congr _ iff.rfl,
      rw [← mul_left_inj' hy, eq_comm, ← sub_eq_zero, add_mul, inv_mul_cancel hy],
      apply eq_iff_eq_cancel_right.mpr,
      ring },
    -- Finally, we prove the claim that our finite union of finite sets covers all of `K`.
    { apply (set.eq_univ_of_forall _).symm,
      intro x,
      simp only [exists_prop, set.mem_Union, set.bind_def, ne.def, set.mem_set_of_eq],
      by_cases hx : x = 0,
      { simp only [hx, and_true, eq_self_iff_true, inv_zero, or_true],
        exact ⟨_, 1, rfl, one_ne_zero⟩ },
      { simp only [hx, or_false, exists_eq_right],
        exact ⟨_, rfl, hx⟩ } } }
end

lemma lambdashev_char_p (p : ℕ) [fact p.prime] [char_p R p] :
  lambdashev R p = X ^ p :=
by rw [← map_lambdashev (zmod.cast_hom (dvd_refl p) R), lambdashev_zmod_p, map_pow, map_X]

end lambdashev

end polynomial
