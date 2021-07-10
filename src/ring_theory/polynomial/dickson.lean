/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/

import ring_theory.polynomial.chebyshev
import ring_theory.localization
import data.zmod.basic
import algebra.char_p.invertible


/-!
# Dickson polynomials

The (generalised) Dickson polynomials are a family of polynomials indexed by `ℕ × ℕ`,
with coefficients in a commutative ring `R` depending on an element `a∈R`. More precisely, the
they satisfy the recursion `dickson k a (n + 2) = X * (dickson k a n + 1) - a * (dickson k a n)`
with starting values `dickson k a 0 = 3 - k` and `dickson k a 1 = X`. In the literature,
`dickson k a n` is called the `n`-th Dickson polynomial of the `k`-th kind associated to the
parameter `a : R`. They are closely related to the Chebyshev polynomials in the case that `a=1`.
When `a=0` they are just the family of monomials `X ^ n`.

## Main definition

* `polynomial.dickson`: the generalised Dickson polynomials.

## Main statements

* `polynomial.dickson_one_one_mul`, the `(m * n)`-th Dickson polynomial of the first kind for
  parameter `1 : R` is the composition of the `m`-th and `n`-th Dickson polynomials of the first
  kind for `1 : R`.
* `polynomial.dickson_one_one_char_p`, for a prime number `p`, the `p`-th Dickson polynomial of the
  first kind associated to parameter `1 : R` is congruent to `X ^ p` modulo `p`.

## References

* [R. Lidl, G. L. Mullen and G. Turnwald, _Dickson polynomials_][MR1237403]

## TODO

* Redefine `dickson` in terms of `linear_recurrence`.
* Show that `dickson 2 1` is equal to the characteristic polynomial of the adjacency matrix of a
  type A Dynkin diagram.
* Prove that the adjacency matrices of simply laced Dynkin diagrams are precisely the adjacency
  matrices of simple connected graphs which annihilate `dickson 2 1`.
-/

noncomputable theory

namespace polynomial

variables {R S : Type*} [comm_ring R] [comm_ring S] (k : ℕ) (a : R)

/-- `dickson` is the `n`the (generalised) Dickson polynomial of the `k`-th kind associated to the
element `a ∈ R`. -/
noncomputable def dickson : ℕ → polynomial R
| 0       := 3 - k
| 1       := X
| (n + 2) := X * dickson (n + 1) - (C a) * dickson n

@[simp] lemma dickson_zero : dickson k a 0 = 3 - k := rfl
@[simp] lemma dickson_one : dickson k a 1 = X := rfl
lemma dickson_two : dickson k a 2 = X ^ 2 - C a * (3 - k) :=
by simp only [dickson, sq]
@[simp] lemma dickson_add_two (n : ℕ) :
  dickson k a (n + 2) = X * dickson k a (n + 1) - C a * dickson k a n :=
by rw dickson

lemma dickson_of_two_le {n : ℕ} (h : 2 ≤ n) :
  dickson k a n = X * dickson k a (n - 1) - C a * dickson k a (n - 2) :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h,
  rw add_comm,
  exact dickson_add_two k a n
end

variables {R S k a}

lemma map_dickson (f : R →+* S) :
  ∀ (n : ℕ), map f (dickson k a n) = dickson k (f a) n
| 0       := by simp only [dickson_zero, map_sub, map_nat_cast, bit1, bit0, map_add, map_one]
| 1       := by simp only [dickson_one, map_X]
| (n + 2) :=
begin
  simp only [dickson_add_two, map_sub, map_mul, map_X, map_C],
  rw [map_dickson, map_dickson]
end

variable {R}

@[simp] lemma dickson_two_zero :
  ∀ (n : ℕ), dickson 2 (0 : R) n = X ^ n
| 0       := by { simp only [dickson_zero, pow_zero], norm_num }
| 1       := by simp only [dickson_one, pow_one]
| (n + 2) :=
begin
  simp only [dickson_add_two, C_0, zero_mul, sub_zero],
  rw [dickson_two_zero, pow_add X (n + 1) 1, mul_comm, pow_one]
end

section dickson
/-!

### A Lambda structure on `polynomial ℤ`

Mathlib doesn't currently know what a Lambda ring is.
But once it does, we can endow `polynomial ℤ` with a Lambda structure
in terms of the `dickson 1 1` polynomials defined below.
There is exactly one other Lambda structure on `polynomial ℤ` in terms of binomial polynomials.

-/

variables {R}

lemma dickson_one_one_eval_add_inv (x y : R) (h : x * y = 1) :
  ∀ n, (dickson 1 (1 : R) n).eval (x + y) = x ^ n + y ^ n
| 0       := by { simp only [bit0, eval_one, eval_add, pow_zero, dickson_zero], norm_num }
| 1       := by simp only [eval_X, dickson_one, pow_one]
| (n + 2) :=
begin
  simp only [eval_sub, eval_mul, dickson_one_one_eval_add_inv, eval_X, dickson_add_two, C_1,
    eval_one],
  conv_lhs { simp only [pow_succ, add_mul, mul_add, h, ← mul_assoc, mul_comm y x, one_mul] },
  ring_exp
end

variables (R)

lemma dickson_one_one_eq_chebyshev_T [invertible (2 : R)] :
  ∀ n, dickson 1 (1 : R) n = 2 * (chebyshev.T R n).comp (C (⅟2) * X)
| 0       := by { simp only [chebyshev.T_zero, mul_one, one_comp, dickson_zero], norm_num }
| 1       := by rw [dickson_one, chebyshev.T_one, X_comp, ← mul_assoc, ← C_1, ← C_bit0, ← C_mul,
                    mul_inv_of_self, C_1, one_mul]
| (n + 2) :=
begin
  simp only [dickson_add_two, chebyshev.T_add_two, dickson_one_one_eq_chebyshev_T (n + 1),
    dickson_one_one_eq_chebyshev_T n, sub_comp, mul_comp, add_comp, X_comp, bit0_comp, one_comp],
  simp only [← C_1, ← C_bit0, ← mul_assoc, ← C_mul, mul_inv_of_self],
  rw [C_1, one_mul],
  ring
end

lemma chebyshev_T_eq_dickson_one_one [invertible (2 : R)] (n : ℕ) :
  chebyshev.T R n = C (⅟2) * (dickson 1 1 n).comp (2 * X) :=
begin
  rw dickson_one_one_eq_chebyshev_T,
  simp only [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_1, ← C_bit0, ← C_mul],
  rw [inv_of_mul_self, C_1, one_mul, one_mul, comp_X]
end

/-- The `(m * n)`-th Dickson polynomial of the first kind is the composition of the `m`-th and
`n`-th. -/
lemma dickson_one_one_mul (m n : ℕ) :
  dickson 1 (1 : R) (m * n) = (dickson 1 1 m).comp (dickson 1 1 n) :=
begin
  have h : (1 : R) = int.cast_ring_hom R (1),
    simp only [ring_hom.eq_int_cast, int.cast_one],
  rw h,
  simp only [← map_dickson (int.cast_ring_hom R), ← map_comp],
  congr' 1,
  apply map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [map_dickson, map_comp, ring_hom.eq_int_cast, int.cast_one,
    dickson_one_one_eq_chebyshev_T, chebyshev.T_mul, two_mul, ← add_comp],
  simp only [← two_mul, ← comp_assoc],
  apply eval₂_congr rfl rfl,
  rw [comp_assoc],
  apply eval₂_congr rfl _ rfl,
  rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_1, ← C_bit0, ← C_mul,
      inv_of_mul_self, C_1, one_mul]
end

lemma dickson_one_one_comp_comm (m n : ℕ) :
  (dickson 1 (1 : R) m).comp (dickson 1 1 n) = (dickson 1 1 n).comp (dickson 1 1 m) :=
by rw [← dickson_one_one_mul, mul_comm, dickson_one_one_mul]

lemma dickson_one_one_zmod_p (p : ℕ) [fact p.prime] :
  dickson 1 (1 : zmod p) p = X ^ p :=
begin
  -- Recall that `dickson_eval_add_inv` characterises `dickson 1 1 p`
  -- as a polynomial that maps `x + x⁻¹` to `x ^ p + (x⁻¹) ^ p`.
  -- Since `X ^ p` also satisfies this property in characteristic `p`,
  -- we can use a variant on `polynomial.funext` to conclude that these polynomials are equal.
  -- For this argument, we need an arbitrary infinite field of characteristic `p`.
  obtain ⟨K, _, _, H⟩ : ∃ (K : Type) [field K], by exactI ∃ [char_p K p], infinite K,
  { let K := fraction_ring (polynomial (zmod p)),
    let f : zmod p →+* K := (algebra_map _ (fraction_ring _)).comp C,
    haveI : char_p K p := by { rw ← f.char_p_iff_char_p, apply_instance },
    haveI : infinite K :=
    infinite.of_injective (algebra_map (polynomial (zmod p)) (fraction_ring (polynomial (zmod p))))
      (is_fraction_ring.injective _ _),
    refine ⟨K, _, _, _⟩; apply_instance },
  resetI,
  apply map_injective (zmod.cast_hom (dvd_refl p) K) (ring_hom.injective _),
  rw [map_dickson, map_pow, map_X],
  apply eq_of_infinite_eval_eq,
  -- The two polynomials agree on all `x` of the form `x = y + y⁻¹`.
  apply @set.infinite_mono _ {x : K | ∃ y, x = y + y⁻¹ ∧ y ≠ 0},
  { rintro _ ⟨x, rfl, hx⟩,
    simp only [eval_X, eval_pow, set.mem_set_of_eq, @add_pow_char K _ p,
      dickson_one_one_eval_add_inv _ _ (mul_inv_cancel hx), inv_pow', zmod.cast_hom_apply,
      zmod.cast_one'] },
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
      refine h.bUnion (λ x hx, _),
      -- The following quadratic polynomial has as solutions the `y` for which `x = y + y⁻¹`.
      let φ : polynomial K := X ^ 2 - C x * X + 1,
      have hφ : φ ≠ 0,
      { intro H,
        have : φ.eval 0 = 0, by rw [H, eval_zero],
        simpa [eval_X, eval_one, eval_pow, eval_sub, sub_zero, eval_add,
          eval_mul, mul_zero, sq, zero_add, one_ne_zero] },
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

lemma dickson_one_one_char_p (p : ℕ) [fact p.prime] [char_p R p] :
  dickson 1 (1 : R) p = X ^ p :=
begin
  have h : (1 : R) = zmod.cast_hom (dvd_refl p) R (1),
    simp only [zmod.cast_hom_apply, zmod.cast_one'],
  rw [h, ← map_dickson (zmod.cast_hom (dvd_refl p) R), dickson_one_one_zmod_p, map_pow, map_X]
end

end dickson

end polynomial
