/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.abel
import data.polynomial.eval

/-!
# The Pochhammer polynomials

We define and prove some basic relations about
`pochhammer S n : polynomial S = X * (X+1) * ... * (X + n - 1)`
which is also known as the rising factorial. A version of this definition
that is focused on `nat` can be found in `data.nat.factorial` as `asc_factorial`.

## Implementation

As with many other families of polynomials, even though the coefficients are always in `ℕ`,
we define the polynomial with coefficients in any `[semiring S]`.

## TODO

There is lots more in this direction:
* q-factorials, q-binomials, q-Pochhammer.
-/

universes u v

open polynomial

section
variables (S : Type u) [semiring S]

/--
`pochhammer S n` is the polynomial `X * (X+1) * ... * (X + n - 1)`,
with coefficients in the semiring `S`.
-/
noncomputable def pochhammer : ℕ → polynomial S
| 0 := 1
| (n+1) := X * (pochhammer n).comp (X + 1)

@[simp] lemma pochhammer_zero : pochhammer S 0 = 1 := rfl
@[simp] lemma pochhammer_one : pochhammer S 1 = X := by simp [pochhammer]

lemma pochhammer_succ_left (n : ℕ) : pochhammer S (n+1) = X * (pochhammer S n).comp (X+1) :=
by rw pochhammer

section
variables {S} {T : Type v} [semiring T]
@[simp] lemma pochhammer_map (f : S →+* T) (n : ℕ) : (pochhammer S n).map f = pochhammer T n :=
begin
  induction n with n ih,
  { simp, },
  { simp [ih, pochhammer_succ_left, map_comp], },
end

end

@[simp, norm_cast] lemma pochhammer_eval_cast (n k : ℕ) :
  ((pochhammer ℕ n).eval k : S) = (pochhammer S n).eval k :=
begin
  rw [←pochhammer_map (algebra_map ℕ S), eval_map, ←(algebra_map ℕ S).eq_nat_cast,
    eval₂_at_nat_cast, nat.cast_id, ring_hom.eq_nat_cast],
end

lemma pochhammer_eval_zero {n : ℕ} : (pochhammer S n).eval 0 = if n = 0 then 1 else 0 :=
begin
  cases n,
  { simp, },
  { simp [X_mul, nat.succ_ne_zero, pochhammer_succ_left], }
end

lemma pochhammer_zero_eval_zero : (pochhammer S 0).eval 0 = 1 :=
by simp

@[simp] lemma pochhammer_ne_zero_eval_zero {n : ℕ} (h : n ≠ 0) : (pochhammer S n).eval 0 = 0 :=
by simp [pochhammer_eval_zero, h]

lemma pochhammer_succ_right (n : ℕ) : pochhammer S (n+1) = pochhammer S n * (X + n) :=
begin
  suffices h : pochhammer ℕ (n+1) = pochhammer ℕ n * (X + n),
  { apply_fun polynomial.map (algebra_map ℕ S) at h,
    simpa only [pochhammer_map, map_mul, map_add, map_X, map_nat_cast] using h, },
  induction n with n ih,
  { simp, },
  { conv_lhs {
    rw [pochhammer_succ_left, ih, mul_comp, ←mul_assoc, ←pochhammer_succ_left, add_comp, X_comp,
      nat_cast_comp, add_assoc, add_comm (1 : polynomial ℕ)], },
    refl, },
end

lemma polynomial.mul_X_add_nat_cast_comp {p q : polynomial S} {n : ℕ} :
  (p * (X + n)).comp q = (p.comp q) * (q + n) :=
by rw [mul_add, add_comp, mul_X_comp, ←nat.cast_comm, nat_cast_mul_comp, nat.cast_comm, mul_add]

lemma pochhammer_mul (n m : ℕ) :
  pochhammer S n * (pochhammer S m).comp (X + n) = pochhammer S (n + m) :=
begin
  induction m with m ih,
  { simp, },
  { rw [pochhammer_succ_right, polynomial.mul_X_add_nat_cast_comp, ←mul_assoc, ih,
      nat.succ_eq_add_one, ←add_assoc, pochhammer_succ_right, nat.cast_add, add_assoc], }
end

lemma pochhammer_nat_eq_asc_factorial (n : ℕ) :
  ∀ k, (pochhammer ℕ k).eval (n + 1) = n.asc_factorial k
| 0 := by erw [eval_one]; refl
| (t + 1) := begin
  rw [pochhammer_succ_right, eval_mul, pochhammer_nat_eq_asc_factorial t],
  suffices : n.asc_factorial t * (n + 1 + t) = n.asc_factorial (t + 1), by simpa,
  rw [nat.asc_factorial_succ, add_right_comm, mul_comm]
end

end

section
variables {S : Type*} [ordered_semiring S] [nontrivial S]

lemma pochhammer_pos (n : ℕ) (s : S) (h : 0 < s) : 0 < (pochhammer S n).eval s :=
begin
  induction n with n ih,
  { simp only [nat.nat_zero_eq_zero, pochhammer_zero, eval_one], exact zero_lt_one, },
  { rw [pochhammer_succ_right, mul_add, eval_add, ←nat.cast_comm, eval_nat_cast_mul, eval_mul_X,
      nat.cast_comm, ←mul_add],
    exact mul_pos ih
      (lt_of_lt_of_le h ((le_add_iff_nonneg_right _).mpr (nat.cast_nonneg n))), }
end

end

section factorial

open_locale nat

variables (S : Type*) [semiring S] (r n : ℕ)

@[simp]
lemma pochhammer_eval_one (S : Type*) [semiring S] (n : ℕ) :
  (pochhammer S n).eval (1 : S) = (n! : S) :=
by rw_mod_cast [pochhammer_nat_eq_asc_factorial, nat.zero_asc_factorial]

lemma factorial_mul_pochhammer (S : Type*) [semiring S] (r n : ℕ) :
  (r! : S) * (pochhammer S n).eval (r + 1) = (r + n)! :=
by rw_mod_cast [pochhammer_nat_eq_asc_factorial, nat.factorial_mul_asc_factorial]

lemma pochhammer_nat_eval_succ (r : ℕ) :
  ∀ n : ℕ, n * (pochhammer ℕ r).eval (n + 1) = (n + r) * (pochhammer ℕ r).eval n
| 0 := begin
  by_cases h : r = 0,
  { simp only [h, zero_mul, zero_add], },
  { simp only [pochhammer_eval_zero, zero_mul, if_neg h, mul_zero], }
end
| (k + 1) := by simp only [pochhammer_nat_eq_asc_factorial, nat.succ_asc_factorial, add_right_comm]

lemma pochhammer_eval_succ (r n : ℕ) :
  (n : S) * (pochhammer S r).eval (n + 1 : S) = (n + r) * (pochhammer S r).eval n :=
by exact_mod_cast congr_arg nat.cast (pochhammer_nat_eval_succ r n)

end factorial
