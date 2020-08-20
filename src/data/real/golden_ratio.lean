/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Alexey Soloyev, Junyan Xu
-/
import data.real.irrational
import data.nat.fib
import data.matrix.notation
import tactic.ring_exp
import algebra.linear_recurrence

/-!
# The golden ratio and its conjugate

This file defines the golden ratio `φ := (1 + √5)/2` and its conjugate
`ψ := (1 - √5)/2`, which are the two real roots of `X² - X - 1`.

Along with various computational facts about them, we prove their
irrationality, and we link them to the Fibonacci sequence by proving
Binet's formula.
-/

noncomputable theory

/-- The golden ratio `φ := (1 + √5)/2`. -/
@[reducible] def golden_ratio := (1 + real.sqrt 5)/2

/-- The conjugate of the golden ratio `ψ := (1 - √5)/2`. -/
@[reducible] def golden_conj := (1 - real.sqrt 5)/2

localized "notation `φ` := golden_ratio" in real
localized "notation `ψ` := golden_conj" in real

/-- The inverse of the golden ratio is the opposite of its conjugate. -/
@[simp] lemma inv_gold : φ⁻¹ = -ψ :=
begin
  have : 1 + real.sqrt 5 ≠ 0,
    from ne_of_gt (add_pos (by norm_num) $ real.sqrt_pos.mpr (by norm_num)),
  field_simp,
  apply mul_left_cancel' this,
  rw mul_div_cancel' _ this,
  rw [add_comm, ← sq_sub_sq],
  norm_num
end

@[simp] lemma gold_mul_gold_conj : φ * ψ = -1 :=
by {field_simp, rw ← sq_sub_sq, norm_num}

@[simp] lemma gold_add_gold_conj : φ + ψ = 1 := by {rw [golden_ratio, golden_conj], ring}

lemma one_sub_gold_conj : 1 - φ = ψ := by linarith [gold_add_gold_conj]

lemma one_sub_gold : 1 - ψ = φ := by linarith [gold_add_gold_conj]

@[simp] lemma gold_sub_gold_conj : φ - ψ = real.sqrt 5 := by {rw [golden_ratio, golden_conj], ring}

@[simp] lemma gold_sq : φ^2 = φ + 1 :=
begin
  rw [golden_ratio, ←sub_eq_zero],
  ring_exp,
  rw real.sqr_sqrt; norm_num,
end

@[simp] lemma gold_conj_sq : ψ^2 = ψ + 1 :=
begin
  rw [golden_conj, ←sub_eq_zero],
  ring_exp,
  rw real.sqr_sqrt; norm_num,
end

/-!
## Irrationality
-/

/-- The golden ratio is irrational. -/
theorem gold_irrational : irrational φ :=
begin
  have := nat.prime.irrational_sqrt (show nat.prime 5, by norm_num),
  have := this.rat_add 1,
  have := this.rat_mul (show (0.5 : ℚ) ≠ 0, by norm_num),
  convert this,
  field_simp
end

/-- The conjugate of the golden ratio is irrational. -/
theorem gold_conj_irrational : irrational ψ :=
begin
  have := nat.prime.irrational_sqrt (show nat.prime 5, by norm_num),
  have := this.rat_sub 1,
  have := this.rat_mul (show (0.5 : ℚ) ≠ 0, by norm_num),
  convert this,
  field_simp
end

/-!
## Links with Fibonacci sequence
-/

section fibrec

variables {α : Type*} [comm_semiring α]

/-- The recurrence relation satisfied by the Fibonacci sequence. -/
def fib_rec : linear_recurrence α :=
{ order := 2,
  coeffs := ![1, 1]}

section poly

open polynomial

/-- The characteristic polynomial of `fib_rec` is `X² - (X + 1)`. -/
lemma fib_rec_char_poly_eq {β : Type*} [comm_ring β] :
  fib_rec.char_poly = X^2 - (X + (1 : polynomial β)) :=
begin
  rw [fib_rec, linear_recurrence.char_poly],
  simp [finset.univ_sum_eq_range_sum, finset.sum_range_succ', monomial_eq_smul_X]
end

end poly

/-- As expected, the Fibonacci sequence is a solution of `fib_rec`. -/
lemma fib_is_sol_fib_rec : fib_rec.is_solution (λ x, x.fib : ℕ → α) :=
begin
  rw fib_rec,
  intros n,
  simp only,
  rw [nat.fib_succ_succ, add_comm],
  simp [finset.univ_sum_eq_range_sum, finset.sum_range_succ']
end

/-- The geometric sequence `λ n, φ^n` is a solution of `fib_rec`. -/
lemma geom_gold_is_sol_fib_rec : fib_rec.is_solution (pow φ) :=
begin
  rw [fib_rec.geom_sol_iff_root_char_poly, fib_rec_char_poly_eq],
  simp [sub_eq_zero_iff_eq, gold_sq]
end

/-- The geometric sequence `λ n, ψ^n` is a solution of `fib_rec`. -/
lemma geom_gold_conj_is_sol_fib_rec : fib_rec.is_solution (pow ψ) :=
begin
  rw [fib_rec.geom_sol_iff_root_char_poly, fib_rec_char_poly_eq],
  simp [sub_eq_zero_iff_eq, gold_conj_sq]
end

end fibrec

/-- Binet's formula as a function equality. -/
theorem real.coe_fib_eq' : (λ n, nat.fib n : ℕ → ℝ) = λ n, (φ^n - ψ^n) / real.sqrt 5 :=
begin
  rw fib_rec.sol_eq_of_eq_init,
  { intros i hi,
    fin_cases hi,
    { simp },
    { simp only [golden_ratio, golden_conj], ring_exp, rw mul_inv_cancel; norm_num } },
  { exact fib_is_sol_fib_rec },
  { ring,
    exact (@fib_rec ℝ _).sol_space.sub_mem
              ((@fib_rec ℝ _).sol_space.smul_mem (real.sqrt 5)⁻¹ geom_gold_is_sol_fib_rec)
              ((@fib_rec ℝ _).sol_space.smul_mem (real.sqrt 5)⁻¹ geom_gold_conj_is_sol_fib_rec) }
end

/-- Binet's formula as a dependent equality. -/
theorem real.coe_fib_eq : ∀ n, (nat.fib n : ℝ) = (φ^n - ψ^n) / real.sqrt 5 :=
by rw [← function.funext_iff, real.coe_fib_eq']
