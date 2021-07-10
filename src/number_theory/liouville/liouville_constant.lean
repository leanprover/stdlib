/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jujian Zhang
-/
import number_theory.liouville.basic
/-!

# Liouville constants

This file contains a construction of a family of Liouville numbers, indexed by a natural number $m$.
The most important property is that they are examples of transcendental real numbers.
This fact is recorded in `liouville.is_transcendental`.

More precisely, for a real number $m$, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for $1 < m$.  However, there is no restriction on $m$, since,
if the series does not converge, then the sum of the series is defined to be zero.

We prove that, for $m \in \mathbb{N}$ satisfying $2 \le m$, Liouville's constant associated to $m$
is a transcendental number.  Classically, the Liouville number for $m = 2$ is the one called
``Liouville's constant''.

# Implementation notes

The indexing $m$ is eventually a natural number satisfying $2 ≤ m$.  However, we prove the first few
lemmas for $m \in \mathbb{R}$.
-/

noncomputable theory
open_locale nat big_operators
open real finset

namespace liouville

/--
For a real number `m`, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for `1 < m`.  However, there is no restriction on `m`, since,
if the series does not converge, then the sum of the series is defined to be zero.
-/
def liouville_number (m : ℝ) : ℝ := ∑' (i : ℕ), 1 / m ^ i!

/--
`liouville_number_initial_terms` is the sum of the first `k + 1` terms of Liouville's constant,
i.e.
$$
\sum_{i=0}^k\frac{1}{m^{i!}}.
$$
-/
def liouville_number_initial_terms (m : ℝ) (k : ℕ) : ℝ := ∑ i in range (k+1), 1 / m ^ i!

/--
`liouville_number_tail` is the sum of the series of the terms in `liouville_number m`
starting from `k+1`, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}.
$$
-/
def liouville_number_tail (m : ℝ) (k : ℕ) : ℝ := ∑' i, 1 / m ^ (i + (k+1))!

lemma liouville_number_tail_pos {m : ℝ} (hm : 1 < m) (k : ℕ) :
  0 < liouville_number_tail m k :=
-- replace `0` with the constantly zero series `∑ i : ℕ, 0`
calc  (0 : ℝ) = ∑' i : ℕ, 0 : tsum_zero.symm
          ... < liouville_number_tail m k :
  -- to show that a series with non-negative terms has strictly positive sum it suffices
  -- to prove that
  tsum_lt_tsum_of_nonneg
    -- 1. the terms of the zero series are indeed non-negative
    (λ _, rfl.le)
    -- 2. the terms of our series are non-negative
    (λ i, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _))
    -- 3. one term of our series is strictly positive -- they all are, we use the first term
    (one_div_pos.mpr (pow_pos (zero_lt_one.trans hm) (0 + (k + 1))!)) $
    -- 4. our series converges -- it does since it is the tail of a converging series, though
    -- this is not the argument here.
    summable_one_div_pow_of_le hm (λ i, trans le_self_add (nat.self_le_factorial _))

/--  Split the sum definining a Liouville number into the first `k` term and the rest. -/
lemma liouville_number_eq_initial_terms_add_tail {m : ℝ} (hm : 1 < m) (k : ℕ) :
  liouville_number m = liouville_number_initial_terms m k +
  liouville_number_tail m k :=
(sum_add_tsum_nat_add _ (summable_one_div_pow_of_le hm (λ i, i.self_le_factorial))).symm

/-! We now prove two useful inequalities, before collecting everything together. -/

/--  Partial inequality, works with `m ∈ ℝ` satisfying `1 < m`. -/
lemma tsum_one_div_pow_factorial_lt (n : ℕ) {m : ℝ} (m1 : 1 < m) :
  ∑' (i : ℕ), 1 / m ^ (i + (n + 1))! < (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) :=
-- two useful inequalities
have m0 : 0 < m := (zero_lt_one.trans m1),
have mi : abs (1 / m) < 1 :=
  (le_of_eq (abs_of_pos (one_div_pos.mpr m0))).trans_lt ((div_lt_one m0).mpr m1),
calc (∑' i, 1 / m ^ (i + (n + 1))!)
    < ∑' i, 1 / m ^ (i + (n + 1)!) :
    -- to show the strict inequality between these series, we prove that:
    tsum_lt_tsum_of_nonneg
      -- 1. the first series has non-negative terms
      (λ b, one_div_nonneg.mpr (pow_nonneg m0.le _))
      -- 2. the second series dominates the first
      (λ b, one_div_pow_le_one_div_pow_of_le m1.le (b.add_factorial_succ_le_factorial_add_succ n))
      -- 3. the term with index `i = 2` of the first series is strictly smaller than
      -- the corresponding term of the second series
      (one_div_pow_strict_mono m1 (n.add_factorial_succ_lt_factorial_add_succ rfl.le))
      -- 4. the second series is summable, since its terms grow quickly
      (summable_one_div_pow_of_le m1 (λ j, nat.le.intro rfl))
... = ∑' i, (1 / m) ^ i * (1 / m ^ (n + 1)!) :
    -- split the sum in the exponent and massage
    by { congr, ext i, rw [pow_add, ← div_div_eq_div_mul, div_eq_mul_one_div, ← one_div_pow i] }
-- factor the constant `(1 / m ^ (n + 1)!)` out of the series
... = (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) : tsum_mul_right
... = (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) :
    -- the series if the geometric series
    mul_eq_mul_right_iff.mpr (or.inl (tsum_geometric_of_abs_lt_1 mi))

lemma aux_calc (n : ℕ) {m : ℝ} (hm : 2 ≤ m) :
  (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 1 / (m ^ n!) ^ n :=
calc (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 2 * (1 / m ^ (n + 1)!) :
  -- the second factors coincide (and are non-negative),
  -- the first factors, satisfy the inequality `sub_one_div_inv_le_two`
  mul_mono_nonneg (one_div_nonneg.mpr (pow_nonneg (zero_le_two.trans hm) _))
    (sub_one_div_inv_le_two hm)
... = 2 / m ^ (n + 1)! : mul_one_div 2 _
... = 2 / m ^ (n! * (n + 1)) : congr_arg ((/) 2) (congr_arg (pow m) (mul_comm _ _))
... ≤ 1 / m ^ (n! * n) :
  begin
    -- [ NB: in this block, I do not follow the brace convention for subgoals -- I wait until
    --   I solve all extraneous goals at once with `exact pow_pos (zero_lt_two.trans_le hm) _`. ]
    -- Clear denominators and massage*
    apply (div_le_div_iff _ _).mpr,
    conv_rhs { rw [one_mul, mul_add, pow_add, mul_one, pow_mul, mul_comm, ← pow_mul] },
    -- the second factors coincide, so we prove the inequality of the first factors*
    apply (mul_le_mul_right _).mpr,
    -- solve all the inequalities `0 < m ^ ??`
    any_goals { exact pow_pos (zero_lt_two.trans_le hm) _ },
    -- `2 ≤ m ^ n!` is a consequence of monotonicity of exponentiation at `2 ≤ m`.
    exact trans (trans hm (pow_one _).symm.le) (pow_mono (one_le_two.trans hm) n.factorial_pos)
  end
... = 1 / (m ^ n!) ^ n : congr_arg ((/) 1) (pow_mul m n! n)

/-!  Starting from here, we specialize to the case in which `m` is a natural number. -/

/--  The sum of the `k` initial terms of the Liouville number to base `m` is a ratio of natural
numbers where the denominator is `m ^ k!`. -/
lemma liouville_number_rat_initial_terms {m : ℕ} (hm : 0 < m) (k : ℕ) :
∃ p : ℕ, liouville_number_initial_terms m k = p / m ^ k! :=
begin
  induction k with k h,
  { exact ⟨1, by rw [liouville_number_initial_terms, range_one, sum_singleton, nat.cast_one]⟩ },
  { rcases h with ⟨p_k, h_k⟩,
    use p_k * (m ^ ((k + 1)! - k!)) + 1,
    unfold liouville_number_initial_terms at h_k ⊢,
    rw [sum_range_succ, h_k, div_add_div, div_eq_div_iff, add_mul],
    { norm_cast,
      rw [add_mul, one_mul, nat.factorial_succ,
        show k.succ * k! - k! = (k.succ - 1) * k!, by rw [nat.mul_sub_right_distrib, one_mul],
        nat.succ_sub_one, nat.succ_eq_add_one, add_mul, one_mul, pow_add],
      simp [mul_assoc] },
    refine mul_ne_zero_iff.mpr ⟨_, _⟩,
    all_goals { exact pow_ne_zero _ (nat.cast_ne_zero.mpr hm.ne.symm) } }
end

theorem is_liouville {m : ℕ} (hm : 2 ≤ m) :
  liouville (liouville_number m) :=
begin
  -- two useful inequalities
  have mZ1 : 1 < (m : ℤ), { norm_cast, exact one_lt_two.trans_le hm },
  have m1 : 1 < (m : ℝ), { norm_cast, exact one_lt_two.trans_le hm },
  intro n,
  -- the first `n` terms sum to `p / m ^ k!`
  rcases liouville_number_rat_initial_terms (zero_lt_two.trans_le hm) n with ⟨p, hp⟩,
  refine ⟨p, m ^ n!, one_lt_pow mZ1 n.factorial_pos, _⟩,
  push_cast,
  -- separate out the sum of the first `n` terms and the rest
  rw [liouville_number_eq_initial_terms_add_tail m1 n,
    ← hp, add_sub_cancel', abs_of_nonneg (liouville_number_tail_pos m1 _).le],
  exact ⟨((lt_add_iff_pos_right _).mpr (liouville_number_tail_pos m1 n)).ne.symm,
    (tsum_one_div_pow_factorial_lt n m1).trans_le
    (aux_calc _ (nat.cast_two.symm.le.trans (nat.cast_le.mpr hm)))⟩
end

/- Placing this lemma outside of the `open/closed liouville`-namespace would allow to remove
`_root_.`, at the cost of some other small weirdness. -/
lemma is_transcendental {m : ℕ} (hm : 2 ≤ m) :
  _root_.transcendental ℤ (liouville_number m) :=
transcendental (is_liouville hm)

end liouville
