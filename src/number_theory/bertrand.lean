/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Bolton Bailey
-/

import data.nat.prime
import data.finset.intervals
import data.nat.multiplicity
import data.nat.choose.sum
import number_theory.padics.padic_norm
import ring_theory.multiplicity
import algebra.module
import number_theory.primorial
import analysis.special_functions.pow
import analysis.calculus.local_extr
import data.real.sqrt
import data.real.nnreal
import data.complex.exponential_bounds

/-!
# Bertrand's postulate

In this file we prove Bertrand's postulate: That there is a prime between any positive integer and
its double.

We follow roughly, the proof from "Proofs from the BOOK" by Aigner and Ziegler (TODO cite).
-/

open_locale big_operators

/-- The multiplicity of p in the nth central binomial coefficient-/
private def α (n : nat) (p : nat) [hp : fact p.prime] : nat :=
padic_val_nat p (nat.choose (2 * n) n)

lemma central_binom_nonzero (n : ℕ) : nat.choose (2 * n) n ≠ 0 :=
ne_of_gt (nat.choose_pos (by linarith))

lemma claim_1
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 3 ≤ n)
  : p ^ (α n p) ≤ 2 * n
  :=
begin
  unfold α,
  rw @padic_val_nat_def p hp (nat.choose (2 * n) n) (central_binom_nonzero n),
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (nat.log p (2 * n) + 1)
                        (hp.out) (by linarith) (lt_add_one (nat.log p (2 * n)))],
  have r : 2 * n - n = n, by
    calc 2 * n - n = n + n - n: by rw two_mul n
    ... = n: nat.add_sub_cancel n n,
  simp [r, ←two_mul],
  have bar : (finset.filter (λ (i : ℕ), p ^ i ≤ 2 * (n % p ^ i))
              (finset.Ico 1 (nat.log p (2 * n) + 1))).card ≤ nat.log p (2 * n),
    calc (finset.filter (λ (i : ℕ), p ^ i ≤ 2 * (n % p ^ i))
            (finset.Ico 1 (nat.log p (2 * n) + 1))).card
            ≤ (finset.Ico 1 (nat.log p (2 * n) + 1)).card : by apply finset.card_filter_le
    ... = (nat.log p (2 * n) + 1) - 1 : by simp,
  have baz : p ^ (nat.log p (2 * n)) ≤ 2 * n,
  { apply nat.pow_log_le_self,
    apply hp.out.one_lt,
    calc 1 ≤ 3 : dec_trivial
    ...    ≤ n : n_big
    ...    ≤ 2 * n : by linarith, },
  apply trans (pow_le_pow (trans one_le_two hp.out.two_le) bar) baz,
end

lemma claim_2
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 3 ≤ n)
  (smallish : (2 * n) < p ^ 2)
  : (α n p) ≤ 1
  :=
begin
  have h1 : p ^ α n p < p ^ 2,
    calc p ^ α n p ≤ 2 * n : claim_1 p n n_big
    ...            < p ^ 2 : smallish,

  let h2 : α n p < 2 := (pow_lt_pow_iff hp.out.one_lt).1 h1,
  linarith,
end

lemma twice_nat_small : ∀ (n : nat) (h : 2 * n < 2), n = 0
| 0 := λ _, rfl
| (n + 1) := λ pr, by linarith

lemma claim_3
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 6 < n)
  (small : p ≤ n)
  (big : 2 * n < 3 * p)
  : α n p = 0
  :=
begin
  unfold α,
  rw @padic_val_nat_def p hp (nat.choose (2 * n) n) (central_binom_nonzero n),
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (nat.log p (2 * n) + 1)
                        (hp.out) (by linarith) (lt_add_one (nat.log p (2 * n)))],
  have r : 2 * n - n = n, by
    calc 2 * n - n = n + n - n: by rw two_mul n
    ... = n: nat.add_sub_cancel n n,
  simp only [r, ←two_mul, finset.card_eq_zero, enat.get_coe', finset.filter_congr_decidable],
  clear r,

  let p_pos : 0 < p := trans zero_lt_one hp.out.one_lt,

  apply finset.filter_false_of_mem,
  intros i i_in_interval,
  rw finset.Ico.mem at i_in_interval,
  have three_lt_p : 3 ≤ p ,
    { rcases le_or_lt 3 p with H|H,
      { exact H, },
      { have bad: 12 < 9, by
          calc 12 = 2 * 6: by ring
            ... <  2 * n: (mul_lt_mul_left (by linarith)).2 n_big
            ... < 3 * p: big
            ... < 3 * 3: (mul_lt_mul_left (by linarith)).2 H
            ... = 9: by ring,
        linarith, }, },

  simp only [not_le],

  rcases lt_trichotomy 1 i with H|rfl|H,
    { have two_le_i : 2 ≤ i, by linarith,
      have two_n_lt_pow_p_i : 2 * n < p ^ i,
        { calc 2 * n < 3 * p: big
            ... ≤ p * p: (mul_le_mul_right p_pos).2 three_lt_p
            ... = p ^ 2: by ring
            ... ≤ p ^ i: nat.pow_le_pow_of_le_right p_pos two_le_i, },
      have n_mod : n % p ^ i = n,
        { apply nat.mod_eq_of_lt,
          calc n ≤ n + n: nat.le.intro rfl
              ... = 2 * n: (two_mul n).symm
              ... < p ^ i: two_n_lt_pow_p_i, },
      rw n_mod,
      exact two_n_lt_pow_p_i, },

    { rw [pow_one],
      suffices h23 : 2 * (p * (n / p)) + 2 * (n % p) < 2 * (p * (n / p)) + p,
      { exact (add_lt_add_iff_left (2 * (p * (n / p)))).mp h23, },

      have n_big : 1 ≤ (n / p),
        { apply (nat.le_div_iff_mul_le' p_pos).2,
          simp only [one_mul],
          exact small, },

      rw [←mul_add, nat.div_add_mod],
      let h5 : p * 1 ≤ p * (n / p) := nat.mul_le_mul_left p n_big,

      linarith, },
    { linarith, },
end


lemma claim_4
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (multiplicity_pos : α n p > 0)
  : p ≤ 2 * n
  :=
begin
  unfold α at multiplicity_pos,
  rw @padic_val_nat_def p hp (nat.choose (2 * n) n) (central_binom_nonzero n) at multiplicity_pos,
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (nat.log p (2 * n) + 1)
                        (hp.out) (by linarith) (lt_add_one (nat.log p (2 * n)))]
                          at multiplicity_pos,
  have r : 2 * n - n = n, by
    calc 2 * n - n = n + n - n: by rw two_mul n
    ... = n: nat.add_sub_cancel n n,
  simp only [r, ←two_mul, gt_iff_lt, enat.get_coe', finset.filter_congr_decidable]
    at multiplicity_pos,
  clear r,
  rw finset.card_pos at multiplicity_pos,
  cases multiplicity_pos with m hm,
  simp only [finset.Ico.mem, finset.mem_filter] at hm,
  calc p = p ^ 1 : tactic.ring_exp.base_to_exp_pf rfl
  ...    ≤ p ^ m : nat.pow_le_pow_of_le_right (by linarith [hp.out.one_lt]) hm.left.left
  ...    ≤ 2 * (n % p ^ m) : hm.right
  ...    ≤ 2 * n : nat.mul_le_mul_left _ (nat.mod_le n _),
end


lemma two_n_div_3_le_two_mul_n_choose_n (n : ℕ) : 2 * n / 3 < (2 * n).choose n :=
begin
  cases n,
  { simp only [nat.succ_pos', nat.choose_self, nat.zero_div, mul_zero], },
  calc 2 * (n + 1) / 3 < 2 * (n + 1): nat.div_lt_self (by norm_num) (by norm_num)
  ... = (2 * (n + 1)).choose(1): by norm_num
  ... ≤ (2 * (n + 1)).choose(2 * (n + 1) / 2): nat.choose_le_middle 1 (2 * (n + 1))
  ... = (2 * (n + 1)).choose(n + 1): by simp only [nat.succ_pos', nat.mul_div_right]
end

lemma not_pos_iff_zero (n : ℕ) : ¬ 0 < n ↔ n = 0 :=
begin
  split,
  { intros h, induction n, refl, simp only [nat.succ_pos', not_true] at h, cc, },
  { intros h, rw h, exact irrefl 0, },
end

lemma alskjhads (n x : ℕ): 2 * n / 3 + 1 ≤ x -> 2 * n < 3 * x :=
begin
  intro h,
  rw nat.add_one_le_iff at h,
  cases lt_or_ge (2 * n) (3 * x),
  { exact h_1, },
  { exfalso,
    simp only [ge_iff_le] at h_1,
    induction x,
    { simp at h, exact h, },
    { apply x_ih,
      cases lt_or_ge (2 * n / 3) x_n,
      { exact h_2, },
      { have r : 2 * n / 3 = x_n,
          have h1298 := nat.le_of_lt_succ h,
          linarith,
        exfalso,
        subst r,
        exact nat.lt_le_antisymm (nat.lt_mul_div_succ (2 * n) (by norm_num)) h_1, },
      { calc 3 * x_n ≤ 3 * (x_n + 1): by norm_num
        ... ≤ 2 * n: h_1, }, }, },
end

lemma central_binom_factorization (n : ℕ) :
      ∏ p in finset.filter nat.prime (finset.range ((2 * n).choose n + 1)),
        p ^ (padic_val_nat p ((2 * n).choose n))
      = (2 * n).choose n :=
  prod_pow_prime_padic_val_nat _ (central_binom_nonzero n) _ (lt_add_one _)

def central_binom_lower_bound := nat.four_pow_le_two_mul_add_one_mul_central_binom

lemma prod_of_pos_is_pos {S: finset ℕ} {f: ℕ → ℕ} (p_pos: ∀ p, p ∈ S → 0 < f p) :
0 < ∏ p in S, f p :=
begin
  have prop : ∀ p, p ∈ S → f p ≠ 0, by
    { intros p p_in_s,
      specialize p_pos p p_in_s,
      linarith, },
  let e := finset.prod_ne_zero_iff.2 prop,
  cases lt_or_ge 0 (∏ p in S, f p),
  { exact h, },
  { exfalso,
    simp only [ge_iff_le, le_zero_iff] at h,
    exact e h, },
end

lemma interchange_filters {α: _} {S: finset α} {f g: α → Prop} [decidable_pred f]
[decidable_pred g] : (S.filter g).filter f = S.filter (λ i, g i ∧ f i) :=
begin
  ext1,
  simp only [finset.mem_filter],
  exact and_assoc (a ∈ S) (g a),
end

lemma interchange_and_in_filter {α: _} {S: finset α} {f g: α → Prop} [decidable_pred f]
[decidable_pred g] : S.filter (λ i, g i ∧ f i) = S.filter (λ i, f i ∧ g i) :=
begin
  ext1,
  simp only [finset.mem_filter, and.congr_right_iff],
  intros _,
  exact and.comm,
end

lemma intervening_sqrt {a n : ℕ} (small : (nat.sqrt n) ^ 2 ≤ a ^ 2) (big : a ^ 2 ≤ n) :
a = nat.sqrt n :=
begin
  rcases lt_trichotomy a (nat.sqrt n) with H|rfl|H,
  { exfalso,
    have bad : a ^ 2 < a ^ 2, by
      calc a ^ 2 = a * a: by ring
      ... < (nat.sqrt n) * nat.sqrt n : nat.mul_self_lt_mul_self H
      ... = (nat.sqrt n) ^ 2: by ring
      ... ≤ a ^ 2 : small,
    exact nat.lt_asymm bad bad, },
  { refl, },
  { exfalso,
    have r: n < a ^ 2 :=
      calc n < a * a: nat.sqrt_lt.1 H
      ... = a ^ 2: by ring,
    linarith, },
end

lemma filter_filter_card_le_filter_card {α: _} {S: finset α} {f g: α → Prop}
[_inst : decidable_pred f][_inst : decidable_pred g] :
((S.filter g).filter f).card ≤ (S.filter f).card :=
begin
  calc ((S.filter g).filter f).card = (S.filter (λ i, g i ∧ f i)).card :
                  congr_arg finset.card interchange_filters
  ... = (S.filter (λ i, f i ∧ g i)).card: congr_arg finset.card interchange_and_in_filter
  ... = ((S.filter f).filter g).card: congr_arg finset.card interchange_filters.symm
  ... ≤ (S.filter f).card: (finset.filter f S).card_filter_le g,
end

lemma filter_size {S : finset ℕ} {a : ℕ} : (finset.filter (λ p, p < a) S).card ≤ a :=
begin
  have t : ∀ i, i ∈ (S.filter (λ p, p < a)) → i ∈ finset.range(a),
    { intros i hyp,
      simp only [finset.mem_filter] at hyp,
      simp only [finset.mem_range],
      exact hyp.2, },
  have r: S.filter (λ p, p < a) ⊆ finset.range(a) := finset.subset_iff.mpr t,
  have s: (S.filter (λ p, p < a)).card ≤ (finset.range(a)).card := finset.card_le_of_subset r,
  simp only [finset.card_range] at s,
  exact s,
end

lemma even_prime_is_two {p : ℕ} (pr: nat.prime p) (div: 2 ∣ p) : p = 2 :=
begin
  rcases pr with ⟨_, divs⟩,
  specialize divs 2 div,
  cc,
end

lemma even_prime_is_small {a n : ℕ} (a_prime : nat.prime a) (n_big : 2 < n) (small : a ^ 2 ≤ 2 * n)
: a ^ 2 < 2 * n :=
begin
  cases lt_or_ge (a ^ 2) (2 * n),
  { exact h, },
  { have t : a * a = 2 * n, by
      calc a * a = a ^ 2: by ring
      ... = 2 * n: by linarith,

    have two_prime : nat.prime 2, by norm_num,
    have a_even : 2 ∣ a := (or_self _).mp ((nat.prime.dvd_mul two_prime).mp ⟨n, t⟩),
    have a_two : a = 2 := even_prime_is_two a_prime a_even,
    subst a_two,
    linarith, },
end

-- lemma pow_sub_lt (a b c d : ℕ) (d_le_b : d ≤ b) (h : a ^ b < c * a ^ d) : a ^ (b-d) < c :=
-- begin
--   sorry,
-- end

lemma le_iff_mul_le_mul (a b c : ℕ) (c_pos : 0 < c) : a ≤ b ↔ a * c ≤ b * c :=
begin
  exact (mul_le_mul_right c_pos).symm
end

lemma three_pos : 0 < 3 := by dec_trivial

lemma ge_of_le (a b : ℕ) : a ≤ b → b ≥ a := ge.le



lemma pow_beats_mul (n : ℕ) (big : 3 < n) : 32 * n ≤ 4 ^ n :=
begin
  induction n with n hyp,
  { linarith, },
  { cases le_or_gt n 3,
    { have r : 2 < n := nat.succ_lt_succ_iff.mp big,
      have s : n = 3 := by linarith,
      rw s,
      norm_num, },
    { specialize hyp h,
      have s : 0 < 4 ^ n := pow_pos (by norm_num) _,
      have r : 32 ≤ 4 ^ n := by linarith,
      calc 32 * (n + 1) = 32 * n + 32 : by ring
      ... ≤ 4 ^ n + 32 : by linarith
      ... ≤ 4 ^ n + 4 ^ n : by linarith
      ... = (4 ^ n) * 2 : by ring
      ... ≤ (4 ^ n) * 4 : by linarith
      ... ≤ 4 ^ (n + 1) : by ring_exp, }, },
end

lemma power_conversion_1 (n : ℕ) (n_large : 480 < n) : 2 * n + 1 ≤ 4 ^ (n / 15) :=
begin
  have : 31 ≤ n / 15,
    { cases le_or_gt 31 (n / 15),
      { exact h, },
      { have r : n < n :=
          calc n = 15 * (n / 15) + (n % 15) : (nat.div_add_mod n 15).symm
            ... < 15 * 31 + (n % 15) : add_lt_add_right ((mul_lt_mul_left (nat.succ_pos 14)).2 h) _
            ... < 15 * 31 + 15 : add_lt_add_left (nat.mod_lt n (by linarith)) (15 * 31)
            ... = 480 : by norm_num
            ... < n : n_large,
        exfalso,
        exact lt_irrefl _ r, }, },
  have rem_small : (n % 15) < 15 := nat.mod_lt n (nat.succ_pos 14),
  calc 2 * n + 1 = 2 * (15 * (n / 15) + (n % 15)) + 1 : by rw nat.div_add_mod n 15
  ... = 30 * (n / 15) + 2 * (n % 15) + 1 : by ring
  ... ≤ 30 * (n / 15) + 2 * 15 + 1 : by linarith
  ... = 30 * (n / 15) + 31 : by norm_num
  ... ≤ 31 * (n / 15) + 31 : by linarith
  ... ≤ 31 * (n / 15) + (n / 15) : by linarith
  ... = 32 * (n / 15) : by ring
  ... ≤ 4 ^ (n / 15) : pow_beats_mul (n / 15) (by linarith),
end

open real
open_locale nnreal

lemma pow_coe (a b : ℕ) : (↑(a ^ b) : ℝ) = (↑a) ^ (↑b : ℝ) :=
begin
  rw real.rpow_nat_cast,
  simp only [nat.cast_pow],
end

lemma nat_sqrt_le_real_sqrt (a : ℕ) : (nat.sqrt a : ℝ) ≤ real.sqrt a :=
begin
  have r : (0 : ℝ) ≤ ((nat.sqrt a) : ℝ) := (@nat.cast_le ℝ _ _ 0 (nat.sqrt a)).2
                                              (zero_le (nat.sqrt a)),
  apply (le_sqrt (nat.sqrt a).cast_nonneg (nat.cast_nonneg a)).2,
  calc ↑(nat.sqrt a) ^ 2 = (nat.sqrt a : ℝ) ^ (1 + 1) : rfl
  ... = (nat.sqrt a : ℝ) ^ ↑(1 + 1) : (rpow_nat_cast (nat.sqrt a : ℝ) (1 + 1)).symm
  ... = (nat.sqrt a : ℝ) ^ ((1 : ℝ) + 1) : by simp only [nat.cast_add, nat.cast_one]
  ... = ((nat.sqrt a) : ℝ) ^ (1 : ℝ) * ((nat.sqrt a) : ℝ) ^ (1 : ℝ) : by rw rpow_add' r two_ne_zero
  ... = ↑(nat.sqrt a) * ↑(nat.sqrt a) : by rw rpow_one
  ... = ↑(nat.sqrt a * nat.sqrt a) : by norm_num
  ... ≤ ↑a : nat.cast_le.mpr (nat.sqrt_le a),
end

open set



-- end
lemma add_one_cube_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : (x + 1) ^ (3 : ℝ) ≤ exp (3 * x) :=
begin
  rw mul_comm,
  rw exp_mul,
  apply @rpow_le_rpow (x + 1) (exp x) 3,
  linarith,
  exact add_one_le_exp_of_nonneg hx,
  linarith,
end

lemma le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x ≤ exp (x) :=
begin
  calc x ≤ x + 1 : by linarith
  ...    ≤ exp x : add_one_le_exp_of_nonneg hx,
end


lemma cube_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x ^ (3 : ℝ) ≤ exp (3 * x) :=
begin
  rw mul_comm,
  rw exp_mul,
  apply @rpow_le_rpow (x) (exp x) 3,
  linarith,
  exact le_exp_of_nonneg hx,
  linarith,
end

-- lemma cube_le_exp_of_nonneg2 {x : ℝ} (hx : 0 ≤ x) : (x / 3) ^ (3 : ℝ) ≤ exp (x) :=
-- begin
--   have h := cube_le_exp_of_nonneg (x / 3)
-- end

-- lemma nat_pow_is_real_pow (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n  :=
-- begin
--   induction n,
--   simp,
--   rw pow_succ,
--   rw <-nat.add_one,
--   rw pow_cast,
--   rw pow_add,

-- end

-- set_option pp.notation false
-- set_option pp.implicit true

-- lemma saldkaoiew (x : ℝ) (hx : 0 ≤ x) : sqrt (x) ^ (4 : ℝ) = x ^ (2 : ℝ) :=
-- begin
--   conv
--   begin
--     to_rhs,
--     congr,
--     rw <-sq_sqrt hx,
--     -- skip,
--     -- rw <-pow_one (sqrt x),
--   end,
--   simp,
--   rw <-rpow_mul,
--   norm_num,
--   sorry,
-- end

lemma zero_le_three : (0 : ℝ) ≤ (3 : ℝ) := by norm_num
lemma zero_le_log_four : (0 : ℝ) ≤ log 4 := log_nonneg (by norm_num)

lemma zero_lt_three_pow_nat_three : (0 : ℝ) < 3 ^ 3 :=
begin
  norm_num
end

lemma pow_real_three (x : ℝ) (hx : 0 < x) : x ^ (3 : ℝ) = x * x * x :=
begin
  have h1 : x ^ (3 : ℝ) = x ^ (1 + 1 + 1 : ℝ),
    norm_num,
  rw h1,
  rw rpow_add,
  rw rpow_add,
  rw rpow_one,
  -- norm_num,
  linarith,
  linarith,

  -- rw pow_succ,
  -- rw pow_one,
  -- norm_num,
end

lemma zero_lt_three_pow_real_three : (0 : ℝ) < 3 ^ (3 : ℝ) :=
begin
  rw pow_real_three,
  norm_num,
  linarith,
end

lemma intermediate (x : ℝ) (x_big : 43046721 ≤ x) :
sqrt (8 * x + 8) ^ (3 : ℝ) * (3 ^ (3 : ℝ) * (8 * x + 8)) ≤ x ^ (3 : ℝ) * log 4 ^ (3 : ℝ) :=
begin
  rw pow_real_three,
  rw pow_real_three,
  rw pow_real_three,
  rw ←sqrt_mul,
  rw <-sq,
  rw sqrt_sq,
  calc (8 * x + 8) * sqrt (8 * x + 8) * (3 * 3 * 3 * (8 * x + 8))
      ≤ 9 * x * sqrt (8 * x + 8) * (3 * 3 * 3 * (8 * x + 8)) :
        begin
          apply mul_le_mul,
          apply mul_le_mul,
          linarith,
          apply le_refl,
          apply sqrt_nonneg,
          linarith,
          apply le_refl,
          linarith,
          apply mul_nonneg,
          linarith,
          apply sqrt_nonneg,
        end
  ... ≤ 9 * x * sqrt (8 * x + 8) * (3 * 3 * 3 * 9 * x) :
        begin
          apply mul_le_mul,
          apply le_refl,
          linarith,
          linarith,
          apply mul_nonneg,
          linarith,
          apply sqrt_nonneg,
        end
  ... ≤ 9 * x * sqrt (9 * x) * (3 * 3 * 3 * 9 * x) :
        begin
          apply mul_le_mul,
          apply mul_le_mul,
          apply le_refl,
          apply sqrt_le_sqrt,
          linarith,
          apply sqrt_nonneg,
          linarith,
          apply le_refl,
          linarith,
          apply mul_nonneg,
          linarith,
          apply sqrt_nonneg,
        end
  ... ≤ 9 * x * (x / 2187) * (3 * 3 * 3 * 9 * x) :
        begin
          apply mul_le_mul,
          apply mul_le_mul,
          apply le_refl,
          rw sqrt_mul,
          apply (le_div_iff _).2,
          rw mul_assoc,
          rw mul_comm,
          rw mul_assoc,
          rw mul_comm,
          apply (le_div_iff _).1,
          rw div_sqrt,
          apply (le_sqrt _ _).2,
          rw mul_pow,
          rw sq_sqrt,
          norm_num,
          linarith,
          linarith,
          apply mul_nonneg,
          linarith,
          apply sqrt_nonneg,
          linarith,
          apply sqrt_pos.2,
          linarith,
          linarith,
          linarith,
          apply sqrt_nonneg,
          linarith,
          linarith,
          linarith,
          apply mul_nonneg,
          linarith,
          linarith,
        end
  ... = x * x * x : by linarith
  ... ≤ x * x * x * log 4 ^ (3 : ℝ) :
        begin
          rw <-(mul_one (x * x * x)),
          apply mul_le_mul,
          simp only [le_refl, mul_one],
          apply one_le_rpow,
          conv
          begin
            to_lhs,
            rw <-log_exp 1,
          end,
          apply (log_le_log _ _).2,
          apply le_of_lt,
          apply trans exp_one_lt_d9,
          linarith,
          apply exp_pos,
          linarith,
          linarith,
          linarith,
          apply mul_nonneg,
          apply mul_nonneg,
          apply mul_nonneg,
          linarith,
          linarith,
          linarith,
          linarith,
        end,
  linarith,
  linarith,
  linarith,
  linarith,
  apply sqrt_pos.2,
  linarith,
end

lemma linear_dominates_sqrt_log (x : ℝ) (hx : 43046721 ≤ x) :
sqrt (8 * x + 8) * log (8 * x + 8) ≤ x * log 4 :=
begin
  have h1 : 0 < sqrt (8 * x + 8),
    simp only [sqrt_pos],
    linarith,
  rw ←(le_div_iff' h1),
  rw exp_le_exp.symm,
  rw @exp_log (8 * x + 8) (by linarith),
  calc 8 * x + 8 ≤ (x * log 4 / sqrt (8 * x + 8) / 3) ^ (3 : ℝ) :
              begin
                have x_nonneg : 0 ≤ x := by linarith,
                have s: 0 ≤ x * log 4 := mul_nonneg x_nonneg zero_le_log_four,
                rw div_rpow (div_nonneg s (sqrt_nonneg _)) zero_le_three,
                rw div_rpow s (sqrt_nonneg _),
                rw mul_rpow x_nonneg zero_le_log_four,
                rw le_div_iff',
                { rw le_div_iff',
                  { exact intermediate x hx, },
                  { exact rpow_pos_of_pos h1 3, }, },
                exact zero_lt_three_pow_real_three,
                -- rewrite saldkaoiew (8 * x + 8),
              end
  ...      ≤ exp (3 * (x * log 4 / sqrt (8 * x + 8) / 3)) :
              begin
                apply cube_le_exp_of_nonneg,
                apply mul_nonneg,
                apply mul_nonneg,
                apply mul_nonneg,
                linarith,
                apply log_nonneg,
                linarith,
                rw inv_nonneg,
                linarith,
                rw inv_nonneg,
                linarith,
              end
  ...      = exp (x * log 4 / sqrt (8 * x + 8)) :
              begin
                simp only [exp_eq_exp],
                rw mul_div_assoc.symm,
                apply mul_div_cancel_left,
                linarith,
              end
end

lemma sqrt_9 : sqrt 9 = 3 :=
begin
  apply (sqrt_eq_iff_mul_self_eq _ _).2,
  norm_num,
  linarith,
  linarith,
end

-- lemma linear_dominates_sqrt_log_v2 (x : ℝ) (hx : 1000 ≤ x) :
-- sqrt (8 * x + 8) * log (8 * x + 8) ≤ x * log 4 :=
-- begin
--   calc sqrt (8 * x + 8) * log (8 * x + 8)
--       ≤ sqrt x * sqrt 9 * log (8 * x + 8) :
--         begin
--           apply mul_le_mul,
--           rw <-sqrt_mul,
--           apply (sqrt_le _).2,
--           linarith,
--           linarith,
--           linarith,
--           apply le_refl,
--           apply log_nonneg,
--           linarith,
--           apply mul_nonneg,
--           apply sqrt_nonneg,
--           apply sqrt_nonneg,
--         end
--   ... ≤ sqrt x * sqrt 9 * log (9 * x) :
--         begin
--           apply mul_le_mul,
--           apply le_refl,
--           apply (log_le_log _ _).2,
--           linarith,
--           linarith,
--           linarith,
--           apply log_nonneg,
--           linarith,
--           apply mul_nonneg,
--           apply sqrt_nonneg,
--           apply sqrt_nonneg,
--         end
--   ... ≤ x * log 4 :
--         begin
--           rw mul_assoc,
--           apply (le_div_iff' _).1,
--           rw mul_div_right_comm,
--           rw div_sqrt,
--           rw sqrt_9,
--           apply exp_le_exp.1,
--           rw mul_comm,
--           rw <-rpow_def_of_pos,
--           conv
--           begin
--             to_rhs,
--             rw mul_comm,
--           end,
--           rw <-rpow_def_of_pos,

--         end,

-- end


lemma pow_beats_pow_2 (n : ℕ) (n_large : 43046721 ≤ n) :
(8 * n + 8) ^ nat.sqrt (8 * n + 8) ≤ 4 ^ n :=
begin
  -- suffices : ((8 * n + 8) ^ nat.sqrt (8 * n + 8) : ℝ) ≤ 4 ^ n,
  apply (@nat.cast_le ℝ _ _ _ _).1,
  -- rw pow_coe 4 n,
  -- rw pow_coe (8 * n + 8) (nat.sqrt (8 * n + 8)),
  calc ↑((8 * n + 8) ^ nat.sqrt (8 * n + 8))
      ≤ (↑(8 * n + 8) ^ real.sqrt (↑(8 * n + 8))) :
          begin
            -- unfold_coes,
            rw pow_coe,
            apply real.rpow_le_rpow_of_exponent_le,
              {
                apply nat.one_le_cast.2,
                linarith,
                exact real.nontrivial,
              },
              {apply nat_sqrt_le_real_sqrt,},
          end
  ... ≤ ↑(4 ^ n) :
          begin
            apply (@real.log_le_log _ (↑(4 ^ n)) _ (by norm_num)).1,
            { rw real.log_rpow _,
              { rw pow_coe,
                rw real.log_rpow,
                { norm_cast,
                  norm_num,
                  apply linear_dominates_sqrt_log,
                  norm_cast,
                  exact n_large, },
                { norm_num, },
              },
              { norm_cast,
                linarith,},
              --rw pow_coe,
              --rw real.log_rpow,
              --{ sorry, },
              --{ norm_num, },
              --{ norm_num, sorry, },
            },
            { norm_num,
              refine rpow_pos_of_pos _ _,
              { norm_cast,
                linarith,},
            },
          end,
end

-- lemma sdhfal (n : ℕ) (n_large : 999 < n) : nat.sqrt (n / 8) * nat.sqrt (2 * n) ≤ n / 4 :=
-- begin
--   sorry
-- end

lemma sqrt_pow_le_linear_pow (n : ℕ) (hn : 1 ≤ 8 * (n / 4)) (hn2 : n % 4 < 4)
(hn3 : 43046721 ≤ n / 4)
: (2 * n) ^ nat.sqrt (2 * n) ≤ 4 ^ (n / 4) :=
begin
  calc (2 * n) ^ nat.sqrt (2 * n)
      = (2 * (4 * (n / 4) + (n % 4))) ^ nat.sqrt (2 * (4 * (n / 4) + (n % 4))) :
              by rw nat.div_add_mod n 4
  ... ≤ (2 * (4 * (n / 4) + (n % 4))) ^ nat.sqrt (8 * (n / 4) + 8) :
              begin
                apply pow_le_pow,
                -- squeeze_simp,
                rw mul_add,
                rw ←mul_assoc,
                norm_num,
                suffices : 1 ≤ 8 * (n / 4),
                  exact le_add_right this,
                linarith,
                apply nat.sqrt_le_sqrt,
                rw mul_add,
                rw ←mul_assoc,
                norm_num,
                -- squeeze_simp,
                linarith,
              end
  ... ≤ (8 * (n / 4) + 8) ^ nat.sqrt (8 * (n / 4) + 8) :
              begin
                apply (nat.pow_le_iff_le_left _).2,
                rw mul_add,
                rw ←mul_assoc,
                norm_num,
                linarith,
                -- rw mul_add,
                -- rw ←mul_assoc,
                -- norm_num,
                -- suffices : 1 ≤ 8 * (n / 4),
                --   exact le_add_right this,
                -- linarith,
                -- apply nat.sqrt_le_sqrt,
                -- simp only [nat.succ_pos', mul_le_mul_left, add_le_add_iff_left],
                -- linarith,
                apply nat.le_sqrt.2,
                -- rw mul_add,
                suffices : 1 * 1 ≤ 8,
                  exact le_add_left this,
                norm_num,
              end
  ... ≤ 4 ^ (n / 4) : pow_beats_pow_2 (n / 4) (by linarith),

end

lemma n_div_4_big (n : ℕ) (hn : 172186888 < n): 43046721 ≤ n / 4 :=
begin
  cases le_or_gt 43046721 (n / 4),
      { exact h, },
      {
        -- linarith,
        have r : n < n :=
          calc n = 4 * (n / 4) + (n % 4) : (nat.div_add_mod n 4).symm
            ... < 4 * 43046721 + (n % 4) : add_lt_add_right
                                            ((mul_lt_mul_left (nat.succ_pos 3)).2 h) _
            ... < 4 * 43046721 + 4 : add_lt_add_left (nat.mod_lt n (by linarith)) (4 * 43046721)
            ... = 172186888 : by norm_num
            ... < n : hn,
        exfalso,
        exact lt_irrefl _ r,
      },
end

lemma power_conversion_2 (n : ℕ) (n_large : 172186888 < n) :
(2 * n) ^ nat.sqrt (2 * n) ≤ 4 ^ (n / 4) := -- 1000 < n should be sufficient
begin
  have rem_small : (n % 4) < 4 := nat.mod_lt n (nat.succ_pos 3),
  apply sqrt_pow_le_linear_pow n,
  have fsadoi := n_div_4_big n n_large,
  linarith,
  exact rem_small,
  have fsadoi := n_div_4_big n n_large,
  exact fsadoi,
  -- (by linarith) rem_small this,
end


lemma fooo (n : ℕ) (n_pos : 1 ≤ n) : n / 15 + n / 4 + (2 * n / 3 + 1) ≤ n :=
begin
  suffices: n / 15 + n / 4 + 2 * n / 3 < n, by linarith,
  have s1 : (n / 15) * 15 ≤ n := nat.div_mul_le_self n 15,
  have s2 : (n / 4) * 4 ≤ n := nat.div_mul_le_self n 4,
  have s3 : (2 * n / 3) * 3 ≤ 2 * n := nat.div_mul_le_self (2 * n) 3,
  suffices: (n / 15 + n / 4 + 2 * n / 3) * 60 < n * 60, by linarith,
  calc (n / 15 + n / 4 + 2 * n / 3) * 60
      = n / 15 * 15 * 4 + n / 4 * 4 * 15 + 2 * n / 3 * 3 * 20 : by ring
  ... ≤ n * 4 + n * 15 + 2 * n * 20 : by linarith [s1, s2, s3]
  ... < n * 60 : by linarith,
end


lemma false_inequality_is_false {n : ℕ} (n_large : 172186888 < n) :
4 ^ n < (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1) → false :=
begin
  rw imp_false,
  rw not_lt,
  calc (2 * n + 1) * (2 * n) ^ nat.sqrt (2 * n) * 4 ^ (2 * n / 3 + 1)
       ≤ (4 ^ (n / 15)) * (2 * n) ^ nat.sqrt (2 * n) * 4 ^ (2 * n / 3 + 1) :
          begin
            apply (nat.mul_le_mul_right (4 ^ (2 * n / 3 + 1))),
            apply (nat.mul_le_mul_right ((2 * n) ^ nat.sqrt (2 * n))),
            apply power_conversion_1, -- needs 480 < n currently
            linarith,
          end
  ...  ≤ (4 ^ (n / 15)) * (4 ^ (n / 4)) * 4 ^ (2 * n / 3 + 1) :
          begin
            apply (nat.mul_le_mul_right (4 ^ (2 * n / 3 + 1))),
            apply (nat.mul_le_mul_left (4 ^ (n / 15))),
            apply power_conversion_2,
            finish
          end
  ...  ≤ 4 ^ n :
          begin
            rw tactic.ring.pow_add_rev,
            rw tactic.ring.pow_add_rev,
            apply nat.pow_le_pow_of_le_right,
            dec_trivial,
            exact fooo n (by linarith),
          end
end

lemma more_restrictive_filter_means_smaller_subset {a : _} {S : finset a} {f : _} {g : _}
[decidable_pred f] [decidable_pred g] (p : ∀ i, f i → g i): finset.filter f S ⊆ finset.filter g S
:=
begin
  intros h prop,
  simp only [finset.mem_filter] at prop,
  simp only [finset.mem_filter],
  exact ⟨prop.1, p h prop.2⟩,
end

lemma filter_to_subset {a : _} {S : finset a} {T : finset a} {p : _} [decidable_pred p]
(prop : ∀ i, p i → i ∈ T)
  : finset.filter p S ⊆ T :=
begin
  suffices : ∀ x, x ∈ finset.filter p S → x ∈ T, by exact finset.subset_iff.mpr this,
  intros x hyp,
  simp only [finset.mem_filter] at hyp,
  exact prop x hyp.2
end

lemma foo {n : ℕ} :
(finset.filter (λ (p : ℕ), p ^ 2 < 2 * n)
  (finset.filter nat.prime (finset.range (2 * n / 3 + 1)))).card ≤ nat.sqrt (2 * n) :=
begin
  have t : ∀ p, p ^ 2 ≤ 2 * n ↔ p ≤ nat.sqrt (2 * n),
  { intro p,
    exact nat.le_sqrt'.symm, },

  have u : ∀ p, (p ^ 2 < 2 * n) → p ^ 2 ≤ 2 * n, by
  { intros p hyp,
    exact le_of_lt hyp, },

  have v : finset.filter (λ p, p ^ 2 < 2 * n)
            (finset.filter nat.prime (finset.range (2 * n / 3 + 1))) ⊆
    finset.filter (λ p, p ^ 2 ≤ 2 * n)
      (finset.filter nat.prime (finset.range (2 * n / 3 + 1))) :=
    more_restrictive_filter_means_smaller_subset u,

  have w' : finset.filter (λ p, p ^ 2 ≤ 2 * n)
              (finset.filter nat.prime (finset.range (2 * n / 3 + 1))) =
    finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 0 (2 * n / 3 + 1))) :=
    by {
      apply congr_arg (λ i, finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime i)),
      exact finset.range_eq_Ico (2 * n / 3 + 1),
    },

  have w : finset.filter (λ p, p ^ 2 ≤ 2 * n)
            (finset.filter nat.prime (finset.Ico 0 (2 * n / 3 + 1))) =
    finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1))),
    { refine congr_arg (λ i, finset.filter (λ p, p ^ 2 ≤ 2 * n) i) _,
      ext1,
      split,
      { intros hyp,
        simp only [true_and, finset.Ico.mem, zero_le', finset.mem_filter] at hyp,
        simp only [finset.Ico.mem, finset.mem_filter],
        exact ⟨⟨nat.prime.two_le hyp.2, hyp.1⟩, hyp.2⟩, },
      { intros hyp,
        simp only [finset.Ico.mem, finset.mem_filter] at hyp,
        simp only [true_and, finset.Ico.mem, zero_le', finset.mem_filter],
        exact ⟨hyp.1.2, hyp.2⟩, }, },

  have g : finset.filter (λ p, p ^ 2 ≤ 2 * n)
            (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1))) =
    finset.filter (λ p, 2 ≤ p ^ 2 ∧ p ^ 2 ≤ 2 * n)
      (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1))),
    { ext1,
      split,
      { intros hyp,
        simp only [finset.Ico.mem, finset.mem_filter] at hyp,
        simp only [finset.Ico.mem, finset.mem_filter],
        have r : 2 ≤ a ^ 2 :=
          by calc 2 ≤ a : nat.prime.two_le hyp.1.2
          ... ≤ a * a : nat.le_mul_self a
          ... = a ^ 2 : by ring,
        exact ⟨hyp.1, ⟨r, hyp.2⟩⟩, },
      { intros hyp,
        simp only [finset.Ico.mem, finset.mem_filter] at hyp,
        simp only [finset.Ico.mem, finset.mem_filter],
        exact ⟨hyp.1, hyp.2.2⟩, }, },

  have h : (finset.filter (λ p, 2 ≤ p ^ 2 ∧ p ^ 2 ≤ 2 * n) (finset.filter nat.prime
            (finset.Ico 2 (2 * n / 3 + 1)))) ⊆ finset.Ico 2 (nat.sqrt (2 * n) + 1)
    , by {
      apply filter_to_subset _,
      intros i hyp,
      simp,
      split,
      { cases le_or_gt 2 i,
        { exact h, },
        { cases i,
          { linarith, },
          { cases i,
            { linarith, },
            { exact dec_trivial, }, } }, },
      { have : i ≤ nat.sqrt (2 * n) := nat.le_sqrt'.mpr hyp.2,
        linarith, },
    },

  calc (finset.filter (λ (p : ℕ), p ^ 2 < 2 * n)
        (finset.filter nat.prime (finset.range (2 * n / 3 + 1)))).card
      ≤ (finset.filter (λ p, p ^ 2 ≤ 2 * n)
          (finset.filter nat.prime (finset.range (2 * n / 3 + 1)))).card :
            finset.card_le_of_subset v
  ... = (finset.filter (λ p, p ^ 2 ≤ 2 * n)
          (finset.filter nat.prime (finset.Ico 0 (2 * n / 3 + 1)))).card: congr_arg finset.card w'
  ... = (finset.filter (λ p, p ^ 2 ≤ 2 * n)
          (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1)))).card: congr_arg finset.card w
  ... = (finset.filter (λ p, 2 ≤ p ^ 2 ∧ p ^ 2 ≤ 2 * n)
          (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1)))).card: congr_arg finset.card g
  ... ≤ (finset.Ico 2 (nat.sqrt (2 * n) + 1)).card: finset.card_le_of_subset h
  ... = nat.sqrt (2 * n) + 1 - 2: finset.Ico.card 2 (nat.sqrt (2 * n) + 1)
  ... = nat.sqrt (2 * n) - 1: by ring
  ... ≤ nat.sqrt (2 * n): (nat.sqrt (2 * n)).sub_le 1,

end

lemma bertrand_eventually (n : nat) (n_big : 172186888 < n)
: ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
  by_contradiction no_prime,

  have central_binom_factorization_small :
      ∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
        p ^ (padic_val_nat p ((2 * n).choose n))
      =
      ∏ p in finset.filter nat.prime (finset.range (((2 * n).choose n + 1))),
        p ^ (padic_val_nat p ((2 * n).choose n)) ,
    { apply finset.prod_subset,
      apply finset.subset_iff.2,
      intro x,
      rw [finset.mem_filter, finset.mem_filter, finset.mem_range, finset.mem_range],
      intro hx,
      split,
      { linarith [(hx.left), (two_n_div_3_le_two_mul_n_choose_n n)], },
      { exact hx.right, },
      intro x,
      rw [finset.mem_filter, finset.mem_filter, finset.mem_range, finset.mem_range],
      intros hx h2x,
      simp only [hx.right, and_true, not_lt] at h2x,
      by_contradiction,
      have x_le_two_mul_n : x ≤ 2 * n, by
        { apply (@claim_4 x ⟨hx.right⟩ n),
          unfold α,
          simp only [gt_iff_lt],
          by_contradiction h1,
          rw not_pos_iff_zero at h1,
          rw h1 at h,
          rw pow_zero at h,
          simp only [eq_self_iff_true, not_true] at h,
          exact h, },
      apply no_prime,
      use x,
      split,
      { exact hx.right, },
      { split,
        { by_contradiction neg_n_le_x,
          simp only [not_lt] at neg_n_le_x,
          have claim := @claim_3 x ⟨hx.right⟩ n (by linarith) (by linarith) (alskjhads n x h2x),
          unfold α at claim,
          rw [claim, pow_zero] at h,
          simp only [eq_self_iff_true, not_true] at h,
          exact h, },
        exact x_le_two_mul_n, }, },

    have double_pow_pos: ∀ (i : ℕ), 0 < (2 * n) ^ i,
    { intros _, exact pow_pos (by linarith) _ },

    have binom_inequality : (2 * n).choose n < (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1),
    by
      calc (2 * n).choose n
              = (∏ p in finset.filter nat.prime (finset.range ((2 * n).choose n + 1)),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                      : (central_binom_factorization n).symm
      ...     = (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                      : central_binom_factorization_small.symm
      ...     = (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   if p ^ 2 ≤ 2 * n then p ^ (padic_val_nat p ((2 * n).choose n))
                      else p ^ (padic_val_nat p ((2 * n).choose n)))
                       : by simp only [if_t_t]
      ...     = (∏ p in finset.filter (λ p, p ^ 2 ≤ 2 * n)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                    p ^ (padic_val_nat p ((2 * n).choose n)))
                 *
                (∏ p in finset.filter (λ p, ¬p ^ 2 ≤ 2 * n) (finset.filter nat.prime
                  (finset.range (2 * n / 3 + 1))),
                    p ^ (padic_val_nat p ((2 * n).choose n)))
                    : finset.prod_ite _ _
      ...     = (∏ p in finset.filter (λ p, p ^ 2 ≤ 2 * n)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                 *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                     : by simp only [not_le, finset.filter_congr_decidable]
      ...     ≤ (∏ p in finset.filter (λ p, p ^ 2 ≤ 2 * n)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   2 * n)
                 *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                     : begin
                       refine (nat.mul_le_mul_right _ _),
                       refine finset.prod_le_prod'' _,
                       intros i hyp,
                       simp only [finset.mem_filter, finset.mem_range] at hyp,
                       exact @claim_1 i (fact_iff.2 hyp.1.2) n (by linarith),
                     end
      ...     = (2 * n) ^ finset.card (finset.filter (λ p, p ^ 2 ≤ 2 * n)
                                        (finset.filter nat.prime (finset.range (2 * n / 3 + 1))))
                *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                   : by simp only [finset.prod_const]
      ...     = (2 * n) ^ finset.card (finset.filter (λ p, p ^ 2 < 2 * n)
                                        (finset.filter nat.prime (finset.range (2 * n / 3 + 1))))
                *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                   : begin
                    refine (nat.mul_left_inj _).2 _,
                    { refine prod_of_pos_is_pos _,
                      intros p hyp,
                      simp only [finset.mem_filter, finset.mem_range] at hyp,
                      exact pow_pos
                              (nat.prime.pos hyp.1.2)
                              (padic_val_nat p ((2 * n).choose n)), },
                    { refine congr_arg (λ i, (2 * n) ^ i) _,
                      refine congr_arg (λ s, finset.card s) _,
                      ext1,
                      split,
                      { intro h, simp at h, simp, split, exact h.1, exact even_prime_is_small h.1.2
                                                                          (by linarith) h.2, },
                      { intro h, simp at h, simp, split, exact h.1, linarith, }
                     },
                   end
      ...     ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                     : begin
                       refine (nat.mul_le_mul_right _ _),
                       refine pow_le_pow (by linarith) _,
                       exact foo,
                     end
      ...     ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ 1)
                     : begin
                       refine nat.mul_le_mul_left _ _,
                        { refine finset.prod_le_prod'' _,
                          intros i hyp,
                          simp only [finset.mem_filter, finset.mem_range] at hyp,
                          cases hyp with i_facts sqrt_two_n_lt_i,
                          refine pow_le_pow _ _,
                          { cases le_or_gt 1 i,
                            { exact h, },
                            { have i_zero : i = 0, by linarith,
                              rw i_zero at i_facts,
                              exfalso,
                              exact nat.not_prime_zero i_facts.2, }, },
                          { exact @claim_2 i (fact_iff.2 i_facts.2) n (by linarith)
                            sqrt_two_n_lt_i, }, },
                     end
      ...     ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   p ^ 1)
                     : begin
                       refine nat.mul_le_mul_left _ _,
                       refine finset.prod_le_prod_of_subset_of_one_le'
                                (finset.filter_subset _ _) _,
                        { intros i hyp1 hyp2,
                        cases le_or_gt 1 i,
                        { ring_nf, exact h, },
                        { have i_zero : i = 0, by linarith,
                          simp only [i_zero, true_and, nat.succ_pos', finset.mem_filter,
                                    finset.mem_range] at hyp1,
                          exfalso, exact nat.not_prime_zero hyp1, }, }
                     end
      ...     = (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   p)
                     : by simp only [pow_one]
      ...     = (2 * n) ^ (nat.sqrt (2 * n))
               *
                (primorial (2 * n / 3))
                     : by unfold primorial
      ...     ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                4 ^ (2 * n / 3)
                     : nat.mul_le_mul_left _ (primorial_le_4_pow (2 * n / 3))
      ...     < (2 * n) ^ (nat.sqrt (2 * n))
                 *
                4 ^ (2 * n / 3 + 1)
                : (mul_lt_mul_left (pow_pos (by linarith) _)).mpr (pow_lt_pow
                    (by simp only [nat.succ_pos', nat.one_lt_bit0_iff, nat.one_le_bit0_iff])
                    (by simp only [nat.succ_pos', lt_add_iff_pos_right])),

  have false_inequality : 4 ^ n < (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1),
  by
    calc 4 ^ n ≤ (2 * n + 1) * (2 * n).choose n : central_binom_lower_bound n
      ...      < (2 * n + 1) * ((2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1))
                  : nat.mul_lt_mul_of_pos_left binom_inequality (by linarith)
      ...      = (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1) : by ring,

  exfalso,
  exact false_inequality_is_false n_big false_inequality,
end

lemma prime_199999991 : nat.prime 199999991 :=
begin
  norm_num,
end

lemma prime_119999987 : nat.prime 119999987 :=
begin
  norm_num,
end

lemma prime_79999987 : nat.prime 79999987 :=
begin
  norm_num,
end

lemma prime_49999991 : nat.prime 49999991 :=
begin
  norm_num,
end

lemma prime_25999949 : nat.prime 25999949 :=
begin
  norm_num,
end

lemma prime_13999981 : nat.prime 13999981 :=
begin
  norm_num,
end

lemma prime_7199957 : nat.prime 7199957 :=
begin
  norm_num,
end

lemma prime_3799973 : nat.prime 3799973 :=
begin
  norm_num,
end

lemma prime_1999993 : nat.prime 1999993 :=
begin
  norm_num,
end

lemma prime_1019971 : nat.prime 1019971 :=
begin
  norm_num,
end

lemma prime_519997 : nat.prime 519997 :=
begin
  norm_num,
end

lemma prime_279991 : nat.prime 279991 :=
begin
  norm_num,
end

lemma prime_141991 : nat.prime 141991 :=
begin
  norm_num,
end

lemma prime_71999 : nat.prime 71999 :=
begin
  norm_num,
end

lemma prime_37997 : nat.prime 37997 :=
begin
  norm_num,
end

lemma prime_19997 : nat.prime 19997 :=
begin
  norm_num,
end

lemma prime_10193 : nat.prime 10193 :=
begin
  norm_num,
end

lemma prime_5197 : nat.prime 5197 :=
begin
  norm_num,
end

lemma prime_2797 : nat.prime 2797 :=
begin
  norm_num,
end

lemma prime_1409 : nat.prime 1409 :=
begin
  norm_num,
end

lemma prime_719 : nat.prime 719 :=
begin
  norm_num,
end

lemma prime_547 : nat.prime 547 :=
begin
  norm_num,
end

lemma prime_277 : nat.prime 277 :=
begin
  norm_num,
end

lemma prime_139 : nat.prime 139 :=
begin
  norm_num,
end

lemma prime_73 : nat.prime 73 :=
begin
  norm_num,
end

lemma prime_37 : nat.prime 37 :=
begin
  norm_num,
end
lemma prime_19 : nat.prime 19 :=
begin
  norm_num,
end
lemma prime_11 : nat.prime 11 :=
begin
  norm_num,
end
lemma prime_7 : nat.prime 7 :=
begin
  norm_num,
end

lemma bertrand_initially (n : nat) (n_pos : 0 < n) (n_small : n ≤ 172186888) :
∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n
:=
begin

  cases le_or_lt 100000000 n,
  { use 199999991, split, exact prime_199999991, split, linarith, linarith, },
  clear n_small,

  cases le_or_lt 60000000 n,
  { use 119999987, split, exact prime_119999987, split, linarith, linarith, },
  clear h,

  cases le_or_lt 40000000 n,
  { use 79999987, split, exact prime_79999987, split, linarith, linarith, },
  clear h_1,

  cases le_or_lt 25000000 n,
  { use 49999991, split, exact prime_49999991, split, linarith, linarith, },
  clear h,

  cases le_or_lt 13000000 n,
  { use 25999949, split, exact prime_25999949, split, linarith, linarith, },
  clear h_1,

  cases le_or_lt 7000000 n,
  { use 13999981, split, exact prime_13999981, split, linarith, linarith, },
  clear h,

  cases le_or_lt 3600000 n,
  { use 7199957, split, exact prime_7199957, split, linarith, linarith, },
  clear h_1,

  cases le_or_lt 1900000 n,
  { use 3799973, split, exact prime_3799973, split, linarith, linarith, },
  clear h,

  cases le_or_lt 1000000 n,
  { use 1999993, split, exact prime_1999993, split, linarith, linarith, },
  clear h_1,

  cases le_or_lt 510000 n,
  { use 1019971, split, exact prime_1019971, split, linarith, linarith, },
  clear h,

  cases le_or_lt 260000 n,
  { use 519997, split, exact prime_519997, split, linarith, linarith, },
  clear h_1,

  cases le_or_lt 140000 n,
  { use 279991, split, exact prime_279991, split, linarith, linarith, },
  clear h,

  cases le_or_lt 71000 n,
  { use 141991, split, exact prime_141991, split, linarith, linarith, },
  clear h_1,

  cases le_or_lt 36000 n,
  { use 71999, split, exact prime_71999, split, linarith, linarith, },
  clear h,

  cases le_or_lt 19000 n,
  { use 37997, split, exact prime_37997, split, linarith, linarith, },
  clear h_1,

  cases le_or_lt 10000 n,
  { use 19997, split, exact prime_19997, split, linarith, linarith, },
  clear h,

  cases le_or_lt 5100 n,
  { use 10193, split, exact prime_10193, split, linarith, linarith, },
  clear h_1,

  cases le_or_lt 2600 n,
  { use 5197, split, exact prime_5197, split, linarith, linarith, },
  clear h,

  cases le_or_lt 1400 n,
  { use 2797, split, exact prime_2797, split, linarith, linarith, },
  clear h_1,

  cases le_or_lt 710 n,
  { use 1409, split, exact prime_1409, split, linarith, linarith, },
  clear h,

  cases le_or_lt 360 n,
  { use 719, split, exact prime_719, split, linarith, linarith, },
  clear h_1,

  cases le_or_lt 274 n,
  { use 547, split, exact prime_547, split, linarith, linarith, },
  clear h,

  cases le_or_lt 139 n,
  { use 277, split, exact prime_277, split, linarith, linarith, },
  clear h_1,

  cases le_or_lt 70 n,
  { use 139, split, exact prime_139, split, linarith, linarith, },
  clear h,

  cases le_or_lt 37 n,
  { use 73, split, exact prime_73, split, linarith, linarith, },
  clear h_1,

  cases le_or_lt 19 n,
  { use 37, split, exact prime_37, split, linarith, linarith, },
  clear h,

  cases le_or_lt 11 n,
  { use 19, split, exact prime_19, split, linarith, linarith, },
  clear h_1,

  cases le_or_lt 6 n,
  { use 11, split, exact prime_11, split, linarith, linarith, },
  clear h,

  cases le_or_lt 4 n,
  { use 7, split, exact prime_7, split, linarith, linarith, },
  clear h_1,

  interval_cases n,
  { use 2, norm_num },
  { use 3, norm_num },
  { use 5, norm_num },
end

theorem bertrand (n : nat) (n_pos : 0 < n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin

cases lt_or_le 172186888 n,
{exact bertrand_eventually n h},
{exact bertrand_initially n n_pos h},

end
