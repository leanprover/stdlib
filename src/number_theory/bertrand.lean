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
import data.complex.exponential_bounds
import tactic
import ring_theory.multiplicity
import algebra.module
import number_theory.primorial
import analysis.special_functions.pow
import analysis.special_functions.trigonometric
import analysis.special_functions.sqrt
import analysis.calculus.local_extr
import data.real.sqrt
import data.real.nnreal

open_locale big_operators

/-- The multiplicity of p in the nth central binomial coefficient-/
private def α (n p : nat) [hp : fact p.prime] : nat :=
padic_val_nat p ((2 * n).choose n)

lemma nat.self_le_mul {m : ℕ} : ∀ {n : ℕ} (n0 : 0 < n), m ≤ n * m
| 0     h := (lt_irrefl _ h).elim
| 1     h := (one_mul m).symm.le
| (n+2) h := trans (nat.self_le_mul n.succ_pos) $ mul_le_mul_right' n.succ.le_succ _

lemma nat.le_two_mul_self (n : ℕ) : n ≤ 2 * n :=
nat.self_le_mul zero_lt_two

lemma central_binom_nonzero (n : ℕ) : (2 * n).choose n ≠ 0 :=
(nat.choose_pos n.le_two_mul_self).ne'

lemma claim_1
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 3 ≤ n)
  : p ^ (α n p) ≤ 2 * n
  :=
begin
  unfold α,
  rw @padic_val_nat_def p hp ((2 * n).choose n) (central_binom_nonzero n),
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (p.log (2 * n) + 1)
                        (hp.out) n.le_two_mul_self (lt_add_one (p.log (2 * n)))],
  have r : 2 * n - n = n,
    calc 2 * n - n = n + n - n: congr_arg (flip (has_sub.sub) n) (two_mul n)
    ... = n: nat.add_sub_cancel n n,
  simp [r, ←two_mul],
  apply trans (pow_le_pow (trans one_le_two hp.out.two_le) _) (_ : p ^ p.log (2 * n) ≤ 2 * n),
  { calc _  ≤ (finset.Ico 1 (nat.log p (2 * n) + 1)).card : finset.card_filter_le _ _
        ... = (p.log (2 * n) + 1) - 1                     : finset.Ico.card _ _ },
  { refine nat.pow_log_le_self _ _ hp.out.one_lt _,
    calc 1 ≤ 3     : nat.one_le_bit1 1
       ... ≤ n     : n_big
       ... ≤ 2 * n : n.le_two_mul_self }
end

lemma claim_2
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 3 ≤ n)
  (smallish : (2 * n) < p ^ 2)
  : (α n p) ≤ 1
  :=
nat.le_of_lt_succ $ (pow_lt_pow_iff hp.out.one_lt).1 $
  calc p ^ α n p ≤ 2 * n : claim_1 p n n_big
             ... < p ^ 2 : smallish

lemma twice_nat_small (n : nat) (h : 2 * n < 2) : n = 0 :=
nat.le_zero_iff.mp $ nat.le_of_lt_succ $
  lt_of_mul_lt_mul_left (h.trans_le (mul_one _).symm.le) (nat.zero_le _)

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
  rw @padic_val_nat_def p hp ((2 * n).choose n) (central_binom_nonzero n),
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (p.log (2 * n) + 1)
                        (hp.out) n.le_two_mul_self (lt_add_one (p.log (2 * n)))],
  have r : 2 * n - n = n,
    calc 2 * n - n = n + n - n : congr_arg (flip (has_sub.sub) n) (two_mul n)
               ... = n         : nat.add_sub_cancel n n,
  simp only [r, ←two_mul, finset.card_eq_zero, enat.get_coe', finset.filter_congr_decidable],
  clear r,

  let p_pos : 0 < p := trans zero_lt_one hp.out.one_lt,

  apply finset.filter_false_of_mem,
  intros i i_in_interval,
  rw finset.Ico.mem at i_in_interval,
  have three_lt_p : 3 ≤ p ,
  { rcases le_or_lt 3 p with H|H,
    { exact H, },
    { refine (lt_irrefl 12 _).elim,
      calc 12 = 2 * 6 : rfl
        ... < 2 * n   : (mul_lt_mul_left zero_lt_two).2 n_big
        ... < 3 * p   : big
        ... < 3 * 3   : (mul_lt_mul_left zero_lt_three).2 H
        ... = 9       : rfl
        ... < 12      : nat.lt_of_sub_eq_succ rfl } },

  refine not_le.mpr _,

  rcases lt_trichotomy 1 i with H|rfl|H,
  { have two_le_i : 2 ≤ i := nat.succ_le_of_lt H,
    have two_n_lt_pow_p_i : 2 * n < p ^ i,
    { calc 2 * n < 3 * p : big
             ... ≤ p * p : (mul_le_mul_right p_pos).2 three_lt_p
             ... = p ^ 2 : (sq _).symm
             ... ≤ p ^ i : nat.pow_le_pow_of_le_right p_pos two_le_i, },
    have n_mod : n % p ^ i = n,
    { apply nat.mod_eq_of_lt,
      calc n ≤ n + n : nat.le.intro rfl
         ... = 2 * n : (two_mul n).symm
         ... < p ^ i : two_n_lt_pow_p_i, },
    rw n_mod,
    exact two_n_lt_pow_p_i, },

    { rw [pow_one],
      suffices h23 : 2 * (p * (n / p)) + 2 * (n % p) < 2 * (p * (n / p)) + p,
      { exact (add_lt_add_iff_left (2 * (p * (n / p)))).mp h23, },
      have n_big : 1 ≤ (n / p) := (nat.le_div_iff_mul_le' p_pos).2 (trans (one_mul _).le small),
      rw [←mul_add, nat.div_add_mod],
      calc  2 * n < 3 * p : big
              ... = 2 * p + p : nat.succ_mul _ _
              ... ≤ 2 * (p * (n / p)) + p : add_le_add_right ((mul_le_mul_left zero_lt_two).mpr $
                ((le_mul_iff_one_le_right p_pos).mpr n_big)) _ },
    { have : i = 0 := nat.le_zero_iff.mp (nat.le_of_lt_succ H),
      rw [this, pow_zero, nat.mod_one, mul_zero],
      exact zero_lt_one }
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
  rw @padic_val_nat_def p hp ((2 * n).choose n) (central_binom_nonzero n) at multiplicity_pos,
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (p.log (2 * n) + 1) hp.out
    n.le_two_mul_self (lt_add_one (p.log (2 * n)))] at multiplicity_pos,
  have r : 2 * n - n = n,
    calc 2 * n - n = n + n - n : congr_arg (flip (has_sub.sub) n) (two_mul n)
               ... = n         : nat.add_sub_cancel n n,
  simp only [r, ←two_mul, gt_iff_lt, enat.get_coe', finset.filter_congr_decidable]
    at multiplicity_pos,
  clear r,
  rw finset.card_pos at multiplicity_pos,
  cases multiplicity_pos with m hm,
  simp only [finset.Ico.mem, finset.mem_filter] at hm,
  calc p = p ^ 1 : (pow_one _).symm
  ...    ≤ p ^ m : nat.pow_le_pow_of_le_right
                    (show 0 < p, from trans zero_lt_one hp.out.one_lt) hm.left.left
  ...    ≤ 2 * (n % p ^ m) : hm.right
  ...    ≤ 2 * n : nat.mul_le_mul_left _ (nat.mod_le n _),
end

/-
Then:
4^n ≤ 2nCn * (2 * n + 1) (by choose_halfway_is_big)
= prod (primes ≤ 2n) p^(α n p) * (2n+1)
= prod (primes ≤ n) p^(α n p) * prod (primes n < p <= 2n) p^α * (2n+1)
= prod (primes ≤ 2n/3) p^α * prod (primes 2n/3 to n) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes ≤ 2n/3) p^α * prod (primes 2n/3 to n) 1 * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by claim 3)
= prod (primes ≤ 2n/3) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes ≤ sqrt(2n)) p^α * prod(primes sqrt(2n)..2n/3) p^α
  * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ prod (primes ≤ sqrt(2n)) p^α * prod(primes sqrt(2n)..2n/3) p
  * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by claim 2)
≤ prod (primes ≤ sqrt(2n)) p^α * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by a general bound on the primorial)
≤ prod (primes ≤ sqrt(2n)) (2n) * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by claim 1)
= (2n)^π (sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ (2n)^(sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by "prime count of x is less than x")

For sufficiently large n, that last product term is > 1.
Indeed, suppose for contradiction it's equal to 1.
Then 4^n ≤ (2n)^(sqrt 2n) * 4^(2n/3) * (2n+1)
so 4^(n/3) ≤ (2n)^(sqrt 2n) (2n+1)
and this is Clearly False for sufficiently large n.
-/

lemma two_n_div_3_le_two_mul_n_choose_n (n : ℕ) : 2 * n / 3 < (2 * n).choose n :=
begin
  cases n,
  { simp only [nat.succ_pos', nat.choose_self, nat.zero_div, mul_zero], },
  calc 2 * (n + 1) / 3 < 2 * (n + 1): nat.div_lt_self (by norm_num) (by norm_num)
  ... = (2 * (n + 1)).choose(1): by norm_num
  ... ≤ (2 * (n + 1)).choose(2 * (n + 1) / 2): nat.choose_le_middle 1 (2 * (n + 1))
  ... = (2 * (n + 1)).choose(n + 1): by simp only [nat.succ_pos', nat.mul_div_right]
end

lemma not_pos_iff_zero (n : ℕ) : ¬ 0 < n ↔ n = 0 := trans not_lt le_zero_iff

lemma alskjhads_no_two (n x : ℕ) (h : n / 3 + 1 ≤ x) : n < 3 * x :=
lt_of_lt_of_le ((nat.div_lt_iff_lt_mul' zero_lt_three).mp (nat.succ_le_iff.mp h)) (mul_comm _ _).le

lemma alskjhads (n x : ℕ): 2 * n / 3 + 1 ≤ x -> 2 * n < 3 * x :=
alskjhads_no_two (2 * n) x

lemma central_binom_factorization (n : ℕ) :
      ∏ p in finset.filter nat.prime (finset.range ((2 * n).choose n + 1)),
        p ^ (padic_val_nat p ((2 * n).choose n))
      = (2 * n).choose n :=
  prod_pow_prime_padic_val_nat _ (central_binom_nonzero n) _ (lt_add_one _)


-- lemma two_mul (n : ℕ) : 2 * n = n + n := by linarith

lemma stronger_central_binom_lower_bound (n : ℕ) (n_big : 4 ≤ n) :
  4 ^ n ≤ n * (2 * n).choose n :=
begin
  induction n,
  linarith,
  rw <-nat.add_one at *,

  by_cases n_n = 3,
    {
      rw h, norm_num,
      simp [nat.choose],
      norm_num,
    },
    {
      have hdsf : 4 ≤ n_n,
        have aeiauh := lt_or_eq_of_le n_big,
        cases aeiauh,
        linarith,
        by_contra asoi,
        rw add_comm at aeiauh,
        have adojf := nat.sub_eq_of_eq_add aeiauh,
        rw adojf.symm at h,
        simp at h,
        exact h,
      have dsapo := n_ih hdsf,
      rw pow_succ,
      rw mul_add,
      norm_num,
      -- rw nat.choose,
      calc 4 * 4 ^ n_n ≤ 4 * (n_n * (2 * n_n).choose n_n) :
              begin
                apply mul_le_mul,
                exact rfl.ge,
                exact dsapo,
                exact zero_le (4 ^ n_n),
                apply zero_le,
              end
      ... ≤ (n_n + 1) * ((2 * n_n + 2).choose (n_n + 1)) :
              begin
                simp [nat.choose, nat.choose_symm_half, <-two_mul],
                -- rw nat.choose_eq_factorial_div_factorial,
                -- rw nat.choose_eq_factorial_div_factorial,
                -- simp [nat.factorial],
                sorry
              end,



    }
    -- calc 4 ^ n = (1 + 1) ^ (2 * n) : by norm_num [pow_mul]
    -- ...        = ∑ m in range (2 * n + 1), choose (2 * n) m : by simp [add_pow]
    -- ...        ≤ ∑ m in range (2 * n + 1), choose (2 * n) (2 * n / 2) :
    --   sum_le_sum (λ i hi, choose_le_middle i (2 * n))
    -- ...        = (2 * n + 1) * choose (2 * n) n : by simp
end


def central_binom_lower_bound := nat.four_pow_le_two_mul_add_one_mul_central_binom

lemma interchange_filters {α: _} {S: finset α} {f g: α → Prop} [decidable_pred f] [decidable_pred g] : (S.filter g).filter f = S.filter (λ i, g i ∧ f i) :=
by { ext1, simp only [finset.mem_filter, and_assoc] }

lemma interchange_and_in_filter {α: _} {S: finset α} {f g: α → Prop} [decidable_pred f] [decidable_pred g] : S.filter (λ i, g i ∧ f i) = S.filter (λ i, f i ∧ g i) :=
by { ext1, simp only [finset.mem_filter, and.comm, iff_self] }

lemma intervening_sqrt {a n : ℕ} (small : (nat.sqrt n) ^ 2 ≤ a ^ 2) (big : a ^ 2 ≤ n) : a = nat.sqrt n :=
begin
  rcases lt_trichotomy a (nat.sqrt n) with H|rfl|H,
  { refine (lt_irrefl (a ^ 2) _).elim,
    calc  _ = a * a             : sq _
         ... < n.sqrt * n.sqrt  : nat.mul_self_lt_mul_self H
         ... = (nat.sqrt n) ^ 2 : (sq _).symm
         ... ≤ a ^ 2            : small, },
  { refl, },
  { refine (lt_irrefl (a ^ 2) _).elim,
    calc  _ ≤ n     : big
        ... < a * a : nat.sqrt_lt.1 H
        ... = a ^ 2 : (sq _).symm, },
end

lemma filter_filter_card_le_filter_card {α: _} {S: finset α} {f g: α → Prop} [_inst : decidable_pred f][_inst : decidable_pred g] : ((S.filter g).filter f).card ≤ (S.filter f).card :=
begin
  calc ((S.filter g).filter f).card = (S.filter (λ i, g i ∧ f i)).card: congr_arg finset.card interchange_filters
  ... = (S.filter (λ i, f i ∧ g i)).card: congr_arg finset.card interchange_and_in_filter
  ... = ((S.filter f).filter g).card: congr_arg finset.card interchange_filters.symm
  ... ≤ (S.filter f).card: (finset.filter f S).card_filter_le g,
end

lemma filter_size {S : finset ℕ} {a : ℕ} : (finset.filter (λ p, p < a) S).card ≤ a :=
have t : ∀ i, i ∈ (S.filter (λ p, p < a)) → i ∈ finset.range(a), by simp,
have r: S.filter (λ p, p < a) ⊆ finset.range(a) := finset.subset_iff.mpr t,
have s: (S.filter (λ p, p < a)).card ≤ (finset.range(a)).card := finset.card_le_of_subset r,
by simpa only [finset.card_range] using s

lemma even_prime_is_two {p : ℕ} (pr: nat.prime p) (div: 2 ∣ p) : p = 2 :=
((nat.prime_dvd_prime_iff_eq nat.prime_two pr).mp div).symm

lemma even_prime_is_small {a n : ℕ} (a_prime : nat.prime a) (n_big : 2 < n) (small : a ^ 2 ≤ 2 * n): a ^ 2 < 2 * n :=
begin
  cases lt_or_ge (a ^ 2) (2 * n),
  { exact h, },
  { have t : a * a = 2 * n := (sq _).symm.trans (small.antisymm h),
    have a_even : 2 ∣ a := (or_self _).mp ((nat.prime.dvd_mul nat.prime_two).mp ⟨n, t⟩),
    have a_two : a = 2 := even_prime_is_two a_prime a_even,
    rw [a_two, sq],
    exact (mul_lt_mul_left zero_lt_two).mpr n_big },
end

lemma pow_beats_mul (n : ℕ) (big : 3 < n) : 32 * n ≤ 4 ^ n :=
begin
  induction n with n hyp,
  { exact zero_le_one, },
  { cases le_or_gt n 3,
    { have s : n = 3 := h.antisymm (nat.lt_succ_iff.mp big),
      rw s,
      norm_num, },
  { specialize hyp h,
    have r : 32 ≤ 4 ^ n := trans
        (trans (nat.self_le_mul (trans zero_lt_three h)) (mul_comm _ _ ).le) hyp,
    calc 32 * (n + 1) = 32 * n + 32 : mul_add _ _ _
    ... ≤ 4 ^ n + 32 : add_le_add_right hyp _
    ... ≤ 4 ^ n + 4 ^ n : add_le_add_left r _
    ... = (4 ^ n) * 2 : (mul_two _).symm
    ... ≤ (4 ^ n) * 4 : (mul_le_mul_left (pow_pos zero_lt_four _)).mpr (nat.le_of_sub_eq_zero rfl)
    ... = 4 ^ (n + 1) : (pow_succ' _ _).symm, }, },
end

lemma six_le_three_mul_four_pow_succ : ∀ (k : ℕ), 6 ≤ 3 * 4 ^ (k + 1)
| 0       := by norm_num
| (k + 1) := calc  6 ≤ 3 * 4 ^ (k + 1) : six_le_three_mul_four_pow_succ k
                 ... ≤ 3 * 4 ^ (k + 2) : (mul_le_mul_left zero_lt_three).mpr $
                   pow_le_pow (nat.succ_pos 3) (nat.le_succ _)

lemma thirty_mul_succ_le_four_pow {n : ℕ} (n4 : 4 ≤ n) :
  30 * (n + 1) ≤ 4 ^ n :=
begin
  rcases le_iff_exists_add.mp n4 with ⟨k, rfl⟩,
  -- Case k = 0: easy
  cases k, { norm_num },
  -- Case k = 1: easy
  cases k, { norm_num },
  rw pow_add,
  refine mul_le_mul _ _ (zero_le _) (zero_le _),
  { norm_num },
  { obtain F : k + 1 < 4 ^ (k + 1) := (k + 1).lt_pow_self (nat.succ_lt_succ (2 : ℕ).succ_pos),
    calc  _ = k + 1 + 6 : (congr_arg nat.succ (add_comm 4 _) : _)
        ... ≤ 4 ^ (k + 1) + 6                : add_le_add_right F.le _
        ... ≤ 4 ^ (k + 1) +  3 * 4 ^ (k + 1) : add_le_add_left (six_le_three_mul_four_pow_succ k) _
        ... = 3 * 4 ^ (k + 1) + 4 ^ (k + 1)  : add_comm _ _
        ... = 4 * 4 ^ (k + 1)                : (nat.succ_mul _ _).symm }
end

lemma succ_two_mul_le_four_pow_div_fifteen {n : ℕ} (n_large : 60 ≤ n) :
  2 * n + 1 ≤ 4 ^ (n / 15) :=
begin
  obtain F : 30 * (n / 15 + 1) ≤ 4 ^ (n / 15) := thirty_mul_succ_le_four_pow
    ((nat.le_div_iff_mul_le _ _ (nat.succ_pos 14)).mpr n_large : 4 ≤ n / 15),
  refine trans (nat.succ_le_of_lt _ : 2 * n < 2 * 15 * (n / 15 + 1)) F,
  rw mul_assoc,
  exact (mul_lt_mul_left zero_lt_two).mpr (nat.lt_mul_div_succ _ (nat.succ_pos 14)),
end

lemma power_conversion_1 (n : ℕ) (n_large : 480 < n) : 2 * n + 1 ≤ 4 ^ (n / 15) :=
succ_two_mul_le_four_pow_div_fifteen (trans (nat.le_of_sub_eq_zero rfl : 60 ≤ 481) n_large)

open real
open_locale nnreal

lemma pow_coe (a b : ℕ) : (↑(a ^ b) : ℝ) = (↑a) ^ (↑b : ℝ) :=
by simp only [rpow_nat_cast, nat.cast_pow]

lemma nat_sqrt_le_real_sqrt (a : ℕ) : (nat.sqrt a : ℝ) ≤ real.sqrt a :=
le_sqrt_of_sq_le (by simpa using (nat.cast_le.mpr a.sqrt_le' : ((id nat.sqrt a ^ 2 : ℕ) : ℝ) ≤ a))

open set

noncomputable def fff (x : ℝ) := x * log 4 - sqrt (8 * x + 8) * log (8 * x + 8)

noncomputable def fff' (x : ℝ) := log 4 - (((8 / (2 * (sqrt (8 * x + 8)))) * log (8 * x + 8)) + (sqrt (8 * x + 8) * (8 / (8 * x + 8))))

lemma derivative_fff {x : ℝ} (h : 0 < x) : has_deriv_at (λ x, fff x) (fff' x) x :=
begin
  have linear_deriv: has_deriv_at (λ (x : ℝ), 8 * x + 8) 8 x,
    { refine has_deriv_at.add_const _ _,
      simpa using has_deriv_at.const_mul (8 : ℝ) (has_deriv_at_id x), },
  unfold fff,
  refine has_deriv_at.sub _ _,
  { suffices: has_deriv_at (λ x, x * log 4) (1 * log 4) x, by simpa using this,
    refine has_deriv_at.mul_const _ _,
    exact has_deriv_at_id _, },
  { refine @has_deriv_at.mul _ _ x (λ x, sqrt (8 * x + 8)) (λ x, log (8 * x + 8)) _ _ _ _,
    { refine has_deriv_at.sqrt _ _,
      { exact linear_deriv, },
      { linarith, }, },
    { refine has_deriv_at.log _ _,
      { exact linear_deriv, },
      { linarith, }, }, },
end

lemma fff'_is_deriv {x : ℝ} (h : 0 < x) : deriv fff x = fff' x :=
by refine has_deriv_at.deriv (derivative_fff h)

lemma foobar {x : ℝ} (h : 0 < x) : sqrt x * (1 / x) = 1 / sqrt x :=
begin
  have g : x = sqrt x * sqrt x, by rw mul_self_sqrt (le_of_lt h),
  calc sqrt x * (1 / x) = 1 * (sqrt x / x) : mul_div_comm _ _ _
  ... = (sqrt x / x) : one_mul _
  ... = sqrt x / (sqrt x * sqrt x) : by rw <- g
  ... = 1 / sqrt x : div_mul_right _ (ne_of_gt (sqrt_pos.2 h)),
end

lemma foobar' {x : ℝ} (h : 0 < x) : sqrt x / x = 1 / sqrt x :=
begin
  calc sqrt x / x = sqrt x * (1 / x) : by ring
  ... = 1 / sqrt x : foobar h
end

private noncomputable def aux (x : ℝ) :=
  sqrt 2 * sqrt (x + 1) * log 2 - (log (8 * (x + 1)) + 2)

private noncomputable def aux' (x : ℝ) :=
  sqrt 2 * (1 / (2 * sqrt (x + 1))) * log 2 - 8 / (8 * (x + 1))

lemma derivative_aux {x : ℝ} (hyp : x ≠ -1) : has_deriv_at (λ x, aux x) (aux' x) x :=
begin
  unfold aux,
  refine has_deriv_at.sub _ _,
  { refine has_deriv_at.mul_const _ _,
    refine has_deriv_at.const_mul _ _,
    refine has_deriv_at.sqrt _ _,
    { refine has_deriv_at.add_const _ _,
      exact has_deriv_at_id x, },
    { intro bad,
      have t : x = -1, by linarith,
      exact hyp t, }, },
  { refine has_deriv_at.add_const _ _,
    refine has_deriv_at.log _ _,
    { ring_nf,
      refine has_deriv_at.add_const _ _,
      simpa using has_deriv_at.const_mul 8 (has_deriv_at_id x), },
    { intros bad,
      have t : x = -1, by linarith,
      exact hyp t, }, },
end

lemma sqrt_log_bound : 0 < sqrt 2 * log 2 / 2 :=
begin
  refine div_pos _ (by norm_num),
    { refine mul_pos _ _,
      { exact sqrt_pos.2 (by norm_num), },
      { exact log_pos (by norm_num), },
    },
end

lemma log_pos_eq_zero {x : ℝ} (h : 0 < x) (hyp : log x = 0) : x = 1 :=
log_inj_on_pos h (mem_Ioi.mpr zero_lt_one) (trans hyp log_one.symm)

lemma log_eq_zero {x : ℝ} (hyp : log x = 0) : x = 0 ∨ x = 1 ∨ x = -1 :=
begin
  rcases lt_trichotomy x 0 with h | rfl | h,
  { refine or.inr (or.inr (eq_neg_iff_eq_neg.mp _)),
    exact (log_pos_eq_zero (neg_pos.mpr h) (trans (log_neg_eq_log x) hyp)).symm },
  { exact or.inl rfl },
  { exact or.inr (or.inl (log_pos_eq_zero h hyp)) }
end

lemma zero_pow_complex {a : ℂ} {x : ℂ} (hyp : 0 ^ x = a) : a = 0 ∨ (x = 0 ∧ a = 1) :=
begin
  unfold pow at hyp,
  unfold complex.cpow at hyp,
  simp at hyp,
  by_cases x = 0,
  { right,
    subst h,
    simp at hyp,
    cc, },
  { left,
    cc, },
end

lemma zero_pow_real {a : ℝ} {x : ℝ} (hyp : 0 ^ x = a) : a = 0 ∨ (x = 0 ∧ a = 1) :=
begin
  unfold pow at hyp,
  unfold rpow at hyp,
  simp at hyp,
  cases @zero_pow_complex _ x rfl with k_zero k_one,
  { left,
    simp [k_zero] at hyp,
    exact hyp.symm, },
  { cases k_one with x_zero a_one,
    simp [a_one] at hyp,
    right,
    exact ⟨complex.of_real_eq_zero.1 x_zero, hyp.symm⟩, },
end

lemma log_pow {x y : ℝ} (hyp : 0 < x) : log (x ^ y) = y * log x :=
log_rpow hyp y

lemma two_pow_three : (2 : ℝ) ^ (3 : ℝ) = 8 :=
begin
  calc (2 : ℝ) ^ (3 : ℝ) = (2 : ℝ) ^ ((3 : ℕ) : ℝ) : by simp
  ... = (2 : ℝ) ^ (3 : ℕ) : by rw rpow_nat_cast _ 3
  ... = 8 : by norm_num
end

lemma two_div_three_lt_log_two : (2 : ℝ) / 3 ≤ log 2 :=
begin
  rw div_le_iff,
  { suffices: 2 ≤ log 8,
      { calc (2 : ℝ) ≤ log 8 : this
        ... = log (2 ^ (3 : ℝ)) : congr_arg log two_pow_three.symm
        ... = 3 * log 2 : log_pow (by norm_num)
        ... = log 2 * 3 : mul_comm _ _, },
    suffices: exp 2 ≤ 8,
      { calc 2 = log (exp 2) : by rw log_exp
             ... ≤ log 8 : (log_le_log (exp_pos _) (by norm_num)).2 this, },
    calc exp (2 : ℝ) = exp ((1 : ℝ) * (2 : ℝ)) : by norm_num
    ... = (exp 1) ^ (2 : ℝ) : exp_mul 1 2
    ... = (exp 1) ^ (↑(2 : ℕ)) : congr_arg (λ i, (exp 1) ^ i) (by simp)
    ... = (exp 1) ^ (2 : ℕ) : by rw rpow_nat_cast (exp 1) 2
    ... ≤ (2.7182818286 : ℝ) ^ 2 : begin
      refine sq_le_sq _,
      have: 0 ≤ (13591409143 : ℝ) / 5000000000, by norm_num,
      have t: abs ((13591409143 : ℝ) / 5000000000) = (13591409143 : ℝ) / 5000000000 :=
        abs_of_nonneg this,
      rw t,
      norm_num,
      exact le_of_lt exp_one_lt_d9,
    end
    ... ≤ 8 : by norm_num, },
  { norm_num, }
end

lemma blaaahh {n : ℝ} {m : ℝ} {x : ℝ} (g : 0 < n) (u : 0 < m) (h : n / m ≤ x) : 1 ≤ m / n * x :=
begin
  rw div_mul_eq_mul_div,
  rw one_le_div g,
  rw [div_le_iff u, mul_comm] at h,
  exact h,
end

lemma aux_bound : 1 / (sqrt 2 * log 2 / 2) ^ 2 - 1 ≤ (4 : ℝ) :=
begin
  suffices : 1 / (sqrt 2 * log 2 / 2) ^ 2 ≤ 5, by linarith,
  suffices : 1 ≤ (sqrt 2 * log 2 / 2) ^ 2 * 5,
    { have pos : 0 < (sqrt 2 * log 2 / 2) ^ 2,
      { refine sq_pos_of_ne_zero _ _,
        linarith [sqrt_log_bound], },
      rw div_le_iff' pos,
      exact this, },
  suffices : 1 ≤ (sqrt 2 * (log 2 / 2)) ^ 2 * 5,
    { rw mul_div_assoc, exact this, },
  suffices : 1 ≤ (sqrt 2) ^ 2 * (log 2 / 2) ^ 2 * 5,
    { rw mul_pow, exact this, },
  suffices : 1 ≤ 2 * (log 2 / 2) ^ 2 * 5,
    { rw sq_sqrt, exact this, norm_num, },
  suffices : 1 ≤ 5 / 2 * (log 2) ^ 2,
    { ring_nf, exact this, },
  suffices : 2 / 5 ≤ (log 2) ^ 2,
    { exact blaaahh (by norm_num) (by norm_num) this, },

  have: (2 : ℝ) / 3 ≤ log 2 := two_div_three_lt_log_two,
  have t: ((2 : ℝ) / 3) ^ 2 ≤ (log 2) ^ 2,
    { rw sq_le,
      { split,
        { linarith [sqrt_nonneg (log 2 ^ 2)], },
        { rw sqrt_sq,
          exact this,
          exact log_nonneg (by norm_num), }, },
      exact sq_nonneg _, },

  calc (2 : ℝ) / 5 = 4 / 10 : by norm_num
    ... ≤ 4 / 9 : div_le_div_of_le_left (by norm_num) (by norm_num) (by norm_num)
    ... = (2 / 3) ^ 2 : by norm_num
    ... ≤ (log 2) ^ 2 : t,
end

lemma aux_derivative_ge_zero (x : ℝ) (x_big : 4 ≤ x) : 0 ≤ aux' x :=
begin
  unfold aux',

  -- Multiply through by (x + 1)
  suffices: 0 ≤ sqrt 2 * sqrt (x + 1) / 2 * log 2 - 1,
    { have h : 0 / (x + 1) ≤ (sqrt 2 * sqrt (x + 1) / 2 * log 2 - 1) / (x + 1),
      { have t : 0 < x + 1, by linarith,
        rw (div_le_div_iff t t),
        simpa using mul_nonneg this (le_of_lt t), },
      rw [zero_div, sub_div] at h,
      have eight_not_zero : (8 : ℝ) ≠ 0 := by norm_num,
      rw (div_mul_right _ eight_not_zero),
      rw mul_div_right_comm at h,
      rw [div_div_eq_div_mul, mul_comm 2 (x + 1), ←div_div_eq_div_mul, mul_div_assoc] at h,
      rw @foobar' (x + 1) (by linarith) at h,
      rw [mul_div_assoc, div_div_eq_div_mul, mul_comm (sqrt (x + 1)) 2] at h,
      exact h, },

  suffices: 1 ≤ sqrt 2 * log 2 / 2 * sqrt (x + 1), by linarith,

  suffices: 1 / (sqrt 2 * log 2 / 2) ≤ sqrt (x + 1),
    { refine (div_le_iff' _).mp this,
      exact sqrt_log_bound, },

  suffices: (1 / (sqrt 2 * log 2 / 2)) ^ 2 ≤ x + 1,
    { refine (le_sqrt _ (by linarith)).2 this,
      exact one_div_nonneg.2 (le_of_lt sqrt_log_bound), },

  suffices: (1 / (sqrt 2 * log 2 / 2)) ^ 2 - 1 ≤ x, by linarith,

  calc (1 / (sqrt 2 * log 2 / 2)) ^ 2 - 1
      = (1 ^ 2) / (sqrt 2 * log 2 / 2) ^ 2 - 1 : by rw div_pow
  ... = 1 / (sqrt 2 * log 2 / 2) ^ 2 - 1 : by norm_num
  ... ≤ (4 : ℝ) : aux_bound
  ... ≤ x : x_big,
end

lemma pow_eq_rpow (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
begin
  apply rpow_nat_cast,
end

lemma a_534_pow_100 : (584 : ℝ) ^ (100 : ℝ) = (584 : ℝ) ^ (100 : ℕ) :=
begin
  calc (584 : ℝ) ^ (100 : ℝ) = (584 : ℝ) ^ ((100 : ℕ) : ℝ) : by simp
  ... = (584 : ℝ) ^ (100 : ℕ) : by rw rpow_nat_cast _ 100,
end

lemma a_e_pow_637 : (2.71828 : ℝ) ^ (637 : ℝ) = (2.71828 : ℝ) ^ (637 : ℕ) :=
begin
  calc (2.71828) ^ (637 : ℝ) = (2.71828 : ℝ) ^ ((637 : ℕ) : ℝ) : by simp
  ... = (2.71828) ^ (637 : ℕ) : by rw rpow_nat_cast _ 637,
end


-- lemma lim_real_is_real_lim (s : cau_seq ℂ complex.abs) :
-- s.lim.re = (s.re).lim

lemma power_series_le_exp_of_nonneg (x : ℝ) (n : ℕ) (hx : 0 ≤ x) :
∑ i in finset.range n, x ^ i / i.factorial ≤ exp x
:=
begin
  sorry
end

lemma a_584_le_exp_6 : (584 : ℝ) ≤ exp (6.37 : ℝ) :=
begin
  apply trans _ (power_series_le_exp_of_nonneg 6.37 19 (by linarith)),
  simp_rw [finset.sum_range_succ],
  simp_rw [nat.factorial],
  norm_num,
end

lemma aux_zero : 0 ≤ aux 72 :=
begin
  unfold aux,
  norm_num,
  rw <-sqrt_mul,
  norm_num,
  calc log 584 + 2 ≤ 8.37 :
        begin
          apply le_sub_iff_add_le.1,
          norm_num,
          rw ←log_exp 6.37,
          apply (log_le_log _ _).2,
          exact a_584_le_exp_6,
          linarith,
          apply exp_pos,
        end
  ... ≤ sqrt 146 * log 2 :
        begin
          sorry,
        end,
  linarith,
end

lemma aux_differentiable {i : ℝ} (pr : 0 < i) : differentiable_on ℝ aux (interior (Ici i)) :=
begin
  simp only [interior_Ici],
  refine differentiable_on.sub _ _,
  { refine differentiable_on.mul_const _ _,
    refine differentiable_on.const_mul _ _,
    refine differentiable_on.sqrt _ _,
    { refine differentiable_on.add_const _ _,
      refine differentiable_on_id, },
    { intros x x_big,
      simp at x_big,
      linarith, },
  },
  { refine differentiable_on.add_const _ _,
    refine differentiable_on.log _ _,
    { refine differentiable_on.const_mul _ _,
      refine differentiable_on.add_const _ _,
      refine differentiable_on_id, },
    { intros x x_big,
      simp at x_big,
      linarith, }, },
end

lemma aux_continuous {i : ℝ} (pr : 0 < i) : continuous_on aux (Ici (i : ℝ)) :=
begin
  have e := differentiable_on.continuous_on (@aux_differentiable (i / 2) (by linarith)),
  have s : Ici i ⊆ interior (Ici (i / 2)),
    { simp only [interior_Ici],
      intro a,
      simp,
      intro a_in,
      linarith, },
  exact continuous_on.mono e s,
end

lemma aux'_is_deriv (x : ℝ) (h : x ≠ -1) : deriv aux x = aux' x :=
by refine has_deriv_at.deriv (derivative_aux h)

lemma aux_pos (x : ℝ) (x_big : 72 ≤ x) : 0 ≤ aux x :=
begin
  have conv : convex (Ici (72 : ℝ)) := convex_Ici _,
  have deriv_nonneg : ∀ (x : ℝ), x ∈ interior (Ici (72 : ℝ)) → 0 ≤ deriv aux x,
    { intros x x_big,
      simp at x_big,
      rw aux'_is_deriv x (by linarith),
      exact aux_derivative_ge_zero x (by linarith), },
  calc 0 ≤ aux 72 : aux_zero
  ... ≤ aux x :
    convex.mono_of_deriv_nonneg conv
      (aux_continuous (by norm_num)) (aux_differentiable (by norm_num))
      deriv_nonneg
      72 x (by simp) (by simpa using x_big) x_big,
end

lemma deriv_nonneg {x : ℝ} (x_big : 72 ≤ x) : 0 ≤ fff' x :=
begin
  unfold fff',
  have r : 8 * x + 8 = 8 * (x + 1), by ring,
  rw r,
  simp only [zero_le_one, sqrt_mul, zero_le_bit0],
  have eight_not_zero : (8 : ℝ) ≠ 0 := by norm_num,
  have frac_simp: 8 / (8 * (x + 1)) = 1 / (x + 1), by rw div_mul_right _ eight_not_zero,
  rw frac_simp,
  rw mul_assoc (sqrt 8) (sqrt (x + 1)) (1 / (x + 1)),
  have g : sqrt 8 = 2 * sqrt 2,
    { have g : sqrt 8 = sqrt ((2 * 2) * 2), by norm_num,
      rw g,
      simp, },
  have eight_simp : 8 / (2 * (sqrt 8 * sqrt (x + 1))) = (2 / sqrt 2) * (1 / sqrt (x + 1)),
    { rw <- mul_assoc 2 (sqrt 8) (sqrt (x + 1)),
      rw div_mul_eq_div_mul_one_div,
      suffices : 8 / (2 * sqrt 8) = 2 / sqrt 2, by rw this,
      rw g,
      rw div_mul_eq_div_mul_one_div,
      norm_num,
      rw div_mul_eq_div_mul_one_div,
      rw <- mul_assoc,
      norm_num,
      rw mul_div_comm,
      norm_num, },

  rw eight_simp, clear eight_simp,
  rw g,
  rw @foobar (x + 1) (by linarith),

  have h132 : 0 ≤ 1 / sqrt (x + 1),
    {
      apply div_nonneg,
      linarith,
      apply sqrt_nonneg,
    },

  have h133 : sqrt (x + 1) ≠ 0,
    {
      apply ne_of_gt,
      apply sqrt_pos.2,
      linarith,
    },

  have h134 : 0 ≤ 1 / sqrt 2,
    apply div_nonneg,
    linarith,
    apply sqrt_nonneg,

  -- Multiply through by sqrt (x + 1)
  suffices: 0 ≤ sqrt (x + 1) * log 4 - (2 / sqrt 2 * log (8 * (x + 1)) + 2 * sqrt 2),
    { have h1322 := mul_nonneg h132 this ,
      rw mul_sub at h1322,
      convert h1322,
      simp only [one_div],
      rw <-mul_assoc,
      rw inv_mul_cancel h133,
      simp,
      rw mul_add (1 / sqrt (x+1)),
      ring,
    },

  -- Multiply through by sqrt 2
  suffices: 0 ≤ sqrt 2 * sqrt (x + 1) * log 4 - (2 * log (8 * (x + 1)) + 4),
    {
      have h1342 := mul_nonneg h134 this ,
      convert h1342,
      rw mul_sub,
      apply congr_arg2,
      rw <-mul_assoc,
      rw <-mul_assoc,
      simp,
      rw mul_add (1 / sqrt 2),
      apply congr_arg2,
      rw <-mul_assoc,
      rw mul_comm,
      simp,
      rw mul_comm,
      simp,
      left,
      rw mul_comm,
      rw <-division_def,
      -- simp,
      exact (@div_sqrt 2).symm,
      have h21312 : (4 : ℝ) = 2 * 2,
        norm_num,
      rw h21312,
      conv
      begin
        to_rhs,
        rw mul_comm,
        rw mul_assoc,
        congr,
        skip,
        simp,
        rw <-division_def,
        rw (@div_sqrt 2),
      end,


    },

  suffices: 0 ≤ sqrt 2 * sqrt (x + 1) * (2 * log 2) - 2 * (log (8 * (x + 1)) + 2),
    { convert this,
      rw <-log_rpow,
      congr,
      apply symm,
      calc (2 : ℝ) ^ (2 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) : by simp
      ... = (2 : ℝ) ^ (2 : ℕ) : by rw rpow_nat_cast _ 2
      ... = 4 : by norm_num,
      linarith,
      rw mul_add 2 (log (8 * (x + 1))) 2,
      norm_num,
    },

  suffices: 0 ≤ sqrt 2 * sqrt (x + 1) * log 2 - (log (8 * (x + 1)) + 2),
    { rw <-mul_assoc,
      rw mul_comm _ (2 : ℝ),
      rw mul_assoc,
      rw <-mul_sub,
      apply mul_nonneg,
      norm_num,
      exact this,
    },

  -- Then easy to show it's positive, by taking the derivative.
  exact aux_pos x x_big,
end

lemma fff_differentiable {i : ℝ} (pr : 0 < i) : differentiable_on ℝ fff (interior (Ici i)) :=
begin
  have d : differentiable_on ℝ (λ (x : ℝ), 8 * x + 8) (interior (Ici i)),
    { refine differentiable_on.add_const _ _,
      refine differentiable_on.const_mul _ _,
      refine differentiable_on_id, },
  refine differentiable_on.sub _ _,
  { refine differentiable_on.mul_const _ _,
    refine differentiable_on_id, },
  { refine differentiable_on.mul _ _,
    { refine differentiable_on.comp _ _ _,
      { exact Ici i, },
      { refine differentiable_on.sqrt _ _,
        { refine differentiable_on_id, },
        { intros x,
          simp only [mem_Ici, ne.def],
          intros x_in,
          linarith, }, },
      { exact d, },
      { intro x,
        simp only [interior_Ici, mem_Ici, mem_Ioi, mem_preimage],
        intros x_big,
        calc i ≤ x : le_of_lt x_big
        ... ≤ 8 * x + 8 : by linarith,
      }, },
    { refine differentiable_on.log _ _,
      { exact d, },
      { intros x,
        simp only [interior_Ici, mem_Ioi, ne.def],
        intros x_big,
        linarith, }, }, },
end

lemma fff_continuous {i : ℝ} (pr : 0 < i) : continuous_on fff (Ici (i : ℝ)) :=
begin
  have e := differentiable_on.continuous_on (@fff_differentiable (i / 2) (by linarith)),
  have s : Ici i ⊆ interior (Ici (i / 2)),
    { simp only [interior_Ici],
      intro a,
      simp,
      intro a_in,
      linarith, },
  exact continuous_on.mono e s,
end

lemma sqrt_four : sqrt 4 = 2 :=
begin
  calc sqrt 4 = sqrt (2 * 2) : by norm_num
  ... = 2 : sqrt_mul_self (by linarith)
end


lemma pow_inequality_2008' : (2008 : ℝ) ^ (9 : ℝ) ≤ (4 : ℝ) ^ (50 : ℝ) :=
begin
  calc  (2008 : ℝ) ^ (9 : ℝ)
      = (2008 : ℝ) ^ ((9 : ℕ) : ℝ) : by simp
  ... = (2008 : ℝ) ^ (9 : ℕ) : by rw rpow_nat_cast _ 9
  ... = (530729681093308751060012105728 : ℝ) :
        begin
          norm_num,
        end
  ... ≤ (1267650600228229401496703205376 : ℝ) : by norm_num
  ... = (4 : ℝ) ^ (50 : ℕ) : by norm_num
  ... = (4 : ℝ) ^ ((50 : ℕ) : ℝ) : by rw rpow_nat_cast _ 50
  ... = (4 : ℝ) ^ (50 : ℝ) : by simp,
end



lemma eleven_sqrt_five_hundred_two : (11 : ℝ) * sqrt 502 ≤ 250 :=
begin
  have eleven_nonneg : (0 : ℝ) ≤ 11 := by norm_num,
  have t : (11 : ℝ) * sqrt 502 = sqrt (121 * 502),
    { calc (11 : ℝ) * sqrt 502 = sqrt (11 ^ 2) * sqrt 502 : by rw sqrt_sq eleven_nonneg
      ... = sqrt 121 * sqrt 502 : by norm_num
      ... = sqrt (121 * 502) : (sqrt_mul (by norm_num) _).symm, },
  have two_fifty_pos : (0 : ℝ) ≤ 250 := by norm_num,
  have u : 250 = sqrt 62500,
    calc 250 = sqrt (250 ^ 2) : by rw sqrt_sq two_fifty_pos
      ... = sqrt 62500 : by norm_num,
  rw [t, u],
  apply sqrt_le_sqrt,
  norm_num,
end

lemma fff_250 : 0 ≤ fff 250 :=
begin
  unfold fff,
  norm_num,
  have r : 11 * sqrt 502 < 250,
    { have s : (11 * sqrt 502) ^ 2 < 250 ^ 2,
      { calc (11 * sqrt 502) ^ 2 = 11 ^ 2 * (sqrt 502) ^ 2 : by rw mul_pow
        ... = 121 * (sqrt 502) ^ 2 : by norm_num
        ... = 121 * (sqrt 502) ^ (2 : ℕ) : by simp
        ... = 121 * ((sqrt 502) * (sqrt 502)) : by ring_exp
        ... = 121 * 502 : by rw @mul_self_sqrt 502 (by norm_num)
        ... = 60742 : by norm_num
        ... < 250 ^ 2 : by norm_num, },
      have e := abs_lt_of_sq_lt_sq s (by norm_num),
      have u : 0 < 11 * sqrt 502, by norm_num,
      have v : abs (11 * sqrt 502) = 11 * sqrt 502 := abs_of_pos u,
      rw abs_of_pos u at e,
      exact e, },

  have eight_pow : (8 : ℝ) = 2 ^ 3 := by norm_num,
  have two_fifty_six_pow : (256 : ℝ) = 2 ^ 8 := by norm_num,

  have r : log 251 ≤ log 256 := (@log_le_log 251 256 (by norm_num) (by norm_num)).2 (by norm_num),

  have two_pos: 0 < (2 : ℝ) := by norm_num,

    calc sqrt 2008 * log 2008
      ≤ 45 * log 2008 :
            begin
              apply (mul_le_mul_right _).2,
              apply (sqrt_le_left _).2,
              norm_num,
              norm_num,
              apply log_pos,
              norm_num,
            end
  ... = log (2008 ^ (45 : ℝ)) :
            begin
              rw log_rpow,
              norm_num,
            end
  ... ≤ log (4 ^ (250 : ℝ)) :
            begin
              apply (log_le_log _ _).2,
              -- apply rpow_pos_of_pos,
              -- norm_num,
              apply (@rpow_le_rpow_iff _ _ (1/5) _ _ _).1,
              rw <-rpow_mul,
              rw <-rpow_mul,
              norm_num,
              -- norm_num,
              exact pow_inequality_2008',
              norm_num,
              norm_num,
              apply rpow_nonneg_of_nonneg,
              norm_num,
              apply rpow_nonneg_of_nonneg,
              norm_num,
              norm_num,
              apply rpow_pos_of_pos,
              norm_num,
              apply rpow_pos_of_pos,
              norm_num,
            end
  ... = 250 * log 4 :
            begin
              rw log_rpow,
              norm_num,
            end
end

lemma linear_dominates_sqrt_log (x : ℝ) (hx : 250 ≤ x)
  : sqrt (8 * x + 8) * log (8 * x + 8) ≤ x * log 4 :=
begin
  suffices: 0 ≤ fff x,
    { unfold fff at this,
      simpa using this, },
  have conv : convex (Ici (250 : ℝ)) := convex_Ici _,
  have t : ∀ (x : ℝ), x ∈ interior (Ici (250 : ℝ)) → 0 ≤ deriv fff x,
    { intros x x_in_interior,
      have x_big : 250 < x, by simpa using x_in_interior,
      rw @fff'_is_deriv x (by linarith),
      exact deriv_nonneg (by linarith), },
  calc 0 ≤ fff 250 : fff_250
  ... ≤ fff x :
    convex.mono_of_deriv_nonneg conv
      (fff_continuous (by linarith)) (fff_differentiable (by linarith))
      t
      250 x (by simp) (by simpa using hx)
      hx,
end

lemma pow_beats_pow_2 (n : ℕ) (n_large : 250 ≤ n) : (8 * n + 8) ^ nat.sqrt (8 * n + 8) ≤ 4 ^ n :=
begin
  apply (@nat.cast_le ℝ _ _ _ _).1,
  calc ↑((8 * n + 8) ^ nat.sqrt (8 * n + 8))
      ≤ (↑(8 * n + 8) ^ real.sqrt (↑(8 * n + 8))) :
          begin
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
            },
            { norm_num,
              refine rpow_pos_of_pos _ _,
              { norm_cast,
                linarith,},
            },
          end,
end

lemma power_conversion_2 (n : ℕ) (n_large : 1003 < n) : (2 * n) ^ nat.sqrt (2 * n) ≤ 4 ^ (n / 4) :=
begin
  have : 250 ≤ n / 4,
    { cases le_or_gt 250 (n / 4),
      { exact h, },
      { have r : n < n :=
          calc n = 4 * (n / 4) + (n % 4) : (nat.div_add_mod n 4).symm
            ... < 4 * 250 + (n % 4) : add_lt_add_right ((mul_lt_mul_left (nat.succ_pos 3)).2 h) _
            ... < 4 * 250 + 4 : add_lt_add_left (nat.mod_lt n (by linarith)) _
            ... = 1004 : by norm_num
            ... ≤ n : by linarith,
        exfalso,
        exact lt_irrefl _ r, }, },
  have rem_small : (n % 4) < 4 := nat.mod_lt n (nat.succ_pos 3),
  calc (2 * n) ^ nat.sqrt (2 * n) = (2 * (4 * (n / 4) + (n % 4))) ^ nat.sqrt (2 * (4 * (n / 4) + (n % 4))) : by rw nat.div_add_mod n 4
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
                apply nat.le_sqrt.2,
                suffices : 1 * 1 ≤ 8,
                  exact le_add_left this,
                norm_num,
              end
  ... ≤ 4 ^ (n / 4) : pow_beats_pow_2 (n / 4) (by linarith),
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


lemma false_inequality_is_false {n : ℕ} (n_large : 1003 < n) : 4 ^ n < (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1) → false :=
begin
  rw imp_false,
  rw not_lt,
  calc (2 * n + 1) * (2 * n) ^ nat.sqrt (2 * n) * 4 ^ (2 * n / 3 + 1)
       ≤ (4 ^ (n / 15)) * (2 * n) ^ nat.sqrt (2 * n) * 4 ^ (2 * n / 3 + 1) :
          begin
            apply (nat.mul_le_mul_right (4 ^ (2 * n / 3 + 1))),
            apply (nat.mul_le_mul_right ((2 * n) ^ nat.sqrt (2 * n))),
            apply power_conversion_1,
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

lemma more_restrictive_filter_means_smaller_subset {a : _} {S : finset a} {f : _} {g : _} [decidable_pred f] [decidable_pred g] (p : ∀ i, f i → g i): finset.filter f S ⊆ finset.filter g S :=
begin
  intros h prop,
  simp only [finset.mem_filter] at prop,
  simp only [finset.mem_filter],
  exact ⟨prop.1, p h prop.2⟩,
end

lemma filter_to_subset {a : _} {S : finset a} {T : finset a} {p : _} [decidable_pred p] (prop : ∀ i, p i → i ∈ T)
  : finset.filter p S ⊆ T :=
begin
  suffices : ∀ x, x ∈ finset.filter p S → x ∈ T, by exact finset.subset_iff.mpr this,
  intros x hyp,
  simp only [finset.mem_filter] at hyp,
  exact prop x hyp.2
end

lemma foo {n : ℕ} : (finset.filter (λ (p : ℕ), p ^ 2 < 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1)))).card ≤ nat.sqrt (2 * n) :=
begin
  have t : ∀ p, p ^ 2 ≤ 2 * n ↔ p ≤ nat.sqrt (2 * n),
  { intro p,
    exact nat.le_sqrt'.symm, },

  have u : ∀ p, (p ^ 2 < 2 * n) → p ^ 2 ≤ 2 * n, by
  { intros p hyp,
    exact le_of_lt hyp, },

  have v : finset.filter (λ p, p ^ 2 < 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1))) ⊆
    finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1))) :=
    more_restrictive_filter_means_smaller_subset u,

  have w' : finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1))) =
    finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 0 (2 * n / 3 + 1))) :=
    by {
      apply congr_arg (λ i, finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime i)),
      exact finset.range_eq_Ico (2 * n / 3 + 1),
    },

  have w : finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 0 (2 * n / 3 + 1))) =
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

  have g : finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1))) =
    finset.filter (λ p, 2 ≤ p ^ 2 ∧ p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1))),
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

  have h : (finset.filter (λ p, 2 ≤ p ^ 2 ∧ p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1)))) ⊆ finset.Ico 2 (nat.sqrt (2 * n) + 1)
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

  calc (finset.filter (λ (p : ℕ), p ^ 2 < 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1)))).card
      ≤ (finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1)))).card: finset.card_le_of_subset v
  ... = (finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 0 (2 * n / 3 + 1)))).card: congr_arg finset.card w'
  ... = (finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1)))).card: congr_arg finset.card w
  ... = (finset.filter (λ p, 2 ≤ p ^ 2 ∧ p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1)))).card: congr_arg finset.card g
  ... ≤ (finset.Ico 2 (nat.sqrt (2 * n) + 1)).card: finset.card_le_of_subset h
  ... = nat.sqrt (2 * n) + 1 - 2: finset.Ico.card 2 (nat.sqrt (2 * n) + 1)
  ... = nat.sqrt (2 * n) - 1: by ring
  ... ≤ nat.sqrt (2 * n): (nat.sqrt (2 * n)).sub_le 1,

end

lemma bertrand_eventually (n : nat) (n_big : 1003 < n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
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

    have binom_inequality : (2 * n).choose n < (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1), by
      calc (2 * n).choose n
              = (∏ p in finset.filter nat.prime (finset.range ((2 * n).choose n + 1)),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                      : (central_binom_factorization n).symm
      ...     = (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                      : central_binom_factorization_small.symm
      ...     = (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   if p ^ 2 ≤ 2 * n then p ^ (padic_val_nat p ((2 * n).choose n)) else p ^ (padic_val_nat p ((2 * n).choose n)))
                       : by simp only [if_t_t]
      ...     = (∏ p in finset.filter (λ p, p ^ 2 ≤ 2 * n)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                    p ^ (padic_val_nat p ((2 * n).choose n)))
                 *
                (∏ p in finset.filter (λ p, ¬p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1))),
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
                    { refine finset.prod_pos _,
                      intros p hyp,
                      simp only [finset.mem_filter, finset.mem_range] at hyp,
                      exact pow_pos (nat.prime.pos hyp.1.2) (padic_val_nat p ((2 * n).choose n)), },
                    { refine congr_arg (λ i, (2 * n) ^ i) _,
                      refine congr_arg (λ s, finset.card s) _,
                      ext1,
                      split,
                      { intro h, simp at h, simp, split, exact h.1, exact even_prime_is_small h.1.2 (by linarith) h.2, },
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
                          { exact @claim_2 i (fact_iff.2 i_facts.2) n (by linarith) sqrt_two_n_lt_i, }, },
                     end
      ...     ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   p ^ 1)
                     : begin
                       refine nat.mul_le_mul_left _ _,
                       refine finset.prod_le_prod_of_subset_of_one_le' (finset.filter_subset _ _) _,
                        { intros i hyp1 hyp2,
                        cases le_or_gt 1 i,
                        { ring_nf, exact h, },
                        { have i_zero : i = 0, by linarith,
                          simp only [i_zero, true_and, nat.succ_pos', finset.mem_filter, finset.mem_range] at hyp1,
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
                : (mul_lt_mul_left (pow_pos (by linarith) _)).mpr (pow_lt_pow (by simp only [nat.succ_pos', nat.one_lt_bit0_iff, nat.one_le_bit0_iff]) (by simp only [nat.succ_pos', lt_add_iff_pos_right])),

    have false_inequality : 4 ^ n < (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1), by
      calc 4 ^ n ≤ (2 * n + 1) * (2 * n).choose n : central_binom_lower_bound n
        ...      < (2 * n + 1) * ((2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1))
                    : nat.mul_lt_mul_of_pos_left binom_inequality (by linarith)
        ...      = (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1) : by ring,

    exfalso,
    exact false_inequality_is_false n_big false_inequality,
end

theorem bertrand (n : nat) (n_pos : 0 < n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
cases lt_or_le 1003 n,
{exact bertrand_eventually n h},

cases le_or_lt 505 n,
{ use 1009, norm_num, split, linarith, linarith, },
clear h,

cases le_or_lt 376 n,
{ use 751, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 274 n,
{ use 547, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 139 n,
{ use 277, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 70 n,
{ use 139, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 37 n,
{ use 73, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 19 n,
{ use 37, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 11 n,
{ use 19, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 6 n,
{ use 11, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 4 n,
{ use 7, norm_num, split, linarith, linarith, },
clear h,
interval_cases n,
{ use 2, norm_num },
{ use 3, norm_num },
{ use 5, norm_num },
end
