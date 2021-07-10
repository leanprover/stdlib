/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import number_theory.arithmetic_function
import number_theory.lucas_lehmer
import algebra.geom_sum
import ring_theory.multiplicity

/-!
# Perfect Numbers

This file proves Theorem 70 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The theorem characterizes even perfect numbers.

Euclid proved that if `2 ^ (k + 1) - 1` is prime (these primes are known as Mersenne primes),
  then `2 ^ k * 2 ^ (k + 1) - 1` is perfect.

Euler proved the converse, that if `n` is even and perfect, then there exists `k` such that
  `n = 2 ^ k * 2 ^ (k + 1) - 1` and `2 ^ (k + 1) - 1` is prime.

## References
https://en.wikipedia.org/wiki/Euclid%E2%80%93Euler_theorem
-/

lemma odd_mersenne_succ (k : ℕ) : ¬ 2 ∣ mersenne (k + 1) :=
by simp [← even_iff_two_dvd, ← nat.even_succ, nat.succ_eq_add_one] with parity_simps

namespace nat
open arithmetic_function finset
open_locale arithmetic_function

lemma sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) :=
by simpa [mersenne, prime_two, ← geom_sum_mul_add 1 (k+1)]


/-- Euclid's theorem that Mersenne primes induce perfect numbers -/
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).prime) :
  perfect ((2 ^ k) * mersenne (k + 1)) :=
begin
  rw [perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ, ← sigma_one_apply, mul_comm,
    is_multiplicative_sigma.map_mul_of_coprime
        (nat.prime_two.coprime_pow_of_not_dvd (odd_mersenne_succ _)),
    sigma_two_pow_eq_mersenne_succ],
  { simp [pr, nat.prime_two] },
  { apply mul_pos (pow_pos _ k) (mersenne_pos (nat.succ_pos k)),
    norm_num }
end

lemma ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).prime) :
  k ≠ 0 :=
begin
  rintro rfl,
  simpa [mersenne, not_prime_one] using pr,
end

theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).prime) :
  even ((2 ^ k) * mersenne (k + 1)) :=
by simp [ne_zero_of_prime_mersenne k pr] with parity_simps

lemma eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) :
  ∃ (k m : ℕ), n = 2 ^ k * m ∧ ¬ even m :=
begin
  have h := (multiplicity.finite_nat_iff.2 ⟨nat.prime_two.ne_one, hpos⟩),
  cases multiplicity.pow_multiplicity_dvd h with m hm,
  use [(multiplicity 2 n).get h, m],
  refine ⟨hm, _⟩,
  rw even_iff_two_dvd,
  have hg := multiplicity.is_greatest' h (nat.lt_succ_self _),
  contrapose! hg,
  rcases hg with ⟨k, rfl⟩,
  apply dvd.intro k,
  rw [pow_succ', mul_assoc, ← hm],
end

/-- **Perfect Number Theorem**: Euler's theorem that even perfect numbers can be factored as a
  power of two times a Mersenne prime. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : even n) (perf : perfect n) :
  ∃ (k : ℕ), prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) :=
begin
  have hpos := perf.2,
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩,
  use k,
  rw [perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    is_multiplicative_sigma.map_mul_of_coprime (nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ] at perf,
  rcases nat.coprime.dvd_of_dvd_mul_left
    (nat.prime_two.coprime_pow_of_not_dvd (odd_mersenne_succ _)) (dvd.intro _ perf) with ⟨j, rfl⟩,
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf,
  have h := mul_left_cancel' (ne_of_gt (mersenne_pos (nat.succ_pos _))) perf,
  rw [sigma_one_apply, sum_divisors_eq_sum_proper_divisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h,
  have hj := add_left_cancel h,
  cases sum_proper_divisors_dvd (by { rw hj, apply dvd.intro_left (mersenne (k + 1)) rfl }),
  { have j1 : j = 1 := eq.trans hj.symm h_1,
    rw [j1, mul_one, sum_proper_divisors_eq_one_iff_prime] at h_1,
    simp [h_1, j1] },
  { have jcon := eq.trans hj.symm h_1,
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon,
    have jcon2 := mul_right_cancel' _ jcon,
    { exfalso,
      cases k,
      { apply hm,
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev,
        rw [← jcon2, one_mul],
        exact ev },
      apply ne_of_lt _ jcon2,
      rw [mersenne, ← nat.pred_eq_sub_one, lt_pred_iff, ← pow_one (nat.succ 1)],
      apply pow_lt_pow (nat.lt_succ_self 1) (nat.succ_lt_succ (nat.succ_pos k)) },
    contrapose! hm,
    simp [hm] }
end

/-- The Euclid-Euler theorem characterizing even perfect numbers -/
theorem even_and_perfect_iff {n : ℕ} :
  (even n ∧ perfect n) ↔ ∃ (k : ℕ), prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) :=
begin
  split,
  { rintro ⟨ev, perf⟩,
    exact eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf },
  { rintro ⟨k, pr, rfl⟩,
    exact ⟨even_two_pow_mul_mersenne_of_prime k pr, perfect_two_pow_mul_mersenne_of_prime k pr⟩ }
end

end nat
