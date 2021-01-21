/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.nat.bitwise
import data.nat.parity
import ring_theory.int.basic

/-!

# Natural number multiplicity

This file contains lemmas about the multiplicity function (the maximum prime power divding a number).

# Main results

There are natural number versions of some basic lemmas about multiplicity.

There are also lemmas about the multiplicity of primes in factorials and in binomial coefficients.
-/

open finset nat multiplicity
open_locale big_operators nat

namespace nat

/-- The multiplicity of a divisor `m` of `n`, is the cardinality of the set of
  positive natural numbers `i` such that `p ^ i` divides `n`. The set is expressed
  by filtering `Ico 1 b` where `b` is any bound at least `n` -/
lemma multiplicity_eq_card_pow_dvd {m n b : ℕ} (hm1 : m ≠ 1) (hn0 : 0 < n) (hb : n ≤ b):
  multiplicity m n = ↑((finset.Ico 1 b).filter (λ i, m ^ i ∣ n)).card :=
calc multiplicity m n = ↑(Ico 1 $ ((multiplicity m n).get (finite_nat_iff.2 ⟨hm1, hn0⟩) + 1)).card :
  by simp
... = ↑((finset.Ico 1 b).filter (λ i, m ^ i ∣ n)).card : congr_arg coe $ congr_arg card $
  finset.ext $ λ i,
  have hmn : ¬ m ^ n ∣ n,
    from if hm0 : m = 0
    then λ _, by cases n; simp [*, lt_irrefl, pow_succ'] at *
    else mt (le_of_dvd hn0) (not_le_of_gt $ lt_pow_self
      (lt_of_le_of_ne (nat.pos_of_ne_zero hm0) hm1.symm) _),
  ⟨λ hi, begin
      simp only [Ico.mem, mem_filter, lt_succ_iff] at *,
      exact ⟨⟨hi.1, lt_of_le_of_lt hi.2 $
        lt_of_lt_of_le (by rw [← enat.coe_lt_coe, enat.coe_get,
            multiplicity_lt_iff_neg_dvd]; exact hmn)
          hb⟩,
        by rw [pow_dvd_iff_le_multiplicity];
          rw [← @enat.coe_le_coe i, enat.coe_get] at hi; exact hi.2⟩
    end,
  begin
    simp only [Ico.mem, mem_filter, lt_succ_iff, and_imp, true_and] { contextual := tt },
    assume h1i hib hmin,
    rwa [← enat.coe_le_coe, enat.coe_get, ← pow_dvd_iff_le_multiplicity]
  end⟩

namespace prime

lemma multiplicity_one {p : ℕ} (hp : p.prime) : multiplicity p 1 = 0 :=
multiplicity.one_right (prime_iff_prime.mp hp).not_unit

lemma multiplicity_mul {p m n : ℕ} (hp : p.prime) :
  multiplicity p (m * n) = multiplicity p m + multiplicity p n :=
multiplicity.mul $ prime_iff_prime.mp hp

lemma multiplicity_pow {p m n : ℕ} (hp : p.prime) :
  multiplicity p (m ^ n) = n •ℕ (multiplicity p m) :=
multiplicity.pow $ prime_iff_prime.mp hp

lemma multiplicity_self {p : ℕ} (hp : p.prime) : multiplicity p p = 1 :=
multiplicity_self (prime_iff_prime.mp hp).not_unit hp.ne_zero

lemma multiplicity_pow_self {p n : ℕ} (hp : p.prime) : multiplicity p (p ^ n) = n :=
multiplicity_pow_self hp.ne_zero (prime_iff_prime.mp hp).not_unit n

/-- The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`.
  This sum is expressed over the set `Ico 1 b` where `b` is any bound at least `n` -/
lemma multiplicity_factorial {p : ℕ} (hp : p.prime) :
  ∀ {n b : ℕ}, n ≤ b → multiplicity p n! = (∑ i in Ico 1 b, n / p ^ i : ℕ)
| 0     b hb := by simp [Ico, hp.multiplicity_one]
| (n+1) b hb :=
  calc multiplicity p (n+1)! = multiplicity p n! + multiplicity p (n+1) :
    by rw [factorial_succ, hp.multiplicity_mul, add_comm]
  ... = (∑ i in Ico 1 b, n / p ^ i : ℕ) + ((finset.Ico 1 b).filter (λ i, p ^ i ∣ n+1)).card :
    by rw [multiplicity_factorial (le_of_succ_le hb),
      ← multiplicity_eq_card_pow_dvd (ne_of_gt hp.one_lt) (succ_pos _) hb]
  ... = (∑ i in Ico 1 b, (n / p ^ i + if p^i ∣ n+1 then 1 else 0) : ℕ) :
    by rw [sum_add_distrib, sum_boole]; simp
  ... = (∑ i in Ico 1 b, (n + 1) / p ^ i : ℕ) :
    congr_arg coe $ finset.sum_congr rfl (by intros; simp [nat.succ_div]; congr)

/-- The multiplicity of `p` in `(p(n+1))!` is one more than the sum
  of the multiplicities of `p` in `(p * n)!` and `n + 1`. -/
lemma multiplicity_factorial_mul_succ {n p : ℕ} (hp : p.prime) :
  multiplicity p (p * (n + 1))! = multiplicity p (p * n)! + multiplicity p (n + 1) + 1 :=
begin
  have hp' := prime_iff_prime.mp hp,
  have h0 : 2 ≤ p := hp.two_le,
  have h1 : 1 ≤ p * n + 1 := le_add_left _ _,
  have h2 : p * n + 1 ≤ p * (n + 1), linarith,
  have h3 : p * n + 1 ≤ p * (n + 1) + 1, linarith,
  have hm : multiplicity p (p * n)! ≠ ⊤,
  { rw [ne.def, eq_top_iff_not_finite, not_not, finite_nat_iff],
    exact ⟨hp.ne_one, factorial_pos _⟩ },
  revert hm,
  have h4 : ∀ m ∈ Ico (p * n + 1) (p * (n + 1)), multiplicity p m = 0,
  { intros m hm, apply multiplicity_eq_zero_of_not_dvd,
    rw [← exists_lt_and_lt_iff_not_dvd _ (pos_iff_ne_zero.mpr hp.ne_zero)], rw [Ico.mem] at hm,
    exact ⟨n, lt_of_succ_le hm.1, hm.2⟩ },
  simp_rw [← prod_Ico_id_eq_factorial, multiplicity.finset.prod hp', ← sum_Ico_consecutive _ h1 h3,
    add_assoc], intro h,
  rw [enat.add_left_cancel_iff h, sum_Ico_succ_top h2, multiplicity.mul hp',
    hp.multiplicity_self, sum_congr rfl h4, sum_const_zero, zero_add,
    add_comm (1 : enat)]
end

/-- The multiplicity of `p` in `(pn)!` is `n` more than that of `n!`. -/
lemma multiplicity_factorial_mul {n p : ℕ} (hp : p.prime) :
  multiplicity p (p * n)! = multiplicity p n! + n :=
begin
  induction n with n ih,
  { simp },
  { simp [succ_eq_add_one, multiplicity.mul, hp, prime_iff_prime.mp hp, ih,
      multiplicity_factorial_mul_succ, add_assoc, add_left_comm] }
end

/-- A prime power divides `n!` iff it is at most the sum of the quotients `n / p ^ i`.
  This sum is expressed over the set `Ico 1 b` where `b` is any bound at least `n` -/
lemma pow_dvd_factorial_iff {p : ℕ} {n r b : ℕ} (hp : p.prime) (hbn : n ≤ b) :
   p ^ r ∣ n! ↔ r ≤ ∑ i in Ico 1 b, n / p ^ i :=
by rw [← enat.coe_le_coe, ← hp.multiplicity_factorial hbn, ← pow_dvd_iff_le_multiplicity]

lemma multiplicity_choose_aux {p n b k : ℕ} (hp : p.prime) (hkn : k ≤ n) :
  ∑ i in finset.Ico 1 b, n / p ^ i =
  ∑ i in finset.Ico 1 b, k / p ^ i + ∑ i in finset.Ico 1 b, (n - k) / p ^ i +
  ((finset.Ico 1 b).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card :=
calc ∑ i in finset.Ico 1 b, n / p ^ i
    = ∑ i in finset.Ico 1 b, (k + (n - k)) / p ^ i :
    by simp only [nat.add_sub_cancel' hkn]
... = ∑ i in finset.Ico 1 b, (k / p ^ i + (n - k) / p ^ i +
      if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0) : by simp only [nat.add_div (pow_pos hp.pos _)]
... = _ : begin simp only [sum_add_distrib], simp [sum_boole], end -- we have to use `sum_add_distrib` before `add_ite` fires.

/-- The multiplity of `p` in `choose n k` is the number of carries when `k` and `n - k`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound at least `n`. -/
lemma multiplicity_choose {p n k b : ℕ} (hp : p.prime) (hkn : k ≤ n) (hnb : n ≤ b) :
  multiplicity p (choose n k) =
  ((Ico 1 b).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card :=
have h₁ : multiplicity p (choose n k) + multiplicity p (k! * (n - k)!) =
    ((finset.Ico 1 b).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card +
    multiplicity p (k! * (n - k)!),
  begin
    rw [← hp.multiplicity_mul, ← mul_assoc, choose_mul_factorial_mul_factorial hkn,
        hp.multiplicity_factorial hnb, hp.multiplicity_mul,
        hp.multiplicity_factorial (le_trans hkn hnb),
        hp.multiplicity_factorial (le_trans (nat.sub_le_self _ _) hnb),
        multiplicity_choose_aux hp hkn],
    simp [add_comm],
  end,
(enat.add_right_cancel_iff
  (enat.ne_top_iff_dom.2 $
    by exact finite_nat_iff.2 ⟨ne_of_gt hp.one_lt, mul_pos (factorial_pos k) (factorial_pos (n - k))⟩)).1
  h₁

/-- A lower bound on the multiplicity of `p` in `choose n k`. -/
lemma multiplicity_le_multiplicity_choose_add {p : ℕ} (hp : p.prime) (n k : ℕ) :
  multiplicity p n ≤ multiplicity p (choose n k) + multiplicity p k :=
if hkn : n < k then by simp [choose_eq_zero_of_lt hkn]
else if hk0 : k = 0 then by simp [hk0]
else if hn0 : n = 0 then by cases k; simp [hn0, *] at *
else begin
  rw [multiplicity_choose hp (le_of_not_gt hkn) (le_refl _),
    multiplicity_eq_card_pow_dvd (ne_of_gt hp.one_lt) (nat.pos_of_ne_zero hk0) (le_of_not_gt hkn),
    multiplicity_eq_card_pow_dvd (ne_of_gt hp.one_lt) (nat.pos_of_ne_zero hn0) (le_refl _),
    ← enat.coe_add, enat.coe_le_coe],
  calc ((Ico 1 n).filter (λ i, p ^ i ∣ n)).card
      ≤ ((Ico 1 n).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i) ∪
        (Ico 1 n).filter (λ i, p ^ i ∣ k) ).card :
    card_le_of_subset $ λ i, begin
      have := @le_mod_add_mod_of_dvd_add_of_not_dvd k (n - k) (p ^ i),
      simp [nat.add_sub_cancel' (le_of_not_gt hkn)] at * {contextual := tt},
      tauto
    end
  ... ≤ ((Ico 1 n).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card +
        ((Ico 1 n).filter (λ i, p ^ i ∣ k)).card :
    card_union_le _ _
end

lemma multiplicity_choose_prime_pow {p n k : ℕ} (hp : p.prime)
  (hkn : k ≤ p ^ n) (hk0 : 0 < k) :
  multiplicity p (choose (p ^ n) k) + multiplicity p k = n :=
le_antisymm
  (have hdisj : disjoint
      ((Ico 1 (p ^ n)).filter (λ i, p ^ i ≤ k % p ^ i + (p ^ n - k) % p ^ i))
      ((Ico 1 (p ^ n)).filter (λ i, p ^ i ∣ k)),
    by simp [disjoint_right, *, dvd_iff_mod_eq_zero, nat.mod_lt _ (pow_pos hp.pos _)]
        {contextual := tt},
  have filter_subset_Ico : filter (λ i, p ^ i ≤ k % p ^ i +
      (p ^ n - k) % p ^ i ∨ p ^ i ∣ k) (Ico 1 (p ^ n)) ⊆ Ico 1 n.succ,
    from begin
      simp only [finset.subset_iff, Ico.mem, mem_filter, and_imp, true_and] {contextual := tt},
      assume i h1i hip h,
      refine lt_succ_of_le (le_of_not_gt (λ hin, _)),
      have hpik : ¬ p ^ i ∣ k, from mt (le_of_dvd hk0)
        (not_le_of_gt (lt_of_le_of_lt hkn (pow_right_strict_mono hp.two_le hin))),
      have hpn : k % p ^ i + (p ^ n - k) % p ^ i < p ^ i,
        from calc k % p ^ i + (p ^ n - k) % p ^ i
              ≤ k + (p ^ n - k) : add_le_add (mod_le _ _) (mod_le _ _)
          ... = p ^ n : nat.add_sub_cancel' hkn
          ... < p ^ i : pow_right_strict_mono hp.two_le hin,
      simpa [hpik, not_le_of_gt hpn] using h
    end,
  begin
    rw [multiplicity_choose hp hkn (le_refl _),
      multiplicity_eq_card_pow_dvd (ne_of_gt hp.one_lt) hk0 hkn, ← enat.coe_add,
      enat.coe_le_coe, ← card_disjoint_union hdisj, filter_union_right],
    exact le_trans (card_le_of_subset filter_subset_Ico) (by simp)
  end)
  (by rw [← hp.multiplicity_pow_self];
    exact multiplicity_le_multiplicity_choose_add hp _ _)

end prime

lemma multiplicity_two_factorial_lt : ∀ {n : ℕ} (h : n ≠ 0), multiplicity 2 n! < n :=
begin
  have h2 := prime_iff_prime.mp prime_two,
  refine binary_rec _ _,
  { contradiction },
  { intros b n ih h,
    by_cases hn : n = 0,
    { subst hn, simp at h, simp [h, one_right h2.not_unit, enat.zero_lt_one] },
    have : multiplicity 2 (2 * n)! < (2 * n : ℕ),
    { rw [prime_two.multiplicity_factorial_mul],
      refine (enat.add_lt_add_right (ih hn) (enat.coe_ne_top _)).trans_le _,
      rw [two_mul], norm_cast },
    cases b,
    { simpa [bit0_eq_two_mul n] },
    { suffices : multiplicity 2 (2 * n + 1) + multiplicity 2 (2 * n)! < ↑(2 * n) + 1,
      { simpa [succ_eq_add_one, multiplicity.mul, h2, prime_two, nat.bit1_eq_succ_bit0,
          bit0_eq_two_mul n] },
      rw [multiplicity_eq_zero_of_not_dvd (two_not_dvd_two_mul_add_one n), zero_add],
      refine this.trans _, exact_mod_cast lt_succ_self _ }}
end

end nat
