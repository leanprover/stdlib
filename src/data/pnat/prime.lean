/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Neil Strickland
-/
import data.nat.prime

/-!
# Primality and GCD on pnat

This file extends the theory of `ℕ+` with `gcd`, `lcm` and `prime` functions, analogous to those on
`nat`.
-/

namespace nat.primes

instance coe_pnat : has_coe nat.primes ℕ+ := ⟨λ p, ⟨(p : ℕ), p.property.pos⟩⟩
theorem coe_pnat_nat (p : nat.primes) : ((p : ℕ+) : ℕ) = p := rfl

theorem coe_pnat_inj (p q : nat.primes) : (p : ℕ+) = (q : ℕ+) → p = q := λ h,
begin
  replace h : ((p : ℕ+) : ℕ) = ((q : ℕ+) : ℕ) := congr_arg subtype.val h,
  rw [coe_pnat_nat, coe_pnat_nat] at h,
  exact subtype.eq h,
end

end nat.primes

namespace pnat
open nat

/-- The greatest common divisor (gcd) of two positive natural numbers,
  viewed as positive natural number. -/
def gcd (n m : ℕ+) : ℕ+ :=
 ⟨nat.gcd (n : ℕ) (m : ℕ), nat.gcd_pos_of_pos_left (m : ℕ) n.pos⟩

/-- The least common multiple (lcm) of two positive natural numbers,
  viewed as positive natural number. -/
def lcm (n m : ℕ+) : ℕ+ :=
 ⟨nat.lcm (n : ℕ) (m : ℕ),
  by { let h := mul_pos n.pos m.pos,
       rw [← gcd_mul_lcm (n : ℕ) (m : ℕ), mul_comm] at h,
       exact pos_of_dvd_of_pos (dvd.intro (nat.gcd (n : ℕ) (m : ℕ)) rfl) h }⟩

@[simp] theorem gcd_coe (n m : ℕ+) : ((gcd n m) : ℕ) = nat.gcd n m := rfl

@[simp] theorem lcm_coe (n m : ℕ+) : ((lcm n m) : ℕ) = nat.lcm n m := rfl

theorem gcd_dvd_left (n m : ℕ+) : (gcd n m) ∣ n := dvd_iff.2 (nat.gcd_dvd_left (n : ℕ) (m : ℕ))

theorem gcd_dvd_right (n m : ℕ+) : (gcd n m) ∣ m := dvd_iff.2 (nat.gcd_dvd_right (n : ℕ) (m : ℕ))

theorem dvd_gcd {m n k : ℕ+} (hm : k ∣ m) (hn : k ∣ n) : k ∣ gcd m n :=
 dvd_iff.2 (@nat.dvd_gcd (m : ℕ) (n : ℕ) (k : ℕ) (dvd_iff.1 hm) (dvd_iff.1 hn))

theorem dvd_lcm_left  (n m : ℕ+) : n ∣ lcm n m := dvd_iff.2 (nat.dvd_lcm_left  (n : ℕ) (m : ℕ))

theorem dvd_lcm_right (n m : ℕ+) : m ∣ lcm n m := dvd_iff.2 (nat.dvd_lcm_right (n : ℕ) (m : ℕ))

theorem lcm_dvd {m n k : ℕ+} (hm : m ∣ k) (hn : n ∣ k) : lcm m n ∣ k :=
  dvd_iff.2 (@nat.lcm_dvd (m : ℕ) (n : ℕ) (k : ℕ) (dvd_iff.1 hm) (dvd_iff.1 hn))

theorem gcd_mul_lcm (n m : ℕ+) : (gcd n m) * (lcm n m) = n * m :=
 subtype.eq (nat.gcd_mul_lcm (n : ℕ) (m : ℕ))

lemma eq_one_of_lt_two {n : ℕ+} : n < 2 → n = 1 :=
begin
  intro h, apply le_antisymm, swap, apply pnat.one_le,
  change n < 1 + 1 at h, rw pnat.lt_add_one_iff at h, apply h
end


section prime
/-! ### Prime numbers -/

/-- Primality predicate for `ℕ+`, defined in terms of `nat.prime`. -/
def prime (p : ℕ+) : Prop := (p : ℕ).prime

lemma prime.one_lt {p : ℕ+} : p.prime → 1 < p := nat.prime.one_lt

lemma prime_two : (2 : ℕ+).prime := nat.prime_two

lemma dvd_prime {p m : ℕ+} (pp : p.prime) :
(m ∣ p ↔ m = 1 ∨ m = p) := by { rw pnat.dvd_iff, rw nat.dvd_prime pp, simp }

lemma prime.ne_one {p : ℕ+} : p.prime → p ≠ 1 :=
by { intro pp, intro contra, apply nat.prime.ne_one pp, rw pnat.coe_eq_one_iff, apply contra }

@[simp]
lemma not_prime_one : ¬ (1: ℕ+).prime :=  nat.not_prime_one

lemma prime.not_dvd_one {p : ℕ+} :
p.prime →  ¬ p ∣ 1 := λ pp : p.prime, by {rw dvd_iff, apply nat.prime.not_dvd_one pp}

lemma exists_prime_and_dvd {n : ℕ+} : 2 ≤ n → (∃ (p : ℕ+), p.prime ∧ p ∣ n) :=
begin
  intro h, cases nat.exists_prime_and_dvd h with p hp,
  existsi (⟨p, nat.prime.pos hp.left⟩ : ℕ+), rw dvd_iff, apply hp
end

end prime

section coprime
/-! ### Coprime numbers and gcd -/

/-- Two pnats are coprime if their gcd is 1. -/
def coprime (m n : ℕ+) : Prop := m.gcd n = 1

@[simp]
lemma coprime_coe {m n : ℕ+} : nat.coprime ↑m ↑n ↔ m.coprime n :=
by { unfold coprime, unfold nat.coprime, rw ← coe_inj, simp }

lemma coprime.mul {k m n : ℕ+} : m.coprime k → n.coprime k → (m * n).coprime k :=
by { repeat {rw ← coprime_coe}, rw mul_coe, apply nat.coprime.mul }

lemma coprime.mul_right {k m n : ℕ+} : k.coprime m → k.coprime n → k.coprime (m * n) :=
by { repeat {rw ← coprime_coe}, rw mul_coe, apply nat.coprime.mul_right }

lemma gcd_comm {m n : ℕ+} : m.gcd n = n.gcd m :=
by { apply eq, simp only [gcd_coe], apply nat.gcd_comm }

lemma gcd_eq_left_iff_dvd {m n : ℕ+} : m ∣ n ↔ m.gcd n = m :=
by { rw dvd_iff, rw nat.gcd_eq_left_iff_dvd, rw ← coe_inj, simp }

lemma gcd_eq_right_iff_dvd {m n : ℕ+} : m ∣ n ↔ n.gcd m = m :=
by { rw gcd_comm, apply gcd_eq_left_iff_dvd, }

lemma coprime.gcd_mul_left_cancel (m : ℕ+) {n k : ℕ+} :
  k.coprime n → (k * m).gcd n = m.gcd n :=
begin
  intro h, apply eq, simp only [gcd_coe, mul_coe],
  apply nat.coprime.gcd_mul_left_cancel, simpa
end

lemma coprime.gcd_mul_right_cancel (m : ℕ+) {n k : ℕ+} :
  k.coprime n → (m * k).gcd n = m.gcd n :=
begin
  rw mul_comm, apply coprime.gcd_mul_left_cancel,
end

lemma coprime.gcd_mul_left_cancel_right (m : ℕ+) {n k : ℕ+} :
  k.coprime m → m.gcd (k * n) = m.gcd n :=
begin
  intro h, iterate 2 {rw gcd_comm, symmetry}, apply coprime.gcd_mul_left_cancel _ h,
end

lemma coprime.gcd_mul_right_cancel_right (m : ℕ+) {n k : ℕ+} :
  k.coprime m → m.gcd (n * k) = m.gcd n :=
begin
  rw mul_comm, apply coprime.gcd_mul_left_cancel_right,
end

@[simp]
lemma one_gcd {n : ℕ+} : gcd 1 n = 1 :=
by { rw ← gcd_eq_left_iff_dvd, apply one_dvd }

@[simp]
lemma gcd_one {n : ℕ+} : gcd n 1 = 1 := by { rw gcd_comm, apply one_gcd }

@[symm]
lemma coprime.symm {m n : ℕ+} : m.coprime n → n.coprime m :=
by { unfold coprime, rw gcd_comm, simp }

@[simp]
lemma one_coprime {n : ℕ+} : (1 : ℕ+).coprime n := one_gcd

@[simp]
lemma coprime_one {n : ℕ+} : n.coprime 1 := coprime.symm one_coprime

lemma coprime.coprime_dvd_left {m k n : ℕ+} :
  m ∣ k → k.coprime n → m.coprime n :=
by { rw dvd_iff, repeat {rw ← coprime_coe}, apply nat.coprime.coprime_dvd_left }

lemma coprime.factor_eq_gcd_left {a b m n : ℕ+} (cop : m.coprime n) (am : a ∣ m) (bn : b ∣ n) :
  a = (a * b).gcd m :=
begin
  rw gcd_eq_left_iff_dvd at am,
  conv_lhs {rw ← am}, symmetry,
  apply coprime.gcd_mul_right_cancel a,
  apply coprime.coprime_dvd_left bn cop.symm,
end

lemma coprime.factor_eq_gcd_right {a b m n : ℕ+} (cop : m.coprime n) (am : a ∣ m) (bn : b ∣ n) :
  a = (b * a).gcd m :=
begin
  rw mul_comm, apply coprime.factor_eq_gcd_left cop am bn,
end

lemma coprime.factor_eq_gcd_left_right {a b m n : ℕ+}
  (cop : m.coprime n) (am : a ∣ m) (bn : b ∣ n) : a = m.gcd (a * b) :=
begin
  rw gcd_comm, apply coprime.factor_eq_gcd_left cop am bn,
end

lemma coprime.factor_eq_gcd_right_right {a b m n : ℕ+}
  (cop : m.coprime n) (am : a ∣ m) (bn : b ∣ n) : a = m.gcd (b * a) :=
begin
  rw gcd_comm, apply coprime.factor_eq_gcd_right cop am bn,
end

lemma coprime.gcd_mul (k : ℕ+) {m n : ℕ+} (h: m.coprime n) :
  k.gcd (m * n) = k.gcd m * k.gcd n :=
begin
  rw ← coprime_coe at h, apply eq,
  simp only [gcd_coe, mul_coe], apply nat.coprime.gcd_mul k h
end

lemma gcd_eq_left {m n : ℕ+} : m ∣ n → m.gcd n = m :=
by { rw dvd_iff, intro h, apply eq, simp only [gcd_coe], apply nat.gcd_eq_left h }

lemma coprime.pow {m n : ℕ+} (k l : ℕ) (h : m.coprime n) : (m ^ k).coprime (n ^ l) :=
begin
  rw ← coprime_coe at *, simp only [pow_coe], apply nat.coprime.pow, apply h
end

end coprime

end pnat
