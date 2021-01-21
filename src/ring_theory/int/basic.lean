/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/

import ring_theory.principal_ideal_domain

/-!
# Divisibility over ℕ and ℤ

This file collects results for the integers and natural numbers that use abstract algebra in
their proofs or cases of ℕ and ℤ being examples of structures in abstract algebra.

## Main statements

* `nat.prime_iff`: `nat.prime` coincides with the general definition of `prime`
* `nat.irreducible_iff_prime`: a non-unit natural number is only divisible by `1` iff it is prime
* `nat.factors_eq`: the multiset of elements of `nat.factors` is equal to the factors
   given by the `unique_factorization_monoid` instance
* ℤ is a `normalization_monoid`
* ℤ is a `gcd_monoid`

## Tags

prime, irreducible, natural numbers, integers, normalization monoid, gcd monoid,
greatest common divisor, prime factorization, prime factors, unique factorization,
unique factors
-/

theorem nat.prime_iff {p : ℕ} : p.prime ↔ prime p :=
begin
  split; intro h,
  { refine ⟨h.ne_zero, ⟨_, λ a b, _⟩⟩,
    { rw nat.is_unit_iff, apply h.ne_one },
    { apply h.dvd_mul.1 } },
  { refine ⟨_, λ m hm, _⟩,
    { cases p, { exfalso, apply h.ne_zero rfl },
      cases p, { exfalso, apply h.ne_one rfl },
      omega },
    { cases hm with n hn,
      cases h.2.2 m n (hn ▸ dvd_refl _) with hpm hpn,
      { right, apply nat.dvd_antisymm (dvd.intro _ hn.symm) hpm },
      { left,
        cases n, { exfalso, rw [hn, mul_zero] at h, apply h.ne_zero rfl },
        apply nat.eq_of_mul_eq_mul_right (nat.succ_pos _),
        rw [← hn, one_mul],
        apply nat.dvd_antisymm hpn (dvd.intro m _),
        rw [mul_comm, hn], }, } }
end

theorem nat.irreducible_iff_prime {p : ℕ} : irreducible p ↔ prime p :=
begin
  refine ⟨λ h, _, irreducible_of_prime⟩,
  rw ← nat.prime_iff,
  refine ⟨_, λ m hm, _⟩,
  { cases p, { exfalso, apply h.ne_zero rfl },
    cases p, { exfalso, apply h.1 is_unit_one, },
    omega },
  { cases hm with n hn,
    cases h.2 m n hn with um un,
    { left, rw nat.is_unit_iff.1 um, },
    { right, rw [hn, nat.is_unit_iff.1 un, mul_one], } }
end

namespace nat

instance : wf_dvd_monoid ℕ :=
⟨begin
  apply rel_hom.well_founded _ (with_top.well_founded_lt nat.lt_wf),
  refine ⟨λ x, if x = 0 then ⊤ else x, _⟩,
  intros a b h,
  cases a,
  { exfalso, revert h, simp [dvd_not_unit] },
  cases b,
  {simp [succ_ne_zero, with_top.coe_lt_top]},
  cases dvd_and_not_dvd_iff.2 h with h1 h2,
  simp only [succ_ne_zero, with_top.coe_lt_coe, if_false],
  apply lt_of_le_of_ne (nat.le_of_dvd (nat.succ_pos _) h1) (λ con, h2 _),
  rw con,
end⟩

instance : unique_factorization_monoid ℕ :=
⟨λ _, nat.irreducible_iff_prime⟩

end nat

namespace int

section normalization_monoid

instance : normalization_monoid ℤ :=
{ norm_unit      := λa:ℤ, if 0 ≤ a then 1 else -1,
  norm_unit_zero := if_pos (le_refl _),
  norm_unit_mul  := assume a b hna hnb,
  begin
    cases hna.lt_or_lt with ha ha; cases hnb.lt_or_lt with hb hb;
      simp [mul_nonneg_iff, ha.le, ha.not_le, hb.le, hb.not_le]
  end,
  norm_unit_coe_units := assume u, (units_eq_one_or u).elim
    (assume eq, eq.symm ▸ if_pos zero_le_one)
    (assume eq, eq.symm ▸ if_neg (not_le_of_gt $ show (-1:ℤ) < 0, by dec_trivial)), }

lemma normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : normalize z = z :=
show z * ↑(ite _ _ _) = z, by rw [if_pos h, units.coe_one, mul_one]

lemma normalize_of_neg {z : ℤ} (h : z < 0) : normalize z = -z :=
show z * ↑(ite _ _ _) = -z,
by rw [if_neg (not_le_of_gt h), units.coe_neg, units.coe_one, mul_neg_one]

lemma normalize_coe_nat (n : ℕ) : normalize (n : ℤ) = n :=
normalize_of_nonneg (coe_nat_le_coe_nat_of_le $ nat.zero_le n)

theorem coe_nat_abs_eq_normalize (z : ℤ) : (z.nat_abs : ℤ) = normalize z :=
begin
  by_cases 0 ≤ z,
  { simp [nat_abs_of_nonneg h, normalize_of_nonneg h] },
  { simp [of_nat_nat_abs_of_nonpos (le_of_not_ge h), normalize_of_neg (lt_of_not_ge h)] }
end

end normalization_monoid

section gcd_monoid

instance : gcd_monoid ℤ :=
{ gcd            := λa b, int.gcd a b,
  lcm            := λa b, int.lcm a b,
  gcd_dvd_left   := assume a b, int.gcd_dvd_left _ _,
  gcd_dvd_right  := assume a b, int.gcd_dvd_right _ _,
  dvd_gcd        := assume a b c, dvd_gcd,
  normalize_gcd  := assume a b, normalize_coe_nat _,
  gcd_mul_lcm    := by intros; rw [← int.coe_nat_mul, gcd_mul_lcm, coe_nat_abs_eq_normalize],
  lcm_zero_left  := assume a, coe_nat_eq_zero.2 $ nat.lcm_zero_left _,
  lcm_zero_right := assume a, coe_nat_eq_zero.2 $ nat.lcm_zero_right _,
  .. int.normalization_monoid }

lemma coe_gcd (i j : ℤ) : ↑(int.gcd i j) = gcd_monoid.gcd i j := rfl
lemma coe_lcm (i j : ℤ) : ↑(int.lcm i j) = gcd_monoid.lcm i j := rfl

lemma nat_abs_gcd (i j : ℤ) : nat_abs (gcd_monoid.gcd i j) = int.gcd i j := rfl
lemma nat_abs_lcm (i j : ℤ) : nat_abs (gcd_monoid.lcm i j) = int.lcm i j := rfl

end gcd_monoid

lemma exists_unit_of_abs (a : ℤ) : ∃ (u : ℤ) (h : is_unit u), (int.nat_abs a : ℤ) = u * a :=
begin
  cases (nat_abs_eq a) with h,
  { use [1, is_unit_one], rw [← h, one_mul], },
  { use [-1, is_unit_int.mpr rfl], rw [ ← neg_eq_iff_neg_eq.mp (eq.symm h)],
    simp only [neg_mul_eq_neg_mul_symm, one_mul] }
end

lemma gcd_eq_one_iff_coprime {a b : ℤ} : int.gcd a b = 1 ↔ is_coprime a b :=
begin
  split,
  { intro hg,
    obtain ⟨ua, hua, ha⟩ := exists_unit_of_abs a,
    obtain ⟨ub, hub, hb⟩ := exists_unit_of_abs b,
    use [(nat.gcd_a (int.nat_abs a) (int.nat_abs b)) * ua,
        (nat.gcd_b (int.nat_abs a) (int.nat_abs b)) * ub],
    rw [mul_assoc, ← ha, mul_assoc, ← hb, mul_comm, mul_comm _ (int.nat_abs b : ℤ),
      ← nat.gcd_eq_gcd_ab],
    norm_cast,
    exact hg },
  { rintro ⟨r, s, h⟩,
    by_contradiction hg,
    obtain ⟨p, ⟨hp, ha, hb⟩⟩ := nat.prime.not_coprime_iff_dvd.mp hg,
    apply nat.prime.not_dvd_one hp,
    apply coe_nat_dvd.mp,
    change (p : ℤ) ∣ 1,
    rw [← h],
    exact dvd_add (dvd_mul_of_dvd_right (coe_nat_dvd_left.mpr ha) _)
      (dvd_mul_of_dvd_right (coe_nat_dvd_left.mpr hb) _),
  }
end

lemma sqr_of_gcd_eq_one {a b c : ℤ} (h : int.gcd a b = 1) (heq : a * b = c ^ 2) :
  ∃ (a0 : ℤ), a = a0 ^ 2 ∨ a = - (a0 ^ 2) :=
begin
  have h' : gcd_monoid.gcd a b = 1, { rw [← coe_gcd, h], dec_trivial },
  obtain ⟨d, ⟨u, hu⟩⟩ := exists_associated_pow_of_mul_eq_pow h' heq,
  use d,
  rw ← hu,
  cases int.units_eq_one_or u with hu' hu'; { rw hu', simp }
end

lemma sqr_of_coprime {a b c : ℤ} (h : is_coprime a b) (heq : a * b = c ^ 2) :
  ∃ (a0 : ℤ), a = a0 ^ 2 ∨ a = - (a0 ^ 2) := sqr_of_gcd_eq_one (gcd_eq_one_iff_coprime.mpr h) heq

end int

theorem irreducible_iff_nat_prime : ∀(a : ℕ), irreducible a ↔ nat.prime a
| 0 := by simp [nat.not_prime_zero]
| 1 := by simp [nat.prime, one_lt_two]
| (n + 2) :=
  have h₁ : ¬n + 2 = 1, from dec_trivial,
  begin
    simp [h₁, nat.prime, irreducible, (≥), nat.le_add_left 2 n, (∣)],
    refine forall_congr (assume a, forall_congr $ assume b, forall_congr $ assume hab, _),
    by_cases a = 1; simp [h],
    split,
    { assume hb, simpa [hb] using hab.symm },
    { assume ha, subst ha,
      have : n + 2 > 0, from dec_trivial,
      refine nat.eq_of_mul_eq_mul_left this _,
      rw [← hab, mul_one] }
  end

lemma nat.prime_iff_prime {p : ℕ} : p.prime ↔ _root_.prime (p : ℕ) :=
⟨λ hp, ⟨pos_iff_ne_zero.1 hp.pos, mt is_unit_iff_dvd_one.1 hp.not_dvd_one,
    λ a b, hp.dvd_mul.1⟩,
  λ hp, ⟨nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hp.1, λ h1, hp.2.1 $ h1.symm ▸ is_unit_one⟩,
    λ a h, let ⟨b, hab⟩ := h in
      (hp.2.2 a b (hab ▸ dvd_refl _)).elim
        (λ ha, or.inr (nat.dvd_antisymm h ha))
        (λ hb, or.inl (have hpb : p = b, from nat.dvd_antisymm hb
            (hab.symm ▸ dvd_mul_left _ _),
          (nat.mul_right_inj (show 0 < p, from
              nat.pos_of_ne_zero hp.1)).1 $
            by rw [hpb, mul_comm, ← hab, hpb, mul_one]))⟩⟩

lemma nat.prime_iff_prime_int {p : ℕ} : p.prime ↔ _root_.prime (p : ℤ) :=
⟨λ hp, ⟨int.coe_nat_ne_zero_iff_pos.2 hp.pos, mt is_unit_int.1 hp.ne_one,
  λ a b h, by rw [← int.dvd_nat_abs, int.coe_nat_dvd, int.nat_abs_mul, hp.dvd_mul] at h;
    rwa [← int.dvd_nat_abs, int.coe_nat_dvd, ← int.dvd_nat_abs, int.coe_nat_dvd]⟩,
  λ hp, nat.prime_iff_prime.2 ⟨int.coe_nat_ne_zero.1 hp.1,
      mt nat.is_unit_iff.1 $ λ h, by simpa [h, not_prime_one] using hp,
    λ a b, by simpa only [int.coe_nat_dvd, (int.coe_nat_mul _ _).symm] using hp.2.2 a b⟩⟩

/-- Maps an associate class of integers consisting of `-n, n` to `n : ℕ` -/
def associates_int_equiv_nat : associates ℤ ≃ ℕ :=
begin
  refine ⟨λz, z.out.nat_abs, λn, associates.mk n, _, _⟩,
  { refine (assume a, quotient.induction_on' a $ assume a,
      associates.mk_eq_mk_iff_associated.2 $ associated.symm $ ⟨norm_unit a, _⟩),
    show normalize a = int.nat_abs (normalize a),
    rw [int.coe_nat_abs_eq_normalize, normalize_idem] },
  { intro n, dsimp, rw [associates.out_mk ↑n,
    ← int.coe_nat_abs_eq_normalize, int.nat_abs_of_nat, int.nat_abs_of_nat] }
end

lemma int.prime.dvd_mul {m n : ℤ} {p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ m * n) : p ∣ m.nat_abs ∨ p ∣ n.nat_abs :=
begin
  apply (nat.prime.dvd_mul hp).mp,
  rw ← int.nat_abs_mul,
  exact int.coe_nat_dvd_left.mp h
end

lemma int.prime.dvd_mul' {m n : ℤ} {p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ m * n) : (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n :=
begin
  rw [int.coe_nat_dvd_left, int.coe_nat_dvd_left],
  exact int.prime.dvd_mul hp h
end

lemma int.prime.dvd_pow {n : ℤ} {k p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ n ^ k) : p  ∣ n.nat_abs :=
begin
  apply @nat.prime.dvd_of_dvd_pow _ _ k hp,
  rw ← int.nat_abs_pow,
  exact int.coe_nat_dvd_left.mp h
end

lemma int.prime.dvd_pow' {n : ℤ} {k p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ n ^ k) : (p : ℤ)  ∣ n :=
begin
  rw int.coe_nat_dvd_left,
  exact int.prime.dvd_pow hp h
end

lemma prime_two_or_dvd_of_dvd_two_mul_pow_self_two {m : ℤ} {p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ 2 * m ^ 2) : p = 2 ∨ p ∣ int.nat_abs m :=
begin
  cases int.prime.dvd_mul hp h with hp2 hpp,
  { apply or.intro_left,
    exact le_antisymm (nat.le_of_dvd zero_lt_two hp2) (nat.prime.two_le hp) },
  { apply or.intro_right,
    rw [pow_two, int.nat_abs_mul] at hpp,
    exact (or_self _).mp ((nat.prime.dvd_mul hp).mp hpp)}
end

instance nat.unique_units : unique (units ℕ) :=
{ default := 1, uniq := nat.units_eq_one }

open unique_factorization_monoid

theorem nat.factors_eq {n : ℕ} : factors n = n.factors :=
begin
  cases n, {refl},
  rw [← multiset.rel_eq, ← associated_eq_eq],
  apply factors_unique (irreducible_of_factor) _,
  { rw [multiset.coe_prod, nat.prod_factors (nat.succ_pos _)],
    apply factors_prod (nat.succ_ne_zero _) },
  { apply_instance },
  { intros x hx,
    rw [nat.irreducible_iff_prime, ← nat.prime_iff],
    apply nat.mem_factors hx, }
end

lemma nat.factors_multiset_prod_of_irreducible
  {s : multiset ℕ} (h : ∀ (x : ℕ), x ∈ s → irreducible x) :
  unique_factorization_monoid.factors (s.prod) = s :=
begin
  rw [← multiset.rel_eq, ← associated_eq_eq],
  apply (unique_factorization_monoid.factors_unique irreducible_of_factor h (factors_prod _)),
  rw [ne.def, multiset.prod_eq_zero_iff],
  intro con,
  exact not_irreducible_zero (h 0 con),
end

namespace multiplicity

lemma finite_int_iff_nat_abs_finite {a b : ℤ} : finite a b ↔ finite a.nat_abs b.nat_abs :=
by simp only [finite_def, ← int.nat_abs_dvd_abs_iff, int.nat_abs_pow]

lemma finite_int_iff {a b : ℤ} : finite a b ↔ (a.nat_abs ≠ 1 ∧ b ≠ 0) :=
begin
  have := int.nat_abs_eq a,
  have := @int.nat_abs_ne_zero_of_ne_zero b,
  rw [finite_int_iff_nat_abs_finite, finite_nat_iff, pos_iff_ne_zero],
  split; finish
end

instance decidable_nat : decidable_rel (λ a b : ℕ, (multiplicity a b).dom) :=
λ a b, decidable_of_iff _ finite_nat_iff.symm

instance decidable_int : decidable_rel (λ a b : ℤ, (multiplicity a b).dom) :=
λ a b, decidable_of_iff _ finite_int_iff.symm

end multiplicity
