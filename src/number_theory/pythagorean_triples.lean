/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul van Wamelen
-/
import algebra.field
import ring_theory.int.basic
import algebra.group_with_zero.power
import tactic.ring
import tactic.ring_exp
import tactic.field_simp
import data.zmod.basic

/-!
# Pythagorean Triples

The main result is the classification of Pythagorean triples. The final result is for general
Pythagorean triples. It follows from the more interesting relatively prime case. We use the
"rational parametrization of the circle" method for the proof. The parametrization maps the point
`(x / z, y / z)` to the slope of the line through `(-1 , 0)` and `(x / z, y / z)`. This quickly
shows that `(x / z, y / z) = (2 * m * n / (m ^ 2 + n ^ 2), (m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2))` where
`m / n` is the slope. In order to identify numerators and denominators we now need results showing
that these are coprime. This is easy except for the prime 2. In order to deal with that we have to
analyze the parity of `x`, `y`, `m` and `n` and eliminate all the impossible cases. This takes up
the bulk of the proof below.
-/

lemma sq_ne_two_fin_zmod_four (z : zmod 4) : z * z ≠ 2 :=
begin
  change fin 4 at z,
  fin_cases z; norm_num [fin.ext_iff, fin.coe_bit0, fin.coe_bit1]
end

lemma int.sq_ne_two_mod_four (z : ℤ) : (z * z) % 4 ≠ 2 :=
suffices ¬ (z * z) % (4 : ℕ) = 2 % (4 : ℕ), by norm_num at this,
begin
  rw ← zmod.int_coe_eq_int_coe_iff',
  simpa using sq_ne_two_fin_zmod_four _
end

noncomputable theory
open_locale classical

/-- Three integers `x`, `y`, and `z` form a Pythagorean triple if `x * x + y * y = z * z`. -/
def pythagorean_triple (x y z : ℤ) : Prop := x * x + y * y = z * z

/-- Pythagorean triples are interchangable, i.e `x * x + y * y = y * y + x * x = z * z`.
This comes from additive commutativity. -/
lemma pythagorean_triple_comm {x y z : ℤ} :
 (pythagorean_triple x y z) ↔ (pythagorean_triple y x z) :=
by { delta pythagorean_triple, rw add_comm }

/-- The zeroth Pythagorean triple is all zeros. -/
lemma pythagorean_triple.zero : pythagorean_triple 0 0 0 :=
by simp only [pythagorean_triple, zero_mul, zero_add]

namespace pythagorean_triple

variables {x y z : ℤ} (h : pythagorean_triple x y z)

include h

lemma eq : x * x + y * y = z * z := h

@[symm]
lemma symm :
  pythagorean_triple y x z :=
by rwa [pythagorean_triple_comm]

/-- A triple is still a triple if you multiply `x`, `y` and `z`
by a constant `k`. -/
lemma mul (k : ℤ) : pythagorean_triple (k * x) (k * y) (k * z) :=
begin
  by_cases hk : k = 0,
  { simp only [pythagorean_triple, hk, zero_mul, zero_add], },
  { calc (k * x) * (k * x) + (k * y) * (k * y)
        = k ^ 2 * (x * x + y * y) : by ring
    ... = k ^ 2 * (z * z)         : by rw h.eq
    ... = (k * z) * (k * z)       : by ring }
end

omit h

/-- `(k*x, k*y, k*z)` is a Pythagorean triple if and only if
`(x, y, z)` is also a triple. -/
lemma mul_iff (k : ℤ) (hk : k ≠ 0) :
  pythagorean_triple (k * x) (k * y) (k * z) ↔ pythagorean_triple x y z :=
begin
  refine ⟨_, λ h, h.mul k⟩,
  simp only [pythagorean_triple],
  intro h,
  rw ← mul_left_inj' (mul_ne_zero hk hk),
  convert h using 1; ring,
end

include h

/-- A Pythagorean triple `x, y, z` is “classified” if there exist integers `k, m, n` such that
either
 * `x = k * (m ^ 2 - n ^ 2)` and `y = k * (2 * m * n)`, or
 * `x = k * (2 * m * n)` and `y = k * (m ^ 2 - n ^ 2)`. -/
@[nolint unused_arguments] def is_classified := ∃ (k m n : ℤ),
  ((x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n))
    ∨ (x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)))
  ∧ int.gcd m n = 1

/-- A primitive pythogorean triple `x, y, z` is a pythagorean triple with `x` and `y` coprime.
 Such a triple is “primitively classified” if there exist coprime integers `m, n` such that either
 * `x = m ^ 2 - n ^ 2` and `y = 2 * m * n`, or
 * `x = 2 * m * n` and `y = m ^ 2 - n ^ 2`.
-/
@[nolint unused_arguments] def is_primitive_classified := ∃ (m n : ℤ),
  ((x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n)
    ∨ (x = 2 * m * n ∧ y = m ^ 2 - n ^ 2))
  ∧ int.gcd m n = 1
  ∧ ((m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))

lemma mul_is_classified (k : ℤ) (hc : h.is_classified) : (h.mul k).is_classified :=
begin
  obtain ⟨l, m, n, ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co⟩⟩ := hc,
  { use [k * l, m, n], apply and.intro _ co, left, split; ring },
  { use [k * l, m, n], apply and.intro _ co, right, split; ring },
end

lemma even_odd_of_coprime (hc : int.gcd x y = 1) :
  (x % 2 = 0 ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ y % 2 = 0) :=
begin
  cases int.mod_two_eq_zero_or_one x with hx hx;
    cases int.mod_two_eq_zero_or_one y with hy hy,
  { -- x even, y even
    exfalso,
    apply nat.not_coprime_of_dvd_of_dvd (dec_trivial : 1 < 2) _ _ hc,
    { apply int.dvd_nat_abs_of_of_nat_dvd, apply int.dvd_of_mod_eq_zero hx },
    { apply int.dvd_nat_abs_of_of_nat_dvd, apply int.dvd_of_mod_eq_zero hy } },
  { left, exact ⟨hx, hy⟩ },  -- x even, y odd
  { right, exact ⟨hx, hy⟩ }, -- x odd, y even
  { -- x odd, y odd
    exfalso,
    obtain ⟨x0, y0, rfl, rfl⟩ : ∃ x0 y0, x = x0* 2 + 1 ∧ y = y0 * 2 + 1,
    { cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hx) with x0 hx2,
      cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hy) with y0 hy2,
      rw sub_eq_iff_eq_add at hx2 hy2, exact ⟨x0, y0, hx2, hy2⟩ },
    apply int.sq_ne_two_mod_four z,
    rw show z * z = 4 * (x0 * x0 + x0 + y0 * y0 + y0) + 2, by { rw ← h.eq, ring },
    norm_num [int.add_mod] }
end

lemma gcd_dvd : (int.gcd x y : ℤ) ∣ z :=
begin
  by_cases h0 : int.gcd x y = 0,
  { have hx : x = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_left h0 },
    have hy : y = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_right h0 },
    have hz : z = 0,
    { simpa only [pythagorean_triple, hx, hy, add_zero, zero_eq_mul, mul_zero, or_self] using h },
    simp only [hz, dvd_zero], },
  obtain ⟨k, x0, y0, k0, h2, rfl, rfl⟩ :
    ∃ (k : ℕ) x0 y0, 0 < k ∧ int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    int.exists_gcd_one' (nat.pos_of_ne_zero h0),
  rw [int.gcd_mul_right, h2, int.nat_abs_of_nat, one_mul],
  rw [← int.pow_dvd_pow_iff (dec_trivial : 0 < 2), sq z, ← h.eq],
  rw (by ring : x0 * k * (x0 * k) + y0 * k * (y0 * k) = k ^ 2 * (x0 * x0 + y0 * y0)),
  exact dvd_mul_right _ _
end

lemma normalize : pythagorean_triple (x / int.gcd x y) (y / int.gcd x y) (z / int.gcd x y) :=
begin
  by_cases h0 : int.gcd x y = 0,
  { have hx : x = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_left h0 },
    have hy : y = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_right h0 },
    have hz : z = 0,
    { simpa only [pythagorean_triple, hx, hy, add_zero, zero_eq_mul, mul_zero, or_self] using h },
    simp only [hx, hy, hz, int.zero_div], exact zero },
  rcases h.gcd_dvd with ⟨z0, rfl⟩,
  obtain ⟨k, x0, y0, k0, h2, rfl, rfl⟩ :
    ∃ (k : ℕ) x0 y0, 0 < k ∧ int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    int.exists_gcd_one' (nat.pos_of_ne_zero h0),
  have hk : (k : ℤ) ≠ 0, { norm_cast, rwa pos_iff_ne_zero at k0 },
  rw [int.gcd_mul_right, h2, int.nat_abs_of_nat, one_mul] at h ⊢,
  rw [mul_comm x0, mul_comm y0, mul_iff k hk] at h,
  rwa [int.mul_div_cancel _ hk, int.mul_div_cancel _ hk, int.mul_div_cancel_left _ hk],
end

lemma is_classified_of_is_primitive_classified (hp : h.is_primitive_classified) :
  h.is_classified :=
begin
  obtain ⟨m, n, H⟩ := hp,
  use [1, m, n],
  rcases H with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co, pp⟩;
  { apply and.intro _ co, rw one_mul, rw one_mul, tauto }
end

lemma is_classified_of_normalize_is_primitive_classified
  (hc : h.normalize.is_primitive_classified) : h.is_classified :=
begin
  convert h.normalize.mul_is_classified (int.gcd x y)
    (is_classified_of_is_primitive_classified h.normalize hc);
  rw int.mul_div_cancel',
  { exact int.gcd_dvd_left x y },
  { exact int.gcd_dvd_right x y },
  { exact h.gcd_dvd }
end

lemma ne_zero_of_coprime (hc : int.gcd x y = 1) : z ≠ 0 :=
begin
  suffices : 0 < z * z, { rintro rfl, norm_num at this },
  rw [← h.eq, ← sq, ← sq],
  have hc' : int.gcd x y ≠ 0, { rw hc, exact one_ne_zero },
  cases int.ne_zero_of_gcd hc' with hxz hyz,
  { apply lt_add_of_pos_of_le (sq_pos_of_ne_zero x hxz) (sq_nonneg y) },
  { apply lt_add_of_le_of_pos (sq_nonneg x) (sq_pos_of_ne_zero y hyz) }
end

lemma is_primitive_classified_of_coprime_of_zero_left (hc : int.gcd x y = 1) (hx : x = 0) :
  h.is_primitive_classified :=
begin
  subst x,
  change nat.gcd 0 (int.nat_abs y) = 1 at hc,
  rw [nat.gcd_zero_left (int.nat_abs y)] at hc,
  cases int.nat_abs_eq y with hy hy,
  { use [1, 0], rw [hy, hc, int.gcd_zero_right], norm_num },
  { use [0, 1], rw [hy, hc, int.gcd_zero_left], norm_num }
end

lemma coprime_of_coprime (hc : int.gcd x y = 1) : int.gcd y z = 1 :=
begin
  by_contradiction H,
  obtain ⟨p, hp, hpy, hpz⟩ := nat.prime.not_coprime_iff_dvd.mp H,
  apply hp.not_dvd_one,
  rw [← hc],
  apply nat.dvd_gcd (int.prime.dvd_nat_abs_of_coe_dvd_sq hp _ _) hpy,
  rw [sq, eq_sub_of_add_eq h],
  rw [← int.coe_nat_dvd_left] at hpy hpz,
  exact dvd_sub (dvd_mul_of_dvd_left (hpz) _) (dvd_mul_of_dvd_left (hpy) _),
end

end pythagorean_triple

section circle_equiv_gen
/-!
### A parametrization of the unit circle

For the classification of pythogorean triples, we will use a parametrization of the unit circle.
-/

variables {K : Type*} [field K]

/--  A parameterization of the unit circle that is useful for classifying Pythagorean triples.
 (To be applied in the case where `K = ℚ`.) -/
def circle_equiv_gen (hk : ∀ x : K, 1 + x^2 ≠ 0) :
  K ≃ {p : K × K // p.1^2 + p.2^2 = 1 ∧ p.2 ≠ -1} :=
{ to_fun := λ x, ⟨⟨2 * x / (1 + x^2), (1 - x^2) / (1 + x^2)⟩,
    by { field_simp [hk x, div_pow], ring },
    begin
      simp only [ne.def, div_eq_iff (hk x), ←neg_mul_eq_neg_mul, one_mul, neg_add,
        sub_eq_add_neg, add_left_inj],
      simpa only [eq_neg_iff_add_eq_zero, one_pow] using hk 1,
    end⟩,
  inv_fun := λ p, (p : K × K).1 / ((p : K × K).2 + 1),
  left_inv := λ x,
  begin
    have h2 : (1 + 1 : K) = 2 := rfl,
    have h3 : (2 : K) ≠ 0, { convert hk 1, rw [one_pow 2, h2] },
    field_simp [hk x, h2, add_assoc, add_comm, add_sub_cancel'_right, mul_comm],
  end,
  right_inv := λ ⟨⟨x, y⟩, hxy, hy⟩,
  begin
    change x ^ 2 + y ^ 2 = 1 at hxy,
    have h2 : y + 1 ≠ 0, { apply mt eq_neg_of_add_eq_zero, exact hy },
    have h3 : (y + 1) ^ 2 + x ^ 2 = 2 * (y + 1),
    { rw [(add_neg_eq_iff_eq_add.mpr hxy.symm).symm], ring },
    have h4 : (2 : K) ≠ 0, { convert hk 1, rw one_pow 2, refl },
    simp only [prod.mk.inj_iff, subtype.mk_eq_mk],
    split,
    { field_simp [h3], ring },
    { field_simp [h3], rw [← add_neg_eq_iff_eq_add.mpr hxy.symm], ring }
  end }

@[simp] lemma circle_equiv_apply (hk : ∀ x : K, 1 + x^2 ≠ 0) (x : K) :
  (circle_equiv_gen hk x : K × K) = ⟨2 * x / (1 + x^2), (1 - x^2) / (1 + x^2)⟩ := rfl

@[simp] lemma circle_equiv_symm_apply (hk : ∀ x : K, 1 + x^2 ≠ 0)
  (v : {p : K × K // p.1^2 + p.2^2 = 1 ∧ p.2 ≠ -1}) :
  (circle_equiv_gen hk).symm v = (v : K × K).1 / ((v : K × K).2 + 1) := rfl

end circle_equiv_gen

private lemma coprime_sq_sub_sq_add_of_even_odd {m n : ℤ} (h : int.gcd m n = 1)
  (hm : m % 2 = 0) (hn : n % 2 = 1) :
  int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1 :=
begin
  by_contradiction H,
  obtain ⟨p, hp, hp1, hp2⟩ := nat.prime.not_coprime_iff_dvd.mp H,
  rw ← int.coe_nat_dvd_left at hp1 hp2,
  have h2m : (p : ℤ) ∣ 2 * m ^ 2, { convert dvd_add hp2 hp1, ring },
  have h2n : (p : ℤ) ∣ 2 * n ^ 2, { convert dvd_sub hp2 hp1, ring },
  have hmc : p = 2 ∨ p ∣ int.nat_abs m :=
    prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2m,
  have hnc : p = 2 ∨ p ∣ int.nat_abs n :=
    prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2n,
  by_cases h2 : p = 2,
  { have h3 : (m ^ 2 + n ^ 2) % 2 = 1, { norm_num [sq, int.add_mod, int.mul_mod, hm, hn] },
    have h4 : (m ^ 2 + n ^ 2) % 2 = 0, { apply int.mod_eq_zero_of_dvd, rwa h2 at hp2 },
    rw h4 at h3, exact zero_ne_one h3 },
  { apply hp.not_dvd_one,
    rw ← h,
    exact nat.dvd_gcd (or.resolve_left hmc h2) (or.resolve_left hnc h2), }
end

private lemma coprime_sq_sub_sq_add_of_odd_even {m n : ℤ} (h : int.gcd m n = 1)
  (hm : m % 2 = 1) (hn : n % 2 = 0):
  int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1 :=
begin
  rw [int.gcd, ← int.nat_abs_neg (m ^ 2 - n ^ 2)],
  rw [(by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2), add_comm],
  apply coprime_sq_sub_sq_add_of_even_odd _ hn hm, rwa [int.gcd_comm],
end

private lemma coprime_sq_sub_mul_of_even_odd {m n : ℤ} (h : int.gcd m n = 1)
  (hm : m % 2 = 0) (hn : n % 2 = 1) :
  int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 :=
begin
  by_contradiction H,
  obtain ⟨p, hp, hp1, hp2⟩ := nat.prime.not_coprime_iff_dvd.mp H,
  rw ← int.coe_nat_dvd_left at hp1 hp2,
  have hnp : ¬ (p : ℤ) ∣ int.gcd m n,
  { rw h, norm_cast, exact mt nat.dvd_one.mp (nat.prime.ne_one hp) },
  cases int.prime.dvd_mul hp hp2 with hp2m hpn,
  { rw int.nat_abs_mul at hp2m,
    cases (nat.prime.dvd_mul hp).mp hp2m with hp2 hpm,
    { have hp2' : p = 2 := (nat.le_of_dvd zero_lt_two hp2).antisymm hp.two_le,
      revert hp1, rw hp2',
      apply mt int.mod_eq_zero_of_dvd,
      norm_num [sq, int.sub_mod, int.mul_mod, hm, hn],
    },
    apply mt (int.dvd_gcd (int.coe_nat_dvd_left.mpr hpm)) hnp,
    apply (or_self _).mp, apply int.prime.dvd_mul' hp,
    rw (by ring : n * n = - (m ^ 2 - n ^ 2) + m * m),
    apply dvd_add (dvd_neg_of_dvd hp1),
    exact dvd_mul_of_dvd_left (int.coe_nat_dvd_left.mpr hpm) m
  },
  rw int.gcd_comm at hnp,
  apply mt (int.dvd_gcd (int.coe_nat_dvd_left.mpr hpn)) hnp,
  apply (or_self _).mp, apply int.prime.dvd_mul' hp,
  rw (by ring : m * m = (m ^ 2 - n ^ 2) + n * n),
  apply dvd_add hp1,
  exact dvd_mul_of_dvd_left (int.coe_nat_dvd_left.mpr hpn) n
end

private lemma coprime_sq_sub_mul_of_odd_even {m n : ℤ} (h : int.gcd m n = 1)
  (hm : m % 2 = 1) (hn : n % 2 = 0) :
  int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 :=
begin
  rw [int.gcd, ← int.nat_abs_neg (m ^ 2 - n ^ 2)],
  rw [(by ring : 2 * m * n = 2 * n * m), (by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2)],
  apply coprime_sq_sub_mul_of_even_odd _ hn hm, rwa [int.gcd_comm]
end

private lemma coprime_sq_sub_mul {m n : ℤ} (h : int.gcd m n = 1)
  (hmn : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0)) :
  int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 :=
begin
  cases hmn with h1 h2,
  { exact coprime_sq_sub_mul_of_even_odd h h1.left h1.right },
  { exact coprime_sq_sub_mul_of_odd_even h h2.left h2.right }
end

private lemma coprime_sq_sub_sq_sum_of_odd_odd {m n : ℤ} (h : int.gcd m n = 1)
  (hm : m % 2 = 1) (hn : n % 2 = 1) :
  2 ∣ m ^ 2 + n ^ 2
  ∧ 2 ∣ m ^ 2 - n ^ 2
  ∧ ((m ^ 2 - n ^ 2) / 2) % 2 = 0
  ∧ int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1 :=
begin
  cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hm) with m0 hm2,
  cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hn) with n0 hn2,
  rw sub_eq_iff_eq_add at hm2 hn2, subst m, subst n,
  have h1 : (m0 * 2 + 1) ^ 2 + (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 + n0 ^ 2 + m0 + n0) + 1),
  by ring_exp,
  have h2 : (m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 - n0 ^ 2 + m0 - n0)),
  by ring_exp,
  have h3 : ((m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2) / 2 % 2 = 0,
  { rw [h2, int.mul_div_cancel_left, int.mul_mod_right], exact dec_trivial },
  refine ⟨⟨_, h1⟩, ⟨_, h2⟩, h3, _⟩,
  have h20 : (2:ℤ) ≠ 0 := dec_trivial,
  rw [h1, h2, int.mul_div_cancel_left _ h20, int.mul_div_cancel_left _ h20],
  by_contra h4,
  obtain ⟨p, hp, hp1, hp2⟩ := nat.prime.not_coprime_iff_dvd.mp h4,
  apply hp.not_dvd_one,
  rw ← h,
  rw ← int.coe_nat_dvd_left at hp1 hp2,
  apply nat.dvd_gcd,
  { apply int.prime.dvd_nat_abs_of_coe_dvd_sq hp,
    convert dvd_add hp1 hp2, ring_exp },
  { apply int.prime.dvd_nat_abs_of_coe_dvd_sq hp,
    convert dvd_sub hp2 hp1, ring_exp },
end

namespace pythagorean_triple

variables {x y z : ℤ} (h : pythagorean_triple x y z)

include h

lemma is_primitive_classified_aux (hc : x.gcd y = 1) (hzpos : 0 < z)
  {m n : ℤ} (hm2n2 : 0 < m ^ 2 + n ^ 2)
  (hv2 : (x : ℚ) / z = 2 * m * n / (m ^ 2 + n ^ 2))
  (hw2 : (y : ℚ) / z = (m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2))
  (H : int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1)
  (co : int.gcd m n = 1)
  (pp : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0)):
  h.is_primitive_classified :=
begin
  have hz : z ≠ 0, apply ne_of_gt hzpos,
  have h2 : y = m ^ 2 - n ^ 2 ∧ z = m ^ 2 + n ^ 2,
    { apply rat.div_int_inj hzpos hm2n2 (h.coprime_of_coprime hc) H, rw [hw2], norm_cast },
  use [m, n], apply and.intro _ (and.intro co pp), right,
  refine ⟨_, h2.left⟩,
  rw [← rat.coe_int_inj _ _, ← div_left_inj' ((mt (rat.coe_int_inj z 0).mp) hz), hv2, h2.right],
  norm_cast
end

theorem is_primitive_classified_of_coprime_of_odd_of_pos
  (hc : int.gcd x y = 1) (hyo : y % 2 = 1) (hzpos : 0 < z) :
  h.is_primitive_classified :=
begin
  by_cases h0 : x = 0, { exact h.is_primitive_classified_of_coprime_of_zero_left hc h0 },
  let v := (x : ℚ) / z,
  let w := (y : ℚ) / z,
  have hz : z ≠ 0, apply ne_of_gt hzpos,
  have hq : v ^ 2 + w ^ 2 = 1,
  { field_simp [hz, sq], norm_cast, exact h },
  have hvz : v ≠ 0, { field_simp [hz], exact h0 },
  have hw1 : w ≠ -1,
  { contrapose! hvz with hw1,
    rw [hw1, neg_sq, one_pow, add_left_eq_self] at hq,
    exact pow_eq_zero hq, },
  have hQ : ∀ x : ℚ, 1 + x^2 ≠ 0,
  { intro q, apply ne_of_gt, exact lt_add_of_pos_of_le zero_lt_one (sq_nonneg q) },
  have hp : (⟨v, w⟩ : ℚ × ℚ) ∈ {p : ℚ × ℚ | p.1^2 + p.2^2 = 1 ∧ p.2 ≠ -1} := ⟨hq, hw1⟩,
  let q := (circle_equiv_gen hQ).symm ⟨⟨v, w⟩, hp⟩,
  have ht4 : v = 2 * q / (1 + q ^ 2) ∧ w = (1 - q ^ 2) / (1 + q ^ 2),
  { apply prod.mk.inj,
    have := ((circle_equiv_gen hQ).apply_symm_apply ⟨⟨v, w⟩, hp⟩).symm,
    exact congr_arg subtype.val this, },
  let m := (q.denom : ℤ),
  let n := q.num,
  have hm0 : m ≠ 0, { norm_cast, apply rat.denom_ne_zero q },
  have hq2 : q = n / m := (rat.num_div_denom q).symm,
  have hm2n2 : 0 < m ^ 2 + n ^ 2,
  { apply lt_add_of_pos_of_le _ (sq_nonneg n),
    exact lt_of_le_of_ne (sq_nonneg m) (ne.symm (pow_ne_zero 2 hm0)) },
  have hw2 : w = (m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2),
  { rw [ht4.2, hq2], field_simp [hm2n2, rat.denom_ne_zero q, -rat.num_div_denom] },
  have hm2n20 : (m : ℚ) ^ 2 + (n : ℚ) ^ 2 ≠ 0,
  { norm_cast, simpa only [int.coe_nat_pow] using ne_of_gt hm2n2 },
  have hv2 : v = 2 * m * n / (m ^ 2 + n ^ 2),
  { apply eq.symm, apply (div_eq_iff hm2n20).mpr, rw [ht4.1], field_simp [hQ q],
    rw [hq2] {occs := occurrences.pos [2, 3]},
    field_simp [rat.denom_ne_zero q, -rat.num_div_denom],
    ring },
  have hnmcp : int.gcd n m = 1 := q.cop,
  have hmncp : int.gcd m n = 1, { rw int.gcd_comm, exact hnmcp },
  cases int.mod_two_eq_zero_or_one m with hm2 hm2;
    cases int.mod_two_eq_zero_or_one n with hn2 hn2,
  { -- m even, n even
    exfalso,
    have h1 : 2 ∣ (int.gcd n m : ℤ),
    { exact int.dvd_gcd (int.dvd_of_mod_eq_zero hn2) (int.dvd_of_mod_eq_zero hm2) },
    rw hnmcp at h1, revert h1, norm_num },
  { -- m even, n odd
    apply h.is_primitive_classified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp,
    { apply or.intro_left, exact and.intro hm2 hn2 },
    { apply coprime_sq_sub_sq_add_of_even_odd hmncp hm2 hn2 } },
  { -- m odd, n even
    apply h.is_primitive_classified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp,
    { apply or.intro_right, exact and.intro hm2 hn2 },
    apply coprime_sq_sub_sq_add_of_odd_even hmncp hm2 hn2 },
  { -- m odd, n odd
    exfalso,
    have h1 : 2 ∣ m ^ 2 + n ^ 2 ∧ 2 ∣ m ^ 2 - n ^ 2
      ∧ ((m ^ 2 - n ^ 2) / 2) % 2 = 0 ∧ int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1,
    { exact coprime_sq_sub_sq_sum_of_odd_odd hmncp hm2 hn2 },
    have h2 : y = (m ^ 2 - n ^ 2) / 2 ∧ z = (m ^ 2 + n ^ 2) / 2,
    { apply rat.div_int_inj hzpos _ (h.coprime_of_coprime hc) h1.2.2.2,
      { show w = _, rw [←rat.mk_eq_div, ←(rat.div_mk_div_cancel_left (by norm_num : (2 : ℤ) ≠ 0))],
        rw [int.div_mul_cancel h1.1, int.div_mul_cancel h1.2.1, hw2], norm_cast },
      { apply (mul_lt_mul_right (by norm_num : 0 < (2 : ℤ))).mp,
        rw [int.div_mul_cancel h1.1, zero_mul], exact hm2n2 } },
    rw [h2.1, h1.2.2.1] at hyo,
    revert hyo,
    norm_num }
end

theorem is_primitive_classified_of_coprime_of_pos (hc : int.gcd x y = 1) (hzpos : 0 < z):
  h.is_primitive_classified :=
begin
  cases h.even_odd_of_coprime hc with h1 h2,
  { exact (h.is_primitive_classified_of_coprime_of_odd_of_pos hc h1.right hzpos) },
  rw int.gcd_comm at hc,
  obtain ⟨m, n, H⟩ := (h.symm.is_primitive_classified_of_coprime_of_odd_of_pos hc h2.left hzpos),
  use [m, n], tauto
end

theorem is_primitive_classified_of_coprime (hc : int.gcd x y = 1) : h.is_primitive_classified :=
begin
  by_cases hz : 0 < z,
  { exact h.is_primitive_classified_of_coprime_of_pos hc hz },
  have h' : pythagorean_triple x y (-z),
  { simpa [pythagorean_triple, neg_mul_neg] using h.eq, },
  apply h'.is_primitive_classified_of_coprime_of_pos hc,
  apply lt_of_le_of_ne _ (h'.ne_zero_of_coprime hc).symm,
  exact le_neg.mp (not_lt.mp hz)
end

theorem classified : h.is_classified :=
begin
  by_cases h0 : int.gcd x y = 0,
  { have hx : x = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_left h0 },
    have hy : y = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_right h0 },
    use [0, 1, 0], norm_num [hx, hy], },
  apply h.is_classified_of_normalize_is_primitive_classified,
  apply h.normalize.is_primitive_classified_of_coprime,
  apply int.gcd_div_gcd_div_gcd (nat.pos_of_ne_zero h0),
end

omit h

theorem coprime_classification :
  pythagorean_triple x y z ∧ int.gcd x y = 1 ↔
  ∃ m n, ((x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n) ∨
            (x = 2 * m * n ∧ y = m ^ 2 - n ^ 2))
          ∧ (z = m ^ 2 + n ^ 2 ∨ z = - (m ^ 2 + n ^ 2))
          ∧ int.gcd m n = 1
          ∧ ((m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0)) :=
begin
  split,
  { intro h,
    obtain ⟨m, n, H⟩ := h.left.is_primitive_classified_of_coprime h.right,
    use [m, n],
    rcases H with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co, pp⟩,
    { refine ⟨or.inl ⟨rfl, rfl⟩, _, co, pp⟩,
      have : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2,
      { rw [sq, ← h.left.eq], ring },
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this },
    { refine ⟨or.inr ⟨rfl, rfl⟩, _, co, pp⟩,
      have : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2,
      { rw [sq, ← h.left.eq], ring },
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this } },
  { delta pythagorean_triple,
    rintro ⟨m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl, co, pp⟩;
    { split, { ring }, exact coprime_sq_sub_mul co pp }
    <|>
    { split, { ring }, rw int.gcd_comm, exact coprime_sq_sub_mul co pp } }
end

/-- by assuming `x` is odd and `z` is positive we get a slightly more precise classification of
the pythagorean triple `x ^ 2 + y ^ 2 = z ^ 2`-/
theorem coprime_classification' {x y z : ℤ} (h : pythagorean_triple x y z)
  (h_coprime : int.gcd x y = 1) (h_parity : x % 2 = 1) (h_pos : 0 < z) :
  ∃ m n,  x = m ^ 2 - n ^ 2
        ∧ y = 2 * m * n
        ∧ z = m ^ 2 + n ^ 2
        ∧ int.gcd m n = 1
        ∧ ((m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))
        ∧ 0 ≤ m :=
begin
  obtain ⟨m, n, ht1, ht2, ht3, ht4⟩ :=
    pythagorean_triple.coprime_classification.mp (and.intro h h_coprime),
  cases le_or_lt 0 m with hm hm,
  { use [m, n],
    cases ht1 with h_odd h_even,
    { apply and.intro h_odd.1,
      apply and.intro h_odd.2,
      cases ht2 with h_pos h_neg,
      { apply and.intro h_pos (and.intro ht3 (and.intro ht4 hm)) },
      { exfalso, revert h_pos, rw h_neg,
        exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (add_nonneg (sq_nonneg m)
          (sq_nonneg n)))) } },
    exfalso,
    rcases h_even with ⟨rfl, -⟩,
    rw [mul_assoc, int.mul_mod_right] at h_parity,
    exact zero_ne_one h_parity },
  { use [-m, -n],
    cases ht1 with h_odd h_even,
    { rw [neg_sq m],
      rw [neg_sq n],
      apply and.intro h_odd.1,
      split, { rw h_odd.2, ring },
      cases ht2 with h_pos h_neg,
      { apply and.intro h_pos,
        split,
        { delta int.gcd, rw [int.nat_abs_neg, int.nat_abs_neg], exact ht3 },
        { rw [int.neg_mod_two, int.neg_mod_two],
          apply and.intro ht4, linarith } },
      { exfalso, revert h_pos, rw h_neg,
        exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (add_nonneg (sq_nonneg m)
          (sq_nonneg n)))) } },
    exfalso,
    rcases h_even with ⟨rfl, -⟩,
    rw [mul_assoc, int.mul_mod_right] at h_parity,
    exact zero_ne_one h_parity }
end

/-- **Formula for Pythagorean Triples** -/
theorem classification :
  pythagorean_triple x y z ↔
  ∃ k m n, ((x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n)) ∨
            (x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)))
          ∧ (z = k * (m ^ 2 + n ^ 2) ∨ z = - k * (m ^ 2 + n ^ 2)) :=
begin
  split,
  { intro h,
    obtain ⟨k, m, n, H⟩ := h.classified,
    use [k, m, n],
    rcases H with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
    { refine ⟨or.inl ⟨rfl, rfl⟩, _⟩,
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2,
      { rw [sq, ← h.eq], ring },
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this },
    { refine ⟨or.inr ⟨rfl, rfl⟩, _⟩,
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2,
      { rw [sq, ← h.eq], ring },
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this } },
  { rintro ⟨k, m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl⟩;
    delta pythagorean_triple; ring }
end

end pythagorean_triple
