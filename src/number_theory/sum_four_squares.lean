/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import algebra.group_power.identities
import data.zmod.basic
import field_theory.finite.basic
import data.int.parity
import data.fintype.card

/-!
# Lagrange's four square theorem

The main result in this file is `sum_four_squares`,
a proof that every natural number is the sum of four square numbers.

## Implementation Notes

The proof used is close to Lagrange's original proof.
-/

open finset polynomial finite_field equiv
open_locale big_operators

namespace int

lemma sq_add_sq_of_two_mul_sq_add_sq {m x y : ℤ} (h : 2 * m = x^2 + y^2) :
  m = ((x - y) / 2) ^ 2 + ((x + y) / 2) ^ 2 :=
have even (x^2 + y^2), by simp [h.symm, even_mul],
have hxaddy : even (x + y), by simpa [sq] with parity_simps,
have hxsuby : even (x - y), by simpa [sq] with parity_simps,
(mul_right_inj' (show (2*2 : ℤ) ≠ 0, from dec_trivial)).1 $
calc 2 * 2 * m = (x - y)^2 + (x + y)^2 : by rw [mul_assoc, h]; ring
... = (2 * ((x - y) / 2))^2 + (2 * ((x + y) / 2))^2 :
  by rw [int.mul_div_cancel' hxsuby, int.mul_div_cancel' hxaddy]
... = 2 * 2 * (((x - y) / 2) ^ 2 + ((x + y) / 2) ^ 2) :
  by simp [mul_add, pow_succ, mul_comm, mul_assoc, mul_left_comm]

lemma exists_sq_add_sq_add_one_eq_k (p : ℕ) [hp : fact p.prime] :
  ∃ (a b : ℤ) (k : ℕ), a^2 + b^2 + 1 = k * p ∧ k < p :=
hp.1.eq_two_or_odd.elim (λ hp2, hp2.symm ▸ ⟨1, 0, 1, rfl, dec_trivial⟩) $ λ hp1,
let ⟨a, b, hab⟩ := zmod.sq_add_sq p (-1) in
have hab' : (p : ℤ) ∣ a.val_min_abs ^ 2 + b.val_min_abs ^ 2 + 1,
  from (char_p.int_cast_eq_zero_iff (zmod p) p _).1 $ by simpa [eq_neg_iff_add_eq_zero] using hab,
let ⟨k, hk⟩ := hab' in
have hk0 : 0 ≤ k, from nonneg_of_mul_nonneg_left
  (by rw ← hk; exact (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) zero_le_one))
  (int.coe_nat_pos.2 hp.1.pos),
⟨a.val_min_abs, b.val_min_abs, k.nat_abs,
    by rw [hk, int.nat_abs_of_nonneg hk0, mul_comm],
  lt_of_mul_lt_mul_left
    (calc p * k.nat_abs = a.val_min_abs.nat_abs ^ 2 + b.val_min_abs.nat_abs ^ 2 + 1 :
        by rw [← int.coe_nat_inj', int.coe_nat_add, int.coe_nat_add, int.coe_nat_pow,
          int.coe_nat_pow, int.nat_abs_sq, int.nat_abs_sq,
          int.coe_nat_one, hk, int.coe_nat_mul, int.nat_abs_of_nonneg hk0]
      ... ≤ (p / 2) ^ 2 + (p / 2)^2 + 1 :
        add_le_add
          (add_le_add
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _)
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _))
          (le_refl _)
      ... < (p / 2) ^ 2 + (p / 2)^ 2 + (p % 2)^2 + ((2 * (p / 2)^2 + (4 * (p / 2) * (p % 2)))) :
        by rw [hp1, one_pow, mul_one];
          exact (lt_add_iff_pos_right _).2
            (add_pos_of_nonneg_of_pos (nat.zero_le _) (mul_pos dec_trivial
              (nat.div_pos hp.1.two_le dec_trivial)))
      ... = p * p : by { conv_rhs { rw [← nat.mod_add_div p 2] }, ring })
    (show 0 ≤ p, from nat.zero_le _)⟩

end int

namespace nat

open int

open_locale classical

private lemma sum_four_squares_of_two_mul_sum_four_squares {m a b c d : ℤ}
  (h : a^2 + b^2 + c^2 + d^2 = 2 * m) : ∃ w x y z : ℤ, w^2 + x^2 + y^2 + z^2 = m :=
have ∀ f : fin 4 → zmod 2, (f 0)^2 + (f 1)^2 + (f 2)^2 + (f 3)^2 = 0 →
    ∃ i : (fin 4), (f i)^2 + f (swap i 0 1)^2 = 0 ∧ f (swap i 0 2)^2 + f (swap i 0 3)^2 = 0,
  from dec_trivial,
let f : fin 4 → ℤ :=
  vector.nth (a ::ᵥ b ::ᵥ c ::ᵥ d ::ᵥ vector.nil) in
let ⟨i, hσ⟩ := this (coe ∘ f) (by rw [← @zero_mul (zmod 2) _ m,
  ← show ((2 : ℤ) : zmod 2) = 0, from rfl,
  ← int.cast_mul, ← h]; simp only [int.cast_add, int.cast_pow]; refl) in
let σ := swap i 0 in
have h01 : 2 ∣ f (σ 0) ^ 2 + f (σ 1) ^ 2,
  from (char_p.int_cast_eq_zero_iff (zmod 2) 2 _).1 $ by simpa [σ] using hσ.1,
have h23 : 2 ∣ f (σ 2) ^ 2 + f (σ 3) ^ 2,
  from (char_p.int_cast_eq_zero_iff (zmod 2) 2 _).1 $ by simpa using hσ.2,
let ⟨x, hx⟩ := h01 in let ⟨y, hy⟩ := h23 in
⟨(f (σ 0) - f (σ 1)) / 2, (f (σ 0) + f (σ 1)) / 2, (f (σ 2) - f (σ 3)) / 2, (f (σ 2) + f (σ 3)) / 2,
  begin
    rw [← int.sq_add_sq_of_two_mul_sq_add_sq hx.symm, add_assoc,
      ← int.sq_add_sq_of_two_mul_sq_add_sq hy.symm,
      ← mul_right_inj' (show (2 : ℤ) ≠ 0, from dec_trivial), ← h, mul_add, ← hx, ← hy],
    have : ∑ x, f (σ x)^2 = ∑ x, f x^2,
    { conv_rhs { rw ← σ.sum_comp } },
    have fin4univ : (univ : finset (fin 4)).1 = 0 ::ₘ 1 ::ₘ 2 ::ₘ 3 ::ₘ 0, from dec_trivial,
    simpa [finset.sum_eq_multiset_sum, fin4univ, multiset.sum_cons, f, add_assoc]
  end⟩

private lemma prime_sum_four_squares (p : ℕ) [hp : _root_.fact p.prime] :
  ∃ a b c d : ℤ, a^2 + b^2 + c^2 + d^2 = p :=
have hm : ∃ m < p, 0 < m ∧ ∃ a b c d : ℤ, a^2 + b^2 + c^2 + d^2 = m * p,
  from let ⟨a, b, k, hk⟩ := exists_sq_add_sq_add_one_eq_k p in
  ⟨k, hk.2, nat.pos_of_ne_zero $
    (λ hk0, by { rw [hk0, int.coe_nat_zero, zero_mul] at hk,
      exact ne_of_gt (show a^2 + b^2 + 1 > 0, from add_pos_of_nonneg_of_pos
        (add_nonneg (sq_nonneg _) (sq_nonneg _)) zero_lt_one) hk.1 }),
    a, b, 1, 0, by simpa [sq] using hk.1⟩,
let m := nat.find hm in
let ⟨a, b, c, d, (habcd : a^2 + b^2 + c^2 + d^2 = m * p)⟩ := (nat.find_spec hm).snd.2 in
by haveI hm0 : _root_.fact (0 < m) := ⟨(nat.find_spec hm).snd.1⟩; exact
have hmp : m < p, from (nat.find_spec hm).fst,
m.mod_two_eq_zero_or_one.elim
  (λ hm2 : m % 2 = 0,
    let ⟨k, hk⟩ := (nat.dvd_iff_mod_eq_zero _ _).2 hm2 in
    have hk0 : 0 < k, from nat.pos_of_ne_zero $ λ _, by { simp [*, lt_irrefl] at * },
    have hkm : k < m, { rw [hk, two_mul], exact (lt_add_iff_pos_left _).2 hk0 },
    false.elim $ nat.find_min hm hkm ⟨lt_trans hkm hmp, hk0,
      sum_four_squares_of_two_mul_sum_four_squares
        (show a^2 + b^2 + c^2 + d^2 = 2 * (k * p),
          by { rw [habcd, hk, int.coe_nat_mul, mul_assoc], simp })⟩)
  (λ hm2 : m % 2 = 1,
    if hm1 : m = 1 then ⟨a, b, c, d, by simp only [hm1, habcd, int.coe_nat_one, one_mul]⟩
    else
      let w := (a : zmod m).val_min_abs, x := (b : zmod m).val_min_abs,
          y := (c : zmod m).val_min_abs, z := (d : zmod m).val_min_abs in
      have hnat_abs : w^2 + x^2 + y^2 + z^2 =
          (w.nat_abs^2 + x.nat_abs^2 + y.nat_abs ^2 + z.nat_abs ^ 2 : ℕ),
        by simp [sq],
      have hwxyzlt : w^2 + x^2 + y^2 + z^2 < m^2,
        from calc w^2 + x^2 + y^2 + z^2
            = (w.nat_abs^2 + x.nat_abs^2 + y.nat_abs ^2 + z.nat_abs ^ 2 : ℕ) : hnat_abs
        ... ≤ ((m / 2) ^ 2 + (m / 2) ^ 2 + (m / 2) ^ 2 + (m / 2) ^ 2 : ℕ) :
          int.coe_nat_le.2 $ add_le_add (add_le_add (add_le_add
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _)
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _))
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _))
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _)
        ... = 4 * (m / 2 : ℕ) ^ 2 : by simp [sq, bit0, bit1, mul_add, add_mul, add_assoc]
        ... < 4 * (m / 2 : ℕ) ^ 2 + ((4 * (m / 2) : ℕ) * (m % 2 : ℕ) + (m % 2 : ℕ)^2) :
          (lt_add_iff_pos_right _).2 (by { rw [hm2, int.coe_nat_one, one_pow, mul_one],
            exact add_pos_of_nonneg_of_pos (int.coe_nat_nonneg _) zero_lt_one })
        ... = m ^ 2 : by { conv_rhs {rw [← nat.mod_add_div m 2]},
          simp [-nat.mod_add_div, mul_add, add_mul, bit0, bit1, mul_comm, mul_assoc, mul_left_comm,
            pow_add, add_comm, add_left_comm] },
      have hwxyzabcd : ((w^2 + x^2 + y^2 + z^2 : ℤ) : zmod m) =
          ((a^2 + b^2 + c^2 + d^2 : ℤ) : zmod m),
        by simp [w, x, y, z, sq],
      have hwxyz0 : ((w^2 + x^2 + y^2 + z^2 : ℤ) : zmod m) = 0,
        by rw [hwxyzabcd, habcd, int.cast_mul, cast_coe_nat, zmod.nat_cast_self, zero_mul],
      let ⟨n, hn⟩ := ((char_p.int_cast_eq_zero_iff _ m _).1 hwxyz0) in
      have hn0 : 0 < n.nat_abs, from int.nat_abs_pos_of_ne_zero (λ hn0,
        have hwxyz0 : (w.nat_abs^2 + x.nat_abs^2 + y.nat_abs^2 + z.nat_abs^2 : ℕ) = 0,
          by { rw [← int.coe_nat_eq_zero, ← hnat_abs], rwa [hn0, mul_zero] at hn },
        have habcd0 : (m : ℤ) ∣ a ∧ (m : ℤ) ∣ b ∧ (m : ℤ) ∣ c ∧ (m : ℤ) ∣ d,
          by simpa [add_eq_zero_iff' (sq_nonneg (_ : ℤ)) (sq_nonneg _),
            pow_two, w, x, y, z, (char_p.int_cast_eq_zero_iff _ m _), and.assoc] using hwxyz0,
        let ⟨ma, hma⟩ := habcd0.1,     ⟨mb, hmb⟩ := habcd0.2.1,
            ⟨mc, hmc⟩ := habcd0.2.2.1, ⟨md, hmd⟩ := habcd0.2.2.2 in
        have hmdvdp : m ∣ p,
          from int.coe_nat_dvd.1 ⟨ma^2 + mb^2 + mc^2 + md^2,
            (mul_right_inj' (show (m : ℤ) ≠ 0, from int.coe_nat_ne_zero_iff_pos.2 hm0.1)).1 $
              by { rw [← habcd, hma, hmb, hmc, hmd], ring }⟩,
        (hp.1.2 _ hmdvdp).elim hm1 (λ hmeqp, by simpa [lt_irrefl, hmeqp] using hmp)),
      have hawbxcydz : ((m : ℕ) : ℤ) ∣ a * w + b * x + c * y + d * z,
        from (char_p.int_cast_eq_zero_iff (zmod m) m _).1 $ by { rw [← hwxyz0], simp, ring },
      have haxbwczdy : ((m : ℕ) : ℤ) ∣ a * x - b * w - c * z + d * y,
        from (char_p.int_cast_eq_zero_iff (zmod m) m _).1 $ by { simp [sub_eq_add_neg], ring },
      have haybzcwdx : ((m : ℕ) : ℤ) ∣ a * y + b * z - c * w - d * x,
        from (char_p.int_cast_eq_zero_iff (zmod m) m _).1 $ by { simp [sub_eq_add_neg], ring },
      have hazbycxdw : ((m : ℕ) : ℤ) ∣ a * z - b * y + c * x - d * w,
        from (char_p.int_cast_eq_zero_iff (zmod m) m _).1 $ by { simp [sub_eq_add_neg], ring },
      let ⟨s, hs⟩ := hawbxcydz, ⟨t, ht⟩ := haxbwczdy, ⟨u, hu⟩ := haybzcwdx, ⟨v, hv⟩ := hazbycxdw in
      have hn_nonneg : 0 ≤ n,
        from nonneg_of_mul_nonneg_left
          (by { erw [← hn], repeat {try {refine add_nonneg _ _}, try {exact sq_nonneg _}} })
          (int.coe_nat_pos.2 hm0.1),
      have hnm : n.nat_abs < m,
        from int.coe_nat_lt.1 (lt_of_mul_lt_mul_left
          (by { rw [int.nat_abs_of_nonneg hn_nonneg, ← hn, ← sq], exact hwxyzlt })
          (int.coe_nat_nonneg m)),
      have hstuv : s^2 + t^2 + u^2 + v^2 = n.nat_abs * p,
        from (mul_right_inj' (show (m^2 : ℤ) ≠ 0, from pow_ne_zero 2
            (int.coe_nat_ne_zero_iff_pos.2 hm0.1))).1 $
          calc (m : ℤ)^2 * (s^2 + t^2 + u^2 + v^2) = ((m : ℕ) * s)^2 + ((m : ℕ) * t)^2 +
              ((m : ℕ) * u)^2 + ((m : ℕ) * v)^2 :
            by { simp [mul_pow], ring }
          ... = (w^2 + x^2 + y^2 + z^2) * (a^2 + b^2 + c^2 + d^2) :
            by { simp only [hs.symm, ht.symm, hu.symm, hv.symm], ring }
          ... = _ : by { rw [hn, habcd, int.nat_abs_of_nonneg hn_nonneg], dsimp [m], ring },
      false.elim $ nat.find_min hm hnm ⟨lt_trans hnm hmp, hn0, s, t, u, v, hstuv⟩)

/-- **Four squares theorem** -/
lemma sum_four_squares : ∀ n : ℕ, ∃ a b c d : ℕ, a^2 + b^2 + c^2 + d^2 = n
| 0 := ⟨0, 0, 0, 0, rfl⟩
| 1 := ⟨1, 0, 0, 0, rfl⟩
| n@(k+2) :=
have hm : _root_.fact (min_fac (k+2)).prime := ⟨min_fac_prime dec_trivial⟩,
have n / min_fac n < n := factors_lemma,
let ⟨a, b, c, d, h₁⟩ := show ∃ a b c d : ℤ, a^2 + b^2 + c^2 + d^2 = min_fac n,
  by exactI prime_sum_four_squares (min_fac (k+2)) in
let ⟨w, x, y, z, h₂⟩ := sum_four_squares (n / min_fac n) in
⟨(a * w - b * x - c * y - d * z).nat_abs,
 (a * x + b * w + c * z - d * y).nat_abs,
 (a * y - b * z + c * w + d * x).nat_abs,
 (a * z + b * y - c * x + d * w).nat_abs,
  begin
    rw [← int.coe_nat_inj', ← nat.mul_div_cancel' (min_fac_dvd (k+2)), int.coe_nat_mul, ← h₁, ← h₂],
    simp [sum_four_sq_mul_sum_four_sq],
  end⟩

end nat
