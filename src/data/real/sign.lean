/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Eric Wieser
-/
import data.real.basic

/-!
# Real sign function

This file introduces and contains some results about `real.sign` which maps negative
real numbers to -1, positive real numbers to 1, and 0 to 0.

## Main definitions

 * `real.sign r` is $\begin{cases} -1 & \text{if } r < 0, \\
                               ~~\, 0 & \text{if } r = 0, \\
                               ~~\, 1 & \text{if } r > 0. \end{cases}$

## Tags

sign function
-/

namespace real

/-- The sign function that maps negative real numbers to -1, positive numbers to 1, and 0
otherwise. -/
noncomputable
def sign (r : ℝ) : ℝ :=
if r < 0 then -1 else
if 0 < r then 1 else
0

lemma sign_of_neg {r : ℝ} (hr : r < 0) : sign r = -1 :=
by rw [sign, if_pos hr]

lemma sign_of_pos {r : ℝ} (hr : 0 < r) : sign r = 1 :=
by rw [sign, if_pos hr, if_neg hr.not_lt]

@[simp]
lemma sign_zero : sign 0 = 0 :=
by rw [sign, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

@[simp]
lemma sign_one : sign 1 = 1 :=
sign_of_pos $ by norm_num

lemma sign_apply_eq (r : ℝ) : sign r = -1 ∨ sign r = 0 ∨ sign r = 1 :=
begin
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ),
  { exact (or.inl $ sign_of_neg hn) },
  { exact (or.inr $ or.inl $ sign_zero) },
  { exact (or.inr $ or.inr $ sign_of_pos hp) },
end

/-- This lemma is useful for working with `units ℝ` -/
lemma sign_apply_eq_of_ne_zero (r : ℝ) (h : r ≠ 0) : sign r = -1 ∨ sign r = 1 :=
begin
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ),
  { exact (or.inl $ sign_of_neg hn) },
  { exact (h rfl).elim },
  { exact (or.inr $ sign_of_pos hp) },
end

@[simp]
lemma sign_eq_zero_iff {r : ℝ} : sign r = 0 ↔ r = 0 :=
begin
  refine ⟨λ h, _, λ h, h.symm ▸ sign_zero⟩,
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ),
  { rw [sign_of_neg hn, neg_eq_zero] at h, exact (one_ne_zero h).elim },
  { refl },
  { rw sign_of_pos hp at h, exact (one_ne_zero h).elim },
end

lemma sign_int_cast (z : ℤ) : sign (z : ℝ) = ↑(int.sign z) :=
begin
  obtain hn | rfl | hp := lt_trichotomy z (0 : ℤ),
  { rw [sign_of_neg (int.cast_lt_zero.mpr hn), int.sign_eq_neg_one_of_neg hn, int.cast_neg,
      int.cast_one], },
  { rw [int.cast_zero, sign_zero, int.sign_zero, int.cast_zero], },
  { rw [sign_of_pos (int.cast_pos.mpr hp), int.sign_eq_one_of_pos hp, int.cast_one] }
end

lemma sign_neg {r : ℝ} : sign (-r) = - sign r :=
begin
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ),
  { rw [sign_of_neg hn, sign_of_pos (neg_pos.mpr hn), neg_neg] },
  { rw [sign_zero, neg_zero, sign_zero] },
  { rw [sign_of_pos hp, sign_of_neg (neg_lt_zero.mpr hp)] },
end

lemma sign_mul_nonneg (r : ℝ) : 0 ≤ sign r * r :=
begin
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ),
  { rw sign_of_neg hn,
    exact mul_nonneg_of_nonpos_of_nonpos (by norm_num) hn.le },
  { rw mul_zero, },
  { rw [sign_of_pos hp, one_mul],
    exact hp.le }
end

lemma sign_mul_pos_of_ne_zero (r : ℝ) (hr : r ≠ 0) : 0 < sign r * r :=
begin
  refine lt_of_le_of_ne (sign_mul_nonneg r) (λ h, hr _),
  have hs0 := (zero_eq_mul.mp h).resolve_right hr,
  exact sign_eq_zero_iff.mp hs0,
end

@[simp]
lemma inv_sign (r : ℝ) : (sign r)⁻¹ = sign r :=
begin
  obtain (hn | hz | hp) := sign_apply_eq r,
  { rw hn, norm_num },
  { rw hz, exact inv_zero },
  { rw hp, exact inv_one }
end

@[simp]
lemma sign_inv (r : ℝ) : sign r⁻¹ = sign r :=
begin
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ),
  { rw [sign_of_neg hn, sign_of_neg (inv_lt_zero.mpr hn)] },
  { rw [sign_zero, inv_zero, sign_zero] },
  { rw [sign_of_pos hp, sign_of_pos (inv_pos.mpr hp)] },
end

end real
