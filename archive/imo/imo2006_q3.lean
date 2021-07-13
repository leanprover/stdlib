/-
Copyright (c) 2021 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/

import analysis.special_functions.sqrt

/-!
# IMO 2006 Q3

Determine the least real number $M$ such that
$$
\left| ab(a^2 - b^2) + bc(b^2 - c^2) + ca(c^2 - a^2) \right|
≤ M (a^2 + b^2 + c^2)^2
$$
for all real numbers $a$, $b$, $c$.

## Solution

The answer is $M = \frac{9 \sqrt 2}{32}$.

This is essentially a translation of the solution in
https://web.evanchen.cc/exams/IMO-2006-notes.pdf.

It involves making the substitution
`x = a - b`, `y = b - c`, `z = c - a`, `s = a + b + c`.
-/

open real

/-- Replacing `x` and `y` with their average increases the left side. -/
lemma rhs₁ {x y : ℝ} (hxy : 0 ≤ x * y) :
  16 * x ^ 2 * y ^ 2 * (x + y) ^ 2 ≤ ((x + y) ^ 2) ^ 3 :=
begin
  conv_rhs { rw pow_succ' },
  refine mul_le_mul_of_nonneg_right _ (sq_nonneg _),
  apply le_of_sub_nonneg,
  calc  ((x + y) ^ 2) ^ 2 - 16 * x ^ 2 * y ^ 2
      = (x - y) ^ 2 * ((x + y) ^ 2 + 4 * (x * y))
          : by ring
  ... ≥ 0 : mul_nonneg (sq_nonneg _) $ add_nonneg (sq_nonneg _) $
              mul_nonneg zero_lt_four.le hxy
end

lemma four_pow_four_pos : (0 : ℝ) < 4 ^ 4 := pow_pos zero_lt_four _

lemma rhs₂ {s t : ℝ} :
   s * t ^ 3 ≤ (3 * t + s) ^ 4 / 4^4 :=
(le_div_iff four_pow_four_pos).mpr $ le_of_sub_nonneg $
  calc  (3 * t + s) ^ 4 - s * t ^ 3 * 4 ^ 4
      = (s - t) ^ 2 * ((s + 7 * t) ^ 2 + 2 * (4 * t) ^ 2)
          : by ring
  ... ≥ 0 : mul_nonneg (sq_nonneg _) $ add_nonneg (sq_nonneg _) $
              mul_nonneg zero_le_two (sq_nonneg _)

/-- Replacing `x` and `y` with their average decreases the right side. -/
lemma rhs₃ {x y : ℝ} :
  3 * (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) :=
le_of_sub_nonneg $
  calc _ = (x - y) ^ 2 : by ring
     ... ≥ 0           : sq_nonneg _

lemma zero_lt_32 : (0 : ℝ) < 32 := by norm_num

theorem subst_wlog {x y z s : ℝ} (hxy : 0 ≤ x * y) (hxyz : x + y + z = 0) :
  32 * abs (x * y * z * s) ≤ sqrt 2 * (x^2 + y^2 + z^2 + s^2)^2 :=
have hz : (x + y)^2 = z^2 := neg_eq_of_add_eq_zero hxyz ▸ (neg_sq _).symm,
have hs : 0 ≤ 2 * s ^ 2 := mul_nonneg zero_le_two (sq_nonneg s),
have this : _ :=
  calc  (2 * s^2) * (16 * x^2 * y^2 * (x + y)^2)
      ≤ (3 * (x + y)^2 + 2 * s^2)^4 / 4^4 :
          le_trans (mul_le_mul_of_nonneg_left (rhs₁ hxy) hs) rhs₂
  ... ≤ (2 * (x^2 + y^2 + (x + y)^2) + 2 * s^2)^4 / 4^4 :
          div_le_div_of_le four_pow_four_pos.le $ pow_le_pow_of_le_left
            (add_nonneg (mul_nonneg zero_lt_three.le (sq_nonneg _)) hs)
            (add_le_add_right rhs₃ _) _,
le_of_pow_le_pow _ (mul_nonneg (sqrt_nonneg _) (sq_nonneg _)) nat.succ_pos' $
  calc  (32 * abs (x * y * z * s)) ^ 2
      = 32 * ((2 * s^2) * (16 * x^2 * y^2 * (x + y)^2)) :
          by rw [mul_pow, sq_abs, hz]; ring
  ... ≤ 32 * ((2 * (x^2 + y^2 + (x + y)^2) + 2 * s^2)^4 / 4^4) :
          mul_le_mul_of_nonneg_left this zero_lt_32.le
  ... = (sqrt 2 * (x^2 + y^2 + z^2 + s^2)^2)^2 :
          by rw [← div_mul_eq_mul_div_comm, mul_pow, sq_sqrt zero_le_two,
            hz, ← pow_mul, ← mul_add, mul_pow, ← mul_assoc];
            exact congr (congr_arg _ $ by norm_num) rfl

-- only needs `linear_ordered_ring`
/-- Out of three reals, two must have the same sign. -/
lemma mul_nonneg_of_three (x y z : ℝ) :
  0 ≤ x * y ∨ 0 ≤ y * z ∨ 0 ≤ z * x :=
by iterate 3 { rw mul_nonneg_iff };
  have := le_total 0 x; have := le_total 0 y; have := le_total 0 z; itauto

/-- Proof that `M = 9 * sqrt 2 / 32` works with the substitution. -/
theorem subst_proof₁ (x y z s : ℝ) (hxyz : x + y + z = 0) :
  abs (x * y * z * s) ≤ sqrt 2 / 32 * (x^2 + y^2 + z^2 + s^2)^2 :=
begin
  wlog h' := mul_nonneg_of_three x y z using [x y z, y z x, z x y] tactic.skip,
  { rw [div_mul_eq_mul_div, le_div_iff' zero_lt_32],
    exact subst_wlog h' hxyz },
  { intro h,
    rw [add_assoc, add_comm] at h,
    rw [mul_assoc x, mul_comm x, add_assoc (x^2), add_comm (x^2)],
    exact this h },
  { intro h,
    rw [add_comm, ← add_assoc] at h,
    rw [mul_comm _ z, ← mul_assoc, add_comm _ (z^2), ← add_assoc],
    exact this h }
end

lemma lhs_identity (a b c : ℝ) :
  a * b * (a^2 - b^2) + b * c * (b^2 - c^2) + c * a * (c^2 - a^2)
  = (a - b) * (b - c) * (c - a) * -(a + b + c) :=
by ring

theorem proof₁ {a b c : ℝ} :
  abs (a * b * (a^2 - b^2) + b * c * (b^2 - c^2) + c * a * (c^2 - a^2)) ≤
  9 * sqrt 2 / 32 * (a^2 + b^2 + c^2)^2 :=
calc _ = _ : congr_arg _ $ lhs_identity a b c
   ... ≤ _ : subst_proof₁ (a - b) (b - c) (c - a) (-(a + b + c)) (by ring)
   ... = _ : by ring

theorem proof₂ (M : ℝ)
  (h : ∀ a b c : ℝ,
    abs (a * b * (a^2 - b^2) + b * c * (b^2 - c^2) + c * a * (c^2 - a^2)) ≤
    M * (a^2 + b^2 + c^2)^2) :
  9 * sqrt 2 / 32 ≤ M :=
begin
  have h₁ : ∀ x : ℝ,
    (2 - 3 * x - 2) * (2 - (2 + 3 * x)) * (2 + 3 * x - (2 - 3 * x)) *
    -(2 - 3 * x + 2 + (2 + 3 * x)) = -(18 ^ 2 * x ^ 2 * x),
  { intro, ring },
  have h₂ : ∀ x : ℝ, (2 - 3 * x) ^ 2 + 2 ^ 2 + (2 + 3 * x) ^ 2 = 18 * x ^ 2 + 12,
  { intro, ring },
  have := h (2 - 3 * sqrt 2) 2 (2 + 3 * sqrt 2),
  rw [lhs_identity, h₁, h₂, sq_sqrt zero_le_two,
    abs_neg, abs_eq_self.mpr, ← div_le_iff] at this,
  { convert this using 1, ring },
  { apply pow_pos, norm_num },
  { exact mul_nonneg (mul_nonneg (sq_nonneg _) zero_le_two) (sqrt_nonneg _) }
end

theorem imo2006_q3 (M : ℝ) :
  (∀ a b c : ℝ,
    abs (a * b * (a^2 - b^2) + b * c * (b^2 - c^2) + c * a * (c^2 - a^2)) ≤
    M * (a^2 + b^2 + c^2)^2) ↔
  9 * sqrt 2 / 32 ≤ M :=
⟨proof₂ M, λ h _ _ _, le_trans proof₁ $ mul_le_mul_of_nonneg_right h $ sq_nonneg _⟩
