/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import data.nat.basic
import algebra.group_power.order

/-! # `nat.pow`

Results on the power operation on natural numbers.
-/

namespace nat

/-! ### `pow` -/

-- This is redundant with `canonically_ordered_semiring.pow_le_pow_of_le_left`,
-- but `canonically_ordered_semiring` is not such an obvious abstraction, and also quite long.
-- So, we leave a version in the `nat` namespace as well.
-- (The global `pow_le_pow_of_le_left` needs an extra hypothesis `0 ≤ x`.)
protected theorem pow_le_pow_of_le_left {x y : ℕ} (H : x ≤ y) : ∀ i : ℕ, x^i ≤ y^i :=
canonically_ordered_semiring.pow_le_pow_of_le_left H

theorem pow_le_pow_of_le_right {x : ℕ} (H : x > 0) {i : ℕ} : ∀ {j}, i ≤ j → x^i ≤ x^j
| 0        h := by rw eq_zero_of_le_zero h; apply le_refl
| (succ j) h := h.lt_or_eq_dec.elim
  (λhl, by rw [pow_succ', ← nat.mul_one (x^i)]; exact
    nat.mul_le_mul (pow_le_pow_of_le_right $ le_of_lt_succ hl) H)
  (λe, by rw e; refl)

theorem pow_lt_pow_of_lt_left {x y : ℕ} (H : x < y) {i} (h : 0 < i) : x^i < y^i :=
begin
  cases i with i, { exact absurd h (not_lt_zero _) },
  rw [pow_succ', pow_succ'],
  exact nat.mul_lt_mul' (nat.pow_le_pow_of_le_left (le_of_lt H) _) H
    (pow_pos (lt_of_le_of_lt (zero_le _) H) _)
end

theorem pow_lt_pow_of_lt_right {x : ℕ} (H : x > 1) {i j : ℕ} (h : i < j) : x^i < x^j :=
begin
  have xpos := lt_of_succ_lt H,
  refine lt_of_lt_of_le _ (pow_le_pow_of_le_right xpos h),
  rw [← nat.mul_one (x^i), pow_succ'],
  exact nat.mul_lt_mul_of_pos_left H (pow_pos xpos _)
end

-- TODO: Generalize?
lemma pow_lt_pow_succ {p : ℕ} (h : 1 < p) (n : ℕ) : p^n < p^(n+1) :=
suffices 1*p^n < p*p^n, by simpa [pow_succ],
nat.mul_lt_mul_of_pos_right h (pow_pos (lt_of_succ_lt h) n)

lemma lt_pow_self {p : ℕ} (h : 1 < p) : ∀ n : ℕ, n < p ^ n
| 0 := by simp [zero_lt_one]
| (n+1) := calc
  n + 1 < p^n + 1 : nat.add_lt_add_right (lt_pow_self _) _
    ... ≤ p ^ (n+1) : pow_lt_pow_succ h _

lemma lt_two_pow (n : ℕ) : n < 2^n :=
lt_pow_self dec_trivial n

lemma one_le_pow (n m : ℕ) (h : 0 < m) : 1 ≤ m^n :=
by { rw ←one_pow n, exact nat.pow_le_pow_of_le_left h n }
lemma one_le_pow' (n m : ℕ) : 1 ≤ (m+1)^n := one_le_pow n (m+1) (succ_pos m)

lemma one_le_two_pow (n : ℕ) : 1 ≤ 2^n := one_le_pow n 2 dec_trivial

lemma one_lt_pow (n m : ℕ) (h₀ : 0 < n) (h₁ : 1 < m) : 1 < m^n :=
by { rw ←one_pow n, exact pow_lt_pow_of_lt_left h₁ h₀ }
lemma one_lt_pow' (n m : ℕ) : 1 < (m+2)^(n+1) :=
one_lt_pow (n+1) (m+2) (succ_pos n) (nat.lt_of_sub_eq_succ rfl)

lemma one_lt_two_pow (n : ℕ) (h₀ : 0 < n) : 1 < 2^n := one_lt_pow n 2 h₀ dec_trivial
lemma one_lt_two_pow' (n : ℕ) : 1 < 2^(n+1) := one_lt_pow (n+1) 2 (succ_pos n) dec_trivial

lemma pow_right_strict_mono {x : ℕ} (k : 2 ≤ x) : strict_mono (λ (n : ℕ), x^n) :=
λ _ _, pow_lt_pow_of_lt_right k

lemma pow_le_iff_le_right {x m n : ℕ} (k : 2 ≤ x) : x^m ≤ x^n ↔ m ≤ n :=
strict_mono.le_iff_le (pow_right_strict_mono k)

lemma pow_lt_iff_lt_right {x m n : ℕ} (k : 2 ≤ x) : x^m < x^n ↔ m < n :=
strict_mono.lt_iff_lt (pow_right_strict_mono k)

lemma pow_right_injective {x : ℕ} (k : 2 ≤ x) : function.injective (λ (n : ℕ), x^n) :=
strict_mono.injective (pow_right_strict_mono k)

lemma pow_left_strict_mono {m : ℕ} (k : 1 ≤ m) : strict_mono (λ (x : ℕ), x^m) :=
λ _ _ h, pow_lt_pow_of_lt_left h k

lemma mul_lt_mul_pow_succ {n a q : ℕ} (a0 : 0 < a) (q1 : 1 < q) :
  n * q < a * q ^ (n + 1) :=
begin
  rw [pow_succ', ← mul_assoc, mul_lt_mul_right (zero_lt_one.trans q1)],
  exact lt_mul_of_one_le_of_lt (nat.succ_le_iff.mpr a0) (nat.lt_pow_self q1 n),
end

end nat

lemma strict_mono.nat_pow {n : ℕ} (hn : 1 ≤ n) {f : ℕ → ℕ} (hf : strict_mono f) :
  strict_mono (λ m, (f m) ^ n) :=
(nat.pow_left_strict_mono hn).comp hf

namespace nat

lemma pow_le_iff_le_left {m x y : ℕ} (k : 1 ≤ m) : x^m ≤ y^m ↔ x ≤ y :=
strict_mono.le_iff_le (pow_left_strict_mono k)

lemma pow_lt_iff_lt_left {m x y : ℕ} (k : 1 ≤ m) : x^m < y^m ↔ x < y :=
strict_mono.lt_iff_lt (pow_left_strict_mono k)

lemma pow_left_injective {m : ℕ} (k : 1 ≤ m) : function.injective (λ (x : ℕ), x^m) :=
strict_mono.injective (pow_left_strict_mono k)

theorem sq_sub_sq (a b : ℕ) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
by { rw [sq, sq], exact nat.mul_self_sub_mul_self_eq a b }

alias nat.sq_sub_sq ← nat.pow_two_sub_pow_two

/-! ### `pow` and `mod` / `dvd` -/

theorem mod_pow_succ {b : ℕ} (b_pos : 0 < b) (w m : ℕ)
: m % (b^succ w) = b * (m/b % b^w) + m % b :=
begin
  apply nat.strong_induction_on m,
  clear m,
  intros p IH,
  cases lt_or_ge p (b^succ w) with h₁ h₁,
  -- base case: p < b^succ w
  { have h₂ : p / b < b^w,
    { rw [div_lt_iff_lt_mul p _ b_pos],
      simpa [pow_succ'] using h₁ },
    rw [mod_eq_of_lt h₁, mod_eq_of_lt h₂],
    simp [div_add_mod] },
  -- step: p ≥ b^succ w
  { -- Generate condition for induction hypothesis
    have h₂ : p - b^succ w < p,
    { apply sub_lt_of_pos_le _ _ (pow_pos b_pos _) h₁ },

    -- Apply induction
    rw [mod_eq_sub_mod h₁, IH _ h₂],
    -- Normalize goal and h1
    simp only [pow_succ],
    simp only [ge, pow_succ] at h₁,
    -- Pull subtraction outside mod and div
    rw [sub_mul_mod _ _ _ h₁, sub_mul_div _ _ _ h₁],
    -- Cancel subtraction inside mod b^w
    have p_b_ge :  b^w ≤ p / b,
    { rw [le_div_iff_mul_le _ _ b_pos, mul_comm],
      exact h₁ },
    rw [eq.symm (mod_eq_sub_mod p_b_ge)] }
end

lemma pow_dvd_pow_iff_pow_le_pow {k l : ℕ} : Π {x : ℕ} (w : 0 < x), x^k ∣ x^l ↔ x^k ≤ x^l
| (x+1) w :=
begin
  split,
  { intro a, exact le_of_dvd (pow_pos (succ_pos x) l) a, },
  { intro a, cases x with x,
    { simp only [one_pow], },
    { have le := (pow_le_iff_le_right (le_add_left _ _)).mp a,
      use (x+2)^(l-k),
      rw [←pow_add, add_comm k, nat.sub_add_cancel le], } }
end

/-- If `1 < x`, then `x^k` divides `x^l` if and only if `k` is at most `l`. -/
lemma pow_dvd_pow_iff_le_right {x k l : ℕ} (w : 1 < x) : x^k ∣ x^l ↔ k ≤ l :=
by rw [pow_dvd_pow_iff_pow_le_pow (lt_of_succ_lt w), pow_le_iff_le_right w]

lemma pow_dvd_pow_iff_le_right' {b k l : ℕ} : (b+2)^k ∣ (b+2)^l ↔ k ≤ l :=
pow_dvd_pow_iff_le_right (nat.lt_of_sub_eq_succ rfl)

lemma not_pos_pow_dvd : ∀ {p k : ℕ} (hp : 1 < p) (hk : 1 < k), ¬ p^k ∣ p
| (succ p) (succ k) hp hk h :=
  have succ p * (succ p)^k ∣ succ p * 1, by simpa [pow_succ] using h,
  have (succ p) ^ k ∣ 1, from dvd_of_mul_dvd_mul_left (succ_pos _) this,
  have he : (succ p) ^ k = 1, from eq_one_of_dvd_one this,
  have k < (succ p) ^ k, from lt_pow_self hp k,
  have k < 1, by rwa [he] at this,
  have k = 0, from eq_zero_of_le_zero $ le_of_lt_succ this,
  have 1 < 1, by rwa [this] at hk,
  absurd this dec_trivial

lemma pow_dvd_of_le_of_pow_dvd {p m n k : ℕ} (hmn : m ≤ n) (hdiv : p ^ n ∣ k) : p ^ m ∣ k :=
have p ^ m ∣ p ^ n, from pow_dvd_pow _ hmn,
dvd_trans this hdiv

lemma dvd_of_pow_dvd {p k m : ℕ} (hk : 1 ≤ k) (hpk : p^k ∣ m) : p ∣ m :=
by rw ←pow_one p; exact pow_dvd_of_le_of_pow_dvd hk hpk

lemma pow_div {x m n : ℕ} (h : n ≤ m) (hx : 0 < x) : x ^ m / x ^ n = x ^ (m - n) :=
by rw [nat.div_eq_iff_eq_mul_left (pow_pos hx n) (pow_dvd_pow _ h), pow_sub_mul_pow _ h]

/-! ### `shiftl` and `shiftr` -/

lemma shiftl_eq_mul_pow (m) : ∀ n, shiftl m n = m * 2 ^ n
| 0     := (nat.mul_one _).symm
| (k+1) := show bit0 (shiftl m k) = m * (2 * 2 ^ k),
  by rw [bit0_val, shiftl_eq_mul_pow, mul_left_comm, mul_comm 2]

lemma shiftl'_tt_eq_mul_pow (m) : ∀ n, shiftl' tt m n + 1 = (m + 1) * 2 ^ n
| 0     := by simp [shiftl, shiftl', pow_zero, nat.one_mul]
| (k+1) :=
begin
  change bit1 (shiftl' tt m k) + 1 = (m + 1) * (2 * 2 ^ k),
  rw bit1_val,
  change 2 * (shiftl' tt m k + 1) = _,
  rw [shiftl'_tt_eq_mul_pow, mul_left_comm, mul_comm 2],
end

lemma one_shiftl (n) : shiftl 1 n = 2 ^ n :=
(shiftl_eq_mul_pow _ _).trans (nat.one_mul _)

@[simp] lemma zero_shiftl (n) : shiftl 0 n = 0 :=
(shiftl_eq_mul_pow _ _).trans (nat.zero_mul _)

lemma shiftr_eq_div_pow (m) : ∀ n, shiftr m n = m / 2 ^ n
| 0     := (nat.div_one _).symm
| (k+1) := (congr_arg div2 (shiftr_eq_div_pow k)).trans $
           by rw [div2_val, nat.div_div_eq_div_mul, mul_comm]; refl

@[simp] lemma zero_shiftr (n) : shiftr 0 n = 0 :=
(shiftr_eq_div_pow _ _).trans (nat.zero_div _)

theorem shiftl'_ne_zero_left (b) {m} (h : m ≠ 0) (n) : shiftl' b m n ≠ 0 :=
by induction n; simp [shiftl', bit_ne_zero, *]

theorem shiftl'_tt_ne_zero (m) : ∀ {n} (h : n ≠ 0), shiftl' tt m n ≠ 0
| 0        h := absurd rfl h
| (succ n) _ := nat.bit1_ne_zero _

/-! ### `size` -/

@[simp] theorem size_zero : size 0 = 0 := by simp [size]

@[simp] theorem size_bit {b n} (h : bit b n ≠ 0) : size (bit b n) = succ (size n) :=
begin
  rw size,
  conv { to_lhs, rw [binary_rec], simp [h] },
  rw div2_bit,
end

@[simp] theorem size_bit0 {n} (h : n ≠ 0) : size (bit0 n) = succ (size n) :=
@size_bit ff n (nat.bit0_ne_zero h)

@[simp] theorem size_bit1 (n) : size (bit1 n) = succ (size n) :=
@size_bit tt n (nat.bit1_ne_zero n)

@[simp] theorem size_one : size 1 = 1 :=
show size (bit1 0) = 1, by rw [size_bit1, size_zero]

@[simp] theorem size_shiftl' {b m n} (h : shiftl' b m n ≠ 0) :
  size (shiftl' b m n) = size m + n :=
begin
  induction n with n IH; simp [shiftl'] at h ⊢,
  rw [size_bit h, nat.add_succ],
  by_cases s0 : shiftl' b m n = 0; [skip, rw [IH s0]],
  rw s0 at h ⊢,
  cases b, {exact absurd rfl h},
  have : shiftl' tt m n + 1 = 1 := congr_arg (+1) s0,
  rw [shiftl'_tt_eq_mul_pow] at this,
  have m0 := succ.inj (eq_one_of_dvd_one ⟨_, this.symm⟩),
  subst m0,
  simp at this,
  have : n = 0 := eq_zero_of_le_zero (le_of_not_gt $ λ hn,
    ne_of_gt (pow_lt_pow_of_lt_right dec_trivial hn) this),
  subst n, refl
end

@[simp] theorem size_shiftl {m} (h : m ≠ 0) (n) :
  size (shiftl m n) = size m + n :=
size_shiftl' (shiftl'_ne_zero_left _ h _)

theorem lt_size_self (n : ℕ) : n < 2^size n :=
begin
  rw [← one_shiftl],
  have : ∀ {n}, n = 0 → n < shiftl 1 (size n), { simp },
  apply binary_rec _ _ n, {apply this rfl},
  intros b n IH,
  by_cases bit b n = 0, {apply this h},
  rw [size_bit h, shiftl_succ],
  exact bit_lt_bit0 _ IH
end

theorem size_le {m n : ℕ} : size m ≤ n ↔ m < 2^n :=
⟨λ h, lt_of_lt_of_le (lt_size_self _) (pow_le_pow_of_le_right dec_trivial h),
begin
  rw [← one_shiftl], revert n,
  apply binary_rec _ _ m,
  { intros n h, simp },
  { intros b m IH n h,
    by_cases e : bit b m = 0, { simp [e] },
    rw [size_bit e],
    cases n with n,
    { exact e.elim (eq_zero_of_le_zero (le_of_lt_succ h)) },
    { apply succ_le_succ (IH _),
      apply lt_imp_lt_of_le_imp_le (λ h', bit0_le_bit _ h') h } }
end⟩

theorem lt_size {m n : ℕ} : m < size n ↔ 2^m ≤ n :=
by rw [← not_lt, decidable.iff_not_comm, not_lt, size_le]

theorem size_pos {n : ℕ} : 0 < size n ↔ 0 < n :=
by rw lt_size; refl

theorem size_eq_zero {n : ℕ} : size n = 0 ↔ n = 0 :=
by have := @size_pos n; simp [pos_iff_ne_zero] at this;
   exact decidable.not_iff_not.1 this

theorem size_pow {n : ℕ} : size (2^n) = n+1 :=
le_antisymm
  (size_le.2 $ pow_lt_pow_of_lt_right dec_trivial (lt_succ_self _))
  (lt_size.2 $ le_refl _)

theorem size_le_size {m n : ℕ} (h : m ≤ n) : size m ≤ size n :=
size_le.2 $ lt_of_le_of_lt h (lt_size_self _)

end nat
