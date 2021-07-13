/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta
-/
import data.nat.factorial

/-!
# Binomial coefficients

This file defines binomial coefficients and proves simple lemmas (i.e. those not
requiring more imports).

## Main definition and results

* `nat.choose`: binomial coefficients, defined inductively
* `nat.choose_eq_factorial_div_factorial`: a proof that `choose n k = n! / (k! * (n - k)!)`
* `nat.choose_symm`: symmetry of binomial coefficients
* `nat.choose_le_succ_of_lt_half_left`: `choose n k` is increasing for small values of `k`
* `nat.choose_le_middle`: `choose n r` is maximised when `r` is `n/2`
* `nat.desc_factorial_eq_factorial_mul_choose`: Relates binomial coefficients to the descending
  factorial. This is used to prove `nat.choose_le_pow` and variants. We provide similar statements
  for the ascending factorial.

-/

open_locale nat

namespace nat

/-- `choose n k` is the number of `k`-element subsets in an `n`-element set. Also known as binomial
coefficients. -/
def choose : ℕ → ℕ → ℕ
| _             0 := 1
| 0       (k + 1) := 0
| (n + 1) (k + 1) := choose n k + choose n (k + 1)

@[simp] lemma choose_zero_right (n : ℕ) : choose n 0 = 1 := by cases n; refl

@[simp] lemma choose_zero_succ (k : ℕ) : choose 0 (succ k) = 0 := rfl

lemma choose_succ_succ (n k : ℕ) : choose (succ n) (succ k) = choose n k + choose n (succ k) := rfl

lemma choose_eq_zero_of_lt : ∀ {n k}, n < k → choose n k = 0
| _             0 hk := absurd hk dec_trivial
| 0       (k + 1) hk := choose_zero_succ _
| (n + 1) (k + 1) hk :=
  have hnk : n < k, from lt_of_succ_lt_succ hk,
  have hnk1 : n < k + 1, from lt_of_succ_lt hk,
  by rw [choose_succ_succ, choose_eq_zero_of_lt hnk, choose_eq_zero_of_lt hnk1]

@[simp] lemma choose_self (n : ℕ) : choose n n = 1 :=
by induction n; simp [*, choose, choose_eq_zero_of_lt (lt_succ_self _)]

@[simp] lemma choose_succ_self (n : ℕ) : choose n (succ n) = 0 :=
choose_eq_zero_of_lt (lt_succ_self _)

@[simp] lemma choose_one_right (n : ℕ) : choose n 1 = n :=
by induction n; simp [*, choose, add_comm]

/- The `n+1`-st triangle number is `n` more than the `n`-th triangle number -/
lemma triangle_succ (n : ℕ) : (n + 1) * ((n + 1) - 1) / 2 = n * (n - 1) / 2 + n :=
begin
  rw [← add_mul_div_left, mul_comm 2 n, ← mul_add, nat.add_sub_cancel, mul_comm],
  cases n; refl, apply zero_lt_succ
end

/-- `choose n 2` is the `n`-th triangle number. -/
lemma choose_two_right (n : ℕ) : choose n 2 = n * (n - 1) / 2 :=
begin
  induction n with n ih,
  simp,
  {rw triangle_succ n, simp [choose, ih], rw add_comm},
end

lemma choose_pos : ∀ {n k}, k ≤ n → 0 < choose n k
| 0             _ hk := by rw [eq_zero_of_le_zero hk]; exact dec_trivial
| (n + 1)       0 hk := by simp; exact dec_trivial
| (n + 1) (k + 1) hk := by rw choose_succ_succ;
    exact add_pos_of_pos_of_nonneg (choose_pos (le_of_succ_le_succ hk)) (nat.zero_le _)

lemma succ_mul_choose_eq : ∀ n k, succ n * choose n k = choose (succ n) (succ k) * succ k
| 0             0 := dec_trivial
| 0       (k + 1) := by simp [choose]
| (n + 1)       0 := by simp
| (n + 1) (k + 1) :=
  by rw [choose_succ_succ (succ n) (succ k), add_mul, ←succ_mul_choose_eq, mul_succ,
  ←succ_mul_choose_eq, add_right_comm, ←mul_add, ←choose_succ_succ, ←succ_mul]

lemma choose_mul_factorial_mul_factorial : ∀ {n k}, k ≤ n → choose n k * k! * (n - k)! = n!
| 0              _ hk := by simp [eq_zero_of_le_zero hk]
| (n + 1)        0 hk := by simp
| (n + 1) (succ k) hk :=
begin
  cases lt_or_eq_of_le hk with hk₁ hk₁,
  { have h : choose n k * k.succ! * (n-k)! = k.succ * n! :=
      by rw ← choose_mul_factorial_mul_factorial (le_of_succ_le_succ hk);
      simp [factorial_succ, mul_comm, mul_left_comm],
    have h₁ : (n - k)! = (n - k) * (n - k.succ)! :=
      by rw [← succ_sub_succ, succ_sub (le_of_lt_succ hk₁), factorial_succ],
    have h₂ : choose n (succ k) * k.succ! * ((n - k) * (n - k.succ)!) = (n - k) * n! :=
      by rw ← choose_mul_factorial_mul_factorial (le_of_lt_succ hk₁);
      simp [factorial_succ, mul_comm, mul_left_comm, mul_assoc],
    have h₃ : k * n! ≤ n * n! := mul_le_mul_right _ (le_of_succ_le_succ hk),
  rw [choose_succ_succ, add_mul, add_mul, succ_sub_succ, h, h₁, h₂, ← add_one, add_mul,
      nat.mul_sub_right_distrib, factorial_succ, ← nat.add_sub_assoc h₃, add_assoc, ← add_mul,
      nat.add_sub_cancel_left, add_comm] },
  { simp [hk₁, mul_comm, choose, nat.sub_self] }
end

theorem choose_eq_factorial_div_factorial {n k : ℕ} (hk : k ≤ n) :
  choose n k = n! / (k! * (n - k)!) :=
begin
  rw [← choose_mul_factorial_mul_factorial hk, mul_assoc],
  exact (mul_div_left _ (mul_pos (factorial_pos _) (factorial_pos _))).symm
end

lemma add_choose (i j : ℕ) : (i + j).choose j = (i + j)! / (i! * j!) :=
by rw [choose_eq_factorial_div_factorial (le_add_left j i), nat.add_sub_cancel, mul_comm]

lemma add_choose_mul_factorial_mul_factorial (i j : ℕ) : (i + j).choose j * i! * j! = (i + j)! :=
by rw [← choose_mul_factorial_mul_factorial (le_add_left _ _), nat.add_sub_cancel, mul_right_comm]

theorem factorial_mul_factorial_dvd_factorial {n k : ℕ} (hk : k ≤ n) : k! * (n - k)! ∣ n! :=
by rw [←choose_mul_factorial_mul_factorial hk, mul_assoc]; exact dvd_mul_left _ _

lemma factorial_mul_factorial_dvd_factorial_add (i j : ℕ) :
  i! * j! ∣ (i + j)! :=
begin
  convert factorial_mul_factorial_dvd_factorial (le.intro rfl),
  rw nat.add_sub_cancel_left
end

@[simp] lemma choose_symm {n k : ℕ} (hk : k ≤ n) : choose n (n-k) = choose n k :=
by rw [choose_eq_factorial_div_factorial hk, choose_eq_factorial_div_factorial (sub_le _ _),
  nat.sub_sub_self hk, mul_comm]

lemma choose_symm_of_eq_add {n a b : ℕ} (h : n = a + b) : nat.choose n a = nat.choose n b :=
by { convert nat.choose_symm (nat.le_add_left _ _), rw nat.add_sub_cancel}

lemma choose_symm_add {a b : ℕ} : choose (a+b) a = choose (a+b) b :=
choose_symm_of_eq_add rfl

lemma choose_symm_half (m : ℕ) : choose (2 * m + 1) (m + 1) = choose (2 * m + 1) m :=
by { apply choose_symm_of_eq_add,
  rw [add_comm m 1, add_assoc 1 m m, add_comm (2 * m) 1, two_mul m] }

lemma choose_succ_right_eq (n k : ℕ) : choose n (k + 1) * (k + 1) = choose n k * (n - k) :=
begin
  have e : (n+1) * choose n k = choose n k * (k+1) + choose n (k+1) * (k+1),
    rw [← right_distrib, ← choose_succ_succ, succ_mul_choose_eq],
  rw [← nat.sub_eq_of_eq_add e, mul_comm, ← nat.mul_sub_left_distrib, nat.add_sub_add_right]
end

@[simp] lemma choose_succ_self_right : ∀ (n:ℕ), (n+1).choose n = n+1
| 0     := rfl
| (n+1) := by rw [choose_succ_succ, choose_succ_self_right, choose_self]

lemma choose_mul_succ_eq (n k : ℕ) :
  (n.choose k) * (n + 1) = ((n+1).choose k) * (n + 1 - k) :=
begin
  induction k with k ih, { simp },
  obtain hk | hk := le_or_lt (k + 1) (n + 1),
  { rw [choose_succ_succ, add_mul, succ_sub_succ, ←choose_succ_right_eq, ←succ_sub_succ,
      nat.mul_sub_left_distrib, nat.add_sub_cancel' (mul_le_mul_left _ hk)] },
  rw [choose_eq_zero_of_lt hk, choose_eq_zero_of_lt (n.lt_succ_self.trans hk), zero_mul, zero_mul],
end

lemma asc_factorial_eq_factorial_mul_choose (n k : ℕ) :
  n.asc_factorial k = k! * (n + k).choose k :=
begin
  rw mul_comm,
  apply mul_right_cancel' (factorial_ne_zero (n + k - k)),
  rw [choose_mul_factorial_mul_factorial, nat.add_sub_cancel, ←factorial_mul_asc_factorial,
    mul_comm],
  exact le_add_left k n,
end

lemma factorial_dvd_asc_factorial (n k : ℕ) : k! ∣ n.asc_factorial k :=
⟨(n+k).choose k, asc_factorial_eq_factorial_mul_choose _ _⟩

lemma choose_eq_asc_factorial_div_factorial (n k : ℕ) :
  (n + k).choose k = n.asc_factorial k / k! :=
begin
  apply mul_left_cancel' (factorial_ne_zero k),
  rw ←asc_factorial_eq_factorial_mul_choose,
  exact (nat.mul_div_cancel' $ factorial_dvd_asc_factorial _ _).symm,
end

lemma desc_factorial_eq_factorial_mul_choose (n k : ℕ) : n.desc_factorial k = k! * n.choose k :=
begin
  obtain h | h := nat.lt_or_ge n k,
  { rw [desc_factorial_eq_zero_iff_lt.2 h, choose_eq_zero_of_lt h, mul_zero] },
  rw mul_comm,
  apply mul_right_cancel' (factorial_ne_zero (n - k)),
  rw [choose_mul_factorial_mul_factorial h, ←factorial_mul_desc_factorial h, mul_comm],
end

lemma factorial_dvd_desc_factorial (n k : ℕ) : k! ∣ n.desc_factorial k :=
⟨n.choose k, desc_factorial_eq_factorial_mul_choose _ _⟩

lemma choose_eq_desc_factorial_div_factorial (n k : ℕ) : n.choose k = n.desc_factorial k / k! :=
begin
  apply mul_left_cancel' (factorial_ne_zero k),
  rw ←desc_factorial_eq_factorial_mul_choose,
  exact (nat.mul_div_cancel' $ factorial_dvd_desc_factorial _ _).symm,
end

/-! ### Inequalities -/

/-- Show that `nat.choose` is increasing for small values of the right argument. -/
lemma choose_le_succ_of_lt_half_left {r n : ℕ} (h : r < n/2) :
  choose n r ≤ choose n (r+1) :=
begin
  refine le_of_mul_le_mul_right _ (nat.lt_sub_left_of_add_lt (lt_of_lt_of_le h (n.div_le_self 2))),
  rw ← choose_succ_right_eq,
  apply nat.mul_le_mul_left,
  rw [←lt_iff_add_one_le, nat.lt_sub_left_iff_add_lt, ←mul_two],
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right h zero_lt_two) (n.div_mul_le_self 2),
end

/-- Show that for small values of the right argument, the middle value is largest. -/
private lemma choose_le_middle_of_le_half_left {n r : ℕ} (hr : r ≤ n/2) :
  choose n r ≤ choose n (n/2) :=
decreasing_induction
  (λ _ k a,
      (eq_or_lt_of_le a).elim
        (λ t, t.symm ▸ le_refl _)
        (λ h, (choose_le_succ_of_lt_half_left h).trans (k h)))
  hr (λ _, le_rfl) hr

/-- `choose n r` is maximised when `r` is `n/2`. -/
lemma choose_le_middle (r n : ℕ) : choose n r ≤ choose n (n/2) :=
begin
  cases le_or_gt r n with b b,
  { cases le_or_lt r (n/2) with a h,
    { apply choose_le_middle_of_le_half_left a },
    { rw ← choose_symm b,
      apply choose_le_middle_of_le_half_left,
      rw [div_lt_iff_lt_mul' zero_lt_two] at h,
      rw [le_div_iff_mul_le' zero_lt_two, nat.mul_sub_right_distrib, nat.sub_le_iff,
          mul_two, nat.add_sub_cancel],
      exact le_of_lt h } },
  { rw choose_eq_zero_of_lt b,
    apply zero_le }
end

end nat
