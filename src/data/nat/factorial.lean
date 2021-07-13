/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes, Floris van Doorn, Yaël Dillies
-/
import data.nat.basic
import data.nat.pow

/-!
# Factorial and variants

This file defines the factorial, along with the ascending and descending variants.

## Main declarations

* `factorial`: The factorial.
* `asc_factorial`: The ascending factorial. Note that it runs from `n + 1` to `n + k` and *not*
  from`n`
  to `n + k - 1`. We might want to change that in the future.
* `desc_factorial`: The descending factorial. It runs from `n - k` to `n`.
-/

namespace nat

/-- `nat.factorial n` is the factorial of `n`. -/
@[simp] def factorial : ℕ → ℕ
| 0        := 1
| (succ n) := succ n * factorial n

localized "notation n `!`:10000 := nat.factorial n" in nat

section factorial

variables {m n : ℕ}

@[simp] theorem factorial_zero : 0! = 1 := rfl

@[simp] theorem factorial_succ (n : ℕ) : n.succ! = succ n * n! := rfl

@[simp] theorem factorial_one : 1! = 1 := rfl

theorem mul_factorial_pred (hn : 0 < n) : n * (n - 1)! = n! :=
nat.sub_add_cancel hn ▸ rfl

theorem factorial_pos : ∀ n, 0 < n!
| 0        := zero_lt_one
| (succ n) := mul_pos (succ_pos _) (factorial_pos n)

theorem factorial_ne_zero (n : ℕ) : n! ≠ 0 := ne_of_gt (factorial_pos _)

theorem factorial_dvd_factorial {m n} (h : m ≤ n) : m! ∣ n! :=
begin
  induction n with n IH; simp,
  { have := eq_zero_of_le_zero h, subst m, simp },
  obtain he | hl := h.eq_or_lt,
  { subst m, simp },
  exact dvd_mul_of_dvd_right (IH (le_of_lt_succ hl)) _,
end

theorem dvd_factorial : ∀ {m n}, 0 < m → m ≤ n → m ∣ n!
| (succ m) n _ h := dvd_of_mul_right_dvd (factorial_dvd_factorial h)

@[mono] theorem factorial_le {m n} (h : m ≤ n) : m! ≤ n! :=
le_of_dvd (factorial_pos _) (factorial_dvd_factorial h)

lemma factorial_mul_pow_le_factorial : ∀ {m n : ℕ}, m! * m.succ ^ n ≤ (m + n)!
| m 0     := by simp
| m (n+1) :=
by  rw [← add_assoc, nat.factorial_succ, mul_comm (nat.succ _), pow_succ', ← mul_assoc];
  exact mul_le_mul factorial_mul_pow_le_factorial
    (nat.succ_le_succ (nat.le_add_right _ _)) (nat.zero_le _) (nat.zero_le _)

lemma monotone_factorial : monotone factorial := λ n m, factorial_le

lemma factorial_lt (hn : 0 < n) : n! < m! ↔ n < m :=
begin
  split; intro h,
  { rw [← not_le], intro hmn, apply not_le_of_lt h (factorial_le hmn) },
  have : ∀ n, 0 < n → n! < n.succ!,
  { intros k hk, rw [factorial_succ, succ_mul, lt_add_iff_pos_left],
    apply mul_pos hk (factorial_pos k) },
  induction h with k hnk generalizing hn,
  { exact this _ hn, },
  refine lt_trans (h_ih hn) (this _ _),
  exact lt_trans hn (lt_of_succ_le hnk),
end

lemma one_lt_factorial : 1 < n! ↔ 1 < n :=
by { convert factorial_lt _, refl, exact one_pos }

lemma factorial_eq_one : n! = 1 ↔ n ≤ 1 :=
begin
  split; intro h,
  { rw [← not_lt, ← one_lt_factorial, h],
    apply lt_irrefl },
  cases h with h h, refl, cases h, refl,
end

lemma factorial_inj (hn : 1 < n!) : n! = m! ↔ n = m :=
begin
  split; intro h,
  { obtain hnm | hnm | hnm := lt_trichotomy n m,
    { exfalso, rw [← factorial_lt, h] at hnm, exact lt_irrefl _ hnm,
      rw [one_lt_factorial] at hn, exact lt_trans one_pos hn },
    { exact hnm },
    exfalso,
    rw [h, one_lt_factorial] at hn,
    rw [←factorial_lt (lt_trans one_pos hn), h] at hnm, exact lt_irrefl _ hnm, },
  { rw h },
end

lemma self_le_factorial : ∀ n : ℕ, n ≤ n!
| 0       := zero_le_one
| (k + 1) := le_mul_of_one_le_right k.zero_lt_succ.le (nat.one_le_of_lt $ nat.factorial_pos _)

lemma lt_factorial_self {n : ℕ} (hi : 3 ≤ n) : n < n! :=
begin
  rw [← succ_pred_eq_of_pos ((zero_lt_two.trans (lt.base 2)).trans_le hi), factorial_succ],
  exact lt_mul_of_one_lt_right ((pred n).succ_pos) ((one_lt_two.trans_le
    (le_pred_of_lt (succ_le_iff.mp hi))).trans_le (self_le_factorial _)),
end

lemma add_factorial_succ_lt_factorial_add_succ {i : ℕ} (n : ℕ) (hi : 2 ≤ i) :
  i + (n + 1)! < (i + n + 1)! :=
begin
  rw [factorial_succ (i + _), succ_eq_add_one, add_mul, one_mul],
  have : i ≤ i + n := le.intro rfl,
  exact add_lt_add_of_lt_of_le (this.trans_lt ((lt_mul_iff_one_lt_right (zero_lt_two.trans_le
    (hi.trans this))).mpr (lt_iff_le_and_ne.mpr ⟨(i + n).factorial_pos, λ g,
    nat.not_succ_le_self 1 ((hi.trans this).trans (factorial_eq_one.mp g.symm))⟩))) (factorial_le
    ((le_of_eq (add_comm n 1)).trans ((add_le_add_iff_right n).mpr (one_le_two.trans hi)))),
end

lemma add_factorial_lt_factorial_add {i n : ℕ} (hi : 2 ≤ i) (hn : 1 ≤ n) :
  i + n! < (i + n)! :=
begin
  cases hn,
  { rw factorial_one,
    exact lt_factorial_self (succ_le_succ hi) },
  exact add_factorial_succ_lt_factorial_add_succ _ hi,
end

lemma add_factorial_succ_le_factorial_add_succ (i : ℕ) (n : ℕ) :
  i + (n + 1)! ≤ (i + (n + 1))! :=
begin
  obtain i2 | (_ | ⟨_, i0⟩) := le_or_lt 2 i,
  { exact (n.add_factorial_succ_lt_factorial_add_succ i2).le },
  { change 1 + (n + 1)! ≤ (1 + n + 1) * (1 + n)!,
    rw [add_mul, one_mul, add_comm 1 n],
    exact (add_le_add_iff_right _).mpr (one_le_mul (nat.le_add_left 1 n) (n + 1).factorial_pos) },
  rw [nat.le_zero_iff.mp (nat.succ_le_succ_iff.mp i0), zero_add, zero_add]
end

lemma add_factorial_le_factorial_add (i : ℕ) {n : ℕ} (n1 : 1 ≤ n) :
  i + n! ≤ (i + n)! :=
begin
  cases n1 with h,
  { exact self_le_factorial _ },
  exact add_factorial_succ_le_factorial_add_succ i h,
end

lemma pow_mul_factorial_le_factorial {n m : ℕ} (hnm : n ≤ m) : n ^ (m - n) * n! ≤ m! :=
begin
  induction m,
  have hn : n = 0, exact le_zero_iff.mp hnm,
  rw hn,
  simp only [le_refl, mul_one, nat.nat_zero_eq_zero, nat.factorial_zero, nat.sub_self, pow_zero],
  by_cases n ≤ m_n,
  rw succ_sub,
  rw [nat.factorial_succ, pow_succ],
  rw mul_assoc,
  apply mul_le_mul,
  exact hnm,
  exact m_ih h,
  apply zero_le,
  apply zero_le,
  exact h,
  simp at *,
  have hn : m_n.succ ≤ n, exact succ_le_iff.mpr h,
  have hn' : n = m_n.succ, exact le_antisymm hnm hn,
  rw <- hn',
  simp only [one_mul, nat.sub_self, pow_zero],
  rw hn',
  simp only [le_refl, mul_le_mul_left, nat.factorial_succ],
end


end factorial

/-! ### Ascending and descending factorials -/

section asc_factorial

/-- `n.asc_factorial k = (n + k)! / n!` (as seen in `nat.asc_factorial_eq_div`), but implemented
recursively to allow for "quick" computation when using `norm_num`. This is closely related to
`pochhammer`, but much less general. -/
def asc_factorial (n : ℕ) : ℕ → ℕ
| 0 := 1
| (k + 1) := (n + k + 1) * asc_factorial k

@[simp] lemma asc_factorial_zero (n : ℕ) : n.asc_factorial 0 = 1 := rfl

@[simp] lemma zero_asc_factorial (k : ℕ) : (0 : ℕ).asc_factorial k = k! :=
begin
  induction k with t ht, refl,
  unfold asc_factorial, rw [ht, zero_add, nat.factorial_succ],
end

lemma asc_factorial_succ {n k : ℕ} : n.asc_factorial k.succ = (n + k + 1) * n.asc_factorial k := rfl

lemma succ_asc_factorial (n : ℕ) :
  ∀ k, (n + 1) * n.succ.asc_factorial k = (n + k + 1) * n.asc_factorial k
| 0 := by rw [add_zero, asc_factorial_zero, asc_factorial_zero]
| (k + 1) := by rw [asc_factorial, mul_left_comm, succ_asc_factorial, asc_factorial, succ_add,
  ←add_assoc]

/-- `n.asc_factorial k = (n + k)! / n!` but without ℕ-division. See `nat.asc_factorial_eq_div` for
the version with ℕ-division. -/
theorem factorial_mul_asc_factorial (n : ℕ) : ∀ k, n! * n.asc_factorial k = (n + k)!
| 0 := by rw [asc_factorial, add_zero, mul_one]
| (k + 1) := by rw [asc_factorial_succ, mul_left_comm, factorial_mul_asc_factorial, ← add_assoc,
  factorial]

/-- Avoid in favor of `nat.factorial_mul_asc_factorial` if you can. ℕ-division isn't worth it. -/
lemma asc_factorial_eq_div (n k : ℕ) : n.asc_factorial k = (n + k)! / n! :=
begin
  apply mul_left_cancel' (factorial_ne_zero n),
  rw factorial_mul_asc_factorial,
  exact (nat.mul_div_cancel' $ factorial_dvd_factorial $ le.intro rfl).symm
end

lemma asc_factorial_of_sub {n k : ℕ} (h : k < n) :
  (n - k) * (n - k).asc_factorial k = (n - (k + 1)).asc_factorial (k + 1) :=
begin
  set t := n - k.succ with ht,
  suffices h' : n - k = t.succ, by rw [←ht, h', succ_asc_factorial, asc_factorial_succ],
  rw [ht, succ_eq_add_one, ←sub_sub_assoc h (succ_pos _), succ_sub_one],
end

lemma pow_succ_le_asc_factorial (n : ℕ) : ∀ (k : ℕ), (n + 1)^k ≤ n.asc_factorial k
| 0 := by rw [asc_factorial_zero, pow_zero]
| (k + 1) := begin
  rw pow_succ,
  exact nat.mul_le_mul (nat.add_le_add_right le_self_add _) (pow_succ_le_asc_factorial k),
end

lemma pow_lt_asc_factorial' (n k : ℕ) : (n + 1)^(k + 2) < n.asc_factorial (k + 2) :=
begin
  rw pow_succ,
  exact nat.mul_lt_mul (nat.add_lt_add_right (nat.lt_add_of_pos_right succ_pos') 1)
    (pow_succ_le_asc_factorial n _) (pow_pos succ_pos' _),
end

lemma pow_lt_asc_factorial (n : ℕ) : ∀ {k : ℕ}, 2 ≤ k → (n + 1)^k < n.asc_factorial k
| 0 := by rintro ⟨⟩
| 1 := by rintro (_ | ⟨_, ⟨⟩⟩)
| (k + 2) := λ _, pow_lt_asc_factorial' n k

lemma asc_factorial_le_pow_add (n : ℕ) : ∀ (k : ℕ), n.asc_factorial k ≤ (n + k)^k
| 0 := by rw [asc_factorial_zero, pow_zero]
| (k + 1) := begin
  rw [asc_factorial_succ, pow_succ],
  exact nat.mul_le_mul_of_nonneg_left ((asc_factorial_le_pow_add k).trans (nat.pow_le_pow_of_le_left
  (le_succ _) _)),
end

lemma asc_factorial_lt_pow_add (n : ℕ) : ∀ {k : ℕ}, 2 ≤ k → n.asc_factorial k < (n + k)^k
| 0 := by rintro ⟨⟩
| 1 := by rintro (_ | ⟨_, ⟨⟩⟩)
| (k + 2) := λ _, begin
  rw [asc_factorial_succ, pow_succ],
  refine nat.mul_lt_mul' (le_refl _) ((asc_factorial_le_pow_add n _).trans_lt
    (pow_lt_pow_of_lt_left (lt_add_one _) (succ_pos _))) (succ_pos _),
end

lemma asc_factorial_pos (n k : ℕ) : 0 < n.asc_factorial k :=
(pow_pos (succ_pos n) k).trans_le (pow_succ_le_asc_factorial n k)

end asc_factorial

section desc_factorial

/-- `n.desc_factorial k = n! / (n - k)!` (as seen in `nat.desc_factorial_eq_div`), but
implemented recursively to allow for "quick" computation when using `norm_num`. This is closely
related to `pochhammer`, but much less general. -/
def desc_factorial (n : ℕ) : ℕ → ℕ
| 0 := 1
| (k + 1) := (n - k) * desc_factorial k

@[simp] lemma desc_factorial_zero (n : ℕ) : n.desc_factorial 0 = 1 := rfl

@[simp] lemma desc_factorial_succ (n k : ℕ) :
  n.desc_factorial k.succ = (n - k) * n.desc_factorial k := rfl

lemma zero_desc_factorial_succ (k : ℕ) :
  (0 : ℕ).desc_factorial k.succ = 0 :=
by rw [desc_factorial_succ, nat.zero_sub, zero_mul]

@[simp] lemma desc_factorial_one (n : ℕ) :
  n.desc_factorial 1 = n :=
by rw [desc_factorial_succ, desc_factorial_zero, mul_one, nat.sub_zero]

@[simp] lemma succ_desc_factorial_succ (n : ℕ) :
  ∀ k : ℕ, (n + 1).desc_factorial (k + 1) = (n + 1) * n.desc_factorial k
| 0        := by rw [desc_factorial_zero, desc_factorial_one, mul_one]
| (succ k) := by rw [desc_factorial_succ, succ_desc_factorial_succ, desc_factorial_succ,
  succ_sub_succ, mul_left_comm]

lemma succ_desc_factorial (n : ℕ) :
  ∀ k, (n + 1 - k) * (n + 1).desc_factorial k = (n + 1) * n.desc_factorial k
| 0 := by rw [nat.sub_zero, desc_factorial_zero, desc_factorial_zero]
| (k + 1) := by rw [desc_factorial, succ_desc_factorial, desc_factorial_succ, succ_sub_succ,
  mul_left_comm]

lemma desc_factorial_self : ∀ n : ℕ, n.desc_factorial n = n!
| 0        := by rw [desc_factorial_zero, factorial_zero]
| (succ n) := by rw [succ_desc_factorial_succ, desc_factorial_self, factorial_succ]

@[simp] lemma desc_factorial_eq_zero_iff_lt {n : ℕ} : ∀ {k : ℕ}, n.desc_factorial k = 0 ↔ n < k
| 0        := by simp only [desc_factorial_zero, nat.one_ne_zero, not_lt_zero]
| (succ k) := begin
  rw [desc_factorial_succ, mul_eq_zero, desc_factorial_eq_zero_iff_lt, lt_succ_iff,
    nat.sub_eq_zero_iff_le, lt_iff_le_and_ne, or_iff_left_iff_imp, and_imp],
  exact λ h _, h,
end

lemma add_desc_factorial_eq_asc_factorial (n : ℕ) :
  ∀ k : ℕ, (n + k).desc_factorial k = n.asc_factorial k
| 0        := by rw [asc_factorial_zero, desc_factorial_zero]
| (succ k) := by rw [nat.add_succ, succ_desc_factorial_succ, asc_factorial_succ,
  add_desc_factorial_eq_asc_factorial]

/-- `n.desc_factorial k = n! / (n - k)!` but without ℕ-division. See `nat.desc_factorial_eq_div`
for the version using ℕ-division. -/
theorem factorial_mul_desc_factorial : ∀ {n k : ℕ}, k ≤ n → (n - k)! * n.desc_factorial k = n!
| n        0        := λ _, by rw [desc_factorial_zero, mul_one, nat.sub_zero]
| 0        (succ k) := λ h, by { exfalso, exact not_succ_le_zero k h }
| (succ n) (succ k) := λ h, by rw [succ_desc_factorial_succ, succ_sub_succ, ←mul_assoc,
  mul_comm (n - k)!, mul_assoc, factorial_mul_desc_factorial (nat.succ_le_succ_iff.1 h),
    factorial_succ]

/-- Avoid in favor of `nat.factorial_mul_desc_factorial` if you can. ℕ-division isn't worth it. -/
lemma desc_factorial_eq_div {n k : ℕ} (h : k ≤ n) : n.desc_factorial k = n! / (n - k)! :=
begin
  apply mul_left_cancel' (factorial_ne_zero (n - k)),
  rw factorial_mul_desc_factorial h,
  exact (nat.mul_div_cancel' $ factorial_dvd_factorial $ sub_le n k).symm,
end

lemma pow_sub_le_desc_factorial (n : ℕ) : ∀ (k : ℕ), (n + 1 - k)^k ≤ n.desc_factorial k
| 0 := by rw [desc_factorial_zero, pow_zero]
| (k + 1) := begin
  rw [desc_factorial_succ, pow_succ, succ_sub_succ],
  exact nat.mul_le_mul_of_nonneg_left (le_trans (nat.pow_le_pow_of_le_left
    (nat.sub_le_sub_right (le_succ _) _) k) (pow_sub_le_desc_factorial k)),
end

lemma pow_sub_lt_desc_factorial' {n : ℕ} :
  ∀ {k : ℕ}, k + 2 ≤ n → (n - (k + 1))^(k + 2) < n.desc_factorial (k + 2)
| 0 := λ h, begin
  rw [desc_factorial_succ, pow_succ, pow_one, desc_factorial_one],
  exact nat.mul_lt_mul_of_pos_left (nat.sub_lt_self (lt_of_lt_of_le zero_lt_two h) zero_lt_one)
    (nat.sub_pos_of_lt h),
end
| (k + 1) := λ h, begin
  rw [desc_factorial_succ, pow_succ],
  refine nat.mul_lt_mul_of_pos_left ((nat.pow_le_pow_of_le_left (nat.sub_le_sub_right
    (le_succ n) _) _).trans_lt _) (nat.sub_pos_of_lt h),
  rw succ_sub_succ,
  exact (pow_sub_lt_desc_factorial' ((le_succ _).trans h)),
end

lemma pow_sub_lt_desc_factorial {n : ℕ} :
  ∀ {k : ℕ}, 2 ≤ k → k ≤ n → (n + 1 - k)^k < n.desc_factorial k
| 0 := by rintro ⟨⟩
| 1 := by rintro (_ | ⟨_, ⟨⟩⟩)
| (k + 2) := λ _ h, by { rw succ_sub_succ, exact pow_sub_lt_desc_factorial' h }

lemma desc_factorial_le_pow (n : ℕ) : ∀ (k : ℕ), n.desc_factorial k ≤ n^k
| 0 := by rw [desc_factorial_zero, pow_zero]
| (k + 1) := begin
  rw [desc_factorial_succ, pow_succ],
  exact nat.mul_le_mul (sub_le _ _) (desc_factorial_le_pow k),
end

lemma desc_factorial_lt_pow {n : ℕ} (hn : 1 ≤ n) : ∀ {k : ℕ}, 2 ≤ k → n.desc_factorial k < n^k
| 0 := by rintro ⟨⟩
| 1 := by rintro (_ | ⟨_, ⟨⟩⟩)
| (k + 2) := λ _, begin
  rw [desc_factorial_succ, pow_succ', mul_comm],
  exact nat.mul_lt_mul' (desc_factorial_le_pow _ _) (nat.sub_lt_self hn k.zero_lt_succ)
    (pow_pos hn _),
end

end desc_factorial

end nat
