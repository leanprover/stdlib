/-
Copyright (c) 2021 Adrián Doña Mateo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrián Doña Mateo
-/

import algebra.big_operators
import data.pnat.basic

/-!
# IMO 2014 Q1

Let `a₀ < a₁ < a₂ < ⋯` be an infinite sequence of positive integers.
Prove that there exists a unique `n ≥ 1` such that

  `aₙ < (a₀ + a₁ + ⋯ + aₙ) / n < aₙ₊₁`.

This solutions is a translation of the official solution, which may be found as the
solution to problem A1 [here](https://www.imo-official.org/problems/IMO2014SL.pdf).
-/

open_locale big_operators

noncomputable theory

/-- The integer sequence. -/
variable (a : ℕ → ℤ)

/-- We define an auxiliary sequence `d a : ℕ+ → ℤ` by
  `d a n = (a 0 + a 1 + ⋯ + a n) - n * (a n)`. -/
def d (n : ℕ+) : ℤ := (∑ i : fin (n + 1), a i) - n * (a n)

lemma first_ineq_iff {n : ℕ+} :
  (a n : ℚ) < (↑∑ i : fin (n + 1), a i : ℚ) / n ↔ 0 < d a n :=
show _ < _ / ↑(n : ℤ) ↔ _, begin
  have : (↑(a n) : ℚ) = ↑(a n) / ↑(1 : ℤ) := by simp,
  rw [this, rat.div_lt_div_iff_mul_lt_mul (int.zero_lt_one)],
  { simp [d, mul_comm] }, simp,
end

lemma second_ineq_iff {n : ℕ+} :
  (↑∑ i : fin (n + 1), a i : ℚ) / n ≤ a (n + 1) ↔ d a (n + 1) ≤ 0 :=
show _ / ↑(n : ℤ) ≤ _ ↔ _, begin
  have : (↑(a (n + 1)) : ℚ) = ↑(a (n + 1)) / ↑(1 : ℤ) := by simp, rw this,
  simp only [rat.div_num_denom, mul_one, rat.num_one, one_mul, rat.coe_int_denom, int.coe_nat_zero,
    rat.coe_int_num, int.coe_nat_succ, zero_add, coe_coe],
  rw rat.le_def, swap,
  { norm_cast, have : 1 ≤ ↑n := pnat.one_le n, linarith }, swap,
  { exact zero_lt_one },
  simp only [d, @fin.sum_univ_cast_succ _ _ ↑(n + 1), mul_one, fin.coe_last, pnat.one_coe,
    fin.coe_cast_succ, int.coe_nat_succ, pnat.add_coe, sub_nonpos, coe_coe, add_mul, one_mul],
  rw [add_le_add_iff_right,	mul_comm], refl,
end

/-- We rephrase the original question into a question about `d a`. -/
lemma ineq_iff {n : ℕ+} :
  (a n : ℚ) < (↑∑ i : fin (n + 1), a i : ℚ) / n ∧
  (↑∑ i : fin (n + 1), a i : ℚ) / n ≤ a (n + 1) ↔
  0 < d a n ∧ d a (n + 1) ≤ 0 :=
⟨λ h, ⟨(first_ineq_iff a).1 h.1, (second_ineq_iff a).1 h.2⟩,
  λ h, ⟨(first_ineq_iff a).2 h.1, (second_ineq_iff a).2 h.2⟩⟩

lemma d_one : d a 1 = a 0 :=
show a 0 + (a 1 + 0) - 1 * a 1 = a 0, by simp

/-- If `a` is strictly increasing, then `d a` is strictly decreasing. -/
lemma ddes (hinc : ∀ n, a n < a (n + 1)) (n : ℕ+) : d a (n + 1) < d a n :=
lt_of_sub_neg $
  calc ((∑ i : fin (n + 2), a i) - (n + 1) * a (n + 1))
        - ((∑ i : fin (n + 1), a i) - n * a n)
      = ((∑ i : fin (n + 1), a i) + a (n + 1) - (n + 1) * a (n + 1))
        - ((∑ i : fin (n + 1), a i) - n * a n) : by simp [fin.sum_univ_cast_succ]
  ... = n * (a n - a (n + 1))                  : by ring
  ... < 0
    : mul_neg_iff.mpr (or.inl ⟨by simp, sub_neg_of_lt (hinc n)⟩)

section descending

/-- In this section we prove that for any strictly descending sequence `f : ℕ+ → ℤ`
  and integer `x < f m` for some `m`, there is a unique index `n ≥ m` such that
  `f (n + 1) ≤ x < f n`. -/

variables {f : ℕ+ → ℤ} (hdes : ∀ n, f (n + 1) < f n)
include hdes

theorem lt_of_lt_of_des {n m : ℕ+} (hnm : n < m) :
  f m < f n :=
begin
  have : ∀ k : ℕ, f (n + ⟨k + 1, nat.succ_pos k⟩) < f n,
  { intro k, induction k with k ih,
    { exact hdes n },
    apply lt_trans (hdes _) ih },
  convert this (↑(m - n) - 1),
  have : 1 ≤ ↑(m - n) := (pnat.coe_le_coe 1 _).mpr (pnat.one_le _),
  simp [nat.sub_add_cancel this, pnat.add_sub_of_lt hnm],
end

theorem no_middle_term (n : ℕ+) :
  ¬ ∃ m, f (n + 1) < f m ∧ f m < f n :=
begin
  rintro ⟨m, fn1m, fmn⟩,
  rcases lt_trichotomy m n with hmn | heq | hnm,
  { linarith [lt_of_lt_of_des hdes hmn] },
  { rw heq at fmn, linarith },
  by_cases h : n + 1 < m,
  {	linarith [lt_of_lt_of_des hdes h] },
  have h : m = n + 1 := le_antisymm (le_of_not_gt h) (nat.succ_le_of_lt hnm),
  rw h at fn1m, linarith,
end

lemma term_le_of_des (x : ℤ) (m : ℕ+) (hx : x < f m) :
  ∃ k, f (m + ⟨k + 1, by linarith⟩) ≤ x :=
begin
  have : ∀ d, f (m + ⟨d + 1, by linarith⟩) < f m - d,
  { intro d, induction d with d ih,
    { simp, exact hdes m },
    simp [sub_add_eq_sub_sub],
    apply lt_of_lt_of_le _ (int.le_sub_one_of_lt ih),
    change f (m + ⟨d + 1, by linarith⟩ + 1) < _,
    exact hdes _ },
  cases int.eq_coe_of_zero_le (le_of_lt $ sub_pos_of_lt hx) with k hk,
  use k,
  apply le_trans (le_of_lt $ this k),
  linarith,
end

theorem cross_of_des (x : ℤ) (m : ℕ+) (hx : x < f m) :
  ∃ n, m ≤ n ∧ x < f n ∧ f (n + 1) ≤ x :=
begin
  let S := { k : ℕ | f (m + ⟨k + 1, by linarith⟩) ≤ x },
  rcases well_founded.has_min nat.lt_wf S (term_le_of_des hdes x m hx) with ⟨k, hk, hmin⟩,
  use m + k,
  { have : 1 ≤ ↑m := pnat.one_le m, linarith },
  split, { rw ← pnat.coe_le_coe, simp },
  split, swap, { exact hk },
  by_contradiction h,
  by_cases h1k : 1 ≤ k, swap,
  {	have : k = 0 := by linarith, simp [this] at h, linarith },
  apply (hmin (k - 1) _) _, swap,
  {	apply nat.sub_lt, linarith, norm_num },
  simp only [set.mem_set_of_eq, nat.sub_add_cancel h1k],
  exact (le_of_not_gt h),
end

theorem unique_cross_of_des (x : ℤ) (n : ℕ+) (hcross : x < f n ∧ f (n + 1) ≤ x) :
  ∀ m, x < f m ∧ f (m + 1) ≤ x → m = n :=
begin
  intros m hm,
  have : ∀ {n m}, f (n + 1) ≤ x → x < f m → m ≤ n,
  { intros n m hfn1 hfm, by_contradiction hnm,
    have h1 : f (n + 1) < f m := lt_of_le_of_lt hfn1 hfm,
    have h2 : f m < f n := lt_of_lt_of_des hdes (lt_of_not_ge hnm),
    exact no_middle_term hdes n ⟨m, h1, h2⟩ },
  exact le_antisymm (this hcross.2 hm.1) (this hm.2 hcross.1),
end

end descending

theorem imo2014_q1 (hpos : ∀ n, 0 < a n) (hinc : ∀ n, a n < a (n + 1)) :
  ∃! n : ℕ+,
  (a n : ℚ) < (↑∑ i : fin (n + 1), a i) / n ∧
  (↑∑ i : fin (n + 1), a i : ℚ) / n ≤ a (n + 1) :=
begin
  rcases cross_of_des (ddes a hinc) 0 1 _ with ⟨n, _, hn⟩, swap,
  {	rw d_one, exact hpos 0 },
  use [n, (ineq_iff a).mpr hn],
  have huniq := unique_cross_of_des (ddes a hinc) 0 n hn,
  intros m hm,
  exact huniq m ((ineq_iff a).mp hm),
end
