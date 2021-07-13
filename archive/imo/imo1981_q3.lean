/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/

import data.nat.fib
import tactic.linarith

/-!
# IMO 1981 Q3

Determine the maximum value of `m ^ 2 + n ^ 2`, where `m` and `n` are integers in
`{1, 2, ..., 1981}` and `(n ^ 2 - m * n - m ^ 2) ^ 2 = 1`.

The trick to this problem is that `m` and `n` have to be consecutive Fibonacci numbers,
because you can reduce any solution to a smaller one using the Fibonacci recurrence.
-/

/-
First, define the problem in terms of finding the maximum of a set.

We first generalize the problem to `{1, 2, ..., N}` and specialize to `N = 1981` at the very end.
-/

open int nat set
section
variable (N : ℕ) -- N = 1981

@[mk_iff] structure problem_predicate (m n : ℤ) : Prop :=
(m_range : m ∈ Ioc 0 (N : ℤ))
(n_range : n ∈ Ioc 0 (N : ℤ))
(eq_one : (n ^ 2 - m * n - m ^ 2) ^ 2 = 1)

def specified_set : set ℤ :=
{k : ℤ | ∃ m : ℤ, ∃ n : ℤ, k = m ^ 2 + n ^ 2 ∧ problem_predicate N m n}

/-
We want to reduce every solution to a smaller solution. Specifically,
we show that when `(m, n)` is a solution, `(n - m, m)` is also a solution,
except for the base case of `(1, 1)`.
-/
namespace problem_predicate
variable {N}

lemma m_le_n {m n : ℤ} (h1 : problem_predicate N m n) : m ≤ n :=
begin
  by_contra h2,
  have h3 : 1 = (n * (n - m) - m ^ 2) ^ 2,
  { calc 1 = (n ^ 2 - m * n - m ^ 2) ^ 2 : h1.eq_one.symm
       ... = (n * (n - m) - m ^ 2) ^ 2   : by ring },
  have h4 : n * (n - m) - m ^ 2 < -1, by nlinarith [h1.n_range.left],
  have h5 : 1 < (n * (n - m) - m ^ 2) ^ 2, by nlinarith,
  exact h5.ne h3
end

lemma eq_imp_1 {n : ℤ} (h1 : problem_predicate N n n) : n = 1 :=
begin
  have : n * (n * (n * n)) = 1,
  { calc _ = (n ^ 2 - n * n - n ^ 2) ^ 2 : by simp [sq, mul_assoc]
       ... = 1                           : h1.eq_one },
  exact eq_one_of_mul_eq_one_right h1.m_range.left.le this,
end

lemma reduction {m n : ℤ} (h1 : problem_predicate N m n) (h2 : 1 < n) :
problem_predicate N (n - m) m :=
begin
  obtain (rfl : m = n) | (h3 : m < n) := h1.m_le_n.eq_or_lt,
  { have h4 : m = 1, from h1.eq_imp_1,
    exact absurd h4.symm h2.ne },
  refine_struct { n_range := h1.m_range, .. },
  -- m_range:
  { have h5 : 0 < n - m, from sub_pos.mpr h3,
    have h6 : n - m < N,
    { calc _ < n : sub_lt_self n h1.m_range.left
         ... ≤ N : h1.n_range.right },
    exact ⟨h5, h6.le⟩ },
  -- eq_one:
  { calc _ = (n ^ 2 - m * n - m ^ 2) ^ 2 : by ring
       ... = 1                           : h1.eq_one },
end

end problem_predicate

/-
It will be convenient to have the lemmas above in their natural number form.
Most of these can be proved with the `norm_cast` family of tactics.
-/

def nat_predicate (m n : ℕ) : Prop := problem_predicate N ↑m ↑n

namespace nat_predicate
variable {N}

lemma m_le_n {m n : ℕ} (h1 : nat_predicate N m n) : m ≤ n :=
by exact_mod_cast h1.m_le_n

lemma eq_imp_1 {n : ℕ} (h1 : nat_predicate N n n) : n = 1 :=
by exact_mod_cast h1.eq_imp_1

lemma reduction {m n : ℕ} (h1 : nat_predicate N m n) (h2 : 1 < n) :
  nat_predicate N (n - m) m :=
have m ≤ n, from h1.m_le_n,
by exact_mod_cast h1.reduction (by exact_mod_cast h2)

lemma n_pos {m n : ℕ} (h1 : nat_predicate N m n) : 0 < n :=
by exact_mod_cast h1.n_range.left

lemma m_pos {m n : ℕ} (h1 : nat_predicate N m n) : 0 < m :=
by exact_mod_cast h1.m_range.left

lemma n_le_N {m n : ℕ} (h1 : nat_predicate N m n) : n ≤ N :=
by exact_mod_cast h1.n_range.right

/-
Now we can use induction to show that solutions must be Fibonacci numbers.
-/
lemma imp_fib {n : ℕ} : ∀ m : ℕ, nat_predicate N m n →
  ∃ k : ℕ, m = fib k ∧ n = fib (k + 1) :=
begin
  apply nat.strong_induction_on n _,
  intros n h1 m h2,
  have h3 : m ≤ n, from h2.m_le_n,
  obtain (rfl : 1 = n) | (h4 : 1 < n) := (succ_le_iff.mpr h2.n_pos).eq_or_lt,
  { use 1,
    have h5 : 1 ≤ m, from succ_le_iff.mpr h2.m_pos,
    simpa [fib_one, fib_two] using (h3.antisymm h5 : m = 1) },
  { obtain (rfl : m = n) | (h6 : m < n) := h3.eq_or_lt,
    { exact absurd h2.eq_imp_1 (ne_of_gt h4) },
    { have h7 : nat_predicate N (n - m) m, from h2.reduction h4,
      obtain ⟨k : ℕ, hnm : n - m = fib k, rfl : m = fib (k+1)⟩ := h1 m h6 (n - m) h7,
      use [k + 1, rfl],
      rw [fib_succ_succ, ← hnm, nat.sub_add_cancel h3] } }
end

end nat_predicate

/-
Next, we prove that if `N < fib K + fib (K+1)`, then the largest `m` and `n`
satisfying `nat_predicate m n N` are `fib K` and `fib (K+1)`, respectively.
-/

variables {K : ℕ} (HK : N < fib K + fib (K+1)) {N}
include HK

lemma m_n_bounds {m n : ℕ} (h1 : nat_predicate N m n) : m ≤ fib K ∧ n ≤ fib (K+1) :=
begin
  obtain ⟨k : ℕ, hm : m = fib k, hn : n = fib (k+1)⟩ := h1.imp_fib m,
  by_cases h2 : k < K + 1,
  { have h3 : k ≤ K, from lt_succ_iff.mp h2,
    split,
    { calc m = fib k : hm
         ... ≤ fib K : fib_mono h3, },
    { have h6 : k + 1 ≤ K + 1, from succ_le_succ h3,
      calc n = fib (k+1) : hn
         ... ≤ fib (K+1) : fib_mono h6 } },
  { have h7 : N < n,
    { have h8 : K + 2 ≤ k + 1, from succ_le_succ (not_lt.mp h2),
      calc N < fib (K+2) : HK
         ... ≤ fib (k+1) : fib_mono h8
         ... = n         : hn.symm, },
    have h9 : n ≤ N, from h1.n_le_N,
    exact absurd h7 h9.not_lt }
end

/-
We spell out the consequences of this result for `specified_set N` here.
-/

variables {M : ℕ} (HM : M = (fib K) ^ 2 + (fib (K+1)) ^ 2)
include HM

lemma k_bound {m n : ℤ} (h1 : problem_predicate N m n) : m ^ 2 + n ^ 2 ≤ M :=
begin
  have h2 : 0 ≤ m, from h1.m_range.left.le,
  have h3 : 0 ≤ n, from h1.n_range.left.le,
  rw [← nat_abs_of_nonneg h2, ← nat_abs_of_nonneg h3] at h1, clear h2 h3,
  obtain ⟨h4 : m.nat_abs ≤ fib K, h5 : n.nat_abs ≤ fib (K+1)⟩ := m_n_bounds HK h1,
  have h6 : m ^ 2 ≤ (fib K) ^ 2, from nat_abs_le_iff_sq_le.mp h4,
  have h7 : n ^ 2 ≤ (fib (K+1)) ^ 2, from nat_abs_le_iff_sq_le.mp h5,
  linarith
end

lemma solution_bound : ∀ {k : ℤ}, k ∈ specified_set N → k ≤ M
| _ ⟨_, _, rfl, h⟩ := k_bound HK HM h

theorem solution_greatest (H : problem_predicate N (fib K) (fib (K + 1))) :
  is_greatest (specified_set N) M :=
⟨⟨fib K, fib (K+1), by simp [HM], H⟩, λ k h, solution_bound HK HM h⟩

end

/-
Now we just have to demonstrate that 987 and 1597 are in fact the largest Fibonacci
numbers in this range, and thus provide the maximum of `specified_set`.
-/

theorem imo1981_q3 : is_greatest (specified_set 1981) 3524578 :=
begin
  have := λ h, @solution_greatest 1981 16 h 3524578,
  simp only [show fib (16:ℕ) = 987 ∧ fib (16+1:ℕ) = 1597,
    by norm_num [fib_succ_succ]] at this,
  apply_mod_cast this; norm_num [problem_predicate_iff],
end
