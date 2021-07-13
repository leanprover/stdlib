/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
import data.equiv.basic
import data.equiv.derangements.basic
import data.fintype.basic
import data.fintype.card
import data.set.finite

import tactic.ring
import tactic.zify

/-!
# Derangements on fintypes

This file contains lemmas that describe the cardinality of `derangements α` when `α` is a fintype.

# Main definitions

  - `num_derangements n`: The number of derangements on an n-element set. For concreteness, `fin n`
    is used.

  - `num_derangements_invariant`: A lemma stating that the number of derangements on a type `α`
    depends only on the cardinality of `α`.

  - `num_derangements_recursive`: A lemma giving a recursive expression for `num_derangements (n+2)`
    in terms of `num_derangements n` and `num_derangements (n+1)`.

  - `num_derangements_sum`: A lemma giving an expression for `num_derangements n` in terms of
    factorials.
-/

open equiv fintype perm
open_locale big_operators

variables {α : Type*} [decidable_eq α] [fintype α]

instance : decidable_pred (derangements α) := λ _, fintype.decidable_forall_fintype

instance : fintype (derangements α) :=
begin
  rw [derangements],
  apply_instance
end

/-- The number of derangements on an `n`-element set. This definition is bad for
    computation though, use `num_derangements` instead. -/
def num_derangements_aux (n : ℕ) : ℕ := card (derangements (fin n))

lemma num_derangements_aux_invariant (α : Type*) [fintype α] [decidable_eq α] :
  card (derangements α) = num_derangements_aux (card α) :=
begin
  apply card_eq.mpr,  -- card_eq because we don't need the specific equivalence
  use derangements_congr (equiv_fin α),
end

theorem num_derangements_aux_succ (n : ℕ) :
  num_derangements_aux (n+2) = (n+1) * num_derangements_aux n +
  (n+1) * num_derangements_aux (n+1) :=
begin
  have card_everything_but : ∀ a : fin (n+1), card ({a}ᶜ : set (fin (n+1))) = n,
  { intro a,
    simp only [fintype.card_of_finset, set.mem_compl_singleton_iff],
    rw [finset.filter_ne' _ a, finset.card_erase_of_mem (finset.mem_univ a)],
    simp },
  have key := card_congr (@derangements_recursion_equiv (fin (n+1)) _),
  rw [num_derangements_aux_invariant, fintype.card_option, fintype.card_fin] at key,
  simp [num_derangements_aux_invariant, card_everything_but, mul_add, key],
end

/-- The number of derangements on an `n`-element set. -/
def num_derangements : ℕ → ℤ
| 0 := 1
| (n + 1) := (n + 1) * num_derangements n - (-1 : ℤ)^n

lemma num_derangement_eq_aux (n : ℕ) : (num_derangements_aux n : ℤ) = num_derangements n :=
begin
  apply nat.strong_induction_on n,
  clear n, -- to avoid confusion with the n in the hypothesis
  intros n hyp,
  -- knock out cases 0 and 1
  cases n, { refl },
  cases n, { refl },
  -- now we have n ≥ 2
  rw num_derangements_aux_succ,
  push_cast,
  have n_le : n < n + 2 := nat.lt_succ_of_le (nat.le_succ _),
  have n_succ_le : n + 1 < n + 2 := lt_add_one _,
  rw [hyp n n_le, hyp n.succ n_succ_le],
  repeat { rw num_derangements },
  rw [pow_succ],
  push_cast,
  ring,
end

lemma num_derangements_nonneg (n : ℕ) : num_derangements n ≥ 0 :=
begin
  rw ← num_derangement_eq_aux,
  exact int.coe_zero_le _,
end

theorem num_derangements_sum (n : ℕ) :
  num_derangements n = ∑ k in finset.range (n + 1), (-1 : ℤ)^k * nat.desc_fac k (n - k) :=
begin
  induction n with n hn,
  { refl },
  { rw [finset.sum_range_succ, num_derangements, hn, finset.mul_sum, sub_eq_add_neg],
    congr' 1,
    -- show that (n + 1) * (-1)^x * desc_fac x (n - x) = (-1)^x * desc_fac x (n.succ - x)
    { refine finset.sum_congr (refl _) _,
      intros x hx,
      have h_le : x ≤ n := finset.mem_range_succ_iff.mp hx,
      rw [nat.succ_sub h_le, nat.desc_fac_succ, nat.add_sub_cancel' h_le],
      push_cast,
      ring },
    -- show that -(-1)^n = (-1)^n.succ * desc_fac n.succ (n.succ - n.succ)
    { simp [pow_succ] } }
end
