/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import tactic

/-!
# Probability on finsets

This file gives an API for probabilities over finite sets (as rational numbers). In particular,
`Prob s P` is the probability that a random element from `s` satisfies the predicate `P`.

We prove a range of lemmas about this, mostly as wrappers over finset lemmas.
-/

open finset

/-- `Prob s P` is the probability that a random element from `s` satisfies the predicate `P`. -/
def Prob {α : Type*} (s : finset α) (P : α → Prop) [decidable_pred P] : ℚ :=
(s.filter P).card / s.card

lemma Prob_singleton {α : Type*} (a : α) (P : α → Prop) [decidable_pred P] :
  Prob {a} P = if P a then 1 else 0 :=
by simp [Prob, filter_singleton, apply_ite finset.card]

@[simp]
lemma Prob_empty {α : Type*} (P : α → Prop) [decidable_pred P] :
  Prob ∅ P = 0 :=
by simp [Prob]

lemma Prob_eq_one_of {α : Type*} {s : finset α} (P : α → Prop) [decidable_pred P]
  (hs : s.nonempty) (hP : ∀ x ∈ s, P x) :
  Prob s P = 1 :=
begin
  rw [Prob, div_eq_iff, one_mul],
  { norm_cast,
    rw finset.filter_true_of_mem hP },
  { rw [←card_pos, nat.pos_iff_ne_zero] at hs,
    norm_cast at * }
end

lemma pred_true_of_Prob_eq_one {α : Type*} {s : finset α} (P : α → Prop) [decidable_pred P]
  (h : Prob s P = 1) : (∀ x ∈ s, P x) :=
begin
  rcases s.eq_empty_or_nonempty with (rfl | hs),
  { simp },
  { rw [Prob, div_eq_iff, one_mul] at h,
    norm_cast at h,
    { rw ← eq_of_subset_of_card_le (filter_subset P s) (ge_of_eq h),
      simp },
    { rw [←card_pos, nat.pos_iff_ne_zero] at hs,
      norm_cast at * } }
end

lemma Prob_eq_zero_iff {α : Type*} {s : finset α} (P : α → Prop) [decidable_pred P] :
  Prob s P = 0 ↔ (∀ x ∈ s, ¬ P x) :=
begin
  rcases s.eq_empty_or_nonempty with (rfl | hs),
  { simp },
  { rw [Prob, div_eq_iff, zero_mul],
    { norm_cast,
      split,
      { rw card_eq_zero,
        simp [eq_empty_iff_forall_not_mem] },
      { intro h,
        simp [filter_false_of_mem h] } },
    { norm_cast,
      rwa [←ne.def, ←nat.pos_iff_ne_zero, card_pos] } }
end

lemma Prob_true {α : Type*} {s : finset α} (hs : s.nonempty) : Prob s (λ x, true) = 1 :=
Prob_eq_one_of _ hs (by simp)

lemma Prob_and {α : Type*} (s : finset α) (P Q : α → Prop) [decidable_pred P] [decidable_pred Q] :
  Prob s (λ x, P x ∧ Q x) = Prob (s.filter Q) P * Prob s Q :=
begin
  rw [Prob, Prob, Prob],
  rw mul_div_assoc',
  congr' 1,
  cases eq_empty_or_nonempty (s.filter Q),
    rw h,
    simp,
    apply eq_empty_of_forall_not_mem,
    rintro x hx,
    simp at hx,
    rw eq_empty_iff_forall_not_mem at h,
    apply h x,
    simp [hx.1, hx.2.2],
  rw div_mul_cancel,
  rw filter_filter, simp [and_comm],
  norm_cast,
  cases h,
  apply card_ne_zero_of_mem h_h,
end

lemma Prob_or {α : Type*} [decidable_eq α] (s : finset α) (P Q : α → Prop) [decidable_pred P]
  [decidable_pred Q] (h : ∀ x ∈ s, P x → Q x → false) :
  Prob s (λ x, P x ∨ Q x) = Prob s P + Prob s Q :=
begin
  have : disjoint (s.filter P) (s.filter Q),
  { rwa disjoint_filter },
  rw [Prob, filter_or, card_disjoint_union this, nat.cast_add, add_div],
  refl
end

lemma Prob_neg {α : Type*} [decidable_eq α] (P Q : α → Prop) [decidable_pred P] [decidable_pred Q]
  (s : finset α) (hs : s.nonempty) (h : ∀ x ∈ s, P x ↔ ¬ Q x) :
  Prob s P + Prob s Q = 1 :=
begin
  rw ← Prob_or,
  { rw Prob_eq_one_of _ hs,
    intros x hx,
    rw [h x hx, or_comm _ (Q x)],
    exact em (Q x) },
  { intros x hx,
    rw [h x hx],
    intro h,
    exact h }
end

lemma Prob_disjoint_union {α : Type*} [decidable_eq α] (s t : finset α) (h₁ : disjoint s t)
  (P : α → Prop) [decidable_pred P] :
  Prob (s ∪ t) P =
    Prob s P * (s.card / (s ∪ t).card) + Prob t P * (t.card / (s ∪ t).card) :=
begin
  rcases s.eq_empty_or_nonempty with (rfl | hs),
  { rcases t.eq_empty_or_nonempty with (rfl | ht),
    { simp [Prob] },
    { rw [empty_union, card_empty, nat.cast_zero, zero_div, mul_zero, zero_add, div_self, mul_one],
      rw [← card_pos, nat.pos_iff_ne_zero] at ht,
      norm_cast at * } },
  { rcases t.eq_empty_or_nonempty with (rfl | ht),
    { rw [union_empty, card_empty, nat.cast_zero, zero_div, mul_zero, add_zero, div_self, mul_one],
      rw [←card_pos, nat.pos_iff_ne_zero] at hs,
      norm_cast at * },
    { rw [←card_pos, nat.pos_iff_ne_zero] at hs ht,
      rw [Prob, Prob, Prob, filter_union, card_disjoint_union h₁,
        card_disjoint_union (disjoint_filter_filter h₁), nat.cast_add, nat.cast_add, add_div,
        div_mul_div_cancel, div_mul_div_cancel];
      norm_cast at * } },
end

lemma conditional {α : Type*} (s : finset α) (P Q : α → Prop)
  [decidable_eq α] [decidable_pred P] [decidable_pred Q] :
  Prob s P = Prob (filter Q s) P * Prob s Q + Prob (filter (λ a, ¬Q a) s) P * Prob s (λ a, ¬Q a) :=
begin
  have : Prob s P = Prob s (λ x, P x ∧ Q x) + Prob s (λ x, P x ∧ ¬ Q x),
    rw [Prob, Prob, Prob, ← add_div],
    congr' 1,
    norm_cast,
    rw [← filter_filter, ← filter_filter, ← card_union_eq, filter_union_filter_neg_eq],
    rw [disjoint_iff_inter_eq_empty, filter_inter_filter_neg_eq],
  rw this,
  rw Prob_and,
  rw Prob_and,
end
