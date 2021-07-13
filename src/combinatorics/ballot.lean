/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.fintype.basic
import data.set.finite
import data.list
import tactic.field_simp
import tactic.abel
import combinatorics.Prob

/-!
# Ballot Problem

This file proves Theorem 30 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

-/

open finset

/-- Every nonempty suffix has positive sum. -/
def stays_positive (l : list ℤ) : Prop := ∀ l₂, l₂ ≠ [] → l₂ <:+ l → 0 < l₂.sum

@[simp] lemma stays_positive_empty : stays_positive [] :=
λ l hl hl₁, (hl (list.eq_nil_of_suffix_nil hl₁)).elim

lemma sublist_cons {α : Type*} (x : α) (l₁ l₂ : list α) :
  l₁ <:+ x :: l₂ ↔ l₁ = x :: l₂ ∨ l₁ <:+ l₂ :=
begin
  split,
  { rintro ⟨l₃, hl₃⟩,
    cases l₃ with hd tl,
    { simp only [list.nil_append] at hl₃,
      left,
      apply hl₃ },
    { simp only [list.cons_append] at hl₃,
      right,
      exact ⟨_, hl₃.2⟩ } },
  { rintro (rfl | hl₁),
    { exact (x :: l₂).suffix_refl },
    { apply hl₁.trans (list.suffix_cons _ _) } }
end

lemma stays_positive_cons_pos (x : ℤ) (hx : 0 < x) (l) :
  stays_positive (x :: l) ↔ stays_positive l :=
begin
  split,
  { intros hl l₁ hl₁ hl₂,
    apply hl l₁ hl₁ (hl₂.trans (list.suffix_cons _ _)) },
  { intros hl l₁ hl₁ hl₂,
    rw sublist_cons at hl₂,
    rcases hl₂ with (rfl | hl₂),
    { rw list.sum_cons,
      apply add_pos_of_pos_of_nonneg hx,
      cases l with hd tl,
      { simp },
      { apply le_of_lt (hl (hd :: tl) (list.cons_ne_nil hd tl) (hd :: tl).suffix_refl) } },
    { apply hl _ hl₁ hl₂ } }
end

lemma list.sum_pos : ∀ (l : list ℤ) (hl : ∀ x ∈ l, (0 : ℤ) < x) (hl₂ : l ≠ []), 0 < l.sum
| [] _ h := (h rfl).elim
| [b] h _ := by simpa using h
| (a :: b :: l) hl₁ hl₂ :=
begin
  simp only [forall_eq_or_imp, list.mem_cons_iff _ a] at hl₁,
  rw list.sum_cons,
  apply add_pos_of_pos_of_nonneg hl₁.1,
  apply le_of_lt ((b :: l).sum_pos hl₁.2 (l.cons_ne_nil b)),
end

/--
`counted_sequence p q` is the (fin)set of lists of `ℤ` for which every element is `+1` or `-1`,
there are `p` lots of `+1` and `q` lots of `-1`.
This represents vote sequences where candidate `+1` receives `p` votes and candidate `-1` receives
`q` votes.
-/
def counted_sequence : ℕ → ℕ → finset (list ℤ)
| 0 q := {list.repeat (-1) q}
| (p+1) 0 := {list.repeat 1 (p+1)}
| (p+1) (q+1) :=
      (counted_sequence p (q+1)).map ⟨list.cons 1, list.cons_injective⟩ ∪
      (counted_sequence (p+1) q).map ⟨list.cons (-1), list.cons_injective⟩

lemma counted_right_zero (p : ℕ) : counted_sequence p 0 = {list.repeat 1 p} :=
by cases p; refl

lemma counted_left_zero (q : ℕ) : counted_sequence 0 q = {list.repeat (-1) q} :=
by cases q; refl

lemma counted_succ_succ (p q : ℕ) : counted_sequence (p+1) (q+1) =
  (counted_sequence p (q+1)).map ⟨list.cons 1, list.cons_injective⟩ ∪
      (counted_sequence (p+1) q).map ⟨list.cons (-1), list.cons_injective⟩ :=
rfl

lemma sum_of_mem_counted_sequence :
  ∀ {p q : ℕ} {l : list ℤ} (hl : l ∈ counted_sequence p q), l.sum = p - q
| 0 q l hl :=
  begin
    rw [counted_left_zero, mem_singleton] at hl,
    subst hl,
    simp,
  end
| p 0 l hl :=
  begin
    rw [counted_right_zero, mem_singleton] at hl,
    subst hl,
    simp
  end
| (p+1) (q+1) l hl :=
  begin
    simp only [counted_succ_succ, mem_union, function.embedding.coe_fn_mk, mem_map] at hl,
    rcases hl with (⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩),
    { rw [list.sum_cons, sum_of_mem_counted_sequence hl],
      push_cast,
      abel },
    { rw [list.sum_cons, sum_of_mem_counted_sequence hl],
      push_cast,
      abel }
  end

lemma mem_of_mem_counted_sequence :
  ∀ {p q : ℕ} {l} (hl : l ∈ counted_sequence p q) {x : ℤ} (hx : x ∈ l), x = 1 ∨ x = -1
| 0 q l hl x hx :=
  begin
    rw counted_left_zero at hl,
    simp only [mem_singleton] at hl,
    subst hl,
    right,
    apply list.eq_of_mem_repeat hx,
  end
| p 0 l hl x hx :=
  begin
    rw counted_right_zero at hl,
    simp only [mem_singleton] at hl,
    subst hl,
    left,
    apply list.eq_of_mem_repeat hx,
  end
| (p+1) (q+1) l hl x hx :=
  begin
    simp only [counted_succ_succ, mem_union, function.embedding.coe_fn_mk, mem_map] at hl,
    rcases hl with (⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩);
    rcases hx with (rfl | hx),
    { left, refl },
    { apply mem_of_mem_counted_sequence hl hx },
    { right, refl },
    { apply mem_of_mem_counted_sequence hl hx },
  end

lemma length_of_mem_counted_sequence :
  ∀ {p q : ℕ} {l : list ℤ} (hl : l ∈ counted_sequence p q), l.length = p + q
| 0 q l hl :=
  begin
    rw [counted_left_zero, mem_singleton] at hl,
    simp [hl],
  end
| p 0 l hl :=
  begin
    rw [counted_right_zero, mem_singleton] at hl,
    simp [hl],
  end
| (p+1) (q+1) l hl :=
  begin
    simp only [counted_succ_succ, mem_union, function.embedding.coe_fn_mk, mem_map] at hl,
    rcases hl with (⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩),
    { rw [list.length_cons, length_of_mem_counted_sequence hl, add_right_comm] },
    { rw [list.length_cons, length_of_mem_counted_sequence hl, ←add_assoc] }
  end

lemma disjoint_bits (p q : ℕ) :
  disjoint
    ((counted_sequence p (q+1)).map ⟨list.cons 1, list.cons_injective⟩)
    ((counted_sequence (p+1) q).map ⟨list.cons (-1), list.cons_injective⟩) :=
begin
  simp_rw [disjoint_left, mem_map, not_exists, function.embedding.coe_fn_mk, exists_imp_distrib],
  rintros _ _ _ rfl _ _ ⟨_, _⟩,
end

lemma card_counted_sequence : ∀ p q : ℕ, (counted_sequence p q).card = (p+q).choose p
| p 0 := by simp [counted_right_zero]
| 0 q := by simp [counted_left_zero]
| (p+1) (q+1) :=
  begin
    rw [counted_succ_succ, card_union_eq, card_map, card_map, card_counted_sequence,
        card_counted_sequence, add_assoc, add_comm 1 q, ← nat.choose_succ_succ, nat.succ_eq_add_one,
        add_right_comm],
    simp_rw [disjoint_left, mem_map, not_exists, function.embedding.coe_fn_mk, exists_imp_distrib],
    rintros _ _ _ rfl _ _ ⟨_, _⟩,
  end

open_locale classical

@[elab_as_eliminator]
lemma diag_induction (P : ℕ → ℕ → Prop) (ha : ∀ a, P (a+1) (a+1)) (hb : ∀ p, P 0 (p+1))
  (hd : ∀ a b, a < b → P (a+1) b → P a (b+1) → P (a+1) (b+1)) :
  ∀ q p, q < p → P q p
| 0 (p+1) h := hb _
| (q+1) (p+1) h :=
begin
  apply hd _ _ ((add_lt_add_iff_right _).1 h),
    have : q + 1 = p ∨ q + 1 < p,
      rwa [← le_iff_eq_or_lt, ← nat.lt_succ_iff],
    rcases this with rfl | _,
      apply ha,
    apply diag_induction (q+1) p this,
  apply diag_induction q (p+1),
  apply lt_of_le_of_lt (nat.le_succ _) h,
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ p, p.1 + p.2.1)⟩]}

lemma first_vote_pos :
  ∀ p q, 0 < p + q  → Prob (counted_sequence p q) (λ l, l.head = 1) = p / (p + q)
| (p+1) 0 h :=
  begin
    rw [counted_right_zero, Prob_singleton, list.repeat_succ, list.head_cons, if_pos rfl,
      nat.cast_zero, add_zero, div_self],
    exact nat.cast_add_one_ne_zero p,
  end
| 0 (q+1) _ :=
  begin
    rw [counted_left_zero, Prob_singleton, nat.cast_zero, zero_div, list.repeat_succ,
      list.head_cons, if_neg (show ¬((-1 : ℤ) = 1), by norm_num)],
  end
| (p+1) (q+1) h :=
  begin
    rw [counted_succ_succ, Prob_disjoint_union _ _ (disjoint_bits _ _), Prob, Prob,
      ←counted_succ_succ, filter_true_of_mem, filter_false_of_mem, card_empty, nat.cast_zero,
      zero_div, zero_mul, add_zero, card_map],
    { rw [div_self, one_mul, card_counted_sequence, card_counted_sequence],
      { rw [eq_div_iff, div_mul_eq_mul_div, div_eq_iff],
        { norm_cast,
          rw [mul_comm, ←nat.succ_eq_add_one, nat.succ_add, nat.succ_mul_choose_eq, mul_comm] },
        { norm_cast,
          rw [←ne.def, ←nat.pos_iff_ne_zero],
          apply nat.choose_pos (nat.le_add_right _ _) },
        { norm_cast,
          rw [←ne.def, ←nat.pos_iff_ne_zero],
          apply nat.add_pos_left,
          apply nat.succ_pos } },
      norm_cast,
      rw [←ne.def, ←nat.pos_iff_ne_zero, card_counted_sequence],
      apply nat.choose_pos (nat.le_add_right _ _) },
    { simp_rw [mem_map, function.embedding.coe_fn_mk],
      rintro _ ⟨l, hl, rfl⟩,
      norm_num },
    { simp_rw [mem_map, function.embedding.coe_fn_mk],
      rintro _ ⟨l, hl, rfl⟩,
      refl },
  end

lemma head_mem_of_nonempty {α : Type*} [inhabited α] :
  ∀ {l : list α} (hl : l ≠ []), l.head ∈ l
| [] h := h rfl
| (x :: l) _ := or.inl rfl

lemma first_vote_neg (p q : ℕ) (h : 0 < p + q) :
  Prob (counted_sequence p q) (λ l, ¬(l.head = 1)) = q / (p + q) :=
begin
  have := Prob_neg (λ (l : list ℤ), l.head = 1) (λ (l : list ℤ), ¬(l.head = 1))
            (counted_sequence p q) _ _,
  { rw [first_vote_pos _ _ h, ← eq_sub_iff_add_eq'] at this,
    rw this,
    field_simp [show (p : ℚ) + q ≠ 0, by { apply ne_of_gt, assumption_mod_cast }] },
  { rw [←card_pos, card_counted_sequence],
    apply nat.choose_pos,
    apply nat.le_add_right },
  { intros x hx,
    simp }
end

lemma ballot_same (p : ℕ) : Prob (counted_sequence (p+1) (p+1)) stays_positive = 0 :=
begin
  rw Prob_eq_zero_iff,
  intros x hx t,
  apply ne_of_gt (t x _ _),
  { simpa using sum_of_mem_counted_sequence hx },
  { apply list.ne_nil_of_length_pos,
    rwa length_of_mem_counted_sequence hx,
    apply nat.add_pos_left,
    apply nat.succ_pos },
  exact x.suffix_refl,
end

lemma mem_of_mem_suffix {α : Type*} {l₁ l₂ : list α} {x : α} (hx : x ∈ l₁) (hl : l₁ <:+ l₂) :
  x ∈ l₂ :=
begin
  rcases hl with ⟨l₂, rfl⟩,
  exact list.mem_append_right l₂ hx,
end

lemma ballot_edge (p : ℕ) : Prob (counted_sequence (p + 1) 0) stays_positive = 1 :=
begin
  rw [counted_right_zero],
  apply Prob_eq_one_of,
  { apply finset.singleton_nonempty },
  { intros l hl,
    rw mem_singleton at hl,
    subst hl,
    intros l hl₁ hl₂,
    apply list.sum_pos _ _ hl₁,
    intros x hx,
    rw list.eq_of_mem_repeat (mem_of_mem_suffix hx hl₂),
    norm_num },
end

lemma filter_pos_counted_succ_succ (p q : ℕ) :
  (filter (λ (l : list ℤ), l.head = 1) (counted_sequence (p + 1) (q + 1))) =
    (counted_sequence p (q+1)).map ⟨list.cons 1, list.cons_injective⟩ :=
begin
  rw [counted_succ_succ, filter_union, filter_true_of_mem, filter_false_of_mem, union_empty],
  { simp only [and_imp, list.head, function.embedding.coe_fn_mk, mem_map, forall_apply_eq_imp_iff₂,
      exists_imp_distrib],
    intros l hl,
    norm_num },
  { simp }
end

lemma ballot_pos (p q : ℕ) :
  Prob (filter (λ (l : list ℤ), l.head = 1) (counted_sequence (p + 1) (q + 1))) stays_positive =
    Prob (counted_sequence p (q + 1)) stays_positive :=
begin
  rw [filter_pos_counted_succ_succ, Prob, Prob, card_map],
  congr' 2,
  have : ((counted_sequence p (q + 1)).map
            ⟨list.cons 1, list.cons_injective⟩).filter stays_positive =
         ((counted_sequence p (q + 1)).filter stays_positive).map
            ⟨list.cons 1, list.cons_injective⟩,
  { ext t,
    simp only [exists_prop, mem_filter, function.embedding.coe_fn_mk, mem_map],
    split,
    { simp only [and_imp, exists_imp_distrib],
      rintro l hl rfl t,
      refine ⟨l, ⟨hl, _⟩, rfl⟩,
      rwa stays_positive_cons_pos at t,
      norm_num },
    { simp only [and_imp, exists_imp_distrib],
      rintro l hl₁ hl₂ rfl,
      refine ⟨⟨_, hl₁, rfl⟩, _⟩,
      rwa stays_positive_cons_pos,
      norm_num } },
  rw [this, card_map],
end

lemma filter_neg_counted_succ_succ (p q : ℕ) :
  (filter (λ (l : list ℤ), ¬(l.head = 1)) (counted_sequence (p + 1) (q + 1))) =
    (counted_sequence (p+1) q).map ⟨list.cons (-1), list.cons_injective⟩ :=
begin
  rw [counted_succ_succ, filter_union, filter_false_of_mem, filter_true_of_mem, empty_union],
  { simp only [and_imp, list.head, function.embedding.coe_fn_mk, mem_map, forall_apply_eq_imp_iff₂,
      exists_imp_distrib],
    intros l hl,
    norm_num },
  { simp }
end

example (p q : ℕ) (qp : q < p) :
  0 < (-1 : ℚ) + (↑(p + 1) - ↑q) :=
begin
  push_cast,
  ring,
  rw sub_pos,
  assumption_mod_cast,
end

lemma ballot_neg (p q : ℕ) (qp : q < p) :
  Prob (filter (λ (l : list ℤ), ¬(l.head = 1)) (counted_sequence (p + 1) (q + 1))) stays_positive =
    Prob (counted_sequence (p+1) q) stays_positive :=
begin
  rw [filter_neg_counted_succ_succ, Prob, Prob, card_map],
  congr' 2,
  have : ((counted_sequence (p+1) q).map
            ⟨list.cons (-1), list.cons_injective⟩).filter stays_positive =
         ((counted_sequence (p+1) q).filter stays_positive).map
            ⟨list.cons (-1), list.cons_injective⟩,
  { ext t,
    simp only [exists_prop, mem_filter, function.embedding.coe_fn_mk, mem_map],
    split,
    { simp only [and_imp, exists_imp_distrib],
      rintro l hl rfl t,
      refine ⟨_, ⟨hl, _⟩, rfl⟩,
      intros l₁ hl₁ hl₂,
      apply t l₁ hl₁,
      apply hl₂.trans (list.suffix_cons _ _) },
    { simp only [and_imp, exists_imp_distrib],
      rintro l hl₁ hl₂ rfl,
      refine ⟨⟨l, hl₁, rfl⟩, _⟩,
      intros l₁ hl₃ hl₄,
      rw sublist_cons at hl₄,
      rcases hl₄ with (rfl | hl₄),
      { rw list.sum_cons,
        rw sum_of_mem_counted_sequence hl₁,
        push_cast,
        ring,
        rw sub_pos,
        assumption_mod_cast },
      apply hl₂ _ hl₃ hl₄ } },
  rw [this, card_map],
end

theorem ballot :
  ∀ q p, q < p → Prob (counted_sequence p q) stays_positive = (p - q) / (p + q) :=
begin
  apply diag_induction,
  { intro p,
    rw ballot_same,
    simp },
  { intro p,
    rw [nat.cast_zero, sub_zero, add_zero, div_self, ballot_edge],
    norm_cast,
    simp },
  { intros q p qp h₁ h₂,
    have h₃ : p + 1 + (q + 1) > 0,
    { apply nat.add_pos_left,
      apply nat.succ_pos },
    rw conditional _ _ (λ (l : list ℤ), l.head = 1),
    rw first_vote_pos _ _ h₃,
    rw first_vote_neg _ _ h₃,
    rw ballot_pos,
    rw h₁,
    rw ballot_neg _ _ qp,
    rw h₂,
    have h₄ : (↑(p + 1) + ↑(q + 1)) ≠ (0 : ℚ),
    { apply ne_of_gt,
      assumption_mod_cast },
    have h₅ : (↑(p + 1) + ↑q) ≠ (0 : ℚ),
    { apply ne_of_gt,
      norm_cast,
      linarith },
    have h₆ : (↑p + ↑(q + 1)) ≠ (0 : ℚ),
    { apply ne_of_gt,
      norm_cast,
      linarith },
    field_simp [h₄, h₅, h₆],
    ring }
end
