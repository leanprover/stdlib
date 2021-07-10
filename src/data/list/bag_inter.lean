/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/
import data.list.basic

/-!
# List intersection

This file provides basic results about `list.bag_inter` (definition in `data.list.defs`).
`bag_inter l₁ l₂` is the list of elements that are in both `l₁` and `l₂`, counted with multiplicity
and in the order they appear in `l₁`. For example,
`bag_inter [0, 1, 2, 3, 2, 1, 0] [1, 0, 1, 4, 3] = [0, 1, 3, 1]`
-/

open nat

namespace list
variables {α : Type*} [decidable_eq α]

@[simp] theorem nil_bag_inter (l : list α) : [].bag_inter l = [] :=
by cases l; refl

@[simp] theorem bag_inter_nil (l : list α) : l.bag_inter [] = [] :=
by cases l; refl

@[simp] theorem cons_bag_inter_of_pos {a} (l₁ : list α) {l₂} (h : a ∈ l₂) :
  (a :: l₁).bag_inter l₂ = a :: l₁.bag_inter (l₂.erase a) :=
by cases l₂; exact if_pos h

@[simp] theorem cons_bag_inter_of_neg {a} (l₁ : list α) {l₂} (h : a ∉ l₂) :
  (a :: l₁).bag_inter l₂ = l₁.bag_inter l₂ :=
begin
  cases l₂, {simp only [bag_inter_nil]},
  simp only [erase_of_not_mem h, list.bag_inter, if_neg h]
end

@[simp] theorem mem_bag_inter {a : α} : ∀ {l₁ l₂ : list α}, a ∈ l₁.bag_inter l₂ ↔ a ∈ l₁ ∧ a ∈ l₂
| []        l₂ := by simp only [nil_bag_inter, not_mem_nil, false_and]
| (b :: l₁) l₂ := begin
    by_cases b ∈ l₂,
    { rw [cons_bag_inter_of_pos _ h, mem_cons_iff, mem_cons_iff, mem_bag_inter],
      by_cases ba : a = b,
      { simp only [ba, h, eq_self_iff_true, true_or, true_and] },
      { simp only [mem_erase_of_ne ba, ba, false_or] } },
    { rw [cons_bag_inter_of_neg _ h, mem_bag_inter, mem_cons_iff, or_and_distrib_right],
      symmetry, apply or_iff_right_of_imp,
      rintro ⟨rfl, h'⟩, exact h.elim h' }
  end

@[simp] theorem count_bag_inter {a : α} :
  ∀ {l₁ l₂ : list α}, count a (l₁.bag_inter l₂) = min (count a l₁) (count a l₂)
| []         l₂         := by simp
| l₁         []         := by simp
| (h₁ :: l₁) (h₂ :: l₂) :=
begin
  simp only [list.bag_inter, list.mem_cons_iff],
  by_cases p₁ : h₂ = h₁; by_cases p₂ : h₁ = a,
  { simp only [p₁, p₂, count_bag_inter, min_succ_succ, erase_cons_head, if_true, mem_cons_iff,
               count_cons_self, true_or, eq_self_iff_true] },
  { simp only [p₁, ne.symm p₂, count_bag_inter, count_cons, erase_cons_head, if_true, mem_cons_iff,
               true_or, eq_self_iff_true, if_false] },
  { rw p₂ at p₁,
    by_cases p₃ : a ∈ l₂,
    { simp only [p₁, ne.symm p₁, p₂, p₃, erase_cons, count_bag_inter, eq.symm (min_succ_succ _ _),
                 succ_pred_eq_of_pos (count_pos.2 p₃), if_true, mem_cons_iff, false_or,
                 count_cons_self, eq_self_iff_true, if_false, ne.def, not_false_iff,
                 count_erase_self, list.count_cons_of_ne] },
    { simp [ne.symm p₁, p₂, p₃] } },
  { by_cases p₄ : h₁ ∈ l₂; simp only [ne.symm p₁, ne.symm p₂, p₄, count_bag_inter, if_true,
      if_false, mem_cons_iff, false_or, eq_self_iff_true, ne.def, not_false_iff,count_erase_of_ne,
      count_cons_of_ne] }
end

theorem bag_inter_sublist_left : ∀ l₁ l₂ : list α, l₁.bag_inter l₂ <+ l₁
| []        l₂ := by simp [nil_sublist]
| (b :: l₁) l₂ := begin
  by_cases b ∈ l₂; simp [h],
  { apply cons_sublist_cons, apply bag_inter_sublist_left },
  { apply sublist_cons_of_sublist, apply bag_inter_sublist_left }
end

theorem bag_inter_nil_iff_inter_nil : ∀ l₁ l₂ : list α, l₁.bag_inter l₂ = [] ↔ l₁ ∩ l₂ = []
| []        l₂ := by simp
| (b :: l₁) l₂ :=
begin
  by_cases h : b ∈ l₂; simp [h],
  exact bag_inter_nil_iff_inter_nil l₁ l₂
end


end list
