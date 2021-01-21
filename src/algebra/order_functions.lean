/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import order.lattice

/-!
# `max` and `min`

This file proves basic properties about maxima and minima on a `linear_order`.

## Tags

min, max
-/

universes u v
variables {α : Type u} {β : Type v}

attribute [simp] max_eq_left max_eq_right min_eq_left min_eq_right

section
variables [linear_order α] [linear_order β] {f : α → β} {a b c d : α}

-- translate from lattices to linear orders (sup → max, inf → min)
@[simp] lemma le_min_iff : c ≤ min a b ↔ c ≤ a ∧ c ≤ b := le_inf_iff
@[simp] lemma max_le_iff : max a b ≤ c ↔ a ≤ c ∧ b ≤ c := sup_le_iff
lemma max_le_max : a ≤ c → b ≤ d → max a b ≤ max c d := sup_le_sup
lemma min_le_min : a ≤ c → b ≤ d → min a b ≤ min c d := inf_le_inf
lemma le_max_left_of_le : a ≤ b → a ≤ max b c := le_sup_left_of_le
lemma le_max_right_of_le : a ≤ c → a ≤ max b c := le_sup_right_of_le
lemma min_le_left_of_le : a ≤ c → min a b ≤ c := inf_le_left_of_le
lemma min_le_right_of_le : b ≤ c → min a b ≤ c := inf_le_right_of_le
lemma max_min_distrib_left : max a (min b c) = min (max a b) (max a c) := sup_inf_left
lemma max_min_distrib_right : max (min a b) c = min (max a c) (max b c) := sup_inf_right
lemma min_max_distrib_left : min a (max b c) = max (min a b) (min a c) := inf_sup_left
lemma min_max_distrib_right : min (max a b) c = max (min a c) (min b c) := inf_sup_right
lemma min_le_max : min a b ≤ max a b := le_trans (min_le_left a b) (le_max_left a b)

@[simp] lemma min_eq_left_iff : min a b = a ↔ a ≤ b := inf_eq_left
@[simp] lemma min_eq_right_iff : min a b = b ↔ b ≤ a := inf_eq_right
@[simp] lemma max_eq_left_iff : max a b = a ↔ b ≤ a := sup_eq_left
@[simp] lemma max_eq_right_iff : max a b = b ↔ a ≤ b := sup_eq_right

/-- An instance asserting that `max a a = a` -/
instance max_idem : is_idempotent α max := by apply_instance -- short-circuit type class inference

/-- An instance asserting that `min a a = a` -/
instance min_idem : is_idempotent α min := by apply_instance -- short-circuit type class inference

@[simp] lemma max_lt_iff : max a b < c ↔ (a < c ∧ b < c) :=
sup_lt_iff

@[simp] lemma lt_min_iff : a < min b c ↔ (a < b ∧ a < c) :=
lt_inf_iff

@[simp] lemma lt_max_iff : a < max b c ↔ a < b ∨ a < c :=
lt_sup_iff

@[simp] lemma min_lt_iff : min a b < c ↔ a < c ∨ b < c :=
@lt_max_iff (order_dual α) _ _ _ _

@[simp] lemma min_le_iff : min a b ≤ c ↔ a ≤ c ∨ b ≤ c :=
inf_le_iff

@[simp] lemma le_max_iff : a ≤ max b c ↔ a ≤ b ∨ a ≤ c :=
@min_le_iff (order_dual α) _ _ _ _

lemma max_lt_max (h₁ : a < c) (h₂ : b < d) : max a b < max c d :=
by simp [lt_max_iff, max_lt_iff, *]

lemma min_lt_min (h₁ : a < c) (h₂ : b < d) : min a b < min c d :=
@max_lt_max (order_dual α) _ _ _ _ _ h₁ h₂

theorem min_right_comm (a b c : α) : min (min a b) c = min (min a c) b :=
right_comm min min_comm min_assoc a b c

theorem max.left_comm (a b c : α) : max a (max b c) = max b (max a c) :=
left_comm max max_comm max_assoc a b c

theorem max.right_comm (a b c : α) : max (max a b) c = max (max a c) b :=
right_comm max max_comm max_assoc a b c

lemma monotone.map_max (hf : monotone f) : f (max a b) = max (f a) (f b) :=
by cases le_total a b; simp [h, hf h]

lemma monotone.map_min (hf : monotone f) : f (min a b) = min (f a) (f b) :=
hf.order_dual.map_max

theorem min_choice (a b : α) : min a b = a ∨ min a b = b :=
by cases le_total a b; simp *

theorem max_choice (a b : α) : max a b = a ∨ max a b = b :=
@min_choice (order_dual α) _ a b

lemma le_of_max_le_left {a b c : α} (h : max a b ≤ c) : a ≤ c :=
le_trans (le_max_left _ _) h

lemma le_of_max_le_right {a b c : α} (h : max a b ≤ c) : b ≤ c :=
le_trans (le_max_right _ _) h

end
