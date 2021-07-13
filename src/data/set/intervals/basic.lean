/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import algebra.ordered_group
import data.set.basic
import order.rel_iso

/-!
# Intervals

In any preorder `α`, we define intervals (which on each side can be either infinite, open, or
closed) using the following naming conventions:
- `i`: infinite
- `o`: open
- `c`: closed

Each interval has the name `I` + letter for left side + letter for right side. For instance,
`Ioc a b` denotes the inverval `(a, b]`.

This file contains these definitions, and basic facts on inclusion, intersection, difference of
intervals (where the precise statements may depend on the properties of the order, in particular
for some statements it should be `linear_order` or `densely_ordered`).

TODO: This is just the beginning; a lot of rules are missing
-/

universe u

namespace set

open set

section intervals
variables {α : Type u} [preorder α] {a a₁ a₂ b b₁ b₂ x : α}

/-- Left-open right-open interval -/
def Ioo (a b : α) := {x | a < x ∧ x < b}

/-- Left-closed right-open interval -/
def Ico (a b : α) := {x | a ≤ x ∧ x < b}

/-- Left-infinite right-open interval -/
def Iio (a : α) := {x | x < a}

/-- Left-closed right-closed interval -/
def Icc (a b : α) := {x | a ≤ x ∧ x ≤ b}

/-- Left-infinite right-closed interval -/
def Iic (b : α) := {x | x ≤ b}

/-- Left-open right-closed interval -/
def Ioc (a b : α) := {x | a < x ∧ x ≤ b}

/-- Left-closed right-infinite interval -/
def Ici (a : α) := {x | a ≤ x}

/-- Left-open right-infinite interval -/
def Ioi (a : α) := {x | a < x}

lemma Ioo_def (a b : α) : {x | a < x ∧ x < b} = Ioo a b := rfl

lemma Ico_def (a b : α) : {x | a ≤ x ∧ x < b} = Ico a b := rfl

lemma Iio_def (a : α) : {x | x < a} = Iio a := rfl

lemma Icc_def (a b : α) : {x | a ≤ x ∧ x ≤ b} = Icc a b := rfl

lemma Iic_def (b : α) : {x | x ≤ b} = Iic b := rfl

lemma Ioc_def (a b : α) : {x | a < x ∧ x ≤ b} = Ioc a b := rfl

lemma Ici_def (a : α) : {x | a ≤ x} = Ici a := rfl

lemma Ioi_def (a : α) : {x | a < x} = Ioi a := rfl

@[simp] lemma mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b := iff.rfl
@[simp] lemma mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b := iff.rfl
@[simp] lemma mem_Iio : x ∈ Iio b ↔ x < b := iff.rfl
@[simp] lemma mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := iff.rfl
@[simp] lemma mem_Iic : x ∈ Iic b ↔ x ≤ b := iff.rfl
@[simp] lemma mem_Ioc : x ∈ Ioc a b ↔ a < x ∧ x ≤ b := iff.rfl
@[simp] lemma mem_Ici : x ∈ Ici a ↔ a ≤ x := iff.rfl
@[simp] lemma mem_Ioi : x ∈ Ioi a ↔ a < x := iff.rfl

@[simp] lemma left_mem_Ioo : a ∈ Ioo a b ↔ false := by simp [lt_irrefl]
@[simp] lemma left_mem_Ico : a ∈ Ico a b ↔ a < b := by simp [le_refl]
@[simp] lemma left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := by simp [le_refl]
@[simp] lemma left_mem_Ioc : a ∈ Ioc a b ↔ false := by simp [lt_irrefl]
lemma left_mem_Ici : a ∈ Ici a := by simp
@[simp] lemma right_mem_Ioo : b ∈ Ioo a b ↔ false := by simp [lt_irrefl]
@[simp] lemma right_mem_Ico : b ∈ Ico a b ↔ false := by simp [lt_irrefl]
@[simp] lemma right_mem_Icc : b ∈ Icc a b ↔ a ≤ b := by simp [le_refl]
@[simp] lemma right_mem_Ioc : b ∈ Ioc a b ↔ a < b := by simp [le_refl]
lemma right_mem_Iic : a ∈ Iic a := by simp

@[simp] lemma dual_Ici : @Ici (order_dual α) _ a = @Iic α _ a := rfl
@[simp] lemma dual_Iic : @Iic (order_dual α) _ a = @Ici α _ a := rfl
@[simp] lemma dual_Ioi : @Ioi (order_dual α) _ a = @Iio α _ a := rfl
@[simp] lemma dual_Iio : @Iio (order_dual α) _ a = @Ioi α _ a := rfl
@[simp] lemma dual_Icc : @Icc (order_dual α) _ a b = @Icc α _ b a :=
set.ext $ λ x, and_comm _ _
@[simp] lemma dual_Ioc : @Ioc (order_dual α) _ a b = @Ico α _ b a :=
set.ext $ λ x, and_comm _ _
@[simp] lemma dual_Ico : @Ico (order_dual α) _ a b = @Ioc α _ b a :=
set.ext $ λ x, and_comm _ _
@[simp] lemma dual_Ioo : @Ioo (order_dual α) _ a b = @Ioo α _ b a :=
set.ext $ λ x, and_comm _ _

@[simp] lemma nonempty_Icc : (Icc a b).nonempty ↔ a ≤ b :=
⟨λ ⟨x, hx⟩, hx.1.trans hx.2, λ h, ⟨a, left_mem_Icc.2 h⟩⟩

@[simp] lemma nonempty_Ico : (Ico a b).nonempty ↔ a < b :=
⟨λ ⟨x, hx⟩, hx.1.trans_lt hx.2, λ h, ⟨a, left_mem_Ico.2 h⟩⟩

@[simp] lemma nonempty_Ioc : (Ioc a b).nonempty ↔ a < b :=
⟨λ ⟨x, hx⟩, hx.1.trans_le hx.2, λ h, ⟨b, right_mem_Ioc.2 h⟩⟩

@[simp] lemma nonempty_Ici : (Ici a).nonempty := ⟨a, left_mem_Ici⟩

@[simp] lemma nonempty_Iic : (Iic a).nonempty := ⟨a, right_mem_Iic⟩

@[simp] lemma nonempty_Ioo [densely_ordered α] : (Ioo a b).nonempty ↔ a < b :=
⟨λ ⟨x, ha, hb⟩, ha.trans hb, exists_between⟩

@[simp] lemma nonempty_Ioi [no_top_order α] : (Ioi a).nonempty := no_top a

@[simp] lemma nonempty_Iio [no_bot_order α] : (Iio a).nonempty := no_bot a

lemma nonempty_Icc_subtype (h : a ≤ b) : nonempty (Icc a b) :=
nonempty.to_subtype (nonempty_Icc.mpr h)

lemma nonempty_Ico_subtype (h : a < b) : nonempty (Ico a b) :=
nonempty.to_subtype (nonempty_Ico.mpr h)

lemma nonempty_Ioc_subtype (h : a < b) : nonempty (Ioc a b) :=
nonempty.to_subtype (nonempty_Ioc.mpr h)

/-- An interval `Ici a` is nonempty. -/
instance nonempty_Ici_subtype : nonempty (Ici a) :=
nonempty.to_subtype nonempty_Ici

/-- An interval `Iic a` is nonempty. -/
instance nonempty_Iic_subtype : nonempty (Iic a) :=
nonempty.to_subtype nonempty_Iic

lemma nonempty_Ioo_subtype [densely_ordered α] (h : a < b) : nonempty (Ioo a b) :=
nonempty.to_subtype (nonempty_Ioo.mpr h)

/-- In a `no_top_order`, the intervals `Ioi` are nonempty. -/
instance nonempty_Ioi_subtype [no_top_order α] : nonempty (Ioi a) :=
nonempty.to_subtype nonempty_Ioi

/-- In a `no_bot_order`, the intervals `Iio` are nonempty. -/
instance nonempty_Iio_subtype [no_bot_order α] : nonempty (Iio a) :=
nonempty.to_subtype nonempty_Iio

@[simp] lemma Icc_eq_empty (h : ¬a ≤ b) : Icc a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x ⟨ha, hb⟩, h (ha.trans hb)

@[simp] lemma Ico_eq_empty (h : ¬a < b) : Ico a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x ⟨ha, hb⟩, h (ha.trans_lt hb)

@[simp] lemma Ioc_eq_empty (h : ¬a < b) : Ioc a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x ⟨ha, hb⟩, h (ha.trans_le hb)

@[simp] lemma Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x ⟨ha, hb⟩,  h (ha.trans hb)

@[simp] lemma Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ :=
Icc_eq_empty h.not_le

@[simp] lemma Ico_eq_empty_of_le (h : b ≤ a) : Ico a b = ∅ :=
Ico_eq_empty h.not_lt

@[simp] lemma Ioc_eq_empty_of_le (h : b ≤ a) : Ioc a b = ∅ :=
Ioc_eq_empty h.not_lt

@[simp] lemma Ioo_eq_empty_of_le (h : b ≤ a) : Ioo a b = ∅ :=
Ioo_eq_empty h.not_lt

@[simp] lemma Ico_self (a : α) : Ico a a = ∅ := Ico_eq_empty $ lt_irrefl _
@[simp] lemma Ioc_self (a : α) : Ioc a a = ∅ := Ioc_eq_empty $ lt_irrefl _
@[simp] lemma Ioo_self (a : α) : Ioo a a = ∅ := Ioo_eq_empty $ lt_irrefl _

lemma Ici_subset_Ici : Ici a ⊆ Ici b ↔ b ≤ a :=
⟨λ h, h $ left_mem_Ici, λ h x hx, h.trans hx⟩

lemma Iic_subset_Iic : Iic a ⊆ Iic b ↔ a ≤ b :=
@Ici_subset_Ici (order_dual α) _ _ _

lemma Ici_subset_Ioi : Ici a ⊆ Ioi b ↔ b < a :=
⟨λ h, h left_mem_Ici, λ h x hx, h.trans_le hx⟩

lemma Iic_subset_Iio : Iic a ⊆ Iio b ↔ a < b :=
⟨λ h, h right_mem_Iic, λ h x hx, lt_of_le_of_lt hx h⟩

lemma Ioo_subset_Ioo (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) :
  Ioo a₁ b₁ ⊆ Ioo a₂ b₂ :=
λ x ⟨hx₁, hx₂⟩, ⟨h₁.trans_lt hx₁, hx₂.trans_le h₂⟩

lemma Ioo_subset_Ioo_left (h : a₁ ≤ a₂) : Ioo a₂ b ⊆ Ioo a₁ b :=
Ioo_subset_Ioo h le_rfl

lemma Ioo_subset_Ioo_right (h : b₁ ≤ b₂) : Ioo a b₁ ⊆ Ioo a b₂ :=
Ioo_subset_Ioo le_rfl h

lemma Ico_subset_Ico (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) :
  Ico a₁ b₁ ⊆ Ico a₂ b₂ :=
λ x ⟨hx₁, hx₂⟩, ⟨h₁.trans hx₁, hx₂.trans_le h₂⟩

lemma Ico_subset_Ico_left (h : a₁ ≤ a₂) : Ico a₂ b ⊆ Ico a₁ b :=
Ico_subset_Ico h le_rfl

lemma Ico_subset_Ico_right (h : b₁ ≤ b₂) : Ico a b₁ ⊆ Ico a b₂ :=
Ico_subset_Ico le_rfl h

lemma Icc_subset_Icc (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) :
  Icc a₁ b₁ ⊆ Icc a₂ b₂ :=
λ x ⟨hx₁, hx₂⟩, ⟨h₁.trans hx₁, le_trans hx₂ h₂⟩

lemma Icc_subset_Icc_left (h : a₁ ≤ a₂) : Icc a₂ b ⊆ Icc a₁ b :=
Icc_subset_Icc h le_rfl

lemma Icc_subset_Icc_right (h : b₁ ≤ b₂) : Icc a b₁ ⊆ Icc a b₂ :=
Icc_subset_Icc le_rfl h

lemma Icc_subset_Ioo (ha : a₂ < a₁) (hb : b₁ < b₂) :
  Icc a₁ b₁ ⊆ Ioo a₂ b₂ :=
λ x hx, ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩

lemma Icc_subset_Ici_self : Icc a b ⊆ Ici a := λ x, and.left

lemma Icc_subset_Iic_self : Icc a b ⊆ Iic b := λ x, and.right

lemma Ioc_subset_Iic_self : Ioc a b ⊆ Iic b := λ x, and.right

lemma Ioc_subset_Ioc (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) :
  Ioc a₁ b₁ ⊆ Ioc a₂ b₂ :=
λ x ⟨hx₁, hx₂⟩, ⟨h₁.trans_lt hx₁, hx₂.trans h₂⟩

lemma Ioc_subset_Ioc_left (h : a₁ ≤ a₂) : Ioc a₂ b ⊆ Ioc a₁ b :=
Ioc_subset_Ioc h le_rfl

lemma Ioc_subset_Ioc_right (h : b₁ ≤ b₂) : Ioc a b₁ ⊆ Ioc a b₂ :=
Ioc_subset_Ioc le_rfl h

lemma Ico_subset_Ioo_left (h₁ : a₁ < a₂) : Ico a₂ b ⊆ Ioo a₁ b :=
λ x, and.imp_left h₁.trans_le

lemma Ioc_subset_Ioo_right (h : b₁ < b₂) : Ioc a b₁ ⊆ Ioo a b₂ :=
λ x, and.imp_right $ λ h', h'.trans_lt h

lemma Icc_subset_Ico_right (h₁ : b₁ < b₂) : Icc a b₁ ⊆ Ico a b₂ :=
λ x, and.imp_right $ λ h₂, h₂.trans_lt h₁

lemma Ioo_subset_Ico_self : Ioo a b ⊆ Ico a b := λ x, and.imp_left le_of_lt

lemma Ioo_subset_Ioc_self : Ioo a b ⊆ Ioc a b := λ x, and.imp_right le_of_lt

lemma Ico_subset_Icc_self : Ico a b ⊆ Icc a b := λ x, and.imp_right le_of_lt

lemma Ioc_subset_Icc_self : Ioc a b ⊆ Icc a b := λ x, and.imp_left le_of_lt

lemma Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b :=
subset.trans Ioo_subset_Ico_self Ico_subset_Icc_self

lemma Ico_subset_Iio_self : Ico a b ⊆ Iio b := λ x, and.right

lemma Ioo_subset_Iio_self : Ioo a b ⊆ Iio b := λ x, and.right

lemma Ioc_subset_Ioi_self : Ioc a b ⊆ Ioi a := λ x, and.left

lemma Ioo_subset_Ioi_self : Ioo a b ⊆ Ioi a := λ x, and.left

lemma Ioi_subset_Ici_self : Ioi a ⊆ Ici a := λ x hx, le_of_lt hx

lemma Iio_subset_Iic_self : Iio a ⊆ Iic a := λ x hx, le_of_lt hx

lemma Ico_subset_Ici_self : Ico a b ⊆ Ici a := λ x, and.left

lemma Icc_subset_Icc_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
⟨λ h, ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩,
 λ ⟨h, h'⟩ x ⟨hx, hx'⟩, ⟨h.trans hx, hx'.trans h'⟩⟩

lemma Icc_subset_Ioo_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ :=
⟨λ h, ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩,
 λ ⟨h, h'⟩ x ⟨hx, hx'⟩, ⟨h.trans_le hx, hx'.trans_lt h'⟩⟩

lemma Icc_subset_Ico_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ :=
⟨λ h, ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩,
 λ ⟨h, h'⟩ x ⟨hx, hx'⟩, ⟨h.trans hx, hx'.trans_lt h'⟩⟩

lemma Icc_subset_Ioc_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
⟨λ h, ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩,
 λ ⟨h, h'⟩ x ⟨hx, hx'⟩, ⟨h.trans_le hx, hx'.trans h'⟩⟩

lemma Icc_subset_Iio_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Iio b₂ ↔ b₁ < b₂ :=
⟨λ h, h ⟨h₁, le_rfl⟩, λ h x ⟨hx, hx'⟩, hx'.trans_lt h⟩

lemma Icc_subset_Ioi_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Ioi a₂ ↔ a₂ < a₁ :=
⟨λ h, h ⟨le_rfl, h₁⟩, λ h x ⟨hx, hx'⟩, h.trans_le hx⟩

lemma Icc_subset_Iic_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Iic b₂ ↔ b₁ ≤ b₂ :=
⟨λ h, h ⟨h₁, le_rfl⟩, λ h x ⟨hx, hx'⟩, hx'.trans h⟩

lemma Icc_subset_Ici_iff (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Ici a₂ ↔ a₂ ≤ a₁ :=
⟨λ h, h ⟨le_rfl, h₁⟩, λ h x ⟨hx, hx'⟩, h.trans hx⟩

lemma Icc_ssubset_Icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) :
  Icc a₁ b₁ ⊂ Icc a₂ b₂ :=
(ssubset_iff_of_subset (Icc_subset_Icc (le_of_lt ha) hb)).mpr
  ⟨a₂, left_mem_Icc.mpr hI, not_and.mpr (λ f g, lt_irrefl a₂ (ha.trans_le f))⟩

lemma Icc_ssubset_Icc_right (hI : a₂ ≤ b₂) (ha : a₂ ≤ a₁) (hb : b₁ < b₂) :
  Icc a₁ b₁ ⊂ Icc a₂ b₂ :=
(ssubset_iff_of_subset (Icc_subset_Icc ha (le_of_lt hb))).mpr
  ⟨b₂, right_mem_Icc.mpr hI, (λ f, lt_irrefl b₁ (hb.trans_le f.2))⟩

/-- If `a ≤ b`, then `(b, +∞) ⊆ (a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Ioi_subset_Ioi_iff`. -/
lemma Ioi_subset_Ioi (h : a ≤ b) : Ioi b ⊆ Ioi a :=
λ x hx, h.trans_lt hx

/-- If `a ≤ b`, then `(b, +∞) ⊆ [a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Ioi_subset_Ici_iff`. -/
lemma Ioi_subset_Ici (h : a ≤ b) : Ioi b ⊆ Ici a :=
subset.trans (Ioi_subset_Ioi h) Ioi_subset_Ici_self

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Iio_subset_Iio_iff`. -/
lemma Iio_subset_Iio (h : a ≤ b) : Iio a ⊆ Iio b :=
λ x hx, lt_of_lt_of_le hx h

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b]`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Iio_subset_Iic_iff`. -/
lemma Iio_subset_Iic (h : a ≤ b) : Iio a ⊆ Iic b :=
subset.trans (Iio_subset_Iio h) Iio_subset_Iic_self

lemma Ici_inter_Iic : Ici a ∩ Iic b = Icc a b := rfl
lemma Ici_inter_Iio : Ici a ∩ Iio b = Ico a b := rfl
lemma Ioi_inter_Iic : Ioi a ∩ Iic b = Ioc a b := rfl
lemma Ioi_inter_Iio : Ioi a ∩ Iio b = Ioo a b := rfl

lemma mem_Icc_of_Ioo (h : x ∈ Ioo a b) : x ∈ Icc a b := Ioo_subset_Icc_self h
lemma mem_Ico_of_Ioo (h : x ∈ Ioo a b) : x ∈ Ico a b := Ioo_subset_Ico_self h
lemma mem_Ioc_of_Ioo (h : x ∈ Ioo a b) : x ∈ Ioc a b := Ioo_subset_Ioc_self h
lemma mem_Icc_of_Ico (h : x ∈ Ico a b) : x ∈ Icc a b := Ico_subset_Icc_self h
lemma mem_Icc_of_Ioc (h : x ∈ Ioc a b) : x ∈ Icc a b := Ioc_subset_Icc_self h
lemma mem_Ici_of_Ioi (h : x ∈ Ioi a) : x ∈ Ici a := Ioi_subset_Ici_self h
lemma mem_Iic_of_Iio (h : x ∈ Iio a) : x ∈ Iic a := Iio_subset_Iic_self h

lemma Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a ≤ b :=
by rw [←not_nonempty_iff_eq_empty, not_iff_not, nonempty_Icc]

lemma Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b :=
by rw [←not_nonempty_iff_eq_empty, not_iff_not, nonempty_Ico]

lemma Ioc_eq_empty_iff : Ioc a b = ∅ ↔ ¬a < b :=
by rw [←not_nonempty_iff_eq_empty, not_iff_not, nonempty_Ioc]

lemma Ioo_eq_empty_iff [densely_ordered α] : Ioo a b = ∅ ↔ ¬a < b :=
by rw [←not_nonempty_iff_eq_empty, not_iff_not, nonempty_Ioo]

end intervals

section partial_order
variables {α : Type u} [partial_order α] {a b : α}

@[simp] lemma Icc_self (a : α) : Icc a a = {a} :=
set.ext $ by simp [Icc, le_antisymm_iff, and_comm]

@[simp] lemma Icc_diff_left : Icc a b \ {a} = Ioc a b :=
ext $ λ x, by simp [lt_iff_le_and_ne, eq_comm, and.right_comm]

@[simp] lemma Icc_diff_right : Icc a b \ {b} = Ico a b :=
ext $ λ x, by simp [lt_iff_le_and_ne, and_assoc]

@[simp] lemma Ico_diff_left : Ico a b \ {a} = Ioo a b :=
ext $ λ x, by simp [and.right_comm, ← lt_iff_le_and_ne, eq_comm]

@[simp] lemma Ioc_diff_right : Ioc a b \ {b} = Ioo a b :=
ext $ λ x, by simp [and_assoc, ← lt_iff_le_and_ne]

@[simp] lemma Icc_diff_both : Icc a b \ {a, b} = Ioo a b :=
by rw [insert_eq, ← diff_diff, Icc_diff_left, Ioc_diff_right]

@[simp] lemma Ici_diff_left : Ici a \ {a} = Ioi a :=
ext $ λ x, by simp [lt_iff_le_and_ne, eq_comm]

@[simp] lemma Iic_diff_right : Iic a \ {a} = Iio a :=
ext $ λ x, by simp [lt_iff_le_and_ne]

@[simp] lemma Ico_diff_Ioo_same (h : a < b) : Ico a b \ Ioo a b = {a} :=
by rw [← Ico_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 $ left_mem_Ico.2 h)]

@[simp] lemma Ioc_diff_Ioo_same (h : a < b) : Ioc a b \ Ioo a b = {b} :=
by rw [← Ioc_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 $ right_mem_Ioc.2 h)]

@[simp] lemma Icc_diff_Ico_same (h : a ≤ b) : Icc a b \ Ico a b = {b} :=
by rw [← Icc_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 $ right_mem_Icc.2 h)]

@[simp] lemma Icc_diff_Ioc_same (h : a ≤ b) : Icc a b \ Ioc a b = {a} :=
by rw [← Icc_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 $ left_mem_Icc.2 h)]

@[simp] lemma Icc_diff_Ioo_same (h : a ≤ b) : Icc a b \ Ioo a b = {a, b} :=
by { rw [← Icc_diff_both, diff_diff_cancel_left], simp [insert_subset, h] }

@[simp] lemma Ici_diff_Ioi_same : Ici a \ Ioi a = {a} :=
by rw [← Ici_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 left_mem_Ici)]

@[simp] lemma Iic_diff_Iio_same : Iic a \ Iio a = {a} :=
by rw [← Iic_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 right_mem_Iic)]

@[simp] lemma Ioi_union_left : Ioi a ∪ {a} = Ici a := ext $ λ x, by simp [eq_comm, le_iff_eq_or_lt]

@[simp] lemma Iio_union_right : Iio a ∪ {a} = Iic a := ext $ λ x, le_iff_lt_or_eq.symm

lemma Ioo_union_left (hab : a < b) : Ioo a b ∪ {a} = Ico a b :=
by rw [← Ico_diff_left, diff_union_self,
  union_eq_self_of_subset_right (singleton_subset_iff.2 $ left_mem_Ico.2 hab)]

lemma Ioo_union_right (hab : a < b) : Ioo a b ∪ {b} = Ioc a b :=
by simpa only [dual_Ioo, dual_Ico] using @Ioo_union_left (order_dual α) _ b a hab

lemma Ioc_union_left (hab : a ≤ b) : Ioc a b ∪ {a} = Icc a b :=
by rw [← Icc_diff_left, diff_union_self,
  union_eq_self_of_subset_right (singleton_subset_iff.2 $ left_mem_Icc.2 hab)]

lemma Ico_union_right (hab : a ≤ b) : Ico a b ∪ {b} = Icc a b :=
by simpa only [dual_Ioc, dual_Icc] using @Ioc_union_left (order_dual α) _ b a hab

lemma mem_Ici_Ioi_of_subset_of_subset {s : set α} (ho : Ioi a ⊆ s) (hc : s ⊆ Ici a) :
  s ∈ ({Ici a, Ioi a} : set (set α)) :=
classical.by_cases
  (λ h : a ∈ s, or.inl $ subset.antisymm hc $ by rw [← Ioi_union_left, union_subset_iff]; simp *)
  (λ h, or.inr $ subset.antisymm (λ x hx, lt_of_le_of_ne (hc hx) (λ heq, h $ heq.symm ▸ hx)) ho)

lemma mem_Iic_Iio_of_subset_of_subset {s : set α} (ho : Iio a ⊆ s) (hc : s ⊆ Iic a) :
  s ∈ ({Iic a, Iio a} : set (set α)) :=
@mem_Ici_Ioi_of_subset_of_subset (order_dual α) _ a s ho hc

lemma mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset {s : set α} (ho : Ioo a b ⊆ s) (hc : s ⊆ Icc a b) :
  s ∈ ({Icc a b, Ico a b, Ioc a b, Ioo a b} : set (set α)) :=
begin
  classical,
  by_cases ha : a ∈ s; by_cases hb : b ∈ s,
  { refine or.inl (subset.antisymm hc _),
    rwa [← Ico_diff_left, diff_singleton_subset_iff, insert_eq_of_mem ha,
      ← Icc_diff_right, diff_singleton_subset_iff, insert_eq_of_mem hb] at ho },
  { refine (or.inr $ or.inl $ subset.antisymm _ _),
    { rw [← Icc_diff_right],
      exact subset_diff_singleton hc hb },
    { rwa [← Ico_diff_left, diff_singleton_subset_iff, insert_eq_of_mem ha] at ho } },
  { refine (or.inr $ or.inr $ or.inl $ subset.antisymm _ _),
    { rw [← Icc_diff_left],
      exact subset_diff_singleton hc ha },
    { rwa [← Ioc_diff_right, diff_singleton_subset_iff, insert_eq_of_mem hb] at ho } },
  { refine (or.inr $ or.inr $ or.inr $ subset.antisymm _ ho),
    rw [← Ico_diff_left, ← Icc_diff_right],
    apply_rules [subset_diff_singleton] }
end

lemma mem_Ioo_or_eq_endpoints_of_mem_Icc {x : α} (hmem : x ∈ Icc a b) :
  x = a ∨ x = b ∨ x ∈ Ioo a b :=
begin
  rw [mem_Icc, le_iff_lt_or_eq, le_iff_lt_or_eq] at hmem,
  rcases hmem with ⟨hxa | hxa, hxb | hxb⟩,
  { exact or.inr (or.inr ⟨hxa, hxb⟩) },
  { exact or.inr (or.inl hxb) },
  all_goals { exact or.inl hxa.symm }
end

lemma mem_Ioo_or_eq_left_of_mem_Ico {x : α} (hmem : x ∈ Ico a b) :
  x = a ∨ x ∈ Ioo a b :=
begin
  rw [mem_Ico, le_iff_lt_or_eq] at hmem,
  rcases hmem with ⟨hxa | hxa, hxb⟩,
  { exact or.inr ⟨hxa, hxb⟩ },
  { exact or.inl hxa.symm }
end

lemma mem_Ioo_or_eq_right_of_mem_Ioc {x : α} (hmem : x ∈ Ioc a b) :
  x = b ∨ x ∈ Ioo a b :=
begin
  have := @mem_Ioo_or_eq_left_of_mem_Ico (order_dual α) _ b a x,
  rw [dual_Ioo, dual_Ico] at this,
  exact this hmem
end

lemma Ici_singleton_of_top {a : α} (h_top : ∀ x, x ≤ a) : Ici a = {a} :=
begin
  ext,
  exact ⟨λ h, (h_top _).antisymm h, λ h, h.ge⟩,
end

lemma Iic_singleton_of_bot {a : α} (h_bot : ∀ x, a ≤ x) : Iic a = {a} :=
@Ici_singleton_of_top (order_dual α) _ a h_bot

end partial_order

section order_top

variables {α : Type u} [order_top α] {a : α}

@[simp] lemma Ici_top : Ici (⊤ : α) = {⊤} := Ici_singleton_of_top (λ _, le_top)
@[simp] lemma Iic_top : Iic (⊤ : α) = univ := eq_univ_of_forall $ λ x, le_top
@[simp] lemma Icc_top : Icc a ⊤ = Ici a := by simp [← Ici_inter_Iic]
@[simp] lemma Ioc_top : Ioc a ⊤ = Ioi a := by simp [← Ioi_inter_Iic]

end order_top

section order_bot

variables {α : Type u} [order_bot α] {a : α}

@[simp] lemma Iic_bot : Iic (⊥ : α) = {⊥} := Iic_singleton_of_bot (λ _, bot_le)
@[simp] lemma Ici_bot : Ici (⊥ : α) = univ := @Iic_top (order_dual α) _
@[simp] lemma Icc_bot : Icc ⊥ a = Iic a := by simp [← Ici_inter_Iic]
@[simp] lemma Ico_bot : Ico ⊥ a = Iio a := by simp [← Ici_inter_Iio]

end order_bot

section linear_order
variables {α : Type u} [linear_order α] {a a₁ a₂ b b₁ b₂ c d : α}

lemma not_mem_Ici : c ∉ Ici a ↔ c < a := not_le

lemma not_mem_Iic : c ∉ Iic b ↔ b < c := not_le

lemma not_mem_Icc_of_lt (ha : c < a) : c ∉ Icc a b :=
not_mem_subset Icc_subset_Ici_self $ not_mem_Ici.mpr ha

lemma not_mem_Icc_of_gt (hb : b < c) : c ∉ Icc a b :=
not_mem_subset Icc_subset_Iic_self $ not_mem_Iic.mpr hb

lemma not_mem_Ico_of_lt (ha : c < a) : c ∉ Ico a b :=
not_mem_subset Ico_subset_Ici_self $ not_mem_Ici.mpr ha

lemma not_mem_Ioc_of_gt (hb : b < c) : c ∉ Ioc a b :=
not_mem_subset Ioc_subset_Iic_self $ not_mem_Iic.mpr hb

lemma not_mem_Ioi : c ∉ Ioi a ↔ c ≤ a := not_lt

lemma not_mem_Iio : c ∉ Iio b ↔ b ≤ c := not_lt

lemma not_mem_Ioc_of_le (ha : c ≤ a) : c ∉ Ioc a b :=
not_mem_subset Ioc_subset_Ioi_self $ not_mem_Ioi.mpr ha

lemma not_mem_Ico_of_ge (hb : b ≤ c) : c ∉ Ico a b :=
not_mem_subset Ico_subset_Iio_self $ not_mem_Iio.mpr hb

lemma not_mem_Ioo_of_le (ha : c ≤ a) : c ∉ Ioo a b :=
not_mem_subset Ioo_subset_Ioi_self $ not_mem_Ioi.mpr ha

lemma not_mem_Ioo_of_ge (hb : b ≤ c) : c ∉ Ioo a b :=
not_mem_subset Ioo_subset_Iio_self $ not_mem_Iio.mpr hb

@[simp] lemma compl_Iic : (Iic a)ᶜ = Ioi a := ext $ λ _, not_le
@[simp] lemma compl_Ici : (Ici a)ᶜ = Iio a := ext $ λ _, not_le
@[simp] lemma compl_Iio : (Iio a)ᶜ = Ici a := ext $ λ _, not_lt
@[simp] lemma compl_Ioi : (Ioi a)ᶜ = Iic a := ext $ λ _, not_lt

@[simp] lemma Ici_diff_Ici : Ici a \ Ici b = Ico a b :=
by rw [diff_eq, compl_Ici, Ici_inter_Iio]

@[simp] lemma Ici_diff_Ioi : Ici a \ Ioi b = Icc a b :=
by rw [diff_eq, compl_Ioi, Ici_inter_Iic]

@[simp] lemma Ioi_diff_Ioi : Ioi a \ Ioi b = Ioc a b :=
by rw [diff_eq, compl_Ioi, Ioi_inter_Iic]

@[simp] lemma Ioi_diff_Ici : Ioi a \ Ici b = Ioo a b :=
by rw [diff_eq, compl_Ici, Ioi_inter_Iio]

@[simp] lemma Iic_diff_Iic : Iic b \ Iic a = Ioc a b :=
by rw [diff_eq, compl_Iic, inter_comm, Ioi_inter_Iic]

@[simp] lemma Iio_diff_Iic : Iio b \ Iic a = Ioo a b :=
by rw [diff_eq, compl_Iic, inter_comm, Ioi_inter_Iio]

@[simp] lemma Iic_diff_Iio : Iic b \ Iio a = Icc a b :=
by rw [diff_eq, compl_Iio, inter_comm, Ici_inter_Iic]

@[simp] lemma Iio_diff_Iio : Iio b \ Iio a = Ico a b :=
by rw [diff_eq, compl_Iio, inter_comm, Ici_inter_Iio]

lemma Ico_subset_Ico_iff (h₁ : a₁ < b₁) :
  Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
⟨λ h, have a₂ ≤ a₁ ∧ a₁ < b₂ := h ⟨le_rfl, h₁⟩,
  ⟨this.1, le_of_not_lt $ λ h', lt_irrefl b₂ (h ⟨this.2.le, h'⟩).2⟩,
 λ ⟨h₁, h₂⟩, Ico_subset_Ico h₁ h₂⟩

lemma Ioo_subset_Ioo_iff [densely_ordered α] (h₁ : a₁ < b₁) :
  Ioo a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
⟨λ h, begin
  rcases exists_between h₁ with ⟨x, xa, xb⟩,
  split; refine le_of_not_lt (λ h', _),
  { have ab := (h ⟨xa, xb⟩).1.trans xb,
    exact lt_irrefl _ (h ⟨h', ab⟩).1 },
  { have ab := xa.trans (h ⟨xa, xb⟩).2,
    exact lt_irrefl _ (h ⟨ab, h'⟩).2 }
end, λ ⟨h₁, h₂⟩, Ioo_subset_Ioo h₁ h₂⟩

lemma Ico_eq_Ico_iff (h : a₁ < b₁ ∨ a₂ < b₂) : Ico a₁ b₁ = Ico a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
⟨λ e, begin
  simp [subset.antisymm_iff] at e, simp [le_antisymm_iff],
  cases h; simp [Ico_subset_Ico_iff h] at e;
    [ rcases e with ⟨⟨h₁, h₂⟩, e'⟩, rcases e with ⟨e', ⟨h₁, h₂⟩⟩ ];
    have := (Ico_subset_Ico_iff $ h₁.trans_lt $ h.trans_le h₂).1 e';
    tauto
end, λ ⟨h₁, h₂⟩, by rw [h₁, h₂]⟩

open_locale classical

@[simp] lemma Ioi_subset_Ioi_iff : Ioi b ⊆ Ioi a ↔ a ≤ b :=
begin
  refine ⟨λ h, _, λ h, Ioi_subset_Ioi h⟩,
  by_contradiction ba,
  exact lt_irrefl _ (h (not_le.mp ba))
end

@[simp] lemma Ioi_subset_Ici_iff [densely_ordered α] : Ioi b ⊆ Ici a ↔ a ≤ b :=
begin
  refine ⟨λ h, _, λ h, Ioi_subset_Ici h⟩,
  by_contradiction ba,
  obtain ⟨c, bc, ca⟩ : ∃c, b < c ∧ c < a := exists_between (not_le.mp ba),
  exact lt_irrefl _ (ca.trans_le (h bc))
end

@[simp] lemma Iio_subset_Iio_iff : Iio a ⊆ Iio b ↔ a ≤ b :=
begin
  refine ⟨λ h, _, λ h, Iio_subset_Iio h⟩,
  by_contradiction ab,
  exact lt_irrefl _ (h (not_le.mp ab))
end

@[simp] lemma Iio_subset_Iic_iff [densely_ordered α] : Iio a ⊆ Iic b ↔ a ≤ b :=
by rw [←diff_eq_empty, Iio_diff_Iic, Ioo_eq_empty_iff, not_lt]

/-! ### Unions of adjacent intervals -/

/-! #### Two infinite intervals -/

@[simp] lemma Iic_union_Ici : Iic a ∪ Ici a = univ := eq_univ_of_forall (λ x, le_total x a)

@[simp] lemma Iio_union_Ici : Iio a ∪ Ici a = univ := eq_univ_of_forall (λ x, lt_or_le x a)

@[simp] lemma Iic_union_Ioi : Iic a ∪ Ioi a = univ := eq_univ_of_forall (λ x, le_or_lt x a)

/-! #### A finite and an infinite interval -/

lemma Ioo_union_Ioi' (h₁ : c < b) :
  Ioo a b ∪ Ioi c = Ioi (min a c) :=
begin
  ext1 x,
  simp_rw [mem_union, mem_Ioo, mem_Ioi, min_lt_iff],
  by_cases hc : c < x,
  { tauto },
  { have hxb : x < b := (le_of_not_gt hc).trans_lt h₁,
    tauto },
end

lemma Ioo_union_Ioi (h : c < max a b) :
  Ioo a b ∪ Ioi c = Ioi (min a c) :=
begin
  cases le_total a b with hab hab; simp [hab] at h,
  { exact Ioo_union_Ioi' h },
  { rw min_comm,
    simp [*, min_eq_left_of_lt] },
end

lemma Ioi_subset_Ioo_union_Ici : Ioi a ⊆ Ioo a b ∪ Ici b :=
λ x hx, (lt_or_le x b).elim (λ hxb, or.inl ⟨hx, hxb⟩) (λ hxb, or.inr hxb)

@[simp] lemma Ioo_union_Ici_eq_Ioi (h : a < b) : Ioo a b ∪ Ici b = Ioi a :=
subset.antisymm (λ x hx, hx.elim and.left h.trans_le) Ioi_subset_Ioo_union_Ici

lemma Ici_subset_Ico_union_Ici : Ici a ⊆ Ico a b ∪ Ici b :=
λ x hx, (lt_or_le x b).elim (λ hxb, or.inl ⟨hx, hxb⟩) (λ hxb, or.inr hxb)

@[simp] lemma Ico_union_Ici_eq_Ici (h : a ≤ b) : Ico a b ∪ Ici b = Ici a :=
subset.antisymm (λ x hx, hx.elim and.left h.trans) Ici_subset_Ico_union_Ici

lemma Ico_union_Ici' (h₁ : c ≤ b) :
  Ico a b ∪ Ici c = Ici (min a c) :=
begin
  ext1 x,
  simp_rw [mem_union, mem_Ico, mem_Ici, min_le_iff],
  by_cases hc : c ≤ x,
  { tauto },
  { have hxb : x < b := (lt_of_not_ge hc).trans_le h₁,
    tauto },
end

lemma Ico_union_Ici  (h : c ≤ max a b) :
  Ico a b ∪ Ici c = Ici (min a c) :=
begin
  cases le_total a b with hab hab; simp [hab] at h,
  { exact Ico_union_Ici' h },
  { simp [*] },
end

lemma Ioi_subset_Ioc_union_Ioi : Ioi a ⊆ Ioc a b ∪ Ioi b :=
λ x hx, (le_or_lt x b).elim (λ hxb, or.inl ⟨hx, hxb⟩) (λ hxb, or.inr hxb)

@[simp] lemma Ioc_union_Ioi_eq_Ioi (h : a ≤ b) : Ioc a b ∪ Ioi b = Ioi a :=
subset.antisymm (λ x hx, hx.elim and.left h.trans_lt) Ioi_subset_Ioc_union_Ioi

lemma Ioc_union_Ioi' (h₁ : c ≤ b) :
  Ioc a b ∪ Ioi c = Ioi (min a c) :=
begin
  ext1 x,
  simp_rw [mem_union, mem_Ioc, mem_Ioi, min_lt_iff],
  by_cases hc : c < x,
  { tauto },
  { have hxb : x ≤ b := (le_of_not_gt hc).trans h₁,
    tauto },
end

lemma Ioc_union_Ioi (h : c ≤ max a b) :
  Ioc a b ∪ Ioi c = Ioi (min a c) :=
begin
  cases le_total a b with hab hab; simp [hab] at h,
  { exact Ioc_union_Ioi' h },
  { simp [*] },
end

lemma Ici_subset_Icc_union_Ioi : Ici a ⊆ Icc a b ∪ Ioi b :=
λ x hx, (le_or_lt x b).elim (λ hxb, or.inl ⟨hx, hxb⟩) (λ hxb, or.inr hxb)

@[simp] lemma Icc_union_Ioi_eq_Ici (h : a ≤ b) : Icc a b ∪ Ioi b = Ici a :=
subset.antisymm (λ x hx, hx.elim and.left $ λ hx', h.trans $ le_of_lt hx') Ici_subset_Icc_union_Ioi

lemma Ioi_subset_Ioc_union_Ici : Ioi a ⊆ Ioc a b ∪ Ici b :=
subset.trans Ioi_subset_Ioo_union_Ici (union_subset_union_left _ Ioo_subset_Ioc_self)

@[simp] lemma Ioc_union_Ici_eq_Ioi (h : a < b) : Ioc a b ∪ Ici b = Ioi a :=
subset.antisymm (λ x hx, hx.elim and.left h.trans_le) Ioi_subset_Ioc_union_Ici

lemma Ici_subset_Icc_union_Ici : Ici a ⊆ Icc a b ∪ Ici b :=
subset.trans Ici_subset_Ico_union_Ici (union_subset_union_left _ Ico_subset_Icc_self)

@[simp] lemma Icc_union_Ici_eq_Ici (h : a ≤ b) : Icc a b ∪ Ici b = Ici a :=
subset.antisymm (λ x hx, hx.elim and.left h.trans) Ici_subset_Icc_union_Ici

lemma Icc_union_Ici' (h₁ : c ≤ b) :
  Icc a b ∪ Ici c = Ici (min a c) :=
begin
  ext1 x,
  simp_rw [mem_union, mem_Icc, mem_Ici, min_le_iff],
  by_cases hc : c ≤ x,
  { tauto },
  { have hxb : x ≤ b := (le_of_not_ge hc).trans h₁,
    tauto },
end

lemma Icc_union_Ici (h : c ≤ max a b) :
  Icc a b ∪ Ici c = Ici (min a c) :=
begin
  cases le_or_lt a b with hab hab; simp [hab] at h,
  { exact Icc_union_Ici' h },
  { cases h,
    { simp [*] },
    { have hca : c ≤ a := h.trans hab.le,
      simp [*] } },
end

/-! #### An infinite and a finite interval -/

lemma Iic_subset_Iio_union_Icc : Iic b ⊆ Iio a ∪ Icc a b :=
λ x hx, (lt_or_le x a).elim (λ hxa, or.inl hxa) (λ hxa, or.inr ⟨hxa, hx⟩)

@[simp] lemma Iio_union_Icc_eq_Iic (h : a ≤ b) : Iio a ∪ Icc a b = Iic b :=
subset.antisymm (λ x hx, hx.elim (λ hx, (le_of_lt hx).trans h) and.right)
  Iic_subset_Iio_union_Icc

lemma Iio_subset_Iio_union_Ico : Iio b ⊆ Iio a ∪ Ico a b :=
λ x hx, (lt_or_le x a).elim (λ hxa, or.inl hxa) (λ hxa, or.inr ⟨hxa, hx⟩)

@[simp] lemma Iio_union_Ico_eq_Iio (h : a ≤ b) : Iio a ∪ Ico a b = Iio b :=
subset.antisymm (λ x hx, hx.elim (λ hx', lt_of_lt_of_le hx' h) and.right) Iio_subset_Iio_union_Ico

lemma Iio_union_Ico' (h₁ : c ≤ b) :
  Iio b ∪ Ico c d = Iio (max b d) :=
begin
  ext1 x,
  simp_rw [mem_union, mem_Iio, mem_Ico, lt_max_iff],
  by_cases hc : c ≤ x,
  { tauto },
  { have hxb : x < b := (lt_of_not_ge hc).trans_le h₁,
    tauto },
end

lemma Iio_union_Ico (h : min c d ≤ b) :
  Iio b ∪ Ico c d = Iio (max b d) :=
begin
  cases le_total c d with hcd hcd; simp [hcd] at h,
  { exact Iio_union_Ico' h },
  { simp [*] },
end

lemma Iic_subset_Iic_union_Ioc : Iic b ⊆ Iic a ∪ Ioc a b :=
λ x hx, (le_or_lt x a).elim (λ hxa, or.inl hxa) (λ hxa, or.inr ⟨hxa, hx⟩)

@[simp] lemma Iic_union_Ioc_eq_Iic (h : a ≤ b) : Iic a ∪ Ioc a b = Iic b :=
subset.antisymm (λ x hx, hx.elim (λ hx', le_trans hx' h) and.right) Iic_subset_Iic_union_Ioc

lemma Iic_union_Ioc' (h₁ : c < b) :
  Iic b ∪ Ioc c d = Iic (max b d) :=
begin
  ext1 x,
  simp_rw [mem_union, mem_Iic, mem_Ioc, le_max_iff],
  by_cases hc : c < x,
  { tauto },
  { have hxb : x ≤ b := (le_of_not_gt hc).trans h₁.le,
    tauto },
end

lemma Iic_union_Ioc (h : min c d < b) :
  Iic b ∪ Ioc c d = Iic (max b d) :=
begin
  cases le_total c d with hcd hcd; simp [hcd] at h,
  { exact Iic_union_Ioc' h },
  { rw max_comm,
    simp [*, max_eq_right_of_lt h] },
end

lemma Iio_subset_Iic_union_Ioo : Iio b ⊆ Iic a ∪ Ioo a b :=
λ x hx, (le_or_lt x a).elim (λ hxa, or.inl hxa) (λ hxa, or.inr ⟨hxa, hx⟩)

@[simp] lemma Iic_union_Ioo_eq_Iio (h : a < b) : Iic a ∪ Ioo a b = Iio b :=
subset.antisymm (λ x hx, hx.elim (λ hx', lt_of_le_of_lt hx' h) and.right) Iio_subset_Iic_union_Ioo

lemma Iio_union_Ioo' (h₁ : c < b) :
  Iio b ∪ Ioo c d = Iio (max b d) :=
begin
  ext x,
  cases lt_or_le x b with hba hba,
  { simp [hba, h₁] },
  { simp only [mem_Iio, mem_union_eq, mem_Ioo, lt_max_iff],
    refine or_congr iff.rfl ⟨and.right, _⟩,
    exact λ h₂, ⟨h₁.trans_le hba, h₂⟩ },
end

lemma Iio_union_Ioo (h : min c d < b) :
  Iio b ∪ Ioo c d = Iio (max b d) :=
begin
  cases le_total c d with hcd hcd; simp [hcd] at h,
  { exact Iio_union_Ioo' h },
  { rw max_comm,
    simp [*, max_eq_right_of_lt h] },
end

lemma Iic_subset_Iic_union_Icc : Iic b ⊆ Iic a ∪ Icc a b :=
subset.trans Iic_subset_Iic_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp] lemma Iic_union_Icc_eq_Iic (h : a ≤ b) : Iic a ∪ Icc a b = Iic b :=
subset.antisymm (λ x hx, hx.elim (λ hx', le_trans hx' h) and.right) Iic_subset_Iic_union_Icc

lemma Iic_union_Icc' (h₁ : c ≤ b) :
  Iic b ∪ Icc c d = Iic (max b d) :=
begin
  ext1 x,
  simp_rw [mem_union, mem_Iic, mem_Icc, le_max_iff],
  by_cases hc : c ≤ x,
  { tauto },
  { have hxb : x ≤ b := (le_of_not_ge hc).trans h₁,
    tauto },
end

lemma Iic_union_Icc (h : min c d ≤ b) :
  Iic b ∪ Icc c d = Iic (max b d) :=
begin
  cases le_or_lt c d with hcd hcd; simp [hcd] at h,
  { exact Iic_union_Icc' h },
  { cases h,
    { have hdb : d ≤ b := hcd.le.trans h,
      simp [*] },
    { simp [*] } },
end

lemma Iio_subset_Iic_union_Ico : Iio b ⊆ Iic a ∪ Ico a b :=
subset.trans Iio_subset_Iic_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp] lemma Iic_union_Ico_eq_Iio (h : a < b) : Iic a ∪ Ico a b = Iio b :=
subset.antisymm (λ x hx, hx.elim (λ hx', lt_of_le_of_lt hx' h) and.right) Iio_subset_Iic_union_Ico

/-! #### Two finite intervals, `I?o` and `Ic?` -/

lemma Ioo_subset_Ioo_union_Ico : Ioo a c ⊆ Ioo a b ∪ Ico b c :=
λ x hx, (lt_or_le x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)

@[simp] lemma Ioo_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b ≤ c) : Ioo a b ∪ Ico b c = Ioo a c :=
subset.antisymm
  (λ x hx, hx.elim (λ hx, ⟨hx.1, hx.2.trans_le h₂⟩) (λ hx, ⟨h₁.trans_le hx.1, hx.2⟩))
  Ioo_subset_Ioo_union_Ico

lemma Ico_subset_Ico_union_Ico : Ico a c ⊆ Ico a b ∪ Ico b c :=
λ x hx, (lt_or_le x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)

@[simp] lemma Ico_union_Ico_eq_Ico (h₁ : a ≤ b) (h₂ : b ≤ c) : Ico a b ∪ Ico b c = Ico a c :=
subset.antisymm
  (λ x hx, hx.elim (λ hx, ⟨hx.1, hx.2.trans_le h₂⟩) (λ hx, ⟨h₁.trans hx.1, hx.2⟩))
  Ico_subset_Ico_union_Ico

lemma Ico_union_Ico' (h₁ : c ≤ b) (h₂ : a ≤ d) :
  Ico a b ∪ Ico c d = Ico (min a c) (max b d) :=
begin
  ext1 x,
  simp_rw [mem_union, mem_Ico, min_le_iff, lt_max_iff],
  by_cases hc : c ≤ x; by_cases hd : x < d,
  { tauto },
  { have hax : a ≤ x := h₂.trans (le_of_not_gt hd),
    tauto },
  { have hxb : x < b := (lt_of_not_ge hc).trans_le h₁,
    tauto },
  { tauto },
end

lemma Ico_union_Ico (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
  Ico a b ∪ Ico c d = Ico (min a c) (max b d) :=
begin
  cases le_total a b with hab hab; cases le_total c d with hcd hcd; simp [hab, hcd] at h₁ h₂,
  { exact Ico_union_Ico' h₂ h₁ },
  all_goals { simp [*] },
end

lemma Icc_subset_Ico_union_Icc : Icc a c ⊆ Ico a b ∪ Icc b c :=
λ x hx, (lt_or_le x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)

@[simp] lemma Ico_union_Icc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : Ico a b ∪ Icc b c = Icc a c :=
subset.antisymm
  (λ x hx, hx.elim (λ hx, ⟨hx.1, hx.2.le.trans h₂⟩) (λ hx, ⟨h₁.trans hx.1, hx.2⟩))
  Icc_subset_Ico_union_Icc

lemma Ioc_subset_Ioo_union_Icc : Ioc a c ⊆ Ioo a b ∪ Icc b c :=
λ x hx, (lt_or_le x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)

@[simp] lemma Ioo_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b ≤ c) : Ioo a b ∪ Icc b c = Ioc a c :=
subset.antisymm
  (λ x hx, hx.elim (λ hx, ⟨hx.1, hx.2.le.trans h₂⟩)
    (λ hx, ⟨h₁.trans_le hx.1, hx.2⟩))
  Ioc_subset_Ioo_union_Icc

/-! #### Two finite intervals, `I?c` and `Io?` -/

lemma Ioo_subset_Ioc_union_Ioo : Ioo a c ⊆ Ioc a b ∪ Ioo b c :=
λ x hx, (le_or_lt x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)

@[simp] lemma Ioc_union_Ioo_eq_Ioo (h₁ : a ≤ b) (h₂ : b < c) : Ioc a b ∪ Ioo b c = Ioo a c :=
subset.antisymm
  (λ x hx, hx.elim (λ hx, ⟨hx.1, hx.2.trans_lt h₂⟩) (λ hx, ⟨h₁.trans_lt hx.1, hx.2⟩))
  Ioo_subset_Ioc_union_Ioo

lemma Ico_subset_Icc_union_Ioo : Ico a c ⊆ Icc a b ∪ Ioo b c :=
λ x hx, (le_or_lt x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)

@[simp] lemma Icc_union_Ioo_eq_Ico (h₁ : a ≤ b) (h₂ : b < c) : Icc a b ∪ Ioo b c = Ico a c :=
subset.antisymm
  (λ x hx, hx.elim (λ hx, ⟨hx.1, hx.2.trans_lt h₂⟩)
    (λ hx, ⟨h₁.trans hx.1.le, hx.2⟩))
  Ico_subset_Icc_union_Ioo

lemma Icc_subset_Icc_union_Ioc : Icc a c ⊆ Icc a b ∪ Ioc b c :=
λ x hx, (le_or_lt x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)

@[simp] lemma Icc_union_Ioc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : Icc a b ∪ Ioc b c = Icc a c :=
subset.antisymm
  (λ x hx, hx.elim (λ hx, ⟨hx.1, hx.2.trans h₂⟩) (λ hx, ⟨h₁.trans hx.1.le, hx.2⟩))
  Icc_subset_Icc_union_Ioc

lemma Ioc_subset_Ioc_union_Ioc : Ioc a c ⊆ Ioc a b ∪ Ioc b c :=
λ x hx, (le_or_lt x b).elim (λ hxb, or.inl ⟨hx.1, hxb⟩) (λ hxb, or.inr ⟨hxb, hx.2⟩)

@[simp] lemma Ioc_union_Ioc_eq_Ioc (h₁ : a ≤ b) (h₂ : b ≤ c) : Ioc a b ∪ Ioc b c = Ioc a c :=
subset.antisymm
  (λ x hx, hx.elim (λ hx, ⟨hx.1, hx.2.trans h₂⟩) (λ hx, ⟨h₁.trans_lt hx.1, hx.2⟩))
  Ioc_subset_Ioc_union_Ioc

lemma Ioc_union_Ioc' (h₁ : c ≤ b) (h₂ : a ≤ d) :
  Ioc a b ∪ Ioc c d = Ioc (min a c) (max b d) :=
begin
  ext1 x,
  simp_rw [mem_union, mem_Ioc, min_lt_iff, le_max_iff],
  by_cases hc : c < x; by_cases hd : x ≤ d,
  { tauto },
  { have hax : a < x := h₂.trans_lt (lt_of_not_ge hd),
    tauto },
  { have hxb : x ≤ b := (le_of_not_gt hc).trans h₁,
    tauto },
  { tauto },
end

lemma Ioc_union_Ioc (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
  Ioc a b ∪ Ioc c d = Ioc (min a c) (max b d) :=
begin
  cases le_total a b with hab hab; cases le_total c d with hcd hcd; simp [hab, hcd] at h₁ h₂,
  { exact Ioc_union_Ioc' h₂ h₁ },
  all_goals { simp [*] },
end

/-! #### Two finite intervals with a common point -/

lemma Ioo_subset_Ioc_union_Ico : Ioo a c ⊆ Ioc a b ∪ Ico b c :=
subset.trans Ioo_subset_Ioc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp] lemma Ioc_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b < c) : Ioc a b ∪ Ico b c = Ioo a c :=
subset.antisymm
  (λ x hx, hx.elim (λ hx', ⟨hx'.1, hx'.2.trans_lt h₂⟩) (λ hx', ⟨h₁.trans_le hx'.1, hx'.2⟩))
  Ioo_subset_Ioc_union_Ico

lemma Ico_subset_Icc_union_Ico : Ico a c ⊆ Icc a b ∪ Ico b c :=
subset.trans Ico_subset_Icc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp] lemma Icc_union_Ico_eq_Ico (h₁ : a ≤ b) (h₂ : b < c) : Icc a b ∪ Ico b c = Ico a c :=
subset.antisymm
  (λ x hx, hx.elim (λ hx, ⟨hx.1, hx.2.trans_lt h₂⟩) (λ hx, ⟨h₁.trans hx.1, hx.2⟩))
  Ico_subset_Icc_union_Ico

lemma Icc_subset_Icc_union_Icc : Icc a c ⊆ Icc a b ∪ Icc b c :=
subset.trans Icc_subset_Icc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp] lemma Icc_union_Icc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : Icc a b ∪ Icc b c = Icc a c :=
subset.antisymm
  (λ x hx, hx.elim (λ hx, ⟨hx.1, hx.2.trans h₂⟩) (λ hx, ⟨h₁.trans hx.1, hx.2⟩))
  Icc_subset_Icc_union_Icc

lemma Icc_union_Icc' (h₁ : c ≤ b) (h₂ : a ≤ d) :
  Icc a b ∪ Icc c d = Icc (min a c) (max b d) :=
begin
  ext1 x,
  simp_rw [mem_union, mem_Icc, min_le_iff, le_max_iff],
  by_cases hc : c ≤ x; by_cases hd : x ≤ d,
  { tauto },
  { have hax : a ≤ x := h₂.trans (le_of_not_ge hd),
    tauto },
  { have hxb : x ≤ b := (le_of_not_ge hc).trans h₁,
    tauto },
  { tauto }
end

/--
We cannot replace `<` by `≤` in the hypotheses.
Otherwise for `b < a = d < c` the l.h.s. is `∅` and the r.h.s. is `{a}`.
-/
lemma Icc_union_Icc (h₁ : min a b < max c d) (h₂ : min c d < max a b) :
  Icc a b ∪ Icc c d = Icc (min a c) (max b d) :=
begin
  cases le_or_lt a b with hab hab; cases le_or_lt c d with hcd hcd;
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, min_eq_left_of_lt,
    min_eq_right_of_lt, max_eq_left_of_lt, max_eq_right_of_lt, hab, hcd] at h₁ h₂,
  { exact Icc_union_Icc' h₂.le h₁.le },
  all_goals { simp [*, min_eq_left_of_lt, max_eq_left_of_lt, min_eq_right_of_lt,
    max_eq_right_of_lt] },
end

lemma Ioc_subset_Ioc_union_Icc : Ioc a c ⊆ Ioc a b ∪ Icc b c :=
subset.trans Ioc_subset_Ioc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp] lemma Ioc_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b ≤ c) : Ioc a b ∪ Icc b c = Ioc a c :=
subset.antisymm
  (λ x hx, hx.elim (λ hx, ⟨hx.1, hx.2.trans h₂⟩) (λ hx, ⟨h₁.trans_le hx.1, hx.2⟩))
  Ioc_subset_Ioc_union_Icc

lemma Ioo_union_Ioo' (h₁ : c < b) (h₂ : a < d) :
  Ioo a b ∪ Ioo c d = Ioo (min a c) (max b d) :=
begin
  ext1 x,
  simp_rw [mem_union, mem_Ioo, min_lt_iff, lt_max_iff],
  by_cases hc : c < x; by_cases hd : x < d,
  { tauto },
  { have hax : a < x := h₂.trans_le (le_of_not_lt hd),
    tauto },
  { have hxb : x < b := (le_of_not_lt hc).trans_lt h₁,
    tauto },
  { tauto }
end

lemma Ioo_union_Ioo (h₁ : min a b < max c d) (h₂ : min c d < max a b) :
  Ioo a b ∪ Ioo c d = Ioo (min a c) (max b d) :=
begin
  cases le_total a b with hab hab; cases le_total c d with hcd hcd;
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hab, hcd] at h₁ h₂,
  { exact Ioo_union_Ioo' h₂ h₁ },
  all_goals {
    simp [*, min_eq_left_of_lt, min_eq_right_of_lt, max_eq_left_of_lt, max_eq_right_of_lt,
      le_of_lt h₂, le_of_lt h₁] },
end

end linear_order

section lattice

section inf

variables {α : Type u} [semilattice_inf α]

@[simp] lemma Iic_inter_Iic {a b : α} : Iic a ∩ Iic b = Iic (a ⊓ b) :=
by { ext x, simp [Iic] }

@[simp] lemma Iio_inter_Iio [is_total α (≤)] {a b : α} : Iio a ∩ Iio b = Iio (a ⊓ b) :=
by { ext x, simp [Iio] }

end inf

section sup

variables {α : Type u} [semilattice_sup α]

@[simp] lemma Ici_inter_Ici {a b : α} : Ici a ∩ Ici b = Ici (a ⊔ b) :=
by { ext x, simp [Ici] }

@[simp] lemma Ioi_inter_Ioi [is_total α (≤)] {a b : α} : Ioi a ∩ Ioi b = Ioi (a ⊔ b) :=
by { ext x, simp [Ioi] }

end sup

section both

variables {α : Type u} [lattice α] [ht : is_total α (≤)] {a b c a₁ a₂ b₁ b₂ : α}

lemma Icc_inter_Icc : Icc a₁ b₁ ∩ Icc a₂ b₂ = Icc (a₁ ⊔ a₂) (b₁ ⊓ b₂) :=
by simp only [Ici_inter_Iic.symm, Ici_inter_Ici.symm, Iic_inter_Iic.symm]; ac_refl

@[simp] lemma Icc_inter_Icc_eq_singleton (hab : a ≤ b) (hbc : b ≤ c) :
  Icc a b ∩ Icc b c = {b} :=
by rw [Icc_inter_Icc, sup_of_le_right hab, inf_of_le_left hbc, Icc_self]

include ht

lemma Ico_inter_Ico : Ico a₁ b₁ ∩ Ico a₂ b₂ = Ico (a₁ ⊔ a₂) (b₁ ⊓ b₂) :=
by simp only [Ici_inter_Iio.symm, Ici_inter_Ici.symm, Iio_inter_Iio.symm]; ac_refl

lemma Ioc_inter_Ioc : Ioc a₁ b₁ ∩ Ioc a₂ b₂ = Ioc (a₁ ⊔ a₂) (b₁ ⊓ b₂) :=
by simp only [Ioi_inter_Iic.symm, Ioi_inter_Ioi.symm, Iic_inter_Iic.symm]; ac_refl

lemma Ioo_inter_Ioo : Ioo a₁ b₁ ∩ Ioo a₂ b₂ = Ioo (a₁ ⊔ a₂) (b₁ ⊓ b₂) :=
by simp only [Ioi_inter_Iio.symm, Ioi_inter_Ioi.symm, Iio_inter_Iio.symm]; ac_refl

end both

lemma Icc_bot_top {α} [bounded_lattice α] : Icc (⊥ : α) ⊤ = univ := by simp

end lattice

section linear_order
variables {α : Type u} [linear_order α] {a a₁ a₂ b b₁ b₂ c d : α}

lemma Ioc_inter_Ioo_of_left_lt (h : b₁ < b₂) : Ioc a₁ b₁ ∩ Ioo a₂ b₂ = Ioc (max a₁ a₂) b₁ :=
ext $ λ x, by simp [and_assoc, @and.left_comm (x ≤ _),
  and_iff_left_iff_imp.2 (λ h', lt_of_le_of_lt h' h)]

lemma Ioc_inter_Ioo_of_right_le (h : b₂ ≤ b₁) : Ioc a₁ b₁ ∩ Ioo a₂ b₂ = Ioo (max a₁ a₂) b₂ :=
ext $ λ x, by simp [and_assoc, @and.left_comm (x ≤ _),
  and_iff_right_iff_imp.2 (λ h', ((le_of_lt h').trans h))]

lemma Ioo_inter_Ioc_of_left_le (h : b₁ ≤ b₂) : Ioo a₁ b₁ ∩ Ioc a₂ b₂ = Ioo (max a₁ a₂) b₁ :=
by rw [inter_comm, Ioc_inter_Ioo_of_right_le h, max_comm]

lemma Ioo_inter_Ioc_of_right_lt (h : b₂ < b₁) : Ioo a₁ b₁ ∩ Ioc a₂ b₂ = Ioc (max a₁ a₂) b₂ :=
by rw [inter_comm, Ioc_inter_Ioo_of_left_lt h, max_comm]

lemma Iic_inter_Ioc_of_le (h : a₂ ≤ a) : Iic a₂ ∩ Ioc a₁ a = Ioc a₁ a₂ :=
ext $ λ x, ⟨λ H, ⟨H.2.1, H.1⟩, λ H, ⟨H.2, H.1, H.2.trans h⟩⟩

@[simp] lemma Ico_diff_Iio : Ico a b \ Iio c = Ico (max a c) b :=
ext $ by simp [Ico, Iio, iff_def, max_le_iff] {contextual:=tt}

@[simp] lemma Ico_inter_Iio : Ico a b ∩ Iio c = Ico a (min b c) :=
ext $ by simp [Ico, Iio, iff_def, lt_min_iff] {contextual:=tt}

@[simp] lemma Ioc_union_Ioc_right : Ioc a b ∪ Ioc a c = Ioc a (max b c) :=
by rw [Ioc_union_Ioc, min_self]; exact (min_le_left _ _).trans (le_max_left _ _)

@[simp] lemma Ioc_union_Ioc_left : Ioc a c ∪ Ioc b c = Ioc (min a b) c :=
by rw [Ioc_union_Ioc, max_self]; exact (min_le_right _ _).trans (le_max_right _ _)

@[simp] lemma Ioc_union_Ioc_symm : Ioc a b ∪ Ioc b a = Ioc (min a b) (max a b) :=
by { rw max_comm, apply Ioc_union_Ioc; rw max_comm; exact min_le_max }

@[simp] lemma Ioc_union_Ioc_union_Ioc_cycle :
  Ioc a b ∪ Ioc b c ∪ Ioc c a = Ioc (min a (min b c)) (max a (max b c)) :=
begin
  rw [Ioc_union_Ioc, Ioc_union_Ioc],
  ac_refl,
  all_goals { solve_by_elim [min_le_of_left_le, min_le_of_right_le, le_max_of_le_left,
    le_max_of_le_right, le_refl] { max_depth := 5 }}
end

end linear_order

/-! ### Lemmas about membership of arithmetic operations -/

section ordered_comm_group

variables {α : Type*} [ordered_comm_group α] {a b c d : α}

/-! `inv_mem_Ixx_iff`, `sub_mem_Ixx_iff` -/
@[to_additive] lemma inv_mem_Icc_iff : a⁻¹ ∈ set.Icc c d ↔ a ∈ set.Icc (d⁻¹) (c⁻¹) :=
(and_comm _ _).trans $ and_congr inv_le' le_inv'
@[to_additive] lemma inv_mem_Ico_iff : a⁻¹ ∈ set.Ico c d ↔ a ∈ set.Ioc (d⁻¹) (c⁻¹) :=
(and_comm _ _).trans $ and_congr inv_lt' le_inv'
@[to_additive] lemma inv_mem_Ioc_iff : a⁻¹ ∈ set.Ioc c d ↔ a ∈ set.Ico (d⁻¹) (c⁻¹) :=
(and_comm _ _).trans $ and_congr inv_le' lt_inv'
@[to_additive] lemma inv_mem_Ioo_iff : a⁻¹ ∈ set.Ioo c d ↔ a ∈ set.Ioo (d⁻¹) (c⁻¹) :=
(and_comm _ _).trans $ and_congr inv_lt' lt_inv'

end ordered_comm_group

section ordered_add_comm_group

variables {α : Type*} [ordered_add_comm_group α] {a b c d : α}

/-! `add_mem_Ixx_iff_left` -/
lemma add_mem_Icc_iff_left : a + b ∈ set.Icc c d ↔ a ∈ set.Icc (c - b) (d - b) :=
(and_congr sub_le_iff_le_add le_sub_iff_add_le).symm
lemma add_mem_Ico_iff_left : a + b ∈ set.Ico c d ↔ a ∈ set.Ico (c - b) (d - b) :=
(and_congr sub_le_iff_le_add lt_sub_iff_add_lt).symm
lemma add_mem_Ioc_iff_left : a + b ∈ set.Ioc c d ↔ a ∈ set.Ioc (c - b) (d - b) :=
(and_congr sub_lt_iff_lt_add le_sub_iff_add_le).symm
lemma add_mem_Ioo_iff_left : a + b ∈ set.Ioo c d ↔ a ∈ set.Ioo (c - b) (d - b) :=
(and_congr sub_lt_iff_lt_add lt_sub_iff_add_lt).symm

/-! `add_mem_Ixx_iff_right` -/
lemma add_mem_Icc_iff_right : a + b ∈ set.Icc c d ↔ b ∈ set.Icc (c - a) (d - a) :=
(and_congr sub_le_iff_le_add' le_sub_iff_add_le').symm
lemma add_mem_Ico_iff_right : a + b ∈ set.Ico c d ↔ b ∈ set.Ico (c - a) (d - a) :=
(and_congr sub_le_iff_le_add' lt_sub_iff_add_lt').symm
lemma add_mem_Ioc_iff_right : a + b ∈ set.Ioc c d ↔ b ∈ set.Ioc (c - a) (d - a) :=
(and_congr sub_lt_iff_lt_add' le_sub_iff_add_le').symm
lemma add_mem_Ioo_iff_right : a + b ∈ set.Ioo c d ↔ b ∈ set.Ioo (c - a) (d - a) :=
(and_congr sub_lt_iff_lt_add' lt_sub_iff_add_lt').symm

/-! `sub_mem_Ixx_iff_left` -/
lemma sub_mem_Icc_iff_left : a - b ∈ set.Icc c d ↔ a ∈ set.Icc (c + b) (d + b) :=
and_congr le_sub_iff_add_le sub_le_iff_le_add
lemma sub_mem_Ico_iff_left : a - b ∈ set.Ico c d ↔ a ∈ set.Ico (c + b) (d + b) :=
and_congr le_sub_iff_add_le sub_lt_iff_lt_add
lemma sub_mem_Ioc_iff_left : a - b ∈ set.Ioc c d ↔ a ∈ set.Ioc (c + b) (d + b) :=
and_congr lt_sub_iff_add_lt sub_le_iff_le_add
lemma sub_mem_Ioo_iff_left : a - b ∈ set.Ioo c d ↔ a ∈ set.Ioo (c + b) (d + b) :=
and_congr lt_sub_iff_add_lt sub_lt_iff_lt_add

/-! `sub_mem_Ixx_iff_right` -/
lemma sub_mem_Icc_iff_right : a - b ∈ set.Icc c d ↔ b ∈ set.Icc (a - d) (a - c) :=
(and_comm _ _).trans $ and_congr sub_le le_sub
lemma sub_mem_Ico_iff_right : a - b ∈ set.Ico c d ↔ b ∈ set.Ioc (a - d) (a - c) :=
(and_comm _ _).trans $ and_congr sub_lt le_sub
lemma sub_mem_Ioc_iff_right : a - b ∈ set.Ioc c d ↔ b ∈ set.Ico (a - d) (a - c) :=
(and_comm _ _).trans $ and_congr sub_le lt_sub
lemma sub_mem_Ioo_iff_right : a - b ∈ set.Ioo c d ↔ b ∈ set.Ioo (a - d) (a - c) :=
(and_comm _ _).trans $ and_congr sub_lt lt_sub

-- I think that symmetric intervals deserve attention and API: they arise all the time,
-- for instance when considering metric balls in `ℝ`.
lemma mem_Icc_iff_abs_le {R : Type*} [linear_ordered_add_comm_group R] {x y z : R} :
  abs (x - y) ≤ z ↔ y ∈ Icc (x - z) (x + z) :=
abs_le.trans $ (and_comm _ _).trans $ and_congr sub_le neg_le_sub_iff_le_add

end ordered_add_comm_group

section linear_ordered_add_comm_group

variables {α : Type u} [linear_ordered_add_comm_group α]

/-- If we remove a smaller interval from a larger, the result is nonempty -/
lemma nonempty_Ico_sdiff {x dx y dy : α} (h : dy < dx) (hx : 0 < dx) :
  nonempty ↥(Ico x (x + dx) \ Ico y (y + dy)) :=
begin
  cases lt_or_le x y with h' h',
  { use x, simp [*, not_le.2 h'] },
  { use max x (x + dy), simp [*, le_refl] }
end

end linear_ordered_add_comm_group

end set

namespace order_iso
variables {α β : Type*}

open set

section preorder
variables [preorder α] [preorder β]

@[simp] lemma preimage_Iic (e : α ≃o β) (b : β) : e ⁻¹' (Iic b) = Iic (e.symm b) :=
by { ext x, simp [← e.le_iff_le] }

@[simp] lemma preimage_Ici (e : α ≃o β) (b : β) : e ⁻¹' (Ici b) = Ici (e.symm b) :=
by { ext x, simp [← e.le_iff_le] }

@[simp] lemma preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' (Iio b) = Iio (e.symm b) :=
by { ext x, simp [← e.lt_iff_lt] }

@[simp] lemma preimage_Ioi (e : α ≃o β) (b : β) : e ⁻¹' (Ioi b) = Ioi (e.symm b) :=
by { ext x, simp [← e.lt_iff_lt] }

@[simp] lemma preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' (Icc a b) = Icc (e.symm a) (e.symm b) :=
by simp [← Ici_inter_Iic]

@[simp] lemma preimage_Ico (e : α ≃o β) (a b : β) : e ⁻¹' (Ico a b) = Ico (e.symm a) (e.symm b) :=
by simp [← Ici_inter_Iio]

@[simp] lemma preimage_Ioc (e : α ≃o β) (a b : β) : e ⁻¹' (Ioc a b) = Ioc (e.symm a) (e.symm b) :=
by simp [← Ioi_inter_Iic]

@[simp] lemma preimage_Ioo (e : α ≃o β) (a b : β) : e ⁻¹' (Ioo a b) = Ioo (e.symm a) (e.symm b) :=
by simp [← Ioi_inter_Iio]

end preorder

/-- Order isomorphism between `Iic (⊤ : α)` and `α` when `α` has a top element -/
def Iic_top [order_top α] : set.Iic (⊤ : α) ≃o α :=
{ map_rel_iff' := λ x y, by refl,
  .. (@equiv.subtype_univ_equiv α (set.Iic (⊤ : α)) (λ x, le_top)), }

/-- Order isomorphism between `Ici (⊥ : α)` and `α` when `α` has a bottom element -/
def Ici_bot [order_bot α] : set.Ici (⊥ : α) ≃o α :=
{ map_rel_iff' := λ x y, by refl,
  .. (@equiv.subtype_univ_equiv α (set.Ici (⊥ : α)) (λ x, bot_le)) }

end order_iso
