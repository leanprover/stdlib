/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.multiset.erase_dup

/-!
# Preparations for defining operations on `finset`.

The operations here ignore multiplicities,
and preparatory for defining the corresponding operations on `finset`.
-/

namespace multiset
open list

variables {α : Type*} [decidable_eq α]
/-! ### finset insert -/

/-- `ndinsert a s` is the lift of the list `insert` operation. This operation
  does not respect multiplicities, unlike `cons`, but it is suitable as
  an insert operation on `finset`. -/
def ndinsert (a : α) (s : multiset α) : multiset α :=
quot.lift_on s (λ l, (l.insert a : multiset α))
  (λ s t p, quot.sound (p.insert a))

@[simp] theorem coe_ndinsert (a : α) (l : list α) : ndinsert a l = (insert a l : list α) := rfl

@[simp] theorem ndinsert_zero (a : α) : ndinsert a 0 = a ::ₘ 0 := rfl

@[simp, priority 980]
theorem ndinsert_of_mem {a : α} {s : multiset α} : a ∈ s → ndinsert a s = s :=
quot.induction_on s $ λ l h, congr_arg coe $ insert_of_mem h

@[simp, priority 980]
theorem ndinsert_of_not_mem {a : α} {s : multiset α} : a ∉ s → ndinsert a s = a ::ₘ s :=
quot.induction_on s $ λ l h, congr_arg coe $ insert_of_not_mem h

@[simp] theorem mem_ndinsert {a b : α} {s : multiset α} : a ∈ ndinsert b s ↔ a = b ∨ a ∈ s :=
quot.induction_on s $ λ l, mem_insert_iff

@[simp] theorem le_ndinsert_self (a : α) (s : multiset α) : s ≤ ndinsert a s :=
quot.induction_on s $ λ l, (sublist_of_suffix $ suffix_insert _ _).subperm

@[simp] theorem mem_ndinsert_self (a : α) (s : multiset α) : a ∈ ndinsert a s :=
mem_ndinsert.2 (or.inl rfl)

theorem mem_ndinsert_of_mem {a b : α} {s : multiset α} (h : a ∈ s) : a ∈ ndinsert b s :=
mem_ndinsert.2 (or.inr h)

@[simp, priority 980]
theorem length_ndinsert_of_mem {a : α} {s : multiset α} (h : a ∈ s) :
  card (ndinsert a s) = card s :=
by simp [h]

@[simp, priority 980]
theorem length_ndinsert_of_not_mem {a : α} {s : multiset α} (h : a ∉ s) :
  card (ndinsert a s) = card s + 1 :=
by simp [h]

theorem erase_dup_cons {a : α} {s : multiset α} :
  erase_dup (a ::ₘ s) = ndinsert a (erase_dup s) :=
by by_cases a ∈ s; simp [h]

theorem nodup_ndinsert (a : α) {s : multiset α} : nodup s → nodup (ndinsert a s) :=
quot.induction_on s $ λ l, nodup_insert

theorem ndinsert_le {a : α} {s t : multiset α} : ndinsert a s ≤ t ↔ s ≤ t ∧ a ∈ t :=
⟨λ h, ⟨le_trans (le_ndinsert_self _ _) h, mem_of_le h (mem_ndinsert_self _ _)⟩,
 λ ⟨l, m⟩, if h : a ∈ s then by simp [h, l] else
   by rw [ndinsert_of_not_mem h, ← cons_erase m, cons_le_cons_iff,
          ← le_cons_of_not_mem h, cons_erase m]; exact l⟩

lemma attach_ndinsert (a : α) (s : multiset α) :
  (s.ndinsert a).attach =
    ndinsert ⟨a, mem_ndinsert_self a s⟩ (s.attach.map $ λp, ⟨p.1, mem_ndinsert_of_mem p.2⟩) :=
have eq : ∀h : ∀(p : {x // x ∈ s}), p.1 ∈ s,
    (λ (p : {x // x ∈ s}), ⟨p.val, h p⟩ : {x // x ∈ s} → {x // x ∈ s}) = id, from
  assume h, funext $ assume p, subtype.eq rfl,
have ∀t (eq : s.ndinsert a = t), t.attach = ndinsert ⟨a, eq ▸ mem_ndinsert_self a s⟩
  (s.attach.map $ λp, ⟨p.1, eq ▸ mem_ndinsert_of_mem p.2⟩),
begin
  intros t ht,
  by_cases a ∈ s,
  { rw [ndinsert_of_mem h] at ht,
    subst ht,
    rw [eq, map_id, ndinsert_of_mem (mem_attach _ _)] },
  { rw [ndinsert_of_not_mem h] at ht,
    subst ht,
    simp [attach_cons, h] }
end,
this _ rfl

@[simp] theorem disjoint_ndinsert_left {a : α} {s t : multiset α} :
  disjoint (ndinsert a s) t ↔ a ∉ t ∧ disjoint s t :=
iff.trans (by simp [disjoint]) disjoint_cons_left

@[simp] theorem disjoint_ndinsert_right {a : α} {s t : multiset α} :
  disjoint s (ndinsert a t) ↔ a ∉ s ∧ disjoint s t :=
by rw [disjoint_comm, disjoint_ndinsert_left]; tauto

/-! ### finset union -/

/-- `ndunion s t` is the lift of the list `union` operation. This operation
  does not respect multiplicities, unlike `s ∪ t`, but it is suitable as
  a union operation on `finset`. (`s ∪ t` would also work as a union operation
  on finset, but this is more efficient.) -/
def ndunion (s t : multiset α) : multiset α :=
quotient.lift_on₂ s t (λ l₁ l₂, (l₁.union l₂ : multiset α)) $ λ v₁ v₂ w₁ w₂ p₁ p₂,
  quot.sound $ p₁.union p₂

@[simp] theorem coe_ndunion (l₁ l₂ : list α) : @ndunion α _ l₁ l₂ = (l₁ ∪ l₂ : list α) := rfl

@[simp] theorem zero_ndunion (s : multiset α) : ndunion 0 s = s :=
quot.induction_on s $ λ l, rfl

@[simp] theorem cons_ndunion (s t : multiset α) (a : α) :
  ndunion (a ::ₘ s) t = ndinsert a (ndunion s t) :=
quotient.induction_on₂ s t $ λ l₁ l₂, rfl

@[simp] theorem mem_ndunion {s t : multiset α} {a : α} : a ∈ ndunion s t ↔ a ∈ s ∨ a ∈ t :=
quotient.induction_on₂ s t $ λ l₁ l₂, list.mem_union

theorem le_ndunion_right (s t : multiset α) : t ≤ ndunion s t :=
quotient.induction_on₂ s t $ λ l₁ l₂,
(sublist_of_suffix $ suffix_union_right _ _).subperm

theorem subset_ndunion_right (s t : multiset α) : t ⊆ ndunion s t :=
subset_of_le (le_ndunion_right s t)

theorem ndunion_le_add (s t : multiset α) : ndunion s t ≤ s + t :=
quotient.induction_on₂ s t $ λ l₁ l₂, (union_sublist_append _ _).subperm

theorem ndunion_le {s t u : multiset α} : ndunion s t ≤ u ↔ s ⊆ u ∧ t ≤ u :=
multiset.induction_on s (by simp)
begin
  simp only [ndinsert_le, cons_ndunion, cons_subset] {contextual := tt},
  tauto,
end

theorem subset_ndunion_left (s t : multiset α) : s ⊆ ndunion s t :=
λ a h, mem_ndunion.2 $ or.inl h

theorem le_ndunion_left {s} (t : multiset α) (d : nodup s) : s ≤ ndunion s t :=
(le_iff_subset d).2 $ subset_ndunion_left _ _

theorem ndunion_le_union (s t : multiset α) : ndunion s t ≤ s ∪ t :=
ndunion_le.2 ⟨subset_of_le (le_union_left _ _), le_union_right _ _⟩

theorem nodup_ndunion (s : multiset α) {t : multiset α} : nodup t → nodup (ndunion s t) :=
quotient.induction_on₂ s t $ λ l₁ l₂, list.nodup_union _

@[simp, priority 980]
theorem ndunion_eq_union {s t : multiset α} (d : nodup s) : ndunion s t = s ∪ t :=
le_antisymm (ndunion_le_union _ _) $ union_le (le_ndunion_left _ d) (le_ndunion_right _ _)

theorem erase_dup_add (s t : multiset α) : erase_dup (s + t) = ndunion s (erase_dup t) :=
quotient.induction_on₂ s t $ λ l₁ l₂, congr_arg coe $ erase_dup_append _ _

/-! ### finset inter -/

/-- `ndinter s t` is the lift of the list `∩` operation. This operation
  does not respect multiplicities, unlike `s ∩ t`, but it is suitable as
  an intersection operation on `finset`. (`s ∩ t` would also work as a union operation
  on finset, but this is more efficient.) -/
def ndinter (s t : multiset α) : multiset α := filter (∈ t) s

@[simp] theorem coe_ndinter (l₁ l₂ : list α) : @ndinter α _ l₁ l₂ = (l₁ ∩ l₂ : list α) := rfl

@[simp] theorem zero_ndinter (s : multiset α) : ndinter 0 s = 0 := rfl

@[simp, priority 980]
theorem cons_ndinter_of_mem {a : α} (s : multiset α) {t : multiset α} (h : a ∈ t) :
  ndinter (a ::ₘ s) t = a ::ₘ (ndinter s t) := by simp [ndinter, h]

@[simp, priority 980]
theorem ndinter_cons_of_not_mem {a : α} (s : multiset α) {t : multiset α} (h : a ∉ t) :
  ndinter (a ::ₘ s) t = ndinter s t := by simp [ndinter, h]

@[simp] theorem mem_ndinter {s t : multiset α} {a : α} : a ∈ ndinter s t ↔ a ∈ s ∧ a ∈ t :=
mem_filter

@[simp]
theorem nodup_ndinter {s : multiset α} (t : multiset α) : nodup s → nodup (ndinter s t) :=
nodup_filter _

theorem le_ndinter {s t u : multiset α} : s ≤ ndinter t u ↔ s ≤ t ∧ s ⊆ u :=
by simp [ndinter, le_filter, subset_iff]

theorem ndinter_le_left (s t : multiset α) : ndinter s t ≤ s :=
(le_ndinter.1 (le_refl _)).1

theorem ndinter_subset_left (s t : multiset α) : ndinter s t ⊆ s :=
subset_of_le (ndinter_le_left s t)

theorem ndinter_subset_right (s t : multiset α) : ndinter s t ⊆ t :=
(le_ndinter.1 (le_refl _)).2

theorem ndinter_le_right {s} (t : multiset α) (d : nodup s) : ndinter s t ≤ t :=
(le_iff_subset $ nodup_ndinter _ d).2 (ndinter_subset_right _ _)

theorem inter_le_ndinter (s t : multiset α) : s ∩ t ≤ ndinter s t :=
le_ndinter.2 ⟨inter_le_left _ _, subset_of_le $ inter_le_right _ _⟩

@[simp, priority 980]
theorem ndinter_eq_inter {s t : multiset α} (d : nodup s) : ndinter s t = s ∩ t :=
le_antisymm (le_inter (ndinter_le_left _ _) (ndinter_le_right _ d)) (inter_le_ndinter _ _)

theorem ndinter_eq_zero_iff_disjoint {s t : multiset α} : ndinter s t = 0 ↔ disjoint s t :=
by rw ← subset_zero; simp [subset_iff, disjoint]

end multiset
