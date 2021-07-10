/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Chris Hughes
-/
import data.list.nodup
import data.fin

/-!
# List duplicates

## Main definitions

* `list.duplicate x l : Prop` is an inductive property that holds when `x` is a duplicate in `l`

## Implementation details

In this file, `x ∈+ l` notation is shorthand for `list.duplicate x l`.

-/

variable {α : Type*}

namespace list

/-- Property that an element `x : α` of `l : list α` can be found in the list more than once. -/
inductive duplicate (x : α) : list α → Prop
| cons_mem {l : list α} : x ∈ l → duplicate (x :: l)
| cons_duplicate {y : α} {l : list α} : duplicate l → duplicate (y :: l)

local infix ` ∈+ `:50 := list.duplicate

variables {l : list α} {x : α}

lemma mem.duplicate_cons_self (h : x ∈ l) : x ∈+ x :: l := duplicate.cons_mem h

lemma duplicate.duplicate_cons (h : x ∈+ l) (y : α) : x ∈+ y :: l := duplicate.cons_duplicate h

lemma duplicate.mem (h : x ∈+ l) : x ∈ l :=
begin
  induction h with l' h y l' h hm,
  { exact mem_cons_self _ _ },
  { exact mem_cons_of_mem _ hm }
end

lemma duplicate.mem_cons_self (h : x ∈+ x :: l) : x ∈ l :=
begin
  cases h with _ h _ _ h,
  { exact h },
  { exact h.mem }
end

@[simp] lemma duplicate_cons_self_iff : x ∈+ x :: l ↔ x ∈ l :=
⟨duplicate.mem_cons_self, mem.duplicate_cons_self⟩

lemma duplicate.ne_nil (h : x ∈+ l) : l ≠ [] :=
λ H, (mem_nil_iff x).mp (H ▸ h.mem)

@[simp] lemma not_duplicate_nil (x : α) : ¬ x ∈+ [] :=
λ H, H.ne_nil rfl

lemma duplicate.ne_singleton (h : x ∈+ l) (y : α) : l ≠ [y] :=
begin
  induction h with l' h z l' h hm,
  { simp [ne_nil_of_mem h] },
  { simp [ne_nil_of_mem h.mem] }
end

@[simp] lemma not_duplicate_singleton (x y : α) : ¬ x ∈+ [y] :=
λ H, H.ne_singleton _ rfl

lemma duplicate.elim_nil (h : x ∈+ []) : false :=
not_duplicate_nil x h

lemma duplicate.elim_singleton {y : α} (h : x ∈+ [y]) : false :=
not_duplicate_singleton x y h

lemma duplicate_cons_iff {y : α} : x ∈+ y :: l ↔ (y = x ∧ x ∈ l) ∨ x ∈+ l :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { cases h with _ hm _ _ hm,
    { exact or.inl ⟨rfl, hm⟩ },
    { exact or.inr hm } },
  { rcases h with ⟨rfl|h⟩|h,
    { simpa },
    { exact h.cons_duplicate } }
end

lemma duplicate.of_duplicate_cons {y : α} (h : x ∈+ y :: l) (hx : x ≠ y) : x ∈+ l :=
by simpa [duplicate_cons_iff, hx.symm] using h

lemma duplicate_cons_iff_of_ne {y : α} (hne : x ≠ y) : x ∈+ y :: l ↔ x ∈+ l :=
by simp [duplicate_cons_iff, hne.symm]

lemma duplicate.mono_sublist {l' : list α} (hx : x ∈+ l) (h : l <+ l') : x ∈+ l' :=
begin
  induction h with l₁ l₂ y h IH l₁ l₂ y h IH,
  { exact hx },
  { exact (IH hx).duplicate_cons _ },
  { rw duplicate_cons_iff at hx ⊢,
    rcases hx with ⟨rfl, hx⟩|hx,
    { simp [h.subset hx] },
    { simp [IH hx] } }
end

/-- The contrapositive of `list.nodup_iff_sublist`. -/
lemma duplicate_iff_sublist : x ∈+ l ↔ [x, x] <+ l :=
begin
  induction l with y l IH,
  { simp },
  { by_cases hx : x = y,
    { simp [hx, cons_sublist_cons_iff, singleton_sublist] },
    { rw [duplicate_cons_iff_of_ne hx, IH],
      refine ⟨sublist_cons_of_sublist y, λ h, _⟩,
      cases h,
      { assumption },
      { contradiction } } }
end

lemma nodup_iff_forall_not_duplicate : nodup l ↔ ∀ (x : α), ¬ x ∈+ l :=
by simp_rw [nodup_iff_sublist, duplicate_iff_sublist]

lemma exists_duplicate_iff_not_nodup : (∃ (x : α), x ∈+ l) ↔ ¬ nodup l :=
by simp [nodup_iff_forall_not_duplicate]

lemma duplicate.not_nodup (h : x ∈+ l) : ¬ nodup l :=
λ H, nodup_iff_forall_not_duplicate.mp H _ h

lemma duplicate_iff_two_le_count [decidable_eq α] : (x ∈+ l) ↔ 2 ≤ count x l :=
by simp [duplicate_iff_sublist, le_count_iff_repeat_sublist]

instance decidable_duplicate [decidable_eq α] (x : α) : ∀ (l : list α), decidable (x ∈+ l)
| []       := is_false (not_duplicate_nil x)
| (y :: l) := match decidable_duplicate l with
  | is_true  h := is_true (h.duplicate_cons y)
  | is_false h := if hx : y = x ∧ x ∈ l
      then is_true (hx.left.symm ▸ hx.right.duplicate_cons_self)
      else is_false (by simpa [duplicate_cons_iff, h] using hx)
  end

end list
