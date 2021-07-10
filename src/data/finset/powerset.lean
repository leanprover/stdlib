/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.finset.lattice

/-!
# The powerset of a finset
-/

namespace finset
open multiset

variables {α : Type*}

/-! ### powerset -/
section powerset

/-- When `s` is a finset, `s.powerset` is the finset of all subsets of `s` (seen as finsets). -/
def powerset (s : finset α) : finset (finset α) :=
⟨s.1.powerset.pmap finset.mk
  (λ t h, nodup_of_le (mem_powerset.1 h) s.2),
 nodup_pmap (λ a ha b hb, congr_arg finset.val)
   (nodup_powerset.2 s.2)⟩

@[simp] theorem mem_powerset {s t : finset α} : s ∈ powerset t ↔ s ⊆ t :=
by cases s; simp only [powerset, mem_mk, mem_pmap, mem_powerset, exists_prop, exists_eq_right];
  rw ← val_le_iff

@[simp] theorem empty_mem_powerset (s : finset α) : ∅ ∈ powerset s :=
mem_powerset.2 (empty_subset _)

@[simp] theorem mem_powerset_self (s : finset α) : s ∈ powerset s :=
mem_powerset.2 (subset.refl _)

@[simp] lemma powerset_empty : finset.powerset (∅ : finset α) = {∅} := rfl

@[simp] theorem powerset_mono {s t : finset α} : powerset s ⊆ powerset t ↔ s ⊆ t :=
⟨λ h, (mem_powerset.1 $ h $ mem_powerset_self _),
 λ st u h, mem_powerset.2 $ subset.trans (mem_powerset.1 h) st⟩

/-- **Number of Subsets of a Set** -/
@[simp] theorem card_powerset (s : finset α) :
  card (powerset s) = 2 ^ card s :=
(card_pmap _ _ _).trans (card_powerset s.1)

lemma not_mem_of_mem_powerset_of_not_mem {s t : finset α} {a : α}
  (ht : t ∈ s.powerset) (h : a ∉ s) : a ∉ t :=
by { apply mt _ h, apply mem_powerset.1 ht }

lemma powerset_insert [decidable_eq α] (s : finset α) (a : α) :
  powerset (insert a s) = s.powerset ∪ s.powerset.image (insert a) :=
begin
  ext t,
  simp only [exists_prop, mem_powerset, mem_image, mem_union, subset_insert_iff],
  by_cases h : a ∈ t,
  { split,
    { exact λH, or.inr ⟨_, H, insert_erase h⟩ },
    { intros H,
      cases H,
      { exact subset.trans (erase_subset a t) H },
      { rcases H with ⟨u, hu⟩,
        rw ← hu.2,
        exact subset.trans (erase_insert_subset a u) hu.1 } } },
  { have : ¬ ∃ (u : finset α), u ⊆ s ∧ insert a u = t,
      by simp [ne.symm (ne_insert_of_not_mem _ _ h)],
    simp [finset.erase_eq_of_not_mem h, this] }
end

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for any subset. -/
instance decidable_exists_of_decidable_subsets {s : finset α} {p : Π t ⊆ s, Prop}
  [Π t (h : t ⊆ s), decidable (p t h)] : decidable (∃ t (h : t ⊆ s), p t h) :=
decidable_of_iff (∃ t (hs : t ∈ s.powerset), p t (mem_powerset.1 hs))
⟨(λ ⟨t, _, hp⟩, ⟨t, _, hp⟩), (λ ⟨t, hs, hp⟩, ⟨t, mem_powerset.2 hs, hp⟩)⟩

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for every subset. -/
instance decidable_forall_of_decidable_subsets {s : finset α} {p : Π t ⊆ s, Prop}
  [Π t (h : t ⊆ s), decidable (p t h)] : decidable (∀ t (h : t ⊆ s), p t h) :=
decidable_of_iff (∀ t (h : t ∈ s.powerset), p t (mem_powerset.1 h))
⟨(λ h t hs, h t (mem_powerset.2 hs)), (λ h _ _, h _ _)⟩

/-- A version of `finset.decidable_exists_of_decidable_subsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidable_exists_of_decidable_subsets' {s : finset α} {p : finset α → Prop}
  (hu : Π t (h : t ⊆ s), decidable (p t)) : decidable (∃ t (h : t ⊆ s), p t) :=
@finset.decidable_exists_of_decidable_subsets _ _ _ hu

/-- A version of `finset.decidable_forall_of_decidable_subsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidable_forall_of_decidable_subsets' {s : finset α} {p : finset α → Prop}
  (hu : Π t (h : t ⊆ s), decidable (p t)) : decidable (∀ t (h : t ⊆ s), p t) :=
@finset.decidable_forall_of_decidable_subsets _ _ _ hu

end powerset

section ssubsets
variables [decidable_eq α]

/-- For `s` a finset, `s.ssubsets` is the finset comprising strict subsets of `s`. -/
def ssubsets (s : finset α) : finset (finset α) :=
erase (powerset s) s

@[simp] lemma mem_ssubsets {s t : finset α} : t ∈ s.ssubsets ↔ t ⊂ s :=
by rw [ssubsets, mem_erase, mem_powerset, ssubset_iff_subset_ne, and.comm]

lemma empty_mem_ssubsets {s : finset α} (h : s.nonempty) : ∅ ∈ s.ssubsets :=
by { rw [mem_ssubsets, ssubset_iff_subset_ne], exact ⟨empty_subset s, h.ne_empty.symm⟩, }

/-- For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for any ssubset. -/
instance decidable_exists_of_decidable_ssubsets {s : finset α} {p : Π t ⊂ s, Prop}
  [Π t (h : t ⊂ s), decidable (p t h)] : decidable (∃ t h, p t h) :=
decidable_of_iff (∃ t (hs : t ∈ s.ssubsets), p t (mem_ssubsets.1 hs))
⟨(λ ⟨t, _, hp⟩, ⟨t, _, hp⟩), (λ ⟨t, hs, hp⟩, ⟨t, mem_ssubsets.2 hs, hp⟩)⟩

/-- For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for every ssubset. -/
instance decidable_forall_of_decidable_ssubsets {s : finset α} {p : Π t ⊂ s, Prop}
  [Π t (h : t ⊂ s), decidable (p t h)] : decidable (∀ t h, p t h) :=
decidable_of_iff (∀ t (h : t ∈ s.ssubsets), p t (mem_ssubsets.1 h))
⟨(λ h t hs, h t (mem_ssubsets.2 hs)), (λ h _ _, h _ _)⟩

/-- A version of `finset.decidable_exists_of_decidable_ssubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidable_exists_of_decidable_ssubsets' {s : finset α} {p : finset α → Prop}
  (hu : Π t (h : t ⊂ s), decidable (p t)) : decidable (∃ t (h : t ⊂ s), p t) :=
@finset.decidable_exists_of_decidable_ssubsets _ _ _ _ hu

/-- A version of `finset.decidable_forall_of_decidable_ssubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidable_forall_of_decidable_ssubsets' {s : finset α} {p : finset α → Prop}
  (hu : Π t (h : t ⊂ s), decidable (p t)) : decidable (∀ t (h : t ⊂ s), p t) :=
@finset.decidable_forall_of_decidable_ssubsets _ _ _ _ hu

end ssubsets

section powerset_len

/-- Given an integer `n` and a finset `s`, then `powerset_len n s` is the finset of subsets of `s`
of cardinality `n`. -/
def powerset_len (n : ℕ) (s : finset α) : finset (finset α) :=
⟨(s.1.powerset_len n).pmap finset.mk
  (λ t h, nodup_of_le (mem_powerset_len.1 h).1 s.2),
 nodup_pmap (λ a ha b hb, congr_arg finset.val)
   (nodup_powerset_len s.2)⟩

/-- **Formula for the Number of Combinations** -/
theorem mem_powerset_len {n} {s t : finset α} :
  s ∈ powerset_len n t ↔ s ⊆ t ∧ card s = n :=
by cases s; simp [powerset_len, val_le_iff.symm]; refl

@[simp] theorem powerset_len_mono {n} {s t : finset α} (h : s ⊆ t) :
  powerset_len n s ⊆ powerset_len n t :=
λ u h', mem_powerset_len.2 $
  and.imp (λ h₂, subset.trans h₂ h) id (mem_powerset_len.1 h')

/-- **Formula for the Number of Combinations** -/
@[simp] theorem card_powerset_len (n : ℕ) (s : finset α) :
  card (powerset_len n s) = nat.choose (card s) n :=
(card_pmap _ _ _).trans (card_powerset_len n s.1)

@[simp] lemma powerset_len_zero (s : finset α) : finset.powerset_len 0 s = {∅} :=
begin
  ext, rw [mem_powerset_len, mem_singleton, card_eq_zero],
  refine ⟨λ h, h.2, λ h, by { rw h, exact ⟨empty_subset s, rfl⟩ }⟩,
end

@[simp] theorem powerset_len_empty (n : ℕ) {s : finset α} (h : s.card < n) :
  powerset_len n s = ∅ :=
finset.card_eq_zero.mp (by rw [card_powerset_len, nat.choose_eq_zero_of_lt h])

theorem powerset_len_eq_filter {n} {s : finset α} :
  powerset_len n s = (powerset s).filter (λ x, x.card = n) :=
by { ext, simp [mem_powerset_len] }

lemma powerset_len_succ_insert [decidable_eq α] {x : α} {s : finset α} (h : x ∉ s) (n : ℕ) :
  powerset_len n.succ (insert x s) = powerset_len n.succ s ∪ (powerset_len n s).image (insert x) :=
begin
  rw [powerset_len_eq_filter, powerset_insert, filter_union, ←powerset_len_eq_filter],
  congr,
  rw [powerset_len_eq_filter, image_filter],
  congr' 1,
  ext t,
  simp only [mem_powerset, mem_filter, function.comp_app, and.congr_right_iff],
  intro ht,
  have : x ∉ t := λ H, h (ht H),
  simp [card_insert_of_not_mem this, nat.succ_inj']
end

lemma powerset_len_nonempty {n : ℕ} {s : finset α} (h : n < s.card) :
  (powerset_len n s).nonempty :=
begin
  classical,
  induction s using finset.induction_on with x s hx IH generalizing n,
  { simpa using h },
  { cases n,
    { simp },
    { rw [card_insert_of_not_mem hx, nat.succ_lt_succ_iff] at h,
      rw powerset_len_succ_insert hx,
      refine nonempty.mono _ ((IH h).image (insert x)),
      convert (subset_union_right _ _) } }
end

@[simp] lemma powerset_len_self (s : finset α) :
  powerset_len s.card s = {s} :=
begin
  ext,
  rw [mem_powerset_len, mem_singleton],
  split,
  { exact λ ⟨hs, hc⟩, eq_of_subset_of_card_le hs hc.ge },
  { rintro rfl,
    simp }
end

lemma powerset_card_bUnion [decidable_eq (finset α)] (s : finset α) :
  finset.powerset s = (range (s.card + 1)).bUnion (λ i, powerset_len i s) :=
begin
  refine ext (λ a, ⟨λ ha, _, λ ha, _ ⟩),
  { rw mem_bUnion,
    exact ⟨a.card, mem_range.mpr (nat.lt_succ_of_le (card_le_of_subset (mem_powerset.mp ha))),
      mem_powerset_len.mpr ⟨mem_powerset.mp ha, rfl⟩⟩ },
  { rcases mem_bUnion.mp ha with ⟨i, hi, ha⟩,
    exact mem_powerset.mpr (mem_powerset_len.mp ha).1, }
end

lemma powerset_len_sup [decidable_eq α] (u : finset α) (n : ℕ) (hn : n < u.card) :
  (powerset_len n.succ u).sup id = u :=
begin
  apply le_antisymm,
  { simp_rw [sup_le_iff, mem_powerset_len],
    rintros x ⟨h, -⟩,
    exact h },
  { rw [sup_eq_bUnion, le_iff_subset, subset_iff],
    cases (nat.succ_le_of_lt hn).eq_or_lt with h' h',
    { simp [h'] },
    { intros x hx,
      simp only [mem_bUnion, exists_prop, id.def],
      obtain ⟨t, ht⟩ : ∃ t, t ∈ powerset_len n (u.erase x) := powerset_len_nonempty _,
      { refine ⟨insert x t, _, mem_insert_self _ _⟩,
        rw [←insert_erase hx, powerset_len_succ_insert (not_mem_erase _ _)],
        exact mem_union_right _ (mem_image_of_mem _ ht) },
      { rwa [card_erase_of_mem hx, nat.lt_pred_iff] } } }
end

end powerset_len
end finset
