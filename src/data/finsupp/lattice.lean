/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.finsupp
import tactic.squeeze
import algebra.ordered_group
--open finsupp

/-!
# Lattice structure on finsupps

This file provides instances of ordered structures on finsupps.

-/

open_locale classical
noncomputable theory
variables {α : Type*} {β : Type*} [has_zero β] {μ : Type*} [canonically_ordered_add_monoid μ]
variables {γ : Type*} [canonically_linear_ordered_add_monoid γ]

namespace finsupp

lemma le_def [has_zero β] [partial_order β] {a b : α →₀ β} : a ≤ b ↔ ∀ (s : α), a s ≤ b s := by refl

variable [has_zero β]

instance order_bot_of_zero_bot [order_bot β] (h : ⊥ = (0 : β)): order_bot (α →₀ β) :=
{ bot := 0, bot_le := by simp [finsupp.le_def, ← h], .. finsupp.partial_order}

instance : order_bot (α →₀ μ) := finsupp.order_bot_of_zero_bot bot_eq_zero


def binary_rel_pointwise (r : β → β → Prop) (a b : α →₀ β) : Prop := ∀ s : α, r (a s) (b s)

lemma binary_rel_pointwise_ext (r : β → β → Prop) (a b : α →₀ β) :
  (binary_rel_pointwise r a b) ↔ ∀ s, r (a s) (b s) := by refl

def binary_op_pointwise {f : β → β → β} (h : f 0 0 = 0) (a b : α →₀ β) : α →₀ β :=
{ support := ((a.support) ∪ (b.support)).filter (λ s, f (a s) (b s) ≠ 0),
  to_fun := λ s, f (a s) (b s),
  mem_support_to_fun := by {
    simp only [mem_support_iff, ne.def, finset.mem_union, finset.mem_filter],
    intro s, apply and_iff_right_of_imp, rw ← not_and_distrib, rw not_imp_not,
    intro h1, rw h1.left, rw h1.right, apply h, }, }

lemma binary_op_pointwise_apply {f : β → β → β} (h : f 0 0 = 0) (a b : α →₀ β) (s : α) :
  (binary_op_pointwise h a b) s = f (a s) (b s) := rfl

instance [semilattice_inf β] : semilattice_inf (α →₀ β) :=
{ inf := binary_op_pointwise inf_idem,
  inf_le_left := by { intros, rw le_def, intro, apply inf_le_left, },
  inf_le_right := by { intros, rw le_def, intro, apply inf_le_right, },
  le_inf := by { intros, rw le_def at *, intro, apply le_inf (a_1 s) (a_2 s) },
  ..finsupp.partial_order,
}

@[simp]
lemma inf_apply [semilattice_inf β] {a : α} {f g : α →₀ β} : (f ⊓ g) a = f a ⊓ g a := rfl

-- Could deduce these from more instances, but those instances would have different ≤s
lemma support_inf_of_non_disjoint [semilattice_inf β]
  (bz : ∀ x : β, 0 ≤ x) (nd : ∀ x y : β, x ⊓ y = 0 → x = 0 ∨ y = 0)
  {f g : α →₀ β} : (f ⊓ g).support = f.support ∩ g.support :=
begin
  change (binary_op_pointwise inf_idem f g).support = f.support ∩ g.support,
  unfold binary_op_pointwise, dsimp, ext,
  simp only [mem_support_iff,  ne.def,
    finset.mem_union, finset.mem_filter, finset.mem_inter],
  split; intro h, cases h with i j, split; intro con; rw con at j; apply j; simp [bz],
  { split, left, exact h.left,
    intro con, cases nd (f a) (g a) _, apply h.left h_1, apply h.right h_1, rw con }
end

lemma support_inf {f g : α →₀ γ} : (f ⊓ g).support = f.support ∩ g.support :=
begin
  unfold has_inf.inf, apply support_inf_of_non_disjoint zero_le _,
  intros x y, change ite (x ≤ y) x y = 0 → x = 0 ∨ y = 0,
  by_cases x ≤ y; simp only [h, if_true, if_false]; tauto,
end

instance [semilattice_sup β] : semilattice_sup (α →₀ β) :=
{ sup := binary_op_pointwise sup_idem,
  le_sup_left := by { intros, rw le_def, intro, apply le_sup_left, },
  le_sup_right := by { intros, rw le_def, intro, apply le_sup_right, },
  sup_le := by { intros, rw le_def at *, intro, apply sup_le (a_1 s) (a_2 s) },
  ..finsupp.partial_order,
}

@[simp]
lemma sup_apply [semilattice_sup β] {a : α} {f g : α →₀ β} : (f ⊔ g) a = f a ⊔ g a := rfl

@[simp]
lemma support_sup
  {f g : α →₀ γ} : (f ⊔ g).support = f.support ∪ g.support :=
begin
  change (binary_op_pointwise sup_idem f g).support = f.support ∪ g.support,
  unfold binary_op_pointwise, dsimp, rw finset.filter_true_of_mem,
  intros x hx, rw ← bot_eq_zero, rw sup_eq_bot_iff,
   revert hx,
  simp only [not_and, mem_support_iff, bot_eq_zero, ne.def, finset.mem_union], tauto,
end

instance lattice [lattice β] : lattice (α →₀ β) :=
{ .. finsupp.semilattice_inf, .. finsupp.semilattice_sup}

instance semilattice_inf_bot : semilattice_inf_bot (α →₀ γ) :=
{ ..finsupp.order_bot, ..finsupp.lattice}

lemma of_multiset_strict_mono : strict_mono (@finsupp.of_multiset α) :=
begin
  unfold strict_mono, intros, rw lt_iff_le_and_ne at *, split,
  { rw finsupp.le_iff, intros s hs, repeat {rw finsupp.of_multiset_apply},
    rw multiset.le_iff_count at a_1, apply a_1.left },
  { have h := a_1.right, contrapose h, simp at *,
    apply finsupp.equiv_multiset.symm.injective h }
end

lemma bot_eq_zero : (⊥ : α →₀ γ) = 0 := rfl

@[simp]
lemma disjoint_iff {x y : α →₀ γ} : disjoint x y ↔ disjoint x.support y.support :=
begin
  unfold disjoint, repeat {rw le_bot_iff},
  rw [finsupp.bot_eq_zero, ← finsupp.support_eq_empty, finsupp.support_inf], refl,
end

/-- The lattice of finsupps to ℕ is order isomorphic to that of multisets.  -/
def order_iso_multiset (α : Type) :
  (has_le.le : (α →₀ ℕ) → (α →₀ ℕ) → Prop) ≃o (has_le.le : (multiset α) → (multiset α) → Prop) :=
⟨finsupp.equiv_multiset, begin
  intros a b, unfold finsupp.equiv_multiset, dsimp,
  rw multiset.le_iff_count, simp only [finsupp.count_to_multiset], refl
end ⟩



end finsupp
