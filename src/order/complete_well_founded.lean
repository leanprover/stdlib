/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import order.order_iso_nat
import data.set.finite
import tactic.tfae

/-!
# Well-foundedness for complete lattices

For complete lattices, there are numerous equivalent ways to express the fact that the relation `>`
is well-founded. In this file we define two especially-useful characterisations and provide
proofs that they are indeed equivalent to well-foundedness.

## Main definitions
 * `is_sup_closed_compact`
 * `is_Sup_finite_compact`

## Main results
The main result is that the following three conditions are equivalent for a complete lattice:
 * `well_founded (>)`
 * `is_sup_closed_compact`
 * `is_Sup_finite_compact`

This is demonstrated by means of the following three lemmas:
 * `well_founded.is_Sup_finite_compact`
 * `is_Sup_finite_compact.is_sup_closed_compact`
 * `is_sup_closed_compact.well_founded`

## Tags

complete lattice, well-founded, compact
-/

namespace complete_lattice

variables (α : Type*) [complete_lattice α]

/-- A compactness property for a complete lattice is that any `sup`-closed non-empty subset
contains its `Sup`. -/
def is_sup_closed_compact : Prop :=
  ∀ (s : set α) (h : s.nonempty), (∀ a b, a ∈ s → b ∈ s → a ⊔ b ∈ s) → (Sup s) ∈ s

/-- A compactness property for a complete lattice is that any subset has a finite subset with the
same `Sup`. -/
def is_Sup_finite_compact : Prop :=
∀ (s : set α), ∃ (t : finset α), ↑t ⊆ s ∧ Sup s = t.sup id

lemma well_founded.is_Sup_finite_compact (h : well_founded ((>) : α → α → Prop)) :
  is_Sup_finite_compact α :=
begin
  intros s,
  let p : set α := { x | ∃ (t : finset α), ↑t ⊆ s ∧ t.sup id = x },
  have hp : p.nonempty, { use [⊥, ∅], simp, },
  obtain ⟨m, ⟨t, ⟨ht₁, ht₂⟩⟩, hm⟩ := well_founded.well_founded_iff_has_max'.mp h p hp,
  use t, simp only [ht₁, ht₂, true_and], apply le_antisymm,
  { apply Sup_le, intros y hy, classical,
    have hy' : (insert y t).sup id ∈ p,
    { use insert y t, simp, rw set.insert_subset, exact ⟨hy, ht₁⟩, },
    have hm' : m ≤ (insert y t).sup id, { rw ← ht₂, exact finset.sup_mono (t.subset_insert y), },
    rw ← hm _ hy' hm', simp, },
  { rw [← ht₂, finset.sup_eq_Sup], exact Sup_le_Sup ht₁, },
end

lemma is_Sup_finite_compact.is_sup_closed_compact (h : is_Sup_finite_compact α) :
  is_sup_closed_compact α :=
begin
  intros s hne hsc, obtain ⟨t, ht₁, ht₂⟩ := h s, clear h,
  cases t.eq_empty_or_nonempty with h h,
  { subst h, rw finset.sup_empty at ht₂, rw ht₂,
    simp [eq_singleton_bot_of_Sup_eq_bot_of_nonempty ht₂ hne], },
  { rw ht₂, exact t.sup_closed_of_sup_closed h ht₁ hsc, },
end

lemma is_sup_closed_compact.well_founded (h : is_sup_closed_compact α) :
  well_founded ((>) : α → α → Prop) :=
begin
  rw rel_embedding.well_founded_iff_no_descending_seq, rintros ⟨a⟩,
  suffices : Sup (set.range a) ∈ set.range a,
  { obtain ⟨n, hn⟩ := set.mem_range.mp this,
    have h' : Sup (set.range a) < a (n+1), { change _ > _, simp [← hn, a.map_rel_iff], },
    apply lt_irrefl (a (n+1)), apply lt_of_le_of_lt _ h', apply le_Sup, apply set.mem_range_self, },
  apply h (set.range a),
  { use a 37, apply set.mem_range_self, },
  { rintros x y ⟨m, hm⟩ ⟨n, hn⟩, use m ⊔ n, rw [← hm, ← hn], apply a.to_rel_hom.map_sup, },
end

lemma well_founded_characterisations :
  tfae [well_founded ((>) : α → α → Prop), is_Sup_finite_compact α, is_sup_closed_compact α] :=
begin
  tfae_have : 1 → 2, by { exact well_founded.is_Sup_finite_compact α, },
  tfae_have : 2 → 3, by { exact is_Sup_finite_compact.is_sup_closed_compact α, },
  tfae_have : 3 → 1, by { exact is_sup_closed_compact.well_founded α, },
  tfae_finish,
end

lemma well_founded_iff_is_Sup_finite_compact :
  well_founded ((>) : α → α → Prop) ↔ is_Sup_finite_compact α :=
(well_founded_characterisations α).out 0 1

lemma is_Sup_finite_compact_iff_is_sup_closed_compact :
  is_Sup_finite_compact α ↔ is_sup_closed_compact α :=
(well_founded_characterisations α).out 1 2

lemma is_sup_closed_compact_iff_well_founded :
  is_sup_closed_compact α ↔ well_founded ((>) : α → α → Prop) :=
(well_founded_characterisations α).out 2 0

alias well_founded_iff_is_Sup_finite_compact ↔ _ is_Sup_finite_compact.well_founded
alias is_Sup_finite_compact_iff_is_sup_closed_compact ↔
      _ is_sup_closed_compact.is_Sup_finite_compact
alias is_sup_closed_compact_iff_well_founded ↔ _ well_founded.is_sup_closed_compact

end complete_lattice
