/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import data.set.finite
import data.finset.order
import order.well_founded
import order.order_iso_nat
import order.atoms
import order.zorn
import tactic.tfae

/-!
# Compactness properties for complete lattices

For complete lattices, there are numerous equivalent ways to express the fact that the relation `>`
is well-founded. In this file we define three especially-useful characterisations and provide
proofs that they are indeed equivalent to well-foundedness.

## Main definitions
 * `complete_lattice.is_sup_closed_compact`
 * `complete_lattice.is_Sup_finite_compact`
 * `complete_lattice.is_compact_element`
 * `complete_lattice.is_compactly_generated`

## Main results
The main result is that the following four conditions are equivalent for a complete lattice:
 * `well_founded (>)`
 * `complete_lattice.is_sup_closed_compact`
 * `complete_lattice.is_Sup_finite_compact`
 * `∀ k, complete_lattice.is_compact_element k`

This is demonstrated by means of the following four lemmas:
 * `complete_lattice.well_founded.is_Sup_finite_compact`
 * `complete_lattice.is_Sup_finite_compact.is_sup_closed_compact`
 * `complete_lattice.is_sup_closed_compact.well_founded`
 * `complete_lattice.is_Sup_finite_compact_iff_all_elements_compact`

 We also show well-founded lattices are compactly generated
 (`complete_lattice.compactly_generated_of_well_founded`).

## References
- [G. Călugăreanu, *Lattice Concepts of Module Theory*][calugareanu]

## Tags

complete lattice, well-founded, compact
-/

variables {α : Type*} [complete_lattice α]

namespace complete_lattice

variables (α)

/-- A compactness property for a complete lattice is that any `sup`-closed non-empty subset
contains its `Sup`. -/
def is_sup_closed_compact : Prop :=
  ∀ (s : set α) (h : s.nonempty), (∀ a b, a ∈ s → b ∈ s → a ⊔ b ∈ s) → (Sup s) ∈ s

/-- A compactness property for a complete lattice is that any subset has a finite subset with the
same `Sup`. -/
def is_Sup_finite_compact : Prop :=
∀ (s : set α), ∃ (t : finset α), ↑t ⊆ s ∧ Sup s = t.sup id

/-- An element `k` of a complete lattice is said to be compact if any set with `Sup`
above `k` has a finite subset with `Sup` above `k`.  Such an element is also called
"finite" or "S-compact". -/
def is_compact_element {α : Type*} [complete_lattice α] (k : α) :=
∀ s : set α, k ≤ Sup s → ∃ t : finset α, ↑t ⊆ s ∧ k ≤ t.sup id

/-- An element `k` is compact if and only if any directed set with `Sup` above
`k` already got above `k` at some point in the set. -/
theorem is_compact_element_iff_le_of_directed_Sup_le (k : α) :
  is_compact_element k ↔
  ∀ s : set α, s.nonempty → directed_on (≤) s → k ≤ Sup s → ∃ x : α, x ∈ s ∧ k ≤ x :=
begin
  classical,
  split,
  { by_cases hbot : k = ⊥,
    -- Any nonempty directed set certainly has sup above ⊥
    { rintros _ _ ⟨x, hx⟩ _ _, use x, by simp only [hx, hbot, bot_le, and_self], },
    { intros hk s hne hdir hsup,
      obtain ⟨t, ht⟩ := hk s hsup,
      -- If t were empty, its sup would be ⊥, which is not above k ≠ ⊥.
      have tne : t.nonempty,
      { by_contradiction n,
        rw [finset.nonempty_iff_ne_empty, not_not] at n,
        simp only [n, true_and, set.empty_subset, finset.coe_empty,
          finset.sup_empty, le_bot_iff] at ht,
        exact absurd ht hbot, },
      -- certainly every element of t is below something in s, since ↑t ⊆ s.
      have t_below_s : ∀ x ∈ t, ∃ y ∈ s, x ≤ y, from λ x hxt, ⟨x, ht.left hxt, by refl⟩,
      obtain ⟨x, ⟨hxs, hsupx⟩⟩ := finset.sup_le_of_le_directed s hne hdir t t_below_s,
      exact ⟨x, ⟨hxs, le_trans ht.right hsupx⟩⟩, }, },
  { intros hk s hsup,
    -- Consider the set of finite joins of elements of the (plain) set s.
    let S : set α := { x | ∃ t : finset α, ↑t ⊆ s ∧ x = t.sup id },
    -- S is directed, nonempty, and still has sup above k.
    have dir_US : directed_on (≤) S,
    { rintros x ⟨c, hc⟩ y ⟨d, hd⟩,
      use x ⊔ y,
      split,
      { use c ∪ d,
        split,
        { simp only [hc.left, hd.left, set.union_subset_iff, finset.coe_union, and_self], },
        { simp only [hc.right, hd.right, finset.sup_union], }, },
      simp only [and_self, le_sup_left, le_sup_right], },
    have sup_S : Sup s ≤ Sup S,
    { apply Sup_le_Sup,
      intros x hx, use {x},
      simpa only [and_true, id.def, finset.coe_singleton, eq_self_iff_true, finset.sup_singleton,
        set.singleton_subset_iff], },
    have Sne : S.nonempty,
    { suffices : ⊥ ∈ S, from set.nonempty_of_mem this,
      use ∅,
      simp only [set.empty_subset, finset.coe_empty, finset.sup_empty,
        eq_self_iff_true, and_self], },
    -- Now apply the defn of compact and finish.
    obtain ⟨j, ⟨hjS, hjk⟩⟩ := hk S Sne dir_US (le_trans hsup sup_S),
    obtain ⟨t, ⟨htS, htsup⟩⟩ := hjS,
    use t, exact ⟨htS, by rwa ←htsup⟩, },
end

/-- A compact element `k` has the property that any directed set lying strictly below `k` has
its Sup strictly below `k`. -/
lemma is_compact_element.directed_Sup_lt_of_lt {α : Type*} [complete_lattice α] {k : α}
  (hk : is_compact_element k) {s : set α} (hemp : s.nonempty) (hdir : directed_on (≤) s)
  (hbelow : ∀ x ∈ s, x < k) : Sup s < k :=
begin
  rw is_compact_element_iff_le_of_directed_Sup_le at hk,
  by_contradiction,
  have sSup : Sup s ≤ k, from Sup_le (λ s hs, (hbelow s hs).le),
  replace sSup : Sup s = k := eq_iff_le_not_lt.mpr ⟨sSup, h⟩,
  obtain ⟨x, hxs, hkx⟩ := hk s hemp hdir sSup.symm.le,
  obtain hxk := hbelow x hxs,
  exact hxk.ne (hxk.le.antisymm hkx),
end

lemma finset_sup_compact_of_compact {α β : Type*} [complete_lattice α] {f : β → α}
  (s : finset β) (h : ∀ x ∈ s, is_compact_element (f x)) : is_compact_element (s.sup f) :=
begin
  classical,
  rw is_compact_element_iff_le_of_directed_Sup_le,
  intros d hemp hdir hsup,
  change f with id ∘ f, rw ←finset.sup_finset_image,
  apply finset.sup_le_of_le_directed d hemp hdir,
  rintros x hx,
  obtain ⟨p, ⟨hps, rfl⟩⟩ := finset.mem_image.mp hx,
  specialize h p hps,
  rw is_compact_element_iff_le_of_directed_Sup_le at h,
  specialize h d hemp hdir (le_trans (finset.le_sup hps) hsup),
  simpa only [exists_prop],
end

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
  { rw [← ht₂, finset.sup_id_eq_Sup], exact Sup_le_Sup ht₁, },
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

lemma is_Sup_finite_compact_iff_all_elements_compact :
  is_Sup_finite_compact α ↔ (∀ k : α, is_compact_element k) :=
begin
  split,
  { intros h k s hs,
    obtain ⟨t, ⟨hts, htsup⟩⟩ := h s,
    use [t, hts],
    rwa ←htsup, },
  { intros h s,
    obtain ⟨t, ⟨hts, htsup⟩⟩ := h (Sup s) s (by refl),
    have : Sup s = t.sup id,
    { suffices : t.sup id ≤ Sup s, by { apply le_antisymm; assumption },
      simp only [id.def, finset.sup_le_iff],
      intros x hx,
      apply le_Sup, exact hts hx, },
    use [t, hts], assumption, },
end

lemma well_founded_characterisations :
  tfae [well_founded ((>) : α → α → Prop),
        is_Sup_finite_compact α,
        is_sup_closed_compact α,
        ∀ k : α, is_compact_element k] :=
begin
  tfae_have : 1 → 2, by { exact well_founded.is_Sup_finite_compact α, },
  tfae_have : 2 → 3, by { exact is_Sup_finite_compact.is_sup_closed_compact α, },
  tfae_have : 3 → 1, by { exact is_sup_closed_compact.well_founded α, },
  tfae_have : 2 ↔ 4, by { exact is_Sup_finite_compact_iff_all_elements_compact α },
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

/-- A complete lattice is said to be compactly generated if any
element is the `Sup` of compact elements. -/
class is_compactly_generated (α : Type*) [complete_lattice α] : Prop :=
(exists_Sup_eq :
  ∀ (x : α), ∃ (s : set α), (∀ x ∈ s, complete_lattice.is_compact_element x) ∧ Sup s = x)

section
variables {α} [is_compactly_generated α] {a b : α} {s : set α}

@[simp]
lemma Sup_compact_le_eq (b) : Sup {c : α | complete_lattice.is_compact_element c ∧ c ≤ b} = b :=
begin
  rcases is_compactly_generated.exists_Sup_eq b with ⟨s, hs, rfl⟩,
  exact le_antisymm (Sup_le (λ c hc, hc.2)) (Sup_le_Sup (λ c cs, ⟨hs c cs, le_Sup cs⟩)),
end

@[simp]
theorem Sup_compact_eq_top :
  Sup {a : α | complete_lattice.is_compact_element a} = ⊤ :=
begin
  refine eq.trans (congr rfl (set.ext (λ x, _))) (Sup_compact_le_eq ⊤),
  exact (and_iff_left le_top).symm,
end

theorem le_iff_compact_le_imp {a b : α} :
  a ≤ b ↔ ∀ c : α, complete_lattice.is_compact_element c → c ≤ a → c ≤ b :=
⟨λ ab c hc ca, le_trans ca ab, λ h, begin
  rw [← Sup_compact_le_eq a, ← Sup_compact_le_eq b],
  exact Sup_le_Sup (λ c hc, ⟨hc.1, h c hc.1 hc.2⟩),
end⟩

/-- This property is sometimes referred to as `α` being upper continuous. -/
theorem inf_Sup_eq_of_directed_on (h : directed_on (≤) s):
  a ⊓ Sup s = ⨆ b ∈ s, a ⊓ b :=
le_antisymm (begin
  rw le_iff_compact_le_imp,
  by_cases hs : s.nonempty,
  { intros c hc hcinf,
    rw le_inf_iff at hcinf,
    rw complete_lattice.is_compact_element_iff_le_of_directed_Sup_le at hc,
    rcases hc s hs h hcinf.2 with ⟨d, ds, cd⟩,
    exact (le_inf hcinf.1 cd).trans (le_bsupr d ds) },
  { rw set.not_nonempty_iff_eq_empty at hs,
    simp [hs] }
end) supr_inf_le_inf_Sup

/-- This property is equivalent to `α` being upper continuous. -/
theorem inf_Sup_eq_supr_inf_sup_finset :
  a ⊓ Sup s = ⨆ (t : finset α) (H : ↑t ⊆ s), a ⊓ (t.sup id) :=
le_antisymm (begin
  rw le_iff_compact_le_imp,
  intros c hc hcinf,
  rw le_inf_iff at hcinf,
  rcases hc s hcinf.2 with ⟨t, ht1, ht2⟩,
  exact (le_inf hcinf.1 ht2).trans (le_bsupr t ht1),
end)
  (supr_le $ λ t, supr_le $ λ h, inf_le_inf_left _ ((finset.sup_id_eq_Sup t).symm ▸ (Sup_le_Sup h)))

theorem complete_lattice.set_independent_iff_finite {s : set α} :
  complete_lattice.set_independent s ↔
    ∀ t : finset α, ↑t ⊆ s → complete_lattice.set_independent (↑t : set α) :=
⟨λ hs t ht, hs.mono ht, λ h a ha, begin
  rw [disjoint_iff, inf_Sup_eq_supr_inf_sup_finset, supr_eq_bot],
  intro t,
  rw [supr_eq_bot, finset.sup_id_eq_Sup],
  intro ht,
  classical,
  have h' := (h (insert a t) _ (t.mem_insert_self a)).eq_bot,
  { rwa [finset.coe_insert, set.insert_diff_self_of_not_mem] at h',
    exact λ con, ((set.mem_diff a).1 (ht con)).2 (set.mem_singleton a) },
  { rw [finset.coe_insert, set.insert_subset],
    exact ⟨ha, set.subset.trans ht (set.diff_subset _ _)⟩ }
end⟩

lemma complete_lattice.set_independent_Union_of_directed {η : Type*}
  {s : η → set α} (hs : directed (⊆) s)
  (h : ∀ i, complete_lattice.set_independent (s i)) :
  complete_lattice.set_independent (⋃ i, s i) :=
begin
  by_cases hη : nonempty η,
  { resetI,
    rw complete_lattice.set_independent_iff_finite,
    intros t ht,
    obtain ⟨I, fi, hI⟩ := set.finite_subset_Union t.finite_to_set ht,
    obtain ⟨i, hi⟩ := hs.finset_le fi.to_finset,
    exact (h i).mono (set.subset.trans hI $ set.bUnion_subset $
      λ j hj, hi j (fi.mem_to_finset.2 hj)) },
  { rintros a ⟨_, ⟨i, _⟩, _⟩,
    exfalso, exact hη ⟨i⟩, },
end

lemma complete_lattice.independent_sUnion_of_directed {s : set (set α)}
  (hs : directed_on (⊆) s)
  (h : ∀ a ∈ s, complete_lattice.set_independent a) :
  complete_lattice.set_independent (⋃₀ s) :=
by rw set.sUnion_eq_Union; exact
  complete_lattice.set_independent_Union_of_directed hs.directed_coe (by simpa using h)


end

namespace complete_lattice

lemma compactly_generated_of_well_founded (h : well_founded ((>) : α → α → Prop)) :
  is_compactly_generated α :=
begin
  rw [well_founded_iff_is_Sup_finite_compact, is_Sup_finite_compact_iff_all_elements_compact] at h,
  -- x is the join of the set of compact elements {x}
  exact ⟨λ x, ⟨{x}, ⟨λ x _, h x, Sup_singleton⟩⟩⟩,
end

/-- A compact element `k` has the property that any `b < `k lies below a "maximal element below
`k`", which is to say `[⊥, k]` is coatomic. -/
theorem Iic_coatomic_of_compact_element {k : α} (h : is_compact_element k) :
  is_coatomic (set.Iic k) :=
⟨λ ⟨b, hbk⟩, begin
  by_cases htriv : b = k,
  { left, ext, simp only [htriv, set.Iic.coe_top, subtype.coe_mk], },
  right,
  rcases zorn.zorn_nonempty_partial_order₀ (set.Iio k) _ b (lt_of_le_of_ne hbk htriv)
    with ⟨a, a₀, ba, h⟩,
  { refine ⟨⟨a, le_of_lt a₀⟩, ⟨ne_of_lt a₀, λ c hck, by_contradiction $ λ c₀, _⟩, ba⟩,
    cases h c.1 (lt_of_le_of_ne c.2 (λ con, c₀ (subtype.ext con))) hck.le,
    exact lt_irrefl _ hck, },
  { intros S SC cC I IS,
    by_cases hS : S.nonempty,
    { exact ⟨Sup S, h.directed_Sup_lt_of_lt hS cC.directed_on SC, λ _, le_Sup⟩, },
    exact ⟨b, lt_of_le_of_ne hbk htriv, by simp only [set.not_nonempty_iff_eq_empty.mp hS,
      set.mem_empty_eq, forall_const, forall_prop_of_false, not_false_iff]⟩, },
end⟩

lemma coatomic_of_top_compact (h : is_compact_element (⊤ : α)) : is_coatomic α :=
(@order_iso.Iic_top α _).is_coatomic_iff.mp (Iic_coatomic_of_compact_element h)

end complete_lattice

section
variables [is_modular_lattice α] [is_compactly_generated α]

@[priority 100]
instance is_atomic_of_is_complemented [is_complemented α] : is_atomic α :=
⟨λ b, begin
  by_cases h : {c : α | complete_lattice.is_compact_element c ∧ c ≤ b} ⊆ {⊥},
  { left,
    rw [← Sup_compact_le_eq b, Sup_eq_bot],
    exact h },
  { rcases set.not_subset.1 h with ⟨c, ⟨hc, hcb⟩, hcbot⟩,
    right,
    have hc' := complete_lattice.Iic_coatomic_of_compact_element hc,
    rw ← is_atomic_iff_is_coatomic at hc',
    haveI := hc',
    obtain con | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le (⟨c, le_refl c⟩ : set.Iic c),
    { exfalso,
      apply hcbot,
      simp only [subtype.ext_iff, set.Iic.coe_bot, subtype.coe_mk] at con,
      exact con },
    rw [← subtype.coe_le_coe, subtype.coe_mk] at hac,
    exact ⟨a, ha.of_is_atom_coe_Iic, hac.trans hcb⟩ },
end⟩

/-- See Lemma 5.1, Călugăreanu -/
@[priority 100]
instance is_atomistic_of_is_complemented [is_complemented α] : is_atomistic α :=
⟨λ b, ⟨{a | is_atom a ∧ a ≤ b}, begin
  symmetry,
  have hle : Sup {a : α | is_atom a ∧ a ≤ b} ≤ b := (Sup_le $ λ _, and.right),
  apply (lt_or_eq_of_le hle).resolve_left (λ con, _),
  obtain ⟨c, hc⟩ := exists_is_compl (⟨Sup {a : α | is_atom a ∧ a ≤ b}, hle⟩ : set.Iic b),
  obtain rfl | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le c,
  { exact ne_of_lt con (subtype.ext_iff.1 (eq_top_of_is_compl_bot hc)) },
  { apply ha.1,
    rw eq_bot_iff,
    apply le_trans (le_inf _ hac) hc.1,
    rw [← subtype.coe_le_coe, subtype.coe_mk],
    exact le_Sup ⟨ha.of_is_atom_coe_Iic, a.2⟩ }
end, λ _, and.left⟩⟩

/-- This encapsulates some of the general information one can get out of an atomistic lattice.
For more specific data, e.g. the existence of a maximal independent set of atoms, see below. -/
lemma exists_set_independent_Sup_atoms_eq_compl
  (h : Sup {a : α | is_atom a} = ⊤) (b : α) :
  ∃ s : set α, complete_lattice.set_independent s ∧ is_compl b (Sup s) ∧ ∀ a ∈ s, is_atom a :=
begin
  obtain ⟨s, ⟨s_ind, b_inf_Sup_s, s_atoms⟩, s_max⟩ := zorn.zorn_subset
    {s : set α | complete_lattice.set_independent s ∧ b ⊓ Sup s = ⊥ ∧ ∀ a ∈ s, is_atom a} _,
  { refine ⟨s, s_ind, ⟨b_inf_Sup_s.le, _⟩, s_atoms⟩,
    rw [← h, Sup_le_iff],
    intros a ha,
    rw ← inf_eq_left,
    refine (eq_bot_or_eq_of_le_atom ha inf_le_left).resolve_left (λ con, ha.1 _),
    rw [eq_bot_iff, ← con],
    refine le_inf (le_refl a) ((le_Sup _).trans le_sup_right),
    rw ← disjoint_iff at *,
    have a_dis_Sup_s : disjoint a (Sup s) := con.mono_right le_sup_right,
    rw ← s_max (s ∪ {a}) ⟨λ x hx, _, ⟨_, λ x hx, _⟩⟩ (set.subset_union_left _ _),
    { exact set.mem_union_right _ (set.mem_singleton _) },
    { rw [set.mem_union, set.mem_singleton_iff] at hx,
      by_cases xa : x = a,
      { simp only [xa, set.mem_singleton, set.insert_diff_of_mem, set.union_singleton],
        exact con.mono_right (le_trans (Sup_le_Sup (set.diff_subset s {a})) le_sup_right) },
      { have h : (s ∪ {a}) \ {x} = (s \ {x}) ∪ {a},
        { simp only [set.union_singleton],
          rw set.insert_diff_of_not_mem,
          rw set.mem_singleton_iff,
          exact ne.symm xa },
        rw [h, Sup_union, Sup_singleton],
        apply (s_ind (hx.resolve_right xa)).disjoint_sup_right_of_disjoint_sup_left
          (a_dis_Sup_s.mono_right _).symm,
        rw [← Sup_insert, set.insert_diff_singleton,
          set.insert_eq_of_mem (hx.resolve_right xa)] } },
    { rw [Sup_union, Sup_singleton, ← disjoint_iff],
      exact b_inf_Sup_s.disjoint_sup_right_of_disjoint_sup_left con.symm },
    { rw [set.mem_union, set.mem_singleton_iff] at hx,
      cases hx,
      { exact s_atoms x hx },
      { rw hx,
        exact ha } } },
  { intros c hc1 hc2,
    refine ⟨⋃₀ c, ⟨complete_lattice.independent_sUnion_of_directed hc2.directed_on
      (λ s hs, (hc1 hs).1), _, λ a ha, _⟩, λ _, set.subset_sUnion_of_mem⟩,
    { rw [Sup_sUnion, ← Sup_image, inf_Sup_eq_of_directed_on, supr_eq_bot],
      { intro i,
        rw supr_eq_bot,
        intro hi,
        obtain ⟨x, xc, rfl⟩ := (set.mem_image _ _ _).1 hi,
        exact (hc1 xc).2.1 },
      { rw directed_on_image,
        refine hc2.directed_on.mono (λ s t, Sup_le_Sup) } },
    { rcases set.mem_sUnion.1 ha with ⟨s, sc, as⟩,
      exact (hc1 sc).2.2 a as } }
end

/-- See Theorem 6.6, Călugăreanu -/
lemma is_complemented_of_Sup_atoms_eq_top
  (h : Sup {a : α | is_atom a} = ⊤) : is_complemented α :=
⟨λ b, begin
  obtain ⟨s, s_ind, s_top, s_atoms⟩ := exists_set_independent_Sup_atoms_eq_compl h b,
  refine ⟨Sup s, s_top⟩
end⟩

lemma is_atomistic.exist_set_independent_Sup_eq_top (h : Sup {a : α | is_atom a} = ⊤) :
  ∃ s : set α, complete_lattice.set_independent s ∧ Sup s = ⊤ ∧ ∀ a ∈ s, is_atom a :=
begin
  obtain ⟨s, s_ind, s_top, s_atoms⟩ := exists_set_independent_Sup_atoms_eq_compl h (⊥ : α),
  refine ⟨s, s_ind, eq_top_of_is_compl_bot (is_compl.symm s_top), s_atoms⟩,
end

/-- See Theorem 6.6, Călugăreanu -/
theorem is_complemented_of_is_atomistic [is_atomistic α] : is_complemented α :=
is_complemented_of_Sup_atoms_eq_top Sup_atoms_eq_top

theorem is_complemented_iff_is_atomistic : is_complemented α ↔ is_atomistic α :=
begin
  split; introsI,
  { exact is_atomistic_of_is_complemented },
  { exact is_complemented_of_is_atomistic }
end

end
