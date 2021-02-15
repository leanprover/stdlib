/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import topology.bases
import data.finset.order

/-!
# Properties of subsets of topological spaces

In this file we define various properties of subsets of a topological space, and some classes on
topological spaces.

## Main definitions

We define the following properties for sets in a topological space:

* `is_compact`: each open cover has a finite subcover. This is defined in mathlib using filters.
  The main property of a compact set is `is_compact.elim_finite_subcover`.
* `is_clopen`: a set that is both open and closed.
* `is_irreducible`: a nonempty set that has contains no non-trivial pair of disjoint opens.
  See also the section below in the module doc.

For each of these definitions (except for `is_clopen`), we also have a class stating that the whole
space satisfies that property:
`compact_space`, `irreducible_space`

Furthermore, we have two more classes:
* `locally_compact_space`: for every point `x`, every open neighborhood of `x` contains a compact
  neighborhood of `x`. The definition is formulated in terms of the neighborhood filter.
* `sigma_compact_space`: a space that is the union of a countably many compact subspaces.

## On the definition of irreducible and connected sets/spaces

In informal mathematics, irreducible spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `is_preirreducible`.
In other words, the only difference is whether the empty space counts as irreducible.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.
-/

open set filter classical topological_space
open_locale classical topological_space filter

universes u v
variables {α : Type u} {β : Type v} [topological_space α] {s t : set α}

/- compact sets -/
section compact

/-- A set `s` is compact if for every nontrivial filter `f` that contains `s`,
    there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`. -/
def is_compact (s : set α) := ∀ ⦃f⦄ [ne_bot f], f ≤ 𝓟 s → ∃a∈s, cluster_pt a f

/-- The complement to a compact set belongs to a filter `f` if it belongs to each filter
`𝓝 a ⊓ f`, `a ∈ s`. -/
lemma is_compact.compl_mem_sets (hs : is_compact s) {f : filter α} (hf : ∀ a ∈ s, sᶜ ∈ 𝓝 a ⊓ f) :
  sᶜ ∈ f :=
begin
  contrapose! hf,
  simp only [not_mem_iff_inf_principal_compl, compl_compl, inf_assoc, ← exists_prop] at hf ⊢,
  exact @hs _ hf inf_le_right
end

/-- The complement to a compact set belongs to a filter `f` if each `a ∈ s` has a neighborhood `t`
within `s` such that `tᶜ` belongs to `f`. -/
lemma is_compact.compl_mem_sets_of_nhds_within (hs : is_compact s) {f : filter α}
  (hf : ∀ a ∈ s, ∃ t ∈ 𝓝[s] a, tᶜ ∈ f) :
  sᶜ ∈ f :=
begin
  refine hs.compl_mem_sets (λ a ha, _),
  rcases hf a ha with ⟨t, ht, hst⟩,
  replace ht := mem_inf_principal.1 ht,
  refine mem_inf_sets.2 ⟨_, ht, _, hst, _⟩,
  rintros x ⟨h₁, h₂⟩ hs,
  exact h₂ (h₁ hs)
end

/-- If `p : set α → Prop` is stable under restriction and union, and each point `x`
  of a compact set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_eliminator]
lemma is_compact.induction_on {s : set α} (hs : is_compact s) {p : set α → Prop} (he : p ∅)
  (hmono : ∀ ⦃s t⦄, s ⊆ t → p t → p s) (hunion : ∀ ⦃s t⦄, p s → p t → p (s ∪ t))
  (hnhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, p t) :
  p s :=
let f : filter α :=
  { sets := {t | p tᶜ},
    univ_sets := by simpa,
    sets_of_superset := λ t₁ t₂ ht₁ ht, hmono (compl_subset_compl.2 ht) ht₁,
    inter_sets := λ t₁ t₂ ht₁ ht₂, by simp [compl_inter, hunion ht₁ ht₂] } in
have sᶜ ∈ f, from hs.compl_mem_sets_of_nhds_within (by simpa using hnhds),
by simpa

/-- The intersection of a compact set and a closed set is a compact set. -/
lemma is_compact.inter_right (hs : is_compact s) (ht : is_closed t) :
  is_compact (s ∩ t) :=
begin
  introsI f hnf hstf,
  obtain ⟨a, hsa, ha⟩ : ∃ a ∈ s, cluster_pt a f :=
    hs (le_trans hstf (le_principal_iff.2 (inter_subset_left _ _))),
  have : a ∈ t :=
    (ht.mem_of_nhds_within_ne_bot $ ha.mono $
      le_trans hstf (le_principal_iff.2 (inter_subset_right _ _))),
  exact ⟨a, ⟨hsa, this⟩, ha⟩
end

/-- The intersection of a closed set and a compact set is a compact set. -/
lemma is_compact.inter_left (ht : is_compact t) (hs : is_closed s) : is_compact (s ∩ t) :=
inter_comm t s ▸ ht.inter_right hs

/-- The set difference of a compact set and an open set is a compact set. -/
lemma compact_diff (hs : is_compact s) (ht : is_open t) : is_compact (s \ t) :=
hs.inter_right (is_closed_compl_iff.mpr ht)

/-- A closed subset of a compact set is a compact set. -/
lemma compact_of_is_closed_subset (hs : is_compact s) (ht : is_closed t) (h : t ⊆ s) :
  is_compact t :=
inter_eq_self_of_subset_right h ▸ hs.inter_right ht

lemma is_compact.adherence_nhdset {f : filter α}
  (hs : is_compact s) (hf₂ : f ≤ 𝓟 s) (ht₁ : is_open t) (ht₂ : ∀a∈s, cluster_pt a f → a ∈ t) :
  t ∈ f :=
classical.by_cases mem_sets_of_eq_bot $
  assume : f ⊓ 𝓟 tᶜ ≠ ⊥,
  let ⟨a, ha, (hfa : cluster_pt a $ f ⊓ 𝓟 tᶜ)⟩ := @@hs ⟨this⟩ $ inf_le_left_of_le hf₂ in
  have a ∈ t,
    from ht₂ a ha (hfa.of_inf_left),
  have tᶜ ∩ t ∈ 𝓝[tᶜ] a,
    from inter_mem_nhds_within _ (mem_nhds_sets ht₁ this),
  have A : 𝓝[tᶜ] a = ⊥,
    from empty_in_sets_eq_bot.1 $ compl_inter_self t ▸ this,
  have 𝓝[tᶜ] a ≠ ⊥,
    from hfa.of_inf_right.ne,
  absurd A this

lemma compact_iff_ultrafilter_le_nhds :
  is_compact s ↔ (∀f : ultrafilter α, ↑f ≤ 𝓟 s → ∃a∈s, ↑f ≤ 𝓝 a) :=
begin
  refine (forall_ne_bot_le_iff _).trans _,
  { rintro f g hle ⟨a, has, haf⟩,
    exact ⟨a, has, haf.mono hle⟩ },
  { simp only [ultrafilter.cluster_pt_iff] }
end

alias compact_iff_ultrafilter_le_nhds ↔ is_compact.ultrafilter_le_nhds _

/-- For every open cover of a compact set, there exists a finite subcover. -/
lemma is_compact.elim_finite_subcover {ι : Type v} (hs : is_compact s)
  (U : ι → set α) (hUo : ∀i, is_open (U i)) (hsU : s ⊆ ⋃ i, U i) :
  ∃ t : finset ι, s ⊆ ⋃ i ∈ t, U i :=
is_compact.induction_on hs ⟨∅, empty_subset _⟩ (λ s₁ s₂ hs ⟨t, hs₂⟩, ⟨t, subset.trans hs hs₂⟩)
  (λ s₁ s₂ ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩,
    ⟨t₁ ∪ t₂, by { rw [finset.set_bUnion_union], exact union_subset_union ht₁ ht₂ }⟩)
  (λ x hx, let ⟨i, hi⟩ := mem_Union.1 (hsU hx) in
    ⟨U i, mem_nhds_within.2 ⟨U i, hUo i, hi, inter_subset_left _ _⟩, {i}, by simp⟩)

/-- For every family of closed sets whose intersection avoids a compact set,
there exists a finite subfamily whose intersection avoids this compact set. -/
lemma is_compact.elim_finite_subfamily_closed {s : set α} {ι : Type v} (hs : is_compact s)
  (Z : ι → set α) (hZc : ∀i, is_closed (Z i)) (hsZ : s ∩ (⋂ i, Z i) = ∅) :
  ∃ t : finset ι, s ∩ (⋂ i ∈ t, Z i) = ∅ :=
let ⟨t, ht⟩ := hs.elim_finite_subcover (λ i, (Z i)ᶜ) hZc
  (by simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_Union,
    exists_prop, mem_inter_eq, not_and, iff_self, mem_Inter, mem_compl_eq] using hsZ)
    in
⟨t, by simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_Union,
    exists_prop, mem_inter_eq, not_and, iff_self, mem_Inter, mem_compl_eq] using ht⟩

/-- To show that a compact set intersects the intersection of a family of closed sets,
  it is sufficient to show that it intersects every finite subfamily. -/
lemma is_compact.inter_Inter_nonempty {s : set α} {ι : Type v} (hs : is_compact s)
  (Z : ι → set α) (hZc : ∀i, is_closed (Z i)) (hsZ : ∀ t : finset ι, (s ∩ ⋂ i ∈ t, Z i).nonempty) :
  (s ∩ ⋂ i, Z i).nonempty :=
begin
  simp only [← ne_empty_iff_nonempty] at hsZ ⊢,
  apply mt (hs.elim_finite_subfamily_closed Z hZc), push_neg, exact hsZ
end

/-- Cantor's intersection theorem:
the intersection of a directed family of nonempty compact closed sets is nonempty. -/
lemma is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
  {ι : Type v} [hι : nonempty ι] (Z : ι → set α) (hZd : directed (⊇) Z)
  (hZn : ∀ i, (Z i).nonempty) (hZc : ∀ i, is_compact (Z i)) (hZcl : ∀ i, is_closed (Z i)) :
  (⋂ i, Z i).nonempty :=
begin
  apply hι.elim,
  intro i₀,
  let Z' := λ i, Z i ∩ Z i₀,
  suffices : (⋂ i, Z' i).nonempty,
  { exact nonempty.mono (Inter_subset_Inter $ assume i, inter_subset_left (Z i) (Z i₀)) this },
  rw ← ne_empty_iff_nonempty,
  intro H,
  obtain ⟨t, ht⟩ : ∃ (t : finset ι), ((Z i₀) ∩ ⋂ (i ∈ t), Z' i) = ∅,
    from (hZc i₀).elim_finite_subfamily_closed Z'
      (assume i, is_closed_inter (hZcl i) (hZcl i₀)) (by rw [H, inter_empty]),
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : ι, Z i₁ ⊆ Z i₀ ∧ ∀ i ∈ t, Z i₁ ⊆ Z' i,
  { rcases directed.finset_le hZd t with ⟨i, hi⟩,
    rcases hZd i i₀ with ⟨i₁, hi₁, hi₁₀⟩,
    use [i₁, hi₁₀],
    intros j hj,
    exact subset_inter (subset.trans hi₁ (hi j hj)) hi₁₀ },
  suffices : ((Z i₀) ∩ ⋂ (i ∈ t), Z' i).nonempty,
  { rw ← ne_empty_iff_nonempty at this, contradiction },
  refine nonempty.mono _ (hZn i₁),
  exact subset_inter hi₁.left (subset_bInter hi₁.right)
end

/-- Cantor's intersection theorem for sequences indexed by `ℕ`:
the intersection of a decreasing sequence of nonempty compact closed sets is nonempty. -/
lemma is_compact.nonempty_Inter_of_sequence_nonempty_compact_closed
  (Z : ℕ → set α) (hZd : ∀ i, Z (i+1) ⊆ Z i)
  (hZn : ∀ i, (Z i).nonempty) (hZ0 : is_compact (Z 0)) (hZcl : ∀ i, is_closed (Z i)) :
  (⋂ i, Z i).nonempty :=
have Zmono : _, from @monotone_of_monotone_nat (order_dual _) _ Z hZd,
have hZd : directed (⊇) Z, from directed_of_sup Zmono,
have ∀ i, Z i ⊆ Z 0, from assume i, Zmono $ zero_le i,
have hZc : ∀ i, is_compact (Z i), from assume i, compact_of_is_closed_subset hZ0 (hZcl i) (this i),
is_compact.nonempty_Inter_of_directed_nonempty_compact_closed Z hZd hZn hZc hZcl

/-- For every open cover of a compact set, there exists a finite subcover. -/
lemma is_compact.elim_finite_subcover_image {b : set β} {c : β → set α}
  (hs : is_compact s) (hc₁ : ∀i∈b, is_open (c i)) (hc₂ : s ⊆ ⋃i∈b, c i) :
  ∃b'⊆b, finite b' ∧ s ⊆ ⋃i∈b', c i :=
begin
  rcases hs.elim_finite_subcover (λ i, c i.1 : b → set α) _ _ with ⟨d, hd⟩,
  refine ⟨↑(d.image subtype.val), _, finset.finite_to_set _, _⟩,
  { intros i hi,
    erw finset.mem_image at hi,
    rcases hi with ⟨s, hsd, rfl⟩,
    exact s.property },
  { refine subset.trans hd _,
    rintros x ⟨_, ⟨s, rfl⟩, ⟨_, ⟨hsd, rfl⟩, H⟩⟩,
    refine ⟨c s.val, ⟨s.val, _⟩, H⟩,
    simp [finset.mem_image_of_mem subtype.val hsd] },
  { rintro ⟨i, hi⟩, exact hc₁ i hi },
  { refine subset.trans hc₂ _,
    rintros x ⟨_, ⟨i, rfl⟩, ⟨_, ⟨hib, rfl⟩, H⟩⟩,
    exact ⟨_, ⟨⟨i, hib⟩, rfl⟩, H⟩ },
end

/-- A set `s` is compact if for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
theorem compact_of_finite_subfamily_closed
  (h : Π {ι : Type u} (Z : ι → (set α)), (∀ i, is_closed (Z i)) →
    s ∩ (⋂ i, Z i) = ∅ → (∃ (t : finset ι), s ∩ (⋂ i ∈ t, Z i) = ∅)) :
  is_compact s :=
assume f hfn hfs, classical.by_contradiction $ assume : ¬ (∃x∈s, cluster_pt x f),
  have hf : ∀x∈s, 𝓝 x ⊓ f = ⊥,
    by simpa only [cluster_pt, not_exists, not_not, ne_bot_iff],
  have ¬ ∃x∈s, ∀t∈f.sets, x ∈ closure t,
    from assume ⟨x, hxs, hx⟩,
    have ∅ ∈ 𝓝 x ⊓ f, by rw [empty_in_sets_eq_bot, hf x hxs],
    let ⟨t₁, ht₁, t₂, ht₂, ht⟩ := by rw [mem_inf_sets] at this; exact this in
    have ∅ ∈ 𝓝[t₂] x,
      from (𝓝[t₂] x).sets_of_superset (inter_mem_inf_sets ht₁ (subset.refl t₂)) ht,
    have 𝓝[t₂] x = ⊥,
      by rwa [empty_in_sets_eq_bot] at this,
    by simp only [closure_eq_cluster_pts] at hx; exact (hx t₂ ht₂).ne this,
  let ⟨t, ht⟩ := h (λ i : f.sets, closure i.1) (λ i, is_closed_closure)
    (by simpa [eq_empty_iff_forall_not_mem, not_exists]) in
  have (⋂i∈t, subtype.val i) ∈ f,
    from t.Inter_mem_sets.2 $ assume i hi, i.2,
  have s ∩ (⋂i∈t, subtype.val i) ∈ f,
    from inter_mem_sets (le_principal_iff.1 hfs) this,
  have ∅ ∈ f,
    from mem_sets_of_superset this $ assume x ⟨hxs, hx⟩,
    let ⟨i, hit, hxi⟩ := (show ∃i ∈ t, x ∉ closure (subtype.val i),
      by { rw [eq_empty_iff_forall_not_mem] at ht, simpa [hxs, not_forall] using ht x }) in
    have x ∈ closure i.val, from subset_closure (mem_bInter_iff.mp hx i hit),
    show false, from hxi this,
  hfn.ne $ by rwa [empty_in_sets_eq_bot] at this

/-- A set `s` is compact if for every open cover of `s`, there exists a finite subcover. -/
lemma compact_of_finite_subcover
  (h : Π {ι : Type u} (U : ι → (set α)), (∀ i, is_open (U i)) →
    s ⊆ (⋃ i, U i) → (∃ (t : finset ι), s ⊆ (⋃ i ∈ t, U i))) :
  is_compact s :=
compact_of_finite_subfamily_closed $
  assume ι Z hZc hsZ,
  let ⟨t, ht⟩ := h (λ i, (Z i)ᶜ) (assume i, is_open_compl_iff.mpr $ hZc i)
    (by simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_Union,
      exists_prop, mem_inter_eq, not_and, iff_self, mem_Inter, mem_compl_eq] using hsZ)
      in
  ⟨t, by simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_Union,
      exists_prop, mem_inter_eq, not_and, iff_self, mem_Inter, mem_compl_eq] using ht⟩

/-- A set `s` is compact if and only if
for every open cover of `s`, there exists a finite subcover. -/
lemma compact_iff_finite_subcover :
  is_compact s ↔ (Π {ι : Type u} (U : ι → (set α)), (∀ i, is_open (U i)) →
    s ⊆ (⋃ i, U i) → (∃ (t : finset ι), s ⊆ (⋃ i ∈ t, U i))) :=
⟨assume hs ι, hs.elim_finite_subcover, compact_of_finite_subcover⟩

/-- A set `s` is compact if and only if
for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
theorem compact_iff_finite_subfamily_closed :
  is_compact s ↔ (Π {ι : Type u} (Z : ι → (set α)), (∀ i, is_closed (Z i)) →
    s ∩ (⋂ i, Z i) = ∅ → (∃ (t : finset ι), s ∩ (⋂ i ∈ t, Z i) = ∅)) :=
⟨assume hs ι, hs.elim_finite_subfamily_closed, compact_of_finite_subfamily_closed⟩

@[simp]
lemma compact_empty : is_compact (∅ : set α) :=
assume f hnf hsf, not.elim hnf.ne $
empty_in_sets_eq_bot.1 $ le_principal_iff.1 hsf

@[simp]
lemma compact_singleton {a : α} : is_compact ({a} : set α) :=
λ f hf hfa, ⟨a, rfl, cluster_pt.of_le_nhds'
  (hfa.trans $ by simpa only [principal_singleton] using pure_le_nhds a) hf⟩

lemma set.subsingleton.is_compact {s : set α} (hs : s.subsingleton) : is_compact s :=
subsingleton.induction_on hs compact_empty $ λ x, compact_singleton

lemma set.finite.compact_bUnion {s : set β} {f : β → set α} (hs : finite s)
  (hf : ∀i ∈ s, is_compact (f i)) :
  is_compact (⋃i ∈ s, f i) :=
compact_of_finite_subcover $ assume ι U hUo hsU,
  have ∀i : subtype s, ∃t : finset ι, f i ⊆ (⋃ j ∈ t, U j), from
    assume ⟨i, hi⟩, (hf i hi).elim_finite_subcover _ hUo
      (calc f i ⊆ ⋃i ∈ s, f i : subset_bUnion_of_mem hi
            ... ⊆ ⋃j, U j     : hsU),
  let ⟨finite_subcovers, h⟩ := axiom_of_choice this in
  by haveI : fintype (subtype s) := hs.fintype; exact
  let t := finset.bUnion finset.univ finite_subcovers in
  have (⋃i ∈ s, f i) ⊆ (⋃ i ∈ t, U i), from bUnion_subset $
    assume i hi, calc
    f i ⊆ (⋃ j ∈ finite_subcovers ⟨i, hi⟩, U j) : (h ⟨i, hi⟩)
    ... ⊆ (⋃ j ∈ t, U j) : bUnion_subset_bUnion_left $
      assume j hj, finset.mem_bUnion.mpr ⟨_, finset.mem_univ _, hj⟩,
  ⟨t, this⟩

lemma compact_Union {f : β → set α} [fintype β]
  (h : ∀i, is_compact (f i)) : is_compact (⋃i, f i) :=
by rw ← bUnion_univ; exact finite_univ.compact_bUnion (λ i _, h i)

lemma set.finite.is_compact (hs : finite s) : is_compact s :=
bUnion_of_singleton s ▸ hs.compact_bUnion (λ _ _, compact_singleton)

lemma finite_of_is_compact_of_discrete [discrete_topology α] (s : set α) (hs : is_compact s) :
  s.finite :=
begin
  have := hs.elim_finite_subcover (λ x : α, ({x} : set α))
    (λ x, is_open_discrete _),
  simp only [set.subset_univ, forall_prop_of_true, set.Union_of_singleton] at this,
  rcases this with ⟨t, ht⟩,
  suffices : (⋃ (i : α) (H : i ∈ t), {i} : set α) = (t : set α),
  { rw this at ht, exact t.finite_to_set.subset ht },
  ext x,
  simp only [exists_prop, set.mem_Union, set.mem_singleton_iff, exists_eq_right', finset.mem_coe]
end

lemma is_compact.union (hs : is_compact s) (ht : is_compact t) : is_compact (s ∪ t) :=
by rw union_eq_Union; exact compact_Union (λ b, by cases b; assumption)

lemma is_compact.insert (hs : is_compact s) (a) : is_compact (insert a s) :=
compact_singleton.union hs

/-- `filter.cocompact` is the filter generated by complements to compact sets. -/
def filter.cocompact (α : Type*) [topological_space α] : filter α :=
⨅ (s : set α) (hs : is_compact s), 𝓟 (sᶜ)
lemma filter.has_basis_cocompact : (filter.cocompact α).has_basis is_compact compl :=
has_basis_binfi_principal'
  (λ s hs t ht, ⟨s ∪ t, hs.union ht, compl_subset_compl.2 (subset_union_left s t),
    compl_subset_compl.2 (subset_union_right s t)⟩)
  ⟨∅, compact_empty⟩

lemma filter.mem_cocompact : s ∈ filter.cocompact α ↔ ∃ t, is_compact t ∧ tᶜ ⊆ s :=
filter.has_basis_cocompact.mem_iff.trans $ exists_congr $ λ t,  exists_prop

lemma filter.mem_cocompact' : s ∈ filter.cocompact α ↔ ∃ t, is_compact t ∧ sᶜ ⊆ t :=
filter.mem_cocompact.trans $ exists_congr $ λ t, and_congr_right $ λ ht, compl_subset_comm

lemma is_compact.compl_mem_cocompact (hs : is_compact s) : sᶜ ∈ filter.cocompact α :=
filter.has_basis_cocompact.mem_of_mem hs

section tube_lemma

variables [topological_space β]

/-- `nhds_contain_boxes s t` means that any open neighborhood of `s × t` in `α × β` includes
a product of an open neighborhood of `s` by an open neighborhood of `t`. -/
def nhds_contain_boxes (s : set α) (t : set β) : Prop :=
∀ (n : set (α × β)) (hn : is_open n) (hp : set.prod s t ⊆ n),
∃ (u : set α) (v : set β), is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ set.prod u v ⊆ n

lemma nhds_contain_boxes.symm {s : set α} {t : set β} :
  nhds_contain_boxes s t → nhds_contain_boxes t s :=
assume H n hn hp,
  let ⟨u, v, uo, vo, su, tv, p⟩ :=
    H (prod.swap ⁻¹' n)
      (hn.preimage continuous_swap)
      (by rwa [←image_subset_iff, image_swap_prod]) in
  ⟨v, u, vo, uo, tv, su,
    by rwa [←image_subset_iff, image_swap_prod] at p⟩

lemma nhds_contain_boxes.comm {s : set α} {t : set β} :
  nhds_contain_boxes s t ↔ nhds_contain_boxes t s :=
iff.intro nhds_contain_boxes.symm nhds_contain_boxes.symm

lemma nhds_contain_boxes_of_singleton {x : α} {y : β} :
  nhds_contain_boxes ({x} : set α) ({y} : set β) :=
assume n hn hp,
  let ⟨u, v, uo, vo, xu, yv, hp'⟩ :=
    is_open_prod_iff.mp hn x y (hp $ by simp) in
  ⟨u, v, uo, vo, by simpa, by simpa, hp'⟩

lemma nhds_contain_boxes_of_compact {s : set α} (hs : is_compact s) (t : set β)
  (H : ∀ x ∈ s, nhds_contain_boxes ({x} : set α) t) : nhds_contain_boxes s t :=
assume n hn hp,
have ∀x : subtype s, ∃uv : set α × set β,
     is_open uv.1 ∧ is_open uv.2 ∧ {↑x} ⊆ uv.1 ∧ t ⊆ uv.2 ∧ set.prod uv.1 uv.2 ⊆ n,
  from assume ⟨x, hx⟩,
    have set.prod {x} t ⊆ n, from
      subset.trans (prod_mono (by simpa) (subset.refl _)) hp,
    let ⟨ux,vx,H1⟩ := H x hx n hn this in ⟨⟨ux,vx⟩,H1⟩,
let ⟨uvs, h⟩ := classical.axiom_of_choice this in
have us_cover : s ⊆ ⋃i, (uvs i).1, from
  assume x hx, subset_Union _ ⟨x,hx⟩ (by simpa using (h ⟨x,hx⟩).2.2.1),
let ⟨s0, s0_cover⟩ :=
  hs.elim_finite_subcover _ (λi, (h i).1) us_cover in
let u := ⋃(i ∈ s0), (uvs i).1 in
let v := ⋂(i ∈ s0), (uvs i).2 in
have is_open u, from is_open_bUnion (λi _, (h i).1),
have is_open v, from is_open_bInter s0.finite_to_set (λi _, (h i).2.1),
have t ⊆ v, from subset_bInter (λi _, (h i).2.2.2.1),
have set.prod u v ⊆ n, from assume ⟨x',y'⟩ ⟨hx',hy'⟩,
  have ∃i ∈ s0, x' ∈ (uvs i).1, by simpa using hx',
  let ⟨i,is0,hi⟩ := this in
  (h i).2.2.2.2 ⟨hi, (bInter_subset_of_mem is0 : v ⊆ (uvs i).2) hy'⟩,
⟨u, v, ‹is_open u›, ‹is_open v›, s0_cover, ‹t ⊆ v›, ‹set.prod u v ⊆ n›⟩

/-- If `s` and `t` are compact sets and `n` is an open neighborhood of `s × t`, then there exist
open neighborhoods `u ⊇ s` and `v ⊇ t` such that `u × v ⊆ n`. -/
lemma generalized_tube_lemma {s : set α} (hs : is_compact s) {t : set β} (ht : is_compact t)
  {n : set (α × β)} (hn : is_open n) (hp : set.prod s t ⊆ n) :
  ∃ (u : set α) (v : set β), is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ set.prod u v ⊆ n :=
have _, from
  nhds_contain_boxes_of_compact hs t $ assume x _, nhds_contain_boxes.symm $
    nhds_contain_boxes_of_compact ht {x} $ assume y _, nhds_contain_boxes_of_singleton,
this n hn hp

end tube_lemma

/-- Type class for compact spaces. Separation is sometimes included in the definition, especially
in the French literature, but we do not include it here. -/
class compact_space (α : Type*) [topological_space α] : Prop :=
(compact_univ : is_compact (univ : set α))

@[priority 10] -- see Note [lower instance priority]
instance subsingleton.compact_space [subsingleton α] : compact_space α :=
⟨subsingleton_univ.is_compact⟩

lemma compact_univ [h : compact_space α] : is_compact (univ : set α) := h.compact_univ

lemma cluster_point_of_compact [compact_space α] (f : filter α) [ne_bot f] :
  ∃ x, cluster_pt x f :=
by simpa using compact_univ (show f ≤ 𝓟 univ, by simp)

theorem compact_space_of_finite_subfamily_closed {α : Type u} [topological_space α]
  (h : Π {ι : Type u} (Z : ι → (set α)), (∀ i, is_closed (Z i)) →
    (⋂ i, Z i) = ∅ → ∃ (t : finset ι), (⋂ i ∈ t, Z i) = ∅) :
  compact_space α :=
{ compact_univ :=
  begin
    apply compact_of_finite_subfamily_closed,
    intros ι Z, specialize h Z,
    simpa using h
  end }

lemma is_closed.compact [compact_space α] {s : set α} (h : is_closed s) :
  is_compact s :=
compact_of_is_closed_subset compact_univ h (subset_univ _)

/-- A compact discrete space is finite. -/
noncomputable
def fintype_of_compact_of_discrete [compact_space α] [discrete_topology α] :
  fintype α :=
fintype_of_univ_finite $ finite_of_is_compact_of_discrete _ compact_univ

variables [topological_space β]

lemma is_compact.image_of_continuous_on {f : α → β} (hs : is_compact s) (hf : continuous_on f s) :
  is_compact (f '' s) :=
begin
  intros l lne ls,
  have : ne_bot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_ne_bot_of_image_mem lne (le_principal_iff.1 ls),
  obtain ⟨a, has, ha⟩ : ∃ a ∈ s, cluster_pt a (l.comap f ⊓ 𝓟 s) := @@hs this inf_le_right,
  use [f a, mem_image_of_mem f has],
  have : tendsto f (𝓝 a ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f a) ⊓ l),
  { convert (hf a has).inf (@tendsto_comap _ _ f l) using 1,
    rw nhds_within,
    ac_refl },
  exact @@tendsto.ne_bot _ this ha,
end

lemma is_compact.image {f : α → β} (hs : is_compact s) (hf : continuous f) :
  is_compact (f '' s) :=
hs.image_of_continuous_on hf.continuous_on

lemma compact_range [compact_space α] {f : α → β} (hf : continuous f) :
  is_compact (range f) :=
by rw ← image_univ; exact compact_univ.image hf

/-- If X is is_compact then pr₂ : X × Y → Y is a closed map -/
theorem is_closed_proj_of_compact
  {X : Type*} [topological_space X] [compact_space X]
  {Y : Type*} [topological_space Y]  :
  is_closed_map (prod.snd : X × Y → Y) :=
begin
  set πX := (prod.fst : X × Y → X),
  set πY := (prod.snd : X × Y → Y),
  assume C (hC : is_closed C),
  rw is_closed_iff_cluster_pt at hC ⊢,
  assume y (y_closure : cluster_pt y $ 𝓟 (πY '' C)),
  have : ne_bot (map πX (comap πY (𝓝 y) ⊓ 𝓟 C)),
  { suffices : ne_bot (map πY (comap πY (𝓝 y) ⊓ 𝓟 C)),
      by simpa only [map_ne_bot_iff],
    convert y_closure,
    calc map πY (comap πY (𝓝 y) ⊓ 𝓟 C) =
       𝓝 y ⊓ map πY (𝓟 C) : filter.push_pull' _ _ _
      ... = 𝓝 y ⊓ 𝓟 (πY '' C) : by rw map_principal },
  resetI,
  obtain ⟨x, hx⟩ : ∃ x, cluster_pt x (map πX (comap πY (𝓝 y) ⊓ 𝓟 C)),
    from cluster_point_of_compact _,
  refine ⟨⟨x, y⟩, _, by simp [πY]⟩,
  apply hC,
  rw [cluster_pt, ← filter.map_ne_bot_iff πX],
  convert hx,
  calc map πX (𝓝 (x, y) ⊓ 𝓟 C)
      = map πX (comap πX (𝓝 x) ⊓ comap πY (𝓝 y) ⊓ 𝓟 C) : by rw [nhds_prod_eq, filter.prod]
  ... = map πX (comap πY (𝓝 y) ⊓ 𝓟 C ⊓ comap πX (𝓝 x)) : by ac_refl
  ... = map πX (comap πY (𝓝 y) ⊓ 𝓟 C) ⊓ 𝓝 x            : by rw filter.push_pull
  ... = 𝓝 x ⊓ map πX (comap πY (𝓝 y) ⊓ 𝓟 C)            : by rw inf_comm
end

lemma embedding.compact_iff_compact_image {f : α → β} (hf : embedding f) :
  is_compact s ↔ is_compact (f '' s) :=
iff.intro (assume h, h.image hf.continuous) $ assume h, begin
  rw compact_iff_ultrafilter_le_nhds at ⊢ h,
  intros u us',
  have : ↑(u.map f) ≤ 𝓟 (f '' s), begin
    rw [ultrafilter.coe_map, map_le_iff_le_comap, comap_principal], convert us',
    exact preimage_image_eq _ hf.inj
  end,
  rcases h (u.map f) this with ⟨_, ⟨a, ha, ⟨⟩⟩, _⟩,
  refine ⟨a, ha, _⟩,
  rwa [hf.induced, nhds_induced, ←map_le_iff_le_comap]
end

lemma compact_iff_compact_in_subtype {p : α → Prop} {s : set {a // p a}} :
  is_compact s ↔ is_compact ((coe : _ → α) '' s) :=
embedding_subtype_coe.compact_iff_compact_image

lemma compact_iff_compact_univ {s : set α} : is_compact s ↔ is_compact (univ : set s) :=
by rw [compact_iff_compact_in_subtype, image_univ, subtype.range_coe]; refl

lemma compact_iff_compact_space {s : set α} : is_compact s ↔ compact_space s :=
compact_iff_compact_univ.trans ⟨λ h, ⟨h⟩, @compact_space.compact_univ _ _⟩

lemma is_compact.prod {s : set α} {t : set β} (hs : is_compact s) (ht : is_compact t) :
  is_compact (set.prod s t) :=
begin
  rw compact_iff_ultrafilter_le_nhds at hs ht ⊢,
  intros f hfs,
  rw le_principal_iff at hfs,
  obtain ⟨a : α, sa : a ∈ s, ha : map prod.fst ↑f ≤ 𝓝 a⟩ :=
    hs (f.map prod.fst) (le_principal_iff.2 $ mem_map.2 $ mem_sets_of_superset hfs (λ x, and.left)),
  obtain ⟨b : β, tb : b ∈ t, hb : map prod.snd ↑f ≤ 𝓝 b⟩ :=
    ht (f.map prod.snd) (le_principal_iff.2 $ mem_map.2 $
      mem_sets_of_superset hfs (λ x, and.right)),
  rw map_le_iff_le_comap at ha hb,
  refine ⟨⟨a, b⟩, ⟨sa, tb⟩, _⟩,
  rw nhds_prod_eq, exact le_inf ha hb
end

/-- Finite topological spaces are compact. -/
@[priority 100] instance fintype.compact_space [fintype α] : compact_space α :=
{ compact_univ := finite_univ.is_compact }

/-- The product of two compact spaces is compact. -/
instance [compact_space α] [compact_space β] : compact_space (α × β) :=
⟨by { rw ← univ_prod_univ, exact compact_univ.prod compact_univ }⟩

/-- The disjoint union of two compact spaces is compact. -/
instance [compact_space α] [compact_space β] : compact_space (α ⊕ β) :=
⟨begin
  rw ← range_inl_union_range_inr,
  exact (compact_range continuous_inl).union (compact_range continuous_inr)
end⟩

section tychonoff
variables {ι : Type*} {π : ι → Type*} [∀ i, topological_space (π i)]

/-- Tychonoff's theorem -/
lemma compact_pi_infinite {s : Π i, set (π i)} :
  (∀ i, is_compact (s i)) → is_compact {x : Π i, π i | ∀ i, x i ∈ s i} :=
begin
  simp only [compact_iff_ultrafilter_le_nhds, nhds_pi, exists_prop, mem_set_of_eq, le_infi_iff,
    le_principal_iff],
  intros h f hfs,
  have : ∀i:ι, ∃a, a∈s i ∧ tendsto (λx:Πi:ι, π i, x i) f (𝓝 a),
  { refine λ i, h i (f.map _) (mem_map.2 _),
    exact mem_sets_of_superset hfs (λ x hx, hx i) },
  choose a ha,
  exact  ⟨a, assume i, (ha i).left, assume i, (ha i).right.le_comap⟩
end

/-- A version of Tychonoff's theorem that uses `set.pi`. -/
lemma compact_univ_pi {s : Π i, set (π i)} (h : ∀ i, is_compact (s i)) :
  is_compact (pi univ s) :=
by { convert compact_pi_infinite h, simp only [pi, forall_prop_of_true, mem_univ] }

instance pi.compact_space [∀ i, compact_space (π i)] : compact_space (Πi, π i) :=
⟨by { rw [← pi_univ univ], exact compact_univ_pi (λ i, compact_univ) }⟩

end tychonoff

instance quot.compact_space {r : α → α → Prop} [compact_space α] :
  compact_space (quot r) :=
⟨by { rw ← range_quot_mk, exact compact_range continuous_quot_mk }⟩

instance quotient.compact_space {s : setoid α} [compact_space α] :
  compact_space (quotient s) :=
quot.compact_space

/-- There are various definitions of "locally compact space" in the literature, which agree for
Hausdorff spaces but not in general. This one is the precise condition on X needed for the
evaluation `map C(X, Y) × X → Y` to be continuous for all `Y` when `C(X, Y)` is given the
compact-open topology. -/
class locally_compact_space (α : Type*) [topological_space α] : Prop :=
(local_compact_nhds : ∀ (x : α) (n ∈ 𝓝 x), ∃ s ∈ 𝓝 x, s ⊆ n ∧ is_compact s)

/-- A reformulation of the definition of locally compact space: In a locally compact space,
  every open set containing `x` has a compact subset containing `x` in its interior. -/
lemma exists_compact_subset [locally_compact_space α] {x : α} {U : set α}
  (hU : is_open U) (hx : x ∈ U) : ∃ (K : set α), is_compact K ∧ x ∈ interior K ∧ K ⊆ U :=
begin
  rcases locally_compact_space.local_compact_nhds x U _ with ⟨K, h1K, h2K, h3K⟩,
  { refine ⟨K, h3K, _, h2K⟩, rwa [ mem_interior_iff_mem_nhds] },
  rwa [← mem_interior_iff_mem_nhds, hU.interior_eq]
end

/-- In a locally compact space every point has a compact neighborhood. -/
lemma exists_compact_mem_nhds [locally_compact_space α] (x : α) :
  ∃ K, is_compact K ∧ K ∈ 𝓝 x :=
let ⟨K, hKc, hx, H⟩ := exists_compact_subset is_open_univ (mem_univ x)
in ⟨K, hKc, mem_interior_iff_mem_nhds.1 hx⟩

lemma ultrafilter.le_nhds_Lim [compact_space α] (F : ultrafilter α) :
  ↑F ≤ 𝓝 (@Lim _ _ (F : filter α).nonempty_of_ne_bot F) :=
begin
  rcases compact_univ.ultrafilter_le_nhds F (by simp) with ⟨x, -, h⟩,
  exact le_nhds_Lim ⟨x,h⟩,
end

/-- A σ-compact space is a space that is the union of a countable collection of compact subspaces.
  Note that a locally compact separable T₂ space need not be σ-compact.
  The sequence can be extracted using `topological_space.compact_covering`. -/
class sigma_compact_space (α : Type*) [topological_space α] : Prop :=
(exists_compact_covering : ∃ K : ℕ → set α, (∀ n, is_compact (K n)) ∧ (⋃ n, K n) = univ)

@[priority 200] -- see Note [lower instance priority]
instance compact_space.sigma_compact [compact_space α] : sigma_compact_space α :=
⟨⟨λ _, univ, λ _, compact_univ, Union_const _⟩⟩

lemma sigma_compact_space.of_countable (S : set (set α)) (Hc : countable S)
  (Hcomp : ∀ s ∈ S, is_compact s) (HU : ⋃₀ S = univ) : sigma_compact_space α :=
⟨(exists_seq_cover_iff_countable ⟨_, compact_empty⟩).2 ⟨S, Hc, Hcomp, HU⟩⟩

lemma sigma_compact_space_of_locally_compact_second_countable [locally_compact_space α]
  [second_countable_topology α] : sigma_compact_space α :=
begin
  choose K hKc hxK h_ using λ x : α, exists_compact_subset is_open_univ (mem_univ x), clear h_,
  rcases countable_cover_nhds (λ x, mem_interior_iff_mem_nhds.1 (hxK x)) with ⟨s, hsc, hsU⟩,
  refine sigma_compact_space.of_countable _ (hsc.image K) (ball_image_iff.2 $ λ x _, hKc x) _,
  rwa sUnion_image
end

variables (α) [sigma_compact_space α]
open sigma_compact_space

/-- An arbitrary compact covering of a σ-compact space. -/
def compact_covering : ℕ → set α :=
classical.some exists_compact_covering

lemma is_compact_compact_covering (n : ℕ) : is_compact (compact_covering α n) :=
(classical.some_spec sigma_compact_space.exists_compact_covering).1 n

lemma Union_compact_covering : (⋃ n, compact_covering α n) = univ :=
(classical.some_spec sigma_compact_space.exists_compact_covering).2

end compact

section clopen

/-- A set is clopen if it is both open and closed. -/
def is_clopen (s : set α) : Prop :=
is_open s ∧ is_closed s

theorem is_clopen_union {s t : set α} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s ∪ t) :=
⟨is_open_union hs.1 ht.1, is_closed_union hs.2 ht.2⟩

theorem is_clopen_inter {s t : set α} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s ∩ t) :=
⟨is_open_inter hs.1 ht.1, is_closed_inter hs.2 ht.2⟩

@[simp] theorem is_clopen_empty : is_clopen (∅ : set α) :=
⟨is_open_empty, is_closed_empty⟩

@[simp] theorem is_clopen_univ : is_clopen (univ : set α) :=
⟨is_open_univ, is_closed_univ⟩

theorem is_clopen_compl {s : set α} (hs : is_clopen s) : is_clopen sᶜ :=
⟨hs.2, is_closed_compl_iff.2 hs.1⟩

@[simp] theorem is_clopen_compl_iff {s : set α} : is_clopen sᶜ ↔ is_clopen s :=
⟨λ h, compl_compl s ▸ is_clopen_compl h, is_clopen_compl⟩

theorem is_clopen_diff {s t : set α} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s \ t) :=
is_clopen_inter hs (is_clopen_compl ht)

lemma is_clopen_Inter {β : Type*} [fintype β] {s : β → set α}
  (h : ∀ i, is_clopen (s i)) : is_clopen (⋂ i, s i) :=
⟨(is_open_Inter (forall_and_distrib.1 h).1), (is_closed_Inter (forall_and_distrib.1 h).2)⟩

lemma is_clopen_bInter {β : Type*} {s : finset β} {f : β → set α} (h : ∀i∈s, is_clopen (f i)) :
  is_clopen (⋂i∈s, f i) :=
⟨ is_open_bInter ⟨finset_coe.fintype s⟩ (λ i hi, (h i hi).1),
  by {show is_closed (⋂ (i : β) (H : i ∈ (↑s : set β)), f i), rw bInter_eq_Inter,
    apply is_closed_Inter, rintro ⟨i, hi⟩, exact (h i hi).2}⟩

lemma continuous_on.preimage_clopen_of_clopen {β: Type*} [topological_space β]
  {f : α → β} {s : set α} {t : set β} (hf : continuous_on f s) (hs : is_clopen s)
  (ht : is_clopen t) : is_clopen (s ∩ f⁻¹' t) :=
⟨continuous_on.preimage_open_of_open hf hs.1 ht.1,
  continuous_on.preimage_closed_of_closed hf hs.2 ht.2⟩

/-- The intersection of a disjoint covering by two open sets of a clopen set will be clopen. -/
theorem is_clopen_inter_of_disjoint_cover_clopen {Z a b : set α} (h : is_clopen Z)
  (cover : Z ⊆ a ∪ b) (ha : is_open a) (hb : is_open b) (hab : a ∩ b = ∅) : is_clopen (Z ∩ a) :=
begin
  refine ⟨is_open_inter h.1 ha, _⟩,
  have : is_closed (Z ∩ bᶜ) := is_closed_inter h.2 (is_closed_compl_iff.2 hb),
  convert this using 1,
  apply subset.antisymm,
  { exact inter_subset_inter_right Z (subset_compl_iff_disjoint.2 hab) },
  { rintros x ⟨hx₁, hx₂⟩,
    exact ⟨hx₁, by simpa [not_mem_of_mem_compl hx₂] using cover hx₁⟩ }
end

end clopen

section preirreducible

/-- A preirreducible set `s` is one where there is no non-trivial pair of disjoint opens on `s`. -/
def is_preirreducible (s : set α) : Prop :=
∀ (u v : set α), is_open u → is_open v →
  (s ∩ u).nonempty → (s ∩ v).nonempty → (s ∩ (u ∩ v)).nonempty

/-- An irreducible set `s` is one that is nonempty and
where there is no non-trivial pair of disjoint opens on `s`. -/
def is_irreducible (s : set α) : Prop :=
s.nonempty ∧ is_preirreducible s

lemma is_irreducible.nonempty {s : set α} (h : is_irreducible s) :
  s.nonempty := h.1

lemma is_irreducible.is_preirreducible {s : set α} (h : is_irreducible s) :
  is_preirreducible s := h.2

theorem is_preirreducible_empty : is_preirreducible (∅ : set α) :=
λ _ _ _ _ _ ⟨x, h1, h2⟩, h1.elim

theorem is_irreducible_singleton {x} : is_irreducible ({x} : set α) :=
⟨singleton_nonempty x,
 λ u v _ _ ⟨y, h1, h2⟩ ⟨z, h3, h4⟩, by rw mem_singleton_iff at h1 h3;
 substs y z; exact ⟨x, rfl, h2, h4⟩⟩

theorem is_preirreducible.closure {s : set α} (H : is_preirreducible s) :
  is_preirreducible (closure s) :=
λ u v hu hv ⟨y, hycs, hyu⟩ ⟨z, hzcs, hzv⟩,
let ⟨p, hpu, hps⟩ := mem_closure_iff.1 hycs u hu hyu in
let ⟨q, hqv, hqs⟩ := mem_closure_iff.1 hzcs v hv hzv in
let ⟨r, hrs, hruv⟩ := H u v hu hv ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩ in
⟨r, subset_closure hrs, hruv⟩

lemma is_irreducible.closure {s : set α} (h : is_irreducible s) :
  is_irreducible (closure s) :=
⟨h.nonempty.closure, h.is_preirreducible.closure⟩

theorem exists_preirreducible (s : set α) (H : is_preirreducible s) :
  ∃ t : set α, is_preirreducible t ∧ s ⊆ t ∧ ∀ u, is_preirreducible u → t ⊆ u → u = t :=
let ⟨m, hm, hsm, hmm⟩ := zorn.zorn_subset₀ {t : set α | is_preirreducible t}
  (λ c hc hcc hcn, let ⟨t, htc⟩ := hcn in
    ⟨⋃₀ c, λ u v hu hv ⟨y, hy, hyu⟩ ⟨z, hz, hzv⟩,
      let ⟨p, hpc, hyp⟩ := mem_sUnion.1 hy,
          ⟨q, hqc, hzq⟩ := mem_sUnion.1 hz in
      or.cases_on (zorn.chain.total hcc hpc hqc)
        (assume hpq : p ⊆ q, let ⟨x, hxp, hxuv⟩ := hc hqc u v hu hv
            ⟨y, hpq hyp, hyu⟩ ⟨z, hzq, hzv⟩ in
          ⟨x, mem_sUnion_of_mem hxp hqc, hxuv⟩)
        (assume hqp : q ⊆ p, let ⟨x, hxp, hxuv⟩ := hc hpc u v hu hv
            ⟨y, hyp, hyu⟩ ⟨z, hqp hzq, hzv⟩ in
          ⟨x, mem_sUnion_of_mem hxp hpc, hxuv⟩),
    λ x hxc, subset_sUnion_of_mem hxc⟩) s H in
⟨m, hm, hsm, λ u hu hmu, hmm _ hu hmu⟩

/-- A maximal irreducible set that contains a given point. -/
def irreducible_component (x : α) : set α :=
classical.some (exists_preirreducible {x} is_irreducible_singleton.is_preirreducible)

lemma irreducible_component_property (x : α) :
  is_preirreducible (irreducible_component x) ∧ {x} ⊆ (irreducible_component x) ∧
  ∀ u, is_preirreducible u → (irreducible_component x) ⊆ u → u = (irreducible_component x) :=
classical.some_spec (exists_preirreducible {x} is_irreducible_singleton.is_preirreducible)

theorem mem_irreducible_component {x : α} : x ∈ irreducible_component x :=
singleton_subset_iff.1 (irreducible_component_property x).2.1

theorem is_irreducible_irreducible_component {x : α} : is_irreducible (irreducible_component x) :=
⟨⟨x, mem_irreducible_component⟩, (irreducible_component_property x).1⟩

theorem eq_irreducible_component {x : α} :
  ∀ {s : set α}, is_preirreducible s → irreducible_component x ⊆ s → s = irreducible_component x :=
(irreducible_component_property x).2.2

theorem is_closed_irreducible_component {x : α} :
  is_closed (irreducible_component x) :=
closure_eq_iff_is_closed.1 $ eq_irreducible_component
  is_irreducible_irreducible_component.is_preirreducible.closure
  subset_closure

/-- A preirreducible space is one where there is no non-trivial pair of disjoint opens. -/
class preirreducible_space (α : Type u) [topological_space α] : Prop :=
(is_preirreducible_univ [] : is_preirreducible (univ : set α))

/-- An irreducible space is one that is nonempty
and where there is no non-trivial pair of disjoint opens. -/
class irreducible_space (α : Type u) [topological_space α] extends preirreducible_space α : Prop :=
(to_nonempty [] : nonempty α)

attribute [instance, priority 50] irreducible_space.to_nonempty -- see Note [lower instance priority]

theorem nonempty_preirreducible_inter [preirreducible_space α] {s t : set α} :
  is_open s → is_open t → s.nonempty → t.nonempty → (s ∩ t).nonempty :=
by simpa only [univ_inter, univ_subset_iff] using
  @preirreducible_space.is_preirreducible_univ α _ _ s t

theorem is_preirreducible.image [topological_space β] {s : set α} (H : is_preirreducible s)
  (f : α → β) (hf : continuous_on f s) : is_preirreducible (f '' s) :=
begin
  rintros u v hu hv ⟨_, ⟨⟨x, hx, rfl⟩, hxu⟩⟩ ⟨_, ⟨⟨y, hy, rfl⟩, hyv⟩⟩,
  rw ← mem_preimage at hxu hyv,
  rcases continuous_on_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩,
  rcases continuous_on_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩,
  have := H u' v' hu' hv',
  rw [inter_comm s u', ← u'_eq] at this,
  rw [inter_comm s v', ← v'_eq] at this,
  rcases this ⟨x, hxu, hx⟩ ⟨y, hyv, hy⟩ with ⟨z, hzs, hzu', hzv'⟩,
  refine ⟨f z, mem_image_of_mem f hzs, _, _⟩,
  all_goals
  { rw ← mem_preimage,
    apply mem_of_mem_inter_left,
    show z ∈ _ ∩ s,
    simp [*] }
end

theorem is_irreducible.image [topological_space β] {s : set α} (H : is_irreducible s)
  (f : α → β) (hf : continuous_on f s) : is_irreducible (f '' s) :=
⟨nonempty_image_iff.mpr H.nonempty, H.is_preirreducible.image f hf⟩

lemma subtype.preirreducible_space {s : set α} (h : is_preirreducible s) :
  preirreducible_space s :=
{ is_preirreducible_univ :=
  begin
    intros u v hu hv hsu hsv,
    rw is_open_induced_iff at hu hv,
    rcases hu with ⟨u, hu, rfl⟩,
    rcases hv with ⟨v, hv, rfl⟩,
    rcases hsu with ⟨⟨x, hxs⟩, hxs', hxu⟩,
    rcases hsv with ⟨⟨y, hys⟩, hys', hyv⟩,
    rcases h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩ with ⟨z, hzs, ⟨hzu, hzv⟩⟩,
    exact ⟨⟨z, hzs⟩, ⟨set.mem_univ _, ⟨hzu, hzv⟩⟩⟩
  end }

lemma subtype.irreducible_space {s : set α} (h : is_irreducible s) :
  irreducible_space s :=
{ is_preirreducible_univ :=
  (subtype.preirreducible_space h.is_preirreducible).is_preirreducible_univ,
  to_nonempty := h.nonempty.to_subtype }

/-- A set `s` is irreducible if and only if
for every finite collection of open sets all of whose members intersect `s`,
`s` also intersects the intersection of the entire collection
(i.e., there is an element of `s` contained in every member of the collection). -/
lemma is_irreducible_iff_sInter {s : set α} :
  is_irreducible s ↔
  ∀ (U : finset (set α)) (hU : ∀ u ∈ U, is_open u) (H : ∀ u ∈ U, (s ∩ u).nonempty),
  (s ∩ ⋂₀ ↑U).nonempty :=
begin
  split; intro h,
  { intro U, apply finset.induction_on U,
    { intros, simpa using h.nonempty },
    { intros u U hu IH hU H,
      rw [finset.coe_insert, sInter_insert],
      apply h.2,
      { solve_by_elim [finset.mem_insert_self] },
      { apply is_open_sInter (finset.finite_to_set U),
        intros, solve_by_elim [finset.mem_insert_of_mem] },
      { solve_by_elim [finset.mem_insert_self] },
      { apply IH,
        all_goals { intros, solve_by_elim [finset.mem_insert_of_mem] } } } },
  { split,
    { simpa using h ∅ _ _; intro u; simp },
    intros u v hu hv hu' hv',
    simpa using h {u,v} _ _,
    all_goals
    { intro t,
      rw [finset.mem_insert, finset.mem_singleton],
      rintro (rfl|rfl); assumption } }
end

/-- A set is preirreducible if and only if
for every cover by two closed sets, it is contained in one of the two covering sets. -/
lemma is_preirreducible_iff_closed_union_closed {s : set α} :
  is_preirreducible s ↔
  ∀ (z₁ z₂ : set α), is_closed z₁ → is_closed z₂ → s ⊆ z₁ ∪ z₂ → s ⊆ z₁ ∨ s ⊆ z₂ :=
begin
  split,
  all_goals
  { intros h t₁ t₂ ht₁ ht₂,
    specialize h t₁ᶜ t₂ᶜ,
    simp only [is_open_compl_iff, is_closed_compl_iff] at h,
    specialize h ht₁ ht₂ },
  { contrapose!, simp only [not_subset],
    rintro ⟨⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩,
    rcases h ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩ with ⟨z, hz, hz'⟩,
    rw ← compl_union at hz',
    exact ⟨z, hz, hz'⟩ },
  { rintro ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩,
    rw ← compl_inter at h,
    delta set.nonempty,
    rw imp_iff_not_or at h,
    contrapose! h,
    split,
    { intros z hz hz', exact h z ⟨hz, hz'⟩ },
    { split; intro H; refine H _ ‹_›; assumption } }
end

/-- A set is irreducible if and only if
for every cover by a finite collection of closed sets,
it is contained in one of the members of the collection. -/
lemma is_irreducible_iff_sUnion_closed {s : set α} :
  is_irreducible s ↔
  ∀ (Z : finset (set α)) (hZ : ∀ z ∈ Z, is_closed z) (H : s ⊆ ⋃₀ ↑Z),
  ∃ z ∈ Z, s ⊆ z :=
begin
  rw [is_irreducible, is_preirreducible_iff_closed_union_closed],
  split; intro h,
  { intro Z, apply finset.induction_on Z,
    { intros, rw [finset.coe_empty, sUnion_empty] at H,
      rcases h.1 with ⟨x, hx⟩,
      exfalso, tauto },
    { intros z Z hz IH hZ H,
      cases h.2 z (⋃₀ ↑Z) _ _ _
        with h' h',
      { exact ⟨z, finset.mem_insert_self _ _, h'⟩ },
      { rcases IH _ h' with ⟨z', hz', hsz'⟩,
        { exact ⟨z', finset.mem_insert_of_mem hz', hsz'⟩ },
        { intros, solve_by_elim [finset.mem_insert_of_mem] } },
      { solve_by_elim [finset.mem_insert_self] },
      { rw sUnion_eq_bUnion,
        apply is_closed_bUnion (finset.finite_to_set Z),
        { intros, solve_by_elim [finset.mem_insert_of_mem] } },
      { simpa using H } } },
  { split,
    { by_contradiction hs,
      simpa using h ∅ _ _,
      { intro z, simp },
      { simpa [set.nonempty] using hs } },
    intros z₁ z₂ hz₁ hz₂ H,
    have := h {z₁, z₂} _ _,
    simp only [exists_prop, finset.mem_insert, finset.mem_singleton] at this,
    { rcases this with ⟨z, rfl|rfl, hz⟩; tauto },
    { intro t,
      rw [finset.mem_insert, finset.mem_singleton],
      rintro (rfl|rfl); assumption },
    { simpa using H } }
end

end preirreducible
