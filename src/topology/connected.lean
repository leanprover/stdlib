/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import topology.subset_properties

/-!
# Connected subsets of topological spaces

In this file we define connected subsets of a topological spaces and various other properties and
classes related to connectivity.

## Main definitions

We define the following properties for sets in a topological space:

* `is_connected`: a nonempty set that has no non-trivial open partition.
  See also the section below in the module doc.
* `connected_component` is the connected component of an element in the space.
* `is_totally_disconnected`: all of its connected components are singletons.
* `is_totally_separated`: any two points can be separated by two disjoint opens that cover the set.

For each of these definitions, we also have a class stating that the whole space
satisfies that property:
`connected_space`, `totally_disconnected_space`, `totally_separated_space`.

## On the definition of connected sets/spaces

In informal mathematics, connected spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `is_preconnected`.
In other words, the only difference is whether the empty space counts as connected.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.
-/

open set classical topological_space
open_locale classical topological_space

universes u v
variables {α : Type u} {β : Type v} [topological_space α] {s t : set α}

section preconnected

/-- A preconnected set is one where there is no non-trivial open partition. -/
def is_preconnected (s : set α) : Prop :=
∀ (u v : set α), is_open u → is_open v → s ⊆ u ∪ v →
  (s ∩ u).nonempty → (s ∩ v).nonempty → (s ∩ (u ∩ v)).nonempty

/-- A connected set is one that is nonempty and where there is no non-trivial open partition. -/
def is_connected (s : set α) : Prop :=
s.nonempty ∧ is_preconnected s

lemma is_connected.nonempty {s : set α} (h : is_connected s) :
  s.nonempty := h.1

lemma is_connected.is_preconnected {s : set α} (h : is_connected s) :
  is_preconnected s := h.2

theorem is_preirreducible.is_preconnected {s : set α} (H : is_preirreducible s) :
  is_preconnected s :=
λ _ _ hu hv _, H _ _ hu hv

theorem is_irreducible.is_connected {s : set α} (H : is_irreducible s) : is_connected s :=
⟨H.nonempty, H.is_preirreducible.is_preconnected⟩

theorem is_preconnected_empty : is_preconnected (∅ : set α) :=
is_preirreducible_empty.is_preconnected

theorem is_connected_singleton {x} : is_connected ({x} : set α) :=
is_irreducible_singleton.is_connected

/-- If any point of a set is joined to a fixed point by a preconnected subset,
then the original set is preconnected as well. -/
theorem is_preconnected_of_forall {s : set α} (x : α)
  (H : ∀ y ∈ s, ∃ t ⊆ s, x ∈ t ∧ y ∈ t ∧ is_preconnected t) :
  is_preconnected s :=
begin
  rintros u v hu hv hs ⟨z, zs, zu⟩ ⟨y, ys, yv⟩,
  have xs : x ∈ s, by { rcases H y ys with ⟨t, ts, xt, yt, ht⟩, exact ts xt },
  wlog xu : x ∈ u := hs xs using [u v y z, v u z y],
  rcases H y ys with ⟨t, ts, xt, yt, ht⟩,
  have := ht u v hu hv(subset.trans ts hs) ⟨x, xt, xu⟩ ⟨y, yt, yv⟩,
  exact this.imp (λ z hz, ⟨ts hz.1, hz.2⟩)
end

/-- If any two points of a set are contained in a preconnected subset,
then the original set is preconnected as well. -/
theorem is_preconnected_of_forall_pair {s : set α}
  (H : ∀ x y ∈ s, ∃ t ⊆ s, x ∈ t ∧ y ∈ t ∧ is_preconnected t) :
  is_preconnected s :=
begin
  rintros u v hu hv hs ⟨x, xs, xu⟩ ⟨y, ys, yv⟩,
  rcases H x y xs ys with ⟨t, ts, xt, yt, ht⟩,
  have := ht u v hu hv(subset.trans ts hs) ⟨x, xt, xu⟩ ⟨y, yt, yv⟩,
  exact this.imp (λ z hz, ⟨ts hz.1, hz.2⟩)
end

/-- A union of a family of preconnected sets with a common point is preconnected as well. -/
theorem is_preconnected_sUnion (x : α) (c : set (set α)) (H1 : ∀ s ∈ c, x ∈ s)
  (H2 : ∀ s ∈ c, is_preconnected s) : is_preconnected (⋃₀ c) :=
begin
  apply is_preconnected_of_forall x,
  rintros y ⟨s, sc, ys⟩,
  exact ⟨s, subset_sUnion_of_mem sc, H1 s sc, ys, H2 s sc⟩
end

theorem is_preconnected.union (x : α) {s t : set α} (H1 : x ∈ s) (H2 : x ∈ t)
  (H3 : is_preconnected s) (H4 : is_preconnected t) : is_preconnected (s ∪ t) :=
sUnion_pair s t ▸ is_preconnected_sUnion x {s, t}
  (by rintro r (rfl | rfl | h); assumption)
  (by rintro r (rfl | rfl | h); assumption)

theorem is_connected.union {s t : set α} (H : (s ∩ t).nonempty)
  (Hs : is_connected s) (Ht : is_connected t) : is_connected (s ∪ t) :=
begin
  rcases H with ⟨x, hx⟩,
  refine ⟨⟨x, mem_union_left t (mem_of_mem_inter_left hx)⟩, _⟩,
  exact is_preconnected.union x (mem_of_mem_inter_left hx) (mem_of_mem_inter_right hx)
    Hs.is_preconnected Ht.is_preconnected
end

theorem is_preconnected.closure {s : set α} (H : is_preconnected s) :
  is_preconnected (closure s) :=
λ u v hu hv hcsuv ⟨y, hycs, hyu⟩ ⟨z, hzcs, hzv⟩,
let ⟨p, hpu, hps⟩ := mem_closure_iff.1 hycs u hu hyu in
let ⟨q, hqv, hqs⟩ := mem_closure_iff.1 hzcs v hv hzv in
let ⟨r, hrs, hruv⟩ := H u v hu hv (subset.trans subset_closure hcsuv) ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩ in
⟨r, subset_closure hrs, hruv⟩

theorem is_connected.closure {s : set α} (H : is_connected s) :
  is_connected (closure s) :=
⟨H.nonempty.closure, H.is_preconnected.closure⟩

theorem is_preconnected.image [topological_space β] {s : set α} (H : is_preconnected s)
  (f : α → β) (hf : continuous_on f s) : is_preconnected (f '' s) :=
begin
  -- Unfold/destruct definitions in hypotheses
  rintros u v hu hv huv ⟨_, ⟨x, xs, rfl⟩, xu⟩ ⟨_, ⟨y, ys, rfl⟩, yv⟩,
  rcases continuous_on_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩,
  rcases continuous_on_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩,
  -- Reformulate `huv : f '' s ⊆ u ∪ v` in terms of `u'` and `v'`
  replace huv : s ⊆ u' ∪ v',
  { rw [image_subset_iff, preimage_union] at huv,
    replace huv := subset_inter huv (subset.refl _),
    rw [inter_distrib_right, u'_eq, v'_eq, ← inter_distrib_right] at huv,
    exact (subset_inter_iff.1 huv).1 },
  -- Now `s ⊆ u' ∪ v'`, so we can apply `‹is_preconnected s›`
  obtain ⟨z, hz⟩ : (s ∩ (u' ∩ v')).nonempty,
  { refine H u' v' hu' hv' huv ⟨x, _⟩ ⟨y, _⟩; rw inter_comm,
    exacts [u'_eq ▸ ⟨xu, xs⟩, v'_eq ▸ ⟨yv, ys⟩] },
  rw [← inter_self s, inter_assoc, inter_left_comm s u', ← inter_assoc,
    inter_comm s, inter_comm s, ← u'_eq, ← v'_eq] at hz,
  exact ⟨f z, ⟨z, hz.1.2, rfl⟩, hz.1.1, hz.2.1⟩
end

theorem is_connected.image [topological_space β] {s : set α} (H : is_connected s)
  (f : α → β) (hf : continuous_on f s) : is_connected (f '' s) :=
⟨nonempty_image_iff.mpr H.nonempty, H.is_preconnected.image f hf⟩

theorem is_preconnected_closed_iff {s : set α} :
  is_preconnected s ↔ ∀ t t', is_closed t → is_closed t' → s ⊆ t ∪ t' →
    (s ∩ t).nonempty → (s ∩ t').nonempty → (s ∩ (t ∩ t')).nonempty :=
⟨begin
  rintros h t t' ht ht' htt' ⟨x, xs, xt⟩ ⟨y, ys, yt'⟩,
  by_contradiction h',
  rw [← ne_empty_iff_nonempty, ne.def, not_not, ← subset_compl_iff_disjoint, compl_inter] at h',
  have xt' : x ∉ t', from (h' xs).elim (absurd xt) id,
  have yt : y ∉ t, from (h' ys).elim id (absurd yt'),
  have := ne_empty_iff_nonempty.2 (h tᶜ t'ᶜ (is_open_compl_iff.2 ht)
    (is_open_compl_iff.2 ht') h' ⟨y, ys, yt⟩ ⟨x, xs, xt'⟩),
  rw [ne.def, ← compl_union, ← subset_compl_iff_disjoint, compl_compl] at this,
  contradiction
end,
begin
  rintros h u v hu hv huv ⟨x, xs, xu⟩ ⟨y, ys, yv⟩,
  by_contradiction h',
  rw [← ne_empty_iff_nonempty, ne.def, not_not,
    ← subset_compl_iff_disjoint, compl_inter] at h',
  have xv : x ∉ v, from (h' xs).elim (absurd xu) id,
  have yu : y ∉ u, from (h' ys).elim id (absurd yv),
  have := ne_empty_iff_nonempty.2 (h uᶜ vᶜ (is_closed_compl_iff.2 hu)
    (is_closed_compl_iff.2 hv) h' ⟨y, ys, yu⟩ ⟨x, xs, xv⟩),
  rw [ne.def, ← compl_union, ← subset_compl_iff_disjoint, compl_compl] at this,
  contradiction
end⟩

/-- The connected component of a point is the maximal connected set
that contains this point. -/
def connected_component (x : α) : set α :=
⋃₀ { s : set α | is_preconnected s ∧ x ∈ s }

/-- The connected component of a point inside a set. -/
def connected_component_in (F : set α) (x : F) : set α := coe '' (connected_component x)

theorem mem_connected_component {x : α} : x ∈ connected_component x :=
mem_sUnion_of_mem (mem_singleton x) ⟨is_connected_singleton.is_preconnected, mem_singleton x⟩

theorem is_preconnected_connected_component {x : α} : is_preconnected (connected_component x) :=
is_preconnected_sUnion x _ (λ _, and.right) (λ _, and.left)

theorem is_connected_connected_component {x : α} : is_connected (connected_component x) :=
⟨⟨x, mem_connected_component⟩, is_preconnected_connected_component⟩

theorem is_preconnected.subset_connected_component {x : α} {s : set α}
  (H1 : is_preconnected s) (H2 : x ∈ s) : s ⊆ connected_component x :=
λ z hz, mem_sUnion_of_mem hz ⟨H1, H2⟩

theorem is_connected.subset_connected_component {x : α} {s : set α}
  (H1 : is_connected s) (H2 : x ∈ s) : s ⊆ connected_component x :=
H1.2.subset_connected_component H2

theorem connected_component_eq {x y : α} (h : y ∈ connected_component x) :
  connected_component x = connected_component y :=
eq_of_subset_of_subset
  (is_connected_connected_component.subset_connected_component h)
  (is_connected_connected_component.subset_connected_component
    (set.mem_of_mem_of_subset mem_connected_component
      (is_connected_connected_component.subset_connected_component h)))

lemma connected_component_disjoint {x y : α} (h : connected_component x ≠ connected_component y) :
  disjoint (connected_component x) (connected_component y) :=
set.disjoint_left.2 (λ a h1 h2, h
  ((connected_component_eq h1).trans (connected_component_eq h2).symm))

theorem is_closed_connected_component {x : α} :
  is_closed (connected_component x) :=
closure_eq_iff_is_closed.1 $ subset.antisymm
  (is_connected_connected_component.closure.subset_connected_component
    (subset_closure mem_connected_component))
  subset_closure

lemma continuous.image_connected_component_subset {β : Type*} [topological_space β] {f : α → β}
  (h : continuous f) (a : α) : f '' connected_component a ⊆ connected_component (f a) :=
(is_connected_connected_component.image f h.continuous_on).subset_connected_component
  ((mem_image f (connected_component a) (f a)).2 ⟨a, mem_connected_component, rfl⟩)

theorem irreducible_component_subset_connected_component {x : α} :
  irreducible_component x ⊆ connected_component x :=
is_irreducible_irreducible_component.is_connected.subset_connected_component
  mem_irreducible_component

/-- A preconnected space is one where there is no non-trivial open partition. -/
class preconnected_space (α : Type u) [topological_space α] : Prop :=
(is_preconnected_univ : is_preconnected (univ : set α))

export preconnected_space (is_preconnected_univ)

/-- A connected space is a nonempty one where there is no non-trivial open partition. -/
class connected_space (α : Type u) [topological_space α] extends preconnected_space α : Prop :=
(to_nonempty : nonempty α)

attribute [instance, priority 50] connected_space.to_nonempty -- see Note [lower instance priority]

lemma connected_space.is_connected_univ [connected_space α] :
  is_connected (univ : set α) := ⟨univ_nonempty, is_preconnected_univ⟩

lemma is_connected_range [topological_space β] [connected_space α] {f : α → β} (h : continuous f) :
  is_connected (range f) :=
begin
  inhabit α,
  rw ← image_univ,
  exact ⟨⟨f (default α), mem_image_of_mem _ (mem_univ _)⟩,
         is_preconnected.image is_preconnected_univ _ h.continuous_on⟩
end

lemma connected_space_iff_connected_component :
  connected_space α ↔ ∃ x : α, connected_component x = univ :=
begin
  split,
  { rintros ⟨h, ⟨x⟩⟩,
    exactI ⟨x, eq_univ_of_univ_subset $
      is_preconnected_univ.subset_connected_component (mem_univ x)⟩ },
  { rintros ⟨x, h⟩,
    haveI : preconnected_space α := ⟨by { rw ← h, exact is_preconnected_connected_component }⟩,
    exact ⟨⟨x⟩⟩ }
end

@[priority 100] -- see Note [lower instance priority]
instance preirreducible_space.preconnected_space (α : Type u) [topological_space α]
  [preirreducible_space α] : preconnected_space α :=
⟨(preirreducible_space.is_preirreducible_univ α).is_preconnected⟩

@[priority 100] -- see Note [lower instance priority]
instance irreducible_space.connected_space (α : Type u) [topological_space α]
  [irreducible_space α] : connected_space α :=
{ to_nonempty := irreducible_space.to_nonempty α }

theorem nonempty_inter [preconnected_space α] {s t : set α} :
  is_open s → is_open t → s ∪ t = univ → s.nonempty → t.nonempty → (s ∩ t).nonempty :=
by simpa only [univ_inter, univ_subset_iff] using
  @preconnected_space.is_preconnected_univ α _ _ s t

theorem is_clopen_iff [preconnected_space α] {s : set α} : is_clopen s ↔ s = ∅ ∨ s = univ :=
⟨λ hs, classical.by_contradiction $ λ h,
  have h1 : s ≠ ∅ ∧ sᶜ ≠ ∅, from ⟨mt or.inl h,
    mt (λ h2, or.inr $ (by rw [← compl_compl s, h2, compl_empty] : s = univ)) h⟩,
  let ⟨_, h2, h3⟩ := nonempty_inter hs.1 hs.2.is_open_compl (union_compl_self s)
    (ne_empty_iff_nonempty.1 h1.1) (ne_empty_iff_nonempty.1 h1.2) in
  h3 h2,
by rintro (rfl | rfl); [exact is_clopen_empty, exact is_clopen_univ]⟩

lemma eq_univ_of_nonempty_clopen [preconnected_space α] {s : set α}
  (h : s.nonempty) (h' : is_clopen s) : s = univ :=
by { rw is_clopen_iff at h', finish [h.ne_empty] }

lemma subtype.preconnected_space {s : set α} (h : is_preconnected s) :
  preconnected_space s :=
{ is_preconnected_univ :=
  begin
    intros u v hu hv hs hsu hsv,
    rw is_open_induced_iff at hu hv,
    rcases hu with ⟨u, hu, rfl⟩,
    rcases hv with ⟨v, hv, rfl⟩,
    rcases hsu with ⟨⟨x, hxs⟩, hxs', hxu⟩,
    rcases hsv with ⟨⟨y, hys⟩, hys', hyv⟩,
    rcases h u v hu hv _ ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩ with ⟨z, hzs, ⟨hzu, hzv⟩⟩,
    exact ⟨⟨z, hzs⟩, ⟨set.mem_univ _, ⟨hzu, hzv⟩⟩⟩,
    intros z hz,
    rcases hs (mem_univ ⟨z, hz⟩) with hzu|hzv,
    { left, assumption },
    { right, assumption }
  end }

lemma subtype.connected_space {s : set α} (h : is_connected s) :
  connected_space s :=
{ is_preconnected_univ :=
  (subtype.preconnected_space h.is_preconnected).is_preconnected_univ,
  to_nonempty := h.nonempty.to_subtype }

lemma is_preconnected_iff_preconnected_space {s : set α} :
  is_preconnected s ↔ preconnected_space s :=
⟨subtype.preconnected_space,
 begin
   introI,
   simpa using is_preconnected_univ.image (coe : s → α) continuous_subtype_coe.continuous_on
 end⟩

lemma is_connected_iff_connected_space {s : set α} : is_connected s ↔ connected_space s :=
⟨subtype.connected_space,
 λ h, ⟨nonempty_subtype.mp h.2, is_preconnected_iff_preconnected_space.mpr h.1⟩⟩

/-- A set `s` is preconnected if and only if
for every cover by two open sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
lemma is_preconnected_iff_subset_of_disjoint {s : set α} :
  is_preconnected s ↔
  ∀ (u v : set α) (hu : is_open u) (hv : is_open v) (hs : s ⊆ u ∪ v) (huv : s ∩ (u ∩ v) = ∅),
  s ⊆ u ∨ s ⊆ v :=
begin
  split; intro h,
  { intros u v hu hv hs huv,
    specialize h u v hu hv hs,
    contrapose! huv,
    rw ne_empty_iff_nonempty,
    simp [not_subset] at huv,
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩,
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu,
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv,
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩ },
  { intros u v hu hv hs hsu hsv,
    rw ← ne_empty_iff_nonempty,
    intro H,
    specialize h u v hu hv hs H,
    contrapose H,
    apply ne_empty_iff_nonempty.mpr,
    cases h,
    { rcases hsv with ⟨x, hxs, hxv⟩, exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩ },
    { rcases hsu with ⟨x, hxs, hxu⟩, exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩ } }
end

/-- A set `s` is connected if and only if
for every cover by a finite collection of open sets that are pairwise disjoint on `s`,
it is contained in one of the members of the collection. -/
lemma is_connected_iff_sUnion_disjoint_open {s : set α} :
  is_connected s ↔
  ∀ (U : finset (set α)) (H : ∀ (u v : set α), u ∈ U → v ∈ U → (s ∩ (u ∩ v)).nonempty → u = v)
  (hU : ∀ u ∈ U, is_open u) (hs : s ⊆ ⋃₀ ↑U),
  ∃ u ∈ U, s ⊆ u :=
begin
  rw [is_connected, is_preconnected_iff_subset_of_disjoint],
  split; intro h,
  { intro U, apply finset.induction_on U,
    { rcases h.left,
      suffices : s ⊆ ∅ → false, { simpa },
      intro, solve_by_elim },
    { intros u U hu IH hs hU H,
      rw [finset.coe_insert, sUnion_insert] at H,
      cases h.2 u (⋃₀ ↑U) _ _ H _ with hsu hsU,
      { exact ⟨u, finset.mem_insert_self _ _, hsu⟩ },
      { rcases IH _ _ hsU with ⟨v, hvU, hsv⟩,
        { exact ⟨v, finset.mem_insert_of_mem hvU, hsv⟩ },
        { intros, apply hs; solve_by_elim [finset.mem_insert_of_mem] },
        { intros, solve_by_elim [finset.mem_insert_of_mem] } },
      { solve_by_elim [finset.mem_insert_self] },
      { apply is_open_sUnion,
        intros, solve_by_elim [finset.mem_insert_of_mem] },
      { apply eq_empty_of_subset_empty,
        rintro x ⟨hxs, hxu, hxU⟩,
        rw mem_sUnion at hxU,
        rcases hxU with ⟨v, hvU, hxv⟩,
        rcases hs u v (finset.mem_insert_self _ _) (finset.mem_insert_of_mem hvU) _ with rfl,
        { contradiction },
        { exact ⟨x, hxs, hxu, hxv⟩ } } } },
  { split,
    { rw ← ne_empty_iff_nonempty,
      by_contradiction hs, push_neg at hs, subst hs,
      simpa using h ∅ _ _ _; simp },
    intros u v hu hv hs hsuv,
    rcases h {u, v} _ _ _ with ⟨t, ht, ht'⟩,
    { rw [finset.mem_insert, finset.mem_singleton] at ht,
      rcases ht with rfl|rfl; tauto },
    { intros t₁ t₂ ht₁ ht₂ hst,
      rw ← ne_empty_iff_nonempty at hst,
      rw [finset.mem_insert, finset.mem_singleton] at ht₁ ht₂,
      rcases ht₁ with rfl|rfl; rcases ht₂ with rfl|rfl,
      all_goals { refl <|> contradiction <|> skip },
      rw inter_comm t₁ at hst, contradiction },
    { intro t,
      rw [finset.mem_insert, finset.mem_singleton],
      rintro (rfl|rfl); assumption },
    { simpa using hs } }
end

/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
theorem subset_or_disjoint_of_clopen {α : Type*} [topological_space α] {s t : set α}
  (h : is_preconnected t) (h1 : is_clopen s) : s ∩ t = ∅ ∨ t ⊆ s :=
begin
  by_contradiction h2,
  have h3 : (s ∩ t).nonempty := ne_empty_iff_nonempty.mp (mt or.inl h2),
  have h4 : (t ∩ sᶜ).nonempty,
  { apply inter_compl_nonempty_iff.2,
    push_neg at h2,
    exact h2.2 },
  rw [inter_comm] at h3,
  apply ne_empty_iff_nonempty.2 (h s sᶜ h1.1 (is_open_compl_iff.2 h1.2) _ h3 h4),
  { rw [inter_compl_self, inter_empty] },
  { rw [union_compl_self],
    exact subset_univ t },
end

/-- A set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
theorem is_preconnected_iff_subset_of_disjoint_closed {α : Type*} {s : set α}
  [topological_space α] :
  is_preconnected s ↔
    ∀ (u v : set α) (hu : is_closed u) (hv : is_closed v) (hs : s ⊆ u ∪ v) (huv : s ∩ (u ∩ v) = ∅),
      s ⊆ u ∨ s ⊆ v :=
begin
  split; intro h,
  { intros u v hu hv hs huv,
    rw is_preconnected_closed_iff at h,
    specialize h u v hu hv hs,
    contrapose! huv,
    rw ne_empty_iff_nonempty,
    simp [not_subset] at huv,
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩,
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu,
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv,
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩ },
  { rw is_preconnected_closed_iff,
    intros u v hu hv hs hsu hsv,
    rw ← ne_empty_iff_nonempty,
    intro H,
    specialize h u v hu hv hs H,
    contrapose H,
    apply ne_empty_iff_nonempty.mpr,
    cases h,
    { rcases hsv with ⟨x, hxs, hxv⟩, exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩ },
    { rcases hsu with ⟨x, hxs, hxu⟩, exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩ } }
end

/-- A closed set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint,
it is contained in one of the two covering sets. -/
theorem is_preconnected_iff_subset_of_fully_disjoint_closed {s : set α} (hs : is_closed s) :
  is_preconnected s ↔
  ∀ (u v : set α) (hu : is_closed u) (hv : is_closed v) (hss : s ⊆ u ∪ v) (huv : u ∩ v = ∅),
  s ⊆ u ∨ s ⊆ v :=
begin
  split,
  { intros h u v hu hv hss huv,
    apply is_preconnected_iff_subset_of_disjoint_closed.1 h u v hu hv hss,
    rw huv,
    exact inter_empty s },
  intro H,
  rw is_preconnected_iff_subset_of_disjoint_closed,
  intros u v hu hv hss huv,
  have H1 := H (u ∩ s) (v ∩ s),
  rw [subset_inter_iff, subset_inter_iff] at H1,
  simp only [subset.refl, and_true] at H1,
  apply H1 (is_closed.inter hu hs) (is_closed.inter hv hs),
  { rw ←inter_distrib_right,
    apply subset_inter_iff.2,
    exact ⟨hss, subset.refl s⟩ },
  { rw [inter_comm v s, inter_assoc, ←inter_assoc s, inter_self s,
        inter_comm, inter_assoc, inter_comm v u, huv] }
end

/-- The connected component of a point is always a subset of the intersection of all its clopen
neighbourhoods. -/
lemma connected_component_subset_Inter_clopen {x : α} :
  connected_component x ⊆ ⋂ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, Z :=
begin
  apply subset_Inter (λ Z, _),
  cases (subset_or_disjoint_of_clopen (@is_connected_connected_component _ _ x).2 Z.2.1),
  { exfalso,
    apply nonempty.ne_empty
      (nonempty_of_mem (mem_inter (@mem_connected_component _ _ x) Z.2.2)),
    rw inter_comm,
    exact h  },
  exact h,
end

/-- A clopen set is the union of its connected components. -/
lemma is_clopen.eq_union_connected_components {Z : set α} (h : is_clopen Z) :
  Z = (⋃ (x : α) (H : x ∈ Z), connected_component x) :=
eq_of_subset_of_subset (λ x xZ, mem_Union.2 ⟨x, mem_Union.2 ⟨xZ, mem_connected_component⟩⟩)
  (Union_subset $ λ x, Union_subset $ λ xZ,
    (by { apply subset.trans connected_component_subset_Inter_clopen
      (Inter_subset _ ⟨Z, ⟨h, xZ⟩⟩) }))

/-- The preimage of a connected component is preconnected if the function has connected fibers
and a subset is closed iff the preimage is. -/
lemma preimage_connected_component_connected {β : Type*} [topological_space β] {f : α → β}
  (connected_fibers : ∀ t : β, is_connected (f ⁻¹' {t}))
  (hcl : ∀ (T : set β), is_closed T ↔ is_closed (f ⁻¹' T)) (t : β) :
  is_connected (f ⁻¹' connected_component t) :=
begin
  -- The following proof is essentially https://stacks.math.columbia.edu/tag/0377
  -- although the statement is slightly different
  have hf : function.surjective f := function.surjective.of_comp (λ t : β, (connected_fibers t).1),

  split,
  { cases hf t with s hs,
    use s,
    rw [mem_preimage, hs],
    exact mem_connected_component },

  have hT : is_closed (f ⁻¹' connected_component t) :=
    (hcl (connected_component t)).1 is_closed_connected_component,

  -- To show it's preconnected we decompose (f ⁻¹' connected_component t) as a subset of two
  -- closed disjoint sets in α. We want to show that it's a subset of either.
  rw is_preconnected_iff_subset_of_fully_disjoint_closed hT,
  intros u v hu hv huv uv_disj,

  -- To do this we decompose connected_component t into T₁ and T₂
  -- we will show that connected_component t is a subset of either and hence
  -- (f ⁻¹' connected_component t) is a subset of u or v
  let T₁ := {t' ∈ connected_component t | f ⁻¹' {t'} ⊆ u},
  let T₂ := {t' ∈ connected_component t | f ⁻¹' {t'} ⊆ v},

  have fiber_decomp : ∀ t' ∈ connected_component t, f ⁻¹' {t'} ⊆ u ∨ f ⁻¹' {t'} ⊆ v,
  { intros t' ht',
    apply is_preconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv,
    { exact subset.trans (hf.preimage_subset_preimage_iff.2 (singleton_subset_iff.2 ht')) huv },
    rw uv_disj,
    exact inter_empty _ },

  have T₁_u : f ⁻¹' T₁ = (f ⁻¹' connected_component t) ∩ u,
  { apply eq_of_subset_of_subset,
    { rw ←bUnion_preimage_singleton,
      refine bUnion_subset (λ t' ht', subset_inter _ ht'.2),
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff],
      exact ht'.1 },
    rintros a ⟨hat, hau⟩,
    constructor,
    { exact mem_preimage.1 hat },
    dsimp only,
    cases fiber_decomp (f a) (mem_preimage.1 hat),
    { exact h },
    { exfalso,
      rw ←not_nonempty_iff_eq_empty at uv_disj,
      exact uv_disj (nonempty_of_mem (mem_inter hau (h rfl))) } },
  -- This proof is exactly the same as the above (modulo some symmetry)
  have T₂_v : f ⁻¹' T₂ = (f ⁻¹' connected_component t) ∩ v,
  { apply eq_of_subset_of_subset,
    { rw ←bUnion_preimage_singleton,
      refine bUnion_subset (λ t' ht', subset_inter _ ht'.2),
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff],
      exact ht'.1 },
    rintros a ⟨hat, hav⟩,
    constructor,
    { exact mem_preimage.1 hat },
    dsimp only,
    cases fiber_decomp (f a) (mem_preimage.1 hat),
    { exfalso,
      rw ←not_nonempty_iff_eq_empty at uv_disj,
      exact uv_disj (nonempty_of_mem (mem_inter (h rfl) hav)) },
    { exact h } },

  -- Now we show T₁, T₂ are closed, cover connected_component t and are disjoint.
  have hT₁ : is_closed T₁ := ((hcl T₁).2 (T₁_u.symm ▸ (is_closed.inter hT hu))),
  have hT₂ : is_closed T₂ := ((hcl T₂).2 (T₂_v.symm ▸ (is_closed.inter hT hv))),

  have T_decomp : connected_component t ⊆ T₁ ∪ T₂,
  { intros t' ht',
    rw mem_union t' T₁ T₂,
    cases fiber_decomp t' ht' with htu htv,
    { left, exact ⟨ht', htu⟩ },
    right, exact ⟨ht', htv⟩ },

  have T_disjoint : T₁ ∩ T₂ = ∅,
  { rw ←image_preimage_eq (T₁ ∩ T₂) hf,
    suffices : f ⁻¹' (T₁ ∩ T₂) = ∅,
    { rw this, exact image_empty _ },
    rw [preimage_inter, T₁_u, T₂_v],
    rw inter_comm at uv_disj,
    conv
    { congr,
      rw [inter_assoc],
      congr, skip,
      rw [←inter_assoc, inter_comm, ←inter_assoc, uv_disj, empty_inter], },
    exact inter_empty _ },

  -- Now we do cases on whether (connected_component t) is a subset of T₁ or T₂ to show
  -- that the preimage is a subset of u or v.
  cases (is_preconnected_iff_subset_of_fully_disjoint_closed is_closed_connected_component).1
    is_preconnected_connected_component T₁ T₂ hT₁ hT₂ T_decomp T_disjoint,
  { left,
    rw subset.antisymm_iff at T₁_u,
    suffices : f ⁻¹' connected_component t ⊆ f ⁻¹' T₁,
    { exact subset.trans (subset.trans this T₁_u.1) (inter_subset_right _ _) },
    exact preimage_mono h },
  right,
  rw subset.antisymm_iff at T₂_v,
  suffices : f ⁻¹' connected_component t ⊆ f ⁻¹' T₂,
  { exact subset.trans (subset.trans this T₂_v.1) (inter_subset_right _ _) },
  exact preimage_mono h,
end

end preconnected

section totally_disconnected

/-- A set `s` is called totally disconnected if every subset `t ⊆ s` which is preconnected is
a subsingleton, ie either empty or a singleton.-/
def is_totally_disconnected (s : set α) : Prop :=
∀ t, t ⊆ s → is_preconnected t → t.subsingleton

theorem is_totally_disconnected_empty : is_totally_disconnected (∅ : set α) :=
λ _ ht _ _ x_in _ _, (ht x_in).elim

theorem is_totally_disconnected_singleton {x} : is_totally_disconnected ({x} : set α) :=
λ _ ht _, subsingleton.mono subsingleton_singleton ht

/-- A space is totally disconnected if all of its connected components are singletons. -/
class totally_disconnected_space (α : Type u) [topological_space α] : Prop :=
(is_totally_disconnected_univ : is_totally_disconnected (univ : set α))

lemma is_preconnected.subsingleton [totally_disconnected_space α]
  {s : set α} (h : is_preconnected s) : s.subsingleton :=
totally_disconnected_space.is_totally_disconnected_univ s (subset_univ s) h

instance pi.totally_disconnected_space {α : Type*} {β : α → Type*}
  [t₂ : Πa, topological_space (β a)] [∀a, totally_disconnected_space (β a)] :
  totally_disconnected_space (Π (a : α), β a) :=
⟨λ t h1 h2,
  have this : ∀ a, is_preconnected ((λ x : Π a, β a, x a) '' t),
    from λ a, h2.image (λ x, x a) (continuous_apply a).continuous_on,
  λ x x_in y y_in, funext $ λ a, (this a).subsingleton ⟨x, x_in, rfl⟩ ⟨y, y_in, rfl⟩⟩

instance prod.totally_disconnected_space [topological_space β]
  [totally_disconnected_space α] [totally_disconnected_space β] :
  totally_disconnected_space (α × β) :=
⟨λ t h1 h2,
have H1 : is_preconnected (prod.fst '' t), from h2.image prod.fst continuous_fst.continuous_on,
have H2 : is_preconnected (prod.snd '' t), from h2.image prod.snd continuous_snd.continuous_on,
λ x hx y hy, prod.ext
  (H1.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
  (H2.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩

/-- A space is totally disconnected iff its connected components are subsingletons. -/
lemma totally_disconnected_space_iff_connected_component_subsingleton :
  totally_disconnected_space α ↔ ∀ x : α, (connected_component x).subsingleton :=
begin
  split,
  { intros h x,
    apply h.1,
    { exact subset_univ _ },
    exact is_preconnected_connected_component },
  intro h, constructor,
  intros s s_sub hs,
  rcases eq_empty_or_nonempty s with rfl | ⟨x, x_in⟩,
  { exact subsingleton_empty },
  { exact (h x).mono (hs.subset_connected_component x_in) }
end

/-- A space is totally disconnected iff its connected components are singletons. -/
lemma totally_disconnected_space_iff_connected_component_singleton :
  totally_disconnected_space α ↔ ∀ x : α, connected_component x = {x} :=
begin
  rw totally_disconnected_space_iff_connected_component_subsingleton,
  apply forall_congr (λ x, _),
  rw set.subsingleton_iff_singleton,
  exact mem_connected_component
end

/-- The image of a connected component in a totally disconnected space is a singleton. -/
@[simp] lemma continuous.image_connected_component_eq_singleton {β : Type*} [topological_space β]
  [totally_disconnected_space β] {f : α → β} (h : continuous f) (a : α) :
  f '' connected_component a = {f a} :=
(set.subsingleton_iff_singleton $ mem_image_of_mem f mem_connected_component).mp
  (is_preconnected_connected_component.image f h.continuous_on).subsingleton

lemma is_totally_disconnected_of_totally_disconnected_space [totally_disconnected_space α]
  (s : set α) : is_totally_disconnected s :=
λ t hts ht, totally_disconnected_space.is_totally_disconnected_univ _ t.subset_univ ht

lemma is_totally_disconnected_of_image [topological_space β] {f : α → β} (hf : continuous_on f s)
  (hf' : function.injective f) (h : is_totally_disconnected (f '' s)) : is_totally_disconnected s :=
λ t hts ht x x_in y y_in, hf' $ h _ (image_subset f hts) (ht.image f $ hf.mono hts)
  (mem_image_of_mem f x_in) (mem_image_of_mem f y_in)

lemma embedding.is_totally_disconnected [topological_space β] {f : α → β} (hf : embedding f)
  {s : set α} (h : is_totally_disconnected (f '' s)) : is_totally_disconnected s :=
is_totally_disconnected_of_image hf.continuous.continuous_on hf.inj h

instance subtype.totally_disconnected_space {α : Type*} {p : α → Prop} [topological_space α]
  [totally_disconnected_space α] : totally_disconnected_space (subtype p) :=
⟨embedding_subtype_coe.is_totally_disconnected
  (is_totally_disconnected_of_totally_disconnected_space _)⟩

end totally_disconnected

section totally_separated

/-- A set `s` is called totally separated if any two points of this set can be separated
by two disjoint open sets covering `s`. -/
def is_totally_separated (s : set α) : Prop :=
∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∃ u v : set α, is_open u ∧ is_open v ∧
  x ∈ u ∧ y ∈ v ∧ s ⊆ u ∪ v ∧ u ∩ v = ∅

theorem is_totally_separated_empty : is_totally_separated (∅ : set α) :=
λ x, false.elim

theorem is_totally_separated_singleton {x} : is_totally_separated ({x} : set α) :=
λ p hp q hq hpq, (hpq $ (eq_of_mem_singleton hp).symm ▸ (eq_of_mem_singleton hq).symm).elim

theorem is_totally_disconnected_of_is_totally_separated {s : set α}
  (H : is_totally_separated s) : is_totally_disconnected s :=
begin
  intros t hts ht x x_in y y_in,
  by_contra h,
  obtain ⟨u : set α, v : set α, hu : is_open u, hv : is_open v,
          hxu : x ∈ u, hyv : y ∈ v, hs : s ⊆ u ∪ v, huv : u ∩ v = ∅⟩ :=
    H x (hts x_in) y (hts y_in) h,
  have : (t ∩ u).nonempty → (t ∩ v).nonempty → (t ∩ (u ∩ v)).nonempty :=
    ht _ _ hu hv (subset.trans hts hs),
  obtain ⟨z, hz : z ∈ t ∩ (u ∩ v)⟩ := this ⟨x, x_in, hxu⟩ ⟨y, y_in, hyv⟩,
  simpa [huv] using hz
end

alias is_totally_disconnected_of_is_totally_separated ← is_totally_separated.is_totally_disconnected

/-- A space is totally separated if any two points can be separated by two disjoint open sets
covering the whole space. -/
class totally_separated_space (α : Type u) [topological_space α] : Prop :=
(is_totally_separated_univ [] : is_totally_separated (univ : set α))

@[priority 100] -- see Note [lower instance priority]
instance totally_separated_space.totally_disconnected_space (α : Type u) [topological_space α]
  [totally_separated_space α] : totally_disconnected_space α :=
⟨is_totally_disconnected_of_is_totally_separated $
  totally_separated_space.is_totally_separated_univ α⟩

@[priority 100] -- see Note [lower instance priority]
instance totally_separated_space.of_discrete
  (α : Type*) [topological_space α] [discrete_topology α] : totally_separated_space α :=
⟨λ a _ b _ h, ⟨{b}ᶜ, {b}, is_open_discrete _, is_open_discrete _, by simpa⟩⟩

lemma exists_clopen_of_totally_separated {α : Type*} [topological_space α]
  [totally_separated_space α] {x y : α} (hxy : x ≠ y) :
  ∃ (U : set α) (hU : is_clopen U), x ∈ U ∧ y ∈ Uᶜ :=
begin
  obtain ⟨U, V, hU, hV, Ux, Vy, f, disj⟩ :=
    totally_separated_space.is_totally_separated_univ α x (set.mem_univ x) y (set.mem_univ y) hxy,
  have clopen_U := is_clopen_inter_of_disjoint_cover_clopen (is_clopen_univ) f hU hV disj,
  rw set.univ_inter _ at clopen_U,
  rw [←set.subset_compl_iff_disjoint, set.subset_compl_comm] at disj,
  exact ⟨U, clopen_U, Ux, disj Vy⟩,
end

end totally_separated

section connected_component_setoid

/-- The setoid of connected components of a topological space -/
def connected_component_setoid (α : Type*) [topological_space α] : setoid α :=
⟨λ x y, connected_component x = connected_component y,
  ⟨λ x, by trivial, λ x y h1, h1.symm, λ x y z h1 h2, h1.trans h2⟩⟩
-- see Note [lower instance priority]
local attribute [instance, priority 100] connected_component_setoid

lemma connected_component_rel_iff {x y : α} : ⟦x⟧ = ⟦y⟧ ↔
  connected_component x = connected_component y :=
⟨λ h, quotient.exact h, λ h, quotient.sound h⟩

lemma connected_component_nrel_iff {x y : α} : ⟦x⟧ ≠ ⟦y⟧ ↔
  connected_component x ≠ connected_component y :=
by { rw not_iff_not, exact connected_component_rel_iff }

/-- The quotient of a space by its connected components -/
def connected_components (α : Type u) [topological_space α] :=
  quotient (connected_component_setoid α)

instance [inhabited α] : inhabited (connected_components α) := ⟨quotient.mk (default _)⟩
instance connected_components.topological_space : topological_space (connected_components α) :=
  quotient.topological_space

lemma continuous.image_eq_of_equiv {β : Type*} [topological_space β] [totally_disconnected_space β]
  {f : α → β} (h : continuous f) (a b : α) (hab : a ≈ b) : f a = f b :=
singleton_eq_singleton_iff.1 $
  h.image_connected_component_eq_singleton a ▸
  h.image_connected_component_eq_singleton b ▸ hab ▸ rfl

/--
The lift to `connected_components α` of a continuous map from `α` to a totally disconnected space
-/
def continuous.connected_components_lift {β : Type*} [topological_space β]
  [totally_disconnected_space β] {f : α → β} (h : continuous f) : connected_components α → β :=
quotient.lift f h.image_eq_of_equiv

@[continuity] lemma continuous.connected_components_lift_continuous {β : Type*}
  [topological_space β] [totally_disconnected_space β] {f : α → β} (h : continuous f) :
  continuous h.connected_components_lift :=
continuous_quotient_lift h.image_eq_of_equiv h

@[simp] lemma continuous.connected_components_lift_factors {β : Type*} [topological_space β]
  [totally_disconnected_space β] {f : α → β} (h : continuous f) :
  h.connected_components_lift ∘ quotient.mk = f := rfl

lemma continuous.connected_components_lift_unique {β : Type*} [topological_space β]
  [totally_disconnected_space β] {f : α → β} (h : continuous f) (g : connected_components α → β)
  (hg : g ∘ quotient.mk = f) : g = h.connected_components_lift :=
by { subst hg, ext1 x, exact quotient.induction_on x (λ a, refl _) }

lemma connected_components_lift_unique' {β : Type*} (g₁ : connected_components α → β)
  (g₂ : connected_components α → β) (hg : g₁ ∘ quotient.mk = g₂ ∘ quotient.mk ) : g₁ = g₂ :=
begin
  ext1 x,
  refine quotient.induction_on x (λ a, _),
  change (g₁ ∘ quotient.mk) a = (g₂ ∘ quotient.mk) a,
  rw hg,
end

/-- The preimage of a singleton in `connected_components` is the connected component
of an element in the equivalence class. -/
lemma connected_components_preimage_singleton {t : α} :
  connected_component t = quotient.mk ⁻¹' {⟦t⟧} :=
begin
  apply set.eq_of_subset_of_subset; intros a ha,
  { have H : ⟦a⟧ = ⟦t⟧ := quotient.sound (connected_component_eq ha).symm,
    rw [mem_preimage, H],
    exact mem_singleton ⟦t⟧ },
  rw [mem_preimage, mem_singleton_iff] at ha,
  have ha' : connected_component a = connected_component t := quotient.exact ha,
  rw ←ha',
  exact mem_connected_component,
end

/-- The preimage of the image of a set under the quotient map to `connected_components α`
is the union of the connected components of the elements in it. -/
lemma connected_components_preimage_image (U : set α) :
  quotient.mk ⁻¹' (quotient.mk '' U) = ⋃ (x : α) (h : x ∈ U), connected_component x :=
begin
  apply set.eq_of_subset_of_subset,
  { rintros a ⟨b, hb, hab⟩,
    refine mem_Union.2 ⟨b, mem_Union.2 ⟨hb, _⟩⟩,
    rw connected_component_rel_iff.1 hab,
    exact mem_connected_component },
  refine Union_subset (λ a, Union_subset (λ ha, _)),
  rw [connected_components_preimage_singleton,
    (surjective_quotient_mk _).preimage_subset_preimage_iff, singleton_subset_iff],
  exact ⟨a, ha, refl _⟩,
end

instance connected_components.totally_disconnected_space :
  totally_disconnected_space (connected_components α) :=
begin
  rw totally_disconnected_space_iff_connected_component_singleton,
  refine λ x, quotient.induction_on x (λ a, _),
  apply eq_of_subset_of_subset _ (singleton_subset_iff.2 mem_connected_component),
  rw subset_singleton_iff,
  refine λ x, quotient.induction_on x (λ b hb, _),
  rw [connected_component_rel_iff, connected_component_eq],
  suffices : is_preconnected (quotient.mk ⁻¹' connected_component ⟦a⟧),
  { apply mem_of_subset_of_mem (this.subset_connected_component hb),
    exact mem_preimage.2 mem_connected_component },
  apply (@preimage_connected_component_connected _ _ _ _ _ _ _ _).2,
  { refine λ t, quotient.induction_on t (λ s, _),
    rw ←connected_components_preimage_singleton,
    exact is_connected_connected_component },
  refine λ T, ⟨λ hT, hT.preimage continuous_quotient_mk, λ hT, _⟩,
  rwa [← is_open_compl_iff, ← preimage_compl, quotient_map_quotient_mk.is_open_preimage,
    is_open_compl_iff] at hT,
end

/-- Functoriality of `connected_components` -/
def continuous.connected_components_map {β : Type*} [topological_space β] {f : α → β}
  (h : continuous f) : connected_components α → connected_components β :=
continuous.connected_components_lift (continuous_quotient_mk.comp h)

lemma continuous.connected_components_map_continuous {β : Type*} [topological_space β] {f : α → β}
  (h : continuous f) : continuous h.connected_components_map :=
continuous.connected_components_lift_continuous (continuous_quotient_mk.comp h)

end connected_component_setoid
