/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.subset_properties
import topology.connected

/-!
# Separation properties of topological spaces.

This file defines the predicate `separated`, and common separation axioms
(under the Kolmogorov classification).

## Main definitions

* `separated`: Two `set`s are separated if they are contained in disjoint open sets.
* `t0_space`: A T₀/Kolmogorov space is a space where, for every two points `x ≠ y`,
  there is an open set that contains one, but not the other.
* `t1_space`: A T₁/Fréchet space is a space where every singleton set is closed.
  This is equivalent to, for every pair `x ≠ y`, there existing an open set containing `x`
  but not `y` (`t1_iff_exists_open` shows that these conditions are equivalent.)
* `t2_space`: A T₂/Hausdorff space is a space where, for every two points `x ≠ y`,
  there is two disjoint open sets, one containing `x`, and the other `y`.
* `t2_5_space`: A T₂.₅/Urysohn space is a space where, for every two points `x ≠ y`,
  there is two open sets, one containing `x`, and the other `y`, whose closures are disjoint.
* `regular_space`: A T₃ space (sometimes referred to as regular, but authors vary on
  whether this includes T₂; `mathlib` does), is one where given any closed `C` and `x ∉ C`,
  there is disjoint open sets containing `x` and `C` respectively. In `mathlib`, T₃ implies T₂.₅.
* `normal_space`: A T₄ space (sometimes referred to as normal, but authors vary on
  whether this includes T₂; `mathlib` does), is one where given two disjoint closed sets,
  we can find two open sets that separate them. In `mathlib`, T₄ implies T₃.

## Main results

### T₀ spaces

* `is_closed.exists_closed_singleton` Given a closed set `S` in a compact T₀ space,
  there is some `x ∈ S` such that `{x}` is closed.
* `exists_open_singleton_of_open_finset` Given an open `finset` `S` in a T₀ space,
  there is some `x ∈ S` such that `{x}` is open.

### T₁ spaces

* `is_closed_map_const`: The constant map is a closed map.
* `discrete_of_t1_of_finite`: A finite T₁ space must have the discrete topology.

### T₂ spaces

* `t2_iff_nhds`: A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter.
* `t2_iff_is_closed_diagonal`: A space is T₂ iff the `diagonal` of `α` (that is, the set of all
  points of the form `(a, a) : α × α`) is closed under the product topology.
* `finset_disjoing_finset_opens_of_t2`: Any two disjoint finsets are `separated`.
* Most topological constructions preserve Hausdorffness;
  these results are part of the typeclass inference system (e.g. `embedding.t2_space`)
* `set.eq_on.closure`: If two functions are equal on some set `s`, they are equal on its closure.
* `is_compact.is_closed`: All compact sets are closed.
* `locally_compact_of_compact_nhds`: If every point has a compact neighbourhood,
  then the space is locally compact.
* `tot_sep_of_zero_dim`: If `α` has a clopen basis, it is a `totally_separated_space`.
* `loc_compact_t2_tot_disc_iff_tot_sep`: A locally compact T₂ space is totally disconnected iff
  it is totally separated.

If the space is also compact:

* `normal_of_compact_t2`: A compact T₂ space is a `normal_space`.
* `connected_components_eq_Inter_clopen`: The connected component of a point
  is the intersection of all its clopen neighbourhoods.
* `compact_t2_tot_disc_iff_tot_sep`: Being a `totally_disconnected_space`
  is equivalent to being a `totally_separated_space`.
* `connected_components.t2`: `connected_components α` is T₂ for `α` T₂ and compact.

### T₃ spaces

* `disjoint_nested_nhds`: Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and
  `y ∈ V₂ ⊆ U₂`, with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint.

### Discrete spaces

* `discrete_topology_iff_nhds`: Discrete topological spaces are those whose neighbourhood
  filters are the `pure` filter (which is the principal filter at a singleton).
* `induced_bot`/`discrete_topology_induced`: The pullback of the discrete topology
  under an inclusion is the discrete topology.

## References

https://en.wikipedia.org/wiki/Separation_axiom
-/

open set filter
open_locale topological_space filter classical

universes u v
variables {α : Type u} {β : Type v} [topological_space α]

section separation

/--
`separated` is a predicate on pairs of sub`set`s of a topological space.  It holds if the two
sub`set`s are contained in disjoint open sets.
-/
def separated : set α → set α → Prop :=
  λ (s t : set α), ∃ U V : (set α), (is_open U) ∧ is_open V ∧
  (s ⊆ U) ∧ (t ⊆ V) ∧ disjoint U V

namespace separated

open separated

@[symm] lemma symm {s t : set α} : separated s t → separated t s :=
λ ⟨U, V, oU, oV, aU, bV, UV⟩, ⟨V, U, oV, oU, bV, aU, disjoint.symm UV⟩

lemma comm (s t : set α) : separated s t ↔ separated t s :=
⟨symm, symm⟩

lemma empty_right (a : set α) : separated a ∅ :=
⟨_, _, is_open_univ, is_open_empty, λ a h, mem_univ a, λ a h, by cases h, disjoint_empty _⟩

lemma empty_left (a : set α) : separated ∅ a :=
(empty_right _).symm

lemma union_left {a b c : set α} : separated a c → separated b c → separated (a ∪ b) c :=
λ ⟨U, V, oU, oV, aU, bV, UV⟩ ⟨W, X, oW, oX, aW, bX, WX⟩,
  ⟨U ∪ W, V ∩ X, is_open.union oU oW, is_open.inter oV oX,
    union_subset_union aU aW, subset_inter bV bX, set.disjoint_union_left.mpr
    ⟨disjoint_of_subset_right (inter_subset_left _ _) UV,
      disjoint_of_subset_right (inter_subset_right _ _) WX⟩⟩

lemma union_right {a b c : set α} (ab : separated a b) (ac : separated a c) :
  separated a (b ∪ c) :=
(ab.symm.union_left ac.symm).symm

end separated

/-- A T₀ space, also known as a Kolmogorov space, is a topological space
  where for every pair `x ≠ y`, there is an open set containing one but not the other. -/
class t0_space (α : Type u) [topological_space α] : Prop :=
(t0 : ∀ x y, x ≠ y → ∃ U:set α, is_open U ∧ (xor (x ∈ U) (y ∈ U)))

/-- Given a closed set `S` in a compact T₀ space,
there is some `x ∈ S` such that `{x}` is closed. -/
theorem is_closed.exists_closed_singleton {α : Type*} [topological_space α]
  [t0_space α] [compact_space α] {S : set α} (hS : is_closed S) (hne : S.nonempty) :
  ∃ (x : α), x ∈ S ∧ is_closed ({x} : set α) :=
begin
  obtain ⟨V, Vsub, Vne, Vcls, hV⟩ := hS.exists_minimal_nonempty_closed_subset hne,
  by_cases hnt : ∃ (x y : α) (hx : x ∈ V) (hy : y ∈ V), x ≠ y,
  { exfalso,
    obtain ⟨x, y, hx, hy, hne⟩ := hnt,
    obtain ⟨U, hU, hsep⟩ := t0_space.t0 _ _ hne,
    have : ∀ (z w : α) (hz : z ∈ V) (hw : w ∈ V) (hz' : z ∈ U) (hw' : ¬ w ∈ U), false,
    { intros z w hz hw hz' hw',
      have uvne : (V ∩ Uᶜ).nonempty,
      { use w, simp only [hw, hw', set.mem_inter_eq, not_false_iff, and_self, set.mem_compl_eq], },
      specialize hV (V ∩ Uᶜ) (set.inter_subset_left _ _) uvne
        (is_closed.inter Vcls (is_closed_compl_iff.mpr hU)),
      have : V ⊆ Uᶜ,
      { rw ←hV, exact set.inter_subset_right _ _ },
      exact this hz hz', },
    cases hsep,
    { exact this x y hx hy hsep.1 hsep.2 },
    { exact this y x hy hx hsep.1 hsep.2 } },
  { push_neg at hnt,
    obtain ⟨z, hz⟩ := Vne,
    refine ⟨z, Vsub hz, _⟩,
    convert Vcls,
    ext,
    simp only [set.mem_singleton_iff, set.mem_compl_eq],
    split,
    { rintro rfl, exact hz, },
    { exact λ hx, hnt x z hx hz, }, },
end

/-- Given an open `finset` `S` in a T₀ space, there is some `x ∈ S` such that `{x}` is open. -/
theorem exists_open_singleton_of_open_finset [t0_space α] (s : finset α) (sne : s.nonempty)
  (hso : is_open (s : set α)) :
  ∃ x ∈ s, is_open ({x} : set α):=
begin
  induction s using finset.strong_induction_on with s ihs,
  by_cases hs : set.subsingleton (s : set α),
  { rcases sne with ⟨x, hx⟩,
    refine ⟨x, hx, _⟩,
    have : (s : set α) = {x}, from hs.eq_singleton_of_mem hx,
    rwa this at hso },
  { dunfold set.subsingleton at hs,
    push_neg at hs,
    rcases hs with ⟨x, hx, y, hy, hxy⟩,
    rcases t0_space.t0 x y hxy with ⟨U, hU, hxyU⟩,
    wlog H : x ∈ U ∧ y ∉ U := hxyU using [x y, y x],
    obtain ⟨z, hzs, hz⟩ : ∃ z ∈ s.filter (λ z, z ∈ U), is_open ({z} : set α),
    { refine ihs _ (finset.filter_ssubset.2 ⟨y, hy, H.2⟩) ⟨x, finset.mem_filter.2 ⟨hx, H.1⟩⟩ _,
      rw [finset.coe_filter],
      exact is_open.inter hso hU },
    exact ⟨z, (finset.mem_filter.1 hzs).1, hz⟩ }
end

theorem exists_open_singleton_of_fintype [t0_space α] [f : fintype α] [ha : nonempty α] :
  ∃ x:α, is_open ({x}:set α) :=
begin
  refine ha.elim (λ x, _),
  have : is_open ((finset.univ : finset α) : set α), { simp },
  rcases exists_open_singleton_of_open_finset _ ⟨x, finset.mem_univ x⟩ this with ⟨x, _, hx⟩,
  exact ⟨x, hx⟩
end

instance subtype.t0_space [t0_space α] {p : α → Prop} : t0_space (subtype p) :=
⟨λ x y hxy, let ⟨U, hU, hxyU⟩ := t0_space.t0 (x:α) y ((not_congr subtype.ext_iff_val).1 hxy) in
  ⟨(coe : subtype p → α) ⁻¹' U, is_open_induced hU, hxyU⟩⟩

/-- A T₁ space, also known as a Fréchet space, is a topological space
  where every singleton set is closed. Equivalently, for every pair
  `x ≠ y`, there is an open set containing `x` and not `y`. -/
class t1_space (α : Type u) [topological_space α] : Prop :=
(t1 : ∀x, is_closed ({x} : set α))

lemma is_closed_singleton [t1_space α] {x : α} : is_closed ({x} : set α) :=
t1_space.t1 x

lemma is_open_compl_singleton [t1_space α] {x : α} : is_open ({x}ᶜ : set α) :=
is_closed_singleton.is_open_compl

lemma is_open_ne [t1_space α] {x : α} : is_open {y | y ≠ x} :=
is_open_compl_singleton

instance subtype.t1_space {α : Type u} [topological_space α] [t1_space α] {p : α → Prop} :
  t1_space (subtype p) :=
⟨λ ⟨x, hx⟩, is_closed_induced_iff.2 $ ⟨{x}, is_closed_singleton, set.ext $ λ y,
  by simp [subtype.ext_iff_val]⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance t1_space.t0_space [t1_space α] : t0_space α :=
⟨λ x y h, ⟨{z | z ≠ y}, is_open_ne, or.inl ⟨h, not_not_intro rfl⟩⟩⟩

lemma t1_iff_exists_open : t1_space α ↔
  ∀ (x y), x ≠ y → (∃ (U : set α) (hU : is_open U), x ∈ U ∧ y ∉ U) :=
begin
  split,
  { introsI t1 x y hxy,
    exact ⟨{y}ᶜ, is_open_compl_iff.mpr (t1_space.t1 y),
            mem_compl_singleton_iff.mpr hxy,
            not_not.mpr rfl⟩},
  { intro h,
    constructor,
    intro x,
    rw ← is_open_compl_iff,
    have p : ⋃₀ {U : set α | (x ∉ U) ∧ (is_open U)} = {x}ᶜ,
    { apply subset.antisymm; intros t ht,
      { rcases ht with ⟨A, ⟨hxA, hA⟩, htA⟩,
        rw [mem_compl_eq, mem_singleton_iff],
        rintro rfl,
        contradiction },
      { obtain ⟨U, hU, hh⟩ := h t x (mem_compl_singleton_iff.mp ht),
        exact ⟨U, ⟨hh.2, hU⟩, hh.1⟩}},
    rw ← p,
    exact is_open_sUnion (λ B hB, hB.2) }
end

lemma compl_singleton_mem_nhds [t1_space α] {x y : α} (h : y ≠ x) : {x}ᶜ ∈ 𝓝 y :=
is_open.mem_nhds is_open_compl_singleton $ by rwa [mem_compl_eq, mem_singleton_iff]

@[simp] lemma closure_singleton [t1_space α] {a : α} :
  closure ({a} : set α) = {a} :=
is_closed_singleton.closure_eq

lemma set.subsingleton.closure [t1_space α] {s : set α} (hs : s.subsingleton) :
  (closure s).subsingleton :=
hs.induction_on (by simp) $ λ x, by simp

@[simp] lemma subsingleton_closure [t1_space α] {s : set α} :
  (closure s).subsingleton ↔ s.subsingleton :=
⟨λ h, h.mono subset_closure, λ h, h.closure⟩

lemma is_closed_map_const {α β} [topological_space α] [topological_space β] [t1_space β] {y : β} :
  is_closed_map (function.const α y) :=
begin
  apply is_closed_map.of_nonempty, intros s hs h2s, simp_rw [h2s.image_const, is_closed_singleton]
end

lemma discrete_of_t1_of_finite {X : Type*} [topological_space X] [t1_space X] [fintype X] :
  discrete_topology X :=
begin
  apply singletons_open_iff_discrete.mp,
  intros x,
  rw [← is_closed_compl_iff, ← bUnion_of_singleton ({x} : set X)ᶜ],
  exact is_closed_bUnion (finite.of_fintype _) (λ y _, is_closed_singleton)
end

lemma singleton_mem_nhds_within_of_mem_discrete {s : set α} [discrete_topology s]
  {x : α} (hx : x ∈ s) :
  {x} ∈ 𝓝[s] x :=
begin
  have : ({⟨x, hx⟩} : set s) ∈ 𝓝 (⟨x, hx⟩ : s), by simp [nhds_discrete],
  simpa only [nhds_within_eq_map_subtype_coe hx, image_singleton]
    using @image_mem_map _ _ _ (coe : s → α) _ this
end

/-- The neighbourhoods filter of `x` within `s`, under the discrete topology, is equal to
the pure `x` filter (which is the principal filter at the singleton `{x}`.) -/
lemma nhds_within_of_mem_discrete {s : set α} [discrete_topology s] {x : α} (hx : x ∈ s) :
  𝓝[s] x = pure x :=
le_antisymm (le_pure_iff.2 $ singleton_mem_nhds_within_of_mem_discrete hx) (pure_le_nhds_within hx)

lemma filter.has_basis.exists_inter_eq_singleton_of_mem_discrete
  {ι : Type*} {p : ι → Prop} {t : ι → set α} {s : set α} [discrete_topology s] {x : α}
  (hb : (𝓝 x).has_basis p t) (hx : x ∈ s) :
  ∃ i (hi : p i), t i ∩ s = {x} :=
begin
  rcases (nhds_within_has_basis hb s).mem_iff.1 (singleton_mem_nhds_within_of_mem_discrete hx)
    with ⟨i, hi, hix⟩,
  exact ⟨i, hi, subset.antisymm hix $ singleton_subset_iff.2
    ⟨mem_of_mem_nhds $ hb.mem_of_mem hi, hx⟩⟩
end

/-- A point `x` in a discrete subset `s` of a topological space admits a neighbourhood
that only meets `s` at `x`.  -/
lemma nhds_inter_eq_singleton_of_mem_discrete {s : set α} [discrete_topology s]
  {x : α} (hx : x ∈ s) :
  ∃ U ∈ 𝓝 x, U ∩ s = {x} :=
by simpa using (𝓝 x).basis_sets.exists_inter_eq_singleton_of_mem_discrete hx

/-- For point `x` in a discrete subset `s` of a topological space, there is a set `U`
such that
1. `U` is a punctured neighborhood of `x` (ie. `U ∪ {x}` is a neighbourhood of `x`),
2. `U` is disjoint from `s`.
-/
lemma disjoint_nhds_within_of_mem_discrete {s : set α} [discrete_topology s] {x : α} (hx : x ∈ s) :
  ∃ U ∈ 𝓝[{x}ᶜ] x, disjoint U s :=
let ⟨V, h, h'⟩ := nhds_inter_eq_singleton_of_mem_discrete hx in
  ⟨{x}ᶜ ∩ V, inter_mem_nhds_within _ h,
    (disjoint_iff_inter_eq_empty.mpr (by { rw [inter_assoc, h', compl_inter_self] }))⟩

/-- Let `X` be a topological space and let `s, t ⊆ X` be two subsets.  If there is an inclusion
`t ⊆ s`, then the topological space structure on `t` induced by `X` is the same as the one
obtained by the induced topological space structure on `s`. -/
lemma topological_space.subset_trans {X : Type*} [tX : topological_space X]
  {s t : set X} (ts : t ⊆ s) :
  (subtype.topological_space : topological_space t) =
    (subtype.topological_space : topological_space s).induced (set.inclusion ts) :=
begin
  change tX.induced ((coe : s → X) ∘ (set.inclusion ts)) =
    topological_space.induced (set.inclusion ts) (tX.induced _),
  rw ← induced_compose,
end

/-- This lemma characterizes discrete topological spaces as those whose singletons are
neighbourhoods. -/
lemma discrete_topology_iff_nhds {X : Type*} [topological_space X] :
  discrete_topology X ↔ (nhds : X → filter X) = pure :=
begin
  split,
  { introI hX,
    exact nhds_discrete X },
  { intro h,
    constructor,
    apply eq_of_nhds_eq_nhds,
    simp [h, nhds_bot] }
end

/-- The topology pulled-back under an inclusion `f : X → Y` from the discrete topology (`⊥`) is the
discrete topology.
This version does not assume the choice of a topology on either the source `X`
nor the target `Y` of the inclusion `f`. -/
lemma induced_bot {X Y : Type*} {f : X → Y} (hf : function.injective f) :
  topological_space.induced f ⊥ = ⊥ :=
eq_of_nhds_eq_nhds (by simp [nhds_induced, ← set.image_singleton, hf.preimage_image, nhds_bot])

/-- The topology induced under an inclusion `f : X → Y` from the discrete topological space `Y`
is the discrete topology on `X`. -/
lemma discrete_topology_induced {X Y : Type*} [tY : topological_space Y] [discrete_topology Y]
  {f : X → Y} (hf : function.injective f) : @discrete_topology X (topological_space.induced f tY) :=
begin
  constructor,
  rw discrete_topology.eq_bot Y,
  exact induced_bot hf
end

/-- Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and the topology induced
by `X`on `s` is discrete, then also the topology induces on `t` is discrete.  -/
lemma discrete_topology.of_subset {X : Type*} [topological_space X] {s t : set X}
  (ds : discrete_topology s) (ts : t ⊆ s) :
  discrete_topology t :=
begin
  rw [topological_space.subset_trans ts, ds.eq_bot],
  exact {eq_bot := induced_bot (set.inclusion_injective ts)}
end

/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
class t2_space (α : Type u) [topological_space α] : Prop :=
(t2 : ∀x y, x ≠ y → ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅)

lemma t2_separation [t2_space α] {x y : α} (h : x ≠ y) :
  ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
t2_space.t2 x y h

@[priority 100] -- see Note [lower instance priority]
instance t2_space.t1_space [t2_space α] : t1_space α :=
⟨λ x, is_open_compl_iff.1 $ is_open_iff_forall_mem_open.2 $ λ y hxy,
let ⟨u, v, hu, hv, hyu, hxv, huv⟩ := t2_separation (mt mem_singleton_of_eq hxy) in
⟨u, λ z hz1 hz2, (ext_iff.1 huv x).1 ⟨mem_singleton_iff.1 hz2 ▸ hz1, hxv⟩, hu, hyu⟩⟩

lemma eq_of_nhds_ne_bot [ht : t2_space α] {x y : α} (h : ne_bot (𝓝 x ⊓ 𝓝 y)) : x = y :=
classical.by_contradiction $ assume : x ≠ y,
let ⟨u, v, hu, hv, hx, hy, huv⟩ := t2_space.t2 x y this in
absurd huv $ (inf_ne_bot_iff.1 h (is_open.mem_nhds hu hx) (is_open.mem_nhds hv hy)).ne_empty

/-- A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter. -/
lemma t2_iff_nhds : t2_space α ↔ ∀ {x y : α}, ne_bot (𝓝 x ⊓ 𝓝 y) → x = y :=
⟨assume h, by exactI λ x y, eq_of_nhds_ne_bot,
 assume h, ⟨assume x y xy,
   have 𝓝 x ⊓ 𝓝 y = ⊥ := not_ne_bot.1 $ mt h xy,
   let ⟨u', hu', v', hv', u'v'⟩ := empty_in_sets_eq_bot.mpr this,
       ⟨u, uu', uo, hu⟩ := mem_nhds_iff.mp hu',
       ⟨v, vv', vo, hv⟩ := mem_nhds_iff.mp hv' in
   ⟨u, v, uo, vo, hu, hv, disjoint.eq_bot $ disjoint.mono uu' vv' u'v'⟩⟩⟩

lemma t2_iff_ultrafilter :
  t2_space α ↔ ∀ {x y : α} (f : ultrafilter α), ↑f ≤ 𝓝 x → ↑f ≤ 𝓝 y → x = y :=
t2_iff_nhds.trans $ by simp only [←exists_ultrafilter_iff, and_imp, le_inf_iff, exists_imp_distrib]

lemma is_closed_diagonal [t2_space α] : is_closed (diagonal α) :=
begin
  refine is_closed_iff_cluster_pt.mpr _,
  rintro ⟨a₁, a₂⟩ h,
  refine eq_of_nhds_ne_bot ⟨λ this : 𝓝 a₁ ⊓ 𝓝 a₂ = ⊥, h.ne _⟩,
  obtain ⟨t₁, (ht₁ : t₁ ∈ 𝓝 a₁), t₂, (ht₂ : t₂ ∈ 𝓝 a₂), (h' : t₁ ∩ t₂ ⊆ ∅)⟩ :=
    by rw [←empty_in_sets_eq_bot, mem_inf_sets] at this; exact this,
  rw [nhds_prod_eq, ←empty_in_sets_eq_bot],
  apply filter.sets_of_superset,
  apply inter_mem_inf_sets (prod_mem_prod ht₁ ht₂) (mem_principal_sets.mpr (subset.refl _)),
  exact assume ⟨x₁, x₂⟩ ⟨⟨hx₁, hx₂⟩, (heq : x₁ = x₂)⟩,
    show false, from @h' x₁ ⟨hx₁, heq.symm ▸ hx₂⟩
end

lemma t2_iff_is_closed_diagonal : t2_space α ↔ is_closed (diagonal α) :=
begin
  split,
  { introI h,
    exact is_closed_diagonal },
  { intro h,
    constructor,
    intros x y hxy,
    have : (x, y) ∈ (diagonal α)ᶜ, by rwa [mem_compl_iff],
    obtain ⟨t, t_sub, t_op, xyt⟩ : ∃ t ⊆ (diagonal α)ᶜ, is_open t ∧ (x, y) ∈ t :=
      is_open_iff_forall_mem_open.mp h.is_open_compl _ this,
    rcases is_open_prod_iff.mp t_op x y xyt with ⟨U, V, U_op, V_op, xU, yV, H⟩,
    use [U, V, U_op, V_op, xU, yV],
    have := subset.trans H t_sub,
    rw eq_empty_iff_forall_not_mem,
    rintros z ⟨zU, zV⟩,
    have : ¬ (z, z) ∈ diagonal α := this (mk_mem_prod zU zV),
    exact this rfl },
end

section separated

open separated finset

lemma finset_disjoint_finset_opens_of_t2 [t2_space α] :
  ∀ (s t : finset α), disjoint s t → separated (s : set α) t :=
begin
  refine induction_on_union _ (λ a b hi d, (hi d.symm).symm) (λ a d, empty_right a) (λ a b ab, _) _,
  { obtain ⟨U, V, oU, oV, aU, bV, UV⟩ := t2_separation
      (by { rw [ne.def, ← finset.mem_singleton], exact (disjoint_singleton.mp ab.symm) }),
    refine ⟨U, V, oU, oV, _, _, set.disjoint_iff_inter_eq_empty.mpr UV⟩;
    exact singleton_subset_set_iff.mpr ‹_› },
  { intros a b c ac bc d,
    apply_mod_cast union_left (ac (disjoint_of_subset_left (a.subset_union_left b) d)) (bc _),
    exact disjoint_of_subset_left (a.subset_union_right b) d },
end

lemma point_disjoint_finset_opens_of_t2 [t2_space α] {x : α} {s : finset α} (h : x ∉ s) :
  separated ({x} : set α) s :=
by exact_mod_cast finset_disjoint_finset_opens_of_t2 {x} s (singleton_disjoint.mpr h)

end separated

@[simp] lemma nhds_eq_nhds_iff {a b : α} [t2_space α] : 𝓝 a = 𝓝 b ↔ a = b :=
⟨assume h, eq_of_nhds_ne_bot $ by rw [h, inf_idem]; exact nhds_ne_bot, assume h, h ▸ rfl⟩

@[simp] lemma nhds_le_nhds_iff {a b : α} [t2_space α] : 𝓝 a ≤ 𝓝 b ↔ a = b :=
⟨assume h, eq_of_nhds_ne_bot $ by rw [inf_of_le_left h]; exact nhds_ne_bot, assume h, h ▸ le_refl _⟩

lemma tendsto_nhds_unique [t2_space α] {f : β → α} {l : filter β} {a b : α}
  [ne_bot l] (ha : tendsto f l (𝓝 a)) (hb : tendsto f l (𝓝 b)) : a = b :=
eq_of_nhds_ne_bot $ ne_bot_of_le $ le_inf ha hb

lemma tendsto_nhds_unique' [t2_space α] {f : β → α} {l : filter β} {a b : α}
  (hl : ne_bot l) (ha : tendsto f l (𝓝 a)) (hb : tendsto f l (𝓝 b)) : a = b :=
eq_of_nhds_ne_bot $ ne_bot_of_le $ le_inf ha hb

lemma tendsto_nhds_unique_of_eventually_eq [t2_space α] {f g : β → α} {l : filter β} {a b : α}
  [ne_bot l] (ha : tendsto f l (𝓝 a)) (hb : tendsto g l (𝓝 b)) (hfg : f =ᶠ[l] g) :
  a = b :=
tendsto_nhds_unique (ha.congr' hfg) hb

lemma tendsto_const_nhds_iff [t2_space α] {l : filter α} [ne_bot l] {c d : α} :
  tendsto (λ x, c) l (𝓝 d) ↔ c = d :=
⟨λ h, tendsto_nhds_unique (tendsto_const_nhds) h, λ h, h ▸ tendsto_const_nhds⟩

/-- A T₂.₅ space, also known as a Urysohn space, is a topological space
  where for every pair `x ≠ y`, there are two open sets, with the intersection of clousures
  empty, one containing `x` and the other `y` . -/
class t2_5_space (α : Type u) [topological_space α]: Prop :=
(t2_5 : ∀ x y  (h : x ≠ y), ∃ (U V: set α), is_open U ∧  is_open V ∧
                                            closure U ∩ closure V = ∅ ∧ x ∈ U ∧ y ∈ V)

@[priority 100] -- see Note [lower instance priority]
instance t2_5_space.t2_space [t2_5_space α] : t2_space α :=
⟨λ x y hxy,
  let ⟨U, V, hU, hV, hUV, hh⟩ := t2_5_space.t2_5 x y hxy in
  ⟨U, V, hU, hV, hh.1, hh.2, subset_eq_empty (powerset_mono.mpr
    (closure_inter_subset_inter_closure U V) subset_closure) hUV⟩⟩

section lim
variables [t2_space α] {f : filter α}

/-!
### Properties of `Lim` and `lim`

In this section we use explicit `nonempty α` instances for `Lim` and `lim`. This way the lemmas
are useful without a `nonempty α` instance.
-/

lemma Lim_eq {a : α} [ne_bot f] (h : f ≤ 𝓝 a) :
  @Lim _ _ ⟨a⟩ f = a :=
tendsto_nhds_unique (le_nhds_Lim ⟨a, h⟩) h

lemma Lim_eq_iff [ne_bot f] (h : ∃ (a : α), f ≤ nhds a) {a} : @Lim _ _ ⟨a⟩ f = a ↔ f ≤ 𝓝 a :=
⟨λ c, c ▸ le_nhds_Lim h, Lim_eq⟩

lemma ultrafilter.Lim_eq_iff_le_nhds [compact_space α] {x : α} {F : ultrafilter α} :
  F.Lim = x ↔ ↑F ≤ 𝓝 x :=
⟨λ h, h ▸ F.le_nhds_Lim, Lim_eq⟩

lemma is_open_iff_ultrafilter' [compact_space α] (U : set α) :
  is_open U ↔ (∀ F : ultrafilter α, F.Lim ∈ U → U ∈ F.1) :=
begin
  rw is_open_iff_ultrafilter,
  refine ⟨λ h F hF, h F.Lim hF F F.le_nhds_Lim, _⟩,
  intros cond x hx f h,
  rw [← (ultrafilter.Lim_eq_iff_le_nhds.2 h)] at hx,
  exact cond _ hx
end

lemma filter.tendsto.lim_eq {a : α} {f : filter β} [ne_bot f] {g : β → α} (h : tendsto g f (𝓝 a)) :
  @lim _ _ _ ⟨a⟩ f g = a :=
Lim_eq h

lemma filter.lim_eq_iff {f : filter β} [ne_bot f] {g : β → α} (h : ∃ a, tendsto g f (𝓝 a)) {a} :
  @lim _ _ _ ⟨a⟩ f g = a ↔ tendsto g f (𝓝 a) :=
⟨λ c, c ▸ tendsto_nhds_lim h, filter.tendsto.lim_eq⟩

lemma continuous.lim_eq [topological_space β] {f : β → α} (h : continuous f) (a : β) :
  @lim _ _ _ ⟨f a⟩ (𝓝 a) f = f a :=
(h.tendsto a).lim_eq

@[simp] lemma Lim_nhds (a : α) : @Lim _ _ ⟨a⟩ (𝓝 a) = a :=
Lim_eq (le_refl _)

@[simp] lemma lim_nhds_id (a : α) : @lim _ _ _ ⟨a⟩ (𝓝 a) id = a :=
Lim_nhds a

@[simp] lemma Lim_nhds_within {a : α} {s : set α} (h : a ∈ closure s) :
  @Lim _ _ ⟨a⟩ (𝓝[s] a) = a :=
by haveI : ne_bot (𝓝[s] a) := mem_closure_iff_cluster_pt.1 h;
exact Lim_eq inf_le_left

@[simp] lemma lim_nhds_within_id {a : α} {s : set α} (h : a ∈ closure s) :
  @lim _ _ _ ⟨a⟩ (𝓝[s] a) id = a :=
Lim_nhds_within h

end lim

/-!
### `t2_space` constructions

We use two lemmas to prove that various standard constructions generate Hausdorff spaces from
Hausdorff spaces:

* `separated_by_continuous` says that two points `x y : α` can be separated by open neighborhoods
  provided that there exists a continuous map `f : α → β` with a Hausdorff codomain such that
  `f x ≠ f y`. We use this lemma to prove that topological spaces defined using `induced` are
  Hausdorff spaces.

* `separated_by_open_embedding` says that for an open embedding `f : α → β` of a Hausdorff space
  `α`, the images of two distinct points `x y : α`, `x ≠ y` can be separated by open neighborhoods.
  We use this lemma to prove that topological spaces defined using `coinduced` are Hausdorff spaces.
-/

@[priority 100] -- see Note [lower instance priority]
instance t2_space_discrete {α : Type*} [topological_space α] [discrete_topology α] : t2_space α :=
{ t2 := assume x y hxy, ⟨{x}, {y}, is_open_discrete _, is_open_discrete _, rfl, rfl,
  eq_empty_iff_forall_not_mem.2 $ by intros z hz;
    cases eq_of_mem_singleton hz.1; cases eq_of_mem_singleton hz.2; cc⟩ }

lemma separated_by_continuous {α : Type*} {β : Type*}
  [topological_space α] [topological_space β] [t2_space β]
  {f : α → β} (hf : continuous f) {x y : α} (h : f x ≠ f y) :
  ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h in
⟨f ⁻¹' u, f ⁻¹' v, uo.preimage hf, vo.preimage hf, xu, yv,
  by rw [←preimage_inter, uv, preimage_empty]⟩

lemma separated_by_open_embedding {α β : Type*} [topological_space α] [topological_space β]
  [t2_space α] {f : α → β} (hf : open_embedding f) {x y : α} (h : x ≠ y) :
  ∃ u v : set β, is_open u ∧ is_open v ∧ f x ∈ u ∧ f y ∈ v ∧ u ∩ v = ∅ :=
let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h in
⟨f '' u, f '' v, hf.is_open_map _ uo, hf.is_open_map _ vo,
  mem_image_of_mem _ xu, mem_image_of_mem _ yv, by rw [image_inter hf.inj, uv, image_empty]⟩

instance {α : Type*} {p : α → Prop} [t : topological_space α] [t2_space α] : t2_space (subtype p) :=
⟨assume x y h, separated_by_continuous continuous_subtype_val (mt subtype.eq h)⟩

instance {α : Type*} {β : Type*} [t₁ : topological_space α] [t2_space α]
  [t₂ : topological_space β] [t2_space β] : t2_space (α × β) :=
⟨assume ⟨x₁,x₂⟩ ⟨y₁,y₂⟩ h,
  or.elim (not_and_distrib.mp (mt prod.ext_iff.mpr h))
    (λ h₁, separated_by_continuous continuous_fst h₁)
    (λ h₂, separated_by_continuous continuous_snd h₂)⟩

lemma embedding.t2_space [topological_space β] [t2_space β] {f : α → β} (hf : embedding f) :
  t2_space α :=
⟨λ x y h, separated_by_continuous hf.continuous (hf.inj.ne h)⟩

instance {α : Type*} {β : Type*} [t₁ : topological_space α] [t2_space α]
  [t₂ : topological_space β] [t2_space β] : t2_space (α ⊕ β) :=
begin
  constructor,
  rintros (x|x) (y|y) h,
  { replace h : x ≠ y := λ c, (c.subst h) rfl,
    exact separated_by_open_embedding open_embedding_inl h },
  { exact ⟨_, _, is_open_range_inl, is_open_range_inr, ⟨x, rfl⟩, ⟨y, rfl⟩,
      range_inl_inter_range_inr⟩ },
  { exact ⟨_, _, is_open_range_inr, is_open_range_inl, ⟨x, rfl⟩, ⟨y, rfl⟩,
      range_inr_inter_range_inl⟩ },
  { replace h : x ≠ y := λ c, (c.subst h) rfl,
    exact separated_by_open_embedding open_embedding_inr h }
end

instance Pi.t2_space {α : Type*} {β : α → Type v} [t₂ : Πa, topological_space (β a)]
  [∀a, t2_space (β a)] :
  t2_space (Πa, β a) :=
⟨assume x y h,
  let ⟨i, hi⟩ := not_forall.mp (mt funext h) in
  separated_by_continuous (continuous_apply i) hi⟩

instance sigma.t2_space {ι : Type*} {α : ι → Type*} [Πi, topological_space (α i)]
  [∀a, t2_space (α a)] :
  t2_space (Σi, α i) :=
begin
  constructor,
  rintros ⟨i, x⟩ ⟨j, y⟩ neq,
  rcases em (i = j) with (rfl|h),
  { replace neq : x ≠ y := λ c, (c.subst neq) rfl,
    exact separated_by_open_embedding open_embedding_sigma_mk neq },
  { exact ⟨_, _, is_open_range_sigma_mk, is_open_range_sigma_mk, ⟨x, rfl⟩, ⟨y, rfl⟩, by tidy⟩ }
end

variables [topological_space β]

lemma is_closed_eq [t2_space α] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : is_closed {x:β | f x = g x} :=
continuous_iff_is_closed.mp (hf.prod_mk hg) _ is_closed_diagonal

/-- If two continuous maps are equal on `s`, then they are equal on the closure of `s`. -/
lemma set.eq_on.closure [t2_space α] {s : set β} {f g : β → α} (h : eq_on f g s)
  (hf : continuous f) (hg : continuous g) :
  eq_on f g (closure s) :=
closure_minimal h (is_closed_eq hf hg)

/-- If two continuous functions are equal on a dense set, then they are equal. -/
lemma continuous.ext_on [t2_space α] {s : set β} (hs : dense s) {f g : β → α}
  (hf : continuous f) (hg : continuous g) (h : eq_on f g s) :
  f = g :=
funext $ λ x, h.closure hf hg (hs x)

lemma function.left_inverse.closed_range [t2_space α] {f : α → β} {g : β → α}
  (h : function.left_inverse f g) (hf : continuous f) (hg : continuous g) :
  is_closed (range g) :=
have eq_on (g ∘ f) id (closure $ range g),
  from h.right_inv_on_range.eq_on.closure (hg.comp hf) continuous_id,
is_closed_of_closure_subset $ λ x hx,
calc x = g (f x) : (this hx).symm
   ... ∈ _ : mem_range_self _

lemma function.left_inverse.closed_embedding [t2_space α] {f : α → β} {g : β → α}
  (h : function.left_inverse f g) (hf : continuous f) (hg : continuous g) :
  closed_embedding g :=
⟨h.embedding hf hg, h.closed_range hf hg⟩

lemma diagonal_eq_range_diagonal_map {α : Type*} : {p:α×α | p.1 = p.2} = range (λx, (x,x)) :=
ext $ assume p, iff.intro
  (assume h, ⟨p.1, prod.ext_iff.2 ⟨rfl, h⟩⟩)
  (assume ⟨x, hx⟩, show p.1 = p.2, by rw ←hx)

lemma prod_subset_compl_diagonal_iff_disjoint {α : Type*} {s t : set α} :
  set.prod s t ⊆ {p:α×α | p.1 = p.2}ᶜ ↔ s ∩ t = ∅ :=
by rw [eq_empty_iff_forall_not_mem, subset_compl_comm,
       diagonal_eq_range_diagonal_map, range_subset_iff]; simp

lemma compact_compact_separated [t2_space α] {s t : set α}
  (hs : is_compact s) (ht : is_compact t) (hst : s ∩ t = ∅) :
  ∃u v : set α, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ u ∩ v = ∅ :=
by simp only [prod_subset_compl_diagonal_iff_disjoint.symm] at ⊢ hst;
   exact generalized_tube_lemma hs ht is_closed_diagonal.is_open_compl hst

/-- In a `t2_space`, every compact set is closed. -/
lemma is_compact.is_closed [t2_space α] {s : set α} (hs : is_compact s) : is_closed s :=
is_open_compl_iff.1 $ is_open_iff_forall_mem_open.mpr $ assume x hx,
  let ⟨u, v, uo, vo, su, xv, uv⟩ :=
    compact_compact_separated hs (is_compact_singleton : is_compact {x})
      (by rwa [inter_comm, ←subset_compl_iff_disjoint, singleton_subset_iff]) in
  have v ⊆ sᶜ, from
    subset_compl_comm.mp (subset.trans su (subset_compl_iff_disjoint.mpr uv)),
⟨v, this, vo, by simpa using xv⟩

/-- If `V : ι → set α` is a decreasing family of compact sets then any neighborhood of
`⋂ i, V i` contains some `V i`. This is a version of `exists_subset_nhd_of_compact'` where we
don't need to assume each `V i` closed because it follows from compactness since `α` is
assumed to be Hausdorff. -/
lemma exists_subset_nhd_of_compact [t2_space α] {ι : Type*} [nonempty ι] {V : ι → set α}
  (hV : directed (⊇) V) (hV_cpct : ∀ i, is_compact (V i)) {U : set α}
  (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
exists_subset_nhd_of_compact' hV hV_cpct (λ i, (hV_cpct i).is_closed) hU

lemma compact_exhaustion.is_closed [t2_space α] (K : compact_exhaustion α) (n : ℕ) :
  is_closed (K n) :=
(K.is_compact n).is_closed

lemma is_compact.inter [t2_space α] {s t : set α} (hs : is_compact s) (ht : is_compact t) :
  is_compact (s ∩ t) :=
hs.inter_right $ ht.is_closed

lemma compact_closure_of_subset_compact [t2_space α] {s t : set α} (ht : is_compact t) (h : s ⊆ t) :
  is_compact (closure s) :=
compact_of_is_closed_subset ht is_closed_closure (closure_minimal h ht.is_closed)

lemma image_closure_of_compact [t2_space β]
  {s : set α} (hs : is_compact (closure s)) {f : α → β} (hf : continuous_on f (closure s)) :
  f '' closure s = closure (f '' s) :=
subset.antisymm hf.image_closure $ closure_minimal (image_subset f subset_closure)
  (hs.image_of_continuous_on hf).is_closed

/-- If a compact set is covered by two open sets, then we can cover it by two compact subsets. -/
lemma is_compact.binary_compact_cover [t2_space α] {K U V : set α} (hK : is_compact K)
  (hU : is_open U) (hV : is_open V) (h2K : K ⊆ U ∪ V) :
  ∃ K₁ K₂ : set α, is_compact K₁ ∧ is_compact K₂ ∧ K₁ ⊆ U ∧ K₂ ⊆ V ∧ K = K₁ ∪ K₂ :=
begin
  rcases compact_compact_separated (hK.diff hU) (hK.diff hV)
    (by rwa [diff_inter_diff, diff_eq_empty]) with ⟨O₁, O₂, h1O₁, h1O₂, h2O₁, h2O₂, hO⟩,
  refine ⟨_, _, hK.diff h1O₁, hK.diff h1O₂,
    by rwa [diff_subset_comm], by rwa [diff_subset_comm], by rw [← diff_inter, hO, diff_empty]⟩
end

lemma continuous.is_closed_map [compact_space α] [t2_space β] {f : α → β} (h : continuous f) :
  is_closed_map f :=
λ s hs, (hs.is_compact.image h).is_closed

lemma continuous.closed_embedding [compact_space α] [t2_space β] {f : α → β} (h : continuous f)
  (hf : function.injective f) : closed_embedding f :=
closed_embedding_of_continuous_injective_closed h hf h.is_closed_map

section
open finset function
/-- For every finite open cover `Uᵢ` of a compact set, there exists a compact cover `Kᵢ ⊆ Uᵢ`. -/
lemma is_compact.finite_compact_cover [t2_space α] {s : set α} (hs : is_compact s)
  {ι} (t : finset ι) (U : ι → set α) (hU : ∀ i ∈ t, is_open (U i)) (hsC : s ⊆ ⋃ i ∈ t, U i) :
  ∃ K : ι → set α, (∀ i, is_compact (K i)) ∧ (∀i, K i ⊆ U i) ∧ s = ⋃ i ∈ t, K i :=
begin
  classical,
  induction t using finset.induction with x t hx ih generalizing U hU s hs hsC,
  { refine ⟨λ _, ∅, λ i, is_compact_empty, λ i, empty_subset _, _⟩, simpa only [subset_empty_iff,
      finset.not_mem_empty, Union_neg, Union_empty, not_false_iff] using hsC },
  simp only [finset.set_bUnion_insert] at hsC,
  simp only [finset.mem_insert] at hU,
  have hU' : ∀ i ∈ t, is_open (U i) := λ i hi, hU i (or.inr hi),
  rcases hs.binary_compact_cover (hU x (or.inl rfl)) (is_open_bUnion hU') hsC
    with ⟨K₁, K₂, h1K₁, h1K₂, h2K₁, h2K₂, hK⟩,
  rcases ih U hU' h1K₂ h2K₂ with ⟨K, h1K, h2K, h3K⟩,
  refine ⟨update K x K₁, _, _, _⟩,
  { intros i, by_cases hi : i = x,
    { simp only [update_same, hi, h1K₁] },
    { rw [← ne.def] at hi, simp only [update_noteq hi, h1K] }},
  { intros i, by_cases hi : i = x,
    { simp only [update_same, hi, h2K₁] },
    { rw [← ne.def] at hi, simp only [update_noteq hi, h2K] }},
  { simp only [set_bUnion_insert_update _ hx, hK, h3K] }
end
end

lemma locally_compact_of_compact_nhds [t2_space α] (h : ∀ x : α, ∃ s, s ∈ 𝓝 x ∧ is_compact s) :
  locally_compact_space α :=
⟨assume x n hn,
  let ⟨u, un, uo, xu⟩ := mem_nhds_iff.mp hn in
  let ⟨k, kx, kc⟩ := h x in
  -- K is compact but not necessarily contained in N.
  -- K \ U is again compact and doesn't contain x, so
  -- we may find open sets V, W separating x from K \ U.
  -- Then K \ W is a compact neighborhood of x contained in U.
  let ⟨v, w, vo, wo, xv, kuw, vw⟩ :=
    compact_compact_separated is_compact_singleton (is_compact.diff kc uo)
      (by rw [singleton_inter_eq_empty]; exact λ h, h.2 xu) in
  have wn : wᶜ ∈ 𝓝 x, from
   mem_nhds_iff.mpr
     ⟨v, subset_compl_iff_disjoint.mpr vw, vo, singleton_subset_iff.mp xv⟩,
  ⟨k \ w,
   filter.inter_mem_sets kx wn,
   subset.trans (diff_subset_comm.mp kuw) un,
   kc.diff wo⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance locally_compact_of_compact [t2_space α] [compact_space α] : locally_compact_space α :=
locally_compact_of_compact_nhds (assume x, ⟨univ, is_open_univ.mem_nhds trivial, compact_univ⟩)

/-- In a locally compact T₂ space, every point has an open neighborhood with compact closure -/
lemma exists_open_with_compact_closure [locally_compact_space α] [t2_space α] (x : α) :
  ∃ (U : set α), is_open U ∧ x ∈ U ∧ is_compact (closure U) :=
begin
  rcases exists_compact_mem_nhds x with ⟨K, hKc, hxK⟩,
  rcases mem_nhds_iff.1 hxK with ⟨t, h1t, h2t, h3t⟩,
  exact ⟨t, h2t, h3t, compact_closure_of_subset_compact hKc h1t⟩
end

end separation

section regularity

/-- A T₃ space, also known as a regular space (although this condition sometimes
  omits T₂), is one in which for every closed `C` and `x ∉ C`, there exist
  disjoint open sets containing `x` and `C` respectively. -/
class regular_space (α : Type u) [topological_space α] extends t0_space α : Prop :=
(regular : ∀{s:set α} {a}, is_closed s → a ∉ s → ∃t, is_open t ∧ s ⊆ t ∧ 𝓝[t] a = ⊥)

@[priority 100] -- see Note [lower instance priority]
instance regular_space.t1_space [regular_space α] : t1_space α :=
begin
  rw t1_iff_exists_open,
  intros x y hxy,
  obtain ⟨U, hU, h⟩ := t0_space.t0 x y hxy,
  cases h,
  { exact ⟨U, hU, h⟩ },
  { obtain ⟨R, hR, hh⟩ := regular_space.regular (is_closed_compl_iff.mpr hU) (not_not.mpr h.1),
    obtain ⟨V, hV, hhh⟩ := mem_nhds_iff.1 (filter.inf_principal_eq_bot.1 hh.2),
    exact ⟨R, hR, hh.1 (mem_compl h.2), hV hhh.2⟩ }
end

lemma nhds_is_closed [regular_space α] {a : α} {s : set α} (h : s ∈ 𝓝 a) :
  ∃ t ∈ 𝓝 a, t ⊆ s ∧ is_closed t :=
let ⟨s', h₁, h₂, h₃⟩ := mem_nhds_iff.mp h in
have ∃t, is_open t ∧ s'ᶜ ⊆ t ∧ 𝓝[t] a = ⊥,
  from regular_space.regular (is_closed_compl_iff.mpr h₂) (not_not_intro h₃),
let ⟨t, ht₁, ht₂, ht₃⟩ := this in
⟨tᶜ,
  mem_sets_of_eq_bot $ by rwa [compl_compl],
  subset.trans (compl_subset_comm.1 ht₂) h₁,
  is_closed_compl_iff.mpr ht₁⟩

lemma closed_nhds_basis [regular_space α] (a : α) :
  (𝓝 a).has_basis (λ s : set α, s ∈ 𝓝 a ∧ is_closed s) id :=
⟨λ t, ⟨λ t_in, let ⟨s, s_in, h_st, h⟩ := nhds_is_closed t_in in ⟨s, ⟨s_in, h⟩, h_st⟩,
       λ ⟨s, ⟨s_in, hs⟩, hst⟩, mem_sets_of_superset s_in hst⟩⟩

instance subtype.regular_space [regular_space α] {p : α → Prop} : regular_space (subtype p) :=
⟨begin
   intros s a hs ha,
   rcases is_closed_induced_iff.1 hs with ⟨s, hs', rfl⟩,
   rcases regular_space.regular hs' ha with ⟨t, ht, hst, hat⟩,
   refine ⟨coe ⁻¹' t, is_open_induced ht, preimage_mono hst, _⟩,
   rw [nhds_within, nhds_induced, ← comap_principal, ← comap_inf, ← nhds_within, hat, comap_bot]
 end⟩

variable (α)
@[priority 100] -- see Note [lower instance priority]
instance regular_space.t2_space [regular_space α] : t2_space α :=
⟨λ x y hxy,
let ⟨s, hs, hys, hxs⟩ := regular_space.regular is_closed_singleton
    (mt mem_singleton_iff.1 hxy),
  ⟨t, hxt, u, hsu, htu⟩ := empty_in_sets_eq_bot.2 hxs,
  ⟨v, hvt, hv, hxv⟩ := mem_nhds_iff.1 hxt in
⟨v, s, hv, hs, hxv, singleton_subset_iff.1 hys,
eq_empty_of_subset_empty $ λ z ⟨hzv, hzs⟩, htu ⟨hvt hzv, hsu hzs⟩⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance regular_space.t2_5_space [regular_space α] : t2_5_space α :=
⟨λ x y hxy,
let ⟨U, V, hU, hV, hh_1, hh_2, hUV⟩ := t2_space.t2 x y hxy,
  hxcV := not_not.mpr ((interior_maximal (subset_compl_iff_disjoint.mpr hUV) hU) hh_1),
  ⟨R, hR, hh⟩ := regular_space.regular is_closed_closure (by rwa closure_eq_compl_interior_compl),
  ⟨A, hA, hhh⟩ := mem_nhds_iff.1 (filter.inf_principal_eq_bot.1 hh.2) in
⟨A, V, hhh.1, hV, subset_eq_empty ((closure V).inter_subset_inter_left
  (subset.trans (closure_minimal hA (is_closed_compl_iff.mpr hR)) (compl_subset_compl.mpr hh.1)))
  (compl_inter_self (closure V)), hhh.2, hh_2⟩⟩

variable {α}

/-- Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and `y ∈ V₂ ⊆ U₂`,
with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint. -/
lemma disjoint_nested_nhds [regular_space α] {x y : α} (h : x ≠ y) :
  ∃ (U₁ V₁ ∈ 𝓝 x) (U₂ V₂ ∈ 𝓝 y), is_closed V₁ ∧ is_closed V₂ ∧ is_open U₁ ∧ is_open U₂ ∧
  V₁ ⊆ U₁ ∧ V₂ ⊆ U₂ ∧ U₁ ∩ U₂ = ∅ :=
begin
  rcases t2_separation h with ⟨U₁, U₂, U₁_op, U₂_op, x_in, y_in, H⟩,
  rcases nhds_is_closed (is_open.mem_nhds U₁_op x_in) with ⟨V₁, V₁_in, h₁, V₁_closed⟩,
  rcases nhds_is_closed (is_open.mem_nhds U₂_op y_in) with ⟨V₂, V₂_in, h₂, V₂_closed⟩,
  use [U₁, V₁, mem_sets_of_superset V₁_in h₁, V₁_in,
       U₂, V₂, mem_sets_of_superset V₂_in h₂, V₂_in],
  tauto
end

end regularity

section normality

/-- A T₄ space, also known as a normal space (although this condition sometimes
  omits T₂), is one in which for every pair of disjoint closed sets `C` and `D`,
  there exist disjoint open sets containing `C` and `D` respectively. -/
class normal_space (α : Type u) [topological_space α] extends t1_space α : Prop :=
(normal : ∀ s t : set α, is_closed s → is_closed t → disjoint s t →
  ∃ u v, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v)

theorem normal_separation [normal_space α] {s t : set α}
  (H1 : is_closed s) (H2 : is_closed t) (H3 : disjoint s t) :
  ∃ u v, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v :=
normal_space.normal s t H1 H2 H3

theorem normal_exists_closure_subset [normal_space α] {s t : set α} (hs : is_closed s)
  (ht : is_open t) (hst : s ⊆ t) :
  ∃ u, is_open u ∧ s ⊆ u ∧ closure u ⊆ t :=
begin
  have : disjoint s tᶜ, from λ x ⟨hxs, hxt⟩, hxt (hst hxs),
  rcases normal_separation hs (is_closed_compl_iff.2 ht) this
    with ⟨s', t', hs', ht', hss', htt', hs't'⟩,
  refine ⟨s', hs', hss',
    subset.trans (closure_minimal _ (is_closed_compl_iff.2 ht')) (compl_subset_comm.1 htt')⟩,
  exact λ x hxs hxt, hs't' ⟨hxs, hxt⟩
end

@[priority 100] -- see Note [lower instance priority]
instance normal_space.regular_space [normal_space α] : regular_space α :=
{ regular := λ s x hs hxs, let ⟨u, v, hu, hv, hsu, hxv, huv⟩ :=
    normal_separation hs is_closed_singleton
      (λ _ ⟨hx, hy⟩, hxs $ mem_of_eq_of_mem (eq_of_mem_singleton hy).symm hx) in
    ⟨u, hu, hsu, filter.empty_in_sets_eq_bot.1 $ filter.mem_inf_sets.2
      ⟨v, is_open.mem_nhds hv (singleton_subset_iff.1 hxv), u, filter.mem_principal_self u,
        inter_comm u v ▸ huv⟩⟩ }

-- We can't make this an instance because it could cause an instance loop.
lemma normal_of_compact_t2 [compact_space α] [t2_space α] : normal_space α :=
begin
  refine ⟨assume s t hs ht st, _⟩,
  simp only [disjoint_iff],
  exact compact_compact_separated hs.is_compact ht.is_compact st.eq_bot
end

end normality

/-- In a compact t2 space, the connected component of a point equals the intersection of all
its clopen neighbourhoods. -/
lemma connected_component_eq_Inter_clopen [t2_space α] [compact_space α] {x : α} :
  connected_component x = ⋂ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, Z :=
begin
  apply eq_of_subset_of_subset connected_component_subset_Inter_clopen,
  -- Reduce to showing that the clopen intersection is connected.
  refine is_preconnected.subset_connected_component _ (mem_Inter.2 (λ Z, Z.2.2)),
  -- We do this by showing that any disjoint cover by two closed sets implies
  -- that one of these closed sets must contain our whole thing.
  -- To reduce to the case where the cover is disjoint on all of `α` we need that `s` is closed
  have hs : @is_closed _ _inst_1 (⋂ (Z : {Z : set α // is_clopen Z ∧ x ∈ Z}), Z) :=
    is_closed_Inter (λ Z, Z.2.1.2),
  rw (is_preconnected_iff_subset_of_fully_disjoint_closed hs),
  intros a b ha hb hab ab_empty,
  haveI := @normal_of_compact_t2 α _ _ _,
  -- Since our space is normal, we get two larger disjoint open sets containing the disjoint
  -- closed sets. If we can show that our intersection is a subset of any of these we can then
  -- "descend" this to show that it is a subset of either a or b.
  rcases normal_separation ha hb (disjoint_iff.2 ab_empty) with ⟨u, v, hu, hv, hau, hbv, huv⟩,
  -- If we can find a clopen set around x, contained in u ∪ v, we get a disjoint decomposition
  -- Z = Z ∩ u ∪ Z ∩ v of clopen sets. The intersection of all clopen neighbourhoods will then lie
  -- in whichever of u or v x lies in and hence will be a subset of either a or b.
  suffices : ∃ (Z : set α), is_clopen Z ∧ x ∈ Z ∧ Z ⊆ u ∪ v,
  { cases this with Z H,
    rw [disjoint_iff_inter_eq_empty] at huv,
    have H1 := is_clopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hu hv huv,
    rw [union_comm] at H,
    have H2 := is_clopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hv hu (inter_comm u v ▸ huv),
    by_cases (x ∈ u),
    -- The x ∈ u case.
    { left,
      suffices : (⋂ (Z : {Z : set α // is_clopen Z ∧ x ∈ Z}), ↑Z) ⊆ u,
      { rw ←set.disjoint_iff_inter_eq_empty at huv,
        replace hab : (⋂ (Z : {Z // is_clopen Z ∧ x ∈ Z}), ↑Z) ≤ a ∪ b := hab,
        replace this : (⋂ (Z : {Z // is_clopen Z ∧ x ∈ Z}), ↑Z) ≤ u := this,
        exact disjoint.left_le_of_le_sup_right hab (huv.mono this hbv) },
      { apply subset.trans _ (inter_subset_right Z u),
        apply Inter_subset (λ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, ↑Z)
          ⟨Z ∩ u, H1, mem_inter H.2.1 h⟩ } },
    -- If x ∉ u, we get x ∈ v since x ∈ u ∪ v. The rest is then like the x ∈ u case.
    have h1 : x ∈ v,
    { cases (mem_union x u v).1 (mem_of_subset_of_mem (subset.trans hab
        (union_subset_union hau hbv)) (mem_Inter.2 (λ i, i.2.2))) with h1 h1,
      { exfalso, exact h h1},
      { exact h1} },
    right,
    suffices : (⋂ (Z : {Z : set α // is_clopen Z ∧ x ∈ Z}), ↑Z) ⊆ v,
    { rw [inter_comm, ←set.disjoint_iff_inter_eq_empty] at huv,
      replace hab : (⋂ (Z : {Z // is_clopen Z ∧ x ∈ Z}), ↑Z) ≤ a ∪ b := hab,
      replace this : (⋂ (Z : {Z // is_clopen Z ∧ x ∈ Z}), ↑Z) ≤ v := this,
      exact disjoint.left_le_of_le_sup_left hab (huv.mono this hau) },
    { apply subset.trans _ (inter_subset_right Z v),
      apply Inter_subset (λ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, ↑Z)
        ⟨Z ∩ v, H2, mem_inter H.2.1 h1⟩ } },
  -- Now we find the required Z. We utilize the fact that X \ u ∪ v will be compact,
  -- so there must be some finite intersection of clopen neighbourhoods of X disjoint to it,
  -- but a finite intersection of clopen sets is clopen so we let this be our Z.
  have H1 := ((is_closed_compl_iff.2 (hu.union hv)).is_compact.inter_Inter_nonempty
    (λ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, Z) (λ Z, Z.2.1.2)),
  rw [←not_imp_not, not_forall, not_nonempty_iff_eq_empty, inter_comm] at H1,
  have huv_union := subset.trans hab (union_subset_union hau hbv),
  rw [← compl_compl (u ∪ v), subset_compl_iff_disjoint] at huv_union,
  cases H1 huv_union with Zi H2,
  refine ⟨(⋂ (U ∈ Zi), subtype.val U), _, _, _⟩,
  { exact is_clopen_bInter (λ Z hZ, Z.2.1) },
  { exact mem_bInter_iff.2 (λ Z hZ, Z.2.2) },
  { rwa [not_nonempty_iff_eq_empty, inter_comm, ←subset_compl_iff_disjoint, compl_compl] at H2 }
end

section profinite

open topological_space

variables [t2_space α]

/-- A Hausdorff space with a clopen basis is totally separated. -/
lemma tot_sep_of_zero_dim (h : is_topological_basis {s : set α | is_clopen s}) :
    totally_separated_space α :=
begin
  constructor,
  rintros x - y - hxy,
  obtain ⟨u, v, hu, hv, xu, yv, disj⟩ := t2_separation hxy,
  obtain ⟨w, hw : is_clopen w, xw, wu⟩ := (is_topological_basis.mem_nhds_iff h).1
    (is_open.mem_nhds hu xu),
  refine ⟨w, wᶜ, hw.1, (is_clopen_compl_iff.2 hw).1, xw, _, _, set.inter_compl_self w⟩,
  { intro h,
    have : y ∈ u ∩ v := ⟨wu h, yv⟩,
    rwa disj at this },
  rw set.union_compl_self,
end

variables [compact_space α]

/-- A compact Hausdorff space is totally disconnected if and only if it is totally separated, this
  is also true for locally compact spaces. -/
theorem compact_t2_tot_disc_iff_tot_sep :
totally_disconnected_space α ↔ totally_separated_space α :=
begin
  split,
  { intro h, constructor,
    rintros x - y -,
    contrapose!,
    intros hyp,
    suffices : x ∈ connected_component y,
      by simpa [totally_disconnected_space_iff_connected_component_singleton.1 h y,
                mem_singleton_iff],
    rw [connected_component_eq_Inter_clopen, mem_Inter],
    rintro ⟨w : set α, hw : is_clopen w, hy : y ∈ w⟩,
    by_contra hx,
    simpa using hyp wᶜ w (is_open_compl_iff.mpr hw.2) hw.1 hx hy },
  apply totally_separated_space.totally_disconnected_space,
end

variables [totally_disconnected_space α]

lemma nhds_basis_clopen (x : α) : (𝓝 x).has_basis (λ s : set α, x ∈ s ∧ is_clopen s) id :=
⟨λ U, begin
  split,
  { have : connected_component x = {x},
      from totally_disconnected_space_iff_connected_component_singleton.mp ‹_› x,
    rw connected_component_eq_Inter_clopen at this,
    intros hU,
    let N := {Z // is_clopen Z ∧ x ∈ Z},
    suffices : ∃ Z : N, Z.val ⊆ U,
    { rcases this with ⟨⟨s, hs, hs'⟩, hs''⟩,
      exact ⟨s, ⟨hs', hs⟩, hs''⟩ },
    haveI : nonempty N := ⟨⟨univ, is_clopen_univ, mem_univ x⟩⟩,
    have hNcl : ∀ Z : N, is_closed Z.val := (λ Z, Z.property.1.2),
    have hdir : directed superset (λ Z : N, Z.val),
    { rintros ⟨s, hs, hxs⟩ ⟨t, ht, hxt⟩,
      exact ⟨⟨s ∩ t, hs.inter ht, ⟨hxs, hxt⟩⟩, inter_subset_left s t, inter_subset_right s t⟩ },
    have h_nhd: ∀ y ∈ (⋂ Z : N, Z.val), U ∈ 𝓝 y,
    { intros y y_in,
      erw [this, mem_singleton_iff] at y_in,
      rwa y_in },
    exact exists_subset_nhd_of_compact_space hdir hNcl h_nhd },
  { rintro ⟨V, ⟨hxV, V_op, -⟩, hUV : V ⊆ U⟩,
    rw mem_nhds_iff,
    exact ⟨V, hUV, V_op, hxV⟩ }
end⟩

lemma is_topological_basis_clopen : is_topological_basis {s : set α | is_clopen s} :=
begin
  apply is_topological_basis_of_open_of_nhds (λ U (hU : is_clopen U), hU.1),
  intros x U hxU U_op,
  have : U ∈ 𝓝 x,
  from is_open.mem_nhds U_op hxU,
  rcases (nhds_basis_clopen x).mem_iff.mp this with ⟨V, ⟨hxV, hV⟩, hVU : V ⊆ U⟩,
  use V,
  tauto
end

/-- Every member of an open set in a compact Hausdorff totally disconnected space
  is contained in a clopen set contained in the open set.  -/
lemma compact_exists_clopen_in_open {x : α} {U : set α} (is_open : is_open U) (memU : x ∈ U) :
    ∃ (V : set α) (hV : is_clopen V), x ∈ V ∧ V ⊆ U :=
  (is_topological_basis.mem_nhds_iff is_topological_basis_clopen).1 (is_open.mem_nhds memU)

end profinite

section locally_compact

open topological_space

variables {H : Type*} [topological_space H] [locally_compact_space H] [t2_space H]

/-- A locally compact Hausdorff totally disconnected space has a basis with clopen elements. -/
lemma loc_compact_Haus_tot_disc_of_zero_dim [totally_disconnected_space H] :
  is_topological_basis {s : set H | is_clopen s} :=
begin
  refine is_topological_basis_of_open_of_nhds (λ u hu, hu.1) _,
  rintros x U memU hU,
  obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU memU,
  obtain ⟨t, h, ht, xt⟩ := mem_interior.1 xs,
  let u : set s := (coe : s → H)⁻¹' (interior s),
  have u_open_in_s : is_open u := is_open_interior.preimage continuous_subtype_coe,
  let X : s := ⟨x, h xt⟩,
  have Xu : X ∈ u := xs,
  haveI : compact_space s := is_compact_iff_compact_space.1 comp,
  obtain ⟨V : set s, clopen_in_s, Vx, V_sub⟩ := compact_exists_clopen_in_open u_open_in_s Xu,
  have V_clopen : is_clopen ((coe : s → H) '' V),
  { refine ⟨_, (comp.is_closed.closed_embedding_subtype_coe.closed_iff_image_closed).1
               clopen_in_s.2⟩,
    let v : set u := (coe : u → s)⁻¹' V,
    have : (coe : u → H) = (coe : s → H) ∘ (coe : u → s) := rfl,
    have f0 : embedding (coe : u → H) := embedding_subtype_coe.comp embedding_subtype_coe,
    have f1 : open_embedding (coe : u → H),
    { refine ⟨f0, _⟩,
      { have : set.range (coe : u → H) = interior s,
        { rw [this, set.range_comp, subtype.range_coe, subtype.image_preimage_coe],
          apply set.inter_eq_self_of_subset_left interior_subset, },
        rw this,
        apply is_open_interior } },
    have f2 : is_open v := clopen_in_s.1.preimage continuous_subtype_coe,
    have f3 : (coe : s → H) '' V = (coe : u → H) '' v,
    { rw [this, image_comp coe coe, subtype.image_preimage_coe,
          inter_eq_self_of_subset_left V_sub] },
    rw f3,
    apply f1.is_open_map v f2 },
  refine ⟨coe '' V, V_clopen, by simp [Vx, h xt], _⟩,
  transitivity s,
  { simp },
  assumption
end

/-- A locally compact Hausdorff space is totally disconnected
  if and only if it is totally separated. -/
theorem loc_compact_t2_tot_disc_iff_tot_sep :
  totally_disconnected_space H ↔ totally_separated_space H :=
begin
  split,
  { introI h,
    exact tot_sep_of_zero_dim loc_compact_Haus_tot_disc_of_zero_dim, },
  apply totally_separated_space.totally_disconnected_space,
end

end locally_compact

section connected_component_setoid
local attribute [instance] connected_component_setoid

/-- `connected_components α` is Hausdorff when `α` is Hausdorff and compact -/
instance connected_components.t2 [t2_space α] [compact_space α] :
  t2_space (connected_components α) :=
begin
  -- Proof follows that of: https://stacks.math.columbia.edu/tag/0900
  -- Fix 2 distinct connected components, with points a and b
  refine ⟨λ x y, quotient.induction_on x (quotient.induction_on y (λ a b ne, _))⟩,
  rw connected_component_nrel_iff at ne,
  have h := connected_component_disjoint ne,
  -- write ⟦b⟧ as the intersection of all clopen subsets containing it
  rw [connected_component_eq_Inter_clopen, disjoint_iff_inter_eq_empty, inter_comm] at h,
  -- Now we show that this can be reduced to some clopen containing ⟦b⟧ being disjoint to ⟦a⟧
  cases is_closed_connected_component.is_compact.elim_finite_subfamily_closed _ _ h
    with fin_a ha,
  swap, { exact λ Z, Z.2.1.2 },
  set U : set α := (⋂ (i : {Z // is_clopen Z ∧ b ∈ Z}) (H : i ∈ fin_a), i) with hU,
  rw ←hU at ha,
  have hu_clopen : is_clopen U := is_clopen_bInter (λ i j, i.2.1),
  -- This clopen and its complement will separate the points corresponding to ⟦a⟧ and ⟦b⟧
  use [quotient.mk '' U, quotient.mk '' Uᶜ],
  -- Using the fact that clopens are unions of connected components, we show that
  -- U and Uᶜ is the preimage of a clopen set in the quotient
  have hu : quotient.mk ⁻¹' (quotient.mk '' U) = U :=
    (connected_components_preimage_image U ▸ eq.symm) hu_clopen.eq_union_connected_components,
  have huc : quotient.mk ⁻¹' (quotient.mk '' Uᶜ) = Uᶜ :=
    (connected_components_preimage_image Uᶜ ▸ eq.symm)
      (is_clopen.compl hu_clopen).eq_union_connected_components,
  -- showing that U and Uᶜ are open and separates ⟦a⟧ and ⟦b⟧
  refine ⟨_,_,_,_,_⟩,
  { rw [(quotient_map_iff.1 quotient_map_quotient_mk).2 _, hu],
    exact hu_clopen.1 },
  { rw [(quotient_map_iff.1 quotient_map_quotient_mk).2 _, huc],
    exact is_open_compl_iff.2 hu_clopen.2 },
  { exact mem_image_of_mem _ (mem_Inter.2 (λ Z, mem_Inter.2 (λ Zmem, Z.2.2))) },
  { apply mem_image_of_mem,
    exact mem_of_subset_of_mem (subset_compl_iff_disjoint.2 ha) (@mem_connected_component _ _ a) },
  apply preimage_injective.2 (@surjective_quotient_mk _ _),
  rw [preimage_inter, preimage_empty, hu, huc, inter_compl_self _],
end

end connected_component_setoid
