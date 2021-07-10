/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov
-/
import data.fintype.basic
import data.sym2
import data.set.finite
/-!
# Simple graphs

This module defines simple graphs on a vertex type `V` as an
irreflexive symmetric relation.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

## Main definitions

* `simple_graph` is a structure for symmetric, irreflexive relations

* `neighbor_set` is the `set` of vertices adjacent to a given vertex

* `common_neighbors` is the intersection of the neighbor sets of two given vertices

* `neighbor_finset` is the `finset` of vertices adjacent to a given vertex,
   if `neighbor_set` is finite

* `incidence_set` is the `set` of edges containing a given vertex

* `incidence_finset` is the `finset` of edges containing a given vertex,
   if `incidence_set` is finite

## Implementation notes

* A locally finite graph is one with instances `∀ v, fintype (G.neighbor_set v)`.

* Given instances `decidable_rel G.adj` and `fintype V`, then the graph
  is locally finite, too.

## Naming Conventions

* If the vertex type of a graph is finite, we refer to its cardinality as `card_verts`.

TODO: This is the simplest notion of an unoriented graph.  This should
eventually fit into a more complete combinatorics hierarchy which
includes multigraphs and directed graphs.  We begin with simple graphs
in order to start learning what the combinatorics hierarchy should
look like.

TODO: Part of this would include defining, for example, subgraphs of a
simple graph.

-/
open finset
universe u

/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent edges;
see `simple_graph.edge_set` for the corresponding edge set.
-/
@[ext]
structure simple_graph (V : Type u) :=
(adj : V → V → Prop)
(sym : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)

/--
Construct the simple graph induced by the given relation.  It
symmetrizes the relation and makes it irreflexive.
-/
def simple_graph.from_rel {V : Type u} (r : V → V → Prop) : simple_graph V :=
{ adj := λ a b, (a ≠ b) ∧ (r a b ∨ r b a),
  sym := λ a b ⟨hn, hr⟩, ⟨hn.symm, hr.symm⟩,
  loopless := λ a ⟨hn, _⟩, hn rfl }

noncomputable instance {V : Type u} [fintype V] : fintype (simple_graph V) :=
by { classical, exact fintype.of_injective simple_graph.adj simple_graph.ext }

@[simp]
lemma simple_graph.from_rel_adj {V : Type u} (r : V → V → Prop) (v w : V) :
  (simple_graph.from_rel r).adj v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
iff.rfl

/--
The complete graph on a type `V` is the simple graph with all pairs of distinct vertices adjacent.
-/
def complete_graph (V : Type u) : simple_graph V :=
{ adj := ne }

instance (V : Type u) : inhabited (simple_graph V) :=
⟨complete_graph V⟩

instance complete_graph_adj_decidable (V : Type u) [decidable_eq V] :
  decidable_rel (complete_graph V).adj :=
λ v w, not.decidable

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/-- `G.neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set (v : V) : set V := set_of (G.adj v)

instance neighbor_set.mem_decidable (v : V) [decidable_rel G.adj] :
  decidable_pred (∈ (G.neighbor_set v)) := by { unfold neighbor_set, apply_instance }

lemma ne_of_adj {a b : V} (hab : G.adj a b) : a ≠ b :=
by { rintro rfl, exact G.loopless a hab }

/--
The edges of G consist of the unordered pairs of vertices related by
`G.adj`.
-/
def edge_set : set (sym2 V) := sym2.from_rel G.sym

/--
The `incidence_set` is the set of edges incident to a given vertex.
-/
def incidence_set (v : V) : set (sym2 V) := {e ∈ G.edge_set | v ∈ e}

lemma incidence_set_subset (v : V) : G.incidence_set v ⊆ G.edge_set :=
λ _ h, h.1

@[simp]
lemma mem_edge_set {v w : V} : ⟦(v, w)⟧ ∈ G.edge_set ↔ G.adj v w :=
by refl

/--
Two vertices are adjacent iff there is an edge between them.  The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`.
-/
lemma adj_iff_exists_edge {v w : V} :
  G.adj v w ↔ v ≠ w ∧ ∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e :=
begin
  refine ⟨λ _, ⟨G.ne_of_adj ‹_›, ⟦(v,w)⟧, _⟩, _⟩,
  { simpa },
  { rintro ⟨hne, e, he, hv⟩,
    rw sym2.elems_iff_eq hne at hv,
    subst e,
    rwa mem_edge_set at he }
end

lemma edge_other_ne {e : sym2 V} (he : e ∈ G.edge_set) {v : V} (h : v ∈ e) : h.other ≠ v :=
begin
  erw [← sym2.mem_other_spec h, sym2.eq_swap] at he,
  exact G.ne_of_adj he,
end

instance decidable_mem_edge_set [decidable_rel G.adj] :
  decidable_pred (∈ G.edge_set) := sym2.from_rel.decidable_pred _

instance edges_fintype [decidable_eq V] [fintype V] [decidable_rel G.adj] :
  fintype G.edge_set := subtype.fintype _

instance decidable_mem_incidence_set [decidable_eq V] [decidable_rel G.adj] (v : V) :
  decidable_pred (∈ G.incidence_set v) := λ e, and.decidable

/--
The `edge_set` of the graph as a `finset`.
-/
def edge_finset [decidable_eq V] [fintype V] [decidable_rel G.adj] : finset (sym2 V) :=
set.to_finset G.edge_set

@[simp] lemma mem_edge_finset [decidable_eq V] [fintype V] [decidable_rel G.adj] (e : sym2 V) :
  e ∈ G.edge_finset ↔ e ∈ G.edge_set :=
set.mem_to_finset

@[simp] lemma edge_set_univ_card [decidable_eq V] [fintype V] [decidable_rel G.adj] :
  (univ : finset G.edge_set).card = G.edge_finset.card :=
fintype.card_of_subtype G.edge_finset (mem_edge_finset _)

@[simp] lemma irrefl {v : V} : ¬G.adj v v := G.loopless v

lemma edge_symm (u v : V) : G.adj u v ↔ G.adj v u := ⟨λ x, G.sym x, λ x, G.sym x⟩

@[symm] lemma edge_symm' {u v : V} (h : G.adj u v) : G.adj v u := G.sym h

@[simp] lemma mem_neighbor_set (v w : V) : w ∈ G.neighbor_set v ↔ G.adj v w :=
iff.rfl

@[simp] lemma mem_incidence_set (v w : V) : ⟦(v, w)⟧ ∈ G.incidence_set v ↔ G.adj v w :=
by simp [incidence_set]

lemma mem_incidence_iff_neighbor {v w : V} : ⟦(v, w)⟧ ∈ G.incidence_set v ↔ w ∈ G.neighbor_set v :=
by simp only [mem_incidence_set, mem_neighbor_set]

lemma adj_incidence_set_inter {v : V} {e : sym2 V} (he : e ∈ G.edge_set) (h : v ∈ e) :
  G.incidence_set v ∩ G.incidence_set h.other = {e} :=
begin
  ext e',
  simp only [incidence_set, set.mem_sep_eq, set.mem_inter_eq, set.mem_singleton_iff],
  split,
  { intro h', rw ←sym2.mem_other_spec h,
    exact (sym2.elems_iff_eq (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩, },
  { rintro rfl, use [he, h, he], apply sym2.mem_other_mem, },
end

/--
The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`.
-/
def common_neighbors (v w : V) : set V := G.neighbor_set v ∩ G.neighbor_set w

lemma common_neighbors_eq (v w : V) :
  G.common_neighbors v w = G.neighbor_set v ∩ G.neighbor_set w := rfl

lemma mem_common_neighbors {u v w : V} : u ∈ G.common_neighbors v w ↔ G.adj v u ∧ G.adj w u :=
by simp [common_neighbors]

lemma common_neighbors_symm (v w : V) : G.common_neighbors v w = G.common_neighbors w v :=
by { rw [common_neighbors, set.inter_comm], refl }

lemma not_mem_common_neighbors_left (v w : V) : v ∉ G.common_neighbors v w :=
λ h, ne_of_adj G h.1 rfl

lemma not_mem_common_neighbors_right (v w : V) : w ∉ G.common_neighbors v w :=
λ h, ne_of_adj G h.2 rfl

lemma common_neighbors_subset_neighbor_set (v w : V) : G.common_neighbors v w ⊆ G.neighbor_set v :=
by simp [common_neighbors]

instance decidable_mem_common_neighbors [decidable_rel G.adj] (v w : V) :
  decidable_pred (∈ G.common_neighbors v w) :=
λ a, and.decidable

section incidence
variable [decidable_eq V]

/--
Given an edge incident to a particular vertex, get the other vertex on the edge.
-/
def other_vertex_of_incident {v : V} {e : sym2 V} (h : e ∈ G.incidence_set v) : V := h.2.other'

lemma edge_mem_other_incident_set {v : V} {e : sym2 V} (h : e ∈ G.incidence_set v) :
  e ∈ G.incidence_set (G.other_vertex_of_incident h) :=
by { use h.1, simp [other_vertex_of_incident, sym2.mem_other_mem'] }

lemma incidence_other_prop {v : V} {e : sym2 V} (h : e ∈ G.incidence_set v) :
  G.other_vertex_of_incident h ∈ G.neighbor_set v :=
by { cases h with he hv, rwa [←sym2.mem_other_spec' hv, mem_edge_set] at he }

@[simp]
lemma incidence_other_neighbor_edge {v w : V} (h : w ∈ G.neighbor_set v) :
  G.other_vertex_of_incident (G.mem_incidence_iff_neighbor.mpr h) = w :=
sym2.congr_right.mp (sym2.mem_other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

/--
There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex.
-/
@[simps] def incidence_set_equiv_neighbor_set (v : V) : G.incidence_set v ≃ G.neighbor_set v :=
{ to_fun := λ e, ⟨G.other_vertex_of_incident e.2, G.incidence_other_prop e.2⟩,
  inv_fun := λ w, ⟨⟦(v, w.1)⟧, G.mem_incidence_iff_neighbor.mpr w.2⟩,
  left_inv := λ x, by simp [other_vertex_of_incident],
  right_inv := λ ⟨w, hw⟩, by simp }

end incidence

section finite_at

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`fintype (G.neighbor_set v)`.

We define `G.neighbor_finset v` to be the `finset` version of `G.neighbor_set v`.
Use `neighbor_finset_eq_filter` to rewrite this definition as a `filter`.
-/

variables (v : V) [fintype (G.neighbor_set v)]
/--
`G.neighbors v` is the `finset` version of `G.adj v` in case `G` is
locally finite at `v`.
-/
def neighbor_finset : finset V := (G.neighbor_set v).to_finset

@[simp] lemma mem_neighbor_finset (w : V) :
  w ∈ G.neighbor_finset v ↔ G.adj v w :=
set.mem_to_finset

/--
`G.degree v` is the number of vertices adjacent to `v`.
-/
def degree : ℕ := (G.neighbor_finset v).card

@[simp]
lemma card_neighbor_set_eq_degree : fintype.card (G.neighbor_set v) = G.degree v :=
(set.to_finset_card _).symm

lemma degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, G.adj v w :=
by simp only [degree, card_pos, finset.nonempty, mem_neighbor_finset]

instance incidence_set_fintype [decidable_eq V] : fintype (G.incidence_set v) :=
fintype.of_equiv (G.neighbor_set v) (G.incidence_set_equiv_neighbor_set v).symm

/--
This is the `finset` version of `incidence_set`.
-/
def incidence_finset [decidable_eq V] : finset (sym2 V) := (G.incidence_set v).to_finset

@[simp]
lemma card_incidence_set_eq_degree [decidable_eq V] :
  fintype.card (G.incidence_set v) = G.degree v :=
by { rw fintype.card_congr (G.incidence_set_equiv_neighbor_set v), simp }

@[simp]
lemma mem_incidence_finset [decidable_eq V] (e : sym2 V) :
  e ∈ G.incidence_finset v ↔ e ∈ G.incidence_set v :=
set.mem_to_finset

end finite_at

section locally_finite

/--
A graph is locally finite if every vertex has a finite neighbor set.
-/
@[reducible]
def locally_finite := Π (v : V), fintype (G.neighbor_set v)

variable [locally_finite G]

/--
A locally finite simple graph is regular of degree `d` if every vertex has degree `d`.
-/
def is_regular_of_degree (d : ℕ) : Prop := ∀ (v : V), G.degree v = d

lemma is_regular_of_degree_eq {d : ℕ} (h : G.is_regular_of_degree d) (v : V) : G.degree v = d := h v

end locally_finite

section finite

variables [fintype V]

instance neighbor_set_fintype [decidable_rel G.adj] (v : V) : fintype (G.neighbor_set v) :=
@subtype.fintype _ _ (by { simp_rw mem_neighbor_set, apply_instance }) _

lemma neighbor_finset_eq_filter {v : V} [decidable_rel G.adj] :
  G.neighbor_finset v = finset.univ.filter (G.adj v) :=
by { ext, simp }

@[simp]
lemma complete_graph_degree [decidable_eq V] (v : V) :
  (complete_graph V).degree v = fintype.card V - 1 :=
begin
  convert univ.card.pred_eq_sub_one,
  erw [degree, neighbor_finset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v)],
end

lemma complete_graph_is_regular [decidable_eq V] :
  (complete_graph V).is_regular_of_degree (fintype.card V - 1) :=
by { intro v, simp }

/--
The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `min_degree_le_degree`
and `le_min_degree_of_forall_le_degree`.
-/
def min_degree [decidable_rel G.adj] : ℕ :=
option.get_or_else (univ.image (λ v, G.degree v)).min 0

/--
There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
lemma exists_minimal_degree_vertex [decidable_rel G.adj] [nonempty V] :
  ∃ v, G.min_degree = G.degree v :=
begin
  obtain ⟨t, ht : _ = _⟩ := min_of_nonempty (univ_nonempty.image (λ v, G.degree v)),
  obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_of_min ht),
  refine ⟨v, by simp [min_degree, ht]⟩,
end

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
lemma min_degree_le_degree [decidable_rel G.adj] (v : V) : G.min_degree ≤ G.degree v :=
begin
  obtain ⟨t, ht⟩ := finset.min_of_mem (mem_image_of_mem (λ v, G.degree v) (mem_univ v)),
  have := finset.min_le_of_mem (mem_image_of_mem _ (mem_univ v)) ht,
  rw option.mem_def at ht,
  rwa [min_degree, ht, option.get_or_else_some],
end

/--
In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.min_degree` is
defined to be a natural.
-/
lemma le_min_degree_of_forall_le_degree [decidable_rel G.adj] [nonempty V] (k : ℕ)
  (h : ∀ v, k ≤ G.degree v) :
  k ≤ G.min_degree :=
begin
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩,
  rw hv,
  apply h
end

/--
The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_max_degree`
and `max_degree_le_of_forall_degree_le`.
-/
def max_degree [decidable_rel G.adj] : ℕ :=
option.get_or_else (univ.image (λ v, G.degree v)).max 0

/--
There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
lemma exists_maximal_degree_vertex [decidable_rel G.adj] [nonempty V] :
  ∃ v, G.max_degree = G.degree v :=
begin
  obtain ⟨t, ht⟩ := max_of_nonempty (univ_nonempty.image (λ v, G.degree v)),
  have ht₂ := mem_of_max ht,
  simp only [mem_image, mem_univ, exists_prop_of_true] at ht₂,
  rcases ht₂ with ⟨v, rfl⟩,
  rw option.mem_def at ht,
  refine ⟨v, _⟩,
  rw [max_degree, ht],
  refl
end

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
lemma degree_le_max_degree [decidable_rel G.adj] (v : V) : G.degree v ≤ G.max_degree :=
begin
  obtain ⟨t, ht : _ = _⟩ := finset.max_of_mem (mem_image_of_mem (λ v, G.degree v) (mem_univ v)),
  have := finset.le_max_of_mem (mem_image_of_mem _ (mem_univ v)) ht,
  rwa [max_degree, ht, option.get_or_else_some],
end

/--
In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree.
-/
lemma max_degree_le_of_forall_degree_le [decidable_rel G.adj] (k : ℕ)
  (h : ∀ v, G.degree v ≤ k) :
  G.max_degree ≤ k :=
begin
  by_cases hV : (univ : finset V).nonempty,
  { haveI : nonempty V := univ_nonempty_iff.mp hV,
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex,
    rw hv,
    apply h },
  { rw not_nonempty_iff_eq_empty at hV,
    rw [max_degree, hV, image_empty],
    exact zero_le k },
end

lemma degree_lt_card_verts [decidable_rel G.adj] (v : V) : G.degree v < fintype.card V :=
begin
  classical,
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  exact ⟨v, by simp, finset.subset_univ _⟩,
end

/--
The maximum degree of a nonempty graph is less than the number of vertices. Note that the assumption
that `V` is nonempty is necessary, as otherwise this would assert the existence of a natural less
than zero.
-/
lemma max_degree_lt_card_verts [decidable_rel G.adj] [nonempty V] : G.max_degree < fintype.card V :=
begin
  cases G.exists_maximal_degree_vertex with v hv,
  rw hv,
  apply G.degree_lt_card_verts v,
end

lemma card_common_neighbors_le_degree_left [decidable_rel G.adj] (v w : V) :
  fintype.card (G.common_neighbors v w) ≤ G.degree v :=
begin
  rw [←card_neighbor_set_eq_degree],
  exact set.card_le_of_subset (set.inter_subset_left _ _),
end

lemma card_common_neighbors_le_degree_right [decidable_rel G.adj] (v w : V) :
  fintype.card (G.common_neighbors v w) ≤ G.degree w :=
begin
  convert G.card_common_neighbors_le_degree_left w v using 3,
  apply common_neighbors_symm,
end

lemma card_common_neighbors_lt_card_verts [decidable_rel G.adj] (v w : V) :
  fintype.card (G.common_neighbors v w) < fintype.card V :=
nat.lt_of_le_of_lt (G.card_common_neighbors_le_degree_left _ _) (G.degree_lt_card_verts v)

/--
If the condition `G.adj v w` fails, then `card_common_neighbors_le_degree` is
the best we can do in general.
-/
lemma adj.card_common_neighbors_lt_degree {G : simple_graph V} [decidable_rel G.adj]
  {v w : V} (h : G.adj v w) :
  fintype.card (G.common_neighbors v w) < G.degree v :=
begin
  classical,
  erw [←set.to_finset_card],
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  use w,
  split,
  { rw set.mem_to_finset,
    apply not_mem_common_neighbors_right },
  { rw finset.insert_subset,
    split,
    { simpa, },
    { rw [neighbor_finset, ← set.subset_iff_to_finset_subset],
      apply common_neighbors_subset_neighbor_set } },

end

end finite

section complement

/-!
## Complement of a simple graph

This section contains definitions and lemmas concerning the complement of a simple graph.
-/

/--
We define `compl G` to be the `simple_graph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves.)
-/
def compl (G : simple_graph V) : simple_graph V :=
{ adj := λ v w, v ≠ w ∧ ¬G.adj v w,
  sym := λ v w ⟨hne, _⟩, ⟨hne.symm, by rwa edge_symm⟩,
  loopless := λ v ⟨hne, _⟩, false.elim (hne rfl) }

instance has_compl : has_compl (simple_graph V) :=
{ compl := compl }

@[simp]
lemma compl_adj (G : simple_graph V) (v w : V) : Gᶜ.adj v w ↔ v ≠ w ∧ ¬G.adj v w := iff.rfl

instance compl_adj_decidable (V : Type u) [decidable_eq V] (G : simple_graph V)
  [decidable_rel G.adj] : decidable_rel Gᶜ.adj := λ v w, and.decidable

@[simp]
lemma compl_compl (G : simple_graph V) : Gᶜᶜ = G :=
begin
  ext v w,
  split; simp only [compl_adj, not_and, not_not],
  { exact λ ⟨hne, h⟩, h hne },
  { intro h,
    simpa [G.ne_of_adj h], },
end

@[simp]
lemma compl_involutive : function.involutive (@compl V) := compl_compl

lemma compl_neighbor_set_disjoint (G : simple_graph V) (v : V) :
  disjoint (G.neighbor_set v) (Gᶜ.neighbor_set v) :=
begin
  rw set.disjoint_iff,
  rintro w ⟨h, h'⟩,
  rw [mem_neighbor_set, compl_adj] at h',
  exact h'.2 h,
end

lemma neighbor_set_union_compl_neighbor_set_eq (G : simple_graph V) (v : V) :
  G.neighbor_set v ∪ Gᶜ.neighbor_set v = {v}ᶜ :=
begin
  ext w,
  have h := @ne_of_adj _ G,
  simp_rw [set.mem_union, mem_neighbor_set, compl_adj, set.mem_compl_eq, set.mem_singleton_iff],
  tauto,
end

end complement

end simple_graph
