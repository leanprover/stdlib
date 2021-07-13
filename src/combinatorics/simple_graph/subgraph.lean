/-
Copyright (c) 2021 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe, Kyle Miller, Alena Gusakov
-/
import combinatorics.simple_graph.basic
import data.set.finite

/-!
# Subgraphs of a simple graph

A subgraph of a simple graph consists of subsets of the graph's vertices and edges such that the
endpoints of each edge are present in the vertex subset.  The edge subset is formalized as a
sub-relation of the adjacency relation of the simple graph.

## Main definitions

* `subgraph G` is the type of subgraphs of a `G : simple_graph`

* `subgraph.neighbor_set`, `subgraph.incidence_set`, and `subgraph.degree` are like their
  `simple_graph` counterparts, but they refer to vertices from `G` to avoid subtype coercions.

* `subgraph.coe` is the coercion from a `G' : subgraph G` to a `simple_graph G'.verts`.
  (This cannot be a `has_coe` instance since the destination type depends on `G'`.)

* A `bounded_lattice (subgraph G)` instance.

* Graph homomorphisms from a subgraph to a graph (`subgraph.map_top`) and between subgraphs
  (`subgraph.map`).

## Implementation notes

* Recall that subgraphs are not determined by their vertex sets, so `set_like` does not apply to
  this kind of subobject.

## Todo

* Images of graph homomorphisms as subgraphs.

-/

universe u

namespace simple_graph

/-- A subgraph of a `simple_graph` is a subset of vertices along with a restriction of the adjacency
relation that is symmetric and is supported by the vertex subset.  They also form a bounded lattice.

Thinking of `V → V → Prop` as `set (V × V)`, a set of darts (i.e., half-edges), then
`subgraph.adj_sub` is that the darts of a subgraph are a subset of the darts of `G`. -/
@[ext]
structure subgraph {V : Type u} (G : simple_graph V) :=
(verts : set V)
(adj : V → V → Prop)
(adj_sub : ∀ {v w : V}, adj v w → G.adj v w)
(edge_vert : ∀ {v w : V}, adj v w → v ∈ verts)
(sym : symmetric adj . obviously)

namespace subgraph

variables {V : Type u} {G : simple_graph V}

lemma adj_comm (G' : subgraph G) (v w : V) : G'.adj v w ↔ G'.adj w v :=
⟨λ x, G'.sym x, λ x, G'.sym x⟩

@[symm] lemma adj_symm (G' : subgraph G) {u v : V} (h : G'.adj u v) : G'.adj v u := G'.sym h

/-- Coercion from `subgraph G` to `simple_graph G.V`. -/
@[simps] def coe (G' : subgraph G) : simple_graph G'.verts :=
{ adj := λ v w, G'.adj v w,
  sym := λ v w h, G'.sym h,
  loopless := λ v h, loopless G v (G'.adj_sub h) }

@[simp] lemma coe_adj_sub (G' : subgraph G) (u v : G'.verts) (h : G'.coe.adj u v) : G.adj u v :=
G'.adj_sub h

/-- `G'.neighbor_set v` is the set of vertices adjacent to `v` in `G'`. -/
def neighbor_set (G' : subgraph G) (v : V) : set V := set_of (G'.adj v)

lemma neighbor_set_subset (G' : subgraph G) (v : V) : G'.neighbor_set v ⊆ G.neighbor_set v :=
λ w h, G'.adj_sub h

@[simp] lemma mem_neighbor_set (G' : subgraph G) (v w : V) : w ∈ G'.neighbor_set v ↔ G'.adj v w :=
iff.rfl

/-- A subgraph as a graph has equivalent neighbor sets. -/
def coe_neighbor_set_equiv {G' : subgraph G} (v : G'.verts) :
  G'.coe.neighbor_set v ≃ G'.neighbor_set v :=
{ to_fun := λ w, ⟨w, by { obtain ⟨w', hw'⟩ := w, simpa using hw' }⟩,
  inv_fun := λ w, ⟨⟨w, G'.edge_vert (G'.adj_symm w.2)⟩, by simpa using w.2⟩,
  left_inv := λ w, by simp,
  right_inv := λ w, by simp }

/-- The edge set of `G'` consists of a subset of edges of `G`. -/
def edge_set (G' : subgraph G) : set (sym2 V) := sym2.from_rel G'.sym

lemma edge_set_subset (G' : subgraph G) : G'.edge_set ⊆ G.edge_set :=
λ e, quotient.ind (λ e h, G'.adj_sub h) e

@[simp]
lemma mem_edge_set {G' : subgraph G} {v w : V} : ⟦(v, w)⟧ ∈ G'.edge_set ↔ G'.adj v w := iff.rfl

lemma mem_verts_if_mem_edge {G' : subgraph G} {e : sym2 V} {v : V}
  (he : e ∈ G'.edge_set) (hv : v ∈ e) : v ∈ G'.verts :=
begin
  refine quotient.ind (λ e he hv, _) e he hv,
  cases e with v w,
  simp only [mem_edge_set] at he,
  cases sym2.mem_iff.mp hv with h h; subst h,
  { exact G'.edge_vert he, },
  { exact G'.edge_vert (G'.sym he), },
end

/-- The `incidence_set` is the set of edges incident to a given vertex. -/
def incidence_set (G' : subgraph G) (v : V) : set (sym2 V) := {e ∈ G'.edge_set | v ∈ e}

lemma incidence_set_subset_incidence_set (G' : subgraph G) (v : V) :
  G'.incidence_set v ⊆ G.incidence_set v :=
λ e h, ⟨G'.edge_set_subset h.1, h.2⟩

lemma incidence_set_subset (G' : subgraph G) (v : V) : G'.incidence_set v ⊆ G'.edge_set :=
λ _ h, h.1

/-- Give a vertex as an element of the subgraph's vertex type. -/
@[reducible]
def vert (G' : subgraph G) (v : V) (h : v ∈ G'.verts) : G'.verts := ⟨v, h⟩

/--
Create an equal copy of a subgraph (see `copy_eq`) with possibly different definitional equalities.
See Note [range copy pattern].
-/
def copy (G' : subgraph G)
  (V'' : set V) (hV : V'' = G'.verts)
  (adj' : V → V → Prop) (hadj : adj' = G'.adj) :
  subgraph G :=
{ verts := V'',
  adj := adj',
  adj_sub := hadj.symm ▸ G'.adj_sub,
  edge_vert := hV.symm ▸ hadj.symm ▸ G'.edge_vert,
  sym := hadj.symm ▸ G'.sym }

lemma copy_eq (G' : subgraph G)
  (V'' : set V) (hV : V'' = G'.verts)
  (adj' : V → V → Prop) (hadj : adj' = G'.adj) :
  G'.copy V'' hV adj' hadj = G' :=
subgraph.ext _ _ hV hadj

/-- The union of two subgraphs. -/
def union (x y : subgraph G) : subgraph G :=
{ verts := x.verts ∪ y.verts,
  adj := λ v w, x.adj v w ∨ y.adj v w,
  adj_sub := λ v w h, or.cases_on h (λ h, x.adj_sub h) (λ h, y.adj_sub h),
  edge_vert := λ v w h, or.cases_on h (λ h, or.inl (x.edge_vert h)) (λ h, or.inr (y.edge_vert h)),
  sym := λ v w h, by rwa [x.adj_comm, y.adj_comm] }

/-- The intersection of two subgraphs. -/
def inter (x y : subgraph G) : subgraph G :=
{ verts := x.verts ∩ y.verts,
  adj := λ v w, x.adj v w ∧ y.adj v w,
  adj_sub := λ v w h, x.adj_sub h.1,
  edge_vert := λ v w h, ⟨x.edge_vert h.1, y.edge_vert h.2⟩,
  sym := λ v w h, by rwa [x.adj_comm, y.adj_comm] }

instance : has_union (subgraph G) := ⟨union⟩
instance : has_inter (subgraph G) := ⟨inter⟩

/-- The `top` subgraph is `G` as a subgraph of itself. -/
def top : subgraph G :=
{ verts := set.univ,
  adj := G.adj,
  adj_sub := λ v w h, h,
  edge_vert := λ v w h, set.mem_univ v,
  sym := G.sym }

/-- The `bot` subgraph is the subgraph with no vertices or edges. -/
def bot : subgraph G :=
{ verts := ∅,
  adj := λ v w, false,
  adj_sub := λ v w h, false.rec _ h,
  edge_vert := λ v w h, false.rec _ h,
  sym := λ u v h, h }

instance subgraph_inhabited : inhabited (subgraph G) := ⟨bot⟩

/-- The relation that one subgraph is a subgraph of another. -/
def is_subgraph (x y : subgraph G) : Prop := x.verts ⊆ y.verts ∧ ∀ {v w : V}, x.adj v w → y.adj v w

instance : bounded_lattice (subgraph G) :=
{ le := is_subgraph,
  sup := union,
  inf := inter,
  top := top,
  bot := bot,
  le_refl := λ x, ⟨rfl.subset, λ _ _ h, h⟩,
  le_trans := λ x y z hxy hyz, ⟨hxy.1.trans hyz.1, λ _ _ h, hyz.2 (hxy.2 h)⟩,
  le_antisymm := begin
    intros x y hxy hyx,
    ext1 v,
    exact set.subset.antisymm hxy.1 hyx.1,
    ext v w,
    exact iff.intro (λ h, hxy.2 h) (λ h, hyx.2 h),
  end,
  le_top := λ x, ⟨set.subset_univ _, (λ v w h, x.adj_sub h)⟩,
  bot_le := λ x, ⟨set.empty_subset _, (λ v w h, false.rec _ h)⟩,
  sup_le := λ x y z hxy hyz,
            ⟨set.union_subset hxy.1 hyz.1,
              (λ v w h, h.cases_on (λ h, hxy.2 h) (λ h, hyz.2 h))⟩,
  le_sup_left := λ x y, ⟨set.subset_union_left x.verts y.verts, (λ v w h, or.inl h)⟩,
  le_sup_right := λ x y, ⟨set.subset_union_right x.verts y.verts, (λ v w h, or.inr h)⟩,
  le_inf := λ x y z hxy hyz, ⟨set.subset_inter hxy.1 hyz.1, (λ v w h, ⟨hxy.2 h, hyz.2 h⟩)⟩,
  inf_le_left := λ x y, ⟨set.inter_subset_left x.verts y.verts, (λ v w h, h.1)⟩,
  inf_le_right := λ x y, ⟨set.inter_subset_right x.verts y.verts, (λ v w h, h.2)⟩ }

/-- The top of the `subgraph G` lattice is equivalent to the graph itself. -/
def top_equiv : (⊤ : subgraph G).coe ≃g G :=
{ to_fun := λ v, ↑v,
  inv_fun := λ v, ⟨v, by tidy⟩,
  left_inv := by tidy,
  right_inv := by tidy,
  map_rel_iff' := by tidy }

/-- The bottom of the `subgraph G` lattice is equivalent to the empty graph on the empty
vertex type. -/
def bot_equiv : (⊥ : subgraph G).coe ≃g empty_graph empty :=
{ to_fun := λ v, false.elim v.property,
  inv_fun := λ v, begin cases v, end,
  left_inv := by tidy,
  right_inv := by tidy,
  map_rel_iff' := by tidy }

/-- Given two subgraphs, one a subgraph of the other, there is an induced injective homomorphism of
the subgraphs as graphs. -/
def map {x y : subgraph G} (h : x ≤ y) : x.coe →g y.coe :=
{ to_fun := λ v, ⟨↑v, and.left h v.property⟩,
  map_rel' := λ v w hvw, h.2 hvw }

lemma map.injective {x y : subgraph G} (h : x ≤ y) : function.injective (map h) :=
λ v w h, by { simp only [map, rel_hom.coe_fn_mk, subtype.mk_eq_mk] at h, exact subtype.ext h }

/-- There is an induced injective homomorphism of a subgraph of `G` into `G`. -/
def map_top (x : subgraph G) : x.coe →g G :=
{ to_fun := λ v, v,
  map_rel' := λ v w hvw, x.adj_sub hvw }

lemma map_top.injective {x : subgraph G} : function.injective x.map_top :=
λ v w h, subtype.ext h

@[simp]
lemma map_top_to_fun {x : subgraph G} (v : x.verts) : x.map_top v = v := rfl

lemma neighbor_set_subset_of_subgraph {x y : subgraph G} (h : x ≤ y) (v : V) :
  x.neighbor_set v ⊆ y.neighbor_set v :=
λ w h', h.2 h'

instance neighbor_set.decidable_pred (G' : subgraph G) [h : decidable_rel G'.adj] (v : V) :
  decidable_pred (G'.neighbor_set v) := h v

/-- If a graph is locally finite at a vertex, then so is a subgraph of that graph. -/
instance finite_at {G' : subgraph G} (v : G'.verts) [decidable_rel G'.adj]
   [fintype (G.neighbor_set v)] : fintype (G'.neighbor_set v) :=
set.fintype_subset (G.neighbor_set v) (G'.neighbor_set_subset v)

/-- If a subgraph is locally finite at a vertex, then so are subgraphs of that subgraph.

This is not an instance because `G''` cannot be inferred. -/
def finite_at_of_subgraph {G' G'' : subgraph G} [decidable_rel G'.adj]
   (h : G' ≤ G'') (v : G'.verts) [hf : fintype (G''.neighbor_set v)] :
   fintype (G'.neighbor_set v) :=
set.fintype_subset (G''.neighbor_set v) (neighbor_set_subset_of_subgraph h v)

instance coe_finite_at {G' : subgraph G} (v : G'.verts) [fintype (G'.neighbor_set v)] :
  fintype (G'.coe.neighbor_set v) :=
fintype.of_equiv _ (coe_neighbor_set_equiv v).symm

/-- The degree of a vertex in a subgraph.  Is zero for vertices outside the subgraph. -/
def degree (G' : subgraph G) (v : V) [fintype (G'.neighbor_set v)] : ℕ :=
fintype.card (G'.neighbor_set v)

lemma degree_le (G' : subgraph G) (v : V)
  [fintype (G'.neighbor_set v)] [fintype (G.neighbor_set v)] :
  G'.degree v ≤ G.degree v :=
begin
  rw ←card_neighbor_set_eq_degree,
  exact set.card_le_of_subset (G'.neighbor_set_subset v),
end

lemma degree_le' (G' G'' : subgraph G) (h : G' ≤ G'') (v : V)
  [fintype (G'.neighbor_set v)] [fintype (G''.neighbor_set v)] :
  G'.degree v ≤ G''.degree v :=
set.card_le_of_subset (neighbor_set_subset_of_subgraph h v)

@[simp] lemma coe_degree (G' : subgraph G) (v : G'.verts)
  [fintype (G'.coe.neighbor_set v)] [fintype (G'.neighbor_set v)] :
  G'.coe.degree v = G'.degree v :=
begin
  rw ←card_neighbor_set_eq_degree,
  exact fintype.card_congr (coe_neighbor_set_equiv v),
end

end subgraph

end simple_graph
