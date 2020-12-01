/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alena Gusakov.
-/
import data.fintype.basic
import data.sym2
import combinatorics.simple_graph.basic
/-!
# Matchings


## Main definitions

* a `matching` on a simple graph is a subset of its edge set such that
   no two edges share an endpoint.

* a `perfect_matching` on a simple graph is a matching in which every
   vertex belongs to an edge.

TODO:
  - Lemma stating that the existence of a perfect matching on `G` implies that
    the cardinality of `V` is even (assuming it's finite)
  - Hall's Marriage Theorem
  - Tutte's Theorem

TODO: Tutte and Hall require a definition of subgraphs.
-/
open finset
universe u

namespace simple_graph
variables {V : Type u} (G : simple_graph V) (M : set (sym2 V)) (h : M ⊆ edge_set G)

/--
A matching on `G` is a subset of its edges such that no two edges share a vertex.
-/
structure is_matching (M : set (sym2 V)) : Prop :=
(sub_edges : M ⊆ G.edge_set)
(disjoint : ∀ (x y ∈ M) (v : V), v ∈ x ∧ v ∈ y → x = y)

/--
`matching G` is the type of matchings over `G`.
-/
def matching : Type u := {M : set (sym2 V) // G.is_matching M}

instance : inhabited (matching G) :=
  ⟨⟨∅, set.empty_subset _, λ _ _ hx, false.elim (set.not_mem_empty _ hx)⟩⟩

variables {G}

/--
`verts` is the set of vertices of `G` that are
contained in some edge of matching `M`
-/
def matching.verts (M : G.matching) : set V :=
{v : V | ∃ x ∈ M.val, v ∈ x}

/--
A perfect matching `M` on graph `G` is a matching such that
  every vertex is contained in an edge of `M`.
-/
def matching.is_perfect (M : G.matching) : Prop :=
M.verts = set.univ

end simple_graph
