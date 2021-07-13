/-
Copyright (c) 2021 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov
-/
import combinatorics.simple_graph.basic
import data.set.finite
/-!
# Strongly regular graphs

## Main definitions

* `G.is_SRG_of n k l m` (see `is_simple_graph.is_SRG_of`) is a structure for a `simple_graph`
  satisfying the following conditions:
  * The cardinality of the vertex set is `n`
  * `G` is a regular graph with degree `k`
  * The number of common neighbors between any two adjacent vertices in `G` is `l`
  * The number of common neighbors between any two nonadjacent vertices in `G` is `m`

## TODO
- Prove that the complement of a strongly regular graph is strongly regular with parameters
  `is_SRG_of n (n - k - 1) (n - 2 - 2k + m) (n - 2k + l)`
- Prove that the parameters of a strongly regular graph
  obey the relation `(n - k - 1) * m = k * (k - l - 1)`
- Prove that if `I` is the identity matrix and `J` is the all-one matrix,
  then the adj matrix `A` of SRG obeys relation `A^2 = kI + lA + m(J - I - A)`
-/

universes u

namespace simple_graph
variables {V : Type u}
variables [fintype V] [decidable_eq V]
variables (G : simple_graph V) [decidable_rel G.adj]

/--
A graph is strongly regular with parameters `n k l m` if
 * its vertex set has cardinality `n`
 * it is regular with degree `k`
 * every pair of adjacent vertices has `l` common neighbors
 * every pair of nonadjacent vertices has `m` common neighbors
-/
structure is_SRG_of (n k l m : ℕ) : Prop :=
(card : fintype.card V = n)
(regular : G.is_regular_of_degree k)
(adj_common : ∀ (v w : V), G.adj v w → finset.card (G.common_neighbor_finset v w) = l)
(nadj_common : ∀ (v w : V), v ≠ w ∧ ¬ G.adj v w →
  finset.card (G.common_neighbor_finset v w) = m)

open finset

/-- Empty graphs are strongly regular. Note that the parameter `l` can take any value
  for empty graphs, since there are no pairs of adjacent vertices. -/
lemma empty_strongly_regular (l : ℕ) : (empty_graph V).is_SRG_of (fintype.card V) 0 l 0 :=
{ card := rfl,
  regular := empty_graph_degree,
  adj_common := λ v w h, h.elim,
  nadj_common := λ v w h,
    begin
      simp only [card_eq_zero],
      ext;
      rw mem_common_neighbor_finset,
      rw empty_graph,
      simp only [and_self, not_mem_empty],
    end }

-- first of all, what is `2*(k + 1) - m` in `G`? what does it count?
-- it counts the number of vertices that are adjacent to either `v` or `w` when `¬ G.adj v w`
-- so it's the cardinality of `G.neighbor_set v ∪ G.neighbor_set w`
lemma card_neighbor_set_union_nadj (n k l m : ℕ) (h : G.is_SRG_of n k l m) (v w : V) (h2 : ¬ G.adj v w)
  (h3 : v ≠ w) :
finset.card (G.neighbor_finset v ∪ G.neighbor_finset w) = 2 * k - m :=
begin
  rw ← h.nadj_common v w ⟨h3, h2⟩,
  apply @nat.add_right_cancel _ (finset.card (G.common_neighbor_finset v w)),
  rw nat.sub_add_cancel,
  unfold common_neighbor_finset,
  rw [card_union_add_card_inter, two_mul],
  simp only [card_neighbor_set_eq_degree, set.to_finset_card],
  rw [← degree, ← degree, h.regular v, h.regular w],
  { rw two_mul,
    have h4 : (G.common_neighbor_finset v w).card ≤ k,
    { rw ← h.regular v,
      exact card_common_neighbors_le_degree_left'' _ _ _ },
    apply le_add_right h4 },
end

lemma card_neighbor_set_union_adj (n k l m : ℕ) (h : G.is_SRG_of n k l m) (v w : V) (h2 : G.adj v w)
  (h3 : v ≠ w) :
finset.card (G.neighbor_finset v ∪ G.neighbor_finset w) = 2 * k - l :=
begin
  rw ← h.adj_common v w h2,
  apply @nat.add_right_cancel _ (finset.card (G.common_neighbor_finset v w)),
  rw nat.sub_add_cancel,
  unfold common_neighbor_finset,
  rw [card_union_add_card_inter, two_mul],
  simp only [card_neighbor_set_eq_degree, set.to_finset_card],
  rw [← degree, ← degree, h.regular v, h.regular w],
  { rw two_mul,
    have h4 : (G.common_neighbor_finset v w).card ≤ k,
    { rw ← h.regular v,
      exact card_common_neighbors_le_degree_left'' _ _ _ },
    apply le_add_right h4 },
end

lemma adj_nadj_ne (v w x : V) (h6: ¬G.adj w x) (h3: G.adj w v) : x ≠ v :=
begin
  by_contra,
  apply h6,
  push_neg at h,
  rw h,
  exact h3,
end

@[simp] theorem finset_compl_union (s t : finset V) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := compl_sup

-- Prove that the complement of a strongly regular graph is strongly regular with parameters
  -- `is_SRG_of n (n - k - 1) (n - 2 - 2k + m) (n - 2k + l)`
lemma strongly_regular_complement (n k l m : ℕ) (h : G.is_SRG_of n k l m) :
  Gᶜ.is_SRG_of n (n - k - 1) (n - (2 * k - m) - 2) (n - (2 * k - l)) :=
{ card := h.card,
  regular :=
    begin
      rw ← h.card,
      exact compl_regular_is_regular G k h.regular,
    end,
  adj_common :=
    begin
      intros v w h2,
      unfold common_neighbor_finset,
      simp_rw [compl_neighbor_finset G v, compl_neighbor_finset G w],
      have h3 : (G.neighbor_finset v)ᶜ \ {v} ∩ ((G.neighbor_finset w)ᶜ \ {w}) =
        (G.neighbor_finset v)ᶜ ∩ (G.neighbor_finset w)ᶜ \ ({w} ∪ {v}),
      { ext;
        simp only [mem_union, mem_sdiff, mem_compl, mem_neighbor_finset, mem_inter, mem_singleton],
        refine ⟨by cc, by cc⟩ },
      simp_rw h3,
      rw [card_sdiff, ← insert_eq, card_insert_of_not_mem, card_singleton, ← finset_compl_union],
      change (1 + 1) with 2,
      -- want `finset.card (G.neighbor_finset v ∪ G.neighbor_finset w) = n - (2 * k - m)`
      rw [card_compl, card_neighbor_set_union_nadj G n k l m h v w, ← h.card],
      { exact h2.2 },
      { exact h2.1 },
      { rw not_mem_singleton,
        apply Gᶜ.ne_of_adj ((Gᶜ.edge_symm v w).1 h2) },
      { apply union_subset,
        { apply subset_inter,
          { rw singleton_subset_iff,
            simp only [mem_compl, mem_neighbor_finset],
            exact h2.2 },
          { rw singleton_subset_iff,
            simp only [mem_compl, irrefl, not_false_iff, mem_neighbor_finset]} },
        { rw singleton_subset_iff,
          simp only [true_and, mem_compl, irrefl, not_false_iff, mem_neighbor_finset, mem_inter],
          rw edge_symm,
          exact h2.2 },
        },
    end,
  nadj_common :=
    begin
      intros v w h2,
      unfold common_neighbor_finset,
      simp_rw [compl_neighbor_finset G v, compl_neighbor_finset G w],
      have h3 : (G.neighbor_finset v)ᶜ \ {v} ∩ ((G.neighbor_finset w)ᶜ \ {w}) =
        (G.neighbor_finset v)ᶜ ∩ (G.neighbor_finset w)ᶜ \ ({w} ∪ {v}),
      { ext;
        simp,
        refine ⟨by cc, by cc⟩ },
      simp_rw h3,
      have h4 : (G.neighbor_finset v)ᶜ ∩ (G.neighbor_finset w)ᶜ \ ({w} ∪ {v}) =
        (G.neighbor_finset v)ᶜ ∩ (G.neighbor_finset w)ᶜ,
      { ext;
        simp,
        intros h5 h6,
        push_neg,
        split,
        { have h4 : G.adj w v,
          { rw adj_compl,
            refine ⟨ne.symm h2.1, _⟩,
            rw edge_symm,
            exact h2.2 },
          apply adj_nadj_ne G w v a h5,
          rw edge_symm,
          exact h4 },
        { have h3 : G.adj v w,
          { rw adj_compl,
            refine ⟨h2.1, h2.2⟩ },
          apply adj_nadj_ne G v w a h6,
          rw edge_symm,
          exact h3 } },
      rw [h4, ← finset_compl_union, card_compl, card_neighbor_set_union_adj G n k l m h v w,
        ← h.card],
      rw ← adj_compl at h2,
      { exact h2 },
      { exact h2.1 },
    end }

/-Complete graphs are strongly regular. Note that the parameter `m` can take any value
  for complete graphs, since there are no distinct pairs of nonadjacent vertices. -/
/-lemma complete_strongly_regular (m : ℕ) :
  (complete_graph V).is_SRG_of (fintype.card V) (fintype.card V - 1) (fintype.card V - 2) m :=
{ card := rfl,
  regular := --exact compl_regular_is_regular G k h.regular,
    begin
      simp_rw ← compl_empty,
      rw ← nat.sub_zero (fintype.card V),
      apply compl_regular_is_regular (empty_graph V) 0,
      sorry,
    end,
  adj_common := _,
  nadj_common := _ }-/


end simple_graph
