/-
Copyright (c) 2021 Gabriel Moise. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Moise
-/
import combinatorics.simple_graph.basic
import linear_algebra.matrix

/-!
# Incidence matrices

This module defines the incidence matrix `inc_matrix` of an undirected graph `simple_graph`,
and provides theorems and lemmas connecting graph properties to computational properties of the
matrix. It also defines the notion of `orientation` for a `simple_graph`, picking a direction for
each undirected edge in the graph and then defining the oriented incidence matrix
`oriented_inc_matrix` based on that.

## Main definitions

* `inc_matrix`: The incidence matrix `M` of a `simple_graph` with coefficients in a given ring `R`.
* `orientation`: A structure that defines a choice of direction on the edges of a `simple_graph`.
* `oriented_inc_matrix`: The oriented incidence matrix `N(o)` of a `simple_graph` with
respect to a given `orientation`.

## Main results

1. `adj_sum_of_mul_inc_one`: `∑ e : E, M i e * M j e = 1`, for any two adjacent vertices
`i` and `j`.
2. `inc_matrix_mul_non_adj`: `M i e * M j e = 0`, for any two distinct non-adjacent vertices
`i`, `j` and edge `e`.
3. `inc_matrix_element_power_id`: Every element from `M` is idempotent.
4. `degree_equals_sum_of_incidence_row`: For any vertex `i`, the sum on the ith row of `M` is
equal to the degree of `i`.
5. `oriented_inc_matrix_elem_squared`: `(N(o) i e) ^ 2 = M i e`, for any orientation `o`,
vertex `i` and edge `e`.
6. `oriented_inc_matrix_mul_of_adj`: For any adjacent vertices `i`, `j` and edge `e`,
`N(o) i e * N(o) j e = if e = ⟦(i, j)⟧ then -1 else 0`.
7. `oriented_inc_matrix_mul_non_adj`: For any non-adjacent distinct vertices `i`, `j` and
edge `e`, `N(o) i e * N(o) j e = 0`.
8. `vec_mul_oriented_inc_matrix`: `(xᵀ ⬝ N(o)) e = x o.head(e) - x o.tail(e).`

## References

<https://en.wikipedia.org/wiki/Orientation_(graph_theory)>
-/

open_locale big_operators matrix
open finset matrix simple_graph sym2

universes u v
variables {R : Type u} {V : Type v}

section to_move

@[simp]
lemma ite_mul_ite_zero_right
  {R : Type*} [mul_zero_class R] {P Q : Prop} [decidable P] [decidable Q] (a b : R):
  (ite P a 0) * (ite Q b 0) = ite (P ∧ Q) (a * b) 0 :=
by simp [←ite_and]

end to_move

namespace simple_graph

variables (G : simple_graph V)

-- ### Helping lemmas for edges

lemma edge_set_ne {u v : V} {e : G.edge_set} (h : ↑e = ⟦(u, v)⟧) : u ≠ v :=
begin
  apply G.ne_of_adj,
  rw [←G.mem_edge_set, ←h],
  exact e.property
end

lemma incidence_equiv {i : V} {e : G.edge_set} : ↑e ∈ G.incidence_set i ↔ i ∈ (↑e : sym2 V) :=
by simp only [incidence_set, true_and, set.mem_sep_eq, subtype.coe_prop]

lemma any_vertex_if_incidence_set {i u v : V} :
  ⟦(u, v)⟧ ∈ G.incidence_set i → i = u ∨ i = v :=
by simp only [←mem_iff, incidence_set, set.mem_sep_eq, and_imp, imp_self, implies_true_iff]

lemma incidence_set_if_any_vertex {i u v : V} (h : ⟦(u, v)⟧ ∈ G.edge_set) :
  i = u ∨ i = v → ⟦(u, v)⟧ ∈ G.incidence_set i :=
by simp only [←mem_iff, incidence_set, set.mem_sep_eq, h, true_and, imp_self]

lemma edge_in_two_incidence_sets {i j : V} {e : sym2 V} (H_ne : i ≠ j) :
  e ∈ G.incidence_set i ∧ e ∈ G.incidence_set j → e = ⟦(i, j)⟧ :=
begin
  refine quotient.rec_on_subsingleton e (λ p, _),
  rcases p with ⟨v, w⟩,
  rintros ⟨⟨-, H_i⟩, ⟨-, H_j⟩⟩,
  rw ←elems_iff_eq H_ne,
  tauto,
end

lemma mem_incidence_sets_iff_eq {i j : V} {e : sym2 V} (h : G.adj i j) :
  e ∈ G.incidence_set i ∧ e ∈ G.incidence_set j ↔ e = ⟦(i, j)⟧ :=
begin
 split,
  { apply edge_in_two_incidence_sets _,
  rintro rfl,
  exact G.loopless i h },
  { rintro rfl,
  nth_rewrite 1 eq_swap,
  simp only [h, G.sym h, mem_incidence_set, and_self] }
end

lemma adj_iff_exists_edge_coe {i j : V} : G.adj i j ↔ ∃ (e : G.edge_set), ↑e = ⟦(i, j)⟧ :=
by simp only [mem_edge_set, exists_prop, set_coe.exists, exists_eq_right, subtype.coe_mk]

section incidence

variables [fintype V] [decidable_eq V] [decidable_rel G.adj] (R) [ring R]

-- ## Incidence matrix M

/-- `inc_matrix G R` is the matrix `M` such that `M i e = 1` if vertex `i` is an
endpoint of the edge `e` in the simple graph `G`, otherwise `M i j = 0`. -/
def inc_matrix : matrix V G.edge_set R
| i e := if (e : sym2 V) ∈ G.incidence_set i then 1 else 0

@[simp]
lemma inc_matrix_apply {i : V} {e : G.edge_set} :
  G.inc_matrix R i e = if (e : sym2 V) ∈ G.incidence_set i then 1 else 0 := rfl

-- ### Relation between inc_matrix elements and incidence_set property

lemma inc_matrix_zero {i : V} {e : G.edge_set} [char_zero R] :
  G.inc_matrix R i e = 0 ↔ ↑e ∉ G.incidence_set i :=
by simp only [inc_matrix, ite_eq_right_iff, ←decidable.not_imp_not,
              forall_true_left, not_false_iff, one_ne_zero]

lemma inc_matrix_one {i : V} {e : G.edge_set} [char_zero R] :
  G.inc_matrix R i e = 1 ↔ ↑e ∈ G.incidence_set i :=
by simp only [inc_matrix, ite_eq_left_iff, ←decidable.not_imp_not,
              set.not_not_mem, forall_true_left, not_false_iff, zero_ne_one]

-- ### One - zero properties

lemma inc_matrix_not_zero {i : V} {e : G.edge_set} [char_zero R] :
  ¬ G.inc_matrix R i e = 0 ↔ G.inc_matrix R i e = 1 :=
by simp only [inc_matrix_zero, inc_matrix_one, set.not_not_mem]

lemma inc_matrix_not_one {i : V} {e : G.edge_set} [char_zero R] :
  ¬ G.inc_matrix R i e = 1 ↔ G.inc_matrix R i e = 0 :=
by simp only [inc_matrix_zero, inc_matrix_one]

lemma inc_matrix_zero_or_one {i : V} {e : G.edge_set} [char_zero R] :
  G.inc_matrix R i e = 0 ∨ G.inc_matrix R i e = 1 :=
by { rw [inc_matrix_zero, inc_matrix_one], exact (em (↑e ∈ G.incidence_set i)).symm }

lemma inc_matrix_elements_mul_one {i j : V} {e : G.edge_set} [char_zero R] :
  G.inc_matrix R i e * G.inc_matrix R j e = 1 ↔ G.inc_matrix R i e = 1 ∧ G.inc_matrix R j e = 1 :=
begin
  cases G.inc_matrix_zero_or_one R with H₀ H₁,
  { rw H₀, simp only [if_t_t, mul_boole, inc_matrix_apply, zero_ne_one, false_and] },
  { rw H₁, simp only [true_and, mul_boole, inc_matrix_apply, eq_self_iff_true] }
end

-- 1. `∑ e : E, M i e * M j e = 1`, for any two adjacent vertices `i` and `j`.
theorem adj_sum_of_mul_inc_one {i j : V} (H_adj : G.adj i j) :
  ∑ (e : G.edge_set), G.inc_matrix R i e * G.inc_matrix R j e = (1 : R) :=
begin
  simp only [inc_matrix_apply, ite_mul_ite_zero_right, sum_boole,
             G.mem_incidence_sets_iff_eq H_adj, mul_one],
  rw adj_iff_exists_edge_coe at H_adj,
  rcases H_adj with ⟨e, H_e⟩,
  simp only [←H_e, subtype.ext_iff.symm, filter_eq', filter_congr_decidable,
             if_true, mem_univ, nat.cast_one, card_singleton]
end

-- 2. `M i e * M j e = 0`, for any two distinct non-adjacent vertices `i`, `j` and edge `e`.
theorem inc_matrix_mul_non_adj {i j : V} {e : G.edge_set} (Hne : i ≠ j) (H_non_adj : ¬ G.adj i j)
[char_zero R] :
  G.inc_matrix R i e * G.inc_matrix R j e = 0 :=
begin
  by_cases H₁ : G.inc_matrix R i e = 0,
  { rw [H₁, zero_mul] },
  { rw [inc_matrix_not_zero, inc_matrix_one] at H₁,
    by_cases H₂ : G.inc_matrix R j e = 0,
    { rw [H₂, mul_zero] },
    { rw [inc_matrix_not_zero, inc_matrix_one] at H₂,
      exfalso,
      apply H_non_adj,
      rw [←mem_edge_set, ←G.edge_in_two_incidence_sets Hne ⟨H₁, H₂⟩],
      exact e.property } }
end

-- 3. Every element from `M` is idempotent: `(M i e) ^ 2 = M i e`, with `i` a vertex, `e` an edge.
theorem inc_matrix_element_power_id {i : V} {e : G.edge_set} :
  (G.inc_matrix R i e) * (G.inc_matrix R i e) = G.inc_matrix R i e :=
by simp [inc_matrix_apply]

-- 4. `degree(i) = ∑ e : E, M i e`, where `i` is a vertex.
theorem degree_equals_sum_of_incidence_row {i : V} [char_zero R] :
  (G.degree i : R) = ∑ (e : G.edge_set), G.inc_matrix R i e :=
begin
  simp only [inc_matrix_apply, sum_boole],
  rw [←card_incidence_set_eq_degree, nat.cast_inj],
  refine finset.card_congr _ _ _ _,
  { rintros ⟨e, he⟩ he',
    exact ⟨e, G.incidence_set_subset i he⟩ },
  { rintros ⟨e, he⟩ he',
    simpa only [true_and, finset.mem_univ, finset.mem_filter] using he },
  { rintros ⟨e1, he1⟩ ⟨e2, he2⟩ he1' he2' hr,
    ext,
    simp only [subtype.mk_eq_mk] at hr,
    simp only [hr] },
  { rintros ⟨e, he⟩ he',
    use e,
    { simpa only [true_and, finset.mem_univ, finset.mem_filter] using he' },
    { simp only [finset.mem_univ, exists_prop_of_true] } }
end

end incidence

section orientations

-- ## Orientations

/-- Define an `orientation` on the undirected graph G as a structure that defines (consistently)
for each edge a `head` and a `tail`. -/
@[ext]
structure orientation (G : simple_graph V) :=
(head : G.edge_set → V)
(tail : G.edge_set → V)
(consistent (e : G.edge_set) : ↑e = ⟦(head(e), tail(e))⟧)

noncomputable instance (G : simple_graph V) : inhabited (orientation G) :=
⟨{ head := λ (e : G.edge_set), (quotient.out (e : sym2 V)).fst,
  tail := λ (e : G.edge_set), (quotient.out (e : sym2 V)).snd,
  consistent := λ (e : G.edge_set), by rw [prod.mk.eta, quotient.out_eq] }⟩

variables {o : orientation G}

lemma head_tail (o : orientation G) (i : V) (e : G.edge_set) :
  i = o.head e ∨ i = o.tail e ∨ (i ≠ o.head e ∧ i ≠ o.tail e) :=
by tauto

lemma edge_not_incident {i j : V} {e : G.edge_set}
  (H_e : ¬↑e = ⟦(i, j)⟧) (H_adj : G.adj i j) : ↑e ∉ G.incidence_set i ∨ ↑e ∉ G.incidence_set j :=
begin
  classical,
  by_contradiction h,
  rw [decidable.not_or_iff_and_not, not_not, not_not] at h,
  exact H_e (G.edge_in_two_incidence_sets (G.ne_of_adj H_adj) h),
end

lemma head_neq_tail {e : G.edge_set} : o.head(e) ≠ o.tail(e) := G.edge_set_ne (o.consistent e)

lemma incidence_set_orientation_head {e : G.edge_set} : ↑e ∈ G.incidence_set (o.head e) :=
by { rw [incidence_equiv, o.consistent e], simp only [mem_iff, true_or, eq_self_iff_true] }

lemma incidence_set_orientation_tail {e : G.edge_set} : ↑e ∈ G.incidence_set (o.tail e) :=
by { rw [incidence_equiv, o.consistent e], simp only [mem_iff, eq_self_iff_true, or_true] }

lemma incidence_set_orientation {i : V} {e : G.edge_set} :
  ↑e ∈ G.incidence_set i ↔ i = o.head e ∨ i = o.tail e :=
begin
  rw o.consistent e,
  have key : ⟦(o.head e, o.tail e)⟧ ∈ G.edge_set, {rw ←o.consistent e, exact e.property},
  exact ⟨G.any_vertex_if_incidence_set, G.incidence_set_if_any_vertex key⟩,
end

lemma not_inc_set_orientation {i : V} {e : G.edge_set} :
  i ≠ o.head e ∧ i ≠ o.tail e ↔ ↑e ∉ G.incidence_set i :=
begin
  rw G.incidence_set_orientation,
  tauto
end

end orientations

section oriented_incidence

variables [fintype V] [decidable_eq V] [decidable_rel G.adj] (R) [ring R] {o : orientation G}

-- ## Oriented Incidence Matrix N(o)

/-- An `oriented incidence matrix N(o)` is defined with respect to the orientation of the edges
and is defined to be `1` for entries (`i`,`e`) where `i` is the head of `e`, `-1` where `i`
is the tail of `e`, and `0` otherwise. -/
def oriented_inc_matrix (o : orientation G) : matrix V G.edge_set R :=
λ i e, if i = o.head e then (1 : R) else (if i = o.tail e then -1 else 0)

@[simp]
lemma oriented_inc_matrix_apply {i : V} {e : G.edge_set} :
  G.oriented_inc_matrix R o i e = ite (i = o.head e) (1 : R) (ite (i = o.tail e) (-1) 0) := rfl

lemma oriented_inc_matrix_head {i : V} {e : G.edge_set} (H_head : i = o.head e) :
  G.oriented_inc_matrix R o i e = 1 :=
by simp only [H_head, if_true, eq_self_iff_true, oriented_inc_matrix_apply]

lemma oriented_inc_matrix_tail {i : V} {e : G.edge_set} (H_tail : i = o.tail e) :
  G.oriented_inc_matrix R o i e = -1 :=
by simp only [H_tail, oriented_inc_matrix, (G.head_neq_tail).symm,
              if_false, if_true, eq_self_iff_true]

lemma oriented_inc_matrix_zero {i : V} {e : G.edge_set} [char_zero R] :
  G.oriented_inc_matrix R o i e = 0 ↔ i ≠ o.head e ∧ i ≠ o.tail e :=
begin
  obtain H_head | H_tail | ⟨H_not_head, H_not_tail⟩ := G.head_tail o i e,
  { simp only [oriented_inc_matrix, H_head, if_true, eq_self_iff_true, not_true,
               ne.def, one_ne_zero, false_and] },
  { simp only [H_tail, oriented_inc_matrix_tail, eq_self_iff_true, not_true,
                 ne.def, neg_eq_zero, one_ne_zero, and_false] },
  { simp only [H_not_head, H_not_tail, eq_self_iff_true, if_false, ne.def,
                 not_false_iff, and_self, oriented_inc_matrix_apply] }
end

lemma oriented_inc_matrix_zero' {i : V} {e : G.edge_set} [char_zero R] :
  G.oriented_inc_matrix R o i e = 0 ↔ ↑e ∉ G.incidence_set i :=
by rw [oriented_inc_matrix_zero, not_inc_set_orientation]

lemma oriented_inc_matrix_non_zero {i : V} {e : G.edge_set} [char_zero R] :
  ¬ G.oriented_inc_matrix R o i e = 0 ↔ i = o.head e ∨ i = o.tail e :=
by rw [←not_iff_not, not_not, oriented_inc_matrix_zero, ←not_or_distrib]

-- 5. `(N(o) i e) ^ 2 = M i e`, for any orientation `o`, vertex `i` and edge `e`.
theorem oriented_inc_matrix_elem_squared {i : V} {e : G.edge_set} [char_zero R] :
  G.oriented_inc_matrix R o i e * G.oriented_inc_matrix R o i e = G.inc_matrix R i e :=
begin
  obtain H_head | H_tail | H_not := G.head_tail o i e,
  { rw [G.oriented_inc_matrix_head R H_head, H_head, mul_one, eq_comm, inc_matrix_one],
    exact G.incidence_set_orientation_head },
  { rw [G.oriented_inc_matrix_tail R H_tail, H_tail, mul_neg_eq_neg_mul_symm, mul_one,
        neg_neg, eq_comm, inc_matrix_one],
    exact G.incidence_set_orientation_tail },
  { rw [(G.oriented_inc_matrix_zero R).mpr H_not, mul_zero, eq_comm, inc_matrix_zero],
    exact G.not_inc_set_orientation.mp ⟨H_not.1, H_not.2⟩ }
end

/-- 6. For any adjacent vertices `i`, `j` and edge `e`,
`N(o) i e * N(o) j e = if e = ⟦(i, j)⟧` then `-1` else `0`. -/
theorem oriented_inc_matrix_mul_of_adj {i j : V} {e : G.edge_set} (H_adj : G.adj i j) [char_zero R]:
  G.oriented_inc_matrix R o i e * G.oriented_inc_matrix R o j e = ite (↑e = ⟦(i, j)⟧) (-1) 0 :=
begin
  by_cases H_e : ↑e = ⟦(i, j)⟧,
  { rw [H_e, if_pos rfl],
    rw [o.consistent e, eq_iff] at H_e,
    rcases H_e with (⟨H_head, H_tail⟩ | ⟨H_head, H_tail⟩);
    simp only [G.oriented_inc_matrix_head R, G.oriented_inc_matrix_tail R,
               H_head.symm, H_tail.symm, mul_one, one_mul] },
  { cases (G.edge_not_incident H_e H_adj) with H H;
    simp only [(G.oriented_inc_matrix_zero' R).mpr H, zero_mul, mul_zero, H_e, if_false] }
end

-- 7. For any non-adjacent distinct vertices `i`, `j` and edge `e`, `N(o) i e * N(o) j e = 0`.
theorem oriented_inc_matrix_mul_non_adj {i j : V} {e : G.edge_set} [char_zero R] (H_ij : i ≠ j)
  (H_not_adj : ¬G.adj i j) : G.oriented_inc_matrix R o i e * G.oriented_inc_matrix R o j e = 0 :=
begin
  by_cases H₁ : G.oriented_inc_matrix R o i e = 0,
  { rw [H₁, zero_mul] },
  { by_cases H₂ : G.oriented_inc_matrix R o j e = 0,
    { rw [H₂, mul_zero] },
    { rcases ((G.oriented_inc_matrix_non_zero R).mp H₁) with (H_head_i | H_tail_i) ;
      rcases ((G.oriented_inc_matrix_non_zero R).mp H₂) with (H_head_j | H_tail_j),
      { rw [H_head_i, H_head_j] at H_ij, tauto },
      { exfalso, apply H_not_adj,
        rw [H_head_i, H_tail_j, ←mem_edge_set, ←o.consistent e],
        exact subtype.coe_prop e },
      { exfalso, apply H_not_adj, apply (G.edge_symm i j).mpr,
        rw [H_tail_i, H_head_j, ←mem_edge_set, ←o.consistent e],
        exact subtype.coe_prop e },
      { rw [H_tail_i, H_tail_j] at H_ij, tauto } } }
end

-- 8. `(xᵀ ⬝ N(o)) e = x o.head(e) - x o.tail(e)`.
theorem vec_mul_oriented_inc_matrix {o : orientation G} (x : V → R) (e : G.edge_set) :
  vec_mul x (G.oriented_inc_matrix R o) e = x (o.head e) - x (o.tail e) :=
begin
  simp only [vec_mul, dot_product, oriented_inc_matrix, mul_ite,
             mul_one, mul_neg_eq_neg_mul_symm, mul_zero],
  rw [sum_ite, sum_ite, sum_filter, sum_ite_eq', sum_const_zero, add_zero, filter_filter],
  simp only [mem_univ, if_true],
  have key : filter (λ (a : V), ¬a = o.head e ∧ a = o.tail e) univ = {o.tail e},
  { ext,
    simp only [mem_filter, mem_singleton, true_and, and_iff_right_iff_imp, mem_univ],
    rintro rfl,
    exact ne.symm (G.head_neq_tail) },
  rw [key, sum_singleton],
  ring_nf
end

end oriented_incidence

end simple_graph
