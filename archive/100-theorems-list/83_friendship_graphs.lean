/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller
-/
import combinatorics.simple_graph.adj_matrix
import linear_algebra.char_poly.coeff
import data.int.modeq
import data.zmod.basic
import tactic.interval_cases

/-!
# The Friendship Theorem

## Definitions and Statement
- A `friendship` graph is one in which any two distinct vertices have exactly one neighbor in common
- A `politician`, at least in the context of this problem, is a vertex in a graph which is adjacent
  to every other vertex.
- The friendship theorem (Erdős, Rényi, Sós 1966) states that every finite friendship graph has a
  politician.

## Proof outline
The proof revolves around the theory of adjacency matrices, although some steps could equivalently
be phrased in terms of counting walks.
- Assume `G` is a finite friendship graph.
- First we show that any two nonadjacent vertices have the same degree
- Assume for contradiction that `G` does not have a politician.
- Conclude from the last two points that `G` is `d`-regular for some `d : ℕ`.
- Show that `G` has `d ^ 2 - d + 1` vertices.
- By casework, show that if `d = 0, 1, 2`, then `G` has a politician.
- If `3 ≤ d`, let `p` be a prime factor of `d - 1`.
- If `A` is the adjacency matrix of `G` with entries in `ℤ/pℤ`, we show that `A ^ p` has trace `1`.
- This gives a contradiction, as `A` has trace `0`, and thus `A ^ p` has trace `0`.

## References
- [P. Erdős, A. Rényi, V. Sós, *On A Problem of Graph Theory*][erdosrenyisos]
- [C. Huneke, *The Friendship Theorem*][huneke2002]

-/

open_locale classical big_operators
noncomputable theory

open finset simple_graph matrix

universes u v
variables {V : Type u} {R : Type v} [semiring R]

section friendship_def
variables (G : simple_graph V)

/--
This property of a graph is the hypothesis of the friendship theorem:
every pair of nonadjacent vertices has exactly one common friend,
a vertex to which both are adjacent.
-/
def friendship [fintype V] : Prop := ∀ ⦃v w : V⦄, v ≠ w → fintype.card (G.common_neighbors v w) = 1

/--
A politician is a vertex that is adjacent to all other vertices.
-/
def exists_politician : Prop := ∃ (v : V), ∀ (w : V), v ≠ w → G.adj v w

end friendship_def

variables [fintype V] {G : simple_graph V} {d : ℕ} (hG : friendship G)
include hG

namespace friendship

variables (R)
/-- One characterization of a friendship graph is that there is exactly one walk of length 2
  between distinct vertices. These walks are counted in off-diagonal entries of the square of
  the adjacency matrix, so for a friendship graph, those entries are all 1. -/
theorem adj_matrix_sq_of_ne {v w : V} (hvw : v ≠ w) :
  ((G.adj_matrix R) ^ 2) v w = 1 :=
begin
  rw [sq, ← nat.cast_one, ← hG hvw],
  simp [common_neighbors, neighbor_finset_eq_filter, finset.filter_filter, finset.filter_inter,
    and_comm],
end

/-- This calculation amounts to counting the number of length 3 walks between nonadjacent vertices.
  We use it to show that nonadjacent vertices have equal degrees. -/
lemma adj_matrix_pow_three_of_not_adj {v w : V} (non_adj : ¬ G.adj v w) :
  ((G.adj_matrix R) ^ 3) v w = degree G v :=
begin
  rw [pow_succ, mul_eq_mul, adj_matrix_mul_apply, degree, card_eq_sum_ones, nat.cast_sum],
  apply sum_congr rfl,
  intros x hx,
  rw [adj_matrix_sq_of_ne _ hG, nat.cast_one],
  rintro ⟨rfl⟩,
  rw mem_neighbor_finset at hx,
  exact non_adj hx,
end

variable {R}

/-- As `v` and `w` not being adjacent implies
  `degree G v = ((G.adj_matrix R) ^ 3) v w` and `degree G w = ((G.adj_matrix R) ^ 3) v w`,
  the degrees are equal if `((G.adj_matrix R) ^ 3) v w = ((G.adj_matrix R) ^ 3) w v`

  This is true as the adjacency matrix is symmetric. -/
lemma degree_eq_of_not_adj {v w : V} (hvw : ¬ G.adj v w) :
  degree G v = degree G w :=
begin
  rw [← nat.cast_id (G.degree v), ← nat.cast_id (G.degree w),
      ← adj_matrix_pow_three_of_not_adj ℕ hG hvw,
      ← adj_matrix_pow_three_of_not_adj ℕ hG (λ h, hvw (G.sym h))],
  conv_lhs {rw ← transpose_adj_matrix},
  simp only [pow_succ, sq, mul_eq_mul, ← transpose_mul, transpose_apply],
  simp only [← mul_eq_mul, mul_assoc],
end

/-- Let `A` be the adjacency matrix of a graph `G`.
  If `G` is a friendship graph, then all of the off-diagonal entries of `A^2` are 1.
  If `G` is `d`-regular, then all of the diagonal entries of `A^2` are `d`.
  Putting these together determines `A^2` exactly for a `d`-regular friendship graph. -/
theorem adj_matrix_sq_of_regular (hd : G.is_regular_of_degree d) :
  ((G.adj_matrix R) ^ 2) = λ v w, if v = w then d else 1 :=
begin
  ext v w, by_cases h : v = w,
  { rw [h, sq, mul_eq_mul, adj_matrix_mul_self_apply_self, hd], simp, },
  { rw [adj_matrix_sq_of_ne R hG h, if_neg h], },
end

lemma adj_matrix_sq_mod_p_of_regular {p : ℕ} (dmod : (d : zmod p) = 1)
  (hd : G.is_regular_of_degree d) :
  (G.adj_matrix (zmod p)) ^ 2 = λ _ _, 1 :=
by simp [adj_matrix_sq_of_regular hG hd, dmod]

section nonempty

variable [nonempty V]

/-- If `G` is a friendship graph without a politician (a vertex adjacent to all others), then
  it is regular. We have shown that nonadjacent vertices of a friendship graph have the same degree,
  and if there isn't a politician, we can show this for adjacent vertices by finding a vertex
  neither is adjacent to, and then using transitivity. -/
theorem is_regular_of_not_exists_politician (hG' : ¬exists_politician G) :
  ∃ (d : ℕ), G.is_regular_of_degree d :=
begin
  have v := classical.arbitrary V,
  use G.degree v,
  intro x,
  by_cases hvx : G.adj v x, swap, { exact (degree_eq_of_not_adj hG hvx).symm, },
  dunfold exists_politician at hG',
  push_neg at hG',
  rcases hG' v with ⟨w, hvw', hvw⟩,
  rcases hG' x with ⟨y, hxy', hxy⟩,
  by_cases hxw : G.adj x w,
    swap, { rw degree_eq_of_not_adj hG hvw, exact degree_eq_of_not_adj hG hxw },
  rw degree_eq_of_not_adj hG hxy,
  by_cases hvy : G.adj v y,
    swap, { exact (degree_eq_of_not_adj hG hvy).symm },
  rw degree_eq_of_not_adj hG hvw,
  apply degree_eq_of_not_adj hG,
  intro hcontra,
  rcases finset.card_eq_one.mp (hG hvw') with ⟨⟨a, ha⟩, h⟩,
  have key : ∀ {x}, x ∈ G.common_neighbors v w → x = a,
  { intros x hx,
    have h' := mem_univ (subtype.mk x hx),
    rw [h, mem_singleton] at h',
    injection h', },
  apply hxy',
  rw [key ((mem_common_neighbors G).mpr ⟨hvx, G.sym hxw⟩),
      key ((mem_common_neighbors G).mpr ⟨hvy, G.sym hcontra⟩)],
end

/-- Let `A` be the adjacency matrix of a `d`-regular friendship graph, and let `v` be a vector
  all of whose components are `1`. Then `v` is an eigenvector of `A ^ 2`, and we can compute
  the eigenvalue to be `d * d`, or as `d + (fintype.card V - 1)`, so those quantities must be equal.

  This essentially means that the graph has `d ^ 2 - d + 1` vertices. -/
lemma card_of_regular (hd : G.is_regular_of_degree d) :
  d + (fintype.card V - 1) = d * d :=
begin
  have v := classical.arbitrary V,
  transitivity ((G.adj_matrix ℕ) ^ 2).mul_vec (λ _, 1) v,
  { rw [adj_matrix_sq_of_regular hG hd, mul_vec, dot_product, ← insert_erase (mem_univ v)],
    simp only [sum_insert, mul_one, if_true, nat.cast_id, eq_self_iff_true,
               mem_erase, not_true, ne.def, not_false_iff, add_right_inj, false_and],
    rw [finset.sum_const_nat, card_erase_of_mem (mem_univ v), mul_one], { refl },
    intros x hx, simp [(ne_of_mem_erase hx).symm], },
  { rw [sq, mul_eq_mul, ← mul_vec_mul_vec],
    simp [adj_matrix_mul_vec_const_apply_of_regular hd, neighbor_finset,
          card_neighbor_set_eq_degree, hd v], }
end

/-- The size of a `d`-regular friendship graph is `1 mod (d-1)`, and thus `1 mod p` for a
  factor `p ∣ d-1`. -/
lemma card_mod_p_of_regular {p : ℕ} (dmod : (d : zmod p) = 1) (hd : G.is_regular_of_degree d) :
  (fintype.card V : zmod p) = 1 :=
begin
  have hpos : 0 < fintype.card V := fintype.card_pos_iff.mpr infer_instance,
  rw [← nat.succ_pred_eq_of_pos hpos, nat.succ_eq_add_one, nat.pred_eq_sub_one],
  simp only [add_left_eq_self, nat.cast_add, nat.cast_one],
  have h := congr_arg (λ n, (↑n : zmod p)) (card_of_regular hG hd),
  revert h, simp [dmod],
end

end nonempty

omit hG

lemma adj_matrix_sq_mul_const_one_of_regular (hd : G.is_regular_of_degree d) :
  (G.adj_matrix R) * (λ _ _, 1) = λ _ _, d :=
by { ext x, simp [← hd x, degree] }

lemma adj_matrix_mul_const_one_mod_p_of_regular {p : ℕ} (dmod : (d : zmod p) = 1)
  (hd : G.is_regular_of_degree d) :
  (G.adj_matrix (zmod p)) * (λ _ _, 1) = λ _ _, 1 :=
by rw [adj_matrix_sq_mul_const_one_of_regular hd, dmod]

include hG

/-- Modulo a factor of `d-1`, the square and all higher powers of the adjacency matrix
  of a `d`-regular friendship graph reduce to the matrix whose entries are all 1. -/
lemma adj_matrix_pow_mod_p_of_regular {p : ℕ} (dmod : (d : zmod p) = 1)
  (hd : G.is_regular_of_degree d) {k : ℕ} (hk : 2 ≤ k) :
  (G.adj_matrix (zmod p)) ^ k = λ _ _, 1 :=
begin
  iterate 2 {cases k with k, { exfalso, linarith, }, },
  induction k with k hind,
  { exact adj_matrix_sq_mod_p_of_regular hG dmod hd, },
  rw [pow_succ, hind (nat.le_add_left 2 k)],
  exact adj_matrix_mul_const_one_mod_p_of_regular dmod hd,
end

variable [nonempty V]

/-- This is the main proof. Assuming that `3 ≤ d`, we take `p` to be a prime factor of `d-1`.
  Then the `p`th power of the adjacency matrix of a `d`-regular friendship graph must have trace 1
  mod `p`, but we can also show that the trace must be the `p`th power of the trace of the original
  adjacency matrix, which is 0, a contradiction.
-/
lemma false_of_three_le_degree (hd : G.is_regular_of_degree d) (h : 3 ≤ d) : false :=
begin
  -- get a prime factor of d - 1
  let p : ℕ := (d - 1).min_fac,
  have p_dvd_d_pred := (zmod.nat_coe_zmod_eq_zero_iff_dvd _ _).mpr (d - 1).min_fac_dvd,
  have dpos : 0 < d := by linarith,
  have d_cast : ↑(d - 1) = (d : ℤ) - 1 := by norm_cast,
  haveI : fact p.prime := ⟨nat.min_fac_prime (by linarith)⟩,
  have hp2 : 2 ≤ p := (fact.out p.prime).two_le,
  have dmod : (d : zmod p) = 1,
  { rw [← nat.succ_pred_eq_of_pos dpos, nat.succ_eq_add_one, nat.pred_eq_sub_one],
    simp only [add_left_eq_self, nat.cast_add, nat.cast_one],
    exact p_dvd_d_pred, },
  have Vmod := card_mod_p_of_regular hG dmod hd,
  -- now we reduce to a trace calculation
  have := zmod.trace_pow_card (G.adj_matrix (zmod p)),
  contrapose! this, clear this,
  -- the trace is 0 mod p when computed one way
  rw [trace_adj_matrix, zero_pow (fact.out p.prime).pos],
  -- but the trace is 1 mod p when computed the other way
  rw adj_matrix_pow_mod_p_of_regular hG dmod hd hp2,
  dunfold fintype.card at Vmod,
  simp only [matrix.trace, diag_apply, mul_one, nsmul_eq_mul, linear_map.coe_mk, sum_const],
  rw [Vmod, ← nat.cast_one, zmod.nat_coe_zmod_eq_zero_iff_dvd, nat.dvd_one,
    nat.min_fac_eq_one_iff],
  linarith,
end

/-- If `d ≤ 1`, a `d`-regular friendship graph has at most one vertex, which is
  trivially a politician. -/
lemma exists_politician_of_degree_le_one (hd : G.is_regular_of_degree d) (hd1 : d ≤ 1) :
  exists_politician G :=
begin
  have sq : d * d = d := by { interval_cases d; norm_num },
  have h := card_of_regular hG hd,
  rw sq at h,
  have : fintype.card V ≤ 1,
  { cases fintype.card V with n,
    { exact zero_le _, },
    { have : n = 0,
      { rw [nat.succ_sub_succ_eq_sub, nat.sub_zero] at h,
        linarith },
      subst n, } },
  use classical.arbitrary V,
  intros w h, exfalso,
  apply h,
  apply fintype.card_le_one_iff.mp this,
end

/-- If `d = 2`, a `d`-regular friendship graph has 3 vertices, so it must be complete graph,
  and all the vertices are politicians. -/
lemma neighbor_finset_eq_of_degree_eq_two (hd : G.is_regular_of_degree 2) (v : V) :
  G.neighbor_finset v = finset.univ.erase v :=
begin
  apply finset.eq_of_subset_of_card_le,
  { rw finset.subset_iff,
    intro x,
    rw [mem_neighbor_finset, finset.mem_erase],
    exact λ h, ⟨(G.ne_of_adj h).symm, finset.mem_univ _⟩ },
  convert_to 2 ≤ _,
  { convert_to _ = fintype.card V - 1,
    { have hfr:= card_of_regular hG hd,
      linarith },
    { exact finset.card_erase_of_mem (finset.mem_univ _), }, },
  { dsimp [is_regular_of_degree, degree] at hd,
    rw hd, }
end

lemma exists_politician_of_degree_eq_two (hd : G.is_regular_of_degree 2) :
  exists_politician G :=
begin
  have v := classical.arbitrary V,
  use v,
  intros w hvw,
  rw [← mem_neighbor_finset, neighbor_finset_eq_of_degree_eq_two hG hd v, finset.mem_erase],
  exact ⟨hvw.symm, finset.mem_univ _⟩,
end

lemma exists_politician_of_degree_le_two (hd : G.is_regular_of_degree d) (h : d ≤ 2) :
  exists_politician G :=
begin
  interval_cases d,
  iterate 2 { apply exists_politician_of_degree_le_one hG hd, norm_num },
  { exact exists_politician_of_degree_eq_two hG hd },
end

end friendship

/-- **Friendship theorem**: We wish to show that a friendship graph has a politician (a vertex
  adjacent to all others). We proceed by contradiction, and assume the graph has no politician.
  We have already proven that a friendship graph with no politician is `d`-regular for some `d`,
  and now we do casework on `d`.
  If the degree is at most 2, we observe by casework that it has a politician anyway.
  If the degree is at least 3, the graph cannot exist. -/
theorem friendship_theorem [nonempty V] : exists_politician G :=
begin
  by_contradiction npG,
  rcases hG.is_regular_of_not_exists_politician npG with ⟨d, dreg⟩,
  cases lt_or_le d 3 with dle2 dge3,
  { exact npG (hG.exists_politician_of_degree_le_two dreg (nat.lt_succ_iff.mp dle2)) },
  { exact hG.false_of_three_le_degree dreg dge3 },
end
