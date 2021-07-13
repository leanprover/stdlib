/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import linear_algebra.affine_space.independent
import linear_algebra.finite_dimensional

/-!
# Finite-dimensional subspaces of affine spaces.

This file provides a few results relating to finite-dimensional
subspaces of affine spaces.

## Main definitions

* `collinear` defines collinear sets of points as those that span a
  subspace of dimension at most 1.

-/

noncomputable theory
open_locale big_operators classical affine

section affine_space'

variables (k : Type*) {V : Type*} {P : Type*} [field k] [add_comm_group V] [module k V]
          [affine_space V P]
variables {ι : Type*}
include V

open affine_subspace finite_dimensional module

/-- The `vector_span` of a finite set is finite-dimensional. -/
lemma finite_dimensional_vector_span_of_finite {s : set P} (h : set.finite s) :
  finite_dimensional k (vector_span k s) :=
span_of_finite k $ h.vsub h

/-- The `vector_span` of a family indexed by a `fintype` is
finite-dimensional. -/
instance finite_dimensional_vector_span_of_fintype [fintype ι] (p : ι → P) :
  finite_dimensional k (vector_span k (set.range p)) :=
finite_dimensional_vector_span_of_finite k (set.finite_range _)

/-- The `vector_span` of a subset of a family indexed by a `fintype`
is finite-dimensional. -/
instance finite_dimensional_vector_span_image_of_fintype [fintype ι] (p : ι → P)
  (s : set ι) : finite_dimensional k (vector_span k (p '' s)) :=
finite_dimensional_vector_span_of_finite k ((set.finite.of_fintype _).image _)

/-- The direction of the affine span of a finite set is
finite-dimensional. -/
lemma finite_dimensional_direction_affine_span_of_finite {s : set P} (h : set.finite s) :
  finite_dimensional k (affine_span k s).direction :=
(direction_affine_span k s).symm ▸ finite_dimensional_vector_span_of_finite k h

/-- The direction of the affine span of a family indexed by a
`fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_of_fintype [fintype ι] (p : ι → P) :
  finite_dimensional k (affine_span k (set.range p)).direction :=
finite_dimensional_direction_affine_span_of_finite k (set.finite_range _)

/-- The direction of the affine span of a subset of a family indexed
by a `fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_image_of_fintype [fintype ι] (p : ι → P)
  (s : set ι) : finite_dimensional k (affine_span k (p '' s)).direction :=
finite_dimensional_direction_affine_span_of_finite k ((set.finite.of_fintype _).image _)

variables {k}

/-- The `vector_span` of a finite subset of an affinely independent
family has dimension one less than its cardinality. -/
lemma finrank_vector_span_image_finset_of_affine_independent {p : ι → P}
  (hi : affine_independent k p) {s : finset ι} {n : ℕ} (hc : finset.card s = n + 1) :
  finrank k (vector_span k (s.image p : set P)) = n :=
begin
  have hi' := affine_independent_of_subset_affine_independent
    (affine_independent_set_of_affine_independent hi) (set.image_subset_range p ↑s),
  have hc' : (s.image p).card = n + 1,
  { rwa [s.card_image_of_injective (injective_of_affine_independent hi)] },
  have hn : (s.image p).nonempty,
  { simp [hc', ←finset.card_pos] },
  rcases hn with ⟨p₁, hp₁⟩,
  have hp₁' : p₁ ∈ p '' s := by simpa using hp₁,
  rw [affine_independent_set_iff_linear_independent_vsub k hp₁', ← finset.coe_singleton,
      ← finset.coe_image, ← finset.coe_sdiff, finset.sdiff_singleton_eq_erase,
      ← finset.coe_image] at hi',
  have hc : (finset.image (λ (p : P), p -ᵥ p₁) ((finset.image p s).erase p₁)).card = n,
  { rw [finset.card_image_of_injective _ (vsub_left_injective _),
        finset.card_erase_of_mem hp₁],
    exact nat.pred_eq_of_eq_succ hc' },
  rwa [vector_span_eq_span_vsub_finset_right_ne k hp₁, finrank_span_finset_eq_card, hc]
end

/-- The `vector_span` of a finite affinely independent family has
dimension one less than its cardinality. -/
lemma finrank_vector_span_of_affine_independent [fintype ι] {p : ι → P}
  (hi : affine_independent k p) {n : ℕ} (hc : fintype.card ι = n + 1) :
  finrank k (vector_span k (set.range p)) = n :=
begin
  rw ← finset.card_univ at hc,
  rw [← set.image_univ, ← finset.coe_univ, ← finset.coe_image],
  exact finrank_vector_span_image_finset_of_affine_independent hi hc
end

/-- If the `vector_span` of a finite subset of an affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
lemma vector_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one
  {p : ι → P} (hi : affine_independent k p) {s : finset ι} {sm : submodule k V}
  [finite_dimensional k sm] (hle : vector_span k (s.image p : set P) ≤ sm)
  (hc : finset.card s = finrank k sm + 1) : vector_span k (s.image p : set P) = sm :=
eq_of_le_of_finrank_eq hle $ finrank_vector_span_image_finset_of_affine_independent hi hc

/-- If the `vector_span` of a finite affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
lemma vector_span_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one [fintype ι]
  {p : ι → P} (hi : affine_independent k p) {sm : submodule k V} [finite_dimensional k sm]
  (hle : vector_span k (set.range p) ≤ sm) (hc : fintype.card ι = finrank k sm + 1) :
  vector_span k (set.range p) = sm :=
eq_of_le_of_finrank_eq hle $ finrank_vector_span_of_affine_independent hi hc

/-- If the `affine_span` of a finite subset of an affinely independent
family lies in an affine subspace whose direction has dimension one
less than its cardinality, it equals that subspace. -/
lemma affine_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one
  {p : ι → P} (hi : affine_independent k p) {s : finset ι} {sp : affine_subspace k P}
  [finite_dimensional k sp.direction] (hle : affine_span k (s.image p : set P) ≤ sp)
  (hc : finset.card s = finrank k sp.direction + 1) : affine_span k (s.image p : set P) = sp :=
begin
  have hn : (s.image p).nonempty,
  { rw [finset.nonempty.image_iff, ← finset.card_pos, hc], apply nat.succ_pos },
  refine eq_of_direction_eq_of_nonempty_of_le _ ((affine_span_nonempty k _).2 hn) hle,
  have hd := direction_le hle,
  rw direction_affine_span at ⊢ hd,
  exact vector_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one hi hd hc
end

/-- If the `affine_span` of a finite affinely independent family lies
in an affine subspace whose direction has dimension one less than its
cardinality, it equals that subspace. -/
lemma affine_span_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one [fintype ι]
  {p : ι → P} (hi : affine_independent k p) {sp : affine_subspace k P}
  [finite_dimensional k sp.direction] (hle : affine_span k (set.range p) ≤ sp)
  (hc : fintype.card ι = finrank k sp.direction + 1) : affine_span k (set.range p) = sp :=
begin
  rw ←finset.card_univ at hc,
  rw [←set.image_univ, ←finset.coe_univ, ← finset.coe_image] at ⊢ hle,
  exact affine_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one hi hle hc
end

/-- The `vector_span` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
lemma vector_span_eq_top_of_affine_independent_of_card_eq_finrank_add_one [finite_dimensional k V]
  [fintype ι] {p : ι → P} (hi : affine_independent k p) (hc : fintype.card ι = finrank k V + 1) :
  vector_span k (set.range p) = ⊤ :=
eq_top_of_finrank_eq $ finrank_vector_span_of_affine_independent hi hc

/-- The `affine_span` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
lemma affine_span_eq_top_of_affine_independent_of_card_eq_finrank_add_one [finite_dimensional k V]
  [fintype ι] {p : ι → P} (hi : affine_independent k p) (hc : fintype.card ι = finrank k V + 1) :
  affine_span k (set.range p) = ⊤ :=
begin
  rw [←finrank_top, ←direction_top k V P] at hc,
  exact affine_span_eq_of_le_of_affine_independent_of_card_eq_finrank_add_one hi le_top hc
end

variables (k)

/-- The `vector_span` of `n + 1` points in an indexed family has
dimension at most `n`. -/
lemma finrank_vector_span_image_finset_le (p : ι → P) (s : finset ι) {n : ℕ}
  (hc : finset.card s = n + 1) : finrank k (vector_span k (s.image p : set P)) ≤ n :=
begin
  have hn : (s.image p).nonempty,
  { rw [finset.nonempty.image_iff, ← finset.card_pos, hc], apply nat.succ_pos },
  rcases hn with ⟨p₁, hp₁⟩,
  rw [vector_span_eq_span_vsub_finset_right_ne k hp₁],
  refine le_trans (finrank_span_finset_le_card (((s.image p).erase p₁).image (λ p, p -ᵥ p₁))) _,
  rw [finset.card_image_of_injective _ (vsub_left_injective p₁), finset.card_erase_of_mem hp₁,
      nat.pred_le_iff, nat.succ_eq_add_one, ← hc],
  apply finset.card_image_le
end

/-- The `vector_span` of an indexed family of `n + 1` points has
dimension at most `n`. -/
lemma finrank_vector_span_range_le [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 1) : finrank k (vector_span k (set.range p)) ≤ n :=
begin
  rw [←set.image_univ, ←finset.coe_univ, ← finset.coe_image],
  rw ←finset.card_univ at hc,
  exact finrank_vector_span_image_finset_le _ _ _ hc
end

/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension `n`. -/
lemma affine_independent_iff_finrank_vector_span_eq [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 1) :
  affine_independent k p ↔ finrank k (vector_span k (set.range p)) = n :=
begin
  have hn : nonempty ι, by simp [←fintype.card_pos_iff, hc],
  cases hn with i₁,
  rw [affine_independent_iff_linear_independent_vsub _ _ i₁,
      linear_independent_iff_card_eq_finrank_span, eq_comm,
      vector_span_range_eq_span_range_vsub_right_ne k p i₁],
  congr',
  rw ←finset.card_univ at hc,
  rw fintype.subtype_card,
  simp [finset.filter_ne', finset.card_erase_of_mem, hc]
end

/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension at least `n`. -/
lemma affine_independent_iff_le_finrank_vector_span [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 1) :
  affine_independent k p ↔ n ≤ finrank k (vector_span k (set.range p)) :=
begin
  rw affine_independent_iff_finrank_vector_span_eq k p hc,
  split,
  { rintro rfl,
    refl },
  { exact λ hle, le_antisymm (finrank_vector_span_range_le k p hc) hle }
end

/-- `n + 2` points are affinely independent if and only if their
`vector_span` does not have dimension at most `n`. -/
lemma affine_independent_iff_not_finrank_vector_span_le [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 2) :
  affine_independent k p ↔ ¬ finrank k (vector_span k (set.range p)) ≤ n :=
by rw [affine_independent_iff_le_finrank_vector_span k p hc, ←lt_iff_add_one_le, lt_iff_not_ge]

/-- `n + 2` points have a `vector_span` with dimension at most `n` if
and only if they are not affinely independent. -/
lemma finrank_vector_span_le_iff_not_affine_independent [fintype ι] (p : ι → P) {n : ℕ}
  (hc : fintype.card ι = n + 2) :
  finrank k (vector_span k (set.range p)) ≤ n ↔ ¬ affine_independent k p :=
(not_iff_comm.1 (affine_independent_iff_not_finrank_vector_span_le k p hc).symm).symm

/-- A set of points is collinear if their `vector_span` has dimension
at most `1`. -/
def collinear (s : set P) : Prop := module.rank k (vector_span k s) ≤ 1

/-- The definition of `collinear`. -/
lemma collinear_iff_dim_le_one (s : set P) : collinear k s ↔ module.rank k (vector_span k s) ≤ 1 :=
iff.rfl

/-- A set of points, whose `vector_span` is finite-dimensional, is
collinear if and only if their `vector_span` has dimension at most
`1`. -/
lemma collinear_iff_finrank_le_one (s : set P) [finite_dimensional k (vector_span k s)] :
  collinear k s ↔ finrank k (vector_span k s) ≤ 1 :=
begin
  have h := collinear_iff_dim_le_one k s,
  rw ←finrank_eq_dim at h,
  exact_mod_cast h
end

variables (P)

/-- The empty set is collinear. -/
lemma collinear_empty : collinear k (∅ : set P) :=
begin
  rw [collinear_iff_dim_le_one, vector_span_empty],
  simp
end

variables {P}

/-- A single point is collinear. -/
lemma collinear_singleton (p : P) : collinear k ({p} : set P) :=
begin
  rw [collinear_iff_dim_le_one, vector_span_singleton],
  simp
end

/-- Given a point `p₀` in a set of points, that set is collinear if and
only if the points can all be expressed as multiples of the same
vector, added to `p₀`. -/
lemma collinear_iff_of_mem {s : set P} {p₀ : P} (h : p₀ ∈ s) :
  collinear k s ↔ ∃ v : V, ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ :=
begin
  simp_rw [collinear_iff_dim_le_one, dim_submodule_le_one_iff', submodule.le_span_singleton_iff],
  split,
  { rintro ⟨v₀, hv⟩,
    use v₀,
    intros p hp,
    obtain ⟨r, hr⟩ := hv (p -ᵥ p₀) (vsub_mem_vector_span k hp h),
    use r,
    rw eq_vadd_iff_vsub_eq,
    exact hr.symm },
  { rintro ⟨v, hp₀v⟩,
    use v,
    intros w hw,
    have hs : vector_span k s ≤ k ∙ v,
    { rw [vector_span_eq_span_vsub_set_right k h, submodule.span_le, set.subset_def],
      intros x hx,
      rw [set_like.mem_coe, submodule.mem_span_singleton],
      rw set.mem_image at hx,
      rcases hx with ⟨p, hp, rfl⟩,
      rcases hp₀v p hp with ⟨r, rfl⟩,
      use r,
      simp },
    have hw' := set_like.le_def.1 hs hw,
    rwa submodule.mem_span_singleton at hw' }
end

/-- A set of points is collinear if and only if they can all be
expressed as multiples of the same vector, added to the same base
point. -/
lemma collinear_iff_exists_forall_eq_smul_vadd (s : set P) :
  collinear k s ↔ ∃ (p₀ : P) (v : V), ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ :=
begin
  rcases set.eq_empty_or_nonempty s with rfl | ⟨⟨p₁, hp₁⟩⟩,
  { simp [collinear_empty] },
  { rw collinear_iff_of_mem k hp₁,
    split,
    { exact λ h, ⟨p₁, h⟩ },
    { rintros ⟨p, v, hv⟩,
      use v,
      intros p₂ hp₂,
      rcases hv p₂ hp₂ with ⟨r, rfl⟩,
      rcases hv p₁ hp₁ with ⟨r₁, rfl⟩,
      use r - r₁,
      simp [vadd_vadd, ←add_smul] } }
end

/-- Two points are collinear. -/
lemma collinear_insert_singleton (p₁ p₂ : P) : collinear k ({p₁, p₂} : set P) :=
begin
  rw collinear_iff_exists_forall_eq_smul_vadd,
  use [p₁, p₂ -ᵥ p₁],
  intros p hp,
  rw [set.mem_insert_iff, set.mem_singleton_iff] at hp,
  cases hp,
  { use 0,
    simp [hp] },
  { use 1,
    simp [hp] }
end

/-- Three points are affinely independent if and only if they are not
collinear. -/
lemma affine_independent_iff_not_collinear (p : fin 3 → P) :
  affine_independent k p ↔ ¬ collinear k (set.range p) :=
by rw [collinear_iff_finrank_le_one,
       affine_independent_iff_not_finrank_vector_span_le k p (fintype.card_fin 3)]

/-- Three points are collinear if and only if they are not affinely
independent. -/
lemma collinear_iff_not_affine_independent (p : fin 3 → P) :
  collinear k (set.range p) ↔ ¬ affine_independent k p :=
by rw [collinear_iff_finrank_le_one,
       finrank_vector_span_le_iff_not_affine_independent k p (fintype.card_fin 3)]

end affine_space'
