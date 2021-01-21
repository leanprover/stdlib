/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import analysis.convex.basic

/-!
# Carathéodory's convexity theorem

This file is devoted to proving Carathéodory's convexity theorem:
The convex hull of a set `s` in ℝᵈ is the union of the convex hulls of the (d+1)-tuples in `s`.

## Main results:

* `convex_hull_eq_union`: Carathéodory's convexity theorem

## Implementation details

This theorem was formalized as part of the Sphere Eversion project.

## Tags
convex hull, caratheodory

-/

universes u

open set finset finite_dimensional
open_locale big_operators

variables {E : Type u} [add_comm_group E] [vector_space ℝ E] [finite_dimensional ℝ E]

namespace caratheodory

/--
If `x` is in the convex hull of some finset `t` with strictly more than `findim + 1` elements,
then it is in the union of the convex hulls of the finsets `t.erase y` for `y ∈ t`.
-/
lemma mem_convex_hull_erase [decidable_eq E] {t : finset E} (h : findim ℝ E + 1 < t.card)
  {x : E} (m : x ∈ convex_hull (↑t : set E)) :
  ∃ (y : (↑t : set E)), x ∈ convex_hull (↑(t.erase y) : set E) :=
begin
  simp only [finset.convex_hull_eq, mem_set_of_eq] at m ⊢,
  obtain ⟨f, fpos, fsum, rfl⟩ := m,
  obtain ⟨g, gcombo, gsum, gpos⟩ := exists_relation_sum_zero_pos_coefficient_of_dim_succ_lt_card h,
  clear h,
  let s := t.filter (λ z : E, 0 < g z),
  obtain ⟨i₀, mem, w⟩ : ∃ i₀ ∈ s, ∀ i ∈ s, f i₀ / g i₀ ≤ f i / g i,
  { apply s.exists_min_image (λ z, f z / g z),
    obtain ⟨x, hx, hgx⟩ : ∃ x ∈ t, 0 < g x := gpos,
    exact ⟨x, mem_filter.mpr ⟨hx, hgx⟩⟩, },
  have hg   : 0 < g i₀ := by { rw mem_filter at mem, exact mem.2 },
  have hi₀  : i₀ ∈ t   := filter_subset _ _ mem,
  let  k    : E → ℝ    := λ z, f z - (f i₀ / g i₀) * g z,
  have hk   : k i₀ = 0 := by field_simp [k, ne_of_gt hg],
  have ksum : ∑ e in t.erase i₀, k e = 1,
  { calc ∑ e in t.erase i₀, k e = ∑ e in t, k e :
      by conv_rhs { rw [← insert_erase hi₀, sum_insert (not_mem_erase i₀ t), hk, zero_add], }
    ... = ∑ e in t, (f e - f i₀ / g i₀ * g e) : rfl
    ... = 1 : by rw [sum_sub_distrib, fsum, ← mul_sum, gsum, mul_zero, sub_zero] },
  refine ⟨⟨i₀, hi₀⟩, k, _, ksum, _⟩,
  { simp only [and_imp, sub_nonneg, mem_erase, ne.def, subtype.coe_mk],
    intros e hei₀ het,
    by_cases hes : e ∈ s,
    { have hge : 0 < g e := by { rw mem_filter at hes, exact hes.2 },
      rw ← le_div_iff hge,
      exact w _ hes, },
    { calc _ ≤ 0   : mul_nonpos_of_nonneg_of_nonpos _ _ -- prove two goals below
         ... ≤ f e : fpos e het,
      { apply div_nonneg (fpos i₀ (mem_of_subset (filter_subset _ t) mem)) (le_of_lt hg) },
      { simpa only [mem_filter, het, true_and, not_lt] using hes }, } },
  { simp only [subtype.coe_mk, center_mass_eq_of_sum_1 _ id ksum, id],
    calc ∑ e in t.erase i₀, k e • e = ∑ e in t, k e • e :
      by conv_rhs { rw [← insert_erase hi₀, sum_insert (not_mem_erase i₀ t), hk, zero_smul, zero_add], }
    ... = ∑ e in t, (f e - f i₀ / g i₀ * g e) • e : rfl
    ... = t.center_mass f id : _,
    simp only [sub_smul, mul_smul, sum_sub_distrib, ← smul_sum, gcombo, smul_zero,
      sub_zero, center_mass, fsum, inv_one, one_smul, id.def], },
end

/--
The convex hull of a finset `t` with `findim ℝ E + 1 < t.card` is equal to
the union of the convex hulls of the finsets `t.erase x` for `x ∈ t`.
-/
lemma step [decidable_eq E] (t : finset E) (h : findim ℝ E + 1 < t.card) :
  convex_hull (↑t : set E) = ⋃ (x : (↑t : set E)), convex_hull ↑(t.erase x) :=
begin
  apply set.subset.antisymm,
  { intros x m',
    obtain ⟨y, m⟩ := mem_convex_hull_erase h m',
    exact mem_Union.2 ⟨y, m⟩, },
  { refine Union_subset _,
    intro x,
    apply convex_hull_mono,
    apply erase_subset, }
end

/--
The convex hull of a finset `t` with `findim ℝ E + 1 < t.card` is contained in
the union of the convex hulls of the finsets `t' ⊆ t` with `t'.card ≤ findim ℝ E + 1`.
-/
lemma shrink' (t : finset E) (k : ℕ) (h : t.card = findim ℝ E + 1 + k) :
  convex_hull (↑t : set E) ⊆
    ⋃ (t' : finset E) (w : t' ⊆ t) (b : t'.card ≤ findim ℝ E + 1), convex_hull ↑t' :=
begin
  induction k with k ih generalizing t,
  { apply subset_subset_Union t,
    apply subset_subset_Union (set.subset.refl _),
    exact subset_subset_Union (le_of_eq h) (subset.refl _), },
  { classical,
    rw step _ (by { rw h, simp, } : findim ℝ E + 1 < t.card),
    apply Union_subset,
    intro i,
    transitivity,
    { apply ih,
      rw [card_erase_of_mem, h, nat.pred_succ],
      exact i.2, },
    { apply Union_subset_Union,
      intro t',
      apply Union_subset_Union_const,
      exact λ h, set.subset.trans h (erase_subset _ _), } }
end

/--
The convex hull of any finset `t` is contained in
the union of the convex hulls of the finsets `t' ⊆ t` with `t'.card ≤ findim ℝ E + 1`.
-/
lemma shrink (t : finset E) :
  convex_hull (↑t : set E) ⊆
    ⋃ (t' : finset E) (w : t' ⊆ t) (b : t'.card ≤ findim ℝ E + 1), convex_hull ↑t' :=
begin
  by_cases h : t.card ≤ findim ℝ E + 1,
  { apply subset_subset_Union t,
    apply subset_subset_Union (set.subset.refl _),
    exact subset_subset_Union h (set.subset.refl _), },
  push_neg at h,
  obtain ⟨k, w⟩ := le_iff_exists_add.mp (le_of_lt h), clear h,
  exact shrink' _ _ w,
end

end caratheodory

/--
One inclusion of Carathéodory's convexity theorem.

The convex hull of a set `s` in ℝᵈ is contained in
the union of the convex hulls of the (d+1)-tuples in `s`.
-/
lemma convex_hull_subset_union (s : set E) :
  convex_hull s ⊆ ⋃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1), convex_hull ↑t :=
begin
  -- First we replace `convex_hull s` with the union of the convex hulls of finite subsets,
  rw convex_hull_eq_union_convex_hull_finite_subsets,
  -- and prove the inclusion for each of those.
  apply Union_subset, intro r,
  apply Union_subset, intro h,
  -- Second, for each convex hull of a finite subset, we shrink it.
  transitivity,
  { apply caratheodory.shrink, },
  { -- After that it's just shuffling unions around.
    apply Union_subset, intro t,
    apply Union_subset, intro htr,
    apply Union_subset, intro ht,
    apply set.subset_subset_Union t,
    apply set.subset_subset_Union (subset.trans htr h),
    exact subset_Union _ ht, },
end

/--
Carathéodory's convexity theorem.

The convex hull of a set `s` in ℝᵈ is the union of the convex hulls of the (d+1)-tuples in `s`.
-/
theorem convex_hull_eq_union (s : set E) :
  convex_hull s = ⋃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1), convex_hull ↑t :=
begin
  apply set.subset.antisymm,
  { apply convex_hull_subset_union, },
  iterate 3 { convert Union_subset _, intro, },
  exact convex_hull_mono ‹_›,
end

/--
A more explicit formulation of Carathéodory's convexity theorem,
writing an element of a convex hull as the center of mass
of an explicit `finset` with cardinality at most `dim + 1`.
-/
theorem eq_center_mass_card_le_dim_succ_of_mem_convex_hull
  {s : set E} {x : E} (h : x ∈ convex_hull s) :
  ∃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1)
    (f : E → ℝ), (∀ y ∈ t, 0 ≤ f y) ∧ t.sum f = 1 ∧ t.center_mass f id = x :=
begin
  rw convex_hull_eq_union at h,
  simp only [exists_prop, mem_Union] at h,
  obtain ⟨t, w, b, m⟩ := h,
  refine ⟨t, w, b, _⟩,
  rw finset.convex_hull_eq at m,
  simpa only [exists_prop] using m,
end

/--
A variation on Carathéodory's convexity theorem,
writing an element of a convex hull as a center of mass
of an explicit `finset` with cardinality at most `dim + 1`,
where all coefficients in the center of mass formula
are strictly positive.

(This is proved using `eq_center_mass_card_le_dim_succ_of_mem_convex_hull`,
and discarding any elements of the set with coefficient zero.)
-/
theorem eq_pos_center_mass_card_le_dim_succ_of_mem_convex_hull
  {s : set E} {x : E} (h : x ∈ convex_hull s) :
  ∃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1)
    (f : E → ℝ), (∀ y ∈ t, 0 < f y) ∧ t.sum f = 1 ∧ t.center_mass f id = x :=
begin
  obtain ⟨t, w, b, f, ⟨pos, sum, center⟩⟩ := eq_center_mass_card_le_dim_succ_of_mem_convex_hull h,
  let t' := t.filter (λ z, 0 < f z),
  have t'sum : t'.sum f = 1,
  { convert sum using 1,
    symmetry,
    fapply sum_bij_ne_zero (λ z h w, z),
    { intros z m nz,
      exact multiset.mem_filter_of_mem m (lt_of_le_of_ne (pos z m) (ne.symm nz)), },
    { intros _ _ _ _ _ _ a, exact a, },
    { intros z m nz,
      exact ⟨z, mem_of_subset (filter_subset _ t) m, nz, rfl⟩, },
    { intros, refl, }, },
  refine ⟨t', _, _, f, ⟨_, _, _⟩⟩,
  { exact subset.trans (filter_subset _ t) w, },
  { exact le_trans (card_le_of_subset (filter_subset _ t)) b, },
  { exact λ y H, (mem_filter.mp H).right, },
  { exact t'sum, },
  { convert center using 1,
    symmetry,
    simp only [center_mass, t'sum, sum, inv_one, one_smul, id.def],
    fapply sum_bij_ne_zero (λ z h w, z),
    { intros z m nz,
      have nz' : f z ≠ 0,
      { intro a, rw a at nz,
        simpa using nz, },
      exact multiset.mem_filter_of_mem m (lt_of_le_of_ne (pos z m) (ne.symm nz')), },
    { intros _ _ _ _ _ _ a, exact a, },
    { intros z m nz,
      exact ⟨z, mem_of_subset (filter_subset _ t) m, nz, rfl⟩, },
    { intros, refl, }, },
end
