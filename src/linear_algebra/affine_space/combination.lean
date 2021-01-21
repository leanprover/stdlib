/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import algebra.invertible
import linear_algebra.affine_space.affine_map
import linear_algebra.affine_space.affine_subspace
import linear_algebra.finsupp

/-!
# Affine combinations of points

This file defines affine combinations of points.

## Main definitions

* `weighted_vsub_of_point` is a general weighted combination of
  subtractions with an explicit base point, yielding a vector.

* `weighted_vsub` uses an arbitrary choice of base point and is intended
  to be used when the sum of weights is 0, in which case the result is
  independent of the choice of base point.

* `affine_combination` adds the weighted combination to the arbitrary
  base point, yielding a point rather than a vector, and is intended
  to be used when the sum of weights is 1, in which case the result is
  independent of the choice of base point.

These definitions are for sums over a `finset`; versions for a
`fintype` may be obtained using `finset.univ`, while versions for a
`finsupp` may be obtained using `finsupp.support`.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/

noncomputable theory
open_locale big_operators classical affine

namespace finset

variables {k : Type*} {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [S : affine_space V P]
include S

variables {ι : Type*} (s : finset ι)
variables {ι₂ : Type*} (s₂ : finset ι₂)

/-- A weighted sum of the results of subtracting a base point from the
given points, as a linear map on the weights.  The main cases of
interest are where the sum of the weights is 0, in which case the sum
is independent of the choice of base point, and where the sum of the
weights is 1, in which case the sum added to the base point is
independent of the choice of base point. -/
def weighted_vsub_of_point (p : ι → P) (b : P) : (ι → k) →ₗ[k] V :=
∑ i in s, (linear_map.proj i : (ι → k) →ₗ[k] k).smul_right (p i -ᵥ b)

@[simp] lemma weighted_vsub_of_point_apply (w : ι → k) (p : ι → P) (b : P) :
  s.weighted_vsub_of_point p b w = ∑ i in s, w i • (p i -ᵥ b) :=
by simp [weighted_vsub_of_point, linear_map.sum_apply]

/-- The weighted sum is independent of the base point when the sum of
the weights is 0. -/
lemma weighted_vsub_of_point_eq_of_sum_eq_zero (w : ι → k) (p : ι → P) (h : ∑ i in s, w i = 0)
    (b₁ b₂ : P) : s.weighted_vsub_of_point p b₁ w = s.weighted_vsub_of_point p b₂ w :=
begin
  apply eq_of_sub_eq_zero,
  rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply, ←sum_sub_distrib],
  conv_lhs {
    congr,
    skip,
    funext,
    rw [←smul_sub, vsub_sub_vsub_cancel_left]
  },
  rw [←sum_smul, h, zero_smul]
end

/-- The weighted sum, added to the base point, is independent of the
base point when the sum of the weights is 1. -/
lemma weighted_vsub_of_point_vadd_eq_of_sum_eq_one (w : ι → k) (p : ι → P) (h : ∑ i in s, w i = 1)
    (b₁ b₂ : P) :
  s.weighted_vsub_of_point p b₁ w +ᵥ b₁ = s.weighted_vsub_of_point p b₂ w +ᵥ b₂ :=
begin
  erw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply, ←@vsub_eq_zero_iff_eq V,
       vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, ←add_sub_assoc, add_comm, add_sub_assoc,
       ←sum_sub_distrib],
  conv_lhs {
    congr,
    skip,
    congr,
    skip,
    funext,
    rw [←smul_sub, vsub_sub_vsub_cancel_left]
  },
  rw [←sum_smul, h, one_smul, vsub_add_vsub_cancel, vsub_self]
end

/-- The weighted sum is unaffected by removing the base point, if
present, from the set of points. -/
@[simp] lemma weighted_vsub_of_point_erase (w : ι → k) (p : ι → P) (i : ι) :
  (s.erase i).weighted_vsub_of_point p (p i) w = s.weighted_vsub_of_point p (p i) w :=
begin
  rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply],
  apply sum_erase,
  rw [vsub_self, smul_zero]
end

/-- The weighted sum is unaffected by adding the base point, whether
or not present, to the set of points. -/
@[simp] lemma weighted_vsub_of_point_insert (w : ι → k) (p : ι → P) (i : ι) :
  (insert i s).weighted_vsub_of_point p (p i) w = s.weighted_vsub_of_point p (p i) w :=
begin
  rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply],
  apply sum_insert_zero,
  rw [vsub_self, smul_zero]
end

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
lemma weighted_vsub_of_point_indicator_subset (w : ι → k) (p : ι → P) (b : P) {s₁ s₂ : finset ι}
    (h : s₁ ⊆ s₂) :
  s₁.weighted_vsub_of_point p b w = s₂.weighted_vsub_of_point p b (set.indicator ↑s₁ w) :=
begin
  rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply],
  exact set.sum_indicator_subset_of_eq_zero w (λ i wi, wi • (p i -ᵥ b : V)) h (λ i, zero_smul k _)
end

/-- A weighted sum, over the image of an embedding, equals a weighted
sum with the same points and weights over the original
`finset`. -/
lemma weighted_vsub_of_point_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) (b : P) :
  (s₂.map e).weighted_vsub_of_point p b w = s₂.weighted_vsub_of_point (p ∘ e) b (w ∘ e) :=
begin
  simp_rw [weighted_vsub_of_point_apply],
  exact finset.sum_map _ _ _
end

/-- A weighted sum of the results of subtracting a default base point
from the given points, as a linear map on the weights.  This is
intended to be used when the sum of the weights is 0; that condition
is specified as a hypothesis on those lemmas that require it. -/
def weighted_vsub (p : ι → P) : (ι → k) →ₗ[k] V :=
s.weighted_vsub_of_point p (classical.choice S.nonempty)

/-- Applying `weighted_vsub` with given weights.  This is for the case
where a result involving a default base point is OK (for example, when
that base point will cancel out later); a more typical use case for
`weighted_vsub` would involve selecting a preferred base point with
`weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero` and then
using `weighted_vsub_of_point_apply`. -/
lemma weighted_vsub_apply (w : ι → k) (p : ι → P) :
  s.weighted_vsub p w = ∑ i in s, w i • (p i -ᵥ (classical.choice S.nonempty)) :=
by simp [weighted_vsub, linear_map.sum_apply]

/-- `weighted_vsub` gives the sum of the results of subtracting any
base point, when the sum of the weights is 0. -/
lemma weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero (w : ι → k) (p : ι → P)
    (h : ∑ i in s, w i = 0) (b : P) : s.weighted_vsub p w = s.weighted_vsub_of_point p b w :=
s.weighted_vsub_of_point_eq_of_sum_eq_zero w p h _ _

/-- The `weighted_vsub` for an empty set is 0. -/
@[simp] lemma weighted_vsub_empty (w : ι → k) (p : ι → P) :
  (∅ : finset ι).weighted_vsub p w = (0:V) :=
by simp [weighted_vsub_apply]

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
lemma weighted_vsub_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : finset ι} (h : s₁ ⊆ s₂) :
  s₁.weighted_vsub p w = s₂.weighted_vsub p (set.indicator ↑s₁ w) :=
weighted_vsub_of_point_indicator_subset _ _ _ h

/-- A weighted subtraction, over the image of an embedding, equals a
weighted subtraction with the same points and weights over the
original `finset`. -/
lemma weighted_vsub_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
  (s₂.map e).weighted_vsub p w = s₂.weighted_vsub (p ∘ e) (w ∘ e) :=
s₂.weighted_vsub_of_point_map _ _ _ _

/-- A weighted sum of the results of subtracting a default base point
from the given points, added to that base point, as an affine map on
the weights.  This is intended to be used when the sum of the weights
is 1, in which case it is an affine combination (barycenter) of the
points with the given weights; that condition is specified as a
hypothesis on those lemmas that require it. -/
def affine_combination (p : ι → P) : (ι → k) →ᵃ[k] P :=
{ to_fun := λ w,
    s.weighted_vsub_of_point p (classical.choice S.nonempty) w +ᵥ (classical.choice S.nonempty),
  linear := s.weighted_vsub p,
  map_vadd' := λ w₁ w₂, by simp_rw [vadd_assoc, weighted_vsub, vadd_eq_add, linear_map.map_add] }

/-- The linear map corresponding to `affine_combination` is
`weighted_vsub`. -/
@[simp] lemma affine_combination_linear (p : ι → P) :
  (s.affine_combination p : (ι → k) →ᵃ[k] P).linear = s.weighted_vsub p :=
rfl

/-- Applying `affine_combination` with given weights.  This is for the
case where a result involving a default base point is OK (for example,
when that base point will cancel out later); a more typical use case
for `affine_combination` would involve selecting a preferred base
point with
`affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one` and
then using `weighted_vsub_of_point_apply`. -/
lemma affine_combination_apply (w : ι → k) (p : ι → P) :
  s.affine_combination p w =
    s.weighted_vsub_of_point p (classical.choice S.nonempty) w +ᵥ (classical.choice S.nonempty) :=
rfl

/-- `affine_combination` gives the sum with any base point, when the
sum of the weights is 1. -/
lemma affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one (w : ι → k) (p : ι → P)
    (h : ∑ i in s, w i = 1) (b : P) :
  s.affine_combination p w = s.weighted_vsub_of_point p b w +ᵥ b :=
s.weighted_vsub_of_point_vadd_eq_of_sum_eq_one w p h _ _

/-- Adding a `weighted_vsub` to an `affine_combination`. -/
lemma weighted_vsub_vadd_affine_combination (w₁ w₂ : ι → k) (p : ι → P) :
  s.weighted_vsub p w₁ +ᵥ s.affine_combination p w₂ = s.affine_combination p (w₁ + w₂) :=
by rw [←vadd_eq_add, affine_map.map_vadd, affine_combination_linear]

/-- Subtracting two `affine_combination`s. -/
lemma affine_combination_vsub (w₁ w₂ : ι → k) (p : ι → P) :
  s.affine_combination p w₁ -ᵥ s.affine_combination p w₂ = s.weighted_vsub p (w₁ - w₂) :=
by rw [←affine_map.linear_map_vsub, affine_combination_linear, vsub_eq_sub]

/-- An `affine_combination` equals a point if that point is in the set
and has weight 1 and the other points in the set have weight 0. -/
@[simp] lemma affine_combination_of_eq_one_of_eq_zero (w : ι → k) (p : ι → P) {i : ι}
    (his : i ∈ s) (hwi : w i = 1) (hw0 : ∀ i2 ∈ s, i2 ≠ i → w i2 = 0) :
  s.affine_combination p w = p i :=
begin
  have h1 : ∑ i in s, w i = 1 := hwi ▸ sum_eq_single i hw0 (λ h, false.elim (h his)),
  rw [s.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one w p h1 (p i),
      weighted_vsub_of_point_apply],
  convert zero_vadd V (p i),
  convert sum_eq_zero _,
  intros i2 hi2,
  by_cases h : i2 = i,
  { simp [h] },
  { simp [hw0 i2 hi2 h] }
end

/-- An affine combination is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
lemma affine_combination_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : finset ι}
    (h : s₁ ⊆ s₂) :
  s₁.affine_combination p w = s₂.affine_combination p (set.indicator ↑s₁ w) :=
by rw [affine_combination_apply, affine_combination_apply,
       weighted_vsub_of_point_indicator_subset _ _ _ h]

/-- An affine combination, over the image of an embedding, equals an
affine combination with the same points and weights over the original
`finset`. -/
lemma affine_combination_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
  (s₂.map e).affine_combination p w = s₂.affine_combination (p ∘ e) (w ∘ e) :=
by simp_rw [affine_combination_apply, weighted_vsub_of_point_map]

variables {V}

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as
`weighted_vsub_of_point` using a `finset` lying within that subset and
with a given sum of weights if and only if it can be expressed as
`weighted_vsub_of_point` with that sum of weights for the
corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
lemma eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype {v : V} {x : k}
    {s : set ι} {p : ι → P} {b : P} :
  (∃ (fs : finset ι) (hfs : ↑fs ⊆ s) (w : ι → k) (hw : ∑ i in fs, w i = x),
    v = fs.weighted_vsub_of_point p b w) ↔
  ∃ (fs : finset s) (w : s → k) (hw : ∑ i in fs, w i = x),
    v = fs.weighted_vsub_of_point (λ (i : s), p i) b w :=
begin
  simp_rw weighted_vsub_of_point_apply,
  split,
  { rintros ⟨fs, hfs, w, rfl, rfl⟩,
    use [fs.subtype s, λ i, w i, sum_subtype_of_mem _ hfs, (sum_subtype_of_mem _ hfs).symm] },
  { rintros ⟨fs, w, rfl, rfl⟩,
    refine ⟨fs.map (function.embedding.subtype _), map_subtype_subset _,
         λ i, if h : i ∈ s then w ⟨i, h⟩ else 0, _, _⟩;
      simp }
end

variables (k)

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as `weighted_vsub` using
a `finset` lying within that subset and with sum of weights 0 if and
only if it can be expressed as `weighted_vsub` with sum of weights 0
for the corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
lemma eq_weighted_vsub_subset_iff_eq_weighted_vsub_subtype {v : V} {s : set ι} {p : ι → P} :
  (∃ (fs : finset ι) (hfs : ↑fs ⊆ s) (w : ι → k) (hw : ∑ i in fs, w i = 0),
    v = fs.weighted_vsub p w) ↔
  ∃ (fs : finset s) (w : s → k) (hw : ∑ i in fs, w i = 0),
    v = fs.weighted_vsub (λ (i : s), p i) w :=
eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype

variables (V)

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A point can be expressed as an
`affine_combination` using a `finset` lying within that subset and
with sum of weights 1 if and only if it can be expressed an
`affine_combination` with sum of weights 1 for the corresponding
indexed family whose index type is the subtype corresponding to that
subset. -/
lemma eq_affine_combination_subset_iff_eq_affine_combination_subtype {p0 : P} {s : set ι}
    {p : ι → P} :
  (∃ (fs : finset ι) (hfs : ↑fs ⊆ s) (w : ι → k) (hw : ∑ i in fs, w i = 1),
    p0 = fs.affine_combination p w) ↔
  ∃ (fs : finset s) (w : s → k) (hw : ∑ i in fs, w i = 1),
    p0 = fs.affine_combination (λ (i : s), p i) w :=
begin
  simp_rw [affine_combination_apply, eq_vadd_iff_vsub_eq],
  exact eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype
end

end finset

namespace finset

variables (k : Type*) {V : Type*} {P : Type*} [division_ring k] [add_comm_group V] [module k V]
variables [affine_space V P] {ι : Type*} (s : finset ι) {ι₂ : Type*} (s₂ : finset ι₂)

/-- The weights for the centroid of some points. -/
def centroid_weights : ι → k := function.const ι (card s : k) ⁻¹

/-- `centroid_weights` at any point. -/
@[simp] lemma centroid_weights_apply (i : ι) : s.centroid_weights k i = (card s : k) ⁻¹ :=
rfl

/-- `centroid_weights` equals a constant function. -/
lemma centroid_weights_eq_const :
  s.centroid_weights k = function.const ι ((card s : k) ⁻¹) :=
rfl

variables {k}

/-- The weights in the centroid sum to 1, if the number of points,
converted to `k`, is not zero. -/
lemma sum_centroid_weights_eq_one_of_cast_card_ne_zero (h : (card s : k) ≠ 0) :
  ∑ i in s, s.centroid_weights k i = 1 :=
by simp [h]

variables (k)

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is not zero. -/
lemma sum_centroid_weights_eq_one_of_card_ne_zero [char_zero k] (h : card s ≠ 0) :
  ∑ i in s, s.centroid_weights k i = 1 :=
by simp [h]

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the set is nonempty. -/
lemma sum_centroid_weights_eq_one_of_nonempty [char_zero k] (h : s.nonempty) :
  ∑ i in s, s.centroid_weights k i = 1 :=
s.sum_centroid_weights_eq_one_of_card_ne_zero k (ne_of_gt (card_pos.2 h))

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is `n + 1`. -/
lemma sum_centroid_weights_eq_one_of_card_eq_add_one [char_zero k] {n : ℕ}
  (h : card s = n + 1) : ∑ i in s, s.centroid_weights k i = 1 :=
s.sum_centroid_weights_eq_one_of_card_ne_zero k (h.symm ▸ nat.succ_ne_zero n)

include V

/-- The centroid of some points.  Although defined for any `s`, this
is intended to be used in the case where the number of points,
converted to `k`, is not zero. -/
def centroid (p : ι → P) : P :=
s.affine_combination p (s.centroid_weights k)

/-- The definition of the centroid. -/
lemma centroid_def (p : ι → P) :
  s.centroid k p = s.affine_combination p (s.centroid_weights k) :=
rfl

/-- The centroid of a single point. -/
@[simp] lemma centroid_singleton (p : ι → P) (i : ι) :
  ({i} : finset ι).centroid k p = p i :=
by simp [centroid_def, affine_combination_apply]

/-- The centroid of two points, expressed directly as adding a vector
to a point. -/
lemma centroid_insert_singleton [invertible (2 : k)] (p : ι → P) (i₁ i₂ : ι) :
  ({i₁, i₂} : finset ι).centroid k p = (2 ⁻¹ : k) • (p i₂ -ᵥ p i₁) +ᵥ p i₁ :=
begin
  by_cases h : i₁ = i₂,
  { simp [h] },
  { have hc : (card ({i₁, i₂} : finset ι) : k) ≠ 0,
    { rw [card_insert_of_not_mem (not_mem_singleton.2 h), card_singleton],
      norm_num,
      exact nonzero_of_invertible _ },
    rw [centroid_def,
        affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one _ _ _
          (sum_centroid_weights_eq_one_of_cast_card_ne_zero _ hc) (p i₁)],
    simp [h],
    norm_num }
end

/-- The centroid of two points indexed by `fin 2`, expressed directly
as adding a vector to the first point. -/
lemma centroid_insert_singleton_fin [invertible (2 : k)] (p : fin 2 → P) :
  univ.centroid k p = (2 ⁻¹ : k) • (p 1 -ᵥ p 0) +ᵥ p 0 :=
begin
  have hu : (finset.univ : finset (fin 2)) = {0, 1}, by dec_trivial,
  rw hu,
  convert centroid_insert_singleton k p 0 1
end

/-- A centroid, over the image of an embedding, equals a centroid with
the same points and weights over the original `finset`. -/
lemma centroid_map (e : ι₂ ↪ ι) (p : ι → P) : (s₂.map e).centroid k p = s₂.centroid k (p ∘ e) :=
by simp [centroid_def, affine_combination_map, centroid_weights]

omit V

/-- `centroid_weights` gives the weights for the centroid as a
constant function, which is suitable when summing over the points
whose centroid is being taken.  This function gives the weights in a
form suitable for summing over a larger set of points, as an indicator
function that is zero outside the set whose centroid is being taken.
In the case of a `fintype`, the sum may be over `univ`. -/
def centroid_weights_indicator : ι → k := set.indicator ↑s (s.centroid_weights k)

/-- The definition of `centroid_weights_indicator`. -/
lemma centroid_weights_indicator_def :
  s.centroid_weights_indicator k = set.indicator ↑s (s.centroid_weights k) :=
rfl

/-- The sum of the weights for the centroid indexed by a `fintype`. -/
lemma sum_centroid_weights_indicator [fintype ι] :
  ∑ i, s.centroid_weights_indicator k i = ∑ i in s, s.centroid_weights k i :=
(set.sum_indicator_subset _ (subset_univ _)).symm

/-- In the characteristic zero case, the weights in the centroid
indexed by a `fintype` sum to 1 if the number of points is not
zero. -/
lemma sum_centroid_weights_indicator_eq_one_of_card_ne_zero [char_zero k] [fintype ι]
  (h : card s ≠ 0) : ∑ i, s.centroid_weights_indicator k i = 1 :=
begin
  rw sum_centroid_weights_indicator,
  exact s.sum_centroid_weights_eq_one_of_card_ne_zero k h
end

/-- In the characteristic zero case, the weights in the centroid
indexed by a `fintype` sum to 1 if the set is nonempty. -/
lemma sum_centroid_weights_indicator_eq_one_of_nonempty [char_zero k] [fintype ι]
  (h : s.nonempty) : ∑ i, s.centroid_weights_indicator k i = 1 :=
begin
  rw sum_centroid_weights_indicator,
  exact s.sum_centroid_weights_eq_one_of_nonempty k h
end

/-- In the characteristic zero case, the weights in the centroid
indexed by a `fintype` sum to 1 if the number of points is `n + 1`. -/
lemma sum_centroid_weights_indicator_eq_one_of_card_eq_add_one [char_zero k] [fintype ι] {n : ℕ}
  (h : card s = n + 1) : ∑ i, s.centroid_weights_indicator k i = 1 :=
begin
  rw sum_centroid_weights_indicator,
  exact s.sum_centroid_weights_eq_one_of_card_eq_add_one k h
end

include V

/-- The centroid as an affine combination over a `fintype`. -/
lemma centroid_eq_affine_combination_fintype [fintype ι] (p : ι → P) :
  s.centroid k p = univ.affine_combination p (s.centroid_weights_indicator k) :=
affine_combination_indicator_subset _ _ (subset_univ _)

/-- An indexed family of points that is injective on the given
`finset` has the same centroid as the image of that `finset`.  This is
stated in terms of a set equal to the image to provide control of
definitional equality for the index type used for the centroid of the
image. -/
lemma centroid_eq_centroid_image_of_inj_on {p : ι → P} (hi : ∀ i j ∈ s, p i = p j → i = j)
  {ps : set P} [fintype ps] (hps : ps = p '' ↑s) :
  s.centroid k p = (univ : finset ps).centroid k (λ x, x) :=
begin
  let f : p '' ↑s → ι := λ x, x.property.some,
  have hf : ∀ x, f x ∈ s ∧ p (f x) = x := λ x, x.property.some_spec,
  let f' : ps → ι := λ x, f ⟨x, hps ▸ x.property⟩,
  have hf' : ∀ x, f' x ∈ s ∧ p (f' x) = x := λ x, hf ⟨x, hps ▸ x.property⟩,
  have hf'i : function.injective f',
  { intros x y h,
    rw [subtype.ext_iff, ←(hf' x).2, ←(hf' y).2, h] },
  let f'e : ps ↪ ι := ⟨f', hf'i⟩,
  have hu : finset.univ.map f'e = s,
  { ext x,
    rw mem_map,
    split,
    { rintros ⟨i, _, rfl⟩,
      exact (hf' i).1 },
    { intro hx,
      use [⟨p x, hps.symm ▸ set.mem_image_of_mem _ hx⟩, mem_univ _],
      refine hi _ _ (hf' _).1 hx _,
      rw (hf' _).2,
      refl } },
  rw [←hu, centroid_map],
  congr' with x,
  change p (f' x) = ↑x,
  rw (hf' x).2
end

/-- Two indexed families of points that are injective on the given
`finset`s and with the same points in the image of those `finset`s
have the same centroid. -/
lemma centroid_eq_of_inj_on_of_image_eq {p : ι → P} (hi : ∀ i j ∈ s, p i = p j → i = j)
  {p₂ : ι₂ → P} (hi₂ : ∀ i j ∈ s₂, p₂ i = p₂ j → i = j) (he : p '' ↑s = p₂ '' ↑s₂) :
  s.centroid k p = s₂.centroid k p₂ :=
by rw [s.centroid_eq_centroid_image_of_inj_on k hi rfl,
       s₂.centroid_eq_centroid_image_of_inj_on k hi₂ he]

end finset

section affine_space'

variables {k : Type*} {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
variables {ι : Type*}
include V

/-- A `weighted_vsub` with sum of weights 0 is in the `vector_span` of
an indexed family. -/
lemma weighted_vsub_mem_vector_span {s : finset ι} {w : ι → k}
    (h : ∑ i in s, w i = 0) (p : ι → P) :
    s.weighted_vsub p w ∈ vector_span k (set.range p) :=
begin
  by_cases hn : nonempty ι,
  { cases hn with i0,
    rw [vector_span_range_eq_span_range_vsub_right k p i0, ←set.image_univ,
        finsupp.mem_span_iff_total,
        finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero s w p h (p i0),
        finset.weighted_vsub_of_point_apply],
    let w' := set.indicator ↑s w,
    have hwx : ∀ i, w' i ≠ 0 → i ∈ s := λ i, set.mem_of_indicator_ne_zero,
    use [finsupp.on_finset s w' hwx, set.subset_univ _],
    rw [finsupp.total_apply, finsupp.on_finset_sum hwx],
    { apply finset.sum_congr rfl,
      intros i hi,
      simp [w', set.indicator_apply, if_pos hi] },
    { exact λ _, zero_smul k _ } },
  { simp [finset.eq_empty_of_not_nonempty hn s] }
end

/-- An `affine_combination` with sum of weights 1 is in the
`affine_span` of an indexed family, if the underlying ring is
nontrivial. -/
lemma affine_combination_mem_affine_span [nontrivial k] {s : finset ι} {w : ι → k}
    (h : ∑ i in s, w i = 1) (p : ι → P) :
  s.affine_combination p w ∈ affine_span k (set.range p) :=
begin
  have hnz : ∑ i in s, w i ≠ 0 := h.symm ▸ one_ne_zero,
  have hn : s.nonempty := finset.nonempty_of_sum_ne_zero hnz,
  cases hn with i1 hi1,
  let w1 : ι → k := function.update (function.const ι 0) i1 1,
  have hw1 : ∑ i in s, w1 i = 1,
  { rw [finset.sum_update_of_mem hi1, finset.sum_const_zero, add_zero] },
  have hw1s : s.affine_combination p w1 = p i1 :=
    s.affine_combination_of_eq_one_of_eq_zero w1 p hi1 (function.update_same _ _ _)
                                              (λ _ _ hne, function.update_noteq hne _ _),
  have hv : s.affine_combination p w -ᵥ p i1 ∈ (affine_span k (set.range p)).direction,
  { rw [direction_affine_span, ←hw1s, finset.affine_combination_vsub],
    apply weighted_vsub_mem_vector_span,
    simp [pi.sub_apply, h, hw1] },
  rw ←vsub_vadd (s.affine_combination p w) (p i1),
  exact affine_subspace.vadd_mem_of_mem_direction hv (mem_affine_span k (set.mem_range_self _))
end

variables (k) {V}

/-- A vector is in the `vector_span` of an indexed family if and only
if it is a `weighted_vsub` with sum of weights 0. -/
lemma mem_vector_span_iff_eq_weighted_vsub {v : V} {p : ι → P} :
  v ∈ vector_span k (set.range p) ↔
    ∃ (s : finset ι) (w : ι → k) (h : ∑ i in s, w i = 0), v = s.weighted_vsub p w :=
begin
  split,
  { by_cases hn : nonempty ι,
    { cases hn with i0,
      rw [vector_span_range_eq_span_range_vsub_right k p i0, ←set.image_univ,
          finsupp.mem_span_iff_total],
      rintros ⟨l, hl, hv⟩,
      use insert i0 l.support,
      set w := (l : ι → k) -
        function.update (function.const ι 0 : ι → k) i0 (∑ i in l.support, l i) with hwdef,
      use w,
      have hw : ∑ i in insert i0 l.support, w i = 0,
      { rw hwdef,
        simp_rw [pi.sub_apply, finset.sum_sub_distrib,
                 finset.sum_update_of_mem (finset.mem_insert_self _ _), finset.sum_const_zero,
                 finset.sum_insert_of_eq_zero_if_not_mem finsupp.not_mem_support_iff.1,
                 add_zero, sub_self] },
      use hw,
      have hz : w i0 • (p i0 -ᵥ p i0 : V) = 0 := (vsub_self (p i0)).symm ▸ smul_zero _,
      change (λ i, w i • (p i -ᵥ p i0 : V)) i0 = 0 at hz,
      rw [finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ w p hw (p i0),
          finset.weighted_vsub_of_point_apply, ←hv, finsupp.total_apply,
          finset.sum_insert_zero hz],
      change ∑ i in l.support, l i • _ = _,
      congr' with i,
      by_cases h : i = i0,
      { simp [h] },
      { simp [hwdef, h] } },
    { rw [set.range_eq_empty.2 hn, vector_span_empty, submodule.mem_bot],
      intro hv,
      use [∅],
      simp [hv] } },
  { rintros ⟨s, w, hw, rfl⟩,
    exact weighted_vsub_mem_vector_span hw p }
end

variables {k}

/-- A point in the `affine_span` of an indexed family is an
`affine_combination` with sum of weights 1. -/
lemma eq_affine_combination_of_mem_affine_span {p1 : P} {p : ι → P}
    (h : p1 ∈ affine_span k (set.range p)) :
  ∃ (s : finset ι) (w : ι → k) (hw : ∑ i in s, w i = 1), p1 = s.affine_combination p w :=
begin
  have hn : ((affine_span k (set.range p)) : set P).nonempty := ⟨p1, h⟩,
  rw [affine_span_nonempty, set.range_nonempty_iff_nonempty] at hn,
  cases hn with i0,
  have h0 : p i0 ∈ affine_span k (set.range p) := mem_affine_span k (set.mem_range_self i0),
  have hd : p1 -ᵥ p i0 ∈ (affine_span k (set.range p)).direction :=
    affine_subspace.vsub_mem_direction h h0,
  rw [direction_affine_span, mem_vector_span_iff_eq_weighted_vsub] at hd,
  rcases hd with ⟨s, w, h, hs⟩,
  let s' := insert i0 s,
  let w' := set.indicator ↑s w,
  have h' : ∑ i in s', w' i = 0,
  { rw [←h, set.sum_indicator_subset _ (finset.subset_insert i0 s)] },
  have hs' : s'.weighted_vsub p w' = p1 -ᵥ p i0,
  { rw hs,
    exact (finset.weighted_vsub_indicator_subset _ _ (finset.subset_insert i0 s)).symm },
  let w0 : ι → k := function.update (function.const ι 0) i0 1,
  have hw0 : ∑ i in s', w0 i = 1,
  { rw [finset.sum_update_of_mem (finset.mem_insert_self _ _), finset.sum_const_zero, add_zero] },
  have hw0s : s'.affine_combination p w0 = p i0 :=
    s'.affine_combination_of_eq_one_of_eq_zero w0 p
                                               (finset.mem_insert_self _ _)
                                               (function.update_same _ _ _)
                                               (λ _ _ hne, function.update_noteq hne _ _),
  use [s', w0 + w'],
  split,
  { simp [pi.add_apply, finset.sum_add_distrib, hw0, h'] },
  { rw [add_comm, ←finset.weighted_vsub_vadd_affine_combination, hw0s, hs', vsub_vadd] }
end

variables (k V)

/-- A point is in the `affine_span` of an indexed family if and only
if it is an `affine_combination` with sum of weights 1, provided the
underlying ring is nontrivial. -/
lemma mem_affine_span_iff_eq_affine_combination [nontrivial k] {p1 : P} {p : ι → P} :
  p1 ∈ affine_span k (set.range p) ↔
    ∃ (s : finset ι) (w : ι → k) (hw : ∑ i in s, w i = 1), p1 = s.affine_combination p w :=
begin
  split,
  { exact eq_affine_combination_of_mem_affine_span },
  { rintros ⟨s, w, hw, rfl⟩,
    exact affine_combination_mem_affine_span hw p }
end

end affine_space'

section division_ring

variables {k : Type*} {V : Type*} {P : Type*} [division_ring k] [add_comm_group V] [module k V]
variables [affine_space V P] {ι : Type*}
include V

open set finset

/-- The centroid lies in the affine span if the number of points,
converted to `k`, is not zero. -/
lemma centroid_mem_affine_span_of_cast_card_ne_zero {s : finset ι} (p : ι → P)
  (h : (card s : k) ≠ 0) : s.centroid k p ∈ affine_span k (range p) :=
affine_combination_mem_affine_span (s.sum_centroid_weights_eq_one_of_cast_card_ne_zero h) p

variables (k)

/-- In the characteristic zero case, the centroid lies in the affine
span if the number of points is not zero. -/
lemma centroid_mem_affine_span_of_card_ne_zero [char_zero k] {s : finset ι} (p : ι → P)
  (h : card s ≠ 0) : s.centroid k p ∈ affine_span k (range p) :=
affine_combination_mem_affine_span (s.sum_centroid_weights_eq_one_of_card_ne_zero k h) p

/-- In the characteristic zero case, the centroid lies in the affine
span if the set is nonempty. -/
lemma centroid_mem_affine_span_of_nonempty [char_zero k] {s : finset ι} (p : ι → P)
  (h : s.nonempty) : s.centroid k p ∈ affine_span k (range p) :=
affine_combination_mem_affine_span (s.sum_centroid_weights_eq_one_of_nonempty k h) p

/-- In the characteristic zero case, the centroid lies in the affine
span if the number of points is `n + 1`. -/
lemma centroid_mem_affine_span_of_card_eq_add_one [char_zero k] {s : finset ι} (p : ι → P)
  {n : ℕ} (h : card s = n + 1) : s.centroid k p ∈ affine_span k (range p) :=
affine_combination_mem_affine_span (s.sum_centroid_weights_eq_one_of_card_eq_add_one k h) p

end division_ring

namespace affine_map
variables {k : Type*} {V : Type*} (P : Type*) [comm_ring k] [add_comm_group V] [module k V]
variables [affine_space V P] {ι : Type*} (s : finset ι)
include V

-- TODO: define `affine_map.proj`, `affine_map.fst`, `affine_map.snd`
/-- A weighted sum, as an affine map on the points involved. -/
def weighted_vsub_of_point (w : ι → k) : ((ι → P) × P) →ᵃ[k] V :=
{ to_fun := λ p, s.weighted_vsub_of_point p.fst p.snd w,
  linear := ∑ i in s,
    w i • ((linear_map.proj i).comp (linear_map.fst _ _ _) - linear_map.snd _ _ _),
  map_vadd' := begin
    rintros ⟨p, b⟩ ⟨v, b'⟩,
    simp [linear_map.sum_apply, finset.weighted_vsub_of_point, vsub_vadd_eq_vsub_sub,
          vadd_vsub_assoc, add_sub, ← sub_add_eq_add_sub, smul_add, finset.sum_add_distrib]
  end }

end affine_map
