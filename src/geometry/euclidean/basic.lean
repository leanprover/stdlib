/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import analysis.normed_space.inner_product
import linear_algebra.affine_space.finite_dimensional

noncomputable theory
open_locale big_operators
open_locale classical
open_locale real
open_locale real_inner_product_space

/-!
# Euclidean spaces

This file makes some definitions and proves very basic geometrical
results about real inner product spaces and Euclidean affine spaces.
Results about real inner product spaces that involve the norm and
inner product but not angles generally go in
`analysis.normed_space.inner_product`.  Results with longer
proofs or more geometrical content generally go in separate files.

## Main definitions

* `inner_product_geometry.angle` is the undirected angle between two
  vectors.

* `euclidean_geometry.angle`, with notation `∠`, is the undirected
  angle determined by three points.

* `euclidean_geometry.orthogonal_projection` is the orthogonal
  projection of a point onto an affine subspace.

* `euclidean_geometry.reflection` is the reflection of a point in an
  affine subspace.

## Implementation notes

To declare `P` as the type of points in a Euclidean affine space with
`V` as the type of vectors, use `[inner_product_space ℝ V] [metric_space P]
[normed_add_torsor V P]`.  This works better with `out_param` to make
`V` implicit in most cases than having a separate type alias for
Euclidean affine spaces.

Rather than requiring Euclidean affine spaces to be finite-dimensional
(as in the definition on Wikipedia), this is specified only for those
theorems that need it.

## References

* https://en.wikipedia.org/wiki/Euclidean_space

-/

namespace inner_product_geometry
/-!
### Geometrical results on real inner product spaces

This section develops some geometrical definitions and results on real
inner product spaces, where those definitions and results can most
conveniently be developed in terms of vectors and then used to deduce
corresponding results for Euclidean affine spaces.
-/

variables {V : Type*} [inner_product_space ℝ V]

/-- The undirected angle between two vectors. If either vector is 0,
this is π/2. -/
def angle (x y : V) : ℝ := real.arccos (inner x y / (∥x∥ * ∥y∥))

/-- The cosine of the angle between two vectors. -/
lemma cos_angle (x y : V) : real.cos (angle x y) = inner x y / (∥x∥ * ∥y∥) :=
real.cos_arccos (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
                (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2

/-- The angle between two vectors does not depend on their order. -/
lemma angle_comm (x y : V) : angle x y = angle y x :=
begin
  unfold angle,
  rw [real_inner_comm, mul_comm]
end

/-- The angle between the negation of two vectors. -/
@[simp] lemma angle_neg_neg (x y : V) : angle (-x) (-y) = angle x y :=
begin
  unfold angle,
  rw [inner_neg_neg, norm_neg, norm_neg]
end

/-- The angle between two vectors is nonnegative. -/
lemma angle_nonneg (x y : V) : 0 ≤ angle x y :=
real.arccos_nonneg _

/-- The angle between two vectors is at most π. -/
lemma angle_le_pi (x y : V) : angle x y ≤ π :=
real.arccos_le_pi _

/-- The angle between a vector and the negation of another vector. -/
lemma angle_neg_right (x y : V) : angle x (-y) = π - angle x y :=
begin
  unfold angle,
  rw [←real.arccos_neg, norm_neg, inner_neg_right, neg_div]
end

/-- The angle between the negation of a vector and another vector. -/
lemma angle_neg_left (x y : V) : angle (-x) y = π - angle x y :=
by rw [←angle_neg_neg, neg_neg, angle_neg_right]

/-- The angle between the zero vector and a vector. -/
@[simp] lemma angle_zero_left (x : V) : angle 0 x = π / 2 :=
begin
  unfold angle,
  rw [inner_zero_left, zero_div, real.arccos_zero]
end

/-- The angle between a vector and the zero vector. -/
@[simp] lemma angle_zero_right (x : V) : angle x 0 = π / 2 :=
begin
  unfold angle,
  rw [inner_zero_right, zero_div, real.arccos_zero]
end

/-- The angle between a nonzero vector and itself. -/
@[simp] lemma angle_self {x : V} (hx : x ≠ 0) : angle x x = 0 :=
begin
  unfold angle,
  rw [←real_inner_self_eq_norm_square, div_self (λ h, hx (inner_self_eq_zero.1 h)),
      real.arccos_one]
end

/-- The angle between a nonzero vector and its negation. -/
@[simp] lemma angle_self_neg_of_nonzero {x : V} (hx : x ≠ 0) : angle x (-x) = π :=
by rw [angle_neg_right, angle_self hx, sub_zero]

/-- The angle between the negation of a nonzero vector and that
vector. -/
@[simp] lemma angle_neg_self_of_nonzero {x : V} (hx : x ≠ 0) : angle (-x) x = π :=
by rw [angle_comm, angle_self_neg_of_nonzero hx]

/-- The angle between a vector and a positive multiple of a vector. -/
@[simp] lemma angle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
  angle x (r • y) = angle x y :=
begin
  unfold angle,
  rw [inner_smul_right, norm_smul, real.norm_eq_abs, abs_of_nonneg (le_of_lt hr), ←mul_assoc,
      mul_comm _ r, mul_assoc, mul_div_mul_left _ _ (ne_of_gt hr)]
end

/-- The angle between a positive multiple of a vector and a vector. -/
@[simp] lemma angle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
  angle (r • x) y = angle x y :=
by rw [angle_comm, angle_smul_right_of_pos y x hr, angle_comm]

/-- The angle between a vector and a negative multiple of a vector. -/
@[simp] lemma angle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
  angle x (r • y) = angle x (-y) :=
by rw [←neg_neg r, neg_smul, angle_neg_right, angle_smul_right_of_pos x y (neg_pos_of_neg hr),
       angle_neg_right]

/-- The angle between a negative multiple of a vector and a vector. -/
@[simp] lemma angle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
  angle (r • x) y = angle (-x) y :=
by rw [angle_comm, angle_smul_right_of_neg y x hr, angle_comm]

/-- The cosine of the angle between two vectors, multiplied by the
product of their norms. -/
lemma cos_angle_mul_norm_mul_norm (x y : V) : real.cos (angle x y) * (∥x∥ * ∥y∥) = inner x y :=
begin
  rw [cos_angle, div_mul_cancel_of_imp],
  simp [or_imp_distrib] { contextual := tt },
end

/-- The sine of the angle between two vectors, multiplied by the
product of their norms. -/
lemma sin_angle_mul_norm_mul_norm (x y : V) : real.sin (angle x y) * (∥x∥ * ∥y∥) =
    real.sqrt (inner x x * inner y y - inner x y * inner x y) :=
begin
  unfold angle,
  rw [real.sin_arccos (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
                      (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2,
      ←real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)),
      ←real.sqrt_mul' _ (mul_self_nonneg _), pow_two,
      real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)), real_inner_self_eq_norm_square,
      real_inner_self_eq_norm_square],
  by_cases h : (∥x∥ * ∥y∥) = 0,
  { rw [(show ∥x∥ * ∥x∥ * (∥y∥ * ∥y∥) = (∥x∥ * ∥y∥) * (∥x∥ * ∥y∥), by ring), h, mul_zero, mul_zero,
        zero_sub],
    cases eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy,
    { rw norm_eq_zero at hx,
      rw [hx, inner_zero_left, zero_mul, neg_zero] },
    { rw norm_eq_zero at hy,
      rw [hy, inner_zero_right, zero_mul, neg_zero] } },
  { field_simp [h],
    ring }
end

/-- The angle between two vectors is zero if and only if they are
nonzero and one is a positive multiple of the other. -/
lemma angle_eq_zero_iff {x y : V} : angle x y = 0 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), 0 < r ∧ y = r • x) :=
begin
  rw [angle, ← real_inner_div_norm_mul_norm_eq_one_iff, real.arccos_eq_zero, has_le.le.le_iff_eq,
    eq_comm],
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2
end

/-- The angle between two vectors is π if and only if they are nonzero
and one is a negative multiple of the other. -/
lemma angle_eq_pi_iff {x y : V} : angle x y = π ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r < 0 ∧ y = r • x) :=
begin
  rw [angle, ← real_inner_div_norm_mul_norm_eq_neg_one_iff, real.arccos_eq_pi, has_le.le.le_iff_eq],
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
end

/-- If the angle between two vectors is π, the angles between those
vectors and a third vector add to π. -/
lemma angle_add_angle_eq_pi_of_angle_eq_pi {x y : V} (z : V) (h : angle x y = π) :
  angle x z + angle y z = π :=
begin
  rcases angle_eq_pi_iff.1 h with ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩,
  rw [angle_smul_left_of_neg x z hr, angle_neg_left, add_sub_cancel'_right]
end

/-- Two vectors have inner product 0 if and only if the angle between
them is π/2. -/
lemma inner_eq_zero_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2 :=
iff.symm $ by simp [angle, or_imp_distrib] { contextual := tt }

end inner_product_geometry

namespace euclidean_geometry
/-!
### Geometrical results on Euclidean affine spaces

This section develops some geometrical definitions and results on
Euclidean affine spaces.
-/
open inner_product_geometry

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P]
local notation `⟪`x`, `y`⟫` := @inner ℝ V _ x y
include V

/-- The undirected angle at `p2` between the line segments to `p1` and
`p3`. If either of those points equals `p2`, this is π/2. Use
`open_locale euclidean_geometry` to access the `∠ p1 p2 p3`
notation. -/
def angle (p1 p2 p3 : P) : ℝ := angle (p1 -ᵥ p2 : V) (p3 -ᵥ p2)

localized "notation `∠` := euclidean_geometry.angle" in euclidean_geometry

/-- The angle at a point does not depend on the order of the other two
points. -/
lemma angle_comm (p1 p2 p3 : P) : ∠ p1 p2 p3 = ∠ p3 p2 p1 :=
angle_comm _ _

/-- The angle at a point is nonnegative. -/
lemma angle_nonneg (p1 p2 p3 : P) : 0 ≤ ∠ p1 p2 p3 :=
angle_nonneg _ _

/-- The angle at a point is at most π. -/
lemma angle_le_pi (p1 p2 p3 : P) : ∠ p1 p2 p3 ≤ π :=
angle_le_pi _ _

/-- The angle ∠AAB at a point. -/
lemma angle_eq_left (p1 p2 : P) : ∠ p1 p1 p2 = π / 2 :=
begin
  unfold angle,
  rw vsub_self,
  exact angle_zero_left _
end

/-- The angle ∠ABB at a point. -/
lemma angle_eq_right (p1 p2 : P) : ∠ p1 p2 p2 = π / 2 :=
by rw [angle_comm, angle_eq_left]

/-- The angle ∠ABA at a point. -/
lemma angle_eq_of_ne {p1 p2 : P} (h : p1 ≠ p2) : ∠ p1 p2 p1 = 0 :=
angle_self (λ he, h (vsub_eq_zero_iff_eq.1 he))

/-- If the angle ∠ABC at a point is π, the angle ∠BAC is 0. -/
lemma angle_eq_zero_of_angle_eq_pi_left {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
  ∠ p2 p1 p3 = 0 :=
begin
  unfold angle at h,
  rw angle_eq_pi_iff at h,
  rcases h with ⟨hp1p2, ⟨r, ⟨hr, hpr⟩⟩⟩,
  unfold angle,
  rw angle_eq_zero_iff,
  rw [←neg_vsub_eq_vsub_rev, neg_ne_zero] at hp1p2,
  use [hp1p2, -r + 1, add_pos (neg_pos_of_neg hr) zero_lt_one],
  rw [add_smul, ←neg_vsub_eq_vsub_rev p1 p2, smul_neg],
  simp [←hpr]
end

/-- If the angle ∠ABC at a point is π, the angle ∠BCA is 0. -/
lemma angle_eq_zero_of_angle_eq_pi_right {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
  ∠ p2 p3 p1 = 0 :=
begin
  rw angle_comm at h,
  exact angle_eq_zero_of_angle_eq_pi_left h
end

/-- If ∠BCD = π, then ∠ABC = ∠ABD. -/
lemma angle_eq_angle_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
  ∠ p1 p2 p3 = ∠ p1 p2 p4 :=
begin
  unfold angle at *,
  rcases angle_eq_pi_iff.1 h with ⟨hp2p3, ⟨r, ⟨hr, hpr⟩⟩⟩,
  rw [eq_comm],
  convert angle_smul_right_of_pos (p1 -ᵥ p2) (p3 -ᵥ p2) (add_pos (neg_pos_of_neg hr) zero_lt_one),
  rw [add_smul, ← neg_vsub_eq_vsub_rev p2 p3, smul_neg, neg_smul, ← hpr],
  simp
end

/-- If ∠BCD = π, then ∠ACB + ∠ACD = π. -/
lemma angle_add_angle_eq_pi_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
  ∠ p1 p3 p2 + ∠ p1 p3 p4 = π :=
begin
  unfold angle at h,
  rw [angle_comm p1 p3 p2, angle_comm p1 p3 p4],
  unfold angle,
  exact angle_add_angle_eq_pi_of_angle_eq_pi _ h
end

/-- The inner product of two vectors given with `weighted_vsub`, in
terms of the pairwise distances. -/
lemma inner_weighted_vsub {ι₁ : Type*} {s₁ : finset ι₁} {w₁ : ι₁ → ℝ} (p₁ : ι₁ → P)
    (h₁ : ∑ i in s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : finset ι₂} {w₂ : ι₂ → ℝ} (p₂ : ι₂ → P)
    (h₂ : ∑ i in s₂, w₂ i = 0) :
  inner (s₁.weighted_vsub p₁ w₁) (s₂.weighted_vsub p₂ w₂) =
    (-∑ i₁ in s₁, ∑ i₂ in s₂,
      w₁ i₁ * w₂ i₂ * (dist (p₁ i₁) (p₂ i₂) * dist (p₁ i₁) (p₂ i₂))) / 2 :=
begin
  rw [finset.weighted_vsub_apply, finset.weighted_vsub_apply,
      inner_sum_smul_sum_smul_of_sum_eq_zero _ h₁ _ h₂],
  simp_rw [vsub_sub_vsub_cancel_right],
  rcongr i₁ i₂; rw dist_eq_norm_vsub V (p₁ i₁) (p₂ i₂)
end

/-- The distance between two points given with `affine_combination`,
in terms of the pairwise distances between the points in that
combination. -/
lemma dist_affine_combination {ι : Type*} {s : finset ι} {w₁ w₂ : ι → ℝ} (p : ι → P)
    (h₁ : ∑ i in s, w₁ i = 1) (h₂ : ∑ i in s, w₂ i = 1) :
  dist (s.affine_combination p w₁) (s.affine_combination p w₂) *
    dist (s.affine_combination p w₁) (s.affine_combination p w₂) =
    (-∑ i₁ in s, ∑ i₂ in s,
      (w₁ - w₂) i₁ * (w₁ - w₂) i₂ * (dist (p i₁) (p i₂) * dist (p i₁) (p i₂))) / 2 :=
begin
  rw [dist_eq_norm_vsub V (s.affine_combination p w₁) (s.affine_combination p w₂),
      ←inner_self_eq_norm_square, finset.affine_combination_vsub],
  have h : ∑ i in s, (w₁ - w₂) i = 0,
  { simp_rw [pi.sub_apply, finset.sum_sub_distrib, h₁, h₂, sub_self] },
  exact inner_weighted_vsub p h p h
end

/-- Suppose that `c₁` is equidistant from `p₁` and `p₂`, and the same
applies to `c₂`.  Then the vector between `c₁` and `c₂` is orthogonal
to that between `p₁` and `p₂`.  (In two dimensions, this says that the
diagonals of a kite are orthogonal.) -/
lemma inner_vsub_vsub_of_dist_eq_of_dist_eq {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁)
  (hc₂ : dist p₁ c₂ = dist p₂ c₂) : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 :=
begin
  have h : ⟪(c₂ -ᵥ c₁) + (c₂ -ᵥ c₁), p₂ -ᵥ p₁⟫ = 0,
  { conv_lhs { congr, congr, rw ←vsub_sub_vsub_cancel_right c₂ c₁ p₁,
               skip, rw ←vsub_sub_vsub_cancel_right c₂ c₁ p₂ },
    rw [←add_sub_comm, inner_sub_left],
    conv_lhs { congr, rw ←vsub_sub_vsub_cancel_right p₂ p₁ c₂,
               skip, rw ←vsub_sub_vsub_cancel_right p₂ p₁ c₁ },
    rw [dist_comm p₁, dist_comm p₂, dist_eq_norm_vsub V _ p₁,
        dist_eq_norm_vsub V _ p₂, ←real_inner_add_sub_eq_zero_iff] at hc₁ hc₂,
    simp_rw [←neg_vsub_eq_vsub_rev c₁, ←neg_vsub_eq_vsub_rev c₂, sub_neg_eq_add,
             neg_add_eq_sub, hc₁, hc₂, sub_zero] },
  simpa [inner_add_left, ←mul_two, (by norm_num : (2 : ℝ) ≠ 0)] using h
end

/-- The squared distance between points on a line (expressed as a
multiple of a fixed vector added to a point) and another point,
expressed as a quadratic. -/
lemma dist_smul_vadd_square (r : ℝ) (v : V) (p₁ p₂ : P) :
  dist (r • v +ᵥ p₁) p₂ * dist (r • v +ᵥ p₁) p₂ =
    ⟪v, v⟫ * r * r + 2 * ⟪v, p₁ -ᵥ p₂⟫ * r + ⟪p₁ -ᵥ p₂, p₁ -ᵥ p₂⟫ :=
begin
  rw [dist_eq_norm_vsub V _ p₂, ←real_inner_self_eq_norm_square, vadd_vsub_assoc, real_inner_add_add_self,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_right],
  ring
end

/-- The condition for two points on a line to be equidistant from
another point. -/
lemma dist_smul_vadd_eq_dist {v : V} (p₁ p₂ : P) (hv : v ≠ 0) (r : ℝ) :
  dist (r • v +ᵥ p₁) p₂ = dist p₁ p₂ ↔ (r = 0 ∨ r = -2 * ⟪v, p₁ -ᵥ p₂⟫ / ⟪v, v⟫) :=
begin
  conv_lhs { rw [←mul_self_inj_of_nonneg dist_nonneg dist_nonneg, dist_smul_vadd_square,
                 ←sub_eq_zero_iff_eq, add_sub_assoc, dist_eq_norm_vsub V p₁ p₂,
                 ←real_inner_self_eq_norm_square, sub_self] },
  have hvi : ⟪v, v⟫ ≠ 0, by simpa using hv,
  have hd : discrim ⟪v, v⟫ (2 * ⟪v, p₁ -ᵥ p₂⟫) 0 =
    (2 * inner v (p₁ -ᵥ p₂)) * (2 * inner v (p₁ -ᵥ p₂)),
  { rw discrim, ring },
  rw [quadratic_eq_zero_iff hvi hd, add_left_neg, zero_div, neg_mul_eq_neg_mul,
      ←mul_sub_right_distrib, sub_eq_add_neg, ←mul_two, mul_assoc, mul_div_assoc,
      mul_div_mul_left, mul_div_assoc],
  norm_num
end

open affine_subspace finite_dimensional

/-- Distances `r₁` `r₂` of `p` from two different points `c₁` `c₂` determine at
most two points `p₁` `p₂` in a two-dimensional subspace containing those points
(two circles intersect in at most two points). -/
lemma eq_of_dist_eq_of_dist_eq_of_mem_of_findim_eq_two {s : affine_subspace ℝ P}
  [finite_dimensional ℝ s.direction] (hd : findim ℝ s.direction = 2) {c₁ c₂ p₁ p₂ p : P}
  (hc₁s : c₁ ∈ s) (hc₂s : c₂ ∈ s) (hp₁s : p₁ ∈ s) (hp₂s : p₂ ∈ s) (hps : p ∈ s) {r₁ r₂ : ℝ}
  (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁) (hp₂c₁ : dist p₂ c₁ = r₁)
  (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂) (hp₂c₂ : dist p₂ c₂ = r₂)
  (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ :=
begin
  have ho : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (by cc) (by cc),
  have hop : ⟪c₂ -ᵥ c₁, p -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (by cc) (by cc),
  let b : fin 2 → V := ![c₂ -ᵥ c₁, p₂ -ᵥ p₁],
  have hb : linear_independent ℝ b,
  { refine linear_independent_of_ne_zero_of_inner_eq_zero _ _,
    { intro i,
      fin_cases i; simp [b, hc.symm, hp.symm] },
    { intros i j hij,
      fin_cases i; fin_cases j; try { exact false.elim (hij rfl) },
      { exact ho },
      { rw real_inner_comm, exact ho } } },
  have hbs : submodule.span ℝ (set.range b) = s.direction,
  { refine eq_of_le_of_findim_eq _ _,
    { rw [submodule.span_le, set.range_subset_iff],
      intro i,
      fin_cases i,
      { exact vsub_mem_direction hc₂s hc₁s },
      { exact vsub_mem_direction hp₂s hp₁s } },
    { rw [findim_span_eq_card hb, fintype.card_fin, hd] } },
  have hv : ∀ v ∈ s.direction, ∃ t₁ t₂ : ℝ, v = t₁ • (c₂ -ᵥ c₁) + t₂ • (p₂ -ᵥ p₁),
  { intros v hv,
    have hr : set.range b = {c₂ -ᵥ c₁, p₂ -ᵥ p₁},
    { have hu : (finset.univ : finset (fin 2)) = {0, 1}, by dec_trivial,
      rw [←fintype.coe_image_univ, hu],
      simp,
      refl },
    rw [←hbs, hr, submodule.mem_span_insert] at hv,
    rcases hv with ⟨t₁, v', hv', hv⟩,
    rw submodule.mem_span_singleton at hv',
    rcases hv' with ⟨t₂, rfl⟩,
    exact ⟨t₁, t₂, hv⟩ },
  rcases hv (p -ᵥ p₁) (vsub_mem_direction hps hp₁s) with ⟨t₁, t₂, hpt⟩,
  simp only [hpt, inner_add_right, inner_smul_right, ho, mul_zero, add_zero, mul_eq_zero,
             inner_self_eq_zero, vsub_eq_zero_iff_eq, hc.symm, or_false] at hop,
  rw [hop, zero_smul, zero_add, ←eq_vadd_iff_vsub_eq] at hpt,
  subst hpt,
  have hp' : (p₂ -ᵥ p₁ : V) ≠ 0, { simp [hp.symm] },
  have hp₂ : dist ((1 : ℝ) • (p₂ -ᵥ p₁) +ᵥ p₁) c₁ = r₁, { simp [hp₂c₁] },
  rw [←hp₁c₁, dist_smul_vadd_eq_dist _ _ hp'] at hpc₁ hp₂,
  simp only [one_ne_zero, false_or] at hp₂,
  rw hp₂.symm at hpc₁,
  cases hpc₁; simp [hpc₁]
end

/-- Distances `r₁` `r₂` of `p` from two different points `c₁` `c₂` determine at
most two points `p₁` `p₂` in two-dimensional space (two circles intersect in at
most two points). -/
lemma eq_of_dist_eq_of_dist_eq_of_findim_eq_two [finite_dimensional ℝ V] (hd : findim ℝ V = 2)
  {c₁ c₂ p₁ p₂ p : P} {r₁ r₂ : ℝ} (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁)
  (hp₂c₁ : dist p₂ c₁ = r₁) (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂)
  (hp₂c₂ : dist p₂ c₂ = r₂) (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ :=
begin
  have hd' : findim ℝ (⊤ : affine_subspace ℝ P).direction = 2,
  { rw [direction_top, findim_top],
    exact hd },
  exact eq_of_dist_eq_of_dist_eq_of_mem_of_findim_eq_two hd'
    (mem_top ℝ V _) (mem_top ℝ V _) (mem_top ℝ V _) (mem_top ℝ V _) (mem_top ℝ V _)
    hc hp hp₁c₁ hp₂c₁ hpc₁ hp₁c₂ hp₂c₂ hpc₂
end

variables {V}

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete, as an unbundled function.  This
definition is only intended for use in setting up the bundled version
`orthogonal_projection` and should not be used once that is
defined. -/
def orthogonal_projection_fn (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction]
  (p : P) : P :=
classical.some $ inter_eq_singleton_of_nonempty_of_is_compl
  (nonempty_subtype.mp ‹_›)
  (mk'_nonempty p s.directionᗮ)
  begin
    convert submodule.is_compl_orthogonal_of_is_complete (complete_space_coe_iff_is_complete.mp ‹_›),
    exact direction_mk' p s.directionᗮ
  end

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonal_projection_fn` of that
point onto the subspace.  This lemma is only intended for use in
setting up the bundled version and should not be used once that is
defined. -/
lemma inter_eq_singleton_orthogonal_projection_fn {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] (p : P) :
  (s : set P) ∩ (mk' p s.directionᗮ) = {orthogonal_projection_fn s p} :=
classical.some_spec $ inter_eq_singleton_of_nonempty_of_is_compl
  (nonempty_subtype.mp ‹_›)
  (mk'_nonempty p s.directionᗮ)
  begin
    convert submodule.is_compl_orthogonal_of_is_complete (complete_space_coe_iff_is_complete.mp ‹_›),
    exact direction_mk' p s.directionᗮ
  end

/-- The `orthogonal_projection_fn` lies in the given subspace.  This
lemma is only intended for use in setting up the bundled version and
should not be used once that is defined. -/
lemma orthogonal_projection_fn_mem {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] (p : P) : orthogonal_projection_fn s p ∈ s :=
begin
  rw [←mem_coe, ←set.singleton_subset_iff, ←inter_eq_singleton_orthogonal_projection_fn],
  exact set.inter_subset_left _ _
end

/-- The `orthogonal_projection_fn` lies in the orthogonal
subspace.  This lemma is only intended for use in setting up the
bundled version and should not be used once that is defined. -/
lemma orthogonal_projection_fn_mem_orthogonal {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] (p : P) :
  orthogonal_projection_fn s p ∈ mk' p s.directionᗮ :=
begin
  rw [←mem_coe, ←set.singleton_subset_iff, ←inter_eq_singleton_orthogonal_projection_fn],
  exact set.inter_subset_right _ _
end

/-- Subtracting `p` from its `orthogonal_projection_fn` produces a
result in the orthogonal direction.  This lemma is only intended for
use in setting up the bundled version and should not be used once that
is defined. -/
lemma orthogonal_projection_fn_vsub_mem_direction_orthogonal {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] (p : P) :
  orthogonal_projection_fn s p -ᵥ p ∈ s.directionᗮ :=
direction_mk' p s.directionᗮ ▸
  vsub_mem_direction (orthogonal_projection_fn_mem_orthogonal p) (self_mem_mk' _ _)

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete. The corresponding linear map
(mapping a vector to the difference between the projections of two
points whose difference is that vector) is the `orthogonal_projection`
for real inner product spaces, onto the direction of the affine
subspace being projected onto. -/
def orthogonal_projection (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction] :
  P →ᵃ[ℝ] s :=
{ to_fun := λ p, ⟨orthogonal_projection_fn s p, orthogonal_projection_fn_mem p⟩,
  linear := orthogonal_projection s.direction,
  map_vadd' := λ p v, begin
    have hs : ((orthogonal_projection s.direction) v : V) +ᵥ orthogonal_projection_fn s p ∈ s :=
      vadd_mem_of_mem_direction (orthogonal_projection s.direction v).2
                                (orthogonal_projection_fn_mem p),
    have ho : ((orthogonal_projection s.direction) v : V) +ᵥ orthogonal_projection_fn s p ∈
      mk' (v +ᵥ p) s.directionᗮ,
    { rw [←vsub_right_mem_direction_iff_mem (self_mem_mk' _ _) _, direction_mk',
          vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc],
      refine submodule.add_mem _ (orthogonal_projection_fn_vsub_mem_direction_orthogonal p) _,
      rw submodule.mem_orthogonal',
      intros w hw,
      rw [←neg_sub, inner_neg_left, orthogonal_projection_inner_eq_zero _ w hw, neg_zero], },
    have hm : ((orthogonal_projection s.direction) v : V) +ᵥ orthogonal_projection_fn s p ∈
      ({orthogonal_projection_fn s (v +ᵥ p)} : set P),
    { rw ←inter_eq_singleton_orthogonal_projection_fn (v +ᵥ p),
      exact set.mem_inter hs ho },
    rw set.mem_singleton_iff at hm,
    ext,
    exact hm.symm
  end }

@[simp] lemma orthogonal_projection_fn_eq {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] (p : P) :
  orthogonal_projection_fn s p = orthogonal_projection s p :=
rfl

/-- The linear map corresponding to `orthogonal_projection`. -/
@[simp] lemma orthogonal_projection_linear {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] :
  (orthogonal_projection s).linear = _root_.orthogonal_projection s.direction :=
rfl

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonal_projection` of that point
onto the subspace. -/
lemma inter_eq_singleton_orthogonal_projection {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] (p : P) :
  (s : set P) ∩ (mk' p s.directionᗮ) = {orthogonal_projection s p} :=
begin
  rw ←orthogonal_projection_fn_eq,
  exact inter_eq_singleton_orthogonal_projection_fn p
end

/-- The `orthogonal_projection` lies in the given subspace. -/
lemma orthogonal_projection_mem {s : affine_subspace ℝ P} [nonempty s] [complete_space s.direction]
  (p : P) : ↑(orthogonal_projection s p) ∈ s :=
(orthogonal_projection s p).2

/-- The `orthogonal_projection` lies in the orthogonal subspace. -/
lemma orthogonal_projection_mem_orthogonal (s : affine_subspace ℝ P) [nonempty s]
  [complete_space s.direction] (p : P) :
  ↑(orthogonal_projection s p) ∈ mk' p s.directionᗮ :=
orthogonal_projection_fn_mem_orthogonal p

/-- Subtracting a point in the given subspace from the
`orthogonal_projection` produces a result in the direction of the
given subspace. -/
lemma orthogonal_projection_vsub_mem_direction {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
  ↑(orthogonal_projection s p2 -ᵥ ⟨p1, hp1⟩ : s.direction) ∈ s.direction :=
(orthogonal_projection s p2 -ᵥ ⟨p1, hp1⟩ : s.direction).2

/-- Subtracting the `orthogonal_projection` from a point in the given
subspace produces a result in the direction of the given subspace. -/
lemma vsub_orthogonal_projection_mem_direction {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
  ↑((⟨p1, hp1⟩ : s) -ᵥ orthogonal_projection s p2 : s.direction) ∈ s.direction :=
((⟨p1, hp1⟩ : s) -ᵥ orthogonal_projection s p2 : s.direction).2

/-- A point equals its orthogonal projection if and only if it lies in
the subspace. -/
lemma orthogonal_projection_eq_self_iff {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p : P} :
  ↑(orthogonal_projection s p) = p ↔ p ∈ s :=
begin
  split,
  { exact λ h, h ▸ orthogonal_projection_mem p },
  { intro h,
    have hp : p ∈ ((s : set P) ∩ mk' p s.directionᗮ) := ⟨h, self_mem_mk' p _⟩,
    rw [inter_eq_singleton_orthogonal_projection p] at hp,
    symmetry,
    exact hp }
end

/-- Orthogonal projection is idempotent. -/
@[simp] lemma orthogonal_projection_orthogonal_projection (s : affine_subspace ℝ P) [nonempty s]
  [complete_space s.direction] (p : P) :
  orthogonal_projection s (orthogonal_projection s p) = orthogonal_projection s p :=
begin
  ext,
  rw orthogonal_projection_eq_self_iff,
  exact orthogonal_projection_mem p,
end

lemma eq_orthogonal_projection_of_eq_subspace {s s' : affine_subspace ℝ P} [nonempty s]
  [nonempty s'] [complete_space s.direction] [complete_space s'.direction] (h : s = s') (p : P) :
  (orthogonal_projection s p : P) = (orthogonal_projection s' p : P) :=
begin
  change orthogonal_projection_fn s p = orthogonal_projection_fn s' p,
  congr,
  exact h
end

/-- The distance to a point's orthogonal projection is 0 iff it lies in the subspace. -/
lemma dist_orthogonal_projection_eq_zero_iff {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p : P} :
  dist p (orthogonal_projection s p) = 0 ↔ p ∈ s :=
by rw [dist_comm, dist_eq_zero, orthogonal_projection_eq_self_iff]

/-- The distance between a point and its orthogonal projection is
nonzero if it does not lie in the subspace. -/
lemma dist_orthogonal_projection_ne_zero_of_not_mem {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p : P} (hp : p ∉ s) :
  dist p (orthogonal_projection s p) ≠ 0 :=
mt dist_orthogonal_projection_eq_zero_iff.mp hp

/-- Subtracting `p` from its `orthogonal_projection` produces a result
in the orthogonal direction. -/
lemma orthogonal_projection_vsub_mem_direction_orthogonal (s : affine_subspace ℝ P) [nonempty s]
  [complete_space s.direction] (p : P) :
  (orthogonal_projection s p : P) -ᵥ p ∈ s.directionᗮ :=
orthogonal_projection_fn_vsub_mem_direction_orthogonal p

/-- Subtracting the `orthogonal_projection` from `p` produces a result
in the orthogonal direction. -/
lemma vsub_orthogonal_projection_mem_direction_orthogonal (s : affine_subspace ℝ P) [nonempty s]
  [complete_space s.direction] (p : P) :
  p -ᵥ orthogonal_projection s p ∈ s.directionᗮ :=
direction_mk' p s.directionᗮ ▸
  vsub_mem_direction (self_mem_mk' _ _) (orthogonal_projection_mem_orthogonal s p)

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector was
in the orthogonal direction. -/
lemma orthogonal_projection_vadd_eq_self {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p : P} (hp : p ∈ s) {v : V}
  (hv : v ∈ s.directionᗮ) :
  orthogonal_projection s (v +ᵥ p) = ⟨p, hp⟩ :=
begin
  have h := vsub_orthogonal_projection_mem_direction_orthogonal s (v +ᵥ p),
  rw [vadd_vsub_assoc, submodule.add_mem_iff_right _ hv] at h,
  refine (eq_of_vsub_eq_zero _).symm,
  ext,
  refine submodule.disjoint_def.1 s.direction.orthogonal_disjoint _ _ h,
  exact (_ : s.direction).2
end

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
lemma orthogonal_projection_vadd_smul_vsub_orthogonal_projection {s : affine_subspace ℝ P}
  [nonempty s] [complete_space s.direction] {p1 : P} (p2 : P) (r : ℝ) (hp : p1 ∈ s) :
  orthogonal_projection s (r • (p2 -ᵥ orthogonal_projection s p2 : V) +ᵥ p1) = ⟨p1, hp⟩ :=
orthogonal_projection_vadd_eq_self hp
  (submodule.smul_mem _ _ (vsub_orthogonal_projection_mem_direction_orthogonal s _))

/-- The square of the distance from a point in `s` to `p2` equals the
sum of the squares of the distances of the two points to the
`orthogonal_projection`. -/
lemma dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
  {s : affine_subspace ℝ P} [nonempty s] [complete_space s.direction] {p1 : P}
  (p2 : P) (hp1 : p1 ∈ s) :
  dist p1 p2 * dist p1 p2 =
    dist p1 (orthogonal_projection s p2) * dist p1 (orthogonal_projection s p2) +
    dist p2 (orthogonal_projection s p2) * dist p2 (orthogonal_projection s p2) :=
begin
  rw [metric_space.dist_comm p2 _, dist_eq_norm_vsub V p1 _, dist_eq_norm_vsub V p1 _,
    dist_eq_norm_vsub V _ p2, ← vsub_add_vsub_cancel p1 (orthogonal_projection s p2) p2,
    norm_add_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero],
  exact submodule.inner_right_of_mem_orthogonal
    (vsub_orthogonal_projection_mem_direction p2 hp1)
    (orthogonal_projection_vsub_mem_direction_orthogonal s p2),
end

/-- The square of the distance between two points constructed by
adding multiples of the same orthogonal vector to points in the same
subspace. -/
lemma dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd {s : affine_subspace ℝ P}
    {p1 p2 : P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) (r1 r2 : ℝ) {v : V}
    (hv : v ∈ s.directionᗮ) :
  dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) * dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) =
    dist p1 p2 * dist p1 p2 + (r1 - r2) * (r1 - r2) * (∥v∥ * ∥v∥) :=
calc dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) * dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2)
    = ∥(p1 -ᵥ p2) + (r1 - r2) • v∥ * ∥(p1 -ᵥ p2) + (r1 - r2) • v∥
  : by { rw [dist_eq_norm_vsub V (r1 • v +ᵥ p1), vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, sub_smul],
         abel }
... = ∥p1 -ᵥ p2∥ * ∥p1 -ᵥ p2∥ + ∥(r1 - r2) • v∥ * ∥(r1 - r2) • v∥
  : norm_add_square_eq_norm_square_add_norm_square_real
      (submodule.inner_right_of_mem_orthogonal (vsub_mem_direction hp1 hp2)
        (submodule.smul_mem _ _ hv))
... = ∥(p1 -ᵥ p2 : V)∥ * ∥(p1 -ᵥ p2 : V)∥ + abs (r1 - r2) * abs (r1 - r2) * ∥v∥ * ∥v∥
  : by { rw [norm_smul, real.norm_eq_abs], ring }
... = dist p1 p2 * dist p1 p2 + (r1 - r2) * (r1 - r2) * (∥v∥ * ∥v∥)
  : by { rw [dist_eq_norm_vsub V p1, abs_mul_abs_self, mul_assoc] }

/-- Reflection in an affine subspace, which is expected to be nonempty
and complete.  The word "reflection" is sometimes understood to mean
specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point.  The
definition here, of reflection in an affine subspace, is a more
general sense of the word that includes both those common cases.  If
the subspace is empty or not complete, `orthogonal_projection` is
defined as the identity map, which results in `reflection` being the
identity map in that case as well. -/
def reflection (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction] :
  P ≃ᵢ P :=
{ to_fun := λ p, (↑(orthogonal_projection s p) -ᵥ p) +ᵥ orthogonal_projection s p,
  inv_fun := λ p, (↑(orthogonal_projection s p) -ᵥ p) +ᵥ orthogonal_projection s p,
  left_inv := λ p, by simp [vsub_vadd_eq_vsub_sub, -orthogonal_projection_linear],
  right_inv := λ p, by simp [vsub_vadd_eq_vsub_sub, -orthogonal_projection_linear],
  isometry_to_fun := begin
    dsimp only,
    rw isometry_emetric_iff_metric,
    intros p₁ p₂,
    rw [←mul_self_inj_of_nonneg dist_nonneg dist_nonneg, dist_eq_norm_vsub V
          ((↑(orthogonal_projection s p₁) -ᵥ p₁) +ᵥ ↑(orthogonal_projection s p₁)),
        dist_eq_norm_vsub V p₁, ←inner_self_eq_norm_square, ←inner_self_eq_norm_square],
    calc
      ⟪((orthogonal_projection s p₁ : P) -ᵥ p₁ +ᵥ (orthogonal_projection s p₁ : P) -ᵥ
      ((orthogonal_projection s p₂ : P) -ᵥ p₂ +ᵥ orthogonal_projection s p₂)),
      ((orthogonal_projection s p₁ : P) -ᵥ p₁ +ᵥ (orthogonal_projection s p₁ : P) -ᵥ
      ((orthogonal_projection s p₂ : P) -ᵥ p₂ +ᵥ orthogonal_projection s p₂))⟫
        = ⟪(_root_.orthogonal_projection s.direction (p₁ -ᵥ p₂)) +
          _root_.orthogonal_projection s.direction (p₁ -ᵥ p₂) - (p₁ -ᵥ p₂),
          _root_.orthogonal_projection s.direction (p₁ -ᵥ p₂) +
          _root_.orthogonal_projection s.direction (p₁ -ᵥ p₂) - (p₁ -ᵥ p₂)⟫
        : by { rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc,
          ←vsub_vadd_eq_vsub_sub, vsub_vadd_comm, vsub_vadd_eq_vsub_sub, ←add_sub_assoc, ←coe_vsub,
          ←affine_map.linear_map_vsub], simp }
    ... = -4 * inner (p₁ -ᵥ p₂ - (_root_.orthogonal_projection s.direction (p₁ -ᵥ p₂) : V))
                   (_root_.orthogonal_projection s.direction (p₁ -ᵥ p₂)) +
          ⟪p₁ -ᵥ p₂, p₁ -ᵥ p₂⟫
        : by { simp [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
                 real_inner_comm (p₁ -ᵥ p₂)], ring }
    ... = ⟪p₁ -ᵥ p₂, p₁ -ᵥ p₂⟫ : by simp,
  end }

/-- The result of reflecting. -/
lemma reflection_apply (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction] (p : P) :
  reflection s p = (↑(orthogonal_projection s p) -ᵥ p) +ᵥ orthogonal_projection s p :=
rfl

lemma eq_reflection_of_eq_subspace {s s' : affine_subspace ℝ P} [nonempty s]
  [nonempty s'] [complete_space s.direction] [complete_space s'.direction] (h : s = s') (p : P) :
  (reflection s p : P) = (reflection s' p : P) :=
by simp [reflection_apply, eq_orthogonal_projection_of_eq_subspace h]

/-- Reflection is its own inverse. -/
@[simp] lemma reflection_symm (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction] :
  (reflection s).symm = reflection s :=
rfl

/-- Reflecting twice in the same subspace. -/
@[simp] lemma reflection_reflection (s : affine_subspace ℝ P) [nonempty s]
  [complete_space s.direction] (p : P) :
  reflection s (reflection s p) = p :=
(reflection s).left_inv p

/-- Reflection is involutive. -/
lemma reflection_involutive (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction] :
  function.involutive (reflection s) :=
reflection_reflection s

/-- A point is its own reflection if and only if it is in the
subspace. -/
lemma reflection_eq_self_iff {s : affine_subspace ℝ P} [nonempty s] [complete_space s.direction]
  (p : P) : reflection s p = p ↔ p ∈ s :=
begin
  rw [←orthogonal_projection_eq_self_iff, reflection_apply],
  split,
  { intro h,
    rw [←@vsub_eq_zero_iff_eq V, vadd_vsub_assoc,
        ←two_smul ℝ (↑(orthogonal_projection s p) -ᵥ p), smul_eq_zero] at h,
    norm_num at h,
    exact h },
  { intro h,
    simp [h] }
end

/-- Reflecting a point in two subspaces produces the same result if
and only if the point has the same orthogonal projection in each of
those subspaces. -/
lemma reflection_eq_iff_orthogonal_projection_eq (s₁ s₂ : affine_subspace ℝ P)
  [nonempty s₁] [nonempty s₂] [complete_space s₁.direction] [complete_space s₂.direction] (p : P) :
  reflection s₁ p = reflection s₂ p ↔
    (orthogonal_projection s₁ p : P) = orthogonal_projection s₂ p :=
begin
  rw [reflection_apply, reflection_apply],
  split,
  { intro h,
    rw [←@vsub_eq_zero_iff_eq V, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm,
        add_sub_assoc, vsub_sub_vsub_cancel_right,
        ←two_smul ℝ ((orthogonal_projection s₁ p : P) -ᵥ orthogonal_projection s₂ p),
        smul_eq_zero] at h,
    norm_num at h,
    exact h },
  { intro h,
    rw h }
end

/-- The distance between `p₁` and the reflection of `p₂` equals that
between the reflection of `p₁` and `p₂`. -/
lemma dist_reflection (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction] (p₁ p₂ : P) :
  dist p₁ (reflection s p₂) = dist (reflection s p₁) p₂ :=
begin
  conv_lhs { rw ←reflection_reflection s p₁ },
  exact (reflection s).dist_eq _ _
end

/-- A point in the subspace is equidistant from another point and its
reflection. -/
lemma dist_reflection_eq_of_mem (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction]
  {p₁ : P} (hp₁ : p₁ ∈ s) (p₂ : P) :
  dist p₁ (reflection s p₂) = dist p₁ p₂ :=
begin
  rw ←reflection_eq_self_iff p₁ at hp₁,
  convert (reflection s).dist_eq p₁ p₂,
  rw hp₁
end

/-- The reflection of a point in a subspace is contained in any larger
subspace containing both the point and the subspace reflected in. -/
lemma reflection_mem_of_le_of_mem {s₁ s₂ : affine_subspace ℝ P} [nonempty s₁]
  [complete_space s₁.direction] (hle : s₁ ≤ s₂) {p : P}
  (hp : p ∈ s₂) : reflection s₁ p ∈ s₂ :=
begin
  rw [reflection_apply],
  have ho : ↑(orthogonal_projection s₁ p) ∈ s₂ := hle (orthogonal_projection_mem p),
  exact vadd_mem_of_mem_direction (vsub_mem_direction ho hp) ho
end

/-- Reflecting an orthogonal vector plus a point in the subspace
produces the negation of that vector plus the point. -/
lemma reflection_orthogonal_vadd {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p : P} (hp : p ∈ s) {v : V}
  (hv : v ∈ s.directionᗮ) : reflection s (v +ᵥ p) = -v +ᵥ p :=
begin
  rw [reflection_apply, orthogonal_projection_vadd_eq_self hp hv, vsub_vadd_eq_vsub_sub],
  simp
end

/-- Reflecting a vector plus a point in the subspace produces the
negation of that vector plus the point if the vector is a multiple of
the result of subtracting a point's orthogonal projection from that
point. -/
lemma reflection_vadd_smul_vsub_orthogonal_projection {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p₁ : P} (p₂ : P) (r : ℝ) (hp₁ : p₁ ∈ s) :
  reflection s (r • (p₂ -ᵥ orthogonal_projection s p₂) +ᵥ p₁) =
    -(r • (p₂ -ᵥ orthogonal_projection s p₂)) +ᵥ p₁ :=
reflection_orthogonal_vadd hp₁
  (submodule.smul_mem _ _ (vsub_orthogonal_projection_mem_direction_orthogonal s _))

omit V

/-- A set of points is cospherical if they are equidistant from some
point.  In two dimensions, this is the same thing as being
concyclic. -/
def cospherical (ps : set P) : Prop :=
∃ (center : P) (radius : ℝ), ∀ p ∈ ps, dist p center = radius

/-- The definition of `cospherical`. -/
lemma cospherical_def (ps : set P) :
  cospherical ps ↔ ∃ (center : P) (radius : ℝ), ∀ p ∈ ps, dist p center = radius :=
iff.rfl

/-- A subset of a cospherical set is cospherical. -/
lemma cospherical_subset {ps₁ ps₂ : set P} (hs : ps₁ ⊆ ps₂) (hc : cospherical ps₂) :
  cospherical ps₁ :=
begin
  rcases hc with ⟨c, r, hcr⟩,
  exact ⟨c, r, λ p hp, hcr p (hs hp)⟩
end

include V

/-- The empty set is cospherical. -/
lemma cospherical_empty : cospherical (∅ : set P) :=
begin
  use add_torsor.nonempty.some,
  simp,
end

omit V

/-- A single point is cospherical. -/
lemma cospherical_singleton (p : P) : cospherical ({p} : set P) :=
begin
  use p,
  simp
end

include V

/-- Two points are cospherical. -/
lemma cospherical_insert_singleton (p₁ p₂ : P) : cospherical ({p₁, p₂} : set P) :=
begin
  use [(2⁻¹ : ℝ) • (p₂ -ᵥ p₁) +ᵥ p₁, (2⁻¹ : ℝ) * (dist p₂ p₁)],
  intro p,
  rw [set.mem_insert_iff, set.mem_singleton_iff],
  rintro ⟨_|_⟩,
  { rw [dist_eq_norm_vsub V p₁, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, norm_neg, norm_smul,
        dist_eq_norm_vsub V p₂],
    simp },
  { rw [H, dist_eq_norm_vsub V p₂, vsub_vadd_eq_vsub_sub, dist_eq_norm_vsub V p₂],
    conv_lhs { congr, congr, rw ←one_smul ℝ (p₂ -ᵥ p₁ : V) },
    rw [←sub_smul, norm_smul],
    norm_num }
end

/-- Any three points in a cospherical set are affinely independent. -/
lemma cospherical.affine_independent {s : set P} (hs : cospherical s) {p : fin 3 → P}
  (hps : set.range p ⊆ s) (hpi : function.injective p) :
  affine_independent ℝ p :=
begin
  rw affine_independent_iff_not_collinear,
  intro hc,
  rw collinear_iff_of_mem ℝ (set.mem_range_self (0 : fin 3)) at hc,
  rcases hc with ⟨v, hv⟩,
  rw set.forall_range_iff at hv,
  have hv0 : v ≠ 0,
  { intro h,
    have he : p 1 = p 0, by simpa [h] using hv 1,
    exact (dec_trivial : (1 : fin 3) ≠ 0) (hpi he) },
  rcases hs with ⟨c, r, hs⟩,
  have hs' := λ i, hs (p i) (set.mem_of_mem_of_subset (set.mem_range_self _) hps),
  choose f hf using hv,
  have hsd : ∀ i, dist ((f i • v) +ᵥ p 0) c = r,
  { intro i,
    rw ←hf,
    exact hs' i },
  have hf0 : f 0 = 0,
  { have hf0' := hf 0,
    rw [eq_comm, ←@vsub_eq_zero_iff_eq V, vadd_vsub, smul_eq_zero] at hf0',
    simpa [hv0] using hf0' },
  have hfi : function.injective f,
  { intros i j h,
    have hi := hf i,
    rw [h, ←hf j] at hi,
    exact hpi hi },
  simp_rw [←hsd 0, hf0, zero_smul, zero_vadd, dist_smul_vadd_eq_dist (p 0) c hv0] at hsd,
  have hfn0 : ∀ i, i ≠ 0 → f i ≠ 0 := λ i, (hfi.ne_iff' hf0).2,
  have hfn0' : ∀ i, i ≠ 0 → f i = (-2) * ⟪v, (p 0 -ᵥ c)⟫ / ⟪v, v⟫,
  { intros i hi,
    have hsdi := hsd i,
    simpa [hfn0, hi] using hsdi },
  have hf12 : f 1 = f 2, { rw [hfn0' 1 dec_trivial, hfn0' 2 dec_trivial] },
  exact (dec_trivial : (1 : fin 3) ≠ 2) (hfi hf12)
end

end euclidean_geometry
