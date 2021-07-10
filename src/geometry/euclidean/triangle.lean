/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
import geometry.euclidean.basic
import tactic.interval_cases

/-!
# Triangles

This file proves basic geometrical results about distances and angles
in (possibly degenerate) triangles in real inner product spaces and
Euclidean affine spaces.  More specialized results, and results
developed for simplices in general rather than just for triangles, are
in separate files.  Definitions and results that make sense in more
general affine spaces rather than just in the Euclidean case go under
`linear_algebra.affine_space`.

## Implementation notes

Results in this file are generally given in a form with only those
non-degeneracy conditions needed for the particular result, rather
than requiring affine independence of the points of a triangle
unnecessarily.

## References

* https://en.wikipedia.org/wiki/Pythagorean_theorem
* https://en.wikipedia.org/wiki/Law_of_cosines
* https://en.wikipedia.org/wiki/Pons_asinorum
* https://en.wikipedia.org/wiki/Sum_of_angles_of_a_triangle

-/

noncomputable theory
open_locale big_operators
open_locale classical
open_locale real
open_locale real_inner_product_space

namespace inner_product_geometry

/-!
### Geometrical results on triangles in real inner product spaces

This section develops some results on (possibly degenerate) triangles
in real inner product spaces, where those definitions and results can
most conveniently be developed in terms of vectors and then used to
deduce corresponding results for Euclidean affine spaces.
-/

variables {V : Type*} [inner_product_space ℝ V]

/-- Pythagorean theorem, if-and-only-if vector angle form. -/
lemma norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ angle x y = π / 2 :=
begin
  rw norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero,
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y
end

/-- Pythagorean theorem, vector angle form. -/
lemma norm_add_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ :=
(norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector angle form. -/
lemma norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ angle x y = π / 2 :=
begin
  rw norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero,
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y
end

/-- Pythagorean theorem, subtracting vectors, vector angle form. -/
lemma norm_sub_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ :=
(norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

/-- Law of cosines (cosine rule), vector angle form. -/
lemma norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
    (x y : V) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ - 2 * ∥x∥ * ∥y∥ * real.cos (angle x y) :=
by rw [(show 2 * ∥x∥ * ∥y∥ * real.cos (angle x y) =
             2 * (real.cos (angle x y) * (∥x∥ * ∥y∥)), by ring),
       cos_angle_mul_norm_mul_norm, ←real_inner_self_eq_norm_sq,
       ←real_inner_self_eq_norm_sq, ←real_inner_self_eq_norm_sq, real_inner_sub_sub_self,
       sub_add_eq_add_sub]

/-- Pons asinorum, vector angle form. -/
lemma angle_sub_eq_angle_sub_rev_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) :
  angle x (x - y) = angle y (y - x) :=
begin
  refine real.inj_on_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨angle_nonneg _ _, angle_le_pi _ _⟩ _,
  rw [cos_angle, cos_angle, h, ←neg_sub, norm_neg, neg_sub,
    inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, h, real_inner_comm x y]
end

/-- Converse of pons asinorum, vector angle form. -/
lemma norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {x y : V}
    (h : angle x (x - y) = angle y (y - x)) (hpi : angle x y ≠ π) : ∥x∥ = ∥y∥ :=
begin
  replace h := real.arccos_inj_on
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x (x - y)))
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one y (y - x))) h,
  by_cases hxy : x = y,
  { rw hxy },
  { rw [←norm_neg (y - x), neg_sub, mul_comm, mul_comm ∥y∥, div_eq_mul_inv, div_eq_mul_inv,
        mul_inv_rev', mul_inv_rev', ←mul_assoc, ←mul_assoc] at h,
    replace h :=
      mul_right_cancel' (inv_ne_zero (λ hz, hxy (eq_of_sub_eq_zero (norm_eq_zero.1 hz)))) h,
    rw [inner_sub_right, inner_sub_right, real_inner_comm x y, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq, mul_sub_right_distrib, mul_sub_right_distrib,
        mul_self_mul_inv, mul_self_mul_inv, sub_eq_sub_iff_sub_eq_sub,
        ←mul_sub_left_distrib] at h,
    by_cases hx0 : x = 0,
    { rw [hx0, norm_zero, inner_zero_left, zero_mul, zero_sub, neg_eq_zero] at h,
      rw [hx0, norm_zero, h] },
    { by_cases hy0 : y = 0,
      { rw [hy0, norm_zero, inner_zero_right, zero_mul, sub_zero] at h,
        rw [hy0, norm_zero, h] },
      { rw [inv_sub_inv (λ hz, hx0 (norm_eq_zero.1 hz)) (λ hz, hy0 (norm_eq_zero.1 hz)),
            ←neg_sub, ←mul_div_assoc, mul_comm, mul_div_assoc, ←mul_neg_one] at h,
        symmetry,
        by_contradiction hyx,
        replace h := (mul_left_cancel' (sub_ne_zero_of_ne hyx) h).symm,
        rw [real_inner_div_norm_mul_norm_eq_neg_one_iff, ←angle_eq_pi_iff] at h,
        exact hpi h } } }
end

/-- The cosine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.cos (angle x (x - y) + angle y (y - x)) = -real.cos (angle x y) :=
begin
  by_cases hxy : x = y,
  { rw [hxy, angle_self hy],
    simp },
  { rw [real.cos_add, cos_angle, cos_angle, cos_angle],
    have hxn : ∥x∥ ≠ 0 := (λ h, hx (norm_eq_zero.1 h)),
    have hyn : ∥y∥ ≠ 0 := (λ h, hy (norm_eq_zero.1 h)),
    have hxyn : ∥x - y∥ ≠ 0 := (λ h, hxy (eq_of_sub_eq_zero (norm_eq_zero.1 h))),
    apply mul_right_cancel' hxn,
    apply mul_right_cancel' hyn,
    apply mul_right_cancel' hxyn,
    apply mul_right_cancel' hxyn,
    have H1 : real.sin (angle x (x - y)) * real.sin (angle y (y - x)) *
                ∥x∥ * ∥y∥ * ∥x - y∥ * ∥x - y∥ =
              (real.sin (angle x (x - y)) * (∥x∥ * ∥x - y∥)) *
                (real.sin (angle y (y - x)) * (∥y∥ * ∥x - y∥)), { ring },
    have H2 : ⟪x, x⟫ * (inner x x - inner x y - (inner x y - inner y y)) -
                (inner x x - inner x y) * (inner x x - inner x y) =
              inner x x * inner y y - inner x y * inner x y, { ring },
    have H3 : ⟪y, y⟫ * (inner y y - inner x y - (inner x y - inner x x)) -
                (inner y y - inner x y) * (inner y y - inner x y) =
              inner x x * inner y y - inner x y * inner x y, { ring },
    rw [mul_sub_right_distrib, mul_sub_right_distrib, mul_sub_right_distrib,
        mul_sub_right_distrib, H1, sin_angle_mul_norm_mul_norm, norm_sub_rev x y,
        sin_angle_mul_norm_mul_norm, norm_sub_rev y x, inner_sub_left, inner_sub_left,
        inner_sub_right, inner_sub_right, inner_sub_right, inner_sub_right, real_inner_comm x y, H2,
        H3, real.mul_self_sqrt (sub_nonneg_of_le (real_inner_mul_inner_self_le x y)),
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
        real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two],
    field_simp [hxn, hyn, hxyn],
    ring }
end

/-- The sine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma sin_angle_sub_add_angle_sub_rev_eq_sin_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.sin (angle x (x - y) + angle y (y - x)) = real.sin (angle x y) :=
begin
  by_cases hxy : x = y,
  { rw [hxy, angle_self hy],
    simp },
  { rw [real.sin_add, cos_angle, cos_angle],
    have hxn : ∥x∥ ≠ 0 := (λ h, hx (norm_eq_zero.1 h)),
    have hyn : ∥y∥ ≠ 0 := (λ h, hy (norm_eq_zero.1 h)),
    have hxyn : ∥x - y∥ ≠ 0 := (λ h, hxy (eq_of_sub_eq_zero (norm_eq_zero.1 h))),
    apply mul_right_cancel' hxn,
    apply mul_right_cancel' hyn,
    apply mul_right_cancel' hxyn,
    apply mul_right_cancel' hxyn,
    have H1 : real.sin (angle x (x - y)) * (⟪y, y - x⟫ / (∥y∥ * ∥y - x∥)) * ∥x∥ * ∥y∥ * ∥x - y∥ =
                real.sin (angle x (x - y)) * (∥x∥ * ∥x - y∥) *
                  (⟪y, y - x⟫ / (∥y∥ * ∥y - x∥)) * ∥y∥, { ring },
    have H2 : ⟪x, x - y⟫ / (∥x∥ * ∥y - x∥) * real.sin (angle y (y - x)) * ∥x∥ * ∥y∥ * ∥y - x∥ =
                ⟪x, x - y⟫ / (∥x∥ * ∥y - x∥) *
                  (real.sin (angle y (y - x)) * (∥y∥ * ∥y - x∥)) * ∥x∥, { ring },
    have H3 : ⟪x, x⟫ * (⟪x, x⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪y, y⟫)) -
                (⟪x, x⟫ - ⟪x, y⟫) * (⟪x, x⟫ - ⟪x, y⟫) =
              ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫, { ring },
    have H4 : ⟪y, y⟫ * (⟪y, y⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪x, x⟫)) -
                (⟪y, y⟫ - ⟪x, y⟫) * (⟪y, y⟫ - ⟪x, y⟫) =
              ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫  * ⟪x, y⟫, { ring },
    rw [right_distrib, right_distrib, right_distrib, right_distrib, H1,
        sin_angle_mul_norm_mul_norm, norm_sub_rev x y, H2, sin_angle_mul_norm_mul_norm,
        norm_sub_rev y x, mul_assoc (real.sin (angle x y)), sin_angle_mul_norm_mul_norm,
        inner_sub_left, inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_right,
        inner_sub_right, real_inner_comm x y, H3, H4, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq,
        real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two],
    field_simp [hxn, hyn, hxyn],
    ring }
end

/-- The cosine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma cos_angle_add_angle_sub_add_angle_sub_eq_neg_one {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.cos (angle x y + angle x (x - y) + angle y (y - x)) = -1 :=
by rw [add_assoc, real.cos_add, cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle hx hy,
       sin_angle_sub_add_angle_sub_rev_eq_sin_angle hx hy, ←neg_mul_eq_mul_neg, ←neg_add',
       add_comm, ←sq, ←sq, real.sin_sq_add_cos_sq]

/-- The sine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma sin_angle_add_angle_sub_add_angle_sub_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.sin (angle x y + angle x (x - y) + angle y (y - x)) = 0 :=
begin
  rw [add_assoc, real.sin_add, cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle hx hy,
      sin_angle_sub_add_angle_sub_rev_eq_sin_angle hx hy],
  ring
end

/-- The sum of the angles of a possibly degenerate triangle (where the
two given sides are nonzero), vector angle form. -/
lemma angle_add_angle_sub_add_angle_sub_eq_pi {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  angle x y + angle x (x - y) + angle y (y - x) = π :=
begin
  have hcos := cos_angle_add_angle_sub_add_angle_sub_eq_neg_one hx hy,
  have hsin := sin_angle_add_angle_sub_add_angle_sub_eq_zero hx hy,
  rw real.sin_eq_zero_iff at hsin,
  cases hsin with n hn,
  symmetry' at hn,
  have h0 : 0 ≤ angle x y + angle x (x - y) + angle y (y - x) :=
    add_nonneg (add_nonneg (angle_nonneg _ _) (angle_nonneg _ _)) (angle_nonneg _ _),
  have h3 : angle x y + angle x (x - y) + angle y (y - x) ≤ π + π + π :=
    add_le_add (add_le_add (angle_le_pi _ _) (angle_le_pi _ _)) (angle_le_pi _ _),
  have h3lt : angle x y + angle x (x - y) + angle y (y - x) < π + π + π,
  { by_contradiction hnlt,
    have hxy : angle x y = π,
    { by_contradiction hxy,
      exact hnlt (add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le
                                           (lt_of_le_of_ne (angle_le_pi _ _) hxy)
                                         (angle_le_pi _ _)) (angle_le_pi _ _)) },
    rw hxy at hnlt,
    rw angle_eq_pi_iff at hxy,
    rcases hxy with ⟨hx, ⟨r, ⟨hr, hxr⟩⟩⟩,
    rw [hxr, ←one_smul ℝ x, ←mul_smul, mul_one, ←sub_smul, one_smul, sub_eq_add_neg,
        angle_smul_right_of_pos _ _ (add_pos zero_lt_one (neg_pos_of_neg hr)), angle_self hx,
        add_zero] at hnlt,
    apply hnlt,
    rw add_assoc,
    exact add_lt_add_left (lt_of_le_of_lt (angle_le_pi _ _)
                                          (lt_add_of_pos_right π real.pi_pos)) _ },
  have hn0 : 0 ≤ n,
  { rw [hn, mul_nonneg_iff_right_nonneg_of_pos real.pi_pos] at h0,
    norm_cast at h0,
    exact h0 },
  have hn3 : n < 3,
  { rw [hn, (show π + π + π = 3 * π, by ring)] at h3lt,
    replace h3lt := lt_of_mul_lt_mul_right h3lt (le_of_lt real.pi_pos),
    norm_cast at h3lt,
    exact h3lt },
  interval_cases n,
  { rw hn at hcos,
    simp at hcos,
    norm_num at hcos },
  { rw hn,
    norm_num },
  { rw hn at hcos,
    simp at hcos,
    norm_num at hcos },
end

end inner_product_geometry

namespace euclidean_geometry
/-!
### Geometrical results on triangles in Euclidean affine spaces

This section develops some geometrical definitions and results on
(possible degenerate) triangles in Euclidean affine spaces.
-/
open inner_product_geometry

open_locale euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P]
include V

/-- **Pythagorean theorem**, if-and-only-if angle-at-point form. -/
lemma dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two (p1 p2 p3 : P) :
  dist p1 p3 * dist p1 p3 = dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 ↔
    ∠ p1 p2 p3 = π / 2 :=
by erw [pseudo_metric_space.dist_comm p3 p2, dist_eq_norm_vsub V p1 p3, dist_eq_norm_vsub V p1 p2,
        dist_eq_norm_vsub V p2 p3,
        ←norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two,
        vsub_sub_vsub_cancel_right p1, ←neg_vsub_eq_vsub_rev p2 p3, norm_neg]

/-- **Law of cosines** (cosine rule), angle-at-point form. -/
lemma dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
    (p1 p2 p3 : P) :
  dist p1 p3 * dist p1 p3 =
    dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 -
      2 * dist p1 p2 * dist p3 p2 * real.cos (∠ p1 p2 p3) :=
begin
  rw [dist_eq_norm_vsub V p1 p3, dist_eq_norm_vsub V p1 p2, dist_eq_norm_vsub V p3 p2],
  unfold angle,
  convert norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
          (p1 -ᵥ p2 : V) (p3 -ᵥ p2 : V),
  { exact (vsub_sub_vsub_cancel_right p1 p3 p2).symm },
  { exact (vsub_sub_vsub_cancel_right p1 p3 p2).symm }
end

alias dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle ← law_cos

/-- **Isosceles Triangle Theorem**: Pons asinorum, angle-at-point form. -/
lemma angle_eq_angle_of_dist_eq {p1 p2 p3 : P} (h : dist p1 p2 = dist p1 p3) :
  ∠ p1 p2 p3 = ∠ p1 p3 p2 :=
begin
  rw [dist_eq_norm_vsub V p1 p2, dist_eq_norm_vsub V p1 p3] at h,
  unfold angle,
  convert angle_sub_eq_angle_sub_rev_of_norm_eq h,
  { exact (vsub_sub_vsub_cancel_left p3 p2 p1).symm },
  { exact (vsub_sub_vsub_cancel_left p2 p3 p1).symm }
end

/-- Converse of pons asinorum, angle-at-point form. -/
lemma dist_eq_of_angle_eq_angle_of_angle_ne_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = ∠ p1 p3 p2)
    (hpi : ∠ p2 p1 p3 ≠ π) : dist p1 p2 = dist p1 p3 :=
begin
  unfold angle at h hpi,
  rw [dist_eq_norm_vsub V p1 p2, dist_eq_norm_vsub V p1 p3],
  rw [←angle_neg_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hpi,
  rw [←vsub_sub_vsub_cancel_left p3 p2 p1, ←vsub_sub_vsub_cancel_left p2 p3 p1] at h,
  exact norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi h hpi
end

/-- The **sum of the angles of a triangle** (possibly degenerate, where the
given vertex is distinct from the others), angle-at-point. -/
lemma angle_add_angle_add_angle_eq_pi {p1 p2 p3 : P} (h2 : p2 ≠ p1) (h3 : p3 ≠ p1) :
  ∠ p1 p2 p3 + ∠ p2 p3 p1 + ∠ p3 p1 p2 = π :=
begin
  rw [add_assoc, add_comm, add_comm (∠ p2 p3 p1), angle_comm p2 p3 p1],
  unfold angle,
  rw [←angle_neg_neg (p1 -ᵥ p3), ←angle_neg_neg (p1 -ᵥ p2), neg_vsub_eq_vsub_rev,
      neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev,
      ←vsub_sub_vsub_cancel_right p3 p2 p1, ←vsub_sub_vsub_cancel_right p2 p3 p1],
  exact angle_add_angle_sub_add_angle_sub_eq_pi (λ he, h3 (vsub_eq_zero_iff_eq.1 he))
                                                (λ he, h2 (vsub_eq_zero_iff_eq.1 he))
end

/-- **Stewart's Theorem**. -/
theorem dist_sq_mul_dist_add_dist_sq_mul_dist (a b c p : P) (h : ∠ b p c = π) :
  dist a b ^ 2 * dist c p + dist a c ^ 2 * dist b p =
  dist b c * (dist a p ^ 2 + dist b p * dist c p) :=
begin
  rw [pow_two, pow_two, law_cos a p b, law_cos a p c,
      eq_sub_of_add_eq (angle_add_angle_eq_pi_of_angle_eq_pi a h), real.cos_pi_sub,
      dist_eq_add_dist_of_angle_eq_pi h],
  ring,
end

/-- **Apollonius's Theorem**. -/
theorem dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (a b c : P) :
  dist a b ^ 2 + dist a c ^ 2 = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) :=
begin
  by_cases hbc : b = c,
  { simp [hbc, midpoint_self, dist_self, two_mul] },
  { let m := midpoint ℝ b c,
    have : dist b c ≠ 0 := (dist_pos.mpr hbc).ne',
    have hm := dist_sq_mul_dist_add_dist_sq_mul_dist a b c m (angle_midpoint_eq_pi b c hbc),
    simp only [dist_left_midpoint, dist_right_midpoint, real.norm_two] at hm,
    calc  dist a b ^ 2 + dist a c ^ 2
        = 2 / dist b c * (dist a b ^ 2 * (2⁻¹ * dist b c) + dist a c ^ 2 * (2⁻¹ * dist b c)) :
          by { field_simp, ring }
    ... = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) :
          by { rw hm, field_simp, ring } },
end

lemma dist_mul_of_eq_angle_of_dist_mul (a b c a' b' c' : P) (r : ℝ) (h : ∠ a' b' c' = ∠ a b c)
  (hab : dist a' b' = r * dist a b) (hcb : dist c' b' = r * dist c b) :
  dist a' c' = r * dist a c :=
begin
  have h' : dist a' c' ^ 2 = (r * dist a c) ^ 2,
    calc  dist a' c' ^ 2
        = dist a' b' ^ 2 + dist c' b' ^ 2 - 2 * dist a' b' * dist c' b' * real.cos (∠ a' b' c') :
          by { simp [pow_two, law_cos a' b' c'] }
    ... = r ^ 2 * (dist a b ^ 2 + dist c b ^ 2 - 2 * dist a b * dist c b * real.cos (∠ a b c)) :
          by { rw [h, hab, hcb], ring }
    ... = (r * dist a c) ^ 2 : by simp [pow_two, ← law_cos a b c, mul_pow],
  by_cases hab₁ : a = b,
  { have hab'₁ : a' = b', { rw [← dist_eq_zero, hab, dist_eq_zero.mpr hab₁, mul_zero r] },
    rw [hab₁, hab'₁, dist_comm b' c', dist_comm b c, hcb] },
  { have h1 : 0 ≤ r * dist a b, { rw ← hab, exact dist_nonneg },
    have h2 : 0 ≤ r := nonneg_of_mul_nonneg_right h1 (dist_pos.mpr hab₁),
    exact (eq_of_sq_eq_sq dist_nonneg (mul_nonneg h2 dist_nonneg)).mp h' },
end

end euclidean_geometry
