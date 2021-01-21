/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import geometry.euclidean.basic
import tactic.derive_fintype

noncomputable theory
open_locale big_operators
open_locale classical
open_locale real
open_locale real_inner_product_space

/-!
# Circumcenter and circumradius

This file proves some lemmas on points equidistant from a set of
points, and defines the circumradius and circumcenter of a simplex.
There are also some definitions for use in calculations where it is
convenient to work with affine combinations of vertices together with
the circumcenter.

## Main definitions

* `circumcenter` and `circumradius` are the circumcenter and
  circumradius of a simplex.

## References

* https://en.wikipedia.org/wiki/Circumscribed_circle

-/

namespace euclidean_geometry

open inner_product_geometry

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P]
include V

open affine_subspace

/-- `p` is equidistant from two points in `s` if and only if its
`orthogonal_projection` is. -/
lemma dist_eq_iff_dist_orthogonal_projection_eq {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p1 p2 : P} (p3 : P) (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) :
  dist p1 p3 = dist p2 p3 ↔
    dist p1 (orthogonal_projection s p3) = dist p2 (orthogonal_projection s p3) :=
begin
  rw [←mul_self_inj_of_nonneg dist_nonneg dist_nonneg,
      ←mul_self_inj_of_nonneg dist_nonneg dist_nonneg,
      dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
        p3 hp1,
      dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
        p3 hp2],
  simp
end

/-- `p` is equidistant from a set of points in `s` if and only if its
`orthogonal_projection` is. -/
lemma dist_set_eq_iff_dist_orthogonal_projection_eq {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {ps : set P} (hps : ps ⊆ s) (p : P) :
  (set.pairwise_on ps (λ p1 p2, dist p1 p = dist p2 p) ↔
    (set.pairwise_on ps (λ p1 p2, dist p1 (orthogonal_projection s p) =
      dist p2 (orthogonal_projection s p)))) :=
⟨λ h p1 hp1 p2 hp2 hne,
  (dist_eq_iff_dist_orthogonal_projection_eq p (hps hp1) (hps hp2)).1 (h p1 hp1 p2 hp2 hne),
λ h p1 hp1 p2 hp2 hne,
  (dist_eq_iff_dist_orthogonal_projection_eq p (hps hp1) (hps hp2)).2 (h p1 hp1 p2 hp2 hne)⟩

/-- There exists `r` such that `p` has distance `r` from all the
points of a set of points in `s` if and only if there exists (possibly
different) `r` such that its `orthogonal_projection` has that distance
from all the points in that set. -/
lemma exists_dist_eq_iff_exists_dist_orthogonal_projection_eq {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {ps : set P} (hps : ps ⊆ s) (p : P) :
  (∃ r, ∀ p1 ∈ ps, dist p1 p = r) ↔
    ∃ r, ∀ p1 ∈ ps, dist p1 ↑(orthogonal_projection s p) = r :=
begin
  have h := dist_set_eq_iff_dist_orthogonal_projection_eq hps p,
  simp_rw set.pairwise_on_eq_iff_exists_eq at h,
  exact h
end

/-- The induction step for the existence and uniqueness of the
circumcenter.  Given a nonempty set of points in a nonempty affine
subspace whose direction is complete, such that there is a unique
(circumcenter, circumradius) pair for those points in that subspace,
and a point `p` not in that subspace, there is a unique (circumcenter,
circumradius) pair for the set with `p` added, in the span of the
subspace with `p` added. -/
lemma exists_unique_dist_eq_of_insert {s : affine_subspace ℝ P}
  [complete_space s.direction] {ps : set P} (hnps : ps.nonempty) {p : P}
  (hps : ps ⊆ s) (hp : p ∉ s)
  (hu : ∃! cccr : (P × ℝ), cccr.fst ∈ s ∧ ∀ p1 ∈ ps, dist p1 cccr.fst = cccr.snd) :
  ∃! cccr₂ : (P × ℝ), cccr₂.fst ∈ affine_span ℝ (insert p (s : set P)) ∧
    ∀ p1 ∈ insert p ps, dist p1 cccr₂.fst = cccr₂.snd :=
begin
  haveI : nonempty s := set.nonempty.to_subtype (hnps.mono hps),
  rcases hu with ⟨⟨cc, cr⟩, ⟨hcc, hcr⟩, hcccru⟩,
  simp only [prod.fst, prod.snd] at hcc hcr hcccru,
  let x := dist cc (orthogonal_projection s p),
  let y := dist p (orthogonal_projection s p),
  have hy0 : y ≠ 0 := dist_orthogonal_projection_ne_zero_of_not_mem hp,
  let ycc₂ := (x * x + y * y - cr * cr) / (2 * y),
  let cc₂ := (ycc₂ / y) • (p -ᵥ orthogonal_projection s p : V) +ᵥ cc,
  let cr₂ := real.sqrt (cr * cr + ycc₂ * ycc₂),
  use (cc₂, cr₂),
  simp only [prod.fst, prod.snd],
  have hpo : p = (1 : ℝ) • (p -ᵥ orthogonal_projection s p : V) +ᵥ orthogonal_projection s p,
  { simp },
  split,
  { split,
    { refine vadd_mem_of_mem_direction _ (mem_affine_span ℝ (set.mem_insert_of_mem _ hcc)),
      rw direction_affine_span,
      exact submodule.smul_mem _ _
        (vsub_mem_vector_span ℝ (set.mem_insert _ _)
                                (set.mem_insert_of_mem _ (orthogonal_projection_mem _))) },
    { intros p1 hp1,
      rw [←mul_self_inj_of_nonneg dist_nonneg (real.sqrt_nonneg _),
          real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))],
      cases hp1,
      { rw hp1,
        rw [hpo,
            dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd
              (orthogonal_projection_mem p) hcc _ _
              (vsub_orthogonal_projection_mem_direction_orthogonal s p),
            ←dist_eq_norm_vsub V p, dist_comm _ cc],
        field_simp [hy0],
        ring },
      { rw [dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
               _ (hps hp1),
            orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ hcc, subtype.coe_mk,
            hcr _ hp1, dist_eq_norm_vsub V cc₂ cc, vadd_vsub, norm_smul, ←dist_eq_norm_vsub V,
            real.norm_eq_abs, abs_div, abs_of_nonneg dist_nonneg, div_mul_cancel _ hy0,
            abs_mul_abs_self] } } },
  { rintros ⟨cc₃, cr₃⟩ ⟨hcc₃, hcr₃⟩,
    simp only [prod.fst, prod.snd] at hcc₃ hcr₃,
    obtain ⟨t₃, cc₃', hcc₃', hcc₃''⟩ :
      ∃ (r : ℝ) (p0 : P) (hp0 : p0 ∈ s), cc₃ = r • (p -ᵥ ↑((orthogonal_projection s) p)) +ᵥ p0,
    { rwa mem_affine_span_insert_iff (orthogonal_projection_mem p) at hcc₃ },
    have hcr₃' : ∃ r, ∀ p1 ∈ ps, dist p1 cc₃ = r :=
      ⟨cr₃, λ p1 hp1, hcr₃ p1 (set.mem_insert_of_mem _ hp1)⟩,
    rw [exists_dist_eq_iff_exists_dist_orthogonal_projection_eq hps cc₃, hcc₃'',
      orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ hcc₃'] at hcr₃',
    cases hcr₃' with cr₃' hcr₃',
    have hu := hcccru (cc₃', cr₃'),
    simp only [prod.fst, prod.snd] at hu,
    replace hu := hu ⟨hcc₃', hcr₃'⟩,
    rw prod.ext_iff at hu,
    simp only [prod.fst, prod.snd] at hu,
    cases hu with hucc hucr,
    substs hucc hucr,
    have hcr₃val : cr₃ = real.sqrt (cr₃' * cr₃' + (t₃ * y) * (t₃ * y)),
    { cases hnps with p0 hp0,
      have h' : ↑(⟨cc₃', hcc₃'⟩ : s) = cc₃' := rfl,
      rw [←hcr₃ p0 (set.mem_insert_of_mem _ hp0), hcc₃'',
          ←mul_self_inj_of_nonneg dist_nonneg (real.sqrt_nonneg _),
          real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)),
          dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square
            _ (hps hp0),
          orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ hcc₃', h', hcr p0 hp0,
          dist_eq_norm_vsub V _ cc₃', vadd_vsub, norm_smul, ←dist_eq_norm_vsub V p,
          real.norm_eq_abs, ←mul_assoc, mul_comm _ (abs t₃), ←mul_assoc, abs_mul_abs_self],
      ring },
    replace hcr₃ := hcr₃ p (set.mem_insert _ _),
    rw [hpo, hcc₃'', hcr₃val, ←mul_self_inj_of_nonneg dist_nonneg (real.sqrt_nonneg _),
        dist_square_smul_orthogonal_vadd_smul_orthogonal_vadd
          (orthogonal_projection_mem p) hcc₃' _ _
          (vsub_orthogonal_projection_mem_direction_orthogonal s p),
        dist_comm, ←dist_eq_norm_vsub V p,
        real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))] at hcr₃,
    change x * x + _ * (y * y) = _ at hcr₃,
    rw [(show x * x + (1 - t₃) * (1 - t₃) * (y * y) =
           x * x + y * y - 2 * y * (t₃ * y) + t₃ * y * (t₃ * y), by ring), add_left_inj] at hcr₃,
    have ht₃ : t₃ = ycc₂ / y,
    { field_simp [←hcr₃, hy0],
      ring },
    subst ht₃,
    change cc₃ = cc₂ at hcc₃'',
    congr',
    rw hcr₃val,
    congr' 2,
    field_simp [hy0],
    ring }
end

/-- Given a finite nonempty affinely independent family of points,
there is a unique (circumcenter, circumradius) pair for those points
in the affine subspace they span. -/
lemma exists_unique_dist_eq_of_affine_independent {ι : Type*} [hne : nonempty ι] [fintype ι]
    {p : ι → P} (ha : affine_independent ℝ p) :
  ∃! cccr : (P × ℝ), cccr.fst ∈ affine_span ℝ (set.range p) ∧
    ∀ i, dist (p i) cccr.fst = cccr.snd :=
begin
  generalize' hn : fintype.card ι = n,
  unfreezingI { induction n with m hm generalizing ι },
  { exfalso,
    have h := fintype.card_pos_iff.2 hne,
    rw hn at h,
    exact lt_irrefl 0 h },
  { cases m,
    { rw fintype.card_eq_one_iff at hn,
      cases hn with i hi,
      haveI : unique ι := ⟨⟨i⟩, hi⟩,
      use (p i, 0),
      simp only [prod.fst, prod.snd, set.range_unique, affine_subspace.mem_affine_span_singleton],
      split,
      { simp_rw [hi (default ι)],
        use rfl,
        intro i1,
        rw hi i1,
        exact dist_self _ },
      { rintros ⟨cc, cr⟩,
        simp only [prod.fst, prod.snd],
        rintros ⟨rfl, hdist⟩,
        rw hi (default ι),
        congr',
        rw ←hdist (default ι),
        exact dist_self _ } },
    { have i := hne.some,
      let ι2 := {x // x ≠ i},
      have hc : fintype.card ι2 = m + 1,
      { rw fintype.card_of_subtype (finset.univ.filter (λ x, x ≠ i)),
        { rw finset.filter_not,
          simp_rw eq_comm,
          rw [finset.filter_eq, if_pos (finset.mem_univ _),
              finset.card_sdiff (finset.subset_univ _), finset.card_singleton, finset.card_univ,
              hn],
          simp },
        { simp } },
      haveI : nonempty ι2 := fintype.card_pos_iff.1 (hc.symm ▸ nat.zero_lt_succ _),
      have ha2 : affine_independent ℝ (λ i2 : ι2, p i2) :=
        affine_independent_subtype_of_affine_independent ha _,
      replace hm := hm ha2 hc,
      have hr : set.range p = insert (p i) (set.range (λ i2 : ι2, p i2)),
      { change _ = insert _ (set.range (λ i2 : {x | x ≠ i}, p i2)),
        rw [←set.image_eq_range, ←set.image_univ, ←set.image_insert_eq],
        congr' with j,
        simp [classical.em] },
      change ∃! (cccr : P × ℝ), (_ ∧ ∀ i2, (λ q, dist q cccr.fst = cccr.snd) (p i2)),
      conv { congr, funext, conv { congr, skip, rw ←set.forall_range_iff } },
      dsimp only,
      rw hr,
      change ∃! (cccr : P × ℝ), (_ ∧ ∀ (i2 : ι2), (λ q, dist q cccr.fst = cccr.snd) (p i2)) at hm,
      conv at hm { congr, funext, conv { congr, skip, rw ←set.forall_range_iff } },
      rw ←affine_span_insert_affine_span,
      refine exists_unique_dist_eq_of_insert
        (set.range_nonempty _)
        (subset_span_points ℝ _)
        _
        hm,
      convert not_mem_affine_span_diff_of_affine_independent ha i set.univ,
      change set.range (λ i2 : {x | x ≠ i}, p i2) = _,
      rw ←set.image_eq_range,
      congr' with j, simp, refl } }
end

end euclidean_geometry

namespace affine

namespace simplex

open finset affine_subspace euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P]
include V

/-- The pair (circumcenter, circumradius) of a simplex. -/
def circumcenter_circumradius {n : ℕ} (s : simplex ℝ P n) : (P × ℝ) :=
(exists_unique_dist_eq_of_affine_independent s.independent).some

/-- The property satisfied by the (circumcenter, circumradius) pair. -/
lemma circumcenter_circumradius_unique_dist_eq {n : ℕ} (s : simplex ℝ P n) :
  (s.circumcenter_circumradius.fst ∈ affine_span ℝ (set.range s.points) ∧
    ∀ i, dist (s.points i) s.circumcenter_circumradius.fst = s.circumcenter_circumradius.snd) ∧
  (∀ cccr : (P × ℝ), (cccr.fst ∈ affine_span ℝ (set.range s.points) ∧
    ∀ i, dist (s.points i) cccr.fst = cccr.snd) → cccr = s.circumcenter_circumradius) :=
(exists_unique_dist_eq_of_affine_independent s.independent).some_spec

/-- The circumcenter of a simplex. -/
def circumcenter {n : ℕ} (s : simplex ℝ P n) : P :=
s.circumcenter_circumradius.fst

/-- The circumradius of a simplex. -/
def circumradius {n : ℕ} (s : simplex ℝ P n) : ℝ :=
s.circumcenter_circumradius.snd

/-- The circumcenter lies in the affine span. -/
lemma circumcenter_mem_affine_span {n : ℕ} (s : simplex ℝ P n) :
  s.circumcenter ∈ affine_span ℝ (set.range s.points) :=
s.circumcenter_circumradius_unique_dist_eq.1.1

/-- All points have distance from the circumcenter equal to the
circumradius. -/
@[simp] lemma dist_circumcenter_eq_circumradius {n : ℕ} (s : simplex ℝ P n) :
  ∀ i, dist (s.points i) s.circumcenter = s.circumradius :=
s.circumcenter_circumradius_unique_dist_eq.1.2

/-- All points have distance to the circumcenter equal to the
circumradius. -/
@[simp] lemma dist_circumcenter_eq_circumradius' {n : ℕ} (s : simplex ℝ P n) :
  ∀ i, dist s.circumcenter (s.points i) = s.circumradius :=
begin
  intro i,
  rw dist_comm,
  exact dist_circumcenter_eq_circumradius _ _
end

/-- Given a point in the affine span from which all the points are
equidistant, that point is the circumcenter. -/
lemma eq_circumcenter_of_dist_eq {n : ℕ} (s : simplex ℝ P n) {p : P}
    (hp : p ∈ affine_span ℝ (set.range s.points)) {r : ℝ} (hr : ∀ i, dist (s.points i) p = r) :
  p = s.circumcenter :=
begin
  have h := s.circumcenter_circumradius_unique_dist_eq.2 (p, r),
  simp only [hp, hr, forall_const, eq_self_iff_true, and_self, prod.ext_iff] at h,
  exact h.1
end

/-- Given a point in the affine span from which all the points are
equidistant, that distance is the circumradius. -/
lemma eq_circumradius_of_dist_eq {n : ℕ} (s : simplex ℝ P n) {p : P}
    (hp : p ∈ affine_span ℝ (set.range s.points)) {r : ℝ} (hr : ∀ i, dist (s.points i) p = r) :
  r = s.circumradius :=
begin
  have h := s.circumcenter_circumradius_unique_dist_eq.2 (p, r),
  simp only [hp, hr, forall_const, eq_self_iff_true, and_self, prod.ext_iff] at h,
  exact h.2
end

/-- The circumradius is non-negative. -/
lemma circumradius_nonneg {n : ℕ} (s : simplex ℝ P n) : 0 ≤ s.circumradius :=
s.dist_circumcenter_eq_circumradius 0 ▸ dist_nonneg

/-- The circumradius of a simplex with at least two points is
positive. -/
lemma circumradius_pos {n : ℕ} (s : simplex ℝ P (n + 1)) : 0 < s.circumradius :=
begin
  refine lt_of_le_of_ne s.circumradius_nonneg _,
  intro h,
  have hr := s.dist_circumcenter_eq_circumradius,
  simp_rw [←h, dist_eq_zero] at hr,
  have h01 := (injective_of_affine_independent s.independent).ne
    (dec_trivial : (0 : fin (n + 2)) ≠ 1),
  simpa [hr] using h01
end

/-- The circumcenter of a 0-simplex equals its unique point. -/
lemma circumcenter_eq_point (s : simplex ℝ P 0) (i : fin 1) :
  s.circumcenter = s.points i :=
begin
  have h := s.circumcenter_mem_affine_span,
  rw [set.range_unique, mem_affine_span_singleton] at h,
  rw h,
  congr
end

/-- The circumcenter of a 1-simplex equals its centroid. -/
lemma circumcenter_eq_centroid (s : simplex ℝ P 1) :
  s.circumcenter = finset.univ.centroid ℝ s.points :=
begin
  have hr : set.pairwise_on set.univ
    (λ i j : fin 2, dist (s.points i) (finset.univ.centroid ℝ s.points) =
                    dist (s.points j) (finset.univ.centroid ℝ s.points)),
  { intros i hi j hj hij,
    rw [finset.centroid_insert_singleton_fin, dist_eq_norm_vsub V (s.points i),
        dist_eq_norm_vsub V (s.points j), vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub,
        ←one_smul ℝ (s.points i -ᵥ s.points 0), ←one_smul ℝ (s.points j -ᵥ s.points 0)],
    fin_cases i; fin_cases j; simp [-one_smul, ←sub_smul]; norm_num },
  rw set.pairwise_on_eq_iff_exists_eq at hr,
  cases hr with r hr,
  exact (s.eq_circumcenter_of_dist_eq
          (centroid_mem_affine_span_of_card_eq_add_one ℝ _ (finset.card_fin 2))
          (λ i, hr i (set.mem_univ _))).symm
end

/-- If there exists a distance that a point has from all vertices of a
simplex, the orthogonal projection of that point onto the subspace
spanned by that simplex is its circumcenter.  -/
lemma orthogonal_projection_eq_circumcenter_of_exists_dist_eq {n : ℕ} (s : simplex ℝ P n)
  {p : P} (hr : ∃ r, ∀ i, dist (s.points i) p = r) :
  ↑(orthogonal_projection (affine_span ℝ (set.range s.points)) p) = s.circumcenter :=
begin
  change ∃ r : ℝ, ∀ i, (λ x, dist x p = r) (s.points i) at hr,
  conv at hr { congr, funext, rw ←set.forall_range_iff },
  rw exists_dist_eq_iff_exists_dist_orthogonal_projection_eq (subset_affine_span ℝ _) p at hr,
  cases hr with r hr,
  exact s.eq_circumcenter_of_dist_eq
    (orthogonal_projection_mem p) (λ i, hr _ (set.mem_range_self i)),
end

/-- If a point has the same distance from all vertices of a simplex,
the orthogonal projection of that point onto the subspace spanned by
that simplex is its circumcenter.  -/
lemma orthogonal_projection_eq_circumcenter_of_dist_eq {n : ℕ} (s : simplex ℝ P n) {p : P}
  {r : ℝ} (hr : ∀ i, dist (s.points i) p = r) :
  ↑(orthogonal_projection (affine_span ℝ (set.range s.points)) p) = s.circumcenter :=
s.orthogonal_projection_eq_circumcenter_of_exists_dist_eq ⟨r, hr⟩

/-- The orthogonal projection of the circumcenter onto a face is the
circumcenter of that face. -/
lemma orthogonal_projection_circumcenter {n : ℕ} (s : simplex ℝ P n) {fs : finset (fin (n + 1))}
  {m : ℕ} (h : fs.card = m + 1) :
  ↑(orthogonal_projection (affine_span ℝ (set.range (s.face h).points)) s.circumcenter) =
    (s.face h).circumcenter :=
begin
  have hr : ∃ r, ∀ i, dist ((s.face h).points i) s.circumcenter = r,
  { use s.circumradius,
    simp [face_points] },
  exact orthogonal_projection_eq_circumcenter_of_exists_dist_eq _ hr
end

/-- Two simplices with the same points have the same circumcenter. -/
lemma circumcenter_eq_of_range_eq {n : ℕ} {s₁ s₂ : simplex ℝ P n}
  (h : set.range s₁.points = set.range s₂.points) : s₁.circumcenter = s₂.circumcenter :=
begin
  have hs : s₁.circumcenter ∈ affine_span ℝ (set.range s₂.points) :=
    h ▸ s₁.circumcenter_mem_affine_span,
  have hr : ∀ i, dist (s₂.points i) s₁.circumcenter = s₁.circumradius,
  { intro i,
    have hi : s₂.points i ∈ set.range s₂.points := set.mem_range_self _,
    rw [←h, set.mem_range] at hi,
    rcases hi with ⟨j, hj⟩,
    rw [←hj, s₁.dist_circumcenter_eq_circumradius j] },
  exact s₂.eq_circumcenter_of_dist_eq hs hr
end

omit V

/-- An index type for the vertices of a simplex plus its circumcenter.
This is for use in calculations where it is convenient to work with
affine combinations of vertices together with the circumcenter.  (An
equivalent form sometimes used in the literature is placing the
circumcenter at the origin and working with vectors for the vertices.) -/
@[derive fintype]
inductive points_with_circumcenter_index (n : ℕ)
| point_index : fin (n + 1) → points_with_circumcenter_index
| circumcenter_index : points_with_circumcenter_index

open points_with_circumcenter_index

instance points_with_circumcenter_index_inhabited (n : ℕ) :
  inhabited (points_with_circumcenter_index n) :=
⟨circumcenter_index⟩

/-- `point_index` as an embedding. -/
def point_index_embedding (n : ℕ) : fin (n + 1) ↪ points_with_circumcenter_index n :=
⟨λ i, point_index i, λ _ _ h, by injection h⟩

/-- The sum of a function over `points_with_circumcenter_index`. -/
lemma sum_points_with_circumcenter {α : Type*} [add_comm_monoid α] {n : ℕ}
  (f : points_with_circumcenter_index n → α) :
  ∑ i, f i = (∑ (i : fin (n + 1)), f (point_index i)) + f circumcenter_index :=
begin
  have h : univ = insert circumcenter_index (univ.map (point_index_embedding n)),
  { ext x,
    refine ⟨λ h, _, λ _, mem_univ _⟩,
    cases x with i,
    { exact mem_insert_of_mem (mem_map_of_mem _ (mem_univ i)) },
    { exact mem_insert_self _ _ } },
  change _ = ∑ i, f (point_index_embedding n i) + _,
  rw [add_comm, h, ←sum_map, sum_insert],
  simp_rw [mem_map, not_exists],
  intros x hx h,
  injection h
end

include V

/-- The vertices of a simplex plus its circumcenter. -/
def points_with_circumcenter {n : ℕ} (s : simplex ℝ P n) : points_with_circumcenter_index n → P
| (point_index i) := s.points i
| circumcenter_index := s.circumcenter

/-- `points_with_circumcenter`, applied to a `point_index` value,
equals `points` applied to that value. -/
@[simp] lemma points_with_circumcenter_point {n : ℕ} (s : simplex ℝ P n) (i : fin (n + 1)) :
  s.points_with_circumcenter (point_index i) = s.points i :=
rfl

/-- `points_with_circumcenter`, applied to `circumcenter_index`, equals the
circumcenter. -/
@[simp] lemma points_with_circumcenter_eq_circumcenter {n : ℕ} (s : simplex ℝ P n) :
  s.points_with_circumcenter circumcenter_index = s.circumcenter :=
rfl

omit V

/-- The weights for a single vertex of a simplex, in terms of
`points_with_circumcenter`. -/
def point_weights_with_circumcenter {n : ℕ} (i : fin (n + 1)) : points_with_circumcenter_index n → ℝ
| (point_index j) := if j = i then 1 else 0
| circumcenter_index := 0

/-- `point_weights_with_circumcenter` sums to 1. -/
@[simp] lemma sum_point_weights_with_circumcenter {n : ℕ} (i : fin (n + 1)) :
  ∑ j, point_weights_with_circumcenter i j = 1 :=
begin
  convert sum_ite_eq' univ (point_index i) (function.const _ (1 : ℝ)),
  { ext j,
    cases j ; simp [point_weights_with_circumcenter] },
  { simp }
end

include V

/-- A single vertex, in terms of `points_with_circumcenter`. -/
lemma point_eq_affine_combination_of_points_with_circumcenter {n : ℕ} (s : simplex ℝ P n)
  (i : fin (n + 1)) :
  s.points i =
    (univ : finset (points_with_circumcenter_index n)).affine_combination
      s.points_with_circumcenter (point_weights_with_circumcenter i) :=
begin
  rw ←points_with_circumcenter_point,
  symmetry,
  refine affine_combination_of_eq_one_of_eq_zero _ _ _
    (mem_univ _)
    (by simp [point_weights_with_circumcenter])
    _,
  intros i hi hn,
  cases i,
  { have h : i_1 ≠ i := λ h, hn (h ▸ rfl),
    simp [point_weights_with_circumcenter, h] },
  { refl }
end

omit V

/-- The weights for the centroid of some vertices of a simplex, in
terms of `points_with_circumcenter`. -/
def centroid_weights_with_circumcenter {n : ℕ} (fs : finset (fin (n + 1)))
  : points_with_circumcenter_index n → ℝ
| (point_index i) := if i ∈ fs then ((card fs : ℝ) ⁻¹) else 0
| circumcenter_index := 0

/-- `centroid_weights_with_circumcenter` sums to 1, if the `finset` is
nonempty. -/
@[simp] lemma sum_centroid_weights_with_circumcenter {n : ℕ} {fs : finset (fin (n + 1))} (h : fs.nonempty) :
  ∑ i, centroid_weights_with_circumcenter fs i = 1 :=
begin
  simp_rw [sum_points_with_circumcenter, centroid_weights_with_circumcenter, add_zero,
           ←fs.sum_centroid_weights_eq_one_of_nonempty ℝ h,
           set.sum_indicator_subset _ fs.subset_univ],
  rcongr
end

include V

/-- The centroid of some vertices of a simplex, in terms of
`points_with_circumcenter`. -/
lemma centroid_eq_affine_combination_of_points_with_circumcenter {n : ℕ} (s : simplex ℝ P n)
  (fs : finset (fin (n + 1))) :
  fs.centroid ℝ s.points =
    (univ : finset (points_with_circumcenter_index n)).affine_combination
      s.points_with_circumcenter (centroid_weights_with_circumcenter fs) :=
begin
  simp_rw [centroid_def, affine_combination_apply,
           weighted_vsub_of_point_apply, sum_points_with_circumcenter,
           centroid_weights_with_circumcenter, points_with_circumcenter_point, zero_smul,
           add_zero, centroid_weights,
           set.sum_indicator_subset_of_eq_zero
             (function.const (fin (n + 1)) ((card fs : ℝ)⁻¹))
             (λ i wi, wi • (s.points i -ᵥ classical.choice add_torsor.nonempty))
             fs.subset_univ
             (λ i, zero_smul ℝ _),
           set.indicator_apply],
  rcongr
end

omit V

/-- The weights for the circumcenter of a simplex, in terms of
`points_with_circumcenter`. -/
def circumcenter_weights_with_circumcenter (n : ℕ) : points_with_circumcenter_index n → ℝ
| (point_index i) := 0
| circumcenter_index := 1

/-- `circumcenter_weights_with_circumcenter` sums to 1. -/
@[simp] lemma sum_circumcenter_weights_with_circumcenter (n : ℕ) :
  ∑ i, circumcenter_weights_with_circumcenter n i = 1 :=
begin
  convert sum_ite_eq' univ circumcenter_index (function.const _ (1 : ℝ)),
  { ext ⟨j⟩ ; simp [circumcenter_weights_with_circumcenter] },
  { simp },
  { exact classical.dec_eq _ }
end

include V

/-- The circumcenter of a simplex, in terms of
`points_with_circumcenter`. -/
lemma circumcenter_eq_affine_combination_of_points_with_circumcenter {n : ℕ}
  (s : simplex ℝ P n) :
  s.circumcenter = (univ : finset (points_with_circumcenter_index n)).affine_combination
    s.points_with_circumcenter (circumcenter_weights_with_circumcenter n) :=
begin
  rw ←points_with_circumcenter_eq_circumcenter,
  symmetry,
  refine affine_combination_of_eq_one_of_eq_zero _ _ _ (mem_univ _) rfl _,
  rintros ⟨i⟩ hi hn ; tauto
end

omit V

/-- The weights for the reflection of the circumcenter in an edge of a
simplex.  This definition is only valid with `i₁ ≠ i₂`. -/
def reflection_circumcenter_weights_with_circumcenter {n : ℕ} (i₁ i₂ : fin (n + 1)) :
  points_with_circumcenter_index n → ℝ
| (point_index i) := if i = i₁ ∨ i = i₂ then 1 else 0
| circumcenter_index := -1

/-- `reflection_circumcenter_weights_with_circumcenter` sums to 1. -/
@[simp] lemma sum_reflection_circumcenter_weights_with_circumcenter {n : ℕ} {i₁ i₂ : fin (n + 1)}
  (h : i₁ ≠ i₂) : ∑ i, reflection_circumcenter_weights_with_circumcenter i₁ i₂ i = 1 :=
begin
  simp_rw [sum_points_with_circumcenter, reflection_circumcenter_weights_with_circumcenter,
           sum_ite, sum_const, filter_or, filter_eq'],
  rw card_union_eq,
  { simp },
  { simp [h.symm] }
end

include V

/-- The reflection of the circumcenter of a simplex in an edge, in
terms of `points_with_circumcenter`. -/
lemma reflection_circumcenter_eq_affine_combination_of_points_with_circumcenter {n : ℕ}
  (s : simplex ℝ P n) {i₁ i₂ : fin (n + 1)} (h : i₁ ≠ i₂) :
  reflection (affine_span ℝ (s.points '' {i₁, i₂})) s.circumcenter =
    (univ : finset (points_with_circumcenter_index n)).affine_combination
      s.points_with_circumcenter (reflection_circumcenter_weights_with_circumcenter i₁ i₂) :=
begin
  have hc : card ({i₁, i₂} : finset (fin (n + 1))) = 2,
  { simp [h] },
  have h_faces : ↑(orthogonal_projection (affine_span ℝ (s.points '' {i₁, i₂})) s.circumcenter)
    = ↑(orthogonal_projection (affine_span ℝ (set.range (s.face hc).points)) s.circumcenter),
  { apply eq_orthogonal_projection_of_eq_subspace,
    simp },
  rw [reflection_apply, h_faces, s.orthogonal_projection_circumcenter hc, circumcenter_eq_centroid,
      s.face_centroid_eq_centroid hc, centroid_eq_affine_combination_of_points_with_circumcenter,
      circumcenter_eq_affine_combination_of_points_with_circumcenter, ←@vsub_eq_zero_iff_eq V,
      affine_combination_vsub, weighted_vsub_vadd_affine_combination, affine_combination_vsub,
      weighted_vsub_apply, sum_points_with_circumcenter],
  simp_rw [pi.sub_apply, pi.add_apply, pi.sub_apply, sub_smul, add_smul, sub_smul,
           centroid_weights_with_circumcenter, circumcenter_weights_with_circumcenter,
           reflection_circumcenter_weights_with_circumcenter, ite_smul, zero_smul, sub_zero,
           apply_ite2 (+), add_zero, ←add_smul, hc, zero_sub, neg_smul, sub_self, add_zero],
  convert sum_const_zero,
  norm_num
end

end simplex

end affine

namespace euclidean_geometry

open affine affine_subspace finite_dimensional

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P]
include V

/-- Given a nonempty affine subspace, whose direction is complete,
that contains a set of points, those points are cospherical if and
only if they are equidistant from some point in that subspace. -/
lemma cospherical_iff_exists_mem_of_complete {s : affine_subspace ℝ P} {ps : set P} (h : ps ⊆ s)
  [nonempty s] [complete_space s.direction] :
  cospherical ps ↔ ∃ (center ∈ s) (radius : ℝ), ∀ p ∈ ps, dist p center = radius :=
begin
  split,
  { rintro ⟨c, hcr⟩,
    rw exists_dist_eq_iff_exists_dist_orthogonal_projection_eq h c at hcr,
    exact ⟨orthogonal_projection s c, orthogonal_projection_mem _, hcr⟩ },
  { exact λ ⟨c, hc, hd⟩, ⟨c, hd⟩ }
end

/-- Given a nonempty affine subspace, whose direction is
finite-dimensional, that contains a set of points, those points are
cospherical if and only if they are equidistant from some point in
that subspace. -/
lemma cospherical_iff_exists_mem_of_finite_dimensional {s : affine_subspace ℝ P} {ps : set P}
  (h : ps ⊆ s) [nonempty s] [finite_dimensional ℝ s.direction] :
  cospherical ps ↔ ∃ (center ∈ s) (radius : ℝ), ∀ p ∈ ps, dist p center = radius :=
cospherical_iff_exists_mem_of_complete h

/-- All n-simplices among cospherical points in an n-dimensional
subspace have the same circumradius. -/
lemma exists_circumradius_eq_of_cospherical_subset {s : affine_subspace ℝ P} {ps : set P}
  (h : ps ⊆ s) [nonempty s] {n : ℕ} [finite_dimensional ℝ s.direction]
  (hd : findim ℝ s.direction = n) (hc : cospherical ps) :
  ∃ r : ℝ, ∀ sx : simplex ℝ P n, set.range sx.points ⊆ ps → sx.circumradius = r :=
begin
  rw cospherical_iff_exists_mem_of_finite_dimensional h at hc,
  rcases hc with ⟨c, hc, r, hcr⟩,
  use r,
  intros sx hsxps,
  have hsx : affine_span ℝ (set.range sx.points) = s,
  { refine affine_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one sx.independent
      (span_points_subset_coe_of_subset_coe (set.subset.trans hsxps h)) _,
    simp [hd] },
  have hc : c ∈ affine_span ℝ (set.range sx.points) := hsx.symm ▸ hc,
  exact (sx.eq_circumradius_of_dist_eq
    hc
    (λ i, hcr (sx.points i) (hsxps (set.mem_range_self i)))).symm
end

/-- Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumradius. -/
lemma circumradius_eq_of_cospherical_subset {s : affine_subspace ℝ P} {ps : set P}
  (h : ps ⊆ s) [nonempty s] {n : ℕ} [finite_dimensional ℝ s.direction]
  (hd : findim ℝ s.direction = n) (hc : cospherical ps) {sx₁ sx₂ : simplex ℝ P n}
  (hsx₁ : set.range sx₁.points ⊆ ps) (hsx₂ : set.range sx₂.points ⊆ ps) :
  sx₁.circumradius = sx₂.circumradius :=
begin
  rcases exists_circumradius_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩,
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]
end

/-- All n-simplices among cospherical points in n-space have the same
circumradius. -/
lemma exists_circumradius_eq_of_cospherical {ps : set P} {n : ℕ} [finite_dimensional ℝ V]
  (hd : findim ℝ V = n) (hc : cospherical ps) :
  ∃ r : ℝ, ∀ sx : simplex ℝ P n, set.range sx.points ⊆ ps → sx.circumradius = r :=
begin
  haveI : nonempty (⊤ : affine_subspace ℝ P) := set.univ.nonempty,
  rw [←findim_top, ←direction_top ℝ V P] at hd,
  refine exists_circumradius_eq_of_cospherical_subset _ hd hc,
  exact set.subset_univ _
end

/-- Two n-simplices among cospherical points in n-space have the same
circumradius. -/
lemma circumradius_eq_of_cospherical {ps : set P} {n : ℕ} [finite_dimensional ℝ V]
  (hd : findim ℝ V = n) (hc : cospherical ps) {sx₁ sx₂ : simplex ℝ P n}
  (hsx₁ : set.range sx₁.points ⊆ ps) (hsx₂ : set.range sx₂.points ⊆ ps) :
  sx₁.circumradius = sx₂.circumradius :=
begin
  rcases exists_circumradius_eq_of_cospherical hd hc with ⟨r, hr⟩,
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]
end

/-- All n-simplices among cospherical points in an n-dimensional
subspace have the same circumcenter. -/
lemma exists_circumcenter_eq_of_cospherical_subset {s : affine_subspace ℝ P} {ps : set P}
  (h : ps ⊆ s) [nonempty s] {n : ℕ} [finite_dimensional ℝ s.direction]
  (hd : findim ℝ s.direction = n) (hc : cospherical ps) :
  ∃ c : P, ∀ sx : simplex ℝ P n, set.range sx.points ⊆ ps → sx.circumcenter = c :=
begin
  rw cospherical_iff_exists_mem_of_finite_dimensional h at hc,
  rcases hc with ⟨c, hc, r, hcr⟩,
  use c,
  intros sx hsxps,
  have hsx : affine_span ℝ (set.range sx.points) = s,
  { refine affine_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one sx.independent
      (span_points_subset_coe_of_subset_coe (set.subset.trans hsxps h)) _,
    simp [hd] },
  have hc : c ∈ affine_span ℝ (set.range sx.points) := hsx.symm ▸ hc,
  exact (sx.eq_circumcenter_of_dist_eq
    hc
    (λ i, hcr (sx.points i) (hsxps (set.mem_range_self i)))).symm
end

/-- Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumcenter. -/
lemma circumcenter_eq_of_cospherical_subset {s : affine_subspace ℝ P} {ps : set P}
  (h : ps ⊆ s) [nonempty s] {n : ℕ} [finite_dimensional ℝ s.direction]
  (hd : findim ℝ s.direction = n) (hc : cospherical ps) {sx₁ sx₂ : simplex ℝ P n}
  (hsx₁ : set.range sx₁.points ⊆ ps) (hsx₂ : set.range sx₂.points ⊆ ps) :
  sx₁.circumcenter = sx₂.circumcenter :=
begin
  rcases exists_circumcenter_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩,
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]
end

/-- All n-simplices among cospherical points in n-space have the same
circumcenter. -/
lemma exists_circumcenter_eq_of_cospherical {ps : set P} {n : ℕ} [finite_dimensional ℝ V]
  (hd : findim ℝ V = n) (hc : cospherical ps) :
  ∃ c : P, ∀ sx : simplex ℝ P n, set.range sx.points ⊆ ps → sx.circumcenter = c :=
begin
  haveI : nonempty (⊤ : affine_subspace ℝ P) := set.univ.nonempty,
  rw [←findim_top, ←direction_top ℝ V P] at hd,
  refine exists_circumcenter_eq_of_cospherical_subset _ hd hc,
  exact set.subset_univ _
end

/-- Two n-simplices among cospherical points in n-space have the same
circumcenter. -/
lemma circumcenter_eq_of_cospherical {ps : set P} {n : ℕ} [finite_dimensional ℝ V]
  (hd : findim ℝ V = n) (hc : cospherical ps) {sx₁ sx₂ : simplex ℝ P n}
  (hsx₁ : set.range sx₁.points ⊆ ps) (hsx₂ : set.range sx₂.points ⊆ ps) :
  sx₁.circumcenter = sx₂.circumcenter :=
begin
  rcases exists_circumcenter_eq_of_cospherical hd hc with ⟨r, hr⟩,
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]
end

/-- Suppose all distances from `p₁` and `p₂` to the points of a
simplex are equal, and that `p₁` and `p₂` lie in the affine span of
`p` with the vertices of that simplex.  Then `p₁` and `p₂` are equal
or reflections of each other in the affine span of the vertices of the
simplex. -/
lemma eq_or_eq_reflection_of_dist_eq {n : ℕ} {s : simplex ℝ P n} {p p₁ p₂ : P} {r : ℝ}
    (hp₁ : p₁ ∈ affine_span ℝ (insert p (set.range s.points)))
    (hp₂ : p₂ ∈ affine_span ℝ (insert p (set.range s.points)))
    (h₁ : ∀ i, dist (s.points i) p₁ = r) (h₂ : ∀ i, dist (s.points i) p₂ = r) :
  p₁ = p₂ ∨ p₁ = reflection (affine_span ℝ (set.range s.points)) p₂ :=
begin
  let span_s := affine_span ℝ (set.range s.points),
  have h₁' := s.orthogonal_projection_eq_circumcenter_of_dist_eq h₁,
  have h₂' := s.orthogonal_projection_eq_circumcenter_of_dist_eq h₂,
  have hn : (span_s : set P).nonempty := (affine_span_nonempty ℝ _).2 (set.range_nonempty _),
  have hc : is_complete (span_s.direction : set V) := submodule.complete_of_finite_dimensional _,
  rw [←affine_span_insert_affine_span,
      mem_affine_span_insert_iff (orthogonal_projection_mem p)] at hp₁ hp₂,
  obtain ⟨r₁, p₁o, hp₁o, hp₁⟩ := hp₁,
  obtain ⟨r₂, p₂o, hp₂o, hp₂⟩ := hp₂,
  obtain rfl : ↑(orthogonal_projection span_s p₁) = p₁o,
  { have := orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ hp₁o,
    rw ← hp₁ at this,
    rw this,
    refl },
  rw h₁' at hp₁,
  obtain rfl : ↑(orthogonal_projection span_s p₂) = p₂o,
  { have := orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ hp₂o,
    rw ← hp₂ at this,
    rw this,
    refl },
  rw h₂' at hp₂,
  have h : s.points 0 ∈ span_s := mem_affine_span ℝ (set.mem_range_self _),
  have hd₁ : dist p₁ s.circumcenter * dist p₁ s.circumcenter =
    r * r - s.circumradius * s.circumradius,
  { rw [dist_comm, ←h₁ 0,
        dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square p₁ h],
    simp [h₁', dist_comm p₁] },
  have hd₂ : dist p₂ s.circumcenter * dist p₂ s.circumcenter =
    r * r - s.circumradius * s.circumradius,
  { rw [dist_comm, ←h₂ 0,
        dist_square_eq_dist_orthogonal_projection_square_add_dist_orthogonal_projection_square p₂ h],
    simp [h₂', dist_comm p₂] },
  rw [←hd₂, hp₁, hp₂, dist_eq_norm_vsub V _ s.circumcenter,
      dist_eq_norm_vsub V _ s.circumcenter, vadd_vsub, vadd_vsub, ←real_inner_self_eq_norm_square,
      ←real_inner_self_eq_norm_square, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_right, ←mul_assoc, ←mul_assoc] at hd₁,
  by_cases hp : p = orthogonal_projection span_s p,
  { rw [hp₁, hp₂, ←hp],
    simp },
  { have hz : ⟪p -ᵥ orthogonal_projection span_s p, p -ᵥ orthogonal_projection span_s p⟫ ≠ 0,
    { simpa using hp },
    rw [mul_left_inj' hz, mul_self_eq_mul_self_iff] at hd₁,
    rw [hp₁, hp₂],
    cases hd₁,
    { left,
      rw hd₁ },
    { right,
      rw [hd₁,
          reflection_vadd_smul_vsub_orthogonal_projection p r₂ s.circumcenter_mem_affine_span,
          neg_smul] } }
end

end euclidean_geometry
