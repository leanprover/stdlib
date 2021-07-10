/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/
import analysis.convex.basic
import analysis.normed_space.finite_dimension
import topology.path_connected

/-!
# Topological and metric properties of convex sets

We prove the following facts:

* `convex.interior` : interior of a convex set is convex;
* `convex.closure` : closure of a convex set is convex;
* `set.finite.compact_convex_hull` : convex hull of a finite set is compact;
* `set.finite.is_closed_convex_hull` : convex hull of a finite set is closed;
* `convex_on_dist` : distance to a fixed point is convex on any convex set;
* `convex_hull_ediam`, `convex_hull_diam` : convex hull of a set has the same (e)metric diameter
  as the original set;
* `bounded_convex_hull` : convex hull of a set is bounded if and only if the original set
  is bounded.
* `bounded_std_simplex`, `is_closed_std_simplex`, `compact_std_simplex`: topological properties
  of the standard simplex;
-/

variables {ι : Type*} {E : Type*}

open set

lemma real.convex_iff_is_preconnected {s : set ℝ} : convex s ↔ is_preconnected s :=
real.convex_iff_ord_connected.trans is_preconnected_iff_ord_connected.symm

alias real.convex_iff_is_preconnected ↔ convex.is_preconnected is_preconnected.convex

/-! ### Standard simplex -/

section std_simplex

variables [fintype ι]

/-- Every vector in `std_simplex ι` has `max`-norm at most `1`. -/
lemma std_simplex_subset_closed_ball :
  std_simplex ι ⊆ metric.closed_ball 0 1 :=
begin
  assume f hf,
  rw [metric.mem_closed_ball, dist_zero_right],
  refine (nnreal.coe_one ▸ nnreal.coe_le_coe.2 $ finset.sup_le $ λ x hx, _),
  change abs (f x) ≤ 1,
  rw [abs_of_nonneg $ hf.1 x],
  exact (mem_Icc_of_mem_std_simplex hf x).2
end

variable (ι)

/-- `std_simplex ι` is bounded. -/
lemma bounded_std_simplex : metric.bounded (std_simplex ι) :=
(metric.bounded_iff_subset_ball 0).2 ⟨1, std_simplex_subset_closed_ball⟩

/-- `std_simplex ι` is closed. -/
lemma is_closed_std_simplex : is_closed (std_simplex ι) :=
(std_simplex_eq_inter ι).symm ▸ is_closed.inter
  (is_closed_Inter $ λ i, is_closed_le continuous_const (continuous_apply i))
  (is_closed_eq (continuous_finset_sum _ $ λ x _, continuous_apply x) continuous_const)

/-- `std_simplex ι` is compact. -/
lemma compact_std_simplex : is_compact (std_simplex ι) :=
metric.compact_iff_closed_bounded.2 ⟨is_closed_std_simplex ι, bounded_std_simplex ι⟩

end std_simplex

/-! ### Topological vector space -/

section has_continuous_smul

variables [add_comm_group E] [module ℝ E] [topological_space E]
  [topological_add_group E] [has_continuous_smul ℝ E]

/-- In a topological vector space, the interior of a convex set is convex. -/
lemma convex.interior {s : set E} (hs : convex s) : convex (interior s) :=
convex_iff_pointwise_add_subset.mpr $ λ a b ha hb hab,
  have h : is_open (a • interior s + b • interior s), from
  or.elim (classical.em (a = 0))
  (λ heq,
    have hne : b ≠ 0, by { rw [heq, zero_add] at hab, rw hab, exact one_ne_zero },
    by { rw ← image_smul,
         exact (is_open_map_smul' hne _ is_open_interior).add_left } )
  (λ hne,
    by { rw ← image_smul,
         exact (is_open_map_smul' hne _ is_open_interior).add_right }),
  (subset_interior_iff_subset_of_open h).mpr $ subset.trans
    (by { simp only [← image_smul], apply add_subset_add; exact image_subset _ interior_subset })
    (convex_iff_pointwise_add_subset.mp hs ha hb hab)

/-- In a topological vector space, the closure of a convex set is convex. -/
lemma convex.closure {s : set E} (hs : convex s) : convex (closure s) :=
λ x y hx hy a b ha hb hab,
let f : E → E → E := λ x' y', a • x' + b • y' in
have hf : continuous (λ p : E × E, f p.1 p.2), from
  (continuous_const.smul continuous_fst).add (continuous_const.smul continuous_snd),
show f x y ∈ closure s, from
  mem_closure_of_continuous2 hf hx hy (λ x' hx' y' hy', subset_closure
  (hs hx' hy' ha hb hab))

/-- Convex hull of a finite set is compact. -/
lemma set.finite.compact_convex_hull {s : set E} (hs : finite s) :
  is_compact (convex_hull s) :=
begin
  rw [hs.convex_hull_eq_image],
  apply (compact_std_simplex _).image,
  haveI := hs.fintype,
  apply linear_map.continuous_on_pi
end

/-- Convex hull of a finite set is closed. -/
lemma set.finite.is_closed_convex_hull [t2_space E] {s : set E} (hs : finite s) :
  is_closed (convex_hull s) :=
hs.compact_convex_hull.is_closed

/-- If `x ∈ s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`. -/
lemma convex.add_smul_sub_mem_interior {s : set E} (hs : convex s)
  {x y : E} (hx : x ∈ s) (hy : y ∈ interior s) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
  x + t • (y - x) ∈ interior s :=
begin
  let f := λ z, x + t • (z - x),
  have : is_open_map f := (is_open_map_add_left _).comp
    ((is_open_map_smul (units.mk0 _ ht.1.ne')).comp (is_open_map_sub_right _)),
  apply mem_interior.2 ⟨f '' (interior s), _, this _ is_open_interior, mem_image_of_mem _ hy⟩,
  refine image_subset_iff.2 (λ z hz, _),
  exact hs.add_smul_sub_mem hx (interior_subset hz) ⟨ht.1.le, ht.2⟩,
end

/-- If `x ∈ s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
lemma convex.add_smul_mem_interior {s : set E} (hs : convex s)
  {x y : E} (hx : x ∈ s) (hy : x + y ∈ interior s) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
  x + t • y ∈ interior s :=
by { convert hs.add_smul_sub_mem_interior hx hy ht, abel }

end has_continuous_smul

/-! ### Normed vector space -/

section normed_space
variables [normed_group E] [normed_space ℝ E]

lemma convex_on_dist (z : E) (s : set E) (hs : convex s) :
  convex_on s (λz', dist z' z) :=
and.intro hs $
assume x y hx hy a b ha hb hab,
calc
  dist (a • x + b • y) z = ∥ (a • x + b • y) - (a + b) • z ∥ :
    by rw [hab, one_smul, normed_group.dist_eq]
  ... = ∥a • (x - z) + b • (y - z)∥ :
    by rw [add_smul, smul_sub, smul_sub, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add,
           ←add_assoc, add_assoc (a • x), add_comm (b • y)]; simp only [add_assoc]
  ... ≤ ∥a • (x - z)∥ + ∥b • (y - z)∥ :
    norm_add_le (a • (x - z)) (b • (y - z))
  ... = a * dist x z + b * dist y z :
    by simp [norm_smul, normed_group.dist_eq, real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]

lemma convex_ball (a : E) (r : ℝ) : convex (metric.ball a r) :=
by simpa only [metric.ball, sep_univ] using (convex_on_dist a _ convex_univ).convex_lt r

lemma convex_closed_ball (a : E) (r : ℝ) : convex (metric.closed_ball a r) :=
by simpa only [metric.closed_ball, sep_univ] using (convex_on_dist a _ convex_univ).convex_le r

/-- Given a point `x` in the convex hull of `s` and a point `y`, there exists a point
of `s` at distance at least `dist x y` from `y`. -/
lemma convex_hull_exists_dist_ge {s : set E} {x : E} (hx : x ∈ convex_hull s) (y : E) :
  ∃ x' ∈ s, dist x y ≤ dist x' y :=
(convex_on_dist y _ (convex_convex_hull _)).exists_ge_of_mem_convex_hull hx

/-- Given a point `x` in the convex hull of `s` and a point `y` in the convex hull of `t`,
there exist points `x' ∈ s` and `y' ∈ t` at distance at least `dist x y`. -/
lemma convex_hull_exists_dist_ge2 {s t : set E} {x y : E}
  (hx : x ∈ convex_hull s) (hy : y ∈ convex_hull t) :
  ∃ (x' ∈ s) (y' ∈ t), dist x y ≤ dist x' y' :=
begin
  rcases convex_hull_exists_dist_ge hx y with ⟨x', hx', Hx'⟩,
  rcases convex_hull_exists_dist_ge hy x' with ⟨y', hy', Hy'⟩,
  use [x', hx', y', hy'],
  exact le_trans Hx' (dist_comm y x' ▸ dist_comm y' x' ▸ Hy')
end

/-- Emetric diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp] lemma convex_hull_ediam (s : set E) :
  emetric.diam (convex_hull s) = emetric.diam s :=
begin
  refine (emetric.diam_le $ λ x hx y hy, _).antisymm (emetric.diam_mono $ subset_convex_hull s),
  rcases convex_hull_exists_dist_ge2 hx hy with ⟨x', hx', y', hy', H⟩,
  rw edist_dist,
  apply le_trans (ennreal.of_real_le_of_real H),
  rw ← edist_dist,
  exact emetric.edist_le_diam_of_mem hx' hy'
end

/-- Diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp] lemma convex_hull_diam (s : set E) :
  metric.diam (convex_hull s) = metric.diam s :=
by simp only [metric.diam, convex_hull_ediam]

/-- Convex hull of `s` is bounded if and only if `s` is bounded. -/
@[simp] lemma bounded_convex_hull {s : set E} :
  metric.bounded (convex_hull s) ↔ metric.bounded s :=
by simp only [metric.bounded_iff_ediam_ne_top, convex_hull_ediam]

lemma convex.is_path_connected {s : set E} (hconv : convex s) (hne : s.nonempty) :
  is_path_connected s :=
begin
  refine is_path_connected_iff.mpr ⟨hne, _⟩,
  intros x y x_in y_in,
  let f := λ θ : ℝ, x + θ • (y - x),
  have hf : continuous f, by continuity,
  have h₀ : f 0 = x, by simp [f],
  have h₁ : f 1 = y, by { dsimp [f], rw one_smul, abel },
  have H := hconv.segment_subset x_in y_in,
  rw segment_eq_image' at H,
  exact joined_in.of_line hf.continuous_on h₀ h₁ H
end

@[priority 100]
instance normed_space.path_connected : path_connected_space E :=
path_connected_space_iff_univ.mpr $ convex_univ.is_path_connected ⟨(0 : E), trivial⟩

@[priority 100]
instance normed_space.loc_path_connected : loc_path_connected_space E :=
loc_path_connected_of_bases (λ x, metric.nhds_basis_ball)
  (λ x r r_pos, (convex_ball x r).is_path_connected $ by simp [r_pos])

end normed_space
