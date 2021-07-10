/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.specific_limits
import analysis.asymptotics.asymptotics

/-!
# The group of units of a complete normed ring

This file contains the basic theory for the group of units (invertible elements) of a complete
normed ring (Banach algebras being a notable special case).

## Main results

The constructions `one_sub`, `add` and `unit_of_nearby` state, in varying forms, that perturbations
of a unit are units.  The latter two are not stated in their optimal form; more precise versions
would use the spectral radius.

The first main result is `is_open`:  the group of units of a complete normed ring is an open subset
of the ring.

The function `inverse` (defined in `algebra.ring`), for a ring `R`, sends `a : R` to `a⁻¹` if `a` is
a unit and 0 if not.  The other major results of this file (notably `inverse_add`,
`inverse_add_norm` and `inverse_add_norm_diff_nth_order`) cover the asymptotic properties of
`inverse (x + t)` as `t → 0`.

-/

noncomputable theory
open_locale topological_space
variables {R : Type*} [normed_ring R] [complete_space R]

namespace units

/-- In a complete normed ring, a perturbation of `1` by an element `t` of distance less than `1`
from `1` is a unit.  Here we construct its `units` structure.  -/
@[simps coe]
def one_sub (t : R) (h : ∥t∥ < 1) : units R :=
{ val := 1 - t,
  inv := ∑' n : ℕ, t ^ n,
  val_inv := mul_neg_geom_series t h,
  inv_val := geom_series_mul_neg t h }

/-- In a complete normed ring, a perturbation of a unit `x` by an element `t` of distance less than
`∥x⁻¹∥⁻¹` from `x` is a unit.  Here we construct its `units` structure. -/
@[simps coe]
def add (x : units R) (t : R) (h : ∥t∥ < ∥(↑x⁻¹ : R)∥⁻¹) : units R :=
units.copy  -- to make `coe_add` true definitionally, for convenience
  (x * (units.one_sub (-(↑x⁻¹ * t)) begin
      nontriviality R using [zero_lt_one],
      have hpos : 0 < ∥(↑x⁻¹ : R)∥ := units.norm_pos x⁻¹,
      calc ∥-(↑x⁻¹ * t)∥
          = ∥↑x⁻¹ * t∥                    : by { rw norm_neg }
      ... ≤ ∥(↑x⁻¹ : R)∥ * ∥t∥            : norm_mul_le ↑x⁻¹ _
      ... < ∥(↑x⁻¹ : R)∥ * ∥(↑x⁻¹ : R)∥⁻¹ : by nlinarith only [h, hpos]
      ... = 1                             : mul_inv_cancel (ne_of_gt hpos)
    end))
  (x + t) (by simp [mul_add]) _ rfl

/-- In a complete normed ring, an element `y` of distance less than `∥x⁻¹∥⁻¹` from `x` is a unit.
Here we construct its `units` structure. -/
@[simps coe]
def unit_of_nearby (x : units R) (y : R) (h : ∥y - x∥ < ∥(↑x⁻¹ : R)∥⁻¹) : units R :=
units.copy (x.add (y - x : R) h) y (by simp) _ rfl

/-- The group of units of a complete normed ring is an open subset of the ring. -/
protected lemma is_open : is_open {x : R | is_unit x} :=
begin
  nontriviality R,
  apply metric.is_open_iff.mpr,
  rintros x' ⟨x, rfl⟩,
  refine ⟨∥(↑x⁻¹ : R)∥⁻¹, inv_pos.mpr (units.norm_pos x⁻¹), _⟩,
  intros y hy,
  rw [metric.mem_ball, dist_eq_norm] at hy,
  exact (x.unit_of_nearby y hy).is_unit
end

protected lemma nhds (x : units R) : {x : R | is_unit x} ∈ 𝓝 (x : R) :=
is_open.mem_nhds units.is_open x.is_unit

end units

namespace normed_ring
open_locale classical big_operators
open asymptotics filter metric finset ring

lemma inverse_one_sub (t : R) (h : ∥t∥ < 1) : inverse (1 - t) = ↑(units.one_sub t h)⁻¹ :=
by rw [← inverse_unit (units.one_sub t h), units.coe_one_sub]

/-- The formula `inverse (x + t) = inverse (1 + x⁻¹ * t) * x⁻¹` holds for `t` sufficiently small. -/
lemma inverse_add (x : units R) :
  ∀ᶠ t in (𝓝 0), inverse ((x : R) + t) = inverse (1 + ↑x⁻¹ * t) * ↑x⁻¹ :=
begin
  nontriviality R,
  rw [eventually_iff, metric.mem_nhds_iff],
  have hinv : 0 < ∥(↑x⁻¹ : R)∥⁻¹, by cancel_denoms,
  use [∥(↑x⁻¹ : R)∥⁻¹, hinv],
  intros t ht,
  simp only [mem_ball, dist_zero_right] at ht,
  have ht' : ∥-↑x⁻¹ * t∥ < 1,
  { refine lt_of_le_of_lt (norm_mul_le _ _) _,
    rw norm_neg,
    refine lt_of_lt_of_le (mul_lt_mul_of_pos_left ht x⁻¹.norm_pos) _,
    cancel_denoms },
  have hright := inverse_one_sub (-↑x⁻¹ * t) ht',
  have hleft := inverse_unit (x.add t ht),
  simp only [← neg_mul_eq_neg_mul, sub_neg_eq_add] at hright,
  simp only [units.coe_add] at hleft,
  simp [hleft, hright, units.add]
end

lemma inverse_one_sub_nth_order (n : ℕ) :
  ∀ᶠ t in (𝓝 0), inverse ((1:R) - t) = (∑ i in range n, t ^ i) + (t ^ n) * inverse (1 - t) :=
begin
  simp only [eventually_iff, metric.mem_nhds_iff],
  use [1, by norm_num],
  intros t ht,
  simp only [mem_ball, dist_zero_right] at ht,
  simp only [inverse_one_sub t ht, set.mem_set_of_eq],
  have h : 1 = ((range n).sum (λ i, t ^ i)) * (units.one_sub t ht) + t ^ n,
  { simp only [units.coe_one_sub],
    rw [← geom_sum, geom_sum_mul_neg],
    simp },
  rw [← one_mul ↑(units.one_sub t ht)⁻¹, h, add_mul],
  congr,
  { rw [mul_assoc, (units.one_sub t ht).mul_inv],
    simp },
  { simp only [units.coe_one_sub],
    rw [← add_mul, ← geom_sum, geom_sum_mul_neg],
    simp }
end

/-- The formula
`inverse (x + t) = (∑ i in range n, (- x⁻¹ * t) ^ i) * x⁻¹ + (- x⁻¹ * t) ^ n * inverse (x + t)`
holds for `t` sufficiently small. -/
lemma inverse_add_nth_order (x : units R) (n : ℕ) :
  ∀ᶠ t in (𝓝 0), inverse ((x : R) + t)
  = (∑ i in range n, (- ↑x⁻¹ * t) ^ i) * ↑x⁻¹ + (- ↑x⁻¹ * t) ^ n * inverse (x + t) :=
begin
  refine (inverse_add x).mp _,
  have hzero : tendsto (λ (t : R), - ↑x⁻¹ * t) (𝓝 0) (𝓝 0),
  { convert ((mul_left_continuous (- (↑x⁻¹ : R))).tendsto 0).comp tendsto_id,
    simp },
  refine (hzero.eventually (inverse_one_sub_nth_order n)).mp (eventually_of_forall _),
  simp only [neg_mul_eq_neg_mul_symm, sub_neg_eq_add],
  intros t h1 h2,
  have h := congr_arg (λ (a : R), a * ↑x⁻¹) h1,
  dsimp at h,
  convert h,
  rw [add_mul, mul_assoc],
  simp [h2.symm]
end

lemma inverse_one_sub_norm : is_O (λ t, inverse ((1:R) - t)) (λ t, (1:ℝ)) (𝓝 (0:R)) :=
begin
  simp only [is_O, is_O_with, eventually_iff, metric.mem_nhds_iff],
  refine ⟨∥(1:R)∥ + 1, (2:ℝ)⁻¹, by norm_num, _⟩,
  intros t ht,
  simp only [ball, dist_zero_right, set.mem_set_of_eq] at ht,
  have ht' : ∥t∥ < 1,
  { have : (2:ℝ)⁻¹ < 1 := by cancel_denoms,
    linarith },
  simp only [inverse_one_sub t ht', norm_one, mul_one, set.mem_set_of_eq],
  change ∥∑' n : ℕ, t ^ n∥ ≤ _,
  have := normed_ring.tsum_geometric_of_norm_lt_1 t ht',
  have : (1 - ∥t∥)⁻¹ ≤ 2,
  { rw ← inv_inv' (2:ℝ),
    refine inv_le_inv_of_le (by norm_num) _,
    have : (2:ℝ)⁻¹ + (2:ℝ)⁻¹ = 1 := by ring,
    linarith },
  linarith
end

/-- The function `λ t, inverse (x + t)` is O(1) as `t → 0`. -/
lemma inverse_add_norm (x : units R) : is_O (λ t, inverse (↑x + t)) (λ t, (1:ℝ)) (𝓝 (0:R)) :=
begin
  nontriviality R,
  simp only [is_O_iff, norm_one, mul_one],
  cases is_O_iff.mp (@inverse_one_sub_norm R _ _) with C hC,
  use C * ∥((x⁻¹:units R):R)∥,
  have hzero : tendsto (λ t, - (↑x⁻¹ : R) * t) (𝓝 0) (𝓝 0),
  { convert ((mul_left_continuous (-↑x⁻¹ : R)).tendsto 0).comp tendsto_id,
    simp },
  refine (inverse_add x).mp ((hzero.eventually hC).mp (eventually_of_forall _)),
  intros t bound iden,
  rw iden,
  simp at bound,
  have hmul := norm_mul_le (inverse (1 + ↑x⁻¹ * t)) ↑x⁻¹,
  nlinarith [norm_nonneg (↑x⁻¹ : R)]
end

/-- The function
`λ t, inverse (x + t) - (∑ i in range n, (- x⁻¹ * t) ^ i) * x⁻¹`
is `O(t ^ n)` as `t → 0`. -/
lemma inverse_add_norm_diff_nth_order (x : units R) (n : ℕ) :
  is_O (λ (t : R), inverse (↑x + t) - (∑ i in range n, (- ↑x⁻¹ * t) ^ i) * ↑x⁻¹)
  (λ t, ∥t∥ ^ n) (𝓝 (0:R)) :=
begin
  by_cases h : n = 0,
  { simpa [h] using inverse_add_norm x },
  have hn : 0 < n := nat.pos_of_ne_zero h,
  simp [is_O_iff],
  cases (is_O_iff.mp (inverse_add_norm x)) with C hC,
  use C * ∥(1:ℝ)∥ * ∥(↑x⁻¹ : R)∥ ^ n,
  have h : eventually_eq (𝓝 (0:R))
    (λ t, inverse (↑x + t) - (∑ i in range n, (- ↑x⁻¹ * t) ^ i) * ↑x⁻¹)
    (λ t, ((- ↑x⁻¹ * t) ^ n) * inverse (x + t)),
  { refine (inverse_add_nth_order x n).mp (eventually_of_forall _),
    intros t ht,
    convert congr_arg (λ a, a - (range n).sum (pow (-↑x⁻¹ * t)) * ↑x⁻¹) ht,
    simp },
  refine h.mp (hC.mp (eventually_of_forall _)),
  intros t _ hLHS,
  simp only [neg_mul_eq_neg_mul_symm] at hLHS,
  rw hLHS,
  refine le_trans (norm_mul_le _ _ ) _,
  have h' : ∥(-(↑x⁻¹ * t)) ^ n∥ ≤ ∥(↑x⁻¹ : R)∥ ^ n * ∥t∥ ^ n,
  { calc ∥(-(↑x⁻¹ * t)) ^ n∥ ≤ ∥(-(↑x⁻¹ * t))∥ ^ n : norm_pow_le' _ hn
    ... = ∥↑x⁻¹ * t∥ ^ n : by rw norm_neg
    ... ≤ (∥(↑x⁻¹ : R)∥ * ∥t∥) ^ n : _
    ... =  ∥(↑x⁻¹ : R)∥ ^ n * ∥t∥ ^ n : mul_pow _ _ n,
    exact pow_le_pow_of_le_left (norm_nonneg _) (norm_mul_le ↑x⁻¹ t) n },
  have h'' : 0 ≤ ∥(↑x⁻¹ : R)∥ ^ n * ∥t∥ ^ n,
  { refine mul_nonneg _ _;
    exact pow_nonneg (norm_nonneg _) n },
  nlinarith [norm_nonneg (inverse (↑x + t))],
end

/-- The function `λ t, inverse (x + t) - x⁻¹` is `O(t)` as `t → 0`. -/
lemma inverse_add_norm_diff_first_order (x : units R) :
  is_O (λ t, inverse (↑x + t) - ↑x⁻¹) (λ t, ∥t∥) (𝓝 (0:R)) :=
by { convert inverse_add_norm_diff_nth_order x 1; simp }

/-- The function
`λ t, inverse (x + t) - x⁻¹ + x⁻¹ * t * x⁻¹`
is `O(t ^ 2)` as `t → 0`. -/
lemma inverse_add_norm_diff_second_order (x : units R) :
  is_O (λ t, inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) (λ t, ∥t∥ ^ 2) (𝓝 (0:R)) :=
begin
  convert inverse_add_norm_diff_nth_order x 2,
  ext t,
  simp only [range_succ, range_one, sum_insert, mem_singleton, sum_singleton, not_false_iff,
    one_ne_zero, pow_zero, add_mul, pow_one, one_mul, neg_mul_eq_neg_mul_symm,
    sub_add_eq_sub_sub_swap, sub_neg_eq_add],
end

/-- The function `inverse` is continuous at each unit of `R`. -/
lemma inverse_continuous_at (x : units R) : continuous_at inverse (x : R) :=
begin
  have h_is_o : is_o (λ (t : R), ∥inverse (↑x + t) - ↑x⁻¹∥) (λ (t : R), (1:ℝ)) (𝓝 0),
  { refine is_o_norm_left.mpr ((inverse_add_norm_diff_first_order x).trans_is_o _),
    exact is_o_norm_left.mpr (is_o_id_const one_ne_zero) },
  have h_lim : tendsto (λ (y:R), y - x) (𝓝 x) (𝓝 0),
  { refine tendsto_zero_iff_norm_tendsto_zero.mpr _,
    exact tendsto_iff_norm_tendsto_zero.mp tendsto_id },
  simp only [continuous_at],
  rw [tendsto_iff_norm_tendsto_zero, inverse_unit],
  convert h_is_o.tendsto_0.comp h_lim,
  ext, simp
end

end normed_ring

namespace units
open opposite filter normed_ring

/-- In a normed ring, the coercion from `units R` (equipped with the induced topology from the
embedding in `R × R`) to `R` is an open map. -/
lemma is_open_map_coe : is_open_map (coe : units R → R) :=
begin
  rw is_open_map_iff_nhds_le,
  intros x s,
  rw [mem_map, mem_nhds_induced],
  rintros ⟨t, ht, hts⟩,
  obtain ⟨u, hu, v, hv, huvt⟩ :
    ∃ (u : set R), u ∈ 𝓝 ↑x ∧ ∃ (v : set Rᵒᵖ), v ∈ 𝓝 (opposite.op ↑x⁻¹) ∧ u.prod v ⊆ t,
  { simpa [embed_product, mem_nhds_prod_iff] using ht },
  have : u ∩ (op ∘ ring.inverse) ⁻¹' v ∩ (set.range (coe : units R → R)) ∈ 𝓝 ↑x,
  { refine inter_mem_sets (inter_mem_sets hu _) (units.nhds x),
    refine (continuous_op.continuous_at.comp (inverse_continuous_at x)).preimage_mem_nhds _,
    simpa using hv },
  refine mem_sets_of_superset this _,
  rintros _ ⟨⟨huy, hvy⟩, ⟨y, rfl⟩⟩,
  have : embed_product R y ∈ u.prod v := ⟨huy, by simpa using hvy⟩,
  simpa using hts (huvt this)
end

/-- In a normed ring, the coercion from `units R` (equipped with the induced topology from the
embedding in `R × R`) to `R` is an open embedding. -/
lemma open_embedding_coe : open_embedding (coe : units R → R) :=
open_embedding_of_continuous_injective_open continuous_coe ext is_open_map_coe

end units
