/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.instances.real_vector_space
import analysis.normed_space.add_torsor
import linear_algebra.affine_space.midpoint
import analysis.normed_space.linear_isometry

/-!
# Mazur-Ulam Theorem

Mazur-Ulam theorem states that an isometric bijection between two normed affine spaces over `ℝ` is
affine. We formalize it in three definitions:

* `isometric.to_real_linear_isometry_equiv_of_map_zero` : given `E ≃ᵢ F` sending `0` to `0`,
  returns `E ≃ₗᵢ[ℝ] F` with the same `to_fun` and `inv_fun`;
* `isometric.to_real_linear_isometry_equiv` : given `f : E ≃ᵢ F`,
  returns `g : E ≃ₗᵢ[ℝ] F` with `g x = f x - f 0`.
* `isometric.to_affine_equiv` : given `PE ≃ᵢ PF`, returns `g : PE ≃ᵃ[ℝ] PF` with the same
  `to_equiv`.

The formalization is based on [Jussi Väisälä, *A Proof of the Mazur-Ulam Theorem*][Vaisala_2003].

## Tags

isometry, affine map, linear map
-/

variables
  {E PE : Type*} [normed_group E] [normed_space ℝ E] [metric_space PE] [normed_add_torsor E PE]
  {F PF : Type*} [normed_group F] [normed_space ℝ F] [metric_space PF] [normed_add_torsor F PF]

open set affine_map

noncomputable theory

namespace isometric

include E

/-- If an isometric self-homeomorphism of a normed vector space over `ℝ` fixes `x` and `y`,
then it fixes the midpoint of `[x, y]`. This is a lemma for a more general Mazur-Ulam theorem,
see below. -/
lemma midpoint_fixed {x y : PE} :
  ∀ e : PE ≃ᵢ PE, e x = x → e y = y → e (midpoint ℝ x y) = midpoint ℝ x y :=
begin
  set z := midpoint ℝ x y,
  -- Consider the set of `e : E ≃ᵢ E` such that `e x = x` and `e y = y`
  set s := { e : PE ≃ᵢ PE | e x = x ∧ e y = y },
  haveI : nonempty s := ⟨⟨isometric.refl PE, rfl, rfl⟩⟩,
  -- On the one hand, `e` cannot send the midpoint `z` of `[x, y]` too far
  have h_bdd : bdd_above (range $ λ e : s, dist (e z) z),
  { refine ⟨dist x z + dist x z, forall_range_iff.2 $ subtype.forall.2 _⟩,
    rintro e ⟨hx, hy⟩,
    calc dist (e z) z ≤ dist (e z) x + dist x z     : dist_triangle (e z) x z
                  ... = dist (e x) (e z) + dist x z : by rw [hx, dist_comm]
                  ... = dist x z + dist x z         : by erw [e.dist_eq x z] },
  -- On the other hand, consider the map `f : (E ≃ᵢ E) → (E ≃ᵢ E)`
  -- sending each `e` to `R ∘ e⁻¹ ∘ R ∘ e`, where `R` is the point reflection in the
  -- midpoint `z` of `[x, y]`.
  set R : PE ≃ᵢ PE := point_reflection z,
  set f : (PE ≃ᵢ PE) → (PE ≃ᵢ PE) := λ e, ((e.trans R).trans e.symm).trans R,
  -- Note that `f` doubles the value of ``dist (e z) z`
  have hf_dist : ∀ e, dist (f e z) z = 2 * dist (e z) z,
  { intro e,
    dsimp [f],
    rw [dist_point_reflection_fixed, ← e.dist_eq, e.apply_symm_apply,
      dist_point_reflection_self_real, dist_comm] },
  -- Also note that `f` maps `s` to itself
  have hf_maps_to : maps_to f s s,
  { rintros e ⟨hx, hy⟩,
    split; simp [hx, hy, e.symm_apply_eq.2 hx.symm, e.symm_apply_eq.2 hy.symm], },
  -- Therefore, `dist (e z) z = 0` for all `e ∈ s`.
  set c := ⨆ e : s, dist (e z) z,
  have : c ≤ c / 2,
  { apply csupr_le,
    rintros ⟨e, he⟩,
    simp only [coe_fn_coe_base, subtype.coe_mk, le_div_iff' (@zero_lt_two ℝ _ _), ← hf_dist],
    exact le_csupr h_bdd ⟨f e, hf_maps_to he⟩ },
  replace : c ≤ 0, { linarith },
  refine λ e hx hy, dist_le_zero.1 (le_trans _ this),
  exact le_csupr h_bdd ⟨e, hx, hy⟩
end

include F

/-- A bijective isometry sends midpoints to midpoints. -/
lemma map_midpoint (f : PE ≃ᵢ PF) (x y : PE) : f (midpoint ℝ x y) = midpoint ℝ (f x) (f y) :=
begin
  set e : PE ≃ᵢ PE := ((f.trans $ point_reflection $ midpoint ℝ (f x) (f y)).trans f.symm).trans
    (point_reflection $ midpoint ℝ x y),
  have hx : e x = x, by simp,
  have hy : e y = y, by simp,
  have hm := e.midpoint_fixed hx hy,
  simp only [e, trans_apply] at hm,
  rwa [← eq_symm_apply, point_reflection_symm, point_reflection_self, symm_apply_eq,
    point_reflection_fixed_iff ℝ] at hm,
  apply_instance
end

/-!
Since `f : PE ≃ᵢ PF` sends midpoints to midpoints, it is an affine map.
We define a conversion to a `continuous_linear_equiv` first, then a conversion to an `affine_map`.
-/

/-- **Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed vector spaces
over `ℝ` and `f 0 = 0`, then `f` is a linear equivalence. -/
def to_real_linear_isometry_equiv_of_map_zero (f : E ≃ᵢ F) (h0 : f 0 = 0) :
  E ≃ₗᵢ[ℝ] F :=
{ norm_map' := λ x, show ∥f x∥ = ∥x∥, by simp only [← dist_zero_right, ← h0, f.dist_eq],
  .. ((add_monoid_hom.of_map_midpoint ℝ ℝ f h0 f.map_midpoint).to_real_linear_map f.continuous),
  .. f }

@[simp] lemma coe_to_real_linear_equiv_of_map_zero (f : E ≃ᵢ F) (h0 : f 0 = 0) :
  ⇑(f.to_real_linear_isometry_equiv_of_map_zero h0) = f := rfl

@[simp] lemma coe_to_real_linear_equiv_of_map_zero_symm (f : E ≃ᵢ F) (h0 : f 0 = 0) :
  ⇑(f.to_real_linear_isometry_equiv_of_map_zero h0).symm = f.symm := rfl

/-- **Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed vector spaces
over `ℝ`, then `x ↦ f x - f 0` is a linear equivalence. -/
def to_real_linear_isometry_equiv (f : E ≃ᵢ F) : E ≃ₗᵢ[ℝ] F :=
(f.trans (isometric.add_right (f 0)).symm).to_real_linear_isometry_equiv_of_map_zero
  (by simpa only [sub_eq_add_neg] using sub_self (f 0))

@[simp] lemma to_real_linear_equiv_apply (f : E ≃ᵢ F) (x : E) :
  (f.to_real_linear_isometry_equiv : E → F) x = f x - f 0 :=
(sub_eq_add_neg (f x) (f 0)).symm

@[simp] lemma to_real_linear_isometry_equiv_symm_apply (f : E ≃ᵢ F) (y : F) :
  (f.to_real_linear_isometry_equiv.symm : F → E) y = f.symm (y + f 0) := rfl

/-- Convert an isometric equivalence between two affine spaces to an `affine_map`. -/
def to_affine_equiv (f : PE ≃ᵢ PF) : PE ≃ᵃ[ℝ] PF :=
affine_equiv.mk' f.to_equiv
  (((vadd_const (classical.arbitrary PE)).trans $ f.trans
    (vadd_const (f $ classical.arbitrary PE)).symm).to_real_linear_isometry_equiv.to_linear_equiv)
  (classical.arbitrary PE) (λ p, by simp)

@[simp] lemma coe_to_affine_equiv (f : PE ≃ᵢ PF) : ⇑f.to_affine_equiv = f := rfl

end isometric
