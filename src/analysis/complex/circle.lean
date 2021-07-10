/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.special_functions.exp_log

/-!
# The circle

This file defines `circle` to be the metric sphere (`metric.sphere`) in `ℂ` centred at `0` of
radius `1`.  We equip it with the following structure:

* a submonoid of `ℂ`
* a group
* a topological group

We furthermore define `exp_map_circle` to be the natural map `λ t, exp (t * I)` from `ℝ` to
`circle`, and show that this map is a group homomorphism.

## Implementation notes

Because later (in `geometry.manifold.instances.sphere`) one wants to equip the circle with a smooth
manifold structure borrowed from `metric.sphere`, the underlying set is
`{z : ℂ | abs (z - 0) = 1}`.  This prevents certain algebraic facts from working definitionally --
for example, the circle is not defeq to `{z : ℂ | abs z = 1}`, which is the kernel of `complex.abs`
considered as a homomorphism from `ℂ` to `ℝ`, nor is it defeq to `{z : ℂ | norm_sq z = 1}`, which
is the kernel of the homomorphism `complex.norm_sq` from `ℂ` to `ℝ`.

-/

noncomputable theory

open complex metric

/-- The unit circle in `ℂ`, here given the structure of a submonoid of `ℂ`. -/
def circle : submonoid ℂ :=
{ carrier := sphere (0:ℂ) 1,
  one_mem' := by simp,
  mul_mem' := λ a b, begin
    simp only [norm_eq_abs, mem_sphere_zero_iff_norm],
    intros ha hb,
    simp [ha, hb],
  end }

@[simp] lemma mem_circle_iff_abs (z : ℂ) : z ∈ circle ↔ abs z = 1 := mem_sphere_zero_iff_norm

lemma circle_def : ↑circle = {z : ℂ | abs z = 1} := by { ext, simp }

@[simp] lemma abs_eq_of_mem_circle (z : circle) : abs z = 1 := by { convert z.2, simp }

@[simp] lemma norm_sq_eq_of_mem_circle (z : circle) : norm_sq z = 1 := by simp [norm_sq_eq_abs]

lemma nonzero_of_mem_circle (z : circle) : (z:ℂ) ≠ 0 := nonzero_of_mem_unit_sphere z

instance : group circle :=
{ inv := λ z, ⟨conj z, by simp⟩,
  mul_left_inv := λ z, subtype.ext $ by { simp [has_inv.inv, ← norm_sq_eq_conj_mul_self,
    ← mul_self_abs] },
  .. circle.to_monoid }

lemma coe_inv_circle_eq_conj (z : circle) : ↑(z⁻¹) = conj z := rfl

@[simp] lemma coe_inv_circle (z : circle) : ↑(z⁻¹) = (z : ℂ)⁻¹ :=
begin
  rw coe_inv_circle_eq_conj,
  apply eq_inv_of_mul_right_eq_one,
  rw [mul_comm, ← complex.norm_sq_eq_conj_mul_self],
  simp,
end

@[simp] lemma coe_div_circle (z w : circle) : ↑(z / w) = (z:ℂ) / w :=
show ↑(z * w⁻¹) = (z:ℂ) * w⁻¹, by simp

instance : compact_space circle := metric.sphere.compact_space _ _

-- the following result could instead be deduced from the Lie group structure on the circle using
-- `topological_group_of_lie_group`, but that seems a little awkward since one has to first provide
-- and then forget the model space
instance : topological_group circle :=
{ continuous_mul := let h : continuous (λ x : circle, (x : ℂ)) := continuous_subtype_coe in
    continuous_induced_rng (continuous_mul.comp (h.prod_map h)),
  continuous_inv := continuous_induced_rng $
    complex.conj_cle.continuous.comp continuous_subtype_coe }

/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ`. -/
def exp_map_circle (t : ℝ) : circle :=
⟨exp (t * I), by simp [exp_mul_I, abs_cos_add_sin_mul_I]⟩

@[simp] lemma exp_map_circle_apply (t : ℝ) : ↑(exp_map_circle t) = complex.exp (t * complex.I) :=
rfl

/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ`, considered as a homomorphism of
groups. -/
def exp_map_circle_hom : ℝ →+ (additive circle) :=
{ to_fun := exp_map_circle,
  map_zero' := by { rw exp_map_circle, convert of_mul_one, simp },
  map_add' := λ x y, show exp_map_circle (x + y) = (exp_map_circle x) * (exp_map_circle y),
    from subtype.ext $ by simp [exp_map_circle, exp_add, add_mul] }
