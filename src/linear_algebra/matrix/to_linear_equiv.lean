/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.to_lin

/-!
# Matrices and linear equivalences

This file gives the map `matrix.to_linear_equiv` from matrices with invertible determinant,
to linear equivs.

## Main definitions

 * `matrix.to_linear_equiv`: a matrix with an invertible determinant forms a linear equiv

## Tags

matrix, linear_equiv, determinant, inverse

-/

namespace matrix

open linear_map

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables {n : Type*} [fintype n]

section to_linear_equiv'

variables [decidable_eq n]

/-- An invertible matrix yields a linear equivalence from the free module to itself.

See `matrix.to_linear_equiv` for the same map on arbitrary modules.
-/
noncomputable def to_linear_equiv' (P : matrix n n R) (h : is_unit P) : (n → R) ≃ₗ[R] (n → R) :=
have h' : is_unit P.det := P.is_unit_iff_is_unit_det.mp h,
{ inv_fun   := P⁻¹.to_lin',
  left_inv  := λ v,
    show (P⁻¹.to_lin'.comp P.to_lin') v = v,
    by rw [← matrix.to_lin'_mul, P.nonsing_inv_mul h', matrix.to_lin'_one, linear_map.id_apply],
  right_inv := λ v,
    show (P.to_lin'.comp P⁻¹.to_lin') v = v,
    by rw [← matrix.to_lin'_mul, P.mul_nonsing_inv h', matrix.to_lin'_one, linear_map.id_apply],
  ..P.to_lin' }

@[simp] lemma to_linear_equiv'_apply (P : matrix n n R) (h : is_unit P) :
  (↑(P.to_linear_equiv' h) : module.End R (n → R)) = P.to_lin' := rfl

@[simp] lemma to_linear_equiv'_symm_apply (P : matrix n n R) (h : is_unit P) :
  (↑(P.to_linear_equiv' h).symm : module.End R (n → R)) = P⁻¹.to_lin' := rfl

end to_linear_equiv'

section to_linear_equiv

variables (b : basis n R M)

include b

/-- Given `hA : is_unit A.det` and `b : basis R b`, `A.to_linear_equiv b hA` is
the `linear_equiv` arising from `to_lin b b A`.

See `matrix.to_linear_equiv'` for this result on `n → R`.
-/
@[simps apply]
noncomputable def to_linear_equiv [decidable_eq n] (A : matrix n n R) (hA : is_unit A.det) :
  M ≃ₗ[R] M :=
begin
  refine {
    to_fun := to_lin b b A,
    inv_fun := to_lin b b A⁻¹,
    left_inv := λ x, _,
    right_inv := λ x, _,
    .. to_lin b b A };
  simp only [← linear_map.comp_apply, ← matrix.to_lin_mul b b b,
             matrix.nonsing_inv_mul _ hA, matrix.mul_nonsing_inv _ hA,
             to_lin_one, linear_map.id_apply]
end

lemma ker_to_lin_eq_bot [decidable_eq n] (A : matrix n n R) (hA : is_unit A.det) :
  (to_lin b b A).ker = ⊥ :=
ker_eq_bot.mpr (to_linear_equiv b A hA).injective

lemma range_to_lin_eq_top [decidable_eq n] (A : matrix n n R) (hA : is_unit A.det) :
  (to_lin b b A).range = ⊤ :=
range_eq_top.mpr (to_linear_equiv b A hA).surjective

end to_linear_equiv

end matrix
