/-
  Copyright (c) 2020 Anne Baanen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Anne Baanen.

  The Special Linear group $SL(n, R)$
-/
import linear_algebra.matrix

/-!
# The Special Linear group $SL(n, R)$

This file defines the elements of the Special Linear group `special_linear_group n R`,
also written `SL(n, R)` or `SLₙ(R)`, consisting of all `n` by `n` `R`-matrices with
determinant `1`.  In addition, we define the group structure on `special_linear_group n R`
and the embedding into the general linear group `general_linear_group R (n → R)`
(i.e. `GL(n, R)` or `GLₙ(R)`).

## Main definitions

 * `matrix.special_linear_group` is the type of matrices with determinant 1
 * `matrix.special_linear_group.group` gives the group structure (under multiplication)
 * `matrix.special_linear_group.embedding_GL` is the embedding `SLₙ(R) → GLₙ(R)`

## Implementation notes
The inverse operation in the `special_linear_group` is defined to be the adjugate
matrix, so that `special_linear_group n R` has a group structure for all `comm_ring R`.

We define the elements of `special_linear_group` to be matrices, since we need to
compute their determinant. This is in contrast with `general_linear_group R M`,
which consists of invertible `R`-linear maps on `M`.

## References

 * https://en.wikipedia.org/wiki/Special_linear_group

## Tags

matrix group, group, matrix inverse
-/

namespace matrix
universes u v
open_locale matrix
open linear_map


section

variables (n : Type u) [decidable_eq n] [fintype n] (R : Type v) [comm_ring R]

/-- `special_linear_group n R` is the group of `n` by `n` `R`-matrices with determinant equal to 1. -/
def special_linear_group := { A : matrix n n R // A.det = 1 }

end

namespace special_linear_group

variables {n : Type u} [decidable_eq n] [fintype n] {R : Type v} [comm_ring R]

instance coe_matrix : has_coe (special_linear_group n R) (matrix n n R) :=
⟨λ A, A.val⟩

instance coe_fun : has_coe_to_fun (special_linear_group n R) :=
{ F   := λ _, n → n → R,
  coe := λ A, A.val }

/--
  `to_lin' A` is matrix multiplication of vectors by `A`, as a linear map.

  After the group structure on `special_linear_group n R` is defined,
  we show in `to_linear_equiv` that this gives a linear equivalence.
-/
def to_lin' (A : special_linear_group n R) := matrix.to_lin' A

lemma ext_iff (A B : special_linear_group n R) : A = B ↔ (∀ i j, A i j = B i j) :=
iff.trans subtype.ext_iff_val ⟨(λ h i j, congr_fun (congr_fun h i) j), matrix.ext⟩

@[ext] lemma ext (A B : special_linear_group n R) : (∀ i j, A i j = B i j) → A = B :=
(special_linear_group.ext_iff A B).mpr

instance has_inv : has_inv (special_linear_group n R) :=
⟨λ A, ⟨adjugate A, det_adjugate_eq_one A.2⟩⟩

instance has_mul : has_mul (special_linear_group n R) :=
⟨λ A B, ⟨A.1 ⬝ B.1, by erw [det_mul, A.2, B.2, one_mul]⟩⟩

instance has_one : has_one (special_linear_group n R) :=
⟨⟨1, det_one⟩⟩

instance : inhabited (special_linear_group n R) := ⟨1⟩

section coe_lemmas

variables (A B : special_linear_group n R)

@[simp] lemma inv_val : ↑(A⁻¹) = adjugate A := rfl

@[simp] lemma inv_apply : ⇑(A⁻¹) = adjugate A := rfl

@[simp] lemma mul_val : ↑(A * B) = A ⬝ B := rfl

@[simp] lemma mul_apply : ⇑(A * B) = (A ⬝ B) := rfl

@[simp] lemma one_val : ↑(1 : special_linear_group n R) = (1 : matrix n n R) := rfl

@[simp] lemma one_apply : ⇑(1 : special_linear_group n R) = (1 : matrix n n R) := rfl

@[simp] lemma det_coe_matrix : det A = 1 := A.2

lemma det_coe_fun : det ⇑A = 1 := A.2

@[simp] lemma to_lin'_mul :
  to_lin' (A * B) = (to_lin' A).comp (to_lin' B) :=
matrix.to_lin'_mul A B

@[simp] lemma to_lin'_one :
  to_lin' (1 : special_linear_group n R) = linear_map.id :=
matrix.to_lin'_one

end coe_lemmas

instance group : group (special_linear_group n R) :=
{ mul_assoc := λ A B C, by { ext, simp [matrix.mul_assoc] },
  one_mul := λ A, by { ext, simp },
  mul_one := λ A, by { ext, simp },
  mul_left_inv := λ A, by { ext, simp [adjugate_mul] },
  ..special_linear_group.has_mul,
  ..special_linear_group.has_one,
  ..special_linear_group.has_inv }

/-- `to_linear_equiv A` is matrix multiplication of vectors by `A`, as a linear equivalence. -/
def to_linear_equiv (A : special_linear_group n R) : (n → R) ≃ₗ[R] (n → R) :=
{ inv_fun := A⁻¹.to_lin',
  left_inv := λ x, calc
    A⁻¹.to_lin'.comp A.to_lin' x
        = (A⁻¹ * A).to_lin' x : by rw [←to_lin'_mul]
    ... = x : by rw [mul_left_inv, to_lin'_one, id_apply],
  right_inv := λ x, calc
    A.to_lin'.comp A⁻¹.to_lin' x
        = (A * A⁻¹).to_lin' x : by rw [←to_lin'_mul]
    ... = x : by rw [mul_right_inv, to_lin'_one, id_apply],
  ..matrix.to_lin' A }

/-- `to_GL` is the map from the special linear group to the general linear group -/
def to_GL (A : special_linear_group n R) : general_linear_group R (n → R) :=
general_linear_group.of_linear_equiv (to_linear_equiv A)

lemma coe_to_GL (A : special_linear_group n R) :
  (@coe (units _) _ _ (to_GL A)) = A.to_lin' :=
rfl

@[simp]
lemma to_GL_one : to_GL (1 : special_linear_group n R) = 1 :=
by { ext v i, rw [coe_to_GL, to_lin'_one], refl }

@[simp]
lemma to_GL_mul (A B : special_linear_group n R) :
  to_GL (A * B) = to_GL A * to_GL B :=
by { ext v i, rw [coe_to_GL, to_lin'_mul], refl }

/-- `special_linear_group.embedding_GL` is the embedding from `special_linear_group n R`
  to `general_linear_group n R`. -/
def embedding_GL : (special_linear_group n R) →* (general_linear_group R (n → R)) :=
⟨λ A, to_GL A, by simp, by simp⟩

end special_linear_group

end matrix
