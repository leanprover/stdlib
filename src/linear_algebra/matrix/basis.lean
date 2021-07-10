/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import linear_algebra.matrix.reindex
import linear_algebra.matrix.to_lin

/-!
# Bases and matrices

This file defines the map `basis.to_matrix` that sends a family of vectors to
the matrix of their coordinates with respect to some basis.

## Main definitions

 * `basis.to_matrix e v` is the matrix whose `i, j`th entry is `e.repr (v j) i`
 * `basis.to_matrix_equiv` is `basis.to_matrix` bundled as a linear equiv

## Main results

 * `linear_map.to_matrix_id_eq_basis_to_matrix`: `linear_map.to_matrix b c id`
   is equal to `basis.to_matrix b c`
 * `basis.to_matrix_mul_to_matrix`: multiplying `basis.to_matrix` with another
   `basis.to_matrix` gives a `basis.to_matrix`

## Tags

matrix, basis
-/

noncomputable theory

open linear_map matrix set submodule
open_locale big_operators
open_locale matrix

section basis_to_matrix

variables {ι ι' κ κ' : Type*} [fintype ι] [fintype ι'] [fintype κ] [fintype κ']
variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]

open function matrix

/-- From a basis `e : ι → M` and a family of vectors `v : ι' → M`, make the matrix whose columns
are the vectors `v i` written in the basis `e`. -/
def basis.to_matrix (e : basis ι R M) (v : ι' → M) : matrix ι ι' R :=
λ i j, e.repr (v j) i

variables (e : basis ι R M) (v : ι' → M) (i : ι) (j : ι')

namespace basis

lemma to_matrix_apply : e.to_matrix v i j = e.repr (v j) i :=
rfl

lemma to_matrix_transpose_apply : (e.to_matrix v)ᵀ j = e.repr (v j) :=
funext $ (λ _, rfl)

lemma to_matrix_eq_to_matrix_constr [decidable_eq ι] (v : ι → M) :
  e.to_matrix v = linear_map.to_matrix e e (e.constr ℕ v) :=
by { ext, rw [basis.to_matrix_apply, linear_map.to_matrix_apply, basis.constr_basis] }

@[simp] lemma to_matrix_self [decidable_eq ι] : e.to_matrix e = 1 :=
begin
  rw basis.to_matrix,
  ext i j,
  simp [basis.equiv_fun, matrix.one_apply, finsupp.single, eq_comm]
end

lemma to_matrix_update [decidable_eq ι'] (x : M) :
  e.to_matrix (function.update v j x) = matrix.update_column (e.to_matrix v) j (e.repr x) :=
begin
  ext i' k,
  rw [basis.to_matrix, matrix.update_column_apply, e.to_matrix_apply],
  split_ifs,
  { rw [h, update_same j x v] },
  { rw update_noteq h },
end

@[simp] lemma sum_to_matrix_smul_self : ∑ (i : ι), e.to_matrix v i j • e i = v j :=
by simp_rw [e.to_matrix_apply, e.sum_repr]

@[simp] lemma to_lin_to_matrix [decidable_eq ι'] (v : basis ι' R M) :
  matrix.to_lin v e (e.to_matrix v) = id :=
v.ext (λ i, by rw [to_lin_self, id_apply, e.sum_to_matrix_smul_self])

/-- From a basis `e : ι → M`, build a linear equivalence between families of vectors `v : ι → M`,
and matrices, making the matrix whose columns are the vectors `v i` written in the basis `e`. -/
def to_matrix_equiv (e : basis ι R M) : (ι → M) ≃ₗ[R] matrix ι ι R :=
{ to_fun := e.to_matrix,
  map_add' := λ v w, begin
    ext i j,
    change _ = _ + _,
    rw [e.to_matrix_apply, pi.add_apply, linear_equiv.map_add],
    refl
  end,
  map_smul' := begin
    intros c v,
    ext i j,
    rw [e.to_matrix_apply, pi.smul_apply, linear_equiv.map_smul],
    refl
  end,
  inv_fun := λ m j, ∑ i, (m i j) • e i,
  left_inv := begin
    intro v,
    ext j,
    exact e.sum_to_matrix_smul_self v j
  end,
  right_inv := begin
    intros m,
    ext k l,
    simp only [e.to_matrix_apply, ← e.equiv_fun_apply, ← e.equiv_fun_symm_apply,
               linear_equiv.apply_symm_apply],
  end }

end basis

section mul_linear_map_to_matrix

variables {N : Type*} [add_comm_group N] [module R N]
variables (b : basis ι R M) (b' : basis ι' R M) (c : basis κ R N) (c' : basis κ' R N)
variables (f : M →ₗ[R] N)

open linear_map

@[simp] lemma basis_to_matrix_mul_linear_map_to_matrix [decidable_eq ι'] :
  c.to_matrix c' ⬝ linear_map.to_matrix b' c' f = linear_map.to_matrix b' c f :=
(matrix.to_lin b' c).injective
  (by haveI := classical.dec_eq κ';
      rw [to_lin_to_matrix, to_lin_mul b' c' c, to_lin_to_matrix, c.to_lin_to_matrix, id_comp])

@[simp] lemma linear_map_to_matrix_mul_basis_to_matrix [decidable_eq ι] [decidable_eq ι'] :
  linear_map.to_matrix b' c' f ⬝ b'.to_matrix b = linear_map.to_matrix b c' f :=
(matrix.to_lin b c').injective
  (by rw [to_lin_to_matrix, to_lin_mul b b' c', to_lin_to_matrix, b'.to_lin_to_matrix, comp_id])

/-- A generalization of `linear_map.to_matrix_id`. -/
@[simp] lemma linear_map.to_matrix_id_eq_basis_to_matrix [decidable_eq ι] :
  linear_map.to_matrix b b' id = b'.to_matrix b :=
by { haveI := classical.dec_eq ι',
      rw [← basis_to_matrix_mul_linear_map_to_matrix b b', to_matrix_id, matrix.mul_one] }

/-- A generalization of `basis.to_matrix_self`, in the opposite direction. -/
@[simp] lemma basis.to_matrix_mul_to_matrix
  {ι'' : Type*} [fintype ι''] (b'' : ι'' → M) :
  b.to_matrix b' ⬝ b'.to_matrix b'' = b.to_matrix b'' :=
begin
  haveI := classical.dec_eq ι,
  haveI := classical.dec_eq ι',
  haveI := classical.dec_eq ι'',
  ext i j,
  simp only [matrix.mul_apply, basis.to_matrix_apply, basis.sum_repr_mul_repr],
end

@[simp]
lemma basis.to_matrix_reindex
  (b : basis ι R M) (v : ι' → M) (e : ι ≃ ι') :
  (b.reindex e).to_matrix v = (b.to_matrix v).minor e.symm id :=
by { ext, simp only [basis.to_matrix_apply, basis.reindex_repr, matrix.minor_apply, id.def] }

/-- See also `basis.to_matrix_reindex` which gives the `simp` normal form of this result. -/
lemma basis.to_matrix_reindex' [decidable_eq ι] [decidable_eq ι']
  (b : basis ι R M) (v : ι' → M) (e : ι ≃ ι') :
  (b.reindex e).to_matrix v = matrix.reindex_alg_equiv _ e (b.to_matrix (v ∘ e)) :=
by { ext, simp only [basis.to_matrix_apply, basis.reindex_repr, matrix.reindex_alg_equiv_apply,
        matrix.reindex_apply, matrix.minor_apply, function.comp_app, e.apply_symm_apply] }

@[simp]
lemma basis.to_matrix_map (b : basis ι R M) (f : M ≃ₗ[R] N) (v : ι → N) :
  (b.map f).to_matrix v = b.to_matrix (f.symm ∘ v) :=
by { ext, simp only [basis.to_matrix_apply, basis.map, linear_equiv.trans_apply] }

end mul_linear_map_to_matrix

end basis_to_matrix
