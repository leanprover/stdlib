/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/

import linear_algebra.matrix.determinant

/-!
# Changing the index type of a matrix

This file concerns the map `matrix.reindex`, mapping a `m` by `n` matrix
to an `m'` by `n'` matrix, as long as `m ≃ m'` and `n ≃ n'`.

## Main definitions

* `matrix.reindex_linear_equiv R A`: `matrix.reindex` is an `R`-linear equivalence between
  `A`-matrices.
* `matrix.reindex_alg_equiv R`: `matrix.reindex` is an `R`-algebra equivalence between `R`-matrices.

## Tags

matrix, reindex

-/

namespace matrix

open equiv

open_locale matrix



variables {l m n o : Type*} [fintype l] [fintype m] [fintype n] [fintype o]
variables {l' m' n' o' : Type*} [fintype l'] [fintype m'] [fintype n'] [fintype o']
variables {m'' n'' : Type*} [fintype m''] [fintype n'']
variables (R A : Type*)

section add_comm_monoid
variables [semiring R] [add_comm_monoid A] [module R A]

/-- The natural map that reindexes a matrix's rows and columns with equivalent types,
`matrix.reindex`, is a linear equivalence. -/
def reindex_linear_equiv (eₘ : m ≃ m') (eₙ : n ≃ n') : matrix m n A ≃ₗ[R] matrix m' n' A :=
{ map_add'  := λ _ _, rfl,
  map_smul' := λ _ _, rfl,
  ..(reindex eₘ eₙ)}

@[simp] lemma reindex_linear_equiv_apply
  (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m n A) :
  reindex_linear_equiv R A eₘ eₙ M = reindex eₘ eₙ M :=
rfl

@[simp] lemma reindex_linear_equiv_symm (eₘ : m ≃ m') (eₙ : n ≃ n') :
  (reindex_linear_equiv R A eₘ eₙ).symm = reindex_linear_equiv R A eₘ.symm eₙ.symm :=
rfl

@[simp] lemma reindex_linear_equiv_refl_refl :
  reindex_linear_equiv R A (equiv.refl m) (equiv.refl n) = linear_equiv.refl R _ :=
linear_equiv.ext $ λ _, rfl

lemma reindex_linear_equiv_trans (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'')
  (e₂' : n' ≃ n'') : (reindex_linear_equiv R A e₁ e₂).trans (reindex_linear_equiv R A e₁' e₂') =
   (reindex_linear_equiv R A (e₁.trans e₁') (e₂.trans e₂') : _ ≃ₗ[R] _) :=
by { ext, refl }

lemma reindex_linear_equiv_comp (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'')
  (e₂' : n' ≃ n'') :
  (reindex_linear_equiv R A e₁' e₂') ∘ (reindex_linear_equiv R A e₁ e₂)
  = reindex_linear_equiv R A (e₁.trans e₁') (e₂.trans e₂') :=
by { rw [← reindex_linear_equiv_trans], refl }

lemma reindex_linear_equiv_comp_apply (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'')
  (e₂' : n' ≃ n'') (M : matrix m n A) :
  (reindex_linear_equiv R A e₁' e₂') (reindex_linear_equiv R A e₁ e₂ M) =
    reindex_linear_equiv R A (e₁.trans e₁') (e₂.trans e₂') M :=
minor_minor _ _ _ _ _

lemma reindex_linear_equiv_one [decidable_eq m] [decidable_eq m'] [has_one A]
  (e : m ≃ m') : (reindex_linear_equiv R A e e (1 : matrix m m A)) = 1 :=
minor_one_equiv e.symm

end add_comm_monoid

section semiring
variables [semiring R] [semiring A] [module R A]

lemma reindex_linear_equiv_mul
  (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o') (M : matrix m n A) (N : matrix n o A) :
  reindex_linear_equiv R A eₘ eₒ (M ⬝ N) =
    reindex_linear_equiv R A eₘ eₙ M ⬝ reindex_linear_equiv R A eₙ eₒ N :=
minor_mul_equiv M N _ _ _

lemma mul_reindex_linear_equiv_one [decidable_eq o] (e₁ : o ≃ n) (e₂ : o ≃ n')
  (M : matrix m n A) : M.mul (reindex_linear_equiv R A e₁ e₂ 1) =
    reindex_linear_equiv R A (equiv.refl m) (e₁.symm.trans e₂) M :=
mul_minor_one _ _ _

end semiring

section algebra

variables [comm_semiring R] [decidable_eq m] [decidable_eq n]

/--
For square matrices with coefficients in commutative semirings, the natural map that reindexes
a matrix's rows and columns with equivalent types, `matrix.reindex`, is an equivalence of algebras.
-/
def reindex_alg_equiv (e : m ≃ n) : matrix m m R ≃ₐ[R] matrix n n R :=
{ to_fun    := reindex e e,
  map_mul'  := reindex_linear_equiv_mul R R e e e,
  commutes' := λ r, by simp [algebra_map, algebra.to_ring_hom, minor_smul],
  ..(reindex_linear_equiv R R e e) }

@[simp] lemma reindex_alg_equiv_apply (e : m ≃ n) (M : matrix m m R) :
  reindex_alg_equiv R e M = reindex e e M :=
rfl

@[simp] lemma reindex_alg_equiv_symm (e : m ≃ n) :
  (reindex_alg_equiv R e).symm = reindex_alg_equiv R e.symm :=
rfl

@[simp] lemma reindex_alg_equiv_refl : reindex_alg_equiv R (equiv.refl m) = alg_equiv.refl :=
alg_equiv.ext $ λ _, rfl

lemma reindex_alg_equiv_mul (e : m ≃ n) (M : matrix m m R) (N : matrix m m R) :
  reindex_alg_equiv R e (M ⬝ N) = reindex_alg_equiv R e M ⬝ reindex_alg_equiv R e N :=
(reindex_alg_equiv R e).map_mul M N

end algebra

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_minor_equiv_self`.
-/
lemma det_reindex_linear_equiv_self [comm_ring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) (M : matrix m m R) :
  det (reindex_linear_equiv R R e e M) = det M :=
det_reindex_self e M

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_minor_equiv_self`.
-/
lemma det_reindex_alg_equiv [comm_ring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) (A : matrix m m R) :
  det (reindex_alg_equiv R e A) = det A :=
det_reindex_self e A

end matrix
