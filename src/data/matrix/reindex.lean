/-
Copyright (c) 2021 Filippo Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo Nuccio
-/
import data.matrix.basic
import linear_algebra.matrix.reindex

/-!
# Matrices
-/
universes v

open matrix

variables {m n o : Type*} [fintype m] [fintype n] [fintype o]
variables {m₁ n₁ o₁ : Type*} [fintype m₁] [fintype n₁] [fintype o₁]
variables {R : Type*}{α : Type v}

namespace matrix

/-- equivalences between matrix ((m × n) × o) ((m₁ × n₁) × o₁) R and
 matrix (m × n × o) (m₁ × n₁ × o₁) R -/
def index_assoc : matrix ((m × n) × o) ((m₁ × n₁) × o₁) R ≃ matrix (m × n × o) (m₁ × n₁ × o₁) R :=
matrix.reindex (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _)

def linear_equiv_index_assoc :
  matrix ((m × n) × o) ((m₁ × n₁) × o₁) R ≃ₗ[R] matrix (m × n × o) (m₁ × n₁ × o₁) R :=
-- { to_fun := λ A, reindex (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _) A,
--   map_add' := λ _ _, by simp only [reindex_apply, minor_add, pi.add_apply],
--   map_smul' := λ _ _, by simp only [reindex_apply, minor_smul, pi.smul_apply],
--   inv_fun := λ A, reindex (equiv.prod_assoc _ _ _).symm (equiv.prod_assoc _ _ _).symm A,
--   left_inv := λ _, by simp only [equiv.symm_symm, reindex_apply, minor_minor, minor_id_id,
--     equiv.symm_comp_self],
--   right_inv := λ _, by simp only [equiv.symm_symm, reindex_apply, minor_minor, minor_id_id,
--     equiv.self_comp_symm],
--   }
matrix.reindex_linear_equiv (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _)

end matrix
