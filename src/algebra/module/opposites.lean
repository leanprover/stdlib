/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.module.linear_map

/-!
# Module operations on `Mᵒᵖ`

This file contains definitions that could not be placed into `algebra.opposites` due to import
cycles.
-/

namespace opposite
universes u v

variables (R : Type u) {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M]

/-- `opposite.distrib_mul_action` extends to a `semimodule` -/
instance : semimodule R (opposite M) :=
{ add_smul := λ r₁ r₂ x, unop_injective $ add_smul r₁ r₂ (unop x),
  zero_smul := λ x, unop_injective $ zero_smul _ (unop x),
  ..opposite.distrib_mul_action M R }

/-- The function `op` is a linear equivalence. -/
def op_linear_equiv : M ≃ₗ[R] Mᵒᵖ :=
{ map_smul' := opposite.op_smul, .. op_add_equiv }

@[simp] lemma coe_op_linear_equiv :
  (op_linear_equiv R : M → Mᵒᵖ) = op := rfl
@[simp] lemma coe_op_linear_equiv_symm :
  ((op_linear_equiv R).symm : Mᵒᵖ → M) = unop := rfl

@[simp] lemma coe_op_linear_equiv_to_linear_map :
  ((op_linear_equiv R).to_linear_map : M → Mᵒᵖ) = op := rfl
@[simp] lemma coe_op_linear_equiv_symm_to_linear_map :
  ((op_linear_equiv R).symm.to_linear_map : Mᵒᵖ → M) = unop := rfl

@[simp] lemma op_linear_equiv_to_add_equiv :
  (op_linear_equiv R : M ≃ₗ[R] Mᵒᵖ).to_add_equiv = op_add_equiv := rfl
@[simp] lemma op_linear_equiv_symm_to_add_equiv :
  (op_linear_equiv R : M ≃ₗ[R] Mᵒᵖ).symm.to_add_equiv = op_add_equiv.symm := rfl

end opposite
