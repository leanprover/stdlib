/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Wieser
-/

import linear_algebra.tensor_product
import linear_algebra.multilinear

/-! # Tensor product of multlinear maps

This file provides a single definition, `multilinear_map.dom_coprod_pi`, a more general
version of `multilinear_map.dom_coprod`.
-/

open_locale tensor_product

namespace sum.elim

instance {ι₁ ι₂ : Type*}
  {M : ι₁ → Type*} [∀ i, add_comm_monoid (M i)]
  {N : ι₂ → Type*} [∀ i, add_comm_monoid (N i)]
  (i : ι₁ ⊕ ι₂)
  : add_comm_monoid (i.elim M N) := by cases i; { dsimp, apply_instance }

instance {ι₁ ι₂ : Type*} [decidable_eq ι₁] [decidable_eq ι₂]
  (R : Type*) [semiring R]
  {M : ι₁ → Type*} [∀ i, add_comm_monoid (M i)] [∀ i, semimodule R (M i)]
  {N : ι₂ → Type*} [∀ i, add_comm_monoid (N i)] [∀ i, semimodule R (N i)]
  (i : ι₁ ⊕ ι₂)
  : semimodule R (i.elim M N) := by cases i; { dsimp, apply_instance }

end sum.elim

namespace multilinear_map

universes u

variables {ι₁ ι₂ : Type*} [decidable_eq ι₁] [decidable_eq ι₂]
  (R : Type*) [comm_semiring R]
  {M : ι₁ → Type u} [∀ i, add_comm_monoid (M i)] [∀ i, semimodule R (M i)]
  {N : ι₂ → Type u} [∀ i, add_comm_monoid (N i)] [∀ i, semimodule R (N i)]
  {M' : Type*} [add_comm_monoid M'] [semimodule R M']
  {N' : Type*} [add_comm_monoid N'] [semimodule R N']

def dom_coprod_pi
  (a : multilinear_map R M M') (b : multilinear_map R N N') :
  multilinear_map R (λ (i : ι₁ ⊕ ι₂), i.elim M N) (M' ⊗[R] N')
  :=
{ to_fun := λ v, a (λ i, v (sum.inl i)) ⊗ₜ b (λ i, v (sum.inr i)),
  map_add' := λ v i p q, begin
    cases i,
    {
      have : ∀ {α β : Type*} (a : α),
        (sum.inl a : α ⊕ β) ∉ set.range (@sum.inr α β) := by simp,
      iterate 3 {
        rw [function.update_comp_eq_of_injective' _ sum.injective_inl,
            function.update_comp_eq_of_not_mem_range' _ _ (this i)],},
      rw [a.map_add, tensor_product.add_tmul],
    },
    {
      have : ∀ {α β : Type*} (b : β),
        (sum.inr b : α ⊕ β) ∉ set.range (@sum.inl α β) := by simp,
      iterate 3 {
        rw [function.update_comp_eq_of_injective' _ sum.injective_inr,
            function.update_comp_eq_of_not_mem_range' _ _ (this i)],},
      rw [b.map_add, tensor_product.tmul_add],
    }
  end,
  map_smul' := λ v i c p, begin
    cases i,
    {
      have : ∀ {α β : Type*} (a : α),
        (sum.inl a : α ⊕ β) ∉ set.range (@sum.inr α β) := by simp,
      iterate 2 {
        rw [function.update_comp_eq_of_injective' _ sum.injective_inl,
            function.update_comp_eq_of_not_mem_range' _ _ (this i)],},
      rw [a.map_smul, tensor_product.smul_tmul'],
    },
    {
      have : ∀ {α β : Type*} (b : β),
        (sum.inr b : α ⊕ β) ∉ set.range (@sum.inl α β) := by simp,
      iterate 2 {
        rw [function.update_comp_eq_of_injective' _ sum.injective_inr,
            function.update_comp_eq_of_not_mem_range' _ _ (this i)]},
      rw [b.map_smul, tensor_product.tmul_smul],
    },
  end }

/-- Given a tensor product of two multilinear maps, produce a single multilinear map over the
sum of their indices into the tensor product of their codomains. -/
def dom_coprod_pi' :
  multilinear_map R M M' ⊗ multilinear_map R N N' →ₗ[R]
  multilinear_map R (λ (i : ι₁ ⊕ ι₂), i.elim M N) (M' ⊗[R] N') :=
tensor_product.lift $ linear_map.mk₂ R (dom_coprod_pi R)
  (λ m₁ m₂ n, by { ext, simp [dom_coprod_pi, tensor_product.add_tmul] })
  (λ c m n,   by { ext, simp [dom_coprod_pi, tensor_product.smul_tmul'] })
  (λ m n₁ n₂, by { ext, simp [dom_coprod_pi, tensor_product.tmul_add] })
  (λ c m n,   by { ext, simp [dom_coprod_pi, tensor_product.tmul_smul] })

@[simp] lemma dom_coprod_pi_apply_tmul (a : multilinear_map R M M') (b : multilinear_map R N N') (v) :
  dom_coprod_pi' R (a ⊗ₜ b) v = a (λ i, v (sum.inl i)) ⊗ₜ b (λ i, v (sum.inr i)) := rfl

end multilinear_map
