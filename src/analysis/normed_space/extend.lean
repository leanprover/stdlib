/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/

import data.complex.is_R_or_C

/-!
# Extending a continuous `ℝ`-linear map to a continuous `𝕜`-linear map

In this file we provide a way to extend a continuous `ℝ`-linear map to a continuous `𝕜`-linear map
in a way that bounds the norm by the norm of the original map, when `𝕜` is either `ℝ` (the
extension is trivial) or `ℂ`. We formulate the extension uniformly, by assuming `is_R_or_C 𝕜`.

We motivate the form of the extension as follows. Note that `fc : F →ₗ[𝕜] 𝕜` is determined fully by
`Re fc`: for all `x : F`, `fc (I • x) = I * fc x`, so `Im (fc x) = -Re (fc (I • x))`. Therefore,
given an `fr : F →ₗ[ℝ] ℝ`, we define `fc x = fr x - fr (I • x) * I`.
-/

open is_R_or_C

variables {𝕜 : Type*} [is_R_or_C 𝕜] {F : Type*} [normed_group F] [normed_space 𝕜 F]
local notation `abs𝕜` := @is_R_or_C.abs 𝕜 _

/-- Extend `fr : F →ₗ[ℝ] ℝ` to `F →ₗ[𝕜] 𝕜` in a way that will also be continuous and have its norm
bounded by `∥fr∥` if `fr` is continuous. -/
noncomputable def linear_map.extend_to_𝕜 (fr : (restrict_scalars ℝ 𝕜 F) →ₗ[ℝ] ℝ) : F →ₗ[𝕜] 𝕜 :=
begin
  let fc : F → 𝕜 := λ x, (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x)),
  have add : ∀ x y : F, fc (x + y) = fc x + fc y,
  { assume x y,
    simp only [fc],
    unfold_coes,
    simp only [smul_add, ring_hom.map_add, ring_hom.to_fun_eq_coe, linear_map.to_fun_eq_coe,
               linear_map.map_add],
    rw mul_add,
    abel, },
  have A : ∀ (c : ℝ) (x : F), (fr ((c : 𝕜) • x) : 𝕜) = (c : 𝕜) * (fr x : 𝕜),
  { assume c x,
    rw [← of_real_mul],
    congr' 1,
    exact fr.map_smul c x },
  have smul_ℝ : ∀ (c : ℝ) (x : F), fc ((c : 𝕜) • x) = (c : 𝕜) * fc x,
  { assume c x,
    simp only [fc, A],
    rw [smul_smul, mul_comm I (c : 𝕜), ← smul_smul, A, mul_sub],
    ring },
  have smul_I : ∀ x : F, fc ((I : 𝕜) • x) = (I : 𝕜) * fc x,
  { assume x,
    simp only [fc],
    cases @I_mul_I_ax 𝕜 _ with h h, { simp [h] },
    rw [mul_sub, ← mul_assoc, smul_smul, h],
    simp only [neg_mul_eq_neg_mul_symm, linear_map.map_neg, one_mul, one_smul,
      mul_neg_eq_neg_mul_symm, of_real_neg, neg_smul, sub_neg_eq_add, add_comm] },
  have smul_𝕜 : ∀ (c : 𝕜) (x : F), fc (c • x) = c • fc x,
  { assume c x,
    rw [← re_add_im c, add_smul, add_smul, add, smul_ℝ, ← smul_smul, smul_ℝ, smul_I, ← mul_assoc],
    refl },
  exact { to_fun := fc, map_add' := add, map_smul' := smul_𝕜 }
end

/-- The norm of the extension is bounded by `∥fr∥`. -/
lemma norm_bound (fr : (restrict_scalars ℝ 𝕜 F) →L[ℝ] ℝ) (x : F) :
  ∥fr.to_linear_map.extend_to_𝕜 x∥ ≤ ∥fr∥ * ∥x∥ :=
begin
  let lm := fr.to_linear_map.extend_to_𝕜,
  -- We aim to find a `t : 𝕜` such that
  -- * `lm (t • x) = fr (t • x)` (so `lm (t • x) = t * lm x ∈ ℝ`)
  -- * `∥lm x∥ = ∥lm (t • x)∥` (so `t.abs` must be 1)
  -- If `lm x ≠ 0`, `(lm x)⁻¹` satisfies the first requirement, and after normalizing, it
  -- satisfies the second.
  -- (If `lm x = 0`, the goal is trivial.)
  classical,
  by_cases h : lm x = 0,
  { rw [h, norm_zero],
    apply mul_nonneg; exact norm_nonneg _ },
  let fx := (lm x)⁻¹,
  let t := fx / (abs𝕜 fx : 𝕜),
  have ht : abs𝕜 t = 1, by field_simp [abs_of_real, of_real_inv, is_R_or_C.abs_inv,
    is_R_or_C.abs_div, is_R_or_C.abs_abs, h],
  have h1 : (fr (t • x) : 𝕜) = lm (t • x),
  { apply ext,
    { simp only [lm, of_real_re, linear_map.extend_to_𝕜, mul_re, I_re, of_real_im, zero_mul,
        linear_map.coe_mk, add_monoid_hom.map_sub, sub_zero, mul_zero],
      refl },
    { symmetry,
      calc im (lm (t • x))
          = im (t * lm x) : by rw [lm.map_smul, smul_eq_mul]
      ... = im ((lm x)⁻¹ / (abs𝕜 (lm x)⁻¹) * lm x) : rfl
      ... = im (1 / (abs𝕜 (lm x)⁻¹ : 𝕜)) : by rw [div_mul_eq_mul_div, inv_mul_cancel h]
      ... = 0 : by rw [← of_real_one, ← of_real_div, of_real_im]
      ... = im (fr (t • x) : 𝕜) : by rw [of_real_im] } },
  calc ∥lm x∥ = abs𝕜 t * ∥lm x∥ : by rw [ht, one_mul]
  ... = ∥t * lm x∥ : by rw [← norm_eq_abs, normed_field.norm_mul]
  ... = ∥lm (t • x)∥ : by rw [←smul_eq_mul, lm.map_smul]
  ... = ∥(fr (t • x) : 𝕜)∥ : by rw h1
  ... = ∥fr (t • x)∥ : by rw [norm_eq_abs, abs_of_real, norm_eq_abs, abs_to_real]
  ... ≤ ∥fr∥ * ∥t • x∥ : continuous_linear_map.le_op_norm _ _
  ... = ∥fr∥ * (∥t∥ * ∥x∥) : by rw norm_smul
  ... ≤ ∥fr∥ * ∥x∥ : by rw [norm_eq_abs, ht, one_mul]
end

/-- Extend `fr : F →L[ℝ] ℝ` to `F →L[𝕜] 𝕜`. -/
noncomputable def continuous_linear_map.extend_to_𝕜 (fr : (restrict_scalars ℝ 𝕜 F) →L[ℝ] ℝ) :
  F →L[𝕜] 𝕜 :=
fr.to_linear_map.extend_to_𝕜.mk_continuous ∥fr∥ (norm_bound _)
