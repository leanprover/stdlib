/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import analysis.normed_space.extend
import analysis.convex.cone

/-!
# Hahn-Banach theorem

In this file we prove a version of Hahn-Banach theorem for continuous linear
functions on normed spaces over `ℝ` and `ℂ`.

In order to state and prove its corollaries uniformly, we prove the statements for a field `𝕜`
satisfying `is_R_or_C 𝕜`.

In this setting, `exists_dual_vector` states that, for any nonzero `x`, there exists a continuous
linear form `g` of norm `1` with `g x = ∥x∥` (where the norm has to be interpreted as an element
of `𝕜`).

-/

universes u v

/--
The norm of `x` as an element of `𝕜` (a normed algebra over `ℝ`). This is needed in particular to
state equalities of the form `g x = norm' 𝕜 x` when `g` is a linear function.

For the concrete cases of `ℝ` and `𝕜`, this is just `∥x∥` and `↑∥x∥`, respectively.
-/
noncomputable def norm' (𝕜 : Type*) [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜]
  {E : Type*} [normed_group E] (x : E) : 𝕜 :=
algebra_map ℝ 𝕜 ∥x∥

lemma norm'_def (𝕜 : Type*) [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜]
  {E : Type*} [normed_group E] (x : E) :
  norm' 𝕜 x = (algebra_map ℝ 𝕜 ∥x∥) := rfl

lemma norm_norm'
  (𝕜 : Type*) [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜]
  (A : Type*) [normed_group A]
  (x : A) : ∥norm' 𝕜 x∥ = ∥x∥ :=
by rw [norm'_def, norm_algebra_map_eq, norm_norm]

namespace real
variables {E : Type*} [normed_group E] [normed_space ℝ E]

/-- Hahn-Banach theorem for continuous linear functions over `ℝ`. -/
theorem exists_extension_norm_eq (p : subspace ℝ E) (f : p →L[ℝ] ℝ) :
  ∃ g : E →L[ℝ] ℝ, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
  rcases exists_extension_of_le_sublinear ⟨p, f⟩ (λ x, ∥f∥ * ∥x∥)
    (λ c hc x, by simp only [norm_smul c x, real.norm_eq_abs, abs_of_pos hc, mul_left_comm])
    (λ x y, _) (λ x, le_trans (le_abs_self _) (f.le_op_norm _))
    with ⟨g, g_eq, g_le⟩,
  set g' := g.mk_continuous (∥f∥)
    (λ x, abs_le.2 ⟨neg_le.1 $ g.map_neg x ▸ norm_neg x ▸ g_le (-x), g_le x⟩),
  { refine ⟨g', g_eq, _⟩,
    { apply le_antisymm (g.mk_continuous_norm_le (norm_nonneg f) _),
      refine f.op_norm_le_bound (norm_nonneg _) (λ x, _),
      dsimp at g_eq,
      rw ← g_eq,
      apply g'.le_op_norm } },
  { simp only [← mul_add],
    exact mul_le_mul_of_nonneg_left (norm_add_le x y) (norm_nonneg f) }
end

end real

section is_R_or_C
open is_R_or_C

variables {𝕜 : Type*} [is_R_or_C 𝕜] {F : Type*} [normed_group F] [normed_space 𝕜 F]

/-- Hahn-Banach theorem for continuous linear functions over `𝕜` satisyfing `is_R_or_C 𝕜`. -/
theorem exists_extension_norm_eq (p : subspace 𝕜 F) (f : p →L[𝕜] 𝕜) :
  ∃ g : F →L[𝕜] 𝕜, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
  letI : module ℝ F := restrict_scalars.semimodule ℝ 𝕜 F,
  letI : is_scalar_tower ℝ 𝕜 F := restrict_scalars.is_scalar_tower _ _ _,
  letI : normed_space ℝ F := normed_space.restrict_scalars _ 𝕜 _,
  letI : normed_space ℝ p := (by apply_instance : normed_space ℝ (submodule.restrict_scalars ℝ p)),
  -- Let `fr: p →L[ℝ] ℝ` be the real part of `f`.
  let fr := re_clm.comp (f.restrict_scalars ℝ),
  have fr_apply : ∀ x, fr x = re (f x) := λ x, rfl,
  -- Use the real version to get a norm-preserving extension of `fr`, which
  -- we'll call `g : F →L[ℝ] ℝ`.
  rcases real.exists_extension_norm_eq (p.restrict_scalars ℝ) fr with ⟨g, ⟨hextends, hnormeq⟩⟩,
  -- Now `g` can be extended to the `F →L[𝕜] 𝕜` we need.
  use g.extend_to_𝕜,
  -- It is an extension of `f`.
  have h : ∀ x : p, g.extend_to_𝕜 x = f x,
  { assume x,
    change (g (x : F) : 𝕜) - (I : 𝕜) * g ((((I : 𝕜) • x) : p) : F) = f x,
    rw [hextends, hextends],
    change (re (f x) : 𝕜) - (I : 𝕜) * (re (f ((I : 𝕜) • x))) = f x,
    apply ext,
    { simp only [add_zero, algebra.id.smul_eq_mul, I_re, of_real_im, add_monoid_hom.map_add,
        zero_sub, I_im', zero_mul, of_real_re, eq_self_iff_true, sub_zero, mul_neg_eq_neg_mul_symm,
        of_real_neg, mul_re, mul_zero, sub_neg_eq_add, continuous_linear_map.map_smul] },
    { simp only [algebra.id.smul_eq_mul, I_re, of_real_im, add_monoid_hom.map_add, zero_sub, I_im',
        zero_mul, of_real_re, mul_neg_eq_neg_mul_symm, mul_im, zero_add, of_real_neg, mul_re,
        sub_neg_eq_add, continuous_linear_map.map_smul] } },
  refine ⟨h, _⟩,
  -- And we derive the equality of the norms by bounding on both sides.
  refine le_antisymm _ _,
  { calc ∥g.extend_to_𝕜∥
        ≤ ∥g∥ : g.extend_to_𝕜.op_norm_le_bound g.op_norm_nonneg (norm_bound _)
    ... = ∥fr∥ : hnormeq
    ... ≤ ∥re_clm∥ * ∥f∥ : continuous_linear_map.op_norm_comp_le _ _
    ... = ∥f∥ : by rw [norm_re_clm, one_mul] },
  { exact f.op_norm_le_bound g.extend_to_𝕜.op_norm_nonneg (λ x, h x ▸ g.extend_to_𝕜.le_op_norm x) },
end

end is_R_or_C

section dual_vector
variables {𝕜 : Type v} [is_R_or_C 𝕜]
variables {E : Type u} [normed_group E] [normed_space 𝕜 E]

open continuous_linear_equiv submodule
open_locale classical

lemma coord_norm' (x : E) (h : x ≠ 0) : ∥norm' 𝕜 x • coord 𝕜 x h∥ = 1 :=
by rw [norm_smul, norm_norm', coord_norm, mul_inv_cancel (mt norm_eq_zero.mp h)]

/-- Corollary of Hahn-Banach.  Given a nonzero element `x` of a normed space, there exists an
    element of the dual space, of norm `1`, whose value on `x` is `∥x∥`. -/
theorem exists_dual_vector (x : E) (h : x ≠ 0) : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g x = norm' 𝕜 x :=
begin
  let p : submodule 𝕜 E := 𝕜 ∙ x,
  let f := norm' 𝕜 x • coord 𝕜 x h,
  obtain ⟨g, hg⟩ := exists_extension_norm_eq p f,
  use g, split,
  { rw [hg.2, coord_norm'] },
  { calc g x = g (⟨x, mem_span_singleton_self x⟩ : 𝕜 ∙ x) : by rw coe_mk
    ... = (norm' 𝕜 x • coord 𝕜 x h) (⟨x, mem_span_singleton_self x⟩ : 𝕜 ∙ x) : by rw ← hg.1
    ... = norm' 𝕜 x : by simp [coord_self] }
end

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, and choosing
    the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' [nontrivial E] (x : E) :
  ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g x = norm' 𝕜 x :=
begin
  by_cases hx : x = 0,
  { obtain ⟨y, hy⟩ := exists_ne (0 : E),
    obtain ⟨g, hg⟩ : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g y = norm' 𝕜 y := exists_dual_vector y hy,
    refine ⟨g, hg.left, _⟩,
    rw [norm'_def, hx, norm_zero, ring_hom.map_zero, continuous_linear_map.map_zero] },
  { exact exists_dual_vector x hx }
end

end dual_vector
