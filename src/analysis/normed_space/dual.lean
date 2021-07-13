/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis
-/
import analysis.normed_space.hahn_banach
import analysis.normed_space.inner_product

/-!
# The topological dual of a normed space

In this file we define the topological dual of a normed space, and the bounded linear map from
a normed space into its double dual.

We also prove that, for base field `𝕜` with `[is_R_or_C 𝕜]`, this map is an isometry.

We then consider inner product spaces, with base field over `ℝ` (the corresponding results for `ℂ`
will require the definition of conjugate-linear maps). We define `to_dual_map`, a continuous linear
map from `E` to its dual, which maps an element `x` of the space to `λ y, ⟪x, y⟫`. We check
(`to_dual_map_isometry`) that this map is an isometry onto its image, and particular is injective.
We also define `to_dual'` as the function taking taking a vector to its dual for a base field `𝕜`
with `[is_R_or_C 𝕜]`; this is a function and not a linear map.

Finally, under the hypothesis of completeness (i.e., for Hilbert spaces), we prove the Fréchet-Riesz
representation (`to_dual_map_eq_top`), which states the surjectivity: every element of the dual
of a Hilbert space `E` has the form `λ u, ⟪x, u⟫` for some `x : E`.  This permits the map
`to_dual_map` to be upgraded to an (isometric) continuous linear equivalence, `to_dual`, between a
Hilbert space and its dual.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `semi_normed_group` and we specialize to `normed_group` when needed.

## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*]
  [EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/

noncomputable theory
open_locale classical
universes u v

namespace normed_space

section general
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables (E : Type*) [semi_normed_group E] [normed_space 𝕜 E]
variables (F : Type*) [normed_group F] [normed_space 𝕜 F]

/-- The topological dual of a seminormed space `E`. -/
@[derive [has_coe_to_fun, semi_normed_group, normed_space 𝕜]] def dual := E →L[𝕜] 𝕜

instance : inhabited (dual 𝕜 E) := ⟨0⟩

instance : normed_group (dual 𝕜 F) := continuous_linear_map.to_normed_group

instance : normed_space 𝕜 (dual 𝕜 F) := continuous_linear_map.to_normed_space

/-- The inclusion of a normed space in its double (topological) dual. -/
def inclusion_in_double_dual' (x : E) : (dual 𝕜 (dual 𝕜 E)) :=
linear_map.mk_continuous
  { to_fun := λ f, f x,
    map_add'    := by simp,
    map_smul'   := by simp }
  ∥x∥
  (λ f, by { rw mul_comm, exact f.le_op_norm x } )

@[simp] lemma dual_def (x : E) (f : dual 𝕜 E) :
  ((inclusion_in_double_dual' 𝕜 E) x) f = f x := rfl

lemma double_dual_bound (x : E) : ∥(inclusion_in_double_dual' 𝕜 E) x∥ ≤ ∥x∥ :=
begin
  apply continuous_linear_map.op_norm_le_bound,
  { simp },
  { intros f, rw mul_comm, exact f.le_op_norm x, }
end

/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusion_in_double_dual : E →L[𝕜] (dual 𝕜 (dual 𝕜 E)) :=
linear_map.mk_continuous
  { to_fun := λ (x : E), (inclusion_in_double_dual' 𝕜 E) x,
    map_add'    := λ x y, by { ext, simp },
    map_smul'   := λ (c : 𝕜) x, by { ext, simp } }
  1
  (λ x, by { convert double_dual_bound _ _ _, simp } )

end general

section bidual_isometry

variables (𝕜 : Type v) [is_R_or_C 𝕜]
  {E : Type u} [normed_group E] [normed_space 𝕜 E]

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
    Compare `continuous_linear_map.op_norm_le_bound`. -/
lemma norm_le_dual_bound (x : E) {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ (f : dual 𝕜 E), ∥f x∥ ≤ M * ∥f∥) :
  ∥x∥ ≤ M :=
begin
  classical,
  by_cases h : x = 0,
  { simp only [h, hMp, norm_zero] },
  { obtain ⟨f, hf⟩ : ∃ g : E →L[𝕜] 𝕜, _ := exists_dual_vector 𝕜 x h,
    calc ∥x∥ = ∥norm' 𝕜 x∥ : (norm_norm' _ _ _).symm
    ... = ∥f x∥ : by rw hf.2
    ... ≤ M * ∥f∥ : hM f
    ... = M : by rw [hf.1, mul_one] }
end

lemma eq_zero_of_forall_dual_eq_zero {x : E} (h : ∀ f : dual 𝕜 E, f x = (0 : 𝕜)) : x = 0 :=
norm_eq_zero.mp (le_antisymm (norm_le_dual_bound 𝕜 x le_rfl (λ f, by simp [h f])) (norm_nonneg _))

lemma eq_zero_iff_forall_dual_eq_zero (x : E) : x = 0 ↔ ∀ g : dual 𝕜 E, g x = 0 :=
⟨λ hx, by simp [hx], λ h, eq_zero_of_forall_dual_eq_zero 𝕜 h⟩

lemma eq_iff_forall_dual_eq {x y : E} :
  x = y ↔ ∀ g : dual 𝕜 E, g x = g y :=
begin
  rw [← sub_eq_zero, eq_zero_iff_forall_dual_eq_zero 𝕜 (x - y)],
  simp [sub_eq_zero],
end

/-- The inclusion of a normed space in its double dual is an isometry onto its image.-/
lemma inclusion_in_double_dual_isometry (x : E) : ∥inclusion_in_double_dual 𝕜 E x∥ = ∥x∥ :=
begin
  apply le_antisymm,
  { exact double_dual_bound 𝕜 E x },
  { rw continuous_linear_map.norm_def,
    apply real.lb_le_Inf _ continuous_linear_map.bounds_nonempty,
    rintros c ⟨hc1, hc2⟩,
    exact norm_le_dual_bound 𝕜 x hc1 hc2 },
end

end bidual_isometry

end normed_space

namespace inner_product_space
open is_R_or_C continuous_linear_map

section is_R_or_C

variables (𝕜 : Type*)
variables {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y
local postfix `†`:90 := @is_R_or_C.conj 𝕜 _

/--
Given some `x` in an inner product space, we can define its dual as the continuous linear map
`λ y, ⟪x, y⟫`. Consider using `to_dual` or `to_dual_map` instead in the real case.
-/
def to_dual' : E →+ normed_space.dual 𝕜 E :=
{ to_fun := λ x, linear_map.mk_continuous
  { to_fun := λ y, ⟪x, y⟫,
    map_add' := λ _ _, inner_add_right,
    map_smul' := λ _ _, inner_smul_right }
  ∥x∥
  (λ y, by { rw [is_R_or_C.norm_eq_abs], exact abs_inner_le_norm _ _ }),
  map_zero' := by { ext z, simp },
  map_add' := λ x y, by { ext z, simp [inner_add_left] } }

@[simp] lemma to_dual'_apply {x y : E} : to_dual' 𝕜 x y = ⟪x, y⟫ := rfl

/-- In an inner product space, the norm of the dual of a vector `x` is `∥x∥` -/
@[simp] lemma norm_to_dual'_apply (x : E) : ∥to_dual' 𝕜 x∥ = ∥x∥ :=
begin
  refine le_antisymm _ _,
  { exact linear_map.mk_continuous_norm_le _ (norm_nonneg _) _ },
  { cases eq_or_lt_of_le (norm_nonneg x) with h h,
    { have : x = 0 := norm_eq_zero.mp (eq.symm h),
      simp [this] },
    { refine (mul_le_mul_right h).mp _,
      calc ∥x∥ * ∥x∥ = ∥x∥ ^ 2 : by ring
      ... = re ⟪x, x⟫ : norm_sq_eq_inner _
      ... ≤ abs ⟪x, x⟫ : re_le_abs _
      ... = ∥to_dual' 𝕜 x x∥ : by simp [norm_eq_abs]
      ... ≤ ∥to_dual' 𝕜 x∥ * ∥x∥ : le_op_norm (to_dual' 𝕜 x) x } }
end

variables (E)

lemma to_dual'_isometry : isometry (@to_dual' 𝕜 E _ _) :=
add_monoid_hom.isometry_of_norm _ (norm_to_dual'_apply 𝕜)

/--
Fréchet-Riesz representation: any `ℓ` in the dual of a Hilbert space `E` is of the form
`λ u, ⟪y, u⟫` for some `y : E`, i.e. `to_dual'` is surjective.
-/
lemma to_dual'_surjective [complete_space E] : function.surjective (@to_dual' 𝕜 E _ _) :=
begin
  intros ℓ,
  set Y := ker ℓ with hY,
  by_cases htriv : Y = ⊤,
  { have hℓ : ℓ = 0,
    { have h' := linear_map.ker_eq_top.mp htriv,
      rw [←coe_zero] at h',
      apply coe_injective,
      exact h' },
    exact ⟨0, by simp [hℓ]⟩ },
  { have Ycomplete := is_complete_ker ℓ,
    rw [← submodule.orthogonal_eq_bot_iff Ycomplete, ←hY] at htriv,
    change Yᗮ ≠ ⊥ at htriv,
    rw [submodule.ne_bot_iff] at htriv,
    obtain ⟨z : E, hz : z ∈ Yᗮ, z_ne_0 : z ≠ 0⟩ := htriv,
    refine ⟨((ℓ z)† / ⟪z, z⟫) • z, _⟩,
    ext x,
    have h₁ : (ℓ z) • x - (ℓ x) • z ∈ Y,
    { rw [mem_ker, map_sub, map_smul, map_smul, algebra.id.smul_eq_mul, algebra.id.smul_eq_mul,
          mul_comm],
      exact sub_self (ℓ x * ℓ z) },
    have h₂ : (ℓ z) * ⟪z, x⟫ = (ℓ x) * ⟪z, z⟫,
    { have h₃ := calc
        0    = ⟪z, (ℓ z) • x - (ℓ x) • z⟫       : by { rw [(Y.mem_orthogonal' z).mp hz], exact h₁ }
         ... = ⟪z, (ℓ z) • x⟫ - ⟪z, (ℓ x) • z⟫  : by rw [inner_sub_right]
         ... = (ℓ z) * ⟪z, x⟫ - (ℓ x) * ⟪z, z⟫  : by simp [inner_smul_right],
      exact sub_eq_zero.mp (eq.symm h₃) },
    have h₄ := calc
      ⟪((ℓ z)† / ⟪z, z⟫) • z, x⟫ = (ℓ z) / ⟪z, z⟫ * ⟪z, x⟫
            : by simp [inner_smul_left, conj_div, conj_conj]
                            ... = (ℓ z) * ⟪z, x⟫ / ⟪z, z⟫
            : by rw [←div_mul_eq_mul_div]
                            ... = (ℓ x) * ⟪z, z⟫ / ⟪z, z⟫
            : by rw [h₂]
                            ... = ℓ x
            : begin
                have : ⟪z, z⟫ ≠ 0,
                { change z = 0 → false at z_ne_0,
                  rwa ←inner_self_eq_zero at z_ne_0 },
                field_simp [this]
              end,
    exact h₄ }
end

end is_R_or_C

section real

variables {F : Type*} [inner_product_space ℝ F]

/-- In a real inner product space `F`, the function that takes a vector `x` in `F` to its dual
`λ y, ⟪x, y⟫` is a continuous linear map. If the space is complete (i.e. is a Hilbert space),
consider using `to_dual` instead. -/
-- TODO extend to `is_R_or_C` (requires a definition of conjugate linear maps)
def to_dual_map : F →L[ℝ] (normed_space.dual ℝ F) :=
linear_map.mk_continuous
  { to_fun := to_dual' ℝ,
    map_add' := λ x y, by { ext, simp [inner_add_left] },
    map_smul' := λ c x, by { ext, simp [inner_smul_left] } }
  1
  (λ x, by simp only [norm_to_dual'_apply, one_mul, linear_map.coe_mk])

@[simp] lemma to_dual_map_apply {x y : F} : to_dual_map x y = ⟪x, y⟫_ℝ := rfl

/-- In an inner product space, the norm of the dual of a vector `x` is `∥x∥` -/
@[simp] lemma norm_to_dual_map_apply (x : F) : ∥to_dual_map x∥ = ∥x∥ := norm_to_dual'_apply _ _

lemma to_dual_map_isometry : isometry (@to_dual_map F _) :=
add_monoid_hom.isometry_of_norm _ norm_to_dual_map_apply

lemma to_dual_map_injective : function.injective (@to_dual_map F _) :=
(@to_dual_map_isometry F _).injective

@[simp] lemma ker_to_dual_map : (@to_dual_map F _).ker = ⊥ :=
linear_map.ker_eq_bot.mpr to_dual_map_injective

@[simp] lemma to_dual_map_eq_iff_eq {x y : F} : to_dual_map x = to_dual_map y ↔ x = y :=
((linear_map.ker_eq_bot).mp (@ker_to_dual_map F _)).eq_iff

variables [complete_space F]

/--
Fréchet-Riesz representation: any `ℓ` in the dual of a real Hilbert space `F` is of the form
`λ u, ⟪y, u⟫` for some `y` in `F`.  See `inner_product_space.to_dual` for the continuous linear
equivalence thus induced.
-/
-- TODO extend to `is_R_or_C` (requires a definition of conjugate linear maps)
lemma range_to_dual_map : (@to_dual_map F _).range = ⊤ :=
linear_map.range_eq_top.mpr (to_dual'_surjective ℝ F)

/--
Fréchet-Riesz representation: If `F` is a Hilbert space, the function that takes a vector in `F` to
its dual is a continuous linear equivalence.  -/
def to_dual : F ≃L[ℝ] (normed_space.dual ℝ F) :=
continuous_linear_equiv.of_isometry to_dual_map.to_linear_map to_dual_map_isometry range_to_dual_map

/--
Fréchet-Riesz representation: If `F` is a Hilbert space, the function that takes a vector in `F` to
its dual is an isometry.  -/
def isometric.to_dual : F ≃ᵢ normed_space.dual ℝ F :=
{ to_equiv := to_dual.to_linear_equiv.to_equiv,
  isometry_to_fun := to_dual'_isometry ℝ F}

@[simp] lemma to_dual_apply {x y : F} : to_dual x y = ⟪x, y⟫_ℝ := rfl

@[simp] lemma to_dual_eq_iff_eq {x y : F} : to_dual x = to_dual y ↔ x = y :=
(@to_dual F _ _).injective.eq_iff

lemma to_dual_eq_iff_eq' {x x' : F} : (∀ y : F, ⟪x, y⟫_ℝ = ⟪x', y⟫_ℝ) ↔ x = x' :=
begin
  split,
  { intros h,
    have : to_dual x = to_dual x' → x = x' := to_dual_eq_iff_eq.mp,
    apply this,
    simp_rw [←to_dual_apply] at h,
    ext z,
    exact h z },
  { rintros rfl y,
    refl }
end

@[simp] lemma norm_to_dual_apply (x : F) : ∥to_dual x∥ = ∥x∥ := norm_to_dual_map_apply x

/-- In a Hilbert space, the norm of a vector in the dual space is the norm of its corresponding
primal vector. -/
lemma norm_to_dual_symm_apply (ℓ : normed_space.dual ℝ F) : ∥to_dual.symm ℓ∥ = ∥ℓ∥ :=
begin
  have : ℓ = to_dual (to_dual.symm ℓ) := by simp only [continuous_linear_equiv.apply_symm_apply],
  conv_rhs { rw [this] },
  refine eq.symm (norm_to_dual_apply _),
end

end real

end inner_product_space
