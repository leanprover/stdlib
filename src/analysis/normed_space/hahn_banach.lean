/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import analysis.normed_space.operator_norm
import analysis.normed_space.extend
import analysis.convex.cone
import analysis.convex.topology
import analysis.seminorm
import analysis.specific_limits
import data.complex.is_R_or_C

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

For the concrete cases of `ℝ` and `ℂ`, this is just `∥x∥` and `↑∥x∥`, respectively.
-/
noncomputable def norm' (𝕜 : Type*) [nondiscrete_normed_field 𝕜] [semi_normed_algebra ℝ 𝕜]
  {E : Type*} [semi_normed_group E] (x : E) : 𝕜 :=
algebra_map ℝ 𝕜 ∥x∥

lemma norm'_def (𝕜 : Type*) [nondiscrete_normed_field 𝕜] [semi_normed_algebra ℝ 𝕜]
  {E : Type*} [semi_normed_group E] (x : E) :
  norm' 𝕜 x = (algebra_map ℝ 𝕜 ∥x∥) := rfl

lemma norm_norm'
  (𝕜 : Type*) [nondiscrete_normed_field 𝕜] [semi_normed_algebra ℝ 𝕜]
  (A : Type*) [semi_normed_group A]
  (x : A) : ∥norm' 𝕜 x∥ = ∥x∥ :=
by rw [norm'_def, norm_algebra_map_eq, norm_norm]

@[simp] lemma norm'_eq_zero_iff
  (𝕜 : Type*) [nondiscrete_normed_field 𝕜] [semi_normed_algebra ℝ 𝕜]
  (A : Type*) [normed_group A] (x : A) :
  norm' 𝕜 x = 0 ↔ x = 0 :=
by simp [norm', ← norm_eq_zero, norm_algebra_map_eq]

namespace real
variables {E : Type*} [semi_normed_group E] [semi_normed_space ℝ E]

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

variables {𝕜 : Type*} [is_R_or_C 𝕜] {F : Type*} [semi_normed_group F] [semi_normed_space 𝕜 F]

/-- Hahn-Banach theorem for continuous linear functions over `𝕜` satisyfing `is_R_or_C 𝕜`. -/
theorem exists_extension_norm_eq (p : subspace 𝕜 F) (f : p →L[𝕜] 𝕜) :
  ∃ g : F →L[𝕜] 𝕜, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
  letI : module ℝ F := restrict_scalars.module ℝ 𝕜 F,
  letI : is_scalar_tower ℝ 𝕜 F := restrict_scalars.is_scalar_tower _ _ _,
  letI : semi_normed_space ℝ F := semi_normed_space.restrict_scalars _ 𝕜 _,
  -- Let `fr: p →L[ℝ] ℝ` be the real part of `f`.
  let fr := re_clm.comp (f.restrict_scalars ℝ),
  have fr_apply : ∀ x, fr x = re (f x), by { assume x, refl },
  -- Use the real version to get a norm-preserving extension of `fr`, which
  -- we'll call `g : F →L[ℝ] ℝ`.
  rcases real.exists_extension_norm_eq (p.restrict_scalars ℝ) fr with ⟨g, ⟨hextends, hnormeq⟩⟩,
  -- Now `g` can be extended to the `F →L[𝕜] 𝕜` we need.
  refine ⟨g.extend_to_𝕜, _⟩,
  -- It is an extension of `f`.
  have h : ∀ x : p, g.extend_to_𝕜 x = f x,
  { assume x,
    rw [continuous_linear_map.extend_to_𝕜_apply, ←submodule.coe_smul, hextends, hextends],
    have : (fr x : 𝕜) - I * ↑(fr (I • x)) = (re (f x) : 𝕜) - (I : 𝕜) * (re (f ((I : 𝕜) • x))),
      by refl,
    rw this,
    apply ext,
    { simp only [add_zero, algebra.id.smul_eq_mul, I_re, of_real_im, add_monoid_hom.map_add,
        zero_sub, I_im', zero_mul, of_real_re, eq_self_iff_true, sub_zero, mul_neg_eq_neg_mul_symm,
        of_real_neg, mul_re, mul_zero, sub_neg_eq_add, continuous_linear_map.map_smul] },
    { simp only [algebra.id.smul_eq_mul, I_re, of_real_im, add_monoid_hom.map_add, zero_sub, I_im',
        zero_mul, of_real_re, mul_neg_eq_neg_mul_symm, mul_im, zero_add, of_real_neg, mul_re,
        sub_neg_eq_add, continuous_linear_map.map_smul] } },
  -- And we derive the equality of the norms by bounding on both sides.
  refine ⟨h, le_antisymm _ _⟩,
  { calc ∥g.extend_to_𝕜∥
        ≤ ∥g∥ : g.extend_to_𝕜.op_norm_le_bound g.op_norm_nonneg (norm_bound _)
    ... = ∥fr∥ : hnormeq
    ... ≤ ∥re_clm∥ * ∥f∥ : continuous_linear_map.op_norm_comp_le _ _
    ... = ∥f∥ : by rw [re_clm_norm, one_mul] },
  { exact f.op_norm_le_bound g.extend_to_𝕜.op_norm_nonneg (λ x, h x ▸ g.extend_to_𝕜.le_op_norm x) }
end

end is_R_or_C

section dual_vector
variables (𝕜 : Type v) [is_R_or_C 𝕜]
variables {E : Type u} [normed_group E] [normed_space 𝕜 E]

open continuous_linear_equiv submodule
open_locale classical

lemma coord_norm' (x : E) (h : x ≠ 0) : ∥norm' 𝕜 x • coord 𝕜 x h∥ = 1 :=
by rw [norm_smul, norm_norm', coord_norm, mul_inv_cancel (mt norm_eq_zero.mp h)]

/-- Corollary of Hahn-Banach.  Given a nonzero element `x` of a normed space, there exists an
    element of the dual space, of norm `1`, whose value on `x` is `∥x∥`. -/
theorem exists_dual_vector (x : E) (h : x ≠ 0) :
  ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g x = norm' 𝕜 x :=
begin
  let p : submodule 𝕜 E := 𝕜 ∙ x,
  let f := norm' 𝕜 x • coord 𝕜 x h,
  obtain ⟨g, hg⟩ := exists_extension_norm_eq p f,
  refine ⟨g, _, _⟩,
  { rw [hg.2, coord_norm'] },
  { calc g x = g (⟨x, mem_span_singleton_self x⟩ : 𝕜 ∙ x) : by rw coe_mk
    ... = (norm' 𝕜 x • coord 𝕜 x h) (⟨x, mem_span_singleton_self x⟩ : 𝕜 ∙ x) : by rw ← hg.1
    ... = norm' 𝕜 x : by simp }
end

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, and choosing
    the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' [nontrivial E] (x : E) :
  ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g x = norm' 𝕜 x :=
begin
  by_cases hx : x = 0,
  { obtain ⟨y, hy⟩ := exists_ne (0 : E),
    obtain ⟨g, hg⟩ : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g y = norm' 𝕜 y := exists_dual_vector 𝕜 y hy,
    refine ⟨g, hg.left, _⟩,
    rw [norm'_def, hx, norm_zero, ring_hom.map_zero, continuous_linear_map.map_zero] },
  { exact exists_dual_vector 𝕜 x hx }
end

end dual_vector

section separating
open set

noncomputable theory

variables {E : Type*} [normed_group E] [normed_space ℝ E]

lemma continuous_at_of_exists_open
  (f : E →ₗ[ℝ] ℝ) (hf : ∀ ε, 0 < ε → ∃ (U : set E), (0:E) ∈ U ∧ is_open U ∧ ∀ x ∈ U, ∥f x∥ < ε) :
  continuous_at f (0:E) :=
begin
  intros U hU,
  rw metric.nhds_basis_ball.1 at hU,
  rcases hU with ⟨ε, hε₁, hε₂⟩,
  simp only [linear_map.map_zero] at hε₂,
  simp only [filter.mem_map],
  obtain ⟨V, hV₁, hV₂, hV₃⟩ := hf ε hε₁,
  rw mem_nhds_iff,
  refine ⟨V, λ x hx, hε₂ _, hV₂, hV₁⟩,
  simp only [metric.mem_ball, dist_zero_right],
  apply hV₃ _ hx,
end

/--
Given a set `C` which is a convex neighbourhood of `0` and a point `x₀` outside of it, there is a
continuous linear functional `f` which sends `x₀` to 1 and all of `C` to values strictly below 1.
-/
lemma separate_convex_open_set
  {C : set E} (zero_mem : (0:E) ∈ C) (hC : convex C) (hC₂ : is_open C)
  (x₀ : E) (hx₀ : x₀ ∉ C) :
∃ (f : E →L[ℝ] ℝ), f x₀ = 1 ∧ ∀ x ∈ C, f x < 1 :=
begin
  let f : linear_pmap ℝ E ℝ :=
    linear_pmap.mk_span_singleton x₀ 1 (ne_of_mem_of_not_mem zero_mem hx₀).symm,
  have : f ⟨(1:ℝ) • x₀, by { dsimp, rw submodule.mem_span_singleton, refine ⟨1, rfl⟩ }⟩ = 1,
  { change linear_pmap.mk_span_singleton _ _ _ _ = _,
    rw linear_pmap.mk_span_singleton_apply,
    simp },
  rcases exists_extension_of_le_sublinear f (gauge C) _ _ _ with ⟨φ, hφ₁, hφ₂⟩,
  { refine ⟨⟨φ, _⟩, _, _⟩,
    { refine (φ.to_add_monoid_hom.uniform_continuous_of_continuous_at_zero _).continuous,
      apply continuous_at_of_exists_open,
      intros ε hε,
      refine ⟨(ε • C) ∩ (-ε • C), ⟨_, _⟩, _, _⟩,
      { rw mem_smul_set,
        refine ⟨0, zero_mem, by simp⟩ },
      { rw mem_smul_set,
        refine ⟨0, zero_mem, by simp⟩ },
      { apply is_open.inter (is_open_map_smul' hε.ne' _ hC₂),
        { exact is_open_map_smul' (by linarith) _ hC₂ } },
      { rintro x ⟨hx₁, hx₂⟩,
        rw [real.norm_eq_abs, abs_lt],
        split,
        { rw [neg_lt, ←linear_map.map_neg],
          apply (hφ₂ _).trans_lt,
          have : -ε⁻¹ • x ∈ C,
          { obtain ⟨y, _, rfl⟩ := hx₂,
            simpa [smul_smul, hε.ne'] },
          have := gauge_lt_one_of_mem_of_open hC zero_mem hC₂ (-ε⁻¹ • x) ‹_ ∈ C›,
          simpa [←smul_neg, gauge_mul_nonneg (inv_nonneg.2 hε.le), inv_mul_lt_iff hε] using this },
        { have : ε⁻¹ • x ∈ C,
          { rwa ←mem_smul_set_iff_inv_smul_mem hε.ne' },
          have := gauge_lt_one_of_mem_of_open hC zero_mem hC₂ (ε⁻¹ • x) ‹_›,
          rw [gauge_mul_nonneg (inv_nonneg.2 hε.le), inv_mul_lt_iff hε, mul_one] at this,
          apply (hφ₂ _).trans_lt ‹_› } } },
    { dsimp,
      rw [←‹f ⟨_, _⟩ = 1›, ←hφ₁],
      simp, },
    { intros x hx,
      apply (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_open hC zero_mem hC₂ _ hx) } },
  { intros c hc x,
    apply gauge_mul_nonneg (le_of_lt hc) },
  { intros x y,
    apply gauge_subadditive hC (absorbent_nhds_zero (hC₂.mem_nhds zero_mem)) },
  { rintro ⟨x, hx⟩,
    obtain ⟨y, rfl⟩ := submodule.mem_span_singleton.1 hx,
    rw linear_pmap.mk_span_singleton_apply,
    simp only [mul_one, algebra.id.smul_eq_mul, submodule.coe_mk],
    cases lt_or_le 0 y,
    { rw [gauge_mul_nonneg (le_of_lt h), le_mul_iff_one_le_right h],
      apply one_le_gauge_of_not_mem hC ‹_› ‹_› _ hx₀ },
    apply ‹y ≤ 0›.trans (gauge_nonneg _) }
end

/-- A nonzero continuous linear functional is open. -/
lemma nonzero_linear_map_is_open_map {E : Type*} [add_comm_group E] [topological_space E]
  [topological_add_group E] [module ℝ E] [has_continuous_smul ℝ E]
  (f : E →L[ℝ] ℝ) (hf : f ≠ 0) :
  is_open_map f :=
begin
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0,
  { by_contra h,
    push_neg at h,
    exact hf (continuous_linear_map.ext (λ x, by simp [h]) )},
  intros A hA,
  rw is_open_iff_mem_nhds,
  rintro _ ⟨a, ha, rfl⟩,
  let g : ℝ → E := λ x, a + (x - f a) • (f x₀)⁻¹ • x₀,
  have := (show continuous g, by continuity).is_open_preimage _ ‹is_open A›,
  rw is_open_iff_mem_nhds at this,
  refine filter.mem_sets_of_superset (this (f a) _) (λ x hx, ⟨_, hx, by simp [hx₀]⟩),
  { change _ + _ • _ ∈ A,
    simpa },
end

/--
A version of the Hahn-Banach theorem: given disjoint convex subsets `A,B` where `A` is open, there
is a continuous linear functional which separates them.
-/
theorem geometric_hahn_banach_open {A B : set E}
  (hA₁ : convex A) (hA₂ : is_open A) (hB : convex B) (disj : disjoint A B) :
  ∃ (f : E →L[ℝ] ℝ) (s : ℝ), (∀ a ∈ A, f a < s) ∧ (∀ b ∈ B, s ≤ f b) :=
begin
  rcases A.eq_empty_or_nonempty with (rfl | ⟨a₀, ha₀⟩),
  { refine ⟨0, 0, by simp, λ b hb, by simp⟩ },
  rcases B.eq_empty_or_nonempty with (rfl | ⟨b₀, hb₀⟩),
  { refine ⟨0, 1, λ a ha, by norm_num, by simp⟩ },
  let x₀ := b₀ - a₀,
  let C := {x₀} + A + -B,
  have : (0:E) ∈ C := ⟨_ + a₀, -b₀, add_mem_add rfl ‹_›, neg_mem_neg.2 ‹_›, by simp⟩,
  have : convex C := ((convex_singleton _).add hA₁).add ‹convex B›.neg_preimage,
  have : x₀ ∉ C,
  { intro hx₀,
    simp only [mem_add, mem_singleton_iff, mem_neg, exists_eq_left, exists_exists_and_eq_and,
      exists_and_distrib_left, add_assoc x₀, add_right_eq_self] at hx₀,
    obtain ⟨a, ha, b, hb, _⟩ := hx₀,
    apply disj ⟨ha, _⟩,
    convert hb,
    rwa ←add_eq_zero_iff_eq_neg },
  obtain ⟨f, hf₁, hf₂⟩ := separate_convex_open_set ‹0 ∈ C› ‹_› hA₂.add_left.add_right _ ‹x₀ ∉ C›,
  have : f b₀ = f a₀ + 1,
  { simp [←hf₁] },
  have forall_lt : ∀ (a ∈ A) (b ∈ B), f a < f b,
  { intros a ha b hb,
    have := hf₂ (x₀ + a + -b) (add_mem_add (add_mem_add rfl ha) (neg_mem_neg.2 hb)),
    simp [‹f b₀ = _›] at this,
    linarith },
  refine ⟨f, Inf (f '' B), _, _⟩,
  { suffices : f '' A ⊆ Iio (Inf (f '' B)),
    { intros a ha,
      apply this ⟨_, ha, rfl⟩ },
    rw ←interior_Iic,
    apply interior_maximal,
    { rintro _ ⟨a, ha, rfl⟩,
      apply le_cInf ⟨f b₀, _⟩,
      { rintro _ ⟨b', _, rfl⟩,
        apply (forall_lt _ ‹a ∈ _› _ ‹b' ∈ _›).le },
      { apply mem_image_of_mem _ ‹b₀ ∈ B› } },
    apply nonzero_linear_map_is_open_map _ _ _ hA₂,
    rintro rfl,
    simpa using hf₁ },
  { intros b hb,
    apply cInf_le ⟨f a₀, _⟩ (mem_image_of_mem _ hb),
    rintro _ ⟨b', hb', rfl⟩,
    apply (forall_lt _ ha₀ _ hb').le },
end

theorem geometric_hahn_banach_open_point {A : set E} {x : E}
  (hA₁ : convex A) (hA₂ : is_open A)
  (disj : x ∉ A) :
  ∃ (f : E →L[ℝ] ℝ), (∀ a ∈ A, f a < f x) :=
let ⟨f, s, hA, hx⟩ := geometric_hahn_banach_open hA₁ hA₂ (convex_singleton x)
  (disjoint_singleton_right.2 disj)
  in ⟨f, λ a ha, lt_of_lt_of_le (hA a ha) (hx x (mem_singleton _))⟩

theorem geometric_hahn_banach_point_open {x : E} {B : set E}
  (hB₁ : convex B) (hB₂ : is_open B)
  (disj : x ∉ B) :
  ∃ (f : E →L[ℝ] ℝ), (∀ b ∈ B, f x < f b) :=
let ⟨f, hf⟩ := geometric_hahn_banach_open_point hB₁ hB₂ disj in ⟨-f, by simpa⟩

theorem geometric_hahn_banach_open_open {A B : set E}
  (hA₁ : convex A) (hA₂ : is_open A)
  (hB₁ : convex B) (hB₃ : is_open B)
  (disj : disjoint A B) :
∃ (f : E →L[ℝ] ℝ) (s : ℝ), (∀ a ∈ A, f a < s) ∧ (∀ b ∈ B, s < f b) :=
begin
  rcases A.eq_empty_or_nonempty with (rfl | ⟨a₀, ha₀⟩),
  { refine ⟨0, -1, by simp, λ b hb, by norm_num⟩ },
  rcases B.eq_empty_or_nonempty with (rfl | ⟨b₀, hb₀⟩),
  { refine ⟨0, 1, λ a ha, by norm_num, by simp⟩ },
  obtain ⟨f, s, hf₁, hf₂⟩ := geometric_hahn_banach_open hA₁ hA₂ hB₁ disj,
  have : f ≠ 0,
  { rintro rfl,
    have := hf₁ _ ha₀,
    simp only [continuous_linear_map.zero_apply] at this,
    have := hf₂ _ hb₀,
    simp only [continuous_linear_map.zero_apply] at this,
    linarith },
  have : is_open_map f := nonzero_linear_map_is_open_map _ ‹f ≠ 0›,
  refine ⟨f, s, hf₁, _⟩,
  suffices : f '' B ⊆ Ioi s,
  { intros b hb,
    apply this ⟨b, ‹_›, rfl⟩ },
  rw ←interior_Ici,
  apply interior_maximal,
  { rintro _ ⟨_, _, rfl⟩,
    refine hf₂ _ ‹_› },
  apply ‹is_open_map f› _ hB₃,
end

open filter
open_locale topological_space

/--
If `A,B` are disjoint convex sets, `A` is compact and `B` is closed then we can find open disjoint
convex subsets containing them.
-/
-- TODO: This proof uses the normed space structure of `E`, but it could work for locally convex
-- topological vector spaces: instead of taking the balls around 0 with radius 1/n, we could show
-- there must be some convex neighbourhood `W` of 0 which make `A + W` and `B + W` disjoint?
theorem closed_compact_separate {A B : set E}
  (hA₁ : convex A) (hA₂ : is_compact A) (hB₁ : convex B) (hB₃ : is_closed B) (disj : disjoint A B) :
  ∃ U V, is_open U ∧ is_open V ∧ convex U ∧ convex V ∧ A ⊆ U ∧ B ⊆ V ∧ disjoint U V :=
begin
  have : ∃ (n : ℕ), disjoint (A + metric.ball 0 (n+1)⁻¹) (B + metric.ball 0 (n+1)⁻¹),
  { by_contra h,
    push_neg at h,
    simp only [not_disjoint_iff, set.mem_add, metric.mem_ball, dist_zero_right,
      ←exists_and_distrib_left, ←exists_and_distrib_right, and_assoc] at h,
    choose z f f' g g' h₁ h₂ h₃ h₄ h₅ h₆ using h,
    obtain ⟨w, hw, φ, hφ₁, hφ₂ : tendsto (f ∘ _) _ _⟩ := hA₂.tendsto_subseq h₁,
    have : tendsto (g ∘ φ) at_top (𝓝 w),
    { have : tendsto (f - g) at_top (𝓝 0),
      { suffices : ∀ n, ∥(f - g) n∥ ≤ 2 * (n+1)⁻¹,
        { apply squeeze_zero_norm this,
          rw ←mul_zero (2:ℝ),
          apply tendsto.const_mul (2:ℝ),
          simp_rw inv_eq_one_div,
          apply tendsto_one_div_add_at_top_nhds_0_nat },
        intro n,
        simp only [pi.sub_apply],
        have : f n - g n = g' n - f' n,
        { rw [sub_eq_iff_eq_add', ←add_sub_assoc, h₆, ←h₃, add_sub_cancel] },
        rw this,
        apply le_trans (norm_sub_le _ _) _,
        rw two_mul,
        apply add_le_add (h₅ n).le (h₂ n).le },
      have : tendsto (f ∘ φ - g ∘ φ) at_top (𝓝 0),
      { have : f ∘ φ - g ∘ φ = (f - g) ∘ φ,
        { ext,
          simp },
        rw this,
        apply tendsto.comp ‹tendsto (f - g) at_top _› (strict_mono_tendsto_at_top hφ₁) },
      simpa using tendsto.sub hφ₂ ‹tendsto (f ∘ φ - g ∘ φ) at_top _› },
    have := mem_of_is_closed_sequential ‹is_closed B› (λ n, h₄ (φ n)) this,
    apply disj ⟨hw, ‹w ∈ B›⟩ },
  obtain ⟨n, hn⟩ := this,
  refine ⟨_, _, _, _, hA₁.add _, hB₁.add _, _, _, hn⟩,
  { exact metric.is_open_ball.add_left },
  { exact metric.is_open_ball.add_left },
  { exact convex_ball 0 _ },
  { exact convex_ball 0 _ },
  { suffices : A + {0} ⊆ A + metric.ball (0:E) (n+1)⁻¹,
    { simpa },
    apply add_subset_add (set.subset.refl _),
    simp only [metric.mem_ball, norm_zero, dist_zero_left, singleton_subset_iff, inv_pos],
    norm_cast,
    simp },
  { suffices : B + {0} ⊆ B + metric.ball (0:E) (n+1)⁻¹,
    { simpa },
    apply add_subset_add (set.subset.refl _),
    simp only [metric.mem_ball, norm_zero, dist_zero_left, singleton_subset_iff, inv_pos],
    norm_cast,
    simp },
end

/--
A version of the Hahn-Banach theorem: given disjoint convex subsets `A,B` where `A` is compact,
and `B` is closed, there is a continuous linear functional which strongly separates them.
-/
theorem geometric_hahn_banach_compact_closed {A B : set E}
  (hA₁ : convex A) (hA₂ : is_compact A)
  (hB₁ : convex B) (hB₂ : is_closed B)
  (disj : disjoint A B) :
  ∃ (f : E →L[ℝ] ℝ) (s t : ℝ), (∀ a ∈ A, f a < s) ∧ s < t ∧ (∀ b ∈ B, t < f b) :=
begin
  rcases A.eq_empty_or_nonempty with (rfl | hA),
  { refine ⟨0, -2, -1, by simp, by norm_num, λ b hb, by norm_num⟩ },
  rcases B.eq_empty_or_nonempty with (h | hB),
  { rw h,
    exact ⟨0, 1, 2, λ a ha, by norm_num, by norm_num, by simp⟩ },
  obtain ⟨U, V, hU, hV, hU₁, hV₁, AU, BV, disj'⟩ := closed_compact_separate hA₁ hA₂ hB₁ hB₂ disj,
  obtain ⟨f, s, hf₁, hf₂⟩ := geometric_hahn_banach_open_open hU₁ hU hV₁ hV disj',
  obtain ⟨x, hx₁, hx₂⟩ := hA₂.exists_forall_ge hA f.continuous.continuous_on,
  have : Sup (f '' A) = f x,
  { apply le_antisymm (cSup_le (hA.image f) (by simpa)),
    refine le_cSup ⟨f x, by simpa [upper_bounds]⟩ ⟨_, hx₁, rfl⟩ },
  have : f x < s := hf₁ x (AU hx₁),
  exact ⟨f, (f x + s)/2, s, λ a ha, by linarith [hx₂ a ha], by linarith, λ b hb, hf₂ b (BV hb)⟩,
end

/--
A version of the Hahn-Banach theorem: given disjoint convex subsets `A,B` where `A` is closed,
and `B` is compact, there is a continuous linear functional which strongly separates them.
-/
theorem geometric_hahn_banach_closed_compact {A B : set E}
  (hA₁ : convex A) (hA₂ : is_closed A)
  (hB₁ : convex B) (hB₂ : is_compact B)
  (disj : disjoint A B) :
  ∃ (f : E →L[ℝ] ℝ) (s t : ℝ), (∀ a ∈ A, f a < s) ∧ s < t ∧ (∀ b ∈ B, t < f b) :=
let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed hB₁ hB₂ hA₁ hA₂ disj.symm in
⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩

theorem geometric_hahn_banach_point_closed {x : E} {B : set E}
  (hB₁ : convex B) (hB₂ : is_closed B)
  (disj : x ∉ B) :
  ∃ (f : E →L[ℝ] ℝ) (s : ℝ), f x < s ∧ (∀ b ∈ B, s < f b) :=
let ⟨f, s, t, ha, hst, hb⟩ := geometric_hahn_banach_compact_closed (convex_singleton x)
  is_compact_singleton hB₁ hB₂ (disjoint_singleton_left.2 disj)
  in ⟨f, t, lt_trans (ha x (mem_singleton _)) hst, hb⟩

theorem geometric_hahn_banach_closed_point {A : set E} {x : E}
  (hA₁ : convex A) (hA₂ : is_closed A)
  (disj : x ∉ A) :
  ∃ (f : E →L[ℝ] ℝ) (s : ℝ), (∀ a ∈ A, f a < s) ∧ s < f x :=
let ⟨f, s, t, ha, hst, hb⟩ := geometric_hahn_banach_closed_compact hA₁ hA₂ (convex_singleton x)
  is_compact_singleton (disjoint_singleton_right.2 disj)
  in ⟨f, s, ha, lt_trans hst (hb x (mem_singleton _))⟩

theorem geometric_hahn_banach_point_point {x y : E} (hxy : x ≠ y) :
  ∃ (f : E →L[ℝ] ℝ), f x < f y :=
begin
  have : disjoint ({x} : set E) {y},
  { simp [hxy.symm] },
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) is_compact_singleton
      (convex_singleton y) is_closed_singleton this,
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩,
end

end separating
