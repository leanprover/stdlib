/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import analysis.special_functions.pow
import analysis.normed_space.inner_product
import measure_theory.borel_space

/-!
# Measurability of real and complex functions

We show that most standard real and complex functions are measurable, notably `exp`, `cos`, `sin`,
`cosh`, `sinh`, `log`, `pow`, `arcsin`, `arccos`, `arctan`, and scalar products.
-/

noncomputable theory
open_locale nnreal ennreal

namespace real

lemma measurable_exp : measurable exp := continuous_exp.measurable

lemma measurable_log : measurable log :=
measurable_of_measurable_on_compl_singleton 0 $ continuous.measurable $
  continuous_on_iff_continuous_restrict.1 continuous_on_log

lemma measurable_sin : measurable sin := continuous_sin.measurable

lemma measurable_cos : measurable cos := continuous_cos.measurable

lemma measurable_sinh : measurable sinh := continuous_sinh.measurable

lemma measurable_cosh : measurable cosh := continuous_cosh.measurable

lemma measurable_arcsin : measurable arcsin := continuous_arcsin.measurable

lemma measurable_arccos : measurable arccos := continuous_arccos.measurable

lemma measurable_arctan : measurable arctan := continuous_arctan.measurable

end real

namespace complex

lemma measurable_re : measurable re := continuous_re.measurable

lemma measurable_im : measurable im := continuous_im.measurable

lemma measurable_of_real : measurable (coe : ℝ → ℂ) := continuous_of_real.measurable

lemma measurable_exp : measurable exp := continuous_exp.measurable

lemma measurable_sin : measurable sin := continuous_sin.measurable

lemma measurable_cos : measurable cos := continuous_cos.measurable

lemma measurable_sinh : measurable sinh := continuous_sinh.measurable

lemma measurable_cosh : measurable cosh := continuous_cosh.measurable

lemma measurable_arg : measurable arg :=
have A : measurable (λ x : ℂ, real.arcsin (x.im / x.abs)),
  from real.measurable_arcsin.comp (measurable_im.div measurable_norm),
have B : measurable (λ x : ℂ, real.arcsin ((-x).im / x.abs)),
  from real.measurable_arcsin.comp ((measurable_im.comp measurable_neg).div measurable_norm),
measurable.ite (is_closed_le continuous_const continuous_re).measurable_set A $
  measurable.ite (is_closed_le continuous_const continuous_im).measurable_set
    (B.add_const _) (B.sub_const _)

lemma measurable_log : measurable log :=
(measurable_of_real.comp $ real.measurable_log.comp measurable_norm).add $
  (measurable_of_real.comp measurable_arg).mul_const I

end complex

section real_composition
open real
variables {α : Type*} [measurable_space α] {f : α → ℝ} (hf : measurable f)

lemma measurable.exp : measurable (λ x, real.exp (f x)) :=
real.measurable_exp.comp hf

lemma measurable.log : measurable (λ x, log (f x)) :=
measurable_log.comp hf

lemma measurable.cos : measurable (λ x, real.cos (f x)) :=
real.measurable_cos.comp hf

lemma measurable.sin : measurable (λ x, real.sin (f x)) :=
real.measurable_sin.comp hf

lemma measurable.cosh : measurable (λ x, real.cosh (f x)) :=
real.measurable_cosh.comp hf

lemma measurable.sinh : measurable (λ x, real.sinh (f x)) :=
real.measurable_sinh.comp hf

lemma measurable.arctan : measurable (λ x, arctan (f x)) :=
measurable_arctan.comp hf

lemma measurable.sqrt : measurable (λ x, sqrt (f x)) :=
continuous_sqrt.measurable.comp hf

end real_composition

section complex_composition
open complex
variables {α : Type*} [measurable_space α] {f : α → ℂ} (hf : measurable f)

lemma measurable.cexp : measurable (λ x, complex.exp (f x)) :=
complex.measurable_exp.comp hf

lemma measurable.ccos : measurable (λ x, complex.cos (f x)) :=
complex.measurable_cos.comp hf

lemma measurable.csin : measurable (λ x, complex.sin (f x)) :=
complex.measurable_sin.comp hf

lemma measurable.ccosh : measurable (λ x, complex.cosh (f x)) :=
complex.measurable_cosh.comp hf

lemma measurable.csinh : measurable (λ x, complex.sinh (f x)) :=
complex.measurable_sinh.comp hf

lemma measurable.carg : measurable (λ x, arg (f x)) :=
measurable_arg.comp hf

lemma measurable.clog : measurable (λ x, log (f x)) :=
measurable_log.comp hf

end complex_composition

section pow_instances

instance complex.has_measurable_pow : has_measurable_pow ℂ ℂ :=
⟨measurable.ite (measurable_fst (measurable_set_singleton 0))
  (measurable.ite (measurable_snd (measurable_set_singleton 0)) measurable_one measurable_zero)
  (measurable_fst.clog.mul measurable_snd).cexp⟩

instance real.has_measurable_pow : has_measurable_pow ℝ ℝ :=
⟨complex.measurable_re.comp $ ((complex.measurable_of_real.comp measurable_fst).pow
  (complex.measurable_of_real.comp measurable_snd))⟩

instance nnreal.has_measurable_pow : has_measurable_pow ℝ≥0 ℝ :=
⟨(measurable_fst.coe_nnreal_real.pow measurable_snd).subtype_mk⟩

instance ennreal.has_measurable_pow : has_measurable_pow ℝ≥0∞ ℝ :=
begin
  refine ⟨ennreal.measurable_of_measurable_nnreal_prod _ _⟩,
  { simp_rw ennreal.coe_rpow_def,
    refine measurable.ite _ measurable_const
      (measurable_fst.pow measurable_snd).coe_nnreal_ennreal,
    exact measurable_set.inter (measurable_fst (measurable_set_singleton 0))
      (measurable_snd measurable_set_Iio), },
  { simp_rw ennreal.top_rpow_def,
    refine measurable.ite measurable_set_Ioi measurable_const _,
    exact measurable.ite (measurable_set_singleton 0) measurable_const measurable_const, },
end

end pow_instances

section
variables {α : Type*} {𝕜 : Type*} {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

lemma measurable.inner [measurable_space α] [measurable_space E] [opens_measurable_space E]
  [topological_space.second_countable_topology E] [measurable_space 𝕜] [borel_space 𝕜]
  {f g : α → E} (hf : measurable f) (hg : measurable g) :
  measurable (λ t, ⟪f t, g t⟫) :=
continuous.measurable2 continuous_inner hf hg

lemma ae_measurable.inner [measurable_space α] [measurable_space E] [opens_measurable_space E]
  [topological_space.second_countable_topology E] [measurable_space 𝕜] [borel_space 𝕜]
  {μ : measure_theory.measure α} {f g : α → E} (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ x, ⟪f x, g x⟫) μ :=
begin
  refine ⟨λ x, ⟪hf.mk f x, hg.mk g x⟫, hf.measurable_mk.inner hg.measurable_mk, _⟩,
  refine hf.ae_eq_mk.mp (hg.ae_eq_mk.mono (λ x hxg hxf, _)),
  dsimp only,
  congr,
  { exact hxf, },
  { exact hxg, },
end

end
