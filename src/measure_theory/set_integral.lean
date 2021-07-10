/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import measure_theory.integrable_on
import measure_theory.bochner_integration

/-!
# Set integral

In this file we prove some properties of `∫ x in s, f x ∂μ`. Recall that this notation
is defined as `∫ x, f x ∂(μ.restrict s)`. In `integral_indicator` we prove that for a measurable
function `f` and a measurable set `s` this definition coincides with another natural definition:
`∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ`, where `indicator s f x` is equal to `f x` for `x ∈ s`
and is zero otherwise.

Since `∫ x in s, f x ∂μ` is a notation, one can rewrite or apply any theorem about `∫ x, f x ∂μ`
directly. In this file we prove some theorems about dependence of `∫ x in s, f x ∂μ` on `s`, e.g.
`integral_union`, `integral_empty`, `integral_univ`.

We use the property `integrable_on f s μ := integrable f (μ.restrict s)`, defined in
`measure_theory.integrable_on`. We also defined in that same file a predicate
`integrable_at_filter (f : α → E) (l : filter α) (μ : measure α)` saying that `f` is integrable at
some set `s ∈ l`.

Finally, we prove a version of the
[Fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for set integral, see `filter.tendsto.integral_sub_linear_is_o_ae` and its corollaries.
Namely, consider a measurably generated filter `l`, a measure `μ` finite at this filter, and
a function `f` that has a finite limit `c` at `l ⊓ μ.ae`. Then `∫ x in s, f x ∂μ = μ s • c + o(μ s)`
as `s` tends to `l.lift' powerset`, i.e. for any `ε>0` there exists `t ∈ l` such that
`∥∫ x in s, f x ∂μ - μ s • c∥ ≤ ε * μ s` whenever `s ⊆ t`. We also formulate a version of this
theorem for a locally finite measure `μ` and a function `f` continuous at a point `a`.

## Notation

We provide the following notations for expressing the integral of a function on a set :
* `∫ a in s, f a ∂μ` is `measure_theory.integral (μ.restrict s) f`
* `∫ a in s, f a` is `∫ a in s, f a ∂volume`

Note that the set notations are defined in the file `measure_theory/bochner_integration`,
but we reference them here because all theorems about set integrals are in this file.

## TODO

The file ends with over a hundred lines of commented out code. This is the old contents of this file
using the `indicator` approach to the definition of `∫ x in s, f x ∂μ`. This code should be
migrated to the new definition.

-/

noncomputable theory
open set filter topological_space measure_theory function
open_locale classical topological_space interval big_operators filter ennreal measure_theory

variables {α β E F : Type*} [measurable_space α]

namespace measure_theory

section normed_group

variables [normed_group E] [measurable_space E] {f g : α → E} {s t : set α} {μ ν : measure α}
  {l l' : filter α} [borel_space E] [second_countable_topology E]

variables [complete_space E] [normed_space ℝ E]


lemma set_integral_congr_ae (hs : measurable_set s) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
  ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
integral_congr_ae ((ae_restrict_iff' hs).2 h)

lemma set_integral_congr (hs : measurable_set s) (h : eq_on f g s) :
  ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
set_integral_congr_ae hs $ eventually_of_forall h

lemma integral_union (hst : disjoint s t) (hs : measurable_set s) (ht : measurable_set t)
  (hfs : integrable_on f s μ) (hft : integrable_on f t μ) :
  ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ :=
by simp only [integrable_on, measure.restrict_union hst hs ht, integral_add_measure hfs hft]

lemma integral_empty : ∫ x in ∅, f x ∂μ = 0 := by rw [measure.restrict_empty, integral_zero_measure]

lemma integral_univ : ∫ x in univ, f x ∂μ = ∫ x, f x ∂μ := by rw [measure.restrict_univ]

lemma integral_add_compl (hs : measurable_set s) (hfi : integrable f μ) :
  ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ :=
by rw [← integral_union (@disjoint_compl_right (set α) _ _) hs hs.compl
    hfi.integrable_on hfi.integrable_on, union_compl_self, integral_univ]

/-- For a function `f` and a measurable set `s`, the integral of `indicator s f`
over the whole space is equal to `∫ x in s, f x ∂μ` defined as `∫ x, f x ∂(μ.restrict s)`. -/
lemma integral_indicator (hs : measurable_set s) :
  ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  by_cases hf : ae_measurable f (μ.restrict s), swap,
  { rw integral_non_ae_measurable hf,
    rw [← ae_measurable_indicator_iff hs] at hf,
    exact integral_non_ae_measurable hf },
  by_cases hfi : integrable_on f s μ, swap,
  { rwa [integral_undef, integral_undef],
    rwa integrable_indicator_iff hs },
  calc ∫ x, indicator s f x ∂μ = ∫ x in s, indicator s f x ∂μ + ∫ x in sᶜ, indicator s f x ∂μ :
    (integral_add_compl hs (hfi.indicator hs)).symm
  ... = ∫ x in s, f x ∂μ + ∫ x in sᶜ, 0 ∂μ :
    congr_arg2 (+) (integral_congr_ae (indicator_ae_eq_restrict hs))
      (integral_congr_ae (indicator_ae_eq_restrict_compl hs))
  ... = ∫ x in s, f x ∂μ : by simp
end

lemma set_integral_const (c : E) : ∫ x in s, c ∂μ = (μ s).to_real • c :=
by rw [integral_const, measure.restrict_apply_univ]

@[simp]
lemma integral_indicator_const (e : E) ⦃s : set α⦄ (s_meas : measurable_set s) :
  ∫ (a : α), s.indicator (λ (x : α), e) a ∂μ = (μ s).to_real • e :=
by rw [integral_indicator s_meas, ← set_integral_const]

lemma set_integral_map {β} [measurable_space β] {g : α → β} {f : β → E} {s : set β}
  (hs : measurable_set s) (hf : ae_measurable f (measure.map g μ)) (hg : measurable g) :
  ∫ y in s, f y ∂(measure.map g μ) = ∫ x in g ⁻¹' s, f (g x) ∂μ :=
begin
  rw [measure.restrict_map hg hs, integral_map hg (hf.mono_measure _)],
  exact measure.map_mono g measure.restrict_le_self
end

lemma set_integral_map_of_closed_embedding [topological_space α] [borel_space α]
  {β} [measurable_space β] [topological_space β] [borel_space β]
  {g : α → β} {f : β → E} {s : set β} (hs : measurable_set s) (hg : closed_embedding g) :
  ∫ y in s, f y ∂(measure.map g μ) = ∫ x in g ⁻¹' s, f (g x) ∂μ :=
by rw [measure.restrict_map hg.measurable hs, integral_map_of_closed_embedding hg]

lemma norm_set_integral_le_of_norm_le_const_ae {C : ℝ} (hs : μ s < ∞)
  (hC : ∀ᵐ x ∂μ.restrict s, ∥f x∥ ≤ C) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
begin
  rw ← measure.restrict_apply_univ at *,
  haveI : finite_measure (μ.restrict s) := ⟨‹_›⟩,
  exact norm_integral_le_of_norm_le_const hC
end

lemma norm_set_integral_le_of_norm_le_const_ae' {C : ℝ} (hs : μ s < ∞)
  (hC : ∀ᵐ x ∂μ, x ∈ s → ∥f x∥ ≤ C) (hfm : ae_measurable f (μ.restrict s)) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
begin
  apply norm_set_integral_le_of_norm_le_const_ae hs,
  have A : ∀ᵐ (x : α) ∂μ, x ∈ s → ∥ae_measurable.mk f hfm x∥ ≤ C,
  { filter_upwards [hC, hfm.ae_mem_imp_eq_mk],
    assume a h1 h2 h3,
    rw [← h2 h3],
    exact h1 h3 },
  have B : measurable_set {x | ∥(hfm.mk f) x∥ ≤ C} := hfm.measurable_mk.norm measurable_set_Iic,
  filter_upwards [hfm.ae_eq_mk, (ae_restrict_iff B).2 A],
  assume a h1 h2,
  rwa h1
end

lemma norm_set_integral_le_of_norm_le_const_ae'' {C : ℝ} (hs : μ s < ∞) (hsm : measurable_set s)
  (hC : ∀ᵐ x ∂μ, x ∈ s → ∥f x∥ ≤ C) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
norm_set_integral_le_of_norm_le_const_ae hs $ by rwa [ae_restrict_eq hsm, eventually_inf_principal]

lemma norm_set_integral_le_of_norm_le_const {C : ℝ} (hs : μ s < ∞)
  (hC : ∀ x ∈ s, ∥f x∥ ≤ C) (hfm : ae_measurable f (μ.restrict s)) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
norm_set_integral_le_of_norm_le_const_ae' hs (eventually_of_forall hC) hfm

lemma norm_set_integral_le_of_norm_le_const' {C : ℝ} (hs : μ s < ∞) (hsm : measurable_set s)
  (hC : ∀ x ∈ s, ∥f x∥ ≤ C) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
norm_set_integral_le_of_norm_le_const_ae'' hs hsm $ eventually_of_forall hC

lemma set_integral_eq_zero_iff_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f)
  (hfi : integrable_on f s μ) :
  ∫ x in s, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict s] 0 :=
integral_eq_zero_iff_of_nonneg_ae hf hfi

lemma set_integral_pos_iff_support_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f)
  (hfi : integrable_on f s μ) :
  0 < ∫ x in s, f x ∂μ ↔ 0 < μ (support f ∩ s) :=
begin
  rw [integral_pos_iff_support_of_nonneg_ae hf hfi, restrict_apply_of_null_measurable_set],
  exact hfi.ae_measurable.null_measurable_set (measurable_set_singleton 0).compl
end

lemma set_integral_trim {α} {m m0 : measurable_space α} {μ : measure α} (hm : m ≤ m0) {f : α → E}
  (hf_meas : @measurable _ _ m _ f) {s : set α} (hs : @measurable_set α m s) :
  ∫ x in s, f x ∂μ = @integral α E m _ _ _ _ _ _ (@measure.restrict _ m (μ.trim hm) s) f :=
by rwa [integral_trim hm hf_meas, restrict_trim hm μ]

end normed_group

section mono

variables {μ : measure α} {f g : α → ℝ} {s : set α}
  (hf : integrable_on f s μ) (hg : integrable_on g s μ)

lemma set_integral_mono_ae_restrict (h : f ≤ᵐ[μ.restrict s] g) :
  ∫ a in s, f a ∂μ ≤ ∫ a in s, g a ∂μ :=
integral_mono_ae hf hg h

lemma set_integral_mono_ae (h : f ≤ᵐ[μ] g) :
  ∫ a in s, f a ∂μ ≤ ∫ a in s, g a ∂μ :=
set_integral_mono_ae_restrict hf hg (ae_restrict_of_ae h)

lemma set_integral_mono_on (hs : measurable_set s) (h : ∀ x ∈ s, f x ≤ g x) :
  ∫ a in s, f a ∂μ ≤ ∫ a in s, g a ∂μ :=
set_integral_mono_ae_restrict hf hg
  (by simp [hs, eventually_le, eventually_inf_principal, ae_of_all _ h])

lemma set_integral_mono (h : f ≤ g) :
  ∫ a in s, f a ∂μ ≤ ∫ a in s, g a ∂μ :=
integral_mono hf hg h

end mono

section nonneg

variables {μ : measure α} {f : α → ℝ} {s : set α}

lemma set_integral_nonneg_of_ae_restrict (hf : 0 ≤ᵐ[μ.restrict s] f) :
  (0:ℝ) ≤ (∫ a in s, f a ∂μ) :=
integral_nonneg_of_ae hf

lemma set_integral_nonneg_of_ae (hf : 0 ≤ᵐ[μ] f) : (0:ℝ) ≤ (∫ a in s, f a ∂μ) :=
set_integral_nonneg_of_ae_restrict (ae_restrict_of_ae hf)

lemma set_integral_nonneg (hs : measurable_set s) (hf : ∀ a, a ∈ s → 0 ≤ f a) :
  (0:ℝ) ≤ (∫ a in s, f a ∂μ) :=
set_integral_nonneg_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))

end nonneg

lemma set_integral_mono_set {α : Type*} [measurable_space α] {μ : measure α}
  {s t : set α} {f : α → ℝ} (hfi : integrable f μ) (hf : 0 ≤ᵐ[μ] f) (hst : s ≤ᵐ[μ] t) :
  ∫ x in s, f x ∂μ ≤ ∫ x in t, f x ∂μ :=
begin
  repeat { rw integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hf)
            (hfi.1.mono_measure measure.restrict_le_self) },
  rw ennreal.to_real_le_to_real
    (ne_of_lt $ (has_finite_integral_iff_of_real (ae_restrict_of_ae hf)).mp hfi.integrable_on.2)
    (ne_of_lt $ (has_finite_integral_iff_of_real (ae_restrict_of_ae hf)).mp hfi.integrable_on.2),
  exact (lintegral_mono_set' hst),
end


section continuous_set_integral
/-! ### Continuity of the set integral

We prove that for any set `s`, the function `λ f : α →₁[μ] E, ∫ x in s, f x ∂μ` is continuous. -/

variables [normed_group E] [measurable_space E] [second_countable_topology E] [borel_space E]
  {𝕜 : Type*} [is_R_or_C 𝕜] [measurable_space 𝕜]
  [normed_group F] [measurable_space F] [second_countable_topology F] [borel_space F]
  [normed_space 𝕜 F]
  {p : ℝ≥0∞} {μ : measure α}

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.mem_ℒp f).restrict s).to_Lp f`. This map is additive. -/
lemma Lp_to_Lp_restrict_add (f g : Lp E p μ) (s : set α) :
  ((Lp.mem_ℒp (f + g)).restrict s).to_Lp ⇑(f + g)
    = ((Lp.mem_ℒp f).restrict s).to_Lp f + ((Lp.mem_ℒp g).restrict s).to_Lp g :=
begin
  ext1,
  refine (ae_restrict_of_ae (Lp.coe_fn_add f g)).mp _,
  refine (Lp.coe_fn_add (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s))
    (mem_ℒp.to_Lp g ((Lp.mem_ℒp g).restrict s))).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp g).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (f+g)).restrict s)).mono (λ x hx1 hx2 hx3 hx4 hx5, _),
  rw [hx4, hx1, pi.add_apply, hx2, hx3, hx5, pi.add_apply],
end

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.mem_ℒp f).restrict s).to_Lp f`. This map commutes with scalar multiplication. -/
lemma Lp_to_Lp_restrict_smul [opens_measurable_space 𝕜] (c : 𝕜) (f : Lp F p μ) (s : set α) :
  ((Lp.mem_ℒp (c • f)).restrict s).to_Lp ⇑(c • f) = c • (((Lp.mem_ℒp f).restrict s).to_Lp f) :=
begin
  ext1,
  refine (ae_restrict_of_ae (Lp.coe_fn_smul c f)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (c • f)).restrict s)).mp _,
  refine (Lp.coe_fn_smul c (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s))).mono
    (λ x hx1 hx2 hx3 hx4, _),
  rw [hx2, hx1, pi.smul_apply, hx3, hx4, pi.smul_apply],
end

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.mem_ℒp f).restrict s).to_Lp f`. This map is non-expansive. -/
lemma norm_Lp_to_Lp_restrict_le (s : set α) (f : Lp E p μ) :
  ∥((Lp.mem_ℒp f).restrict s).to_Lp f∥ ≤ ∥f∥ :=
begin
  rw [Lp.norm_def, Lp.norm_def, ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _)],
  refine (le_of_eq _).trans (snorm_mono_measure _ measure.restrict_le_self),
  { exact s, },
  exact snorm_congr_ae (mem_ℒp.coe_fn_to_Lp _),
end

variables (α F 𝕜)
/-- Continuous linear map sending a function of `Lp F p μ` to the same function in
`Lp F p (μ.restrict s)`. -/
def Lp_to_Lp_restrict_clm [borel_space 𝕜] (μ : measure α) (p : ℝ≥0∞) [hp : fact (1 ≤ p)]
  (s : set α) :
  Lp F p μ →L[𝕜] Lp F p (μ.restrict s) :=
@linear_map.mk_continuous 𝕜 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _
  ⟨λ f, mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s), λ f g, Lp_to_Lp_restrict_add f g s,
    λ c f, Lp_to_Lp_restrict_smul c f s⟩
  1 (by { intro f, rw one_mul, exact norm_Lp_to_Lp_restrict_le s f, })

variables {α F 𝕜}

variables (𝕜)
lemma Lp_to_Lp_restrict_clm_coe_fn [borel_space 𝕜] [hp : fact (1 ≤ p)] (s : set α) (f : Lp F p μ) :
  Lp_to_Lp_restrict_clm α F 𝕜 μ p s f =ᵐ[μ.restrict s] f :=
mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)
variables {𝕜}

@[continuity]
lemma continuous_set_integral [normed_space ℝ E] [complete_space E] (s : set α) :
  continuous (λ f : α →₁[μ] E, ∫ x in s, f x ∂μ) :=
begin
  haveI : fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩,
  have h_comp : (λ f : α →₁[μ] E, ∫ x in s, f x ∂μ)
    = (integral (μ.restrict s)) ∘ (λ f, Lp_to_Lp_restrict_clm α E ℝ μ 1 s f),
  { ext1 f,
    rw [function.comp_apply, integral_congr_ae (Lp_to_Lp_restrict_clm_coe_fn ℝ s f)], },
  rw h_comp,
  exact continuous_integral.comp (Lp_to_Lp_restrict_clm α E ℝ μ 1 s).continuous,
end

end continuous_set_integral


end measure_theory

open measure_theory asymptotics metric

variables {ι : Type*} [measurable_space E] [normed_group E]

/-- Fundamental theorem of calculus for set integrals: if `μ` is a measure that is finite at a
filter `l` and `f` is a measurable function that has a finite limit `b` at `l ⊓ μ.ae`, then `∫ x in
s i, f x ∂μ = μ (s i) • b + o(μ (s i))` at a filter `li` provided that `s i` tends to `l.lift'
powerset` along `li`. Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in the
actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
lemma filter.tendsto.integral_sub_linear_is_o_ae
  [normed_space ℝ E] [second_countable_topology E] [complete_space E] [borel_space E]
  {μ : measure α} {l : filter α} [l.is_measurably_generated]
  {f : α → E} {b : E} (h : tendsto f (l ⊓ μ.ae) (𝓝 b))
  (hfm : measurable_at_filter f l μ) (hμ : μ.finite_at_filter l)
  {s : ι → set α} {li : filter ι} (hs : tendsto s li (l.lift' powerset))
  (m : ι → ℝ := λ i, (μ (s i)).to_real)
  (hsμ : (λ i, (μ (s i)).to_real) =ᶠ[li] m . tactic.interactive.refl) :
  is_o (λ i, ∫ x in s i, f x ∂μ - m i • b) m li :=
begin
  suffices : is_o (λ s, ∫ x in s, f x ∂μ - (μ s).to_real • b) (λ s, (μ s).to_real)
    (l.lift' powerset),
    from (this.comp_tendsto hs).congr' (hsμ.mono $ λ a ha, ha ▸ rfl) hsμ,
  refine is_o_iff.2 (λ ε ε₀, _),
  have : ∀ᶠ s in l.lift' powerset, ∀ᶠ x in μ.ae, x ∈ s → f x ∈ closed_ball b ε :=
    eventually_lift'_powerset_eventually.2 (h.eventually $ closed_ball_mem_nhds _ ε₀),
  filter_upwards [hμ.eventually, (hμ.integrable_at_filter_of_tendsto_ae hfm h).eventually,
    hfm.eventually, this],
  simp only [mem_closed_ball, dist_eq_norm],
  intros s hμs h_integrable hfm h_norm,
  rw [← set_integral_const, ← integral_sub h_integrable (integrable_on_const.2 $ or.inr hμs),
    real.norm_eq_abs, abs_of_nonneg ennreal.to_real_nonneg],
  exact norm_set_integral_le_of_norm_le_const_ae' hμs h_norm (hfm.sub ae_measurable_const)
end

/-- Fundamental theorem of calculus for set integrals, `nhds_within` version: if `μ` is a locally
finite measure and `f` is an almost everywhere measurable function that is continuous at a point `a`
within a measurable set `t`, then `∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at a filter `li`
provided that `s i` tends to `(𝓝[t] a).lift' powerset` along `li`.  Since `μ (s i)` is an `ℝ≥0∞`
number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
lemma continuous_within_at.integral_sub_linear_is_o_ae
  [topological_space α] [opens_measurable_space α]
  [normed_space ℝ E] [second_countable_topology E] [complete_space E] [borel_space E]
  {μ : measure α} [locally_finite_measure μ] {a : α} {t : set α}
  {f : α → E} (ha : continuous_within_at f t a) (ht : measurable_set t)
  (hfm : measurable_at_filter f (𝓝[t] a) μ)
  {s : ι → set α} {li : filter ι} (hs : tendsto s li ((𝓝[t] a).lift' powerset))
  (m : ι → ℝ := λ i, (μ (s i)).to_real)
  (hsμ : (λ i, (μ (s i)).to_real) =ᶠ[li] m . tactic.interactive.refl) :
  is_o (λ i, ∫ x in s i, f x ∂μ - m i • f a) m li :=
by haveI : (𝓝[t] a).is_measurably_generated := ht.nhds_within_is_measurably_generated _;
exact (ha.mono_left inf_le_left).integral_sub_linear_is_o_ae
  hfm (μ.finite_at_nhds_within a t) hs m hsμ

/-- Fundamental theorem of calculus for set integrals, `nhds` version: if `μ` is a locally finite
measure and `f` is an almost everywhere measurable function that is continuous at a point `a`, then
`∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at `li` provided that `s` tends to `(𝓝 a).lift'
powerset` along `li.  Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in the
actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
lemma continuous_at.integral_sub_linear_is_o_ae
  [topological_space α] [opens_measurable_space α]
  [normed_space ℝ E] [second_countable_topology E] [complete_space E] [borel_space E]
  {μ : measure α} [locally_finite_measure μ] {a : α}
  {f : α → E} (ha : continuous_at f a) (hfm : measurable_at_filter f (𝓝 a) μ)
  {s : ι → set α} {li : filter ι} (hs : tendsto s li ((𝓝 a).lift' powerset))
  (m : ι → ℝ := λ i, (μ (s i)).to_real)
  (hsμ : (λ i, (μ (s i)).to_real) =ᶠ[li] m . tactic.interactive.refl) :
  is_o (λ i, ∫ x in s i, f x ∂μ - m i • f a) m li :=
(ha.mono_left inf_le_left).integral_sub_linear_is_o_ae hfm (μ.finite_at_nhds a) hs m hsμ

/-- If a function is continuous on an open set `s`, then it is measurable at the filter `𝓝 x` for
  all `x ∈ s`. -/
lemma continuous_on.measurable_at_filter
  [topological_space α] [opens_measurable_space α] [borel_space E]
  {f : α → E} {s : set α} {μ : measure α} (hs : is_open s) (hf : continuous_on f s) :
  ∀ x ∈ s, measurable_at_filter f (𝓝 x) μ :=
λ x hx, ⟨s, is_open.mem_nhds hs hx, hf.ae_measurable hs.measurable_set⟩

lemma continuous_at.measurable_at_filter
  [topological_space α] [opens_measurable_space α] [borel_space E]
  {f : α → E} {s : set α} {μ : measure α} (hs : is_open s) (hf : ∀ x ∈ s, continuous_at f x) :
  ∀ x ∈ s, measurable_at_filter f (𝓝 x) μ :=
continuous_on.measurable_at_filter hs $ continuous_at.continuous_on hf

/-- Fundamental theorem of calculus for set integrals, `nhds_within` version: if `μ` is a locally
finite measure, `f` is continuous on a measurable set `t`, and `a ∈ t`, then `∫ x in (s i), f x ∂μ =
μ (s i) • f a + o(μ (s i))` at `li` provided that `s i` tends to `(𝓝[t] a).lift' powerset` along
`li`.  Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
lemma continuous_on.integral_sub_linear_is_o_ae
  [topological_space α] [opens_measurable_space α]
  [normed_space ℝ E] [second_countable_topology E] [complete_space E] [borel_space E]
  {μ : measure α} [locally_finite_measure μ] {a : α} {t : set α}
  {f : α → E} (hft : continuous_on f t) (ha : a ∈ t) (ht : measurable_set t)
  {s : ι → set α} {li : filter ι} (hs : tendsto s li ((𝓝[t] a).lift' powerset))
  (m : ι → ℝ := λ i, (μ (s i)).to_real)
  (hsμ : (λ i, (μ (s i)).to_real) =ᶠ[li] m . tactic.interactive.refl) :
  is_o (λ i, ∫ x in s i, f x ∂μ - m i • f a) m li :=
(hft a ha).integral_sub_linear_is_o_ae ht ⟨t, self_mem_nhds_within, hft.ae_measurable ht⟩ hs m hsμ

section
/-! ### Continuous linear maps composed with integration

The goal of this section is to prove that integration commutes with continuous linear maps.
This holds for simple functions. The general result follows from the continuity of all involved
operations on the space `L¹`. Note that composition by a continuous linear map on `L¹` is not just
the composition, as we are dealing with classes of functions, but it has already been defined
as `continuous_linear_map.comp_Lp`. We take advantage of this construction here.
-/

variables {μ : measure α} [normed_space ℝ E]
variables [normed_group F] [normed_space ℝ F]
variables {p : ennreal}

local attribute [instance] fact_one_le_one_ennreal

namespace continuous_linear_map

variables [measurable_space F] [borel_space F]

variables [second_countable_topology F] [complete_space F]
[borel_space E] [second_countable_topology E]

lemma integral_comp_Lp (L : E →L[ℝ] F) (φ : Lp E p μ) :
  ∫ a, (L.comp_Lp φ) a ∂μ = ∫ a, L (φ a) ∂μ :=
integral_congr_ae $ coe_fn_comp_Lp _ _

lemma continuous_integral_comp_L1 (L : E →L[ℝ] F) :
  continuous (λ (φ : α →₁[μ] E), ∫ (a : α), L (φ a) ∂μ) :=
begin
  rw ← funext L.integral_comp_Lp,
  exact continuous_integral.comp (L.comp_LpL 1 μ).continuous
end

variables [complete_space E]

lemma integral_comp_comm (L : E →L[ℝ] F) {φ : α → E} (φ_int : integrable φ μ) :
  ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ) :=
begin
  apply integrable.induction (λ φ, ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ)),
  { intros e s s_meas s_finite,
    rw [integral_indicator_const e s_meas, continuous_linear_map.map_smul,
        ← integral_indicator_const (L e) s_meas],
    congr' 1 with a,
    rw set.indicator_comp_of_zero L.map_zero },
  { intros f g H f_int g_int hf hg,
    simp [L.map_add, integral_add f_int g_int,
      integral_add (L.integrable_comp f_int) (L.integrable_comp g_int), hf, hg] },
  { exact is_closed_eq L.continuous_integral_comp_L1 (L.continuous.comp continuous_integral) },
  { intros f g hfg f_int hf,
    convert hf using 1 ; clear hf,
    { exact integral_congr_ae (hfg.fun_comp L).symm },
    { rw integral_congr_ae hfg.symm } },
  all_goals { assumption }
end

lemma integral_apply {H : Type*} [normed_group H] [normed_space ℝ H]
  [second_countable_topology $ H →L[ℝ] E] {φ : α → H →L[ℝ] E} (φ_int : integrable φ μ) (v : H) :
  (∫ a, φ a ∂μ) v = ∫ a, φ a v ∂μ :=
((continuous_linear_map.apply ℝ E v).integral_comp_comm φ_int).symm

lemma integral_comp_comm' (L : E →L[ℝ] F) {K} (hL : antilipschitz_with K L) (φ : α → E) :
  ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ) :=
begin
  by_cases h : integrable φ μ,
  { exact integral_comp_comm L h },
  have : ¬ (integrable (L ∘ φ) μ),
    by rwa lipschitz_with.integrable_comp_iff_of_antilipschitz L.lipschitz hL (L.map_zero),
  simp [integral_undef, h, this]
end

lemma integral_comp_L1_comm (L : E →L[ℝ] F) (φ : α →₁[μ] E) : ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ) :=
L.integral_comp_comm (L1.integrable_coe_fn φ)

end continuous_linear_map

namespace linear_isometry

variables [measurable_space F] [borel_space F] [complete_space E]
[second_countable_topology F] [complete_space F]
[borel_space E] [second_countable_topology E]

lemma integral_comp_comm (L : E →ₗᵢ[ℝ] F) (φ : α → E) :
  ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ) :=
L.to_continuous_linear_map.integral_comp_comm' L.antilipschitz _

end linear_isometry

variables [borel_space E] [second_countable_topology E] [complete_space E]
  [measurable_space F] [borel_space F] [second_countable_topology F] [complete_space F]

@[norm_cast] lemma integral_of_real {𝕜 : Type*} [is_R_or_C 𝕜] [measurable_space 𝕜] [borel_space 𝕜]
  {f : α → ℝ} :
  ∫ a, (f a : 𝕜) ∂μ = ↑∫ a, f a ∂μ :=
linear_isometry.integral_comp_comm (@is_R_or_C.of_real_li 𝕜 _) f

lemma integral_conj {𝕜 : Type*} [is_R_or_C 𝕜] [measurable_space 𝕜] [borel_space 𝕜] {f : α → 𝕜} :
  ∫ a, is_R_or_C.conj (f a) ∂μ = is_R_or_C.conj ∫ a, f a ∂μ :=
(@is_R_or_C.conj_lie 𝕜 _).to_linear_isometry.integral_comp_comm f

lemma fst_integral {f : α → E × F} (hf : integrable f μ) :
  (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ :=
((continuous_linear_map.fst ℝ E F).integral_comp_comm hf).symm

lemma snd_integral {f : α → E × F} (hf : integrable f μ) :
  (∫ x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ :=
((continuous_linear_map.snd ℝ E F).integral_comp_comm hf).symm

lemma integral_pair {f : α → E} {g : α → F} (hf : integrable f μ) (hg : integrable g μ) :
  ∫ x, (f x, g x) ∂μ = (∫ x, f x ∂μ, ∫ x, g x ∂μ) :=
have _ := hf.prod_mk hg, prod.ext (fst_integral this) (snd_integral this)

lemma integral_smul_const (f : α → ℝ) (c : E) :
  ∫ x, f x • c ∂μ = (∫ x, f x ∂μ) • c :=
begin
  by_cases hf : integrable f μ,
  { exact ((continuous_linear_map.id ℝ ℝ).smul_right c).integral_comp_comm hf },
  { by_cases hc : c = 0,
    { simp only [hc, integral_zero, smul_zero] },
    rw [integral_undef hf, integral_undef, zero_smul],
    simp_rw [integrable_smul_const hc, hf, not_false_iff] }
end

end

/-
namespace integrable

variables [measurable_space α] [measurable_space β] [normed_group E]

protected lemma measure_mono

end integrable

end measure_theory

section integral_on
variables [measurable_space α]
  [normed_group β] [second_countable_topology β] [normed_space ℝ β] [complete_space β]
  [measurable_space β] [borel_space β]
  {s t : set α} {f g : α → β} {μ : measure α}
open set

lemma integral_on_congr (hf : measurable f) (hg : measurable g) (hs : measurable_set s)
  (h : ∀ᵐ a ∂μ, a ∈ s → f a = g a) : ∫ a in s, f a ∂μ = ∫ a in s, g a ∂μ :=
integral_congr_ae hf hg $ _

lemma integral_on_congr_of_set (hsm : measurable_on s f) (htm : measurable_on t f)
  (h : ∀ᵐ a, a ∈ s ↔ a ∈ t) : (∫ a in s, f a) = (∫ a in t, f a) :=
integral_congr_ae hsm htm $ indicator_congr_of_set h

lemma integral_on_add {s : set α} (hfm : measurable_on s f) (hfi : integrable_on s f)
  (hgm : measurable_on s g) (hgi : integrable_on s g) :
  (∫ a in s, f a + g a) = (∫ a in s, f a) + (∫ a in s, g a) :=
by { simp only [indicator_add], exact integral_add hfm hfi hgm hgi }

lemma integral_on_sub (hfm : measurable_on s f) (hfi : integrable_on s f) (hgm : measurable_on s g)
  (hgi : integrable_on s g) : (∫ a in s, f a - g a) = (∫ a in s, f a) - (∫ a in s, g a) :=
by { simp only [indicator_sub], exact integral_sub hfm hfi hgm hgi }

lemma integral_on_le_integral_on_ae {f g : α → ℝ} (hfm : measurable_on s f)
  (hfi : integrable_on s f) (hgm : measurable_on s g) (hgi : integrable_on s g)
  (h : ∀ᵐ a, a ∈ s → f a ≤ g a) :
  (∫ a in s, f a) ≤ (∫ a in s, g a) :=
begin
  apply integral_le_integral_ae hfm hfi hgm hgi,
  apply indicator_le_indicator_ae,
  exact h
end

lemma integral_on_le_integral_on {f g : α → ℝ} (hfm : measurable_on s f) (hfi : integrable_on s f)
  (hgm : measurable_on s g) (hgi : integrable_on s g) (h : ∀ a, a ∈ s → f a ≤ g a) :
  (∫ a in s, f a) ≤ (∫ a in s, g a) :=
integral_on_le_integral_on_ae hfm hfi hgm hgi $ by filter_upwards [] h

lemma integral_on_union (hsm : measurable_on s f) (hsi : integrable_on s f)
  (htm : measurable_on t f) (hti : integrable_on t f) (h : disjoint s t) :
  (∫ a in (s ∪ t), f a) = (∫ a in s, f a) + (∫ a in t, f a) :=
by { rw [indicator_union_of_disjoint h, integral_add hsm hsi htm hti] }

lemma integral_on_union_ae (hs : measurable_set s) (ht : measurable_set t) (hsm : measurable_on s f)
  (hsi : integrable_on s f) (htm : measurable_on t f) (hti : integrable_on t f)
  (h : ∀ᵐ a, a ∉ s ∩ t) :
  (∫ a in (s ∪ t), f a) = (∫ a in s, f a) + (∫ a in t, f a) :=
begin
  have := integral_congr_ae _ _ (indicator_union_ae h f),
  rw [this, integral_add hsm hsi htm hti],
  { exact hsm.union hs ht htm },
  { exact measurable.add hsm htm }
end

lemma integral_on_nonneg_of_ae {f : α → ℝ} (hf : ∀ᵐ a, a ∈ s → 0 ≤ f a) : (0:ℝ) ≤ (∫ a in s, f a) :=
integral_nonneg_of_ae $ by { filter_upwards [hf] λ a h, indicator_nonneg' h }

lemma integral_on_nonneg {f : α → ℝ} (hf : ∀ a, a ∈ s → 0 ≤ f a) : (0:ℝ) ≤ (∫ a in s, f a) :=
integral_on_nonneg_of_ae $ univ_mem_sets' hf

lemma integral_on_nonpos_of_ae {f : α → ℝ} (hf : ∀ᵐ a, a ∈ s → f a ≤ 0) : (∫ a in s, f a) ≤ 0 :=
integral_nonpos_of_nonpos_ae $ by { filter_upwards [hf] λ a h, indicator_nonpos' h }

lemma integral_on_nonpos {f : α → ℝ} (hf : ∀ a, a ∈ s → f a ≤ 0) : (∫ a in s, f a) ≤ 0 :=
integral_on_nonpos_of_ae $ univ_mem_sets' hf

lemma tendsto_integral_on_of_monotone {s : ℕ → set α} {f : α → β} (hsm : ∀i, measurable_set (s i))
  (h_mono : monotone s) (hfm : measurable_on (Union s) f) (hfi : integrable_on (Union s) f) :
  tendsto (λi, ∫ a in (s i), f a) at_top (nhds (∫ a in (Union s), f a)) :=
let bound : α → ℝ := indicator (Union s) (λa, ∥f a∥) in
begin
  apply tendsto_integral_of_dominated_convergence,
  { assume i, exact hfm.subset (hsm i) (subset_Union _ _) },
  { assumption },
  { show integrable_on (Union s) (λa, ∥f a∥), rwa integrable_on_norm_iff },
  { assume i, apply ae_of_all,
    assume a,
    rw [norm_indicator_eq_indicator_norm],
    exact indicator_le_indicator_of_subset (subset_Union _ _) (λa, norm_nonneg _) _ },
  { filter_upwards [] λa, le_trans (tendsto_indicator_of_monotone _ h_mono _ _) (pure_le_nhds _) }
end

lemma tendsto_integral_on_of_antimono (s : ℕ → set α) (f : α → β) (hsm : ∀i, measurable_set (s i))
  (h_mono : ∀i j, i ≤ j → s j ⊆ s i) (hfm : measurable_on (s 0) f) (hfi : integrable_on (s 0) f) :
  tendsto (λi, ∫ a in (s i), f a) at_top (nhds (∫ a in (Inter s), f a)) :=
let bound : α → ℝ := indicator (s 0) (λa, ∥f a∥) in
begin
  apply tendsto_integral_of_dominated_convergence,
  { assume i, refine hfm.subset (hsm i) (h_mono _ _ (zero_le _)) },
  { exact hfm.subset (measurable_set.Inter hsm) (Inter_subset _ _) },
  { show integrable_on (s 0) (λa, ∥f a∥), rwa integrable_on_norm_iff },
  { assume i, apply ae_of_all,
    assume a,
    rw [norm_indicator_eq_indicator_norm],
    refine indicator_le_indicator_of_subset (h_mono _ _ (zero_le _)) (λa, norm_nonneg _) _ },
  { filter_upwards [] λa, le_trans (tendsto_indicator_of_antimono _ h_mono _ _) (pure_le_nhds _) }
end

-- TODO : prove this for an encodable type
-- by proving an encodable version of `filter.is_countably_generated_at_top_finset_nat `
lemma integral_on_Union (s : ℕ → set α) (f : α → β) (hm : ∀i, measurable_set (s i))
  (hd : ∀ i j, i ≠ j → s i ∩ s j = ∅) (hfm : measurable_on (Union s) f)
  (hfi : integrable_on (Union s) f) :
  (∫ a in (Union s), f a) = ∑'i, ∫ a in s i, f a :=
suffices h : tendsto (λn:finset ℕ, ∑ i in n, ∫ a in s i, f a) at_top (𝓝 $ (∫ a in (Union s), f a)),
  by { rwa has_sum.tsum_eq },
begin
  have : (λn:finset ℕ, ∑ i in n, ∫ a in s i, f a) = λn:finset ℕ, ∫ a in (⋃i∈n, s i), f a,
  { funext,
    rw [← integral_finset_sum, indicator_finset_bUnion],
    { assume i hi j hj hij, exact hd i j hij },
    { assume i, refine hfm.subset (hm _) (subset_Union _ _) },
    { assume i, refine hfi.subset (subset_Union _ _) } },
  rw this,
  refine tendsto_integral_filter_of_dominated_convergence _ _ _ _ _ _ _,
  { exact indicator (Union s) (λ a, ∥f a∥) },
  { exact is_countably_generated_at_top_finset_nat },
  { refine univ_mem_sets' (λ n, _),
    simp only [mem_set_of_eq],
    refine hfm.subset (measurable_set.Union (λ i, measurable_set.Union_Prop (λh, hm _)))
      (bUnion_subset_Union _ _), },
  { assumption },
  { refine univ_mem_sets' (λ n, univ_mem_sets' $ _),
    simp only [mem_set_of_eq],
    assume a,
    rw ← norm_indicator_eq_indicator_norm,
    refine norm_indicator_le_of_subset (bUnion_subset_Union _ _) _ _ },
  { rw [← integrable_on, integrable_on_norm_iff], assumption },
  { filter_upwards [] λa, le_trans (tendsto_indicator_bUnion_finset _ _ _) (pure_le_nhds _) }
end

end integral_on
-/
