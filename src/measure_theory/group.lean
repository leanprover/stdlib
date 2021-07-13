/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.integration
import measure_theory.regular

/-!
# Measures on Groups

We develop some properties of measures on (topological) groups

* We define properties on measures: left and right invariant measures.
* We define the measure `μ.inv : A ↦ μ(A⁻¹)` and show that it is right invariant iff
  `μ` is left invariant.
-/

noncomputable theory

open_locale ennreal
open has_inv set function measure_theory.measure

namespace measure_theory

variables {G : Type*}

section

variables [measurable_space G] [has_mul G]

/-- A measure `μ` on a topological group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself.
  To left translate sets we use preimage under left multiplication,
  since preimages are nicer to work with than images. -/
@[to_additive "A measure on a topological group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself.
  To left translate sets we use preimage under left addition,
  since preimages are nicer to work with than images."]
def is_mul_left_invariant (μ : set G → ℝ≥0∞) : Prop :=
∀ (g : G) {A : set G} (h : measurable_set A), μ ((λ h, g * h) ⁻¹' A) = μ A

/-- A measure `μ` on a topological group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself.
  To right translate sets we use preimage under right multiplication,
  since preimages are nicer to work with than images. -/
@[to_additive "A measure on a topological group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself.
  To right translate sets we use preimage under right addition,
  since preimages are nicer to work with than images."]
def is_mul_right_invariant (μ : set G → ℝ≥0∞) : Prop :=
∀ (g : G) {A : set G} (h : measurable_set A), μ ((λ h, h * g) ⁻¹' A) = μ A

end

namespace measure

variables [measurable_space G]

@[to_additive]
lemma map_mul_left_eq_self [topological_space G] [has_mul G] [has_continuous_mul G] [borel_space G]
  {μ : measure G} : (∀ g, measure.map ((*) g) μ = μ) ↔ is_mul_left_invariant μ :=
begin
  apply forall_congr, intro g, rw [measure.ext_iff], apply forall_congr, intro A,
  apply forall_congr, intro hA, rw [map_apply (measurable_const_mul g) hA]
end

@[to_additive]
lemma map_mul_right_eq_self [topological_space G] [has_mul G] [has_continuous_mul G] [borel_space G]
  {μ : measure G} : (∀ g, measure.map (λ h, h * g) μ = μ) ↔ is_mul_right_invariant μ :=
begin
  apply forall_congr, intro g, rw [measure.ext_iff], apply forall_congr, intro A,
  apply forall_congr, intro hA, rw [map_apply (measurable_mul_const g) hA]
end

/-- The measure `A ↦ μ (A⁻¹)`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive "The measure `A ↦ μ (- A)`, where `- A` is the pointwise negation of `A`."]
protected def inv [has_inv G] (μ : measure G) : measure G :=
measure.map inv μ

variables [group G] [topological_space G] [topological_group G] [borel_space G]

@[to_additive]
lemma inv_apply (μ : measure G) {s : set G} (hs : measurable_set s) :
  μ.inv s = μ s⁻¹ :=
measure.map_apply measurable_inv hs

@[simp, to_additive] protected lemma inv_inv (μ : measure G) : μ.inv.inv = μ :=
begin
  ext1 s hs, rw [μ.inv.inv_apply hs, μ.inv_apply, set.inv_inv],
  exact measurable_inv hs
end

variables {μ : measure G}

@[to_additive]
instance regular.inv [t2_space G] [regular μ] : regular μ.inv :=
regular.map (homeomorph.inv G)

end measure

section inv
variables [measurable_space G] [group G] [topological_space G] [topological_group G] [borel_space G]
  {μ : measure G}

@[simp, to_additive] lemma regular_inv_iff [t2_space G] : μ.inv.regular ↔ μ.regular :=
begin
  split,
  { introI h,
    rw ←μ.inv_inv,
    exact measure.regular.inv },
  { introI h,
    exact measure.regular.inv }
end

@[to_additive]
lemma is_mul_left_invariant.inv (h : is_mul_left_invariant μ) :
  is_mul_right_invariant μ.inv :=
begin
  intros g A hA,
  rw [μ.inv_apply (measurable_mul_const g hA), μ.inv_apply hA],
  convert h g⁻¹ (measurable_inv hA) using 2,
  simp only [←preimage_comp, ← inv_preimage],
  apply preimage_congr,
  intro h,
  simp only [mul_inv_rev, comp_app, inv_inv]
end

@[to_additive]
lemma is_mul_right_invariant.inv (h : is_mul_right_invariant μ) : is_mul_left_invariant μ.inv :=
begin
  intros g A hA,
  rw [μ.inv_apply (measurable_const_mul g hA), μ.inv_apply hA],
  convert h g⁻¹ (measurable_inv hA) using 2,
  simp only [←preimage_comp, ← inv_preimage],
  apply preimage_congr,
  intro h,
  simp only [mul_inv_rev, comp_app, inv_inv]
end

@[simp, to_additive]
lemma is_mul_right_invariant_inv : is_mul_right_invariant μ.inv ↔ is_mul_left_invariant μ :=
⟨λ h, by { rw ← μ.inv_inv, exact h.inv }, λ h, h.inv⟩

@[simp, to_additive]
lemma is_mul_left_invariant_inv : is_mul_left_invariant μ.inv ↔ is_mul_right_invariant μ :=
⟨λ h, by { rw ← μ.inv_inv, exact h.inv }, λ h, h.inv⟩

end inv

variables [measurable_space G] [topological_space G] [borel_space G] {μ : measure G}

section group

variables [group G] [topological_group G]

/-! Properties of regular left invariant measures -/
@[to_additive]
lemma is_mul_left_invariant.null_iff_empty [regular μ] (h2μ : is_mul_left_invariant μ)
  (h3μ : μ ≠ 0) {s : set G} (hs : is_open s) : μ s = 0 ↔ s = ∅ :=
begin
  obtain ⟨K, hK, h2K⟩ := regular.exists_compact_not_null.mpr h3μ,
  refine ⟨λ h, _, λ h, by simp [h]⟩,
  apply classical.by_contradiction, -- `by_contradiction` is very slow
  refine mt (λ h2s, _) h2K,
  rw [← ne.def, ne_empty_iff_nonempty] at h2s, cases h2s with y hy,
  obtain ⟨t, -, h1t, h2t⟩ := hK.elim_finite_subcover_image
    (show ∀ x ∈ @univ G, is_open ((λ y, x * y) ⁻¹' s),
      from λ x _, (continuous_mul_left x).is_open_preimage _ hs) _,
  { rw [← nonpos_iff_eq_zero],
    refine (measure_mono h2t).trans _,
    refine (measure_bUnion_le h1t.countable _).trans_eq _,
    simp_rw [h2μ _ hs.measurable_set], rw [h, tsum_zero] },
  { intros x _,
    simp_rw [mem_Union, mem_preimage],
    use [y * x⁻¹, mem_univ _],
    rwa [inv_mul_cancel_right] }
end

@[to_additive]
lemma is_mul_left_invariant.null_iff [regular μ] (h2μ : is_mul_left_invariant μ)
  {s : set G} (hs : is_open s) : μ s = 0 ↔ s = ∅ ∨ μ = 0 :=
begin
  by_cases h3μ : μ = 0, { simp [h3μ] },
  simp only [h3μ, or_false],
  exact h2μ.null_iff_empty h3μ hs,
end

@[to_additive]
lemma is_mul_left_invariant.measure_ne_zero_iff_nonempty [regular μ]
  (h2μ : is_mul_left_invariant μ) (h3μ : μ ≠ 0) {s : set G} (hs : is_open s) :
  μ s ≠ 0 ↔ s.nonempty :=
by simp_rw [← ne_empty_iff_nonempty, ne.def, h2μ.null_iff_empty h3μ hs]

/-- For nonzero regular left invariant measures, the integral of a continuous nonnegative function
  `f` is 0 iff `f` is 0. -/
@[to_additive]
lemma lintegral_eq_zero_of_is_mul_left_invariant [regular μ]
  (h2μ : is_mul_left_invariant μ) (h3μ : μ ≠ 0) {f : G → ℝ≥0∞} (hf : continuous f) :
  ∫⁻ x, f x ∂μ = 0 ↔ f = 0 :=
begin
  split, swap, { rintro rfl, simp_rw [pi.zero_apply, lintegral_zero] },
  intro h, contrapose h,
  simp_rw [funext_iff, not_forall, pi.zero_apply] at h, cases h with x hx,
  obtain ⟨r, h1r, h2r⟩ : ∃ r : ℝ≥0∞, 0 < r ∧ r < f x :=
  exists_between (pos_iff_ne_zero.mpr hx),
  have h3r := hf.is_open_preimage (Ioi r) is_open_Ioi,
  let s := Ioi r,
  rw [← ne.def, ← pos_iff_ne_zero],
  have : 0 < r * μ (f ⁻¹' Ioi r),
  { rw ennreal.mul_pos,
    refine ⟨h1r, _⟩,
    rw [pos_iff_ne_zero, h2μ.measure_ne_zero_iff_nonempty h3μ h3r],
    exact ⟨x, h2r⟩ },
  refine this.trans_le _,
  rw [← set_lintegral_const, ← lintegral_indicator _ h3r.measurable_set],
  apply lintegral_mono,
  refine indicator_le (λ y, le_of_lt),
end

end group

section integration

variables [group G] [has_continuous_mul G]
open measure

/-- Translating a function by left-multiplication does not change its `lintegral` with respect to
a left-invariant measure. -/
@[to_additive]
lemma lintegral_mul_left_eq_self (hμ : is_mul_left_invariant μ) (f : G → ℝ≥0∞) (g : G) :
  ∫⁻ x, f (g * x) ∂μ = ∫⁻ x, f x ∂μ :=
begin
  have : measure.map (has_mul.mul g) μ = μ,
  { rw ← map_mul_left_eq_self at hμ,
    exact hμ g },
  convert (lintegral_map_equiv f (homeomorph.mul_left g).to_measurable_equiv).symm,
  simp [this]
end

/-- Translating a function by right-multiplication does not change its `lintegral` with respect to
a right-invariant measure. -/
@[to_additive]
lemma lintegral_mul_right_eq_self (hμ : is_mul_right_invariant μ) (f : G → ℝ≥0∞) (g : G) :
  ∫⁻ x, f (x * g) ∂μ = ∫⁻ x, f x ∂μ :=
begin
  have : measure.map (homeomorph.mul_right g) μ = μ,
  { rw ← map_mul_right_eq_self at hμ,
    exact hμ g },
  convert (lintegral_map_equiv f (homeomorph.mul_right g).to_measurable_equiv).symm,
  simp [this]
end

end integration

end measure_theory
