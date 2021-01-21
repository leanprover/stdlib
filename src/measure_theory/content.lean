/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.borel_space

/-!
# Contents

In this file we work with *contents*. A content `λ` is a function from a certain class of subsets
(such as the the compact subsets) to `ennreal` (or `ℝ≥0`) that is
* additive: If `K₁` and `K₂` are disjoint sets in the domain of `λ`,
  then `λ(K₁ ∪ K₂) = λ(K₁) + λ(K₂)`;
* subadditive: If `K₁` and `K₂` are in the domain of `λ`, then `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)`;
* monotone: If `K₁ ⊆ K₂` are in the domain of `λ`, then `λ(K₁) ≤ λ(K₂)`.

We show that:
* Given a content `λ` on compact sets, we get a countably subadditive map that vanishes at `∅`.
  In Halmos (1950) this is called the *inner content* `λ*` of `λ`.
* Given an inner content, we define an outer measure.

We don't explicitly define the type of contents.
In this file we only work on contents on compact sets, and inner contents on open sets, and both
contents and inner contents map into the extended nonnegative reals. However, in other applications
other choices can be made, and it is not a priori clear what the best interface should be.

## Main definitions
* `measure_theory.inner_content`: define an inner content from an content
* `measure_theory.outer_measure.of_content`: construct an outer measure from a content

## References

* Paul Halmos (1950), Measure Theory, §53
* https://en.wikipedia.org/wiki/Content_(measure_theory)
-/

universe variables u v w
noncomputable theory

open set topological_space
open_locale nnreal

namespace measure_theory

variables {G : Type w} [topological_space G]

/-- Constructing the inner content of a content. From a content defined on the compact sets, we
  obtain a function defined on all open sets, by taking the supremum of the content of all compact
  subsets. -/
def inner_content (μ : compacts G → ennreal) (U : opens G) : ennreal :=
⨆ (K : compacts G) (h : K.1 ⊆ U), μ K

lemma le_inner_content {μ : compacts G → ennreal} (K : compacts G) (U : opens G)
  (h2 : K.1 ⊆ U) : μ K ≤ inner_content μ U :=
le_supr_of_le K $ le_supr _ h2

lemma inner_content_le {μ : compacts G → ennreal}
  (h : ∀ (K₁ K₂ : compacts G), K₁.1 ⊆ K₂.1 → μ K₁ ≤ μ K₂)
  (U : opens G) (K : compacts G)
  (h2 : (U : set G) ⊆ K.1) : inner_content μ U ≤ μ K :=
bsupr_le $ λ K' hK', h _ _ (subset.trans hK' h2)

lemma inner_content_of_is_compact {μ : compacts G → ennreal}
  (h : ∀ (K₁ K₂ : compacts G), K₁.1 ⊆ K₂.1 → μ K₁ ≤ μ K₂) {K : set G} (h1K : is_compact K)
  (h2K : is_open K) : inner_content μ ⟨K, h2K⟩ = μ ⟨K, h1K⟩ :=
le_antisymm (bsupr_le $ λ K' hK', h _ ⟨K, h1K⟩ hK')
            (le_inner_content _ _ subset.rfl)

lemma inner_content_empty {μ : compacts G → ennreal} (h : μ ⊥ = 0) :
  inner_content μ ∅ = 0 :=
begin
  refine le_antisymm _ (zero_le _), rw ←h,
  refine bsupr_le (λ K hK, _),
  have : K = ⊥, { ext1, rw [subset_empty_iff.mp hK, compacts.bot_val] }, rw this, refl'
end

/-- This is "unbundled", because that it required for the API of `induced_outer_measure`. -/
lemma inner_content_mono {μ : compacts G → ennreal} ⦃U V : set G⦄ (hU : is_open U) (hV : is_open V)
  (h2 : U ⊆ V) : inner_content μ ⟨U, hU⟩ ≤ inner_content μ ⟨V, hV⟩ :=
supr_le_supr $ λ K, supr_le_supr_const $ λ hK, subset.trans hK h2

lemma inner_content_exists_compact {μ : compacts G → ennreal} {U : opens G}
  (hU : inner_content μ U < ⊤) {ε : ℝ≥0} (hε : 0 < ε) :
  ∃ K : compacts G, K.1 ⊆ U ∧ inner_content μ U ≤ μ K + ε :=
begin
  have h'ε := ennreal.zero_lt_coe_iff.2 hε,
  cases le_or_lt (inner_content μ U) ε,
  { exact ⟨⊥, empty_subset _, le_trans h (le_add_of_nonneg_left (zero_le _))⟩ },
  have := ennreal.sub_lt_self (ne_of_lt hU) (ne_of_gt $ lt_trans h'ε h) h'ε,
  conv at this {to_rhs, rw inner_content }, simp only [lt_supr_iff] at this,
  rcases this with ⟨U, h1U, h2U⟩, refine ⟨U, h1U, _⟩,
  rw [← ennreal.sub_le_iff_le_add], exact le_of_lt h2U
end

/-- The inner content of a supremum of opens is at most the sum of the individual inner
contents. -/
lemma inner_content_Sup_nat [t2_space G] {μ : compacts G → ennreal}
  (h1 : μ ⊥ = 0)
  (h2 : ∀ (K₁ K₂ : compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) (U : ℕ → opens G) :
  inner_content μ (⨆ (i : ℕ), U i) ≤ ∑' (i : ℕ), inner_content μ (U i) :=
begin
  have h3 : ∀ (t : finset ℕ) (K : ℕ → compacts G), μ (t.sup K) ≤ t.sum (λ i, μ (K i)),
  { intros t K, refine finset.induction_on t _ _,
    { simp only [h1, nonpos_iff_eq_zero, finset.sum_empty, finset.sup_empty] },
    { intros n s hn ih, rw [finset.sup_insert, finset.sum_insert hn],
      exact le_trans (h2 _ _) (add_le_add_left ih _) }},
  refine bsupr_le (λ K hK, _),
  rcases is_compact.elim_finite_subcover K.2 _ (λ i, (U i).prop) _ with ⟨t, ht⟩, swap,
  { convert hK, rw [opens.supr_def, subtype.coe_mk] },
  rcases K.2.finite_compact_cover t (coe ∘ U) (λ i _, (U _).prop) (by simp only [ht])
    with ⟨K', h1K', h2K', h3K'⟩,
  let L : ℕ → compacts G := λ n, ⟨K' n, h1K' n⟩,
  convert le_trans (h3 t L) _,
  { ext1, rw [h3K', compacts.finset_sup_val, finset.sup_eq_supr] },
  refine le_trans (finset.sum_le_sum _) (ennreal.sum_le_tsum t),
  intros i hi, refine le_trans _ (le_supr _ (L i)),
  refine le_trans _ (le_supr _ (h2K' i)), refl'
end

/-- The inner content of a union of sets is at most the sum of the individual inner contents.
  This is the "unbundled" version of `inner_content_Sup_nat`.
  It required for the API of `induced_outer_measure`. -/
lemma inner_content_Union_nat [t2_space G] {μ : compacts G → ennreal}
  (h1 : μ ⊥ = 0)
  (h2 : ∀ (K₁ K₂ : compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂)
  ⦃U : ℕ → set G⦄ (hU : ∀ (i : ℕ), is_open (U i)) :
  inner_content μ ⟨⋃ (i : ℕ), U i, is_open_Union hU⟩ ≤ ∑' (i : ℕ), inner_content μ ⟨U i, hU i⟩ :=
by { have := inner_content_Sup_nat h1 h2 (λ i, ⟨U i, hU i⟩), rwa [opens.supr_def] at this }

lemma inner_content_comap {μ : compacts G → ennreal} (f : G ≃ₜ G)
  (h : ∀ ⦃K : compacts G⦄, μ (K.map f f.continuous) = μ K) (U : opens G) :
  inner_content μ (U.comap f.continuous) = inner_content μ U :=
begin
  refine supr_congr _ ((compacts.equiv f).surjective) _,
  intro K, refine supr_congr_Prop image_subset_iff _,
  intro hK, simp only [equiv.coe_fn_mk, subtype.mk_eq_mk, ennreal.coe_eq_coe, compacts.equiv],
  apply h,
end

@[to_additive]
lemma is_mul_left_invariant_inner_content [group G] [topological_group G] {μ : compacts G → ennreal}
  (h : ∀ (g : G) {K : compacts G}, μ (K.map _ $ continuous_mul_left g) = μ K) (g : G)
  (U : opens G) : inner_content μ (U.comap $ continuous_mul_left g) = inner_content μ U :=
by convert inner_content_comap (homeomorph.mul_left g) (λ K, h g) U

-- @[to_additive] (fails for now)
lemma inner_content_pos_of_is_mul_left_invariant [t2_space G] [group G] [topological_group G]
  {μ : compacts G → ennreal}
  (h1 : μ ⊥ = 0)
  (h2 : ∀ (K₁ K₂ : compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂)
  (h3 : ∀ (g : G) {K : compacts G}, μ (K.map _ $ continuous_mul_left g) = μ K)
  (K : compacts G) (hK : 0 < μ K) (U : opens G) (hU : (U : set G).nonempty) :
  0 < inner_content μ U :=
begin
  have : (interior (U : set G)).nonempty, rwa [U.prop.interior_eq],
  rcases compact_covered_by_mul_left_translates K.2 this with ⟨s, hs⟩,
  suffices : μ K ≤ s.card * inner_content μ U,
  { exact (ennreal.mul_pos.mp $ lt_of_lt_of_le hK this).2 },
  have : K.1 ⊆ ↑⨆ (g ∈ s), U.comap $ continuous_mul_left g,
  { simpa only [opens.supr_def, opens.coe_comap, subtype.coe_mk] },
  refine (le_inner_content _ _ this).trans _,
  refine (rel_supr_sum (inner_content μ) (inner_content_empty h1) (≤)
    (inner_content_Sup_nat h1 h2) _ _).trans _,
  simp only [is_mul_left_invariant_inner_content h3, finset.sum_const, nsmul_eq_mul, le_refl]
end

lemma inner_content_mono' {μ : compacts G → ennreal} ⦃U V : set G⦄
  (hU : is_open U) (hV : is_open V) (h2 : U ⊆ V) :
  inner_content μ ⟨U, hU⟩ ≤ inner_content μ ⟨V, hV⟩ :=
supr_le_supr $ λ K, supr_le_supr_const $ λ hK, subset.trans hK h2

namespace outer_measure

/-- Extending a content on compact sets to an outer measure on all sets. -/
def of_content [t2_space G] (μ : compacts G → ennreal) (h1 : μ ⊥ = 0) : outer_measure G :=
induced_outer_measure (λ U hU, inner_content μ ⟨U, hU⟩) is_open_empty (inner_content_empty h1)

variables [t2_space G] {μ : compacts G → ennreal} {h1 : μ ⊥ = 0}
  (h2 : ∀ (K₁ K₂ : compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂)

include h2
lemma of_content_opens (U : opens G) : of_content μ h1 U = inner_content μ U :=
induced_outer_measure_eq' (λ _, is_open_Union) (inner_content_Union_nat h1 h2)
  inner_content_mono U.2

lemma of_content_le (h : ∀ (K₁ K₂ : compacts G), K₁.1 ⊆ K₂.1 → μ K₁ ≤ μ K₂)
  (U : opens G) (K : compacts G) (hUK : (U : set G) ⊆ K.1) : of_content μ h1 U ≤ μ K :=
(of_content_opens h2 U).le.trans $ inner_content_le h U K hUK

lemma le_of_content_compacts (K : compacts G) : μ K ≤ of_content μ h1 K.1 :=
begin
  rw [of_content, induced_outer_measure_eq_infi],
  { exact le_infi (λ U, le_infi $ λ hU, le_infi $ le_inner_content K ⟨U, hU⟩) },
  { exact inner_content_Union_nat h1 h2 },
  { exact inner_content_mono }
end

lemma of_content_eq_infi (A : set G) :
  of_content μ h1 A = ⨅ (U : set G) (hU : is_open U) (h : A ⊆ U), inner_content μ ⟨U, hU⟩ :=
induced_outer_measure_eq_infi _ (inner_content_Union_nat h1 h2) inner_content_mono A

lemma of_content_interior_compacts (h3 : ∀ (K₁ K₂ : compacts G), K₁.1 ⊆ K₂.1 → μ K₁ ≤ μ K₂)
  (K : compacts G) : of_content μ h1 (interior K.1) ≤ μ K :=
le_trans (le_of_eq $ of_content_opens h2 (opens.interior K.1))
         (inner_content_le h3 _ _ interior_subset)

lemma of_content_exists_compact {U : opens G} (hU : of_content μ h1 U < ⊤) {ε : ℝ≥0}
  (hε : 0 < ε) : ∃ K : compacts G, K.1 ⊆ U ∧ of_content μ h1 U ≤ of_content μ h1 K.1 + ε :=
begin
  rw [of_content_opens h2] at hU ⊢,
  rcases inner_content_exists_compact hU hε with ⟨K, h1K, h2K⟩,
  exact ⟨K, h1K, le_trans h2K $ add_le_add_right (le_of_content_compacts h2 K) _⟩,
end

lemma of_content_exists_open {A : set G} (hA : of_content μ h1 A < ⊤) {ε : ℝ≥0} (hε : 0 < ε) :
  ∃ U : opens G, A ⊆ U ∧ of_content μ h1 U ≤ of_content μ h1 A + ε :=
begin
  rcases induced_outer_measure_exists_set _ _ inner_content_mono hA hε with ⟨U, hU, h2U, h3U⟩,
  exact ⟨⟨U, hU⟩, h2U, h3U⟩, swap, exact inner_content_Union_nat h1 h2
end

lemma of_content_preimage (f : G ≃ₜ G) (h : ∀ ⦃K : compacts G⦄, μ (K.map f f.continuous) = μ K)
  (A : set G) : of_content μ h1 (f ⁻¹' A) = of_content μ h1 A :=
begin
  refine induced_outer_measure_preimage _ (inner_content_Union_nat h1 h2) inner_content_mono _
    (λ s, f.is_open_preimage) _,
  intros s hs, convert inner_content_comap f h ⟨s, hs⟩
end

@[to_additive]
lemma is_mul_left_invariant_of_content [group G] [topological_group G]
  (h : ∀ (g : G) {K : compacts G}, μ (K.map _ $ continuous_mul_left g) = μ K) (g : G)
  (A : set G) : of_content μ h1 ((λ h, g * h) ⁻¹' A) = of_content μ h1 A :=
by convert of_content_preimage h2 (homeomorph.mul_left g) (λ K, h g) A

lemma of_content_caratheodory (A : set G) :
  (of_content μ h1).caratheodory.is_measurable' A ↔ ∀ (U : opens G),
  of_content μ h1 (U ∩ A) + of_content μ h1 (U \ A) ≤ of_content μ h1 U :=
begin
  dsimp [opens], rw subtype.forall,
  apply induced_outer_measure_caratheodory,
  apply inner_content_Union_nat h1 h2,
  apply inner_content_mono'
end

-- @[to_additive] (fails for now)
lemma of_content_pos_of_is_mul_left_invariant [group G] [topological_group G]
  (h3 : ∀ (g : G) {K : compacts G}, μ (K.map _ $ continuous_mul_left g) = μ K)
  (K : compacts G) (hK : 0 < μ K) {U : set G} (h1U : is_open U) (h2U : U.nonempty) :
  0 < of_content μ h1 U :=
by { convert inner_content_pos_of_is_mul_left_invariant h1 h2 h3 K hK ⟨U, h1U⟩ h2U,
     exact of_content_opens h2 ⟨U, h1U⟩ }

end outer_measure
end measure_theory
