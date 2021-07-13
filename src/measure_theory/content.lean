/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.measure_space
import measure_theory.regular
import topology.opens
import topology.compacts

/-!
# Contents

In this file we work with *contents*. A content `λ` is a function from a certain class of subsets
(such as the the compact subsets) to `ℝ≥0` that is
* additive: If `K₁` and `K₂` are disjoint sets in the domain of `λ`,
  then `λ(K₁ ∪ K₂) = λ(K₁) + λ(K₂)`;
* subadditive: If `K₁` and `K₂` are in the domain of `λ`, then `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)`;
* monotone: If `K₁ ⊆ K₂` are in the domain of `λ`, then `λ(K₁) ≤ λ(K₂)`.

We show that:
* Given a content `λ` on compact sets, let us define a function `λ*` on open sets, by letting
  `λ* U` be the supremum of `λ K` for `K` included in `U`. This is a countably subadditive map that
  vanishes at `∅`. In Halmos (1950) this is called the *inner content* `λ*` of `λ`, and formalized
  as `inner_content`.
* Given an inner content, we define an outer measure `μ*`, by letting `μ* E` be the infimum of
  `λ* U` over the open sets `U` containing `E`. This is indeed an outer measure. It is formalized
  as `outer_measure`.
* Restricting this outer measure to Borel sets gives a regular measure `μ`.

We define bundled contents as `content`.
In this file we only work on contents on compact sets, and inner contents on open sets, and both
contents and inner contents map into the extended nonnegative reals. However, in other applications
other choices can be made, and it is not a priori clear what the best interface should be.

## Main definitions

For `μ : content G`, we define
* `μ.inner_content` : the inner content associated to `μ`.
* `μ.outer_measure` : the outer measure associated to `μ`.
* `μ.measure`       : the Borel measure associated to `μ`.

We prove that, on a locally compact space, the measure `μ.measure` is regular.

## References

* Paul Halmos (1950), Measure Theory, §53
* <https://en.wikipedia.org/wiki/Content_(measure_theory)>
-/

universe variables u v w
noncomputable theory

open set topological_space
open_locale nnreal ennreal

namespace measure_theory

variables {G : Type w} [topological_space G]

/-- A content is an additive function on compact sets taking values in `ℝ≥0`. It is a device
from which one can define a measure. -/
structure content (G : Type w) [topological_space G] :=
(to_fun : compacts G → ℝ≥0)
(mono' : ∀ (K₁ K₂ : compacts G), K₁.1 ⊆ K₂.1 → to_fun K₁ ≤ to_fun K₂)
(sup_disjoint' : ∀ (K₁ K₂ : compacts G), disjoint K₁.1 K₂.1 →
   to_fun (K₁ ⊔ K₂) = to_fun K₁ + to_fun K₂)
(sup_le' : ∀ (K₁ K₂ : compacts G), to_fun (K₁ ⊔ K₂) ≤ to_fun K₁ + to_fun K₂)

instance : inhabited (content G) :=
⟨{ to_fun := λ K, 0,
  mono' := by simp,
  sup_disjoint' := by simp,
  sup_le' := by simp }⟩

/-- Although the `to_fun` field of a content takes values in `ℝ≥0`, we register a coercion to
functions taking values in `ℝ≥0∞` as most constructions below rely on taking suprs and infs, which
is more convenient in a complete lattice, and aim at constructing a measure. -/
instance : has_coe_to_fun (content G) := ⟨_, λ μ s, (μ.to_fun s : ℝ≥0∞)⟩

namespace content

variable (μ : content G)

lemma apply_eq_coe_to_fun (K : compacts G) : μ K = μ.to_fun K := rfl

lemma mono (K₁ K₂ : compacts G) (h : K₁.1 ⊆ K₂.1) : μ K₁ ≤ μ K₂ :=
by simp [apply_eq_coe_to_fun, μ.mono' _ _ h]

lemma sup_disjoint (K₁ K₂ : compacts G) (h : disjoint K₁.1 K₂.1) : μ (K₁ ⊔ K₂) = μ K₁ + μ K₂ :=
by simp [apply_eq_coe_to_fun, μ.sup_disjoint' _ _ h]

lemma sup_le (K₁ K₂ : compacts G) : μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂ :=
by { simp only [apply_eq_coe_to_fun], norm_cast, exact μ.sup_le' _ _ }

lemma lt_top (K : compacts G) : μ K < ∞ :=
ennreal.coe_lt_top

lemma empty : μ ⊥ = 0 :=
begin
  have := μ.sup_disjoint' ⊥ ⊥,
  simpa [apply_eq_coe_to_fun] using this,
end

/-- Constructing the inner content of a content. From a content defined on the compact sets, we
  obtain a function defined on all open sets, by taking the supremum of the content of all compact
  subsets. -/
def inner_content (U : opens G) : ℝ≥0∞ :=
⨆ (K : compacts G) (h : K.1 ⊆ U), μ K

lemma le_inner_content (K : compacts G) (U : opens G)
  (h2 : K.1 ⊆ U) : μ K ≤ μ.inner_content U :=
le_supr_of_le K $ le_supr _ h2

lemma inner_content_le (U : opens G) (K : compacts G) (h2 : (U : set G) ⊆ K.1) :
  μ.inner_content U ≤ μ K :=
bsupr_le $ λ K' hK', μ.mono _ _ (subset.trans hK' h2)

lemma inner_content_of_is_compact {K : set G} (h1K : is_compact K) (h2K : is_open K) :
  μ.inner_content ⟨K, h2K⟩ = μ ⟨K, h1K⟩ :=
le_antisymm (bsupr_le $ λ K' hK', μ.mono _ ⟨K, h1K⟩ hK')
            (μ.le_inner_content _ _ subset.rfl)

lemma inner_content_empty :
  μ.inner_content ∅ = 0 :=
begin
  refine le_antisymm _ (zero_le _), rw ←μ.empty,
  refine bsupr_le (λ K hK, _),
  have : K = ⊥, { ext1, rw [subset_empty_iff.mp hK, compacts.bot_val] }, rw this, refl'
end

/-- This is "unbundled", because that it required for the API of `induced_outer_measure`. -/
lemma inner_content_mono ⦃U V : set G⦄ (hU : is_open U) (hV : is_open V)
  (h2 : U ⊆ V) : μ.inner_content ⟨U, hU⟩ ≤ μ.inner_content ⟨V, hV⟩ :=
supr_le_supr $ λ K, supr_le_supr_const $ λ hK, subset.trans hK h2

lemma inner_content_exists_compact {U : opens G}
  (hU : μ.inner_content U < ∞) {ε : ℝ≥0} (hε : 0 < ε) :
  ∃ K : compacts G, K.1 ⊆ U ∧ μ.inner_content U ≤ μ K + ε :=
begin
  have h'ε := ennreal.zero_lt_coe_iff.2 hε,
  cases le_or_lt (μ.inner_content U) ε,
  { exact ⟨⊥, empty_subset _, le_trans h (le_add_of_nonneg_left (zero_le _))⟩ },
  have := ennreal.sub_lt_self (ne_of_lt hU) (ne_of_gt $ lt_trans h'ε h) h'ε,
  conv at this {to_rhs, rw inner_content }, simp only [lt_supr_iff] at this,
  rcases this with ⟨U, h1U, h2U⟩, refine ⟨U, h1U, _⟩,
  rw [← ennreal.sub_le_iff_le_add], exact le_of_lt h2U
end

/-- The inner content of a supremum of opens is at most the sum of the individual inner
contents. -/
lemma inner_content_Sup_nat [t2_space G] (U : ℕ → opens G) :
  μ.inner_content (⨆ (i : ℕ), U i) ≤ ∑' (i : ℕ), μ.inner_content (U i) :=
begin
  have h3 : ∀ (t : finset ℕ) (K : ℕ → compacts G), μ (t.sup K) ≤ t.sum (λ i, μ (K i)),
  { intros t K, refine finset.induction_on t _ _,
    { simp only [μ.empty, nonpos_iff_eq_zero, finset.sum_empty, finset.sup_empty], },
    { intros n s hn ih, rw [finset.sup_insert, finset.sum_insert hn],
      exact le_trans (μ.sup_le _ _) (add_le_add_left ih _) }},
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
lemma inner_content_Union_nat [t2_space G] ⦃U : ℕ → set G⦄ (hU : ∀ (i : ℕ), is_open (U i)) :
  μ.inner_content ⟨⋃ (i : ℕ), U i, is_open_Union hU⟩ ≤ ∑' (i : ℕ), μ.inner_content ⟨U i, hU i⟩ :=
by { have := μ.inner_content_Sup_nat (λ i, ⟨U i, hU i⟩), rwa [opens.supr_def] at this }

lemma inner_content_comap (f : G ≃ₜ G)
  (h : ∀ ⦃K : compacts G⦄, μ (K.map f f.continuous) = μ K) (U : opens G) :
  μ.inner_content (U.comap f.continuous) = μ.inner_content U :=
begin
  refine supr_congr _ ((compacts.equiv f).surjective) _,
  intro K, refine supr_congr_Prop image_subset_iff _,
  intro hK, simp only [equiv.coe_fn_mk, subtype.mk_eq_mk, ennreal.coe_eq_coe, compacts.equiv],
  apply h,
end

@[to_additive]
lemma is_mul_left_invariant_inner_content [group G] [topological_group G]
  (h : ∀ (g : G) {K : compacts G}, μ (K.map _ $ continuous_mul_left g) = μ K) (g : G)
  (U : opens G) : μ.inner_content (U.comap $ continuous_mul_left g) = μ.inner_content U :=
by convert μ.inner_content_comap (homeomorph.mul_left g) (λ K, h g) U

@[to_additive]
lemma inner_content_pos_of_is_mul_left_invariant [t2_space G] [group G] [topological_group G]
  (h3 : ∀ (g : G) {K : compacts G}, μ (K.map _ $ continuous_mul_left g) = μ K)
  (K : compacts G) (hK : 0 < μ K) (U : opens G) (hU : (U : set G).nonempty) :
  0 < μ.inner_content U :=
begin
  have : (interior (U : set G)).nonempty, rwa [U.prop.interior_eq],
  rcases compact_covered_by_mul_left_translates K.2 this with ⟨s, hs⟩,
  suffices : μ K ≤ s.card * μ.inner_content U,
  { exact (ennreal.mul_pos.mp $ lt_of_lt_of_le hK this).2 },
  have : K.1 ⊆ ↑⨆ (g ∈ s), U.comap $ continuous_mul_left g,
  { simpa only [opens.supr_def, opens.coe_comap, subtype.coe_mk] },
  refine (μ.le_inner_content _ _ this).trans _,
  refine (rel_supr_sum (μ.inner_content) (μ.inner_content_empty) (≤)
    (μ.inner_content_Sup_nat) _ _).trans _,
  simp only [μ.is_mul_left_invariant_inner_content h3, finset.sum_const, nsmul_eq_mul, le_refl]
end

lemma inner_content_mono' ⦃U V : set G⦄
  (hU : is_open U) (hV : is_open V) (h2 : U ⊆ V) :
  μ.inner_content ⟨U, hU⟩ ≤ μ.inner_content ⟨V, hV⟩ :=
supr_le_supr $ λ K, supr_le_supr_const $ λ hK, subset.trans hK h2

/-- Extending a content on compact sets to an outer measure on all sets. -/
protected def outer_measure : outer_measure G :=
induced_outer_measure (λ U hU, μ.inner_content ⟨U, hU⟩) is_open_empty μ.inner_content_empty

variables [t2_space G]

lemma outer_measure_opens (U : opens G) : μ.outer_measure U = μ.inner_content U :=
induced_outer_measure_eq' (λ _, is_open_Union) μ.inner_content_Union_nat μ.inner_content_mono U.2

lemma outer_measure_of_is_open (U : set G) (hU : is_open U) :
  μ.outer_measure U = μ.inner_content ⟨U, hU⟩ :=
μ.outer_measure_opens ⟨U, hU⟩

lemma outer_measure_le
  (U : opens G) (K : compacts G) (hUK : (U : set G) ⊆ K.1) : μ.outer_measure U ≤ μ K :=
(μ.outer_measure_opens U).le.trans $ μ.inner_content_le U K hUK

lemma le_outer_measure_compacts (K : compacts G) : μ K ≤ μ.outer_measure K.1 :=
begin
  rw [content.outer_measure, induced_outer_measure_eq_infi],
  { exact le_infi (λ U, le_infi $ λ hU, le_infi $ μ.le_inner_content K ⟨U, hU⟩) },
  { exact μ.inner_content_Union_nat },
  { exact μ.inner_content_mono }
end

lemma outer_measure_eq_infi (A : set G) :
  μ.outer_measure A = ⨅ (U : set G) (hU : is_open U) (h : A ⊆ U), μ.inner_content ⟨U, hU⟩ :=
induced_outer_measure_eq_infi _ μ.inner_content_Union_nat μ.inner_content_mono A

lemma outer_measure_interior_compacts (K : compacts G) : μ.outer_measure (interior K.1) ≤ μ K :=
le_trans (le_of_eq $ μ.outer_measure_opens (opens.interior K.1))
         (μ.inner_content_le _ _ interior_subset)

lemma outer_measure_exists_compact {U : opens G} (hU : μ.outer_measure U < ∞) {ε : ℝ≥0}
  (hε : 0 < ε) : ∃ K : compacts G, K.1 ⊆ U ∧ μ.outer_measure U ≤ μ.outer_measure K.1 + ε :=
begin
  rw [μ.outer_measure_opens] at hU ⊢,
  rcases μ.inner_content_exists_compact hU hε with ⟨K, h1K, h2K⟩,
  exact ⟨K, h1K, le_trans h2K $ add_le_add_right (μ.le_outer_measure_compacts K) _⟩,
end

lemma outer_measure_exists_open {A : set G} (hA : μ.outer_measure A < ∞) {ε : ℝ≥0} (hε : 0 < ε) :
  ∃ U : opens G, A ⊆ U ∧ μ.outer_measure U ≤ μ.outer_measure A + ε :=
begin
  rcases induced_outer_measure_exists_set _ _ μ.inner_content_mono hA hε with ⟨U, hU, h2U, h3U⟩,
  exact ⟨⟨U, hU⟩, h2U, h3U⟩, swap, exact μ.inner_content_Union_nat
end

lemma outer_measure_preimage (f : G ≃ₜ G) (h : ∀ ⦃K : compacts G⦄, μ (K.map f f.continuous) = μ K)
  (A : set G) : μ.outer_measure (f ⁻¹' A) = μ.outer_measure A :=
begin
  refine induced_outer_measure_preimage _ μ.inner_content_Union_nat μ.inner_content_mono _
    (λ s, f.is_open_preimage) _,
  intros s hs, convert μ.inner_content_comap f h ⟨s, hs⟩
end

lemma outer_measure_lt_top_of_is_compact [locally_compact_space G]
  {K : set G} (hK : is_compact K) : μ.outer_measure K < ∞ :=
begin
  rcases exists_compact_superset hK with ⟨F, h1F, h2F⟩,
  calc
  μ.outer_measure K ≤ μ.outer_measure (interior F) : outer_measure.mono' _ h2F
  ... ≤ μ ⟨F, h1F⟩ :
    by apply μ.outer_measure_le ⟨interior F, is_open_interior⟩ ⟨F, h1F⟩ interior_subset
  ... < ⊤ : μ.lt_top _
end

@[to_additive]
lemma is_mul_left_invariant_outer_measure [group G] [topological_group G]
  (h : ∀ (g : G) {K : compacts G}, μ (K.map _ $ continuous_mul_left g) = μ K) (g : G)
  (A : set G) : μ.outer_measure ((λ h, g * h) ⁻¹' A) = μ.outer_measure A :=
by convert μ.outer_measure_preimage (homeomorph.mul_left g) (λ K, h g) A

lemma outer_measure_caratheodory (A : set G) :
  μ.outer_measure.caratheodory.measurable_set' A ↔ ∀ (U : opens G),
  μ.outer_measure (U ∩ A) + μ.outer_measure (U \ A) ≤ μ.outer_measure U :=
begin
  dsimp [opens], rw subtype.forall,
  apply induced_outer_measure_caratheodory,
  apply inner_content_Union_nat,
  apply inner_content_mono'
end

@[to_additive]
lemma outer_measure_pos_of_is_mul_left_invariant [group G] [topological_group G]
  (h3 : ∀ (g : G) {K : compacts G}, μ (K.map _ $ continuous_mul_left g) = μ K)
  (K : compacts G) (hK : 0 < μ K) {U : set G} (h1U : is_open U) (h2U : U.nonempty) :
  0 < μ.outer_measure U :=
by { convert μ.inner_content_pos_of_is_mul_left_invariant h3 K hK ⟨U, h1U⟩ h2U,
     exact μ.outer_measure_opens ⟨U, h1U⟩ }

variables [S : measurable_space G] [borel_space G]
include S

/-- For the outer measure coming from a content, all Borel sets are measurable. -/
lemma borel_le_caratheodory : S ≤ μ.outer_measure.caratheodory :=
begin
  rw [@borel_space.measurable_eq G _ _],
  refine measurable_space.generate_from_le _,
  intros U hU,
  rw μ.outer_measure_caratheodory,
  intro U',
  rw μ.outer_measure_of_is_open ((U' : set G) ∩ U) (is_open.inter U'.prop hU),
  simp only [inner_content, supr_subtype'], rw [opens.coe_mk],
  haveI : nonempty {L : compacts G // L.1 ⊆ U' ∩ U} := ⟨⟨⊥, empty_subset _⟩⟩,
  rw [ennreal.supr_add],
  refine supr_le _, rintro ⟨L, hL⟩, simp only [subset_inter_iff] at hL,
  have : ↑U' \ U ⊆ U' \ L.1 := diff_subset_diff_right hL.2,
  refine le_trans (add_le_add_left (μ.outer_measure.mono' this) _) _,
  rw μ.outer_measure_of_is_open (↑U' \ L.1) (is_open.sdiff U'.2 L.2.is_closed),
  simp only [inner_content, supr_subtype'], rw [opens.coe_mk],
  haveI : nonempty {M : compacts G // M.1 ⊆ ↑U' \ L.1} := ⟨⟨⊥, empty_subset _⟩⟩,
  rw [ennreal.add_supr], refine supr_le _, rintro ⟨M, hM⟩, simp only [subset_diff] at hM,
  have : (L ⊔ M).1 ⊆ U',
  { simp only [union_subset_iff, compacts.sup_val, hM, hL, and_self] },
  rw μ.outer_measure_of_is_open ↑U' U'.2,
  refine le_trans (ge_of_eq _) (μ.le_inner_content _ _ this),
  exact μ.sup_disjoint _ _ hM.2.symm,
end

/-- The measure induced by the outer measure coming from a content, on the Borel sigma-algebra. -/
def measure : measure G := μ.outer_measure.to_measure μ.borel_le_caratheodory

lemma measure_apply {s : set G} (hs : measurable_set s) : μ.measure s = μ.outer_measure s :=
to_measure_apply _ _ hs

/-- In a locally compact space, any measure constructed from a content is regular. -/
instance regular [locally_compact_space G] : μ.measure.regular :=
begin
  split,
  { intros K hK,
    rw [measure_apply _ hK.measurable_set],
    exact μ.outer_measure_lt_top_of_is_compact hK },
  { intros A hA,
    rw [measure_apply _ hA, outer_measure_eq_infi],
    refine binfi_le_binfi _,
    intros U hU,
    refine infi_le_infi _,
    intro h2U,
    rw [measure_apply _ hU.measurable_set, μ.outer_measure_of_is_open U hU],
    refl' },
  { intros U hU,
    rw [measure_apply _ hU.measurable_set, μ.outer_measure_of_is_open U hU],
    dsimp only [inner_content], refine bsupr_le (λ K hK, _),
    refine le_supr_of_le K.1 _, refine le_supr_of_le K.2 _, refine le_supr_of_le hK _,
    rw [measure_apply _ K.2.measurable_set],
    apply le_outer_measure_compacts },
end

end content

end measure_theory
