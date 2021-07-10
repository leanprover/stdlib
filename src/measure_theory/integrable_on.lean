/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/

import measure_theory.l1_space
import analysis.normed_space.indicator_function

/-! # Functions integrable on a set and at a filter

We define `integrable_on f s μ := integrable f (μ.restrict s)` and prove theorems like
`integrable_on_union : integrable_on f (s ∪ t) μ ↔ integrable_on f s μ ∧ integrable_on f t μ`.

Next we define a predicate `integrable_at_filter (f : α → E) (l : filter α) (μ : measure α)`
saying that `f` is integrable at some set `s ∈ l` and prove that a measurable function is integrable
at `l` with respect to `μ` provided that `f` is bounded above at `l ⊓ μ.ae` and `μ` is finite
at `l`.

-/

noncomputable theory
open set filter topological_space measure_theory function
open_locale classical topological_space interval big_operators filter ennreal measure_theory

variables {α β E F : Type*} [measurable_space α]

section

variables [measurable_space β] {l l' : filter α} {f g : α → β} {μ ν : measure α}

/-- A function `f` is measurable at filter `l` w.r.t. a measure `μ` if it is ae-measurable
w.r.t. `μ.restrict s` for some `s ∈ l`. -/
def measurable_at_filter (f : α → β) (l : filter α) (μ : measure α . volume_tac) :=
∃ s ∈ l, ae_measurable f (μ.restrict s)

@[simp] lemma measurable_at_bot {f : α → β} : measurable_at_filter f ⊥ μ :=
⟨∅, mem_bot_sets, by simp⟩

protected lemma measurable_at_filter.eventually (h : measurable_at_filter f l μ) :
  ∀ᶠ s in l.lift' powerset, ae_measurable f (μ.restrict s) :=
(eventually_lift'_powerset' $ λ s t, ae_measurable.mono_set).2 h

protected lemma measurable_at_filter.filter_mono (h : measurable_at_filter f l μ) (h' : l' ≤ l) :
  measurable_at_filter f l' μ :=
let ⟨s, hsl, hs⟩ := h in ⟨s, h' hsl, hs⟩

protected lemma ae_measurable.measurable_at_filter (h : ae_measurable f μ) :
  measurable_at_filter f l μ :=
⟨univ, univ_mem_sets, by rwa measure.restrict_univ⟩

lemma ae_measurable.measurable_at_filter_of_mem {s} (h : ae_measurable f (μ.restrict s))
  (hl : s ∈ l):
  measurable_at_filter f l μ :=
⟨s, hl, h⟩

protected lemma measurable.measurable_at_filter (h : measurable f) :
  measurable_at_filter f l μ :=
h.ae_measurable.measurable_at_filter

end

namespace measure_theory

section normed_group

lemma has_finite_integral_restrict_of_bounded [normed_group E] {f : α → E} {s : set α}
  {μ : measure α} {C}  (hs : μ s < ∞) (hf : ∀ᵐ x ∂(μ.restrict s), ∥f x∥ ≤ C) :
  has_finite_integral f (μ.restrict s) :=
by haveI : finite_measure (μ.restrict s) := ⟨by rwa [measure.restrict_apply_univ]⟩;
  exact has_finite_integral_of_bounded hf

variables [normed_group E] [measurable_space E] {f g : α → E} {s t : set α} {μ ν : measure α}

/-- A function is `integrable_on` a set `s` if it is almost everywhere measurable on `s` and if the
integral of its pointwise norm over `s` is less than infinity. -/
def integrable_on (f : α → E) (s : set α) (μ : measure α . volume_tac) : Prop :=
integrable f (μ.restrict s)

lemma integrable_on.integrable (h : integrable_on f s μ) :
  integrable f (μ.restrict s) := h

@[simp] lemma integrable_on_empty : integrable_on f ∅ μ :=
by simp [integrable_on, integrable_zero_measure]

@[simp] lemma integrable_on_univ : integrable_on f univ μ ↔ integrable f μ :=
by rw [integrable_on, measure.restrict_univ]

lemma integrable_on_zero : integrable_on (λ _, (0:E)) s μ := integrable_zero _ _ _

lemma integrable_on_const {C : E} : integrable_on (λ _, C) s μ ↔ C = 0 ∨ μ s < ∞ :=
integrable_const_iff.trans $ by rw [measure.restrict_apply_univ]

lemma integrable_on.mono (h : integrable_on f t ν) (hs : s ⊆ t) (hμ : μ ≤ ν) :
  integrable_on f s μ :=
h.mono_measure $ measure.restrict_mono hs hμ

lemma integrable_on.mono_set (h : integrable_on f t μ) (hst : s ⊆ t) :
  integrable_on f s μ :=
h.mono hst (le_refl _)

lemma integrable_on.mono_measure (h : integrable_on f s ν) (hμ : μ ≤ ν) :
  integrable_on f s μ :=
h.mono (subset.refl _) hμ

lemma integrable_on.mono_set_ae (h : integrable_on f t μ) (hst : s ≤ᵐ[μ] t) :
  integrable_on f s μ :=
h.integrable.mono_measure $ restrict_mono_ae hst

lemma integrable.integrable_on (h : integrable f μ) : integrable_on f s μ :=
h.mono_measure $ measure.restrict_le_self

lemma integrable.integrable_on' (h : integrable f (μ.restrict s)) : integrable_on f s μ :=
h

lemma integrable_on.restrict (h : integrable_on f s μ) (hs : measurable_set s) :
  integrable_on f s (μ.restrict t) :=
by { rw [integrable_on, measure.restrict_restrict hs], exact h.mono_set (inter_subset_left _ _) }

lemma integrable_on.left_of_union (h : integrable_on f (s ∪ t) μ) : integrable_on f s μ :=
h.mono_set $ subset_union_left _ _

lemma integrable_on.right_of_union (h : integrable_on f (s ∪ t) μ) : integrable_on f t μ :=
h.mono_set $ subset_union_right _ _

lemma integrable_on.union (hs : integrable_on f s μ) (ht : integrable_on f t μ) :
  integrable_on f (s ∪ t) μ :=
(hs.add_measure ht).mono_measure $ measure.restrict_union_le _ _

@[simp] lemma integrable_on_union :
  integrable_on f (s ∪ t) μ ↔ integrable_on f s μ ∧ integrable_on f t μ :=
⟨λ h, ⟨h.left_of_union, h.right_of_union⟩, λ h, h.1.union h.2⟩

@[simp] lemma integrable_on_singleton_iff {x : α} [measurable_singleton_class α]:
  integrable_on f {x} μ ↔ f x = 0 ∨ μ {x} < ∞ :=
begin
  have : f =ᵐ[μ.restrict {x}] (λ y, f x),
  { filter_upwards [ae_restrict_mem (measurable_set_singleton x)],
    assume a ha,
    simp only [mem_singleton_iff.1 ha] },
  rw [integrable_on, integrable_congr this, integrable_const_iff],
  simp,
end

@[simp] lemma integrable_on_finite_union {s : set β} (hs : finite s)
  {t : β → set α} : integrable_on f (⋃ i ∈ s, t i) μ ↔ ∀ i ∈ s, integrable_on f (t i) μ :=
begin
  apply hs.induction_on,
  { simp },
  { intros a s ha hs hf, simp [hf, or_imp_distrib, forall_and_distrib] }
end

@[simp] lemma integrable_on_finset_union  {s : finset β} {t : β → set α} :
  integrable_on f (⋃ i ∈ s, t i) μ ↔ ∀ i ∈ s, integrable_on f (t i) μ :=
integrable_on_finite_union s.finite_to_set

lemma integrable_on.add_measure (hμ : integrable_on f s μ) (hν : integrable_on f s ν) :
  integrable_on f s (μ + ν) :=
by { delta integrable_on, rw measure.restrict_add, exact hμ.integrable.add_measure hν }

@[simp] lemma integrable_on_add_measure :
  integrable_on f s (μ + ν) ↔ integrable_on f s μ ∧ integrable_on f s ν :=
⟨λ h, ⟨h.mono_measure (measure.le_add_right (le_refl _)),
  h.mono_measure (measure.le_add_left (le_refl _))⟩,
  λ h, h.1.add_measure h.2⟩

lemma integrable_indicator_iff (hs : measurable_set s) :
  integrable (indicator s f) μ ↔ integrable_on f s μ :=
by simp [integrable_on, integrable, has_finite_integral, nnnorm_indicator_eq_indicator_nnnorm,
  ennreal.coe_indicator, lintegral_indicator _ hs, ae_measurable_indicator_iff hs]

lemma integrable_on.indicator (h : integrable_on f s μ) (hs : measurable_set s) :
  integrable (indicator s f) μ :=
(integrable_indicator_iff hs).2 h

lemma integrable.indicator (h : integrable f μ) (hs : measurable_set s) :
  integrable (indicator s f) μ :=
h.integrable_on.indicator hs

lemma integrable_indicator_const_Lp {E} [normed_group E] [measurable_space E] [borel_space E]
  [second_countable_topology E] {p : ℝ≥0∞} {s : set α} (hs : measurable_set s) (hμs : μ s ≠ ∞)
  (c : E) :
  integrable (indicator_const_Lp p hs hμs c) μ :=
begin
  rw [integrable_congr indicator_const_Lp_coe_fn, integrable_indicator_iff hs, integrable_on,
    integrable_const_iff, lt_top_iff_ne_top],
  right,
  simpa only [set.univ_inter, measurable_set.univ, measure.restrict_apply] using hμs,
end

/-- We say that a function `f` is *integrable at filter* `l` if it is integrable on some
set `s ∈ l`. Equivalently, it is eventually integrable on `s` in `l.lift' powerset`. -/
def integrable_at_filter (f : α → E) (l : filter α) (μ : measure α . volume_tac) :=
∃ s ∈ l, integrable_on f s μ

variables {l l' : filter α}

protected lemma integrable_at_filter.eventually (h : integrable_at_filter f l μ) :
  ∀ᶠ s in l.lift' powerset, integrable_on f s μ :=
by { refine (eventually_lift'_powerset' $ λ s t hst ht, _).2 h, exact ht.mono_set hst }

lemma integrable_at_filter.filter_mono (hl : l ≤ l') (hl' : integrable_at_filter f l' μ) :
  integrable_at_filter f l μ :=
let ⟨s, hs, hsf⟩ := hl' in ⟨s, hl hs, hsf⟩

lemma integrable_at_filter.inf_of_left (hl : integrable_at_filter f l μ) :
  integrable_at_filter f (l ⊓ l') μ :=
hl.filter_mono inf_le_left

lemma integrable_at_filter.inf_of_right (hl : integrable_at_filter f l μ) :
  integrable_at_filter f (l' ⊓ l) μ :=
hl.filter_mono inf_le_right

@[simp] lemma integrable_at_filter.inf_ae_iff {l : filter α} :
  integrable_at_filter f (l ⊓ μ.ae) μ ↔ integrable_at_filter f l μ :=
begin
  refine ⟨_, λ h, h.filter_mono inf_le_left⟩,
  rintros ⟨s, ⟨t, ht, u, hu, hs⟩, hf⟩,
  refine ⟨t, ht, _⟩,
  refine hf.integrable.mono_measure (λ v hv, _),
  simp only [measure.restrict_apply hv],
  refine measure_mono_ae (mem_sets_of_superset hu $ λ x hx, _),
  exact λ ⟨hv, ht⟩, ⟨hv, hs ⟨ht, hx⟩⟩
end

alias integrable_at_filter.inf_ae_iff ↔ measure_theory.integrable_at_filter.of_inf_ae _

/-- If `μ` is a measure finite at filter `l` and `f` is a function such that its norm is bounded
above at `l`, then `f` is integrable at `l`. -/
lemma measure.finite_at_filter.integrable_at_filter {l : filter α} [is_measurably_generated l]
  (hfm : measurable_at_filter f l μ) (hμ : μ.finite_at_filter l)
  (hf : l.is_bounded_under (≤) (norm ∘ f)) :
  integrable_at_filter f l μ :=
begin
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ s in (l.lift' powerset), ∀ x ∈ s, ∥f x∥ ≤ C,
    from hf.imp (λ C hC, eventually_lift'_powerset.2 ⟨_, hC, λ t, id⟩),
  rcases (hfm.eventually.and (hμ.eventually.and hC)).exists_measurable_mem_of_lift'
    with ⟨s, hsl, hsm, hfm, hμ, hC⟩,
  refine ⟨s, hsl, ⟨hfm, has_finite_integral_restrict_of_bounded hμ _⟩⟩,
  exact C,
  rw [ae_restrict_eq hsm, eventually_inf_principal],
  exact eventually_of_forall hC
end

lemma measure.finite_at_filter.integrable_at_filter_of_tendsto_ae
  {l : filter α} [is_measurably_generated l] (hfm : measurable_at_filter f l μ)
  (hμ : μ.finite_at_filter l) {b} (hf : tendsto f (l ⊓ μ.ae) (𝓝 b)) :
  integrable_at_filter f l μ :=
(hμ.inf_of_left.integrable_at_filter (hfm.filter_mono inf_le_left)
  hf.norm.is_bounded_under_le).of_inf_ae

alias measure.finite_at_filter.integrable_at_filter_of_tendsto_ae ←
  filter.tendsto.integrable_at_filter_ae

lemma measure.finite_at_filter.integrable_at_filter_of_tendsto {l : filter α}
  [is_measurably_generated l] (hfm : measurable_at_filter f l μ) (hμ : μ.finite_at_filter l)
  {b} (hf : tendsto f l (𝓝 b)) :
  integrable_at_filter f l μ :=
hμ.integrable_at_filter hfm hf.norm.is_bounded_under_le

alias measure.finite_at_filter.integrable_at_filter_of_tendsto ← filter.tendsto.integrable_at_filter

variables [borel_space E] [second_countable_topology E]

lemma integrable_add [opens_measurable_space E] {f g : α → E}
  (h : disjoint (support f) (support g)) (hf : measurable f) (hg : measurable g) :
  integrable (f + g) μ ↔ integrable f μ ∧ integrable g μ :=
begin
  refine ⟨λ hfg, ⟨_, _⟩, λ h, h.1.add h.2⟩,
  { rw ← indicator_add_eq_left h, exact hfg.indicator (measurable_set_support hf) },
  { rw ← indicator_add_eq_right h, exact hfg.indicator (measurable_set_support hg) }
end

end normed_group

end measure_theory

open measure_theory asymptotics metric

variables [measurable_space E] [normed_group E]

/-- If a function is integrable at `𝓝[s] x` for each point `x` of a compact set `s`, then it is
integrable on `s`. -/
lemma is_compact.integrable_on_of_nhds_within [topological_space α] {μ : measure α} {s : set α}
  (hs : is_compact s) {f : α → E} (hf : ∀ x ∈ s, integrable_at_filter f (𝓝[s] x) μ) :
  integrable_on f s μ :=
is_compact.induction_on hs integrable_on_empty (λ s t hst ht, ht.mono_set hst)
  (λ s t hs ht, hs.union ht) hf

/-- A function which is continuous on a set `s` is almost everywhere measurable with respect to
`μ.restrict s`. -/
lemma continuous_on.ae_measurable [topological_space α] [opens_measurable_space α] [borel_space E]
  {f : α → E} {s : set α} {μ : measure α} (hf : continuous_on f s) (hs : measurable_set s) :
  ae_measurable f (μ.restrict s) :=
begin
  refine ⟨indicator s f, _, (indicator_ae_eq_restrict hs).symm⟩,
  apply measurable_of_is_open,
  assume t ht,
  obtain ⟨u, u_open, hu⟩ : ∃ (u : set α), is_open u ∧ f ⁻¹' t ∩ s = u ∩ s :=
    _root_.continuous_on_iff'.1 hf t ht,
  rw [indicator_preimage, set.ite, hu],
  exact (u_open.measurable_set.inter hs).union ((measurable_zero ht.measurable_set).diff hs)
end

lemma continuous_on.integrable_at_nhds_within
  [topological_space α] [opens_measurable_space α] [borel_space E]
  {μ : measure α} [locally_finite_measure μ] {a : α} {t : set α} {f : α → E}
  (hft : continuous_on f t) (ht : measurable_set t) (ha : a ∈ t) :
  integrable_at_filter f (𝓝[t] a) μ :=
by haveI : (𝓝[t] a).is_measurably_generated := ht.nhds_within_is_measurably_generated _;
exact (hft a ha).integrable_at_filter ⟨_, self_mem_nhds_within, hft.ae_measurable ht⟩
  (μ.finite_at_nhds_within _ _)

/-- A function `f` continuous on a compact set `s` is integrable on this set with respect to any
locally finite measure. -/
lemma continuous_on.integrable_on_compact
  [topological_space α] [opens_measurable_space α] [borel_space E]
  [t2_space α] {μ : measure α} [locally_finite_measure μ]
  {s : set α} (hs : is_compact s) {f : α → E} (hf : continuous_on f s) :
  integrable_on f s μ :=
hs.integrable_on_of_nhds_within $ λ x hx, hf.integrable_at_nhds_within hs.measurable_set hx

lemma continuous_on.integrable_on_Icc [borel_space E]
  [conditionally_complete_linear_order β] [topological_space β] [order_topology β]
  [measurable_space β] [opens_measurable_space β] {μ : measure β} [locally_finite_measure μ]
  {a b : β} {f : β → E} (hf : continuous_on f (Icc a b)) :
  integrable_on f (Icc a b) μ :=
hf.integrable_on_compact is_compact_Icc

lemma continuous_on.integrable_on_interval [borel_space E]
  [conditionally_complete_linear_order β] [topological_space β] [order_topology β]
  [measurable_space β] [opens_measurable_space β] {μ : measure β} [locally_finite_measure μ]
  {a b : β} {f : β → E} (hf : continuous_on f (interval a b)) :
  integrable_on f (interval a b) μ :=
hf.integrable_on_compact is_compact_interval

/-- A continuous function `f` is integrable on any compact set with respect to any locally finite
measure. -/
lemma continuous.integrable_on_compact
  [topological_space α] [opens_measurable_space α] [t2_space α]
  [borel_space E] {μ : measure α} [locally_finite_measure μ] {s : set α}
  (hs : is_compact s) {f : α → E} (hf : continuous f) :
  integrable_on f s μ :=
hf.continuous_on.integrable_on_compact hs

lemma continuous.integrable_on_Icc [borel_space E]
  [conditionally_complete_linear_order β] [topological_space β] [order_topology β]
  [measurable_space β] [opens_measurable_space β] {μ : measure β} [locally_finite_measure μ]
  {a b : β} {f : β → E} (hf : continuous f) :
  integrable_on f (Icc a b) μ :=
hf.integrable_on_compact is_compact_Icc

lemma continuous.integrable_on_interval [borel_space E]
  [conditionally_complete_linear_order β] [topological_space β] [order_topology β]
  [measurable_space β] [opens_measurable_space β] {μ : measure β} [locally_finite_measure μ]
  {a b : β} {f : β → E} (hf : continuous f) :
  integrable_on f (interval a b) μ :=
hf.integrable_on_compact is_compact_interval

/-- A continuous function with compact closure of the support is integrable on the whole space. -/
lemma continuous.integrable_of_compact_closure_support
  [topological_space α] [opens_measurable_space α] [t2_space α] [borel_space E]
  {μ : measure α} [locally_finite_measure μ] {f : α → E} (hf : continuous f)
  (hfc : is_compact (closure $ support f)) :
  integrable f μ :=
begin
  rw [← indicator_eq_self.2 (@subset_closure _ _ (support f)),
    integrable_indicator_iff is_closed_closure.measurable_set],
  { exact hf.integrable_on_compact hfc },
  { apply_instance }
end

lemma measure_theory.integrable_on.mul_continuous_on
  [topological_space α] [opens_measurable_space α] [t2_space α]
  {μ : measure α} {s : set α} {f g : α → ℝ}
  (hf : integrable_on f s μ) (hg : continuous_on g s) (hs : is_compact s) :
  integrable_on (λ x, f x * g x) s μ :=
begin
  rcases is_compact.exists_bound_of_continuous_on hs hg with ⟨C, hC⟩,
  rw [integrable_on, ← mem_ℒp_one_iff_integrable] at hf ⊢,
  have : ∀ᵐ x ∂(μ.restrict s), ∥f x * g x∥ ≤ C * ∥f x∥,
  { filter_upwards [ae_restrict_mem hs.measurable_set],
    assume x hx,
    rw [real.norm_eq_abs, abs_mul, mul_comm, real.norm_eq_abs],
    apply mul_le_mul_of_nonneg_right (hC x hx) (abs_nonneg _) },
  exact mem_ℒp.of_le_mul hf (hf.ae_measurable.mul (hg.ae_measurable hs.measurable_set)) this
end

lemma measure_theory.integrable_on.continuous_on_mul
  [topological_space α] [opens_measurable_space α] [t2_space α]
  {μ : measure α} {s : set α} {f g : α → ℝ}
  (hf : integrable_on f s μ) (hg : continuous_on g s) (hs : is_compact s) :
  integrable_on (λ x, g x * f x) s μ :=
by simpa [mul_comm] using hf.mul_continuous_on hg hs
