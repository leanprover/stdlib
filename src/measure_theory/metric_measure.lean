/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import topology.metric_space.metric_separated
import measure_theory.borel_space
import analysis.special_functions.pow

/-!
# Metric (outer) measures and Hausdorff measure

We say that an outer measure `μ` is a *metric* outer measure (see
`measure_theory.outer_measure.is_metric`) if for any two metric separated sets `s` and `t`
(i.e. sets such that distances between `x ∈ s` and `y ∈ t` are uniformly bounded from below by a
positive constant) we have `μ (s ∪ t) = μ s + μ t`.

A theorem due to Caratheodory (see `measure_theory.outer_measure.is_metric.borel_le_caratheodory`)
says that for a metric outer measure all borel sets are Caratheodory measurable, hence we can turn
it into a `measure_theory.measure` using `measure_theory.outer_measure.to_measure`.

Probably the most well-known metric outer measure is the `d`-dimensional Hausdorff measure, see
`measure_theory.measure.hausdorff_measure`. In this file we define a more general constructor of
metric outer measures and prove some basic properties.

A common way to construct metric measures is to put
`μ s = ⨆ r > 0, ⨅ (t : ℕ → set α) (hts : s ⊆ ⋃ n, t n)
  (htr : ∀ n, emetric.diam (t n) < r), f (t n)`,
where `f : set α → ℝ≥0∞` is a function on sets such that `f ∅ = 0`.
We formalize this definition as `measure_theory.outer_measure.mk_metric'`. 

If we put `f t = (emetric.diam t) ^ d`, then we get the `d`-dimensional Hausdorff measure.
TODO
-/

open_locale nnreal ennreal topological_space big_operators

open emetric set function filter

noncomputable theory

variables {ι X Y : Type*} [emetric_space X] [emetric_space Y]

namespace measure_theory

namespace outer_measure

/-- We say that an outer measure `μ` in an (e)metric space is *metric* if `μ (s ∪ t) = μ s + μ t`
for any two metric separated sets `s`, `t`. -/
def is_metric (μ : outer_measure X) : Prop :=
∀ (s t : set X), is_metric_separated s t → μ (s ∪ t) = μ s + μ t

namespace is_metric

variables {μ : outer_measure X}

/-- A metric outer measure is additive on a finite set of pairwise metric separated sets. -/
lemma finset_Union_of_pairwise_separated (hm : is_metric μ) {I : finset ι} {s : ι → set X}
  (hI : ∀ (i ∈ I) (j ∈ I), i ≠ j → is_metric_separated (s i) (s j)) :
  μ (⋃ i ∈ I, s i) = ∑ i in I, μ (s i) :=
begin
  classical,
  induction I using finset.induction_on with i I hiI ihI hI, { simp },
  simp only [finset.mem_insert] at hI,
  rw [finset.set_bUnion_insert, hm, ihI, finset.sum_insert hiI],
  exacts [λ i hi j hj hij, (hI i (or.inr hi) j (or.inr hj) hij),
    is_metric_separated.finset_Union_right
      (λ j hj, hI i (or.inl rfl) j (or.inr hj) (ne_of_mem_of_not_mem hj hiI).symm)]
end

/-- Caratheodory theorem. If `m` is a metric outer measure, then every Borel measurable set `t` is
Caratheodory measurable: for any (not necessarily measurable) set `s` we have
`μ (s ∩ t) + μ (s \ t) = μ s`. -/
lemma borel_le_caratheodory (hm : is_metric μ) :
  borel X ≤ μ.caratheodory :=
begin
  rw [borel_eq_generate_from_is_closed],
  refine measurable_space.generate_from_le (λ t ht, μ.is_caratheodory_iff_le.2 $ λ s, _),
  set S : ℕ → set X := λ n, {x ∈ s | (↑n)⁻¹ ≤ inf_edist x t},
  have n0 : ∀ {n : ℕ}, (n⁻¹ : ℝ≥0∞) ≠ 0, from λ n, ennreal.inv_ne_zero.2 ennreal.coe_nat_ne_top,
  have Ssep : ∀ n, is_metric_separated (S n) t,
    from λ n, ⟨n⁻¹, n0, λ x hx y hy, hx.2.trans $ inf_edist_le_edist_of_mem hy⟩,
  have Ssep' : ∀ n, is_metric_separated (S n) (s ∩ t),
    from λ n, (Ssep n).mono subset.rfl (inter_subset_right _ _),
  have S_sub : ∀ n, S n ⊆ s \ t,
    from λ n, subset_inter (inter_subset_left _ _) (Ssep n).subset_compl_right,
  have hSs : ∀ n, μ (s ∩ t) + μ (S n) ≤ μ s, from λ n,
  calc μ (s ∩ t) + μ (S n) = μ (s ∩ t ∪ S n) :
    eq.symm $ hm _ _ $ (Ssep' n).symm
  ... ≤ μ (s ∩ t ∪ s \ t)  : by { mono*, exact le_rfl }
  ... = μ s : by rw [inter_union_diff],
  have Union_S : (⋃ n, S n) = s \ t,
  { refine subset.antisymm (Union_subset S_sub) _,
    rintro x ⟨hxs, hxt⟩,
    rw mem_iff_ind_edist_zero_of_closed ht at hxt,
    rcases ennreal.exists_inv_nat_lt hxt with ⟨n, hn⟩,
    exact mem_Union.2 ⟨n, hxs, hn.le⟩ },
  /- Now we have `∀ n, m (s ∩ t) + m (S n) ≤ m s` and we need to prove
  `m (s ∩ t) + m (⋃ n, S n) ≤ m s`. We can't pass to the limit because
  `m` is only an outer measure. -/
  by_cases htop : μ (s \ t) = ∞,
  { rw [htop, ennreal.add_top, ← htop],
    exact μ.mono (diff_subset _ _) },
  suffices : μ (⋃ n, S n) ≤ ⨆ n, μ (S n),
  calc μ (s ∩ t) + μ (s \ t) = μ (s ∩ t) + μ (⋃ n, S n) :
    by rw Union_S
  ... ≤ μ (s ∩ t) + ⨆ n, μ (S n) :
    add_le_add le_rfl this
  ... = ⨆ n, μ (s ∩ t) + μ (S n) : ennreal.add_supr
  ... ≤ μ s : supr_le hSs,
  /- It suffices to show that `∑' k, μ (S (k + 1) \ S k) ≠ ∞`. Indeed, if we have this,
  then for all `N` we have `μ (⋃ n, S n) ≤ μ (S N) + ∑' k, m (S (N + k + 1) \ S (N + k))`
  and the second term tends to zero, see `outer_measure.Union_nat_of_monotone_of_tsum_ne_top`
  for details. -/
  have : ∀ n, S n ⊆ S (n + 1), from λ n x hx,
    ⟨hx.1, le_trans (ennreal.inv_le_inv.2 $ ennreal.coe_nat_le_coe_nat.2 n.le_succ) hx.2⟩,
  refine (μ.Union_nat_of_monotone_of_tsum_ne_top this _).le, clear this,
  /- While the sets `S (k + 1) \ S k` are not pairwise metric separated, the sets in each
  subsequence `S (2 * k + 1) \ S (2 * k)` and `S (2 * k + 2) \ S (2 * k)` are metric separated,
  so `m` is additive on each of those sequences. -/
  rw [← tsum_even_add_odd ennreal.summable ennreal.summable, ennreal.add_ne_top],
  suffices : ∀ a, (∑' (k : ℕ), μ (S (2 * k + 1 + a) \ S (2 * k + a))) ≠ ∞,
    from ⟨by simpa using this 0, by simpa using this 1⟩,
  refine λ r, ne_top_of_le_ne_top htop _,
  rw [← Union_S, ennreal.tsum_eq_supr_nat, supr_le_iff],
  intro n,
  rw [← hm.finset_Union_of_pairwise_separated],
  { exact μ.mono (Union_subset $ λ i, Union_subset $ λ hi x hx, mem_Union.2 ⟨_, hx.1⟩) },
  suffices : ∀ i  j, i < j → is_metric_separated (S (2 * i + 1 + r)) (s \ S (2 * j + r)),
    from λ i _ j _ hij, hij.lt_or_lt.elim
      (λ h, (this i j h).mono (inter_subset_left _ _) (λ x hx, ⟨hx.1.1, hx.2⟩))
      (λ h, (this j i h).symm.mono  (λ x hx, ⟨hx.1.1, hx.2⟩) (inter_subset_left _ _)),
  intros i j hj,
  have A : ((↑(2 * j + r))⁻¹ : ℝ≥0∞) < (↑(2 * i + 1 + r))⁻¹,
    by { rw [ennreal.inv_lt_inv, ennreal.coe_nat_lt_coe_nat], linarith },
  refine ⟨(↑(2 * i + 1 + r))⁻¹ - (↑(2 * j + r))⁻¹, by simpa using A, λ x hx y hy, _⟩,
  have : inf_edist y t < (↑(2 * j + r))⁻¹, from not_le.1 (λ hle, hy.2 ⟨hy.1, hle⟩),
  rcases exists_edist_lt_of_inf_edist_lt this with ⟨z, hzt, hyz⟩,
  have hxz : (↑(2 * i + 1 + r))⁻¹ ≤ edist x z, from le_inf_edist.1 hx.2 _ hzt,
  apply ennreal.le_of_add_le_add_right (hyz.trans_le le_top),
  refine le_trans _ (edist_triangle _ _ _),
  refine (add_le_add le_rfl hyz.le).trans (eq.trans_le _ hxz),
  rw [ennreal.sub_add_cancel_of_le A.le]
end

lemma le_caratheodory [measurable_space X] [borel_space X] (hm : is_metric μ) :
  ‹_› ≤ μ.caratheodory :=
by { rw @borel_space.measurable_eq X _ _, exact hm.borel_le_caratheodory }

end is_metric

/-- Auxiliary definition for `outer_measure.mk_metric'`: given a function on sets
`m : set X → ℝ≥0∞`, returns the maximal outer measure `μ` such that `μ s ≤ m s`
for any set `s` of diamenter at most `r`.-/
def mk_metric'.pre (m : set X → ℝ≥0∞) (r : ℝ≥0∞) :
  outer_measure X :=
bounded_by $ extend (λ s (hs : diam s ≤ r), m s)

/-- Given a function `m : set X → ℝ≥0∞`, `mk_metric' m` is the supremum of `mk_metric'.pre m r`
over `r > 0`. Equivalently, it is the limit of `mk_metric'.pre m r` as `r` tends to zero from
the right. -/
def mk_metric' (m : set X → ℝ≥0∞) :
  outer_measure X :=
⨆ r > 0, mk_metric'.pre m r

/-- Given a function `m : ℝ≥0∞ → ℝ≥0∞`, `mk_metric m = mk_metric' (λ s, m (emetric.diam s))`
is the supremum of `mk_metric'.pre (λ s, m (emetric.diam s)) r` over `r > 0`. Each
`mk_metric'.pre (λ s, m (emetric.diam s)) r` is the maximal outer measure `μ` such that
`μ s ≤ m (emetric.diam s)` for any set of diameter less than `r`. -/
def mk_metric (m : ℝ≥0∞ → ℝ≥0∞) : outer_measure X :=
mk_metric' (λ s, ⨆ (hs : ¬s.subsingleton), m (diam s))

namespace mk_metric'

variables {m : set X → ℝ≥0∞} {r : ℝ≥0∞} {μ : outer_measure X} {s : set X}

lemma le_pre : μ ≤ pre m r ↔ ∀ s : set X, diam s ≤ r → μ s ≤ m s :=
by simp only [pre, le_bounded_by, extend, le_infi_iff]

lemma pre_le (hs : diam s ≤ r) : pre m r s ≤ m s :=
(bounded_by_le _).trans $ infi_le _ hs

lemma mono_pre (m : set X → ℝ≥0∞) {r r' : ℝ≥0∞} (h : r ≤ r') :
  pre m r' ≤ pre m r :=
le_pre.2 $ λ s hs, pre_le (hs.trans h)

lemma mono_pre_nat (m : set X → ℝ≥0∞) :
  monotone (λ k : ℕ, pre m k⁻¹) :=
λ k l h, le_pre.2 $ λ s hs, pre_le (hs.trans $ by simpa)

lemma tendsto_pre (m : set X → ℝ≥0∞) (s : set X) :
  tendsto (λ r, pre m r s) (𝓝[Ioi 0] 0) (𝓝 $ mk_metric' m s) :=
begin
  rw [← map_coe_Ioi_at_bot, tendsto_map'_iff],
  simp only [mk_metric', outer_measure.supr_apply, supr_subtype'],
  exact tendsto_at_bot_supr (λ r r' hr, mono_pre _ hr _)
end

lemma tendsto_pre_nat (m : set X → ℝ≥0∞) (s : set X) :
  tendsto (λ n : ℕ, pre m n⁻¹ s) at_top (𝓝 $ mk_metric' m s) :=
begin
  refine (tendsto_pre m s).comp (tendsto_inf.2 ⟨ennreal.tendsto_inv_nat_nhds_zero, _⟩),
  refine tendsto_principal.2 (eventually_of_forall $ λ n, _),
  simp
end

lemma eq_supr_nat (m : set X → ℝ≥0∞) :
  mk_metric' m = ⨆ n : ℕ, mk_metric'.pre m n⁻¹ :=
begin
  ext1 s,
  rw supr_apply,
  refine tendsto_nhds_unique (mk_metric'.tendsto_pre_nat m s)
    (tendsto_at_top_supr $ λ k l hkl, mk_metric'.mono_pre_nat m hkl s)
end

lemma trim_pre [measurable_space X] [opens_measurable_space X]
  (m : set X → ℝ≥0∞) (hcl : ∀ s, m (closure s) = m s) (r : ℝ≥0∞) :
  (pre m r).trim = pre m r :=
begin
  refine le_antisymm (le_pre.2 $ λ s hs, _) (le_trim _),
  rw trim_eq_infi,
  refine (infi_le_of_le (closure s) $ infi_le_of_le subset_closure $
    infi_le_of_le measurable_set_closure ((pre_le _).trans_eq (hcl _))),
  rwa diam_closure
end

end mk_metric'

/-- An outer measure constructed using `outer_measure.mk_metric'` is a metric outer measure. -/
lemma mk_metric'_is_metric (m : set X → ℝ≥0∞) :
  (mk_metric' m).is_metric :=
begin
  rintros s t ⟨r, r0, hr⟩,
  refine tendsto_nhds_unique_of_eventually_eq
    (mk_metric'.tendsto_pre _ _)
    ((mk_metric'.tendsto_pre _ _).add (mk_metric'.tendsto_pre _ _)) _,
  rw [← pos_iff_ne_zero] at r0,
  filter_upwards [Ioo_mem_nhds_within_Ioi ⟨le_rfl, r0⟩],
  rintro ε ⟨ε0, εr⟩,
  refine bounded_by_union_of_top_of_nonempty_inter _,
  rintro u ⟨x, hxs, hxu⟩ ⟨y, hyt, hyu⟩,
  have : ε < diam u, from εr.trans_le ((hr x hxs y hyt).trans $ edist_le_diam_of_mem hxu hyu),
  exact infi_eq_top.2 (λ h, (this.not_le h).elim)
end

/-- If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `0 < d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[Ioi 0]]` to state this), then `mk_metric m₁ hm₁ ≤ c • mk_metric m₂ hm₂`. -/
lemma mk_metric_mono_smul {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (h0 : c ≠ 0)
  (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] c • m₂) :
  (mk_metric m₁ : outer_measure X) ≤ c • mk_metric m₂ :=
begin
  classical,
  rcases (mem_nhds_within_Ioi_iff_exists_Ioo_subset' ennreal.zero_lt_one).1 hle with ⟨r, hr0, hr⟩,
  refine λ s, le_of_tendsto_of_tendsto (mk_metric'.tendsto_pre _ s)
    (ennreal.tendsto.const_mul (mk_metric'.tendsto_pre _ s) (or.inr hc))
    (mem_sets_of_superset (Ioo_mem_nhds_within_Ioi ⟨le_rfl, hr0⟩) (λ r' hr', _)),
  simp only [mem_set_of_eq, mk_metric'.pre],
  rw [← smul_apply, smul_bounded_by hc],
  refine le_bounded_by.2 (λ t, (bounded_by_le _).trans _) _,
  simp only [smul_eq_mul, pi.smul_apply, extend, infi_eq_if],
  split_ifs with ht ht,
  { refine supr_le (λ ht₁, _),
    rw [supr_eq_if, if_pos ht₁],
    refine hr ⟨_, ht.trans_lt hr'.2⟩,
    exact pos_iff_ne_zero.2 (mt diam_eq_zero_iff.1 ht₁) },
  { simp [h0] }
end

/-- If `m₁ d ≤ m₂ d` for `0 < d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝[Ioi 0]]` to state this), then
`mk_metric m₁ hm₁ ≤ mk_metric m₂ hm₂`-/
lemma mk_metric_mono {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] m₂) :
  (mk_metric m₁ : outer_measure X) ≤ mk_metric m₂ :=
by { convert mk_metric_mono_smul ennreal.one_ne_top ennreal.zero_lt_one.ne' _; simp * }

lemma isometry_comap_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) {f : X → Y} (hf : isometry f)
  (H : monotone (λ d : {d : ℝ≥0∞ | d ≠ 0}, m d) ∨ surjective f) :
  comap f (mk_metric m) = mk_metric m :=
begin
  simp only [mk_metric, mk_metric', mk_metric'.pre, induced_outer_measure, comap_supr],
  refine supr_congr id surjective_id (λ ε, supr_congr id surjective_id $ λ hε, _),
  rw comap_bounded_by _ (H.imp (λ h_mono, _) id),
  { congr' with s : 1,
    apply extend_congr,
    { simp [hf.ediam_image] },
    { intros, simp [hf.injective.subsingleton_image_iff, hf.ediam_image] } },
  { refine λ s t hst, infi_le_infi2 (λ ht, ⟨(diam_mono hst).trans ht, supr_le $ λ hs, _⟩),
    have ht : ¬(t : set Y).subsingleton, from λ ht, hs (ht.mono hst),
    refine (@h_mono ⟨_, mt diam_eq_zero_iff.1 hs⟩ ⟨_, mt diam_eq_zero_iff.1 ht⟩
      (diam_mono hst)).trans _,
    exact le_supr (λ h : ¬(t : set Y).subsingleton, m (diam (t : set Y))) ht }
end

lemma isometry_map_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) {f : X → Y} (hf : isometry f)
  (H : monotone (λ d : {d : ℝ≥0∞ | d ≠ 0}, m d) ∨ surjective f) :
  map f (mk_metric m) = restrict (range f) (mk_metric m) :=
by rw [← isometry_comap_mk_metric _ hf H, map_comap]

lemma isometric_comap_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (f : X ≃ᵢ Y) :
  comap f (mk_metric m) = mk_metric m :=
isometry_comap_mk_metric _ f.isometry (or.inr f.surjective)

lemma isometric_map_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (f : X ≃ᵢ Y) :
  map f (mk_metric m) = mk_metric m :=
by rw [← isometric_comap_mk_metric _ f, map_comap_of_surjective f.surjective]

lemma trim_mk_metric [measurable_space X] [borel_space X] (m : ℝ≥0∞ → ℝ≥0∞) :
  (mk_metric m : outer_measure X).trim = mk_metric m :=
begin
  simp only [mk_metric, mk_metric'.eq_supr_nat, trim_supr],
  congr' 1 with n : 1,
  refine mk_metric'.trim_pre _ (λ s, _) _,
  simp
end

end outer_measure

namespace measure

variables [measurable_space X] [borel_space X]

/-- Given a function `m : set X → ℝ≥0∞`, `mk_metric' m` is the supremum of `μ r`
over `r > 0`, where `μ r` is the maximal outer measure `μ` such that `μ s ≤ m s`
for all `s`. While each `μ r` is an *outer* measure, the supremum is a measure. -/
def mk_metric' (m : set X → ℝ≥0∞) : measure X :=
(outer_measure.mk_metric' m).to_measure (outer_measure.mk_metric'_is_metric _).le_caratheodory

/-- Given a function `m : ℝ≥0∞ → ℝ≥0∞`, `mk_metric m` is the supremum of `μ r` over `r > 0`, where
`μ r` is the maximal outer measure `μ` such that `μ s ≤ m s` for all sets `s` that contain at least
two points. While each `mk_metric'.pre` is an *outer* measure, the supremum is a measure. -/
def mk_metric (m : ℝ≥0∞ → ℝ≥0∞) : measure X :=
(outer_measure.mk_metric m).to_measure (outer_measure.mk_metric'_is_metric _).le_caratheodory

@[simp] lemma mk_metric'_to_outer_measure (m : set X → ℝ≥0∞) :
  (mk_metric' m).to_outer_measure = (outer_measure.mk_metric' m).trim :=
rfl

@[simp] lemma mk_metric_to_outer_measure (m : ℝ≥0∞ → ℝ≥0∞) :
  (mk_metric m : measure X).to_outer_measure = outer_measure.mk_metric m :=
outer_measure.trim_mk_metric m

end measure

lemma outer_measure.coe_mk_metric [measurable_space X] [borel_space X] (m : ℝ≥0∞ → ℝ≥0∞) :
  ⇑(outer_measure.mk_metric m : outer_measure X) = measure.mk_metric m :=
by rw [← measure.mk_metric_to_outer_measure, coe_to_outer_measure]

namespace measure

variables [measurable_space X] [borel_space X]

/-- If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `0 < d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[Ioi 0]]` to state this), then `mk_metric m₁ hm₁ ≤ c • mk_metric m₂ hm₂`. -/
lemma mk_metric_mono_smul {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (h0 : c ≠ 0)
  (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] c • m₂) :
  (mk_metric m₁ : measure X) ≤ c • mk_metric m₂ :=
begin
  intros s hs,
  rw [← outer_measure.coe_mk_metric, coe_smul, ← outer_measure.coe_mk_metric],
  exact outer_measure.mk_metric_mono_smul hc h0 hle s
end

/-- If `m₁ d ≤ m₂ d` for `0 < d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝[Ioi 0]]` to state this), then
`mk_metric m₁ hm₁ ≤ mk_metric m₂ hm₂`-/
lemma mk_metric_mono {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] m₂) :
  (mk_metric m₁ : measure X) ≤ mk_metric m₂ :=
by { convert mk_metric_mono_smul ennreal.one_ne_top ennreal.zero_lt_one.ne' _; simp * }

/-- Hausdorff measure on an (e)metric space. -/
def hausdorff_measure (d : ℝ) : measure X := mk_metric (λ r, r ^ d)

local notation `μH[` d `]` := hausdorff_measure d

lemma hausdorff_measure_zero_or_top {d₁ d₂ : ℝ} (h : d₁ < d₂) (s : set X) :
  μH[d₂] s = 0 ∨ μH[d₁] s = ∞ :=
begin
  by_contra H, push_neg at H,
  suffices : ∀ (c : ℝ≥0), c ≠ 0 → μH[d₂] s ≤ c * μH[d₁] s,
  { rcases ennreal.exists_nnreal_pos_mul_lt H.2 H.1 with ⟨c, hc0, hc⟩,
    exact hc.not_le (this c (pos_iff_ne_zero.1 hc0)) },
  intros c hc,
  refine le_iff'.1 (mk_metric_mono_smul ennreal.coe_ne_top (by exact_mod_cast hc) _) s,
  have : 0 <  (c ^ (d₂ - d₁)⁻¹ : ℝ≥0∞),
  { rw [ennreal.coe_rpow_of_ne_zero hc, pos_iff_ne_zero, ne.def, ennreal.coe_eq_zero,
      nnreal.rpow_eq_zero_iff],
    exact mt and.left hc },
  filter_upwards [Ioo_mem_nhds_within_Ioi ⟨le_rfl, this⟩],
  rintro r ⟨hr₀, hrc⟩,
  lift r to ℝ≥0 using ne_top_of_lt hrc,
  rw [pi.smul_apply, smul_eq_mul, ← ennreal.div_le_iff_le_mul (or.inr ennreal.coe_ne_top)
    (or.inr $ mt ennreal.coe_eq_zero.1 hc), ← ennreal.rpow_sub _ _ hr₀.ne' ennreal.coe_ne_top],
  refine (ennreal.rpow_lt_rpow hrc (sub_pos.2 h)).le.trans _,
  rw [← ennreal.rpow_mul, inv_mul_cancel (sub_pos.2 h).ne', ennreal.rpow_one],
  exact le_rfl
end

lemma hausdorff_measure_mono {d₁ d₂ : ℝ} (h : d₁ ≤ d₂) (s : set X) : μH[d₂] s ≤ μH[d₁] s :=
begin
  rcases h.eq_or_lt with rfl|h, { exact le_rfl },
  cases hausdorff_measure_zero_or_top h s with hs hs,
  { rw hs, exact zero_le _ },
  { rw hs, exact le_top }
end

/-- Hausdorff dimension of a set in an (e)metric space. -/
def hausdorff_dimension (s : set X) : ℝ≥0∞ := ⨆ (d : ℝ≥0) (hd : μH[d] s = ∞), d

lemma hausdorff_measure_of_lt_hausdorff_dimension {s : set X} {d : ℝ≥0}
  (h : ↑d < hausdorff_dimension s) : μH[d] s = ∞ :=
begin
  simp only [hausdorff_dimension, lt_supr_iff] at h,
  rcases h with ⟨d', hsd', hdd'⟩,
  rw [ennreal.coe_lt_coe, ← nnreal.coe_lt_coe] at hdd',
  refine (hausdorff_measure_zero_or_top hdd' s).resolve_left (λ h, _),
  exact (ennreal.zero_ne_top $ h.symm.trans hsd').elim
end

lemma hausdorff_measure_of_hausdorff_dimension_lt {s : set X} {d : ℝ≥0}
  (h : hausdorff_dimension s < d) : μH[d] s = 0 :=
begin
  rcases ennreal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hsd', hd'd⟩,
  rw [ennreal.coe_lt_coe, ← nnreal.coe_lt_coe] at hd'd,
  exact (hausdorff_measure_zero_or_top hd'd s).resolve_right
    (λ h, hsd'.not_le (le_bsupr d' h))
end

end measure

end measure_theory
