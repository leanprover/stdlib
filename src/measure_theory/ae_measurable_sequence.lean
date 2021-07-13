/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.measure_space

/-!
# Sequence of measurable functions associated to a sequence of a.e.-measurable functions

We define here tools to prove statements about limits (infi, supr...) of sequences of
`ae_measurable` functions.
Given a sequence of a.e.-measurable functions `f : ι → α → β` with hypothesis
`hf : ∀ i, ae_measurable (f i) μ`, and a pointwise property `p : α → (ι → β) → Prop` such that we
have `hp : ∀ᵐ x ∂μ, p x (λ n, f n x)`, we define a sequence of measurable functions `ae_seq hf p`
and a measurable set `ae_seq_set hf p`, such that
* `μ (ae_seq_set hf p)ᶜ = 0`
* `x ∈ ae_seq_set hf p → ∀ i : ι, ae_seq hf hp i x = f i x`
* `x ∈ ae_seq_set hf p → p x (λ n, f n x)`
-/

open measure_theory
open_locale classical

variables {α β γ ι : Type*} [measurable_space α] [measurable_space β]
  {f : ι → α → β} {μ : measure α} {p : α → (ι → β) → Prop}

/-- If we have the additional hypothesis `∀ᵐ x ∂μ, p x (λ n, f n x)`, this is a measurable set
whose complement has measure 0 such that for all `x ∈ ae_seq_set`, `f i x` is equal to
`(hf i).mk (f i) x` for all `i` and we have the pointwise property `p x (λ n, f n x)`. -/
def ae_seq_set (hf : ∀ i, ae_measurable (f i) μ) (p : α → (ι → β) → Prop) : set α :=
(to_measurable μ {x | (∀ i, f i x = (hf i).mk (f i) x) ∧ p x (λ n, f n x)}ᶜ)ᶜ

/-- A sequence of measurable functions that are equal to `f` and verify property `p` on the
measurable set `ae_seq_set hf p`. -/
noncomputable
def ae_seq (hf : ∀ i, ae_measurable (f i) μ) (p : α → (ι → β) → Prop) : ι → α → β :=
λ i x, ite (x ∈ ae_seq_set hf p) ((hf i).mk (f i) x) (⟨f i x⟩ : nonempty β).some

namespace ae_seq

section mem_ae_seq_set

lemma mk_eq_fun_of_mem_ae_seq_set (hf : ∀ i, ae_measurable (f i) μ) {x : α}
  (hx : x ∈ ae_seq_set hf p) (i : ι) :
  (hf i).mk (f i) x = f i x :=
begin
  have h_ss : ae_seq_set hf p ⊆ {x | ∀ i, f i x = (hf i).mk (f i) x},
  { rw [ae_seq_set, ←compl_compl {x | ∀ i, f i x = (hf i).mk (f i) x}, set.compl_subset_compl],
    refine set.subset.trans (set.compl_subset_compl.mpr (λ x h, _)) (subset_to_measurable _ _),
    exact h.1, },
  exact (h_ss hx i).symm,
end

lemma ae_seq_eq_mk_of_mem_ae_seq_set (hf : ∀ i, ae_measurable (f i) μ) {x : α}
  (hx : x ∈ ae_seq_set hf p) (i : ι) :
  ae_seq hf p i x = (hf i).mk (f i) x :=
by simp only [ae_seq, hx, if_true]

lemma ae_seq_eq_fun_of_mem_ae_seq_set (hf : ∀ i, ae_measurable (f i) μ) {x : α}
  (hx : x ∈ ae_seq_set hf p) (i : ι) :
  ae_seq hf p i x = f i x :=
by simp only [ae_seq_eq_mk_of_mem_ae_seq_set hf hx i, mk_eq_fun_of_mem_ae_seq_set hf hx i]

lemma prop_of_mem_ae_seq_set (hf : ∀ i, ae_measurable (f i) μ)
  {x : α} (hx : x ∈ ae_seq_set hf p) :
  p x (λ n, ae_seq hf p n x) :=
begin
  simp only [ae_seq, hx, if_true],
  rw funext (λ n, mk_eq_fun_of_mem_ae_seq_set hf hx n),
  have h_ss : ae_seq_set hf p ⊆ {x | p x (λ n, f n x)},
  { rw [←compl_compl {x | p x (λ n, f n x)}, ae_seq_set, set.compl_subset_compl],
    refine set.subset.trans (set.compl_subset_compl.mpr _) (subset_to_measurable _ _),
    exact λ x hx, hx.2, },
  have hx' := set.mem_of_subset_of_mem h_ss hx,
  exact hx',
end

lemma fun_prop_of_mem_ae_seq_set (hf : ∀ i, ae_measurable (f i) μ)
  {x : α} (hx : x ∈ ae_seq_set hf p) :
  p x (λ n, f n x) :=
begin
  have h_eq : (λ n, f n x) = λ n, ae_seq hf p n x,
    from funext (λ n, (ae_seq_eq_fun_of_mem_ae_seq_set hf hx n).symm),
  rw h_eq,
  exact prop_of_mem_ae_seq_set hf hx,
end

end mem_ae_seq_set

lemma ae_seq_set_measurable_set {hf : ∀ i, ae_measurable (f i) μ} :
  measurable_set (ae_seq_set hf p) :=
(measurable_set_to_measurable _ _).compl

lemma measurable (hf : ∀ i, ae_measurable (f i) μ) (p : α → (ι → β) → Prop)
  (i : ι) :
  measurable (ae_seq hf p i) :=
begin
  refine measurable.ite ae_seq_set_measurable_set (hf i).measurable_mk _,
  casesI (is_empty_or_nonempty α).symm with hα,
  { exact @measurable_const _ _ _ _ (hα.map (f i) : nonempty β).some },
  { exact measurable_of_is_empty _ },
end

lemma measure_compl_ae_seq_set_eq_zero [encodable ι] (hf : ∀ i, ae_measurable (f i) μ)
  (hp : ∀ᵐ x ∂μ, p x (λ n, f n x)) :
  μ (ae_seq_set hf p)ᶜ = 0 :=
begin
  rw [ae_seq_set, compl_compl, measure_to_measurable],
  have hf_eq := λ i, (hf i).ae_eq_mk,
  simp_rw [filter.eventually_eq, ←ae_all_iff] at hf_eq,
  exact filter.eventually.and hf_eq hp,
end

lemma ae_seq_eq_mk_ae [encodable ι] (hf : ∀ i, ae_measurable (f i) μ)
  (hp : ∀ᵐ x ∂μ, p x (λ n, f n x)) :
  ∀ᵐ (a : α) ∂μ, ∀ (i : ι), ae_seq hf p i a = (hf i).mk (f i) a :=
begin
  have h_ss : ae_seq_set hf p ⊆ {a : α | ∀ i, ae_seq hf p i a = (hf i).mk (f i) a},
    from λ x hx i, by simp only [ae_seq, hx, if_true],
  exact le_antisymm (le_trans (measure_mono (set.compl_subset_compl.mpr h_ss))
    (le_of_eq (measure_compl_ae_seq_set_eq_zero hf hp))) (zero_le _),
end

lemma ae_seq_eq_fun_ae [encodable ι] (hf : ∀ i, ae_measurable (f i) μ)
  (hp : ∀ᵐ x ∂μ, p x (λ n, f n x)) :
  ∀ᵐ (a : α) ∂μ, ∀ (i : ι), ae_seq hf p i a = f i a :=
begin
  have h_ss : {a : α | ¬∀ (i : ι), ae_seq hf p i a = f i a} ⊆ (ae_seq_set hf p)ᶜ,
    from λ x, mt (λ hx i, (ae_seq_eq_fun_of_mem_ae_seq_set hf hx i)),
  exact measure_mono_null h_ss (measure_compl_ae_seq_set_eq_zero hf hp),
end

lemma ae_seq_n_eq_fun_n_ae [encodable ι] (hf : ∀ i, ae_measurable (f i) μ)
  (hp : ∀ᵐ x ∂μ, p x (λ n, f n x)) (n : ι) :
  ae_seq hf p n =ᵐ[μ] f n:=
ae_all_iff.mp (ae_seq_eq_fun_ae hf hp) n

lemma supr [complete_lattice β] [encodable ι]
  (hf : ∀ i, ae_measurable (f i) μ) (hp : ∀ᵐ x ∂μ, p x (λ n, f n x)) :
  (⨆ n, ae_seq hf p n) =ᵐ[μ] ⨆ n, f n :=
begin
  simp_rw [filter.eventually_eq, ae_iff, supr_apply],
  have h_ss : ae_seq_set hf p ⊆ {a : α | (⨆ (i : ι), ae_seq hf p i a) = ⨆ (i : ι), f i a},
  { intros x hx,
    congr,
    exact funext (λ i, ae_seq_eq_fun_of_mem_ae_seq_set hf hx i), },
  exact measure_mono_null (set.compl_subset_compl.mpr h_ss)
    (measure_compl_ae_seq_set_eq_zero hf hp),
end

end ae_seq
