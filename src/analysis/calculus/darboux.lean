/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.mean_value

/-!
# Darboux's theorem

In this file we prove that the derivative of a differentiable function on an interval takes all
intermediate values. The proof is based on the
[Wikipedia](https://en.wikipedia.org/wiki/Darboux%27s_theorem_(analysis)) page about this theorem.
-/

open filter set
open_locale topological_space classical

variables {a b : ℝ} {f f' : ℝ → ℝ}

/-- **Darboux's theorem**: if `a ≤ b` and `f' a < m < f' b`, then `f' c = m` for some 
`c ∈ [a, b]`. -/
theorem exists_has_deriv_within_at_eq_of_gt_of_lt
  (hab : a ≤ b) (hf : ∀ x ∈ (Icc a b), has_deriv_within_at f (f' x) (Icc a b) x)
  {m : ℝ} (hma : f' a < m) (hmb : m < f' b) :
  m ∈ f' '' (Icc a b) :=
begin
  have hab' : a < b,
  { refine lt_of_le_of_ne hab (λ hab', _),
    subst b,
    exact lt_asymm hma hmb },
  set g : ℝ → ℝ := λ x, f x - m * x,
  have hg : ∀ x ∈ Icc a b, has_deriv_within_at g (f' x - m) (Icc a b) x,
  { intros x hx,
    simpa using (hf x hx).sub ((has_deriv_within_at_id x _).const_mul m) },
  obtain ⟨c, cmem, hc⟩ : ∃ c ∈ Icc a b, is_min_on g (Icc a b) c,
    from is_compact_Icc.exists_forall_le (nonempty_Icc.2 $ hab)
      (λ x hx, (hg x hx).continuous_within_at),
  have cmem' : c ∈ Ioo a b,
  { cases eq_or_lt_of_le cmem.1 with hac hac,
    -- Show that `c` can't be equal to `a`
    { subst c,
      refine absurd (sub_nonneg.1 $ nonneg_of_mul_nonneg_left _ (sub_pos.2 hab'))
        (not_le_of_lt hma),
      have : b - a ∈ pos_tangent_cone_at (Icc a b) a,
        from mem_pos_tangent_cone_at_of_segment_subset (segment_eq_Icc hab ▸ subset.refl _),
      simpa [-sub_nonneg, -continuous_linear_map.map_sub]
        using hc.localize.has_fderiv_within_at_nonneg (hg a (left_mem_Icc.2 hab)) this },
    cases eq_or_lt_of_le cmem.2 with hbc hbc,
    -- Show that `c` can't be equal to `b`
    { subst c,
      refine absurd (sub_nonpos.1 $ nonpos_of_mul_nonneg_right _ (sub_lt_zero.2 hab'))
        (not_le_of_lt hmb),
      have : a - b ∈ pos_tangent_cone_at (Icc a b) b,
        from mem_pos_tangent_cone_at_of_segment_subset (by rw [segment_symm, segment_eq_Icc hab]),
      simpa [-sub_nonneg, -continuous_linear_map.map_sub]
        using hc.localize.has_fderiv_within_at_nonneg (hg b (right_mem_Icc.2 hab)) this },
    exact ⟨hac, hbc⟩ },
  use [c, cmem],
  rw [← sub_eq_zero],
  have : Icc a b ∈ 𝓝 c, by rwa [← mem_interior_iff_mem_nhds, interior_Icc],
  exact (hc.is_local_min this).has_deriv_at_eq_zero ((hg c cmem).has_deriv_at this)
end

/-- Darboux's theorem: if `a ≤ b` and `f' a > m > f' b`, then `f' c = m` for some `c ∈ [a, b]`. -/
theorem exists_has_deriv_within_at_eq_of_lt_of_gt
  (hab : a ≤ b) (hf : ∀ x ∈ (Icc a b), has_deriv_within_at f (f' x) (Icc a b) x)
  {m : ℝ} (hma : m < f' a) (hmb : f' b < m) :
  m ∈ f' '' (Icc a b) :=
let ⟨c, cmem, hc⟩ := exists_has_deriv_within_at_eq_of_gt_of_lt hab (λ x hx, (hf x hx).neg)
  (neg_lt_neg hma) (neg_lt_neg hmb)
in ⟨c, cmem, neg_injective hc⟩

/-- Darboux's theorem: the image of a convex set under `f'` is a convex set. -/
theorem convex_image_has_deriv_at {s : set ℝ} (hs : convex s)
  (hf : ∀ x ∈ s, has_deriv_at f (f' x) x) :
  convex (f' '' s) :=
begin
  refine real.convex_iff_ord_connected.2 ⟨_⟩,
  rintros _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ m ⟨hma, hmb⟩,
  cases eq_or_lt_of_le hma with hma hma,
    by exact hma ▸ mem_image_of_mem f' ha,
  cases eq_or_lt_of_le hmb with hmb hmb,
    by exact hmb.symm ▸ mem_image_of_mem f' hb,
  cases le_total a b with hab hab,
  { have : Icc a b ⊆ s, from hs.ord_connected.out ha hb,
    rcases exists_has_deriv_within_at_eq_of_gt_of_lt hab
      (λ x hx, (hf x $ this hx).has_deriv_within_at) hma hmb
      with ⟨c, cmem, hc⟩,
    exact ⟨c, this cmem, hc⟩ },
  { have : Icc b a ⊆ s, from hs.ord_connected.out hb ha,
    rcases exists_has_deriv_within_at_eq_of_lt_of_gt hab
      (λ x hx, (hf x $ this hx).has_deriv_within_at) hmb hma
      with ⟨c, cmem, hc⟩,
    exact ⟨c, this cmem, hc⟩ }
end

/-- If the derivative of a function is never equal to `m`, then either
it is always greater than `m`, or it is always less than `m`. -/
theorem deriv_forall_lt_or_forall_gt_of_forall_ne {s : set ℝ} (hs : convex s)
  (hf : ∀ x ∈ s, has_deriv_at f (f' x) x) {m : ℝ} (hf' : ∀ x ∈ s, f' x ≠ m) :
  (∀ x ∈ s, f' x < m) ∨ (∀ x ∈ s, m < f' x) :=
begin
  contrapose! hf',
  rcases hf' with ⟨⟨b, hb, hmb⟩, ⟨a, ha, hma⟩⟩,
  exact (convex_image_has_deriv_at hs hf).ord_connected.out (mem_image_of_mem f' ha)
    (mem_image_of_mem f' hb) ⟨hma, hmb⟩
end
