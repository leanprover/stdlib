/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.calculus.mean_value

/-!
# L'Hôpital's rule for 0/0 indeterminate forms

In this file, we prove several forms of "L'Hopital's rule" for computing 0/0
indeterminate forms. The proof of `has_deriv_at.lhopital_zero_right_on_Ioo`
is based on the one given in the corresponding
[Wikibooks](https://en.wikibooks.org/wiki/Calculus/L%27H%C3%B4pital%27s_Rule)
chapter, and all other statements are derived from this one by composing by
carefully chosen functions.

Note that the filter `f'/g'` tends to isn't required to be one of `𝓝 a`,
`at_top` or `at_bot`. In fact, we give a slightly stronger statement by
allowing it to be any filter on `ℝ`.

Each statement is available in a `has_deriv_at` form and a `deriv` form, which
is denoted by each statement being in either the `has_deriv_at` or the `deriv`
namespace.

## Tags

L'Hôpital's rule, L'Hopital's rule
-/

open filter set
open_locale filter topological_space

variables {a b : ℝ} (hab : a < b) {l : filter ℝ} {f f' g g' : ℝ → ℝ}

/-!
## Interval-based versions

We start by proving statements where all conditions (derivability, `g' ≠ 0`) have
to be satisfied on an explicitely-provided interval.
-/

namespace has_deriv_at

include hab

theorem lhopital_zero_right_on_Ioo
  (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hgg' : ∀ x ∈ Ioo a b, has_deriv_at g (g' x) x)
  (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
  (hfa : tendsto f (𝓝[Ioi a] a) (𝓝 0)) (hga : tendsto g (𝓝[Ioi a] a) (𝓝 0))
  (hdiv : tendsto (λ x, (f' x) / (g' x)) (𝓝[Ioi a] a) l) :
  tendsto (λ x, (f x) / (g x)) (𝓝[Ioi a] a) l :=
begin
  have sub : ∀ x ∈ Ioo a b, Ioo a x ⊆ Ioo a b := λ x hx, Ioo_subset_Ioo (le_refl a) (le_of_lt hx.2),
  have hg : ∀ x ∈ (Ioo a b), g x ≠ 0,
  { intros x hx h,
    have : tendsto g (𝓝[Iio x] x) (𝓝 0),
    { rw [← h, ← nhds_within_Ioo_eq_nhds_within_Iio hx.1],
      exact ((hgg' x hx).continuous_at.continuous_within_at.mono $ sub x hx).tendsto },
    obtain ⟨y, hyx, hy⟩ : ∃ c ∈ Ioo a x, g' c = 0,
      from exists_has_deriv_at_eq_zero' hx.1 hga this (λ y hy, hgg' y $ sub x hx hy),
    exact hg' y (sub x hx hyx) hy },
  have : ∀ x ∈ Ioo a b, ∃ c ∈ Ioo a x, (f x) * (g' c) = (g x) * (f' c),
  { intros x hx,
    rw [← sub_zero (f x), ← sub_zero (g x)],
    exact exists_ratio_has_deriv_at_eq_ratio_slope' g g' hx.1 f f'
      (λ y hy, hgg' y $ sub x hx hy) (λ y hy, hff' y $ sub x hx hy) hga hfa
      (tendsto_nhds_within_of_tendsto_nhds (hgg' x hx).continuous_at.tendsto)
      (tendsto_nhds_within_of_tendsto_nhds (hff' x hx).continuous_at.tendsto) },
  choose! c hc using this,
  have : ∀ x ∈ Ioo a b, ((λ x', (f' x') / (g' x')) ∘ c) x = f x / g x,
  { intros x hx,
    rcases hc x hx with ⟨h₁, h₂⟩,
    field_simp [hg x hx, hg' (c x) ((sub x hx) h₁)],
    simp only [h₂],
    rwa mul_comm },
  have cmp : ∀ x ∈ Ioo a b, a < c x ∧ c x < x,
    from λ x hx, (hc x hx).1,
  rw ← nhds_within_Ioo_eq_nhds_within_Ioi hab,
  apply tendsto_nhds_within_congr this,
  simp only,
  apply hdiv.comp,
  refine tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_nhds_within_of_tendsto_nhds tendsto_id) _ _) _,
  all_goals
  { apply eventually_nhds_with_of_forall,
    intros x hx,
    have := cmp x hx,
    try {simp},
    linarith [this] }
end

theorem lhopital_zero_right_on_Ico
  (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hgg' : ∀ x ∈ Ioo a b, has_deriv_at g (g' x) x)
  (hcf : continuous_on f (Ico a b)) (hcg : continuous_on g (Ico a b))
  (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
  (hfa : f a = 0) (hga : g a = 0)
  (hdiv : tendsto (λ x, (f' x) / (g' x)) (nhds_within a (Ioi a)) l) :
  tendsto (λ x, (f x) / (g x)) (nhds_within a (Ioi a)) l :=
begin
  refine lhopital_zero_right_on_Ioo hab hff' hgg' hg' _ _ hdiv,
  { rw [← hfa, ← nhds_within_Ioo_eq_nhds_within_Ioi hab],
    exact ((hcf a $ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto },
  { rw [← hga, ← nhds_within_Ioo_eq_nhds_within_Ioi hab],
    exact ((hcg a $ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto },
end

theorem lhopital_zero_left_on_Ioo
  (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hgg' : ∀ x ∈ Ioo a b, has_deriv_at g (g' x) x)
  (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
  (hfb : tendsto f (nhds_within b (Iio b)) (𝓝 0)) (hgb : tendsto g (nhds_within b (Iio b)) (𝓝 0))
  (hdiv : tendsto (λ x, (f' x) / (g' x)) (nhds_within b (Iio b)) l) :
  tendsto (λ x, (f x) / (g x)) (nhds_within b (Iio b)) l :=
begin
  -- Here, we essentially compose by `has_neg.neg`. The following is mostly technical details.
  have hdnf : ∀ x ∈ -Ioo a b, has_deriv_at (f ∘ has_neg.neg) (f' (-x) * (-1)) x,
    from λ x hx, comp x (hff' (-x) hx) (has_deriv_at_neg x),
  have hdng : ∀ x ∈ -Ioo a b, has_deriv_at (g ∘ has_neg.neg) (g' (-x) * (-1)) x,
    from λ x hx, comp x (hgg' (-x) hx) (has_deriv_at_neg x),
  rw preimage_neg_Ioo at hdnf,
  rw preimage_neg_Ioo at hdng,
  have := lhopital_zero_right_on_Ioo (neg_lt_neg hab) hdnf hdng
    (by { intros x hx h,
          apply hg' _ (by {rw ← preimage_neg_Ioo at hx, exact hx}),
          rwa [mul_comm, ← neg_eq_neg_one_mul, neg_eq_zero] at h })
    (hfb.comp tendsto_neg_nhds_within_Ioi_neg)
    (hgb.comp tendsto_neg_nhds_within_Ioi_neg)
    (by { simp only [neg_div_neg_eq, mul_one, mul_neg_eq_neg_mul_symm],
          exact (tendsto_congr $ λ x, rfl).mp (hdiv.comp tendsto_neg_nhds_within_Ioi_neg) }),
  have := this.comp tendsto_neg_nhds_within_Iio,
  unfold function.comp at this,
  simpa only [neg_neg]
end

theorem lhopital_zero_left_on_Ioc
  (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hgg' : ∀ x ∈ Ioo a b, has_deriv_at g (g' x) x)
  (hcf : continuous_on f (Ioc a b)) (hcg : continuous_on g (Ioc a b))
  (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
  (hfb : f b = 0) (hgb : g b = 0)
  (hdiv : tendsto (λ x, (f' x) / (g' x)) (nhds_within b (Iio b)) l) :
  tendsto (λ x, (f x) / (g x)) (nhds_within b (Iio b)) l :=
begin
  refine lhopital_zero_left_on_Ioo hab hff' hgg' hg' _ _ hdiv,
  { rw [← hfb, ← nhds_within_Ioo_eq_nhds_within_Iio hab],
    exact ((hcf b $ right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto },
  { rw [← hgb, ← nhds_within_Ioo_eq_nhds_within_Iio hab],
    exact ((hcg b $ right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto },
end

omit hab

theorem lhopital_zero_at_top_on_Ioi
  (hff' : ∀ x ∈ Ioi a, has_deriv_at f (f' x) x) (hgg' : ∀ x ∈ Ioi a, has_deriv_at g (g' x) x)
  (hg' : ∀ x ∈ Ioi a, g' x ≠ 0)
  (hftop : tendsto f at_top (𝓝 0)) (hgtop : tendsto g at_top (𝓝 0))
  (hdiv : tendsto (λ x, (f' x) / (g' x)) at_top l) :
  tendsto (λ x, (f x) / (g x)) at_top l :=
begin
  obtain ⟨ a', haa', ha'⟩ : ∃ a', a < a' ∧ 0 < a' :=
    ⟨1 + max a 0, ⟨lt_of_le_of_lt (le_max_left a 0) (lt_one_add _),
                   lt_of_le_of_lt (le_max_right a 0) (lt_one_add _)⟩⟩,
  have fact1 : ∀ (x:ℝ), x ∈ Ioo 0 a'⁻¹ → x ≠ 0 := λ _ hx, (ne_of_lt hx.1).symm,
  have fact2 : ∀ x ∈ Ioo 0 a'⁻¹, a < x⁻¹,
    from λ _ hx, lt_trans haa' ((lt_inv ha' hx.1).mpr hx.2),
  have hdnf : ∀ x ∈ Ioo 0 a'⁻¹, has_deriv_at (f ∘ has_inv.inv) (f' (x⁻¹) * (-(x^2)⁻¹)) x,
    from λ x hx, comp x (hff' (x⁻¹) $ fact2 x hx) (has_deriv_at_inv $ fact1 x hx),
  have hdng : ∀ x ∈ Ioo 0 a'⁻¹, has_deriv_at (g ∘ has_inv.inv) (g' (x⁻¹) * (-(x^2)⁻¹)) x,
    from λ x hx, comp x (hgg' (x⁻¹) $ fact2 x hx) (has_deriv_at_inv $ fact1 x hx),
  have := lhopital_zero_right_on_Ioo (inv_pos.mpr ha') hdnf hdng
    (by { intros x hx,
          refine mul_ne_zero _ (neg_ne_zero.mpr $ inv_ne_zero $ pow_ne_zero _ $ fact1 x hx),
          exact hg' _ (fact2 x hx) })
    (hftop.comp tendsto_inv_zero_at_top)
    (hgtop.comp tendsto_inv_zero_at_top)
    (by { refine (tendsto_congr' _).mp (hdiv.comp tendsto_inv_zero_at_top),
          rw eventually_eq_iff_exists_mem,
          use [Ioi 0, self_mem_nhds_within],
          intros x hx,
          unfold function.comp,
          erw mul_div_mul_right,
          refine neg_ne_zero.mpr (inv_ne_zero $ pow_ne_zero _ $ ne_of_gt hx) }),
  have := this.comp tendsto_inv_at_top_zero',
  unfold function.comp at this,
  simpa only [inv_inv'],
end

theorem lhopital_zero_at_bot_on_Iio
  (hff' : ∀ x ∈ Iio a, has_deriv_at f (f' x) x) (hgg' : ∀ x ∈ Iio a, has_deriv_at g (g' x) x)
  (hg' : ∀ x ∈ Iio a, g' x ≠ 0)
  (hfbot : tendsto f at_bot (𝓝 0)) (hgbot : tendsto g at_bot (𝓝 0))
  (hdiv : tendsto (λ x, (f' x) / (g' x)) at_bot l) :
  tendsto (λ x, (f x) / (g x)) at_bot l :=
begin
  -- Here, we essentially compose by `has_neg.neg`. The following is mostly technical details.
  have hdnf : ∀ x ∈ -Iio a, has_deriv_at (f ∘ has_neg.neg) (f' (-x) * (-1)) x,
    from λ x hx, comp x (hff' (-x) hx) (has_deriv_at_neg x),
  have hdng : ∀ x ∈ -Iio a, has_deriv_at (g ∘ has_neg.neg) (g' (-x) * (-1)) x,
    from λ x hx, comp x (hgg' (-x) hx) (has_deriv_at_neg x),
  rw preimage_neg_Iio at hdnf,
  rw preimage_neg_Iio at hdng,
  have := lhopital_zero_at_top_on_Ioi hdnf hdng
    (by { intros x hx h,
          apply hg' _ (by {rw ← preimage_neg_Iio at hx, exact hx}),
          rwa [mul_comm, ← neg_eq_neg_one_mul, neg_eq_zero] at h })
    (hfbot.comp tendsto_neg_at_top_at_bot)
    (hgbot.comp tendsto_neg_at_top_at_bot)
    (by { simp only [mul_one, mul_neg_eq_neg_mul_symm, neg_div_neg_eq],
          exact (tendsto_congr $ λ x, rfl).mp (hdiv.comp tendsto_neg_at_top_at_bot) }),
  have := this.comp tendsto_neg_at_bot_at_top,
  unfold function.comp at this,
  simpa only [neg_neg],
end

end has_deriv_at

namespace deriv

include hab

theorem lhopital_zero_right_on_Ioo
  (hdf : differentiable_on ℝ f (Ioo a b)) (hg' : ∀ x ∈ Ioo a b, deriv g x ≠ 0)
  (hfa : tendsto f (𝓝[Ioi a] a) (𝓝 0)) (hga : tendsto g (𝓝[Ioi a] a) (𝓝 0))
  (hdiv : tendsto (λ x, ((deriv f) x) / ((deriv g) x)) (𝓝[Ioi a] a) l) :
  tendsto (λ x, (f x) / (g x)) (𝓝[Ioi a] a) l :=
begin
  have hdf : ∀ x ∈ Ioo a b, differentiable_at ℝ f x,
    from λ x hx, (hdf x hx).differentiable_at (Ioo_mem_nhds hx.1 hx.2),
  have hdg : ∀ x ∈ Ioo a b, differentiable_at ℝ g x,
    from λ x hx, classical.by_contradiction (λ h, hg' x hx (deriv_zero_of_not_differentiable_at h)),
  exact has_deriv_at.lhopital_zero_right_on_Ioo hab (λ x hx, (hdf x hx).has_deriv_at)
    (λ x hx, (hdg x hx).has_deriv_at) hg' hfa hga hdiv
end

theorem lhopital_zero_right_on_Ico
  (hdf : differentiable_on ℝ f (Ioo a b))
  (hcf : continuous_on f (Ico a b)) (hcg : continuous_on g (Ico a b))
  (hg' : ∀ x ∈ (Ioo a b), (deriv g) x ≠ 0)
  (hfa : f a = 0) (hga : g a = 0)
  (hdiv : tendsto (λ x, ((deriv f) x) / ((deriv g) x)) (nhds_within a (Ioi a)) l) :
  tendsto (λ x, (f x) / (g x)) (nhds_within a (Ioi a)) l :=
begin
  refine lhopital_zero_right_on_Ioo hab hdf hg' _ _ hdiv,
  { rw [← hfa, ← nhds_within_Ioo_eq_nhds_within_Ioi hab],
    exact ((hcf a $ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto },
  { rw [← hga, ← nhds_within_Ioo_eq_nhds_within_Ioi hab],
    exact ((hcg a $ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto },
end

theorem lhopital_zero_left_on_Ioo
  (hdf : differentiable_on ℝ f (Ioo a b))
  (hg' : ∀ x ∈ (Ioo a b), (deriv g) x ≠ 0)
  (hfb : tendsto f (nhds_within b (Iio b)) (𝓝 0)) (hgb : tendsto g (nhds_within b (Iio b)) (𝓝 0))
  (hdiv : tendsto (λ x, ((deriv f) x) / ((deriv g) x)) (nhds_within b (Iio b)) l) :
  tendsto (λ x, (f x) / (g x)) (nhds_within b (Iio b)) l :=
begin
  have hdf : ∀ x ∈ Ioo a b, differentiable_at ℝ f x,
    from λ x hx, (hdf x hx).differentiable_at (Ioo_mem_nhds hx.1 hx.2),
  have hdg : ∀ x ∈ Ioo a b, differentiable_at ℝ g x,
    from λ x hx, classical.by_contradiction (λ h, hg' x hx (deriv_zero_of_not_differentiable_at h)),
  exact has_deriv_at.lhopital_zero_left_on_Ioo hab (λ x hx, (hdf x hx).has_deriv_at)
    (λ x hx, (hdg x hx).has_deriv_at) hg' hfb hgb hdiv
end

omit hab

theorem lhopital_zero_at_top_on_Ioi
  (hdf : differentiable_on ℝ f (Ioi a))
  (hg' : ∀ x ∈ (Ioi a), (deriv g) x ≠ 0)
  (hftop : tendsto f at_top (𝓝 0)) (hgtop : tendsto g at_top (𝓝 0))
  (hdiv : tendsto (λ x, ((deriv f) x) / ((deriv g) x)) at_top l) :
  tendsto (λ x, (f x) / (g x)) at_top l :=
begin
  have hdf : ∀ x ∈ Ioi a, differentiable_at ℝ f x,
    from λ x hx, (hdf x hx).differentiable_at (Ioi_mem_nhds hx),
  have hdg : ∀ x ∈ Ioi a, differentiable_at ℝ g x,
    from λ x hx, classical.by_contradiction (λ h, hg' x hx (deriv_zero_of_not_differentiable_at h)),
  exact has_deriv_at.lhopital_zero_at_top_on_Ioi (λ x hx, (hdf x hx).has_deriv_at)
    (λ x hx, (hdg x hx).has_deriv_at) hg' hftop hgtop hdiv,
end

theorem lhopital_zero_at_bot_on_Iio
  (hdf : differentiable_on ℝ f (Iio a))
  (hg' : ∀ x ∈ (Iio a), (deriv g) x ≠ 0)
  (hfbot : tendsto f at_bot (𝓝 0)) (hgbot : tendsto g at_bot (𝓝 0))
  (hdiv : tendsto (λ x, ((deriv f) x) / ((deriv g) x)) at_bot l) :
  tendsto (λ x, (f x) / (g x)) at_bot l :=
begin
  have hdf : ∀ x ∈ Iio a, differentiable_at ℝ f x,
    from λ x hx, (hdf x hx).differentiable_at (Iio_mem_nhds hx),
  have hdg : ∀ x ∈ Iio a, differentiable_at ℝ g x,
    from λ x hx, classical.by_contradiction (λ h, hg' x hx (deriv_zero_of_not_differentiable_at h)),
  exact has_deriv_at.lhopital_zero_at_bot_on_Iio (λ x hx, (hdf x hx).has_deriv_at)
    (λ x hx, (hdg x hx).has_deriv_at) hg' hfbot hgbot hdiv,
end

end deriv

/-!
## Generic versions

The following statements no longer any explicit interval, as they only require
conditions holding eventually.
-/

namespace has_deriv_at

/-- L'Hôpital's rule for approaching a real from the right, `has_deriv_at` version -/
theorem lhopital_zero_nhds_right
  (hff' : ∀ᶠ x in 𝓝[Ioi a] a, has_deriv_at f (f' x) x)
  (hgg' : ∀ᶠ x in 𝓝[Ioi a] a, has_deriv_at g (g' x) x)
  (hg' : ∀ᶠ x in 𝓝[Ioi a] a, g' x ≠ 0)
  (hfa : tendsto f (𝓝[Ioi a] a) (𝓝 0)) (hga : tendsto g (𝓝[Ioi a] a) (𝓝 0))
  (hdiv : tendsto (λ x, (f' x) / (g' x)) (𝓝[Ioi a] a) l) :
  tendsto (λ x, (f x) / (g x)) (𝓝[Ioi a] a) l :=
begin
  rw eventually_iff_exists_mem at *,
  rcases hff' with ⟨s₁, hs₁, hff'⟩,
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩,
  rcases hg' with ⟨s₃, hs₃, hg'⟩,
  let s := s₁ ∩ s₂ ∩ s₃,
  have hs : s ∈ 𝓝[Ioi a] a := inter_mem_sets (inter_mem_sets hs₁ hs₂) hs₃,
  rw mem_nhds_within_Ioi_iff_exists_Ioo_subset at hs,
  rcases hs with ⟨u, hau, hu⟩,
  refine lhopital_zero_right_on_Ioo hau _ _ _ hfa hga hdiv;
  intros x hx;
  apply_assumption;
  exact (hu hx).1.1 <|> exact (hu hx).1.2 <|> exact (hu hx).2
end

/-- L'Hôpital's rule for approaching a real from the left, `has_deriv_at` version -/
theorem lhopital_zero_nhds_left
  (hff' : ∀ᶠ x in 𝓝[Iio a] a, has_deriv_at f (f' x) x)
  (hgg' : ∀ᶠ x in 𝓝[Iio a] a, has_deriv_at g (g' x) x)
  (hg' : ∀ᶠ x in 𝓝[Iio a] a, g' x ≠ 0)
  (hfa : tendsto f (𝓝[Iio a] a) (𝓝 0)) (hga : tendsto g (𝓝[Iio a] a) (𝓝 0))
  (hdiv : tendsto (λ x, (f' x) / (g' x)) (𝓝[Iio a] a) l) :
  tendsto (λ x, (f x) / (g x)) (𝓝[Iio a] a) l :=
begin
  rw eventually_iff_exists_mem at *,
  rcases hff' with ⟨s₁, hs₁, hff'⟩,
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩,
  rcases hg' with ⟨s₃, hs₃, hg'⟩,
  let s := s₁ ∩ s₂ ∩ s₃,
  have hs : s ∈ 𝓝[Iio a] a := inter_mem_sets (inter_mem_sets hs₁ hs₂) hs₃,
  rw mem_nhds_within_Iio_iff_exists_Ioo_subset at hs,
  rcases hs with ⟨l, hal, hl⟩,
  refine lhopital_zero_left_on_Ioo hal _ _ _ hfa hga hdiv;
  intros x hx;
  apply_assumption;
  exact (hl hx).1.1 <|> exact (hl hx).1.2 <|> exact (hl hx).2
end

/-- L'Hôpital's rule for approaching a real, `has_deriv_at` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds'
  (hff' : ∀ᶠ x in 𝓝[univ \ {a}] a, has_deriv_at f (f' x) x)
  (hgg' : ∀ᶠ x in 𝓝[univ \ {a}] a, has_deriv_at g (g' x) x)
  (hg' : ∀ᶠ x in 𝓝[univ \ {a}] a, g' x ≠ 0)
  (hfa : tendsto f (𝓝[univ \ {a}] a) (𝓝 0)) (hga : tendsto g (𝓝[univ \ {a}] a) (𝓝 0))
  (hdiv : tendsto (λ x, (f' x) / (g' x)) (𝓝[univ \ {a}] a) l) :
  tendsto (λ x, (f x) / (g x)) (𝓝[univ \ {a}] a) l :=
begin
  have : univ \ {a} = Iio a ∪ Ioi a,
  { ext, rw [mem_diff_singleton, eq_true_intro $ mem_univ x, true_and, ne_iff_lt_or_gt], refl },
  simp only [this, nhds_within_union, tendsto_sup, eventually_sup] at *,
  exact ⟨lhopital_zero_nhds_left hff'.1 hgg'.1 hg'.1 hfa.1 hga.1 hdiv.1,
          lhopital_zero_nhds_right hff'.2 hgg'.2 hg'.2 hfa.2 hga.2 hdiv.2⟩
end

/-- **L'Hôpital's rule** for approaching a real, `has_deriv_at` version -/
theorem lhopital_zero_nhds
  (hff' : ∀ᶠ x in 𝓝 a, has_deriv_at f (f' x) x)
  (hgg' : ∀ᶠ x in 𝓝 a, has_deriv_at g (g' x) x)
  (hg' : ∀ᶠ x in 𝓝 a, g' x ≠ 0)
  (hfa : tendsto f (𝓝 a) (𝓝 0)) (hga : tendsto g (𝓝 a) (𝓝 0))
  (hdiv : tendsto (λ x, f' x / g' x) (𝓝 a) l) :
  tendsto (λ x, f x / g x) (𝓝[univ \ {a}] a) l :=
begin
  apply @lhopital_zero_nhds' _ _ _ f' _ g';
  apply eventually_nhds_within_of_eventually_nhds <|> apply tendsto_nhds_within_of_tendsto_nhds;
  assumption
end

/-- L'Hôpital's rule for approaching +∞, `has_deriv_at` version -/
theorem lhopital_zero_at_top
  (hff' : ∀ᶠ x in at_top, has_deriv_at f (f' x) x)
  (hgg' : ∀ᶠ x in at_top, has_deriv_at g (g' x) x)
  (hg' : ∀ᶠ x in at_top, g' x ≠ 0)
  (hftop : tendsto f at_top (𝓝 0)) (hgtop : tendsto g at_top (𝓝 0))
  (hdiv : tendsto (λ x, (f' x) / (g' x)) at_top l) :
  tendsto (λ x, (f x) / (g x)) at_top l :=
begin
  rw eventually_iff_exists_mem at *,
  rcases hff' with ⟨s₁, hs₁, hff'⟩,
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩,
  rcases hg' with ⟨s₃, hs₃, hg'⟩,
  let s := s₁ ∩ s₂ ∩ s₃,
  have hs : s ∈ at_top := inter_mem_sets (inter_mem_sets hs₁ hs₂) hs₃,
  rw mem_at_top_sets at hs,
  rcases hs with ⟨l, hl⟩,
  have hl' : Ioi l ⊆ s := λ x hx, hl x (le_of_lt hx),
  refine lhopital_zero_at_top_on_Ioi _ _ (λ x hx, hg' x $ (hl' hx).2) hftop hgtop hdiv;
  intros x hx;
  apply_assumption;
  exact (hl' hx).1.1 <|> exact (hl' hx).1.2
end

/-- L'Hôpital's rule for approaching -∞, `has_deriv_at` version -/
theorem lhopital_zero_at_bot
  (hff' : ∀ᶠ x in at_bot, has_deriv_at f (f' x) x)
  (hgg' : ∀ᶠ x in at_bot, has_deriv_at g (g' x) x)
  (hg' : ∀ᶠ x in at_bot, g' x ≠ 0)
  (hfbot : tendsto f at_bot (𝓝 0)) (hgbot : tendsto g at_bot (𝓝 0))
  (hdiv : tendsto (λ x, (f' x) / (g' x)) at_bot l) :
  tendsto (λ x, (f x) / (g x)) at_bot l :=
begin
  rw eventually_iff_exists_mem at *,
  rcases hff' with ⟨s₁, hs₁, hff'⟩,
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩,
  rcases hg' with ⟨s₃, hs₃, hg'⟩,
  let s := s₁ ∩ s₂ ∩ s₃,
  have hs : s ∈ at_bot := inter_mem_sets (inter_mem_sets hs₁ hs₂) hs₃,
  rw mem_at_bot_sets at hs,
  rcases hs with ⟨l, hl⟩,
  have hl' : Iio l ⊆ s := λ x hx, hl x (le_of_lt hx),
  refine lhopital_zero_at_bot_on_Iio _ _ (λ x hx, hg' x $ (hl' hx).2) hfbot hgbot hdiv;
  intros x hx;
  apply_assumption;
  exact (hl' hx).1.1 <|> exact (hl' hx).1.2
end

end has_deriv_at

namespace deriv

/-- **L'Hôpital's rule** for approaching a real from the right, `deriv` version -/
theorem lhopital_zero_nhds_right
  (hdf : ∀ᶠ x in 𝓝[Ioi a] a, differentiable_at ℝ f x)
  (hg' : ∀ᶠ x in 𝓝[Ioi a] a, deriv g x ≠ 0)
  (hfa : tendsto f (𝓝[Ioi a] a) (𝓝 0)) (hga : tendsto g (𝓝[Ioi a] a) (𝓝 0))
  (hdiv : tendsto (λ x, ((deriv f) x) / ((deriv g) x)) (𝓝[Ioi a] a) l) :
  tendsto (λ x, (f x) / (g x)) (𝓝[Ioi a] a) l :=
begin
  have hdg : ∀ᶠ x in 𝓝[Ioi a] a, differentiable_at ℝ g x,
    from hg'.mp (eventually_of_forall $
      λ _ hg', classical.by_contradiction (λ h, hg' (deriv_zero_of_not_differentiable_at h))),
  have hdf' : ∀ᶠ x in 𝓝[Ioi a] a, has_deriv_at f (deriv f x) x,
    from hdf.mp (eventually_of_forall $ λ _, differentiable_at.has_deriv_at),
  have hdg' : ∀ᶠ x in 𝓝[Ioi a] a, has_deriv_at g (deriv g x) x,
    from hdg.mp (eventually_of_forall $ λ _, differentiable_at.has_deriv_at),
  exact has_deriv_at.lhopital_zero_nhds_right hdf' hdg' hg' hfa hga hdiv
end

/-- **L'Hôpital's rule** for approaching a real from the left, `deriv` version -/
theorem lhopital_zero_nhds_left
  (hdf : ∀ᶠ x in 𝓝[Iio a] a, differentiable_at ℝ f x)
  (hg' : ∀ᶠ x in 𝓝[Iio a] a, deriv g x ≠ 0)
  (hfa : tendsto f (𝓝[Iio a] a) (𝓝 0)) (hga : tendsto g (𝓝[Iio a] a) (𝓝 0))
  (hdiv : tendsto (λ x, ((deriv f) x) / ((deriv g) x)) (𝓝[Iio a] a) l) :
  tendsto (λ x, (f x) / (g x)) (𝓝[Iio a] a) l :=
begin
  have hdg : ∀ᶠ x in 𝓝[Iio a] a, differentiable_at ℝ g x,
    from hg'.mp (eventually_of_forall $
      λ _ hg', classical.by_contradiction (λ h, hg' (deriv_zero_of_not_differentiable_at h))),
  have hdf' : ∀ᶠ x in 𝓝[Iio a] a, has_deriv_at f (deriv f x) x,
    from hdf.mp (eventually_of_forall $ λ _, differentiable_at.has_deriv_at),
  have hdg' : ∀ᶠ x in 𝓝[Iio a] a, has_deriv_at g (deriv g x) x,
    from hdg.mp (eventually_of_forall $ λ _, differentiable_at.has_deriv_at),
  exact has_deriv_at.lhopital_zero_nhds_left hdf' hdg' hg' hfa hga hdiv
end

/-- **L'Hôpital's rule** for approaching a real, `deriv` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds'
  (hdf : ∀ᶠ x in 𝓝[univ \ {a}] a, differentiable_at ℝ f x)
  (hg' : ∀ᶠ x in 𝓝[univ \ {a}] a, deriv g x ≠ 0)
  (hfa : tendsto f (𝓝[univ \ {a}] a) (𝓝 0)) (hga : tendsto g (𝓝[univ \ {a}] a) (𝓝 0))
  (hdiv : tendsto (λ x, ((deriv f) x) / ((deriv g) x)) (𝓝[univ \ {a}] a) l) :
  tendsto (λ x, (f x) / (g x)) (𝓝[univ \ {a}] a) l :=
begin
  have : univ \ {a} = Iio a ∪ Ioi a,
  { ext, rw [mem_diff_singleton, eq_true_intro $ mem_univ x, true_and, ne_iff_lt_or_gt], refl },
  simp only [this, nhds_within_union, tendsto_sup, eventually_sup] at *,
  exact ⟨lhopital_zero_nhds_left hdf.1 hg'.1 hfa.1 hga.1 hdiv.1,
          lhopital_zero_nhds_right hdf.2 hg'.2 hfa.2 hga.2 hdiv.2⟩,
end

/-- **L'Hôpital's rule** for approaching a real, `deriv` version -/
theorem lhopital_zero_nhds
  (hdf : ∀ᶠ x in 𝓝 a, differentiable_at ℝ f x)
  (hg' : ∀ᶠ x in 𝓝 a, deriv g x ≠ 0)
  (hfa : tendsto f (𝓝 a) (𝓝 0)) (hga : tendsto g (𝓝 a) (𝓝 0))
  (hdiv : tendsto (λ x, ((deriv f) x) / ((deriv g) x)) (𝓝 a) l) :
  tendsto (λ x, (f x) / (g x)) (𝓝[univ \ {a}] a) l :=
begin
  apply lhopital_zero_nhds';
  apply eventually_nhds_within_of_eventually_nhds <|> apply tendsto_nhds_within_of_tendsto_nhds;
  assumption
end

/-- **L'Hôpital's rule** for approaching +∞, `deriv` version -/
theorem lhopital_zero_at_top
  (hdf : ∀ᶠ (x : ℝ) in at_top, differentiable_at ℝ f x)
  (hg' : ∀ᶠ (x : ℝ) in at_top, deriv g x ≠ 0)
  (hftop : tendsto f at_top (𝓝 0)) (hgtop : tendsto g at_top (𝓝 0))
  (hdiv : tendsto (λ x, ((deriv f) x) / ((deriv g) x)) at_top l) :
  tendsto (λ x, (f x) / (g x)) at_top l :=
begin
  have hdg : ∀ᶠ x in at_top, differentiable_at ℝ g x,
    from hg'.mp (eventually_of_forall $
      λ _ hg', classical.by_contradiction (λ h, hg' (deriv_zero_of_not_differentiable_at h))),
  have hdf' : ∀ᶠ x in at_top, has_deriv_at f (deriv f x) x,
    from hdf.mp (eventually_of_forall $ λ _, differentiable_at.has_deriv_at),
  have hdg' : ∀ᶠ x in at_top, has_deriv_at g (deriv g x) x,
    from hdg.mp (eventually_of_forall $ λ _, differentiable_at.has_deriv_at),
  exact has_deriv_at.lhopital_zero_at_top hdf' hdg' hg' hftop hgtop hdiv
end

/-- **L'Hôpital's rule** for approaching -∞, `deriv` version -/
theorem lhopital_zero_at_bot
  (hdf : ∀ᶠ (x : ℝ) in at_bot, differentiable_at ℝ f x)
  (hg' : ∀ᶠ (x : ℝ) in at_bot, deriv g x ≠ 0)
  (hfbot : tendsto f at_bot (𝓝 0)) (hgbot : tendsto g at_bot (𝓝 0))
  (hdiv : tendsto (λ x, ((deriv f) x) / ((deriv g) x)) at_bot l) :
  tendsto (λ x, (f x) / (g x)) at_bot l :=
begin
  have hdg : ∀ᶠ x in at_bot, differentiable_at ℝ g x,
    from hg'.mp (eventually_of_forall $
      λ _ hg', classical.by_contradiction (λ h, hg' (deriv_zero_of_not_differentiable_at h))),
  have hdf' : ∀ᶠ x in at_bot, has_deriv_at f (deriv f x) x,
    from hdf.mp (eventually_of_forall $ λ _, differentiable_at.has_deriv_at),
  have hdg' : ∀ᶠ x in at_bot, has_deriv_at g (deriv g x) x,
    from hdg.mp (eventually_of_forall $ λ _, differentiable_at.has_deriv_at),
  exact has_deriv_at.lhopital_zero_at_bot hdf' hdg' hg' hfbot hgbot hdiv
end

end deriv
