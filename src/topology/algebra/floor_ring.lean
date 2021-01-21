/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

Basic topological facts (limits and continuity) about `floor`,
`ceil` and `fract` in a `floor_ring`.
-/
import topology.algebra.ordered

open set function filter
open_locale topological_space

variables {α : Type*} [linear_ordered_ring α] [floor_ring α]

lemma tendsto_floor_at_top : tendsto (floor : α → ℤ) at_top at_top :=
begin
  refine monotone.tendsto_at_top_at_top (λ a b hab, floor_mono hab) (λ b, _),
  use (b : α) + ((1 : ℤ) : α),
  rw [floor_add_int, floor_coe],
  exact (lt_add_one _).le
end

lemma tendsto_floor_at_bot : tendsto (floor : α → ℤ) at_bot at_bot :=
begin
  refine monotone.tendsto_at_bot_at_bot (λ a b hab, floor_mono hab) (λ b, ⟨b, _⟩),
  rw floor_coe
end

lemma tendsto_ceil_at_top : tendsto (ceil : α → ℤ) at_top at_top :=
tendsto_neg_at_bot_at_top.comp (tendsto_floor_at_bot.comp tendsto_neg_at_top_at_bot)

lemma tendsto_ceil_at_bot : tendsto (ceil : α → ℤ) at_bot at_bot :=
tendsto_neg_at_top_at_bot.comp (tendsto_floor_at_top.comp tendsto_neg_at_bot_at_top)

variables [topological_space α]

lemma continuous_on_floor (n : ℤ) : continuous_on (λ x, floor x : α → α) (Ico n (n+1) : set α) :=
(continuous_on_congr $ floor_eq_on_Ico' n).mpr continuous_on_const

lemma continuous_on_ceil (n : ℤ) : continuous_on (λ x, ceil x : α → α) (Ioc (n-1) n : set α) :=
(continuous_on_congr $ ceil_eq_on_Ioc' n).mpr continuous_on_const

lemma tendsto_floor_right' [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, floor x : α → α) (𝓝[Ici n] n) (𝓝 n) :=
begin
  rw ← nhds_within_Ico_eq_nhds_within_Ici (lt_add_one (n : α)),
  convert ← (continuous_on_floor _ _ (left_mem_Ico.mpr $ lt_add_one (_ : α))).tendsto,
  rw floor_eq_iff,
  exact ⟨le_refl _, lt_add_one _⟩
end

lemma tendsto_ceil_left' [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, ceil x : α → α) (𝓝[Iic n] n) (𝓝 n) :=
begin
  rw ← nhds_within_Ioc_eq_nhds_within_Iic (sub_one_lt (n : α)),
  convert ← (continuous_on_ceil _ _ (right_mem_Ioc.mpr $ sub_one_lt (_ : α))).tendsto,
  rw ceil_eq_iff,
  exact ⟨sub_one_lt _, le_refl _⟩
end

lemma tendsto_floor_right [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, floor x : α → α) (𝓝[Ici n] n) (𝓝[Ici n] n) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_floor_right' _)
begin
  refine (eventually_nhds_with_of_forall $ λ x (hx : (n : α) ≤ x), _),
  change _ ≤ _,
  norm_cast,
  convert ← floor_mono hx,
  rw floor_eq_iff,
  exact ⟨le_refl _, lt_add_one _⟩
end

lemma tendsto_ceil_left [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, ceil x : α → α) (𝓝[Iic n] n) (𝓝[Iic n] n) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_ceil_left' _)
begin
  refine (eventually_nhds_with_of_forall $ λ x (hx : x ≤ (n : α)), _),
  change _ ≤ _,
  norm_cast,
  convert ← ceil_mono hx,
  rw ceil_eq_iff,
  exact ⟨sub_one_lt _, le_refl _⟩
end

lemma tendsto_floor_left [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, floor x : α → α) (𝓝[Iio n] n) (𝓝[Iic (n-1)] (n-1)) :=
begin
  rw ← nhds_within_Ico_eq_nhds_within_Iio (sub_one_lt (n : α)),
  convert (tendsto_nhds_within_congr $ (λ x hx, (floor_eq_on_Ico' (n-1) x hx).symm))
    (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
      (eventually_of_forall (λ _, mem_Iic.mpr $ le_refl _)));
  norm_cast <|> apply_instance,
  ring
end

lemma tendsto_ceil_right [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, ceil x : α → α) (𝓝[Ioi n] n) (𝓝[Ici (n+1)] (n+1)) :=
begin
  rw ← nhds_within_Ioc_eq_nhds_within_Ioi (lt_add_one (n : α)),
  convert (tendsto_nhds_within_congr $ (λ x hx, (ceil_eq_on_Ioc' (n+1) x hx).symm))
    (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
      (eventually_of_forall (λ _, mem_Ici.mpr $ le_refl _)));
  norm_cast <|> apply_instance,
  ring
end

lemma tendsto_floor_left' [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, floor x : α → α) (𝓝[Iio n] n) (𝓝 (n-1)) :=
begin
  rw ← nhds_within_univ,
  exact tendsto_nhds_within_mono_right (subset_univ _) (tendsto_floor_left n),
end

lemma tendsto_ceil_right' [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, ceil x : α → α) (𝓝[Ioi n] n) (𝓝 (n+1)) :=
begin
  rw ← nhds_within_univ,
  exact tendsto_nhds_within_mono_right (subset_univ _) (tendsto_ceil_right n),
end

lemma continuous_on_fract [topological_add_group α] (n : ℤ) :
  continuous_on (fract : α → α) (Ico n (n+1) : set α) :=
continuous_on_id.sub (continuous_on_floor n)

lemma tendsto_fract_left' [order_closed_topology α] [topological_add_group α]
  (n : ℤ) : tendsto (fract : α → α) (𝓝[Iio n] n) (𝓝 1) :=
begin
  convert (tendsto_nhds_within_of_tendsto_nhds tendsto_id).sub (tendsto_floor_left' n);
  [{norm_cast, ring}, apply_instance, apply_instance]
end

lemma tendsto_fract_left [order_closed_topology α] [topological_add_group α]
  (n : ℤ) : tendsto (fract : α → α) (𝓝[Iio n] n) (𝓝[Iio 1] 1) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
  (tendsto_fract_left' _) (eventually_of_forall fract_lt_one)

lemma tendsto_fract_right' [order_closed_topology α] [topological_add_group α]
  (n : ℤ) : tendsto (fract : α → α) (𝓝[Ici n] n) (𝓝 0) :=
begin
  convert (tendsto_nhds_within_of_tendsto_nhds tendsto_id).sub (tendsto_floor_right' n);
  [exact (sub_self _).symm, apply_instance, apply_instance]
end

lemma tendsto_fract_right [order_closed_topology α] [topological_add_group α]
  (n : ℤ) : tendsto (fract : α → α) (𝓝[Ici n] n) (𝓝[Ici 0] 0) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
  (tendsto_fract_right' _) (eventually_of_forall fract_nonneg)

local notation `I` := (Icc 0 1 : set α)

lemma continuous_on.comp_fract' {β γ : Type*} [order_topology α]
  [topological_add_group α] [topological_space β] [topological_space γ] {f : β → α → γ}
  (h : continuous_on (uncurry f) $ (univ : set β).prod I) (hf : ∀ s, f s 0 = f s 1) :
  continuous (λ st : β × α, f st.1 $ fract st.2) :=
begin
  change continuous ((uncurry f) ∘ (prod.map id (fract))),
  rw continuous_iff_continuous_at,
  rintro ⟨s, t⟩,
  by_cases ht : t = floor t,
  { rw ht,
    rw ← continuous_within_at_univ,
    have : (univ : set (β × α)) ⊆ (set.prod univ (Iio $ floor t)) ∪ (set.prod univ (Ici $ floor t)),
    { rintros p -,
      rw ← prod_union,
      exact ⟨true.intro, lt_or_le _ _⟩ },
    refine continuous_within_at.mono _ this,
    refine continuous_within_at.union _ _,
    { simp only [continuous_within_at, fract_coe, nhds_within_prod_eq,
                  nhds_within_univ, id.def, comp_app, prod.map_mk],
      have : (uncurry f) (s, 0) = (uncurry f) (s, (1 : α)),
        by simp [uncurry, hf],
      rw this,
      refine (h _ ⟨true.intro, by exact_mod_cast right_mem_Icc.mpr zero_le_one⟩).tendsto.comp _,
      rw [nhds_within_prod_eq, nhds_within_univ],
      rw nhds_within_Icc_eq_nhds_within_Iic (@zero_lt_one α _ _),
      exact tendsto_id.prod_map
        (tendsto_nhds_within_mono_right Iio_subset_Iic_self $ tendsto_fract_left _) },
    { simp only [continuous_within_at, fract_coe, nhds_within_prod_eq,
                  nhds_within_univ, id.def, comp_app, prod.map_mk],
      refine (h _ ⟨true.intro, by exact_mod_cast left_mem_Icc.mpr zero_le_one⟩).tendsto.comp _,
      rw [nhds_within_prod_eq, nhds_within_univ, nhds_within_Icc_eq_nhds_within_Ici (@zero_lt_one α _ _)],
      exact tendsto_id.prod_map (tendsto_fract_right _) } },
  { have : t ∈ Ioo (floor t : α) ((floor t : α) + 1),
      from ⟨lt_of_le_of_ne (floor_le t) (ne.symm ht), lt_floor_add_one _⟩,
    refine (h ((prod.map _ fract) _) ⟨trivial, ⟨fract_nonneg _, (fract_lt_one _).le⟩⟩).tendsto.comp _,
    simp only [nhds_prod_eq, nhds_within_prod_eq, nhds_within_univ, id.def, prod.map_mk],
    exact continuous_at_id.tendsto.prod_map
            (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
              (((continuous_on_fract _ _ (Ioo_subset_Ico_self this)).mono
                  Ioo_subset_Ico_self).continuous_at (Ioo_mem_nhds this.1 this.2))
              (eventually_of_forall (λ x, ⟨fract_nonneg _, (fract_lt_one _).le⟩)) ) }
end

lemma continuous_on.comp_fract {β : Type*} [order_topology α]
  [topological_add_group α] [topological_space β] {f : α → β}
  (h : continuous_on f I) (hf : f 0 = f 1) : continuous (f ∘ fract) :=
begin
  let f' : unit → α → β := λ x y, f y,
  have : continuous_on (uncurry f') ((univ : set unit).prod I),
  { rintros ⟨s, t⟩ ⟨-, ht : t ∈ I⟩,
    simp only [continuous_within_at, uncurry, nhds_within_prod_eq, nhds_within_univ, f'],
    rw tendsto_prod_iff,
    intros W hW,
    specialize h t ht hW,
    rw mem_map_sets_iff at h,
    rcases h with ⟨V, hV, hVW⟩,
    rw image_subset_iff at hVW,
    use [univ, univ_mem_sets, V, hV],
    intros x y hx hy,
    exact hVW hy },
  have key : continuous (λ s, ⟨unit.star, s⟩ : α → unit × α) := by continuity,
  exact (this.comp_fract' (λ s, hf)).comp key
end
