/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import topology.maps

/-!
# Constructions of new topological spaces from old ones

This file constructs products, sums, subtypes and quotients of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, sum, disjoint union, subspace, quotient space

-/

noncomputable theory

open topological_space set filter
open_locale classical topological_space filter

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

section constructions

instance {p : α → Prop} [t : topological_space α] : topological_space (subtype p) :=
induced coe t

instance {r : α → α → Prop} [t : topological_space α] : topological_space (quot r) :=
coinduced (quot.mk r) t

instance {s : setoid α} [t : topological_space α] : topological_space (quotient s) :=
coinduced quotient.mk t

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α × β) :=
induced prod.fst t₁ ⊓ induced prod.snd t₂

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α ⊕ β) :=
coinduced sum.inl t₁ ⊔ coinduced sum.inr t₂

instance {β : α → Type v} [t₂ : Πa, topological_space (β a)] : topological_space (sigma β) :=
⨆a, coinduced (sigma.mk a) (t₂ a)

instance Pi.topological_space {β : α → Type v} [t₂ : Πa, topological_space (β a)] :
  topological_space (Πa, β a) :=
⨅a, induced (λf, f a) (t₂ a)

instance ulift.topological_space [t : topological_space α] : topological_space (ulift.{v u} α) :=
t.induced ulift.down

lemma quotient.preimage_mem_nhds [topological_space α] [s : setoid α]
  {V : set $ quotient s} {a : α} (hs : V ∈ 𝓝 (quotient.mk a)) : quotient.mk ⁻¹' V ∈ 𝓝 a :=
preimage_nhds_coinduced hs

/-- The image of a dense set under `quotient.mk` is a dense set. -/
lemma dense.quotient [setoid α] [topological_space α] {s : set α} (H : dense s) :
  dense (quotient.mk '' s) :=
(surjective_quotient_mk α).dense_range.dense_image continuous_coinduced_rng H

/-- The composition of `quotient.mk` and a function with dense range has dense range. -/
lemma dense_range.quotient [setoid α] [topological_space α] {f : β → α} (hf : dense_range f) :
  dense_range (quotient.mk ∘ f) :=
(surjective_quotient_mk α).dense_range.comp hf continuous_coinduced_rng

instance {p : α → Prop} [topological_space α] [discrete_topology α] :
  discrete_topology (subtype p) :=
⟨bot_unique $ assume s hs,
  ⟨coe '' s, is_open_discrete _, (set.preimage_image_eq _ subtype.coe_injective)⟩⟩

instance sum.discrete_topology [topological_space α] [topological_space β]
  [hα : discrete_topology α] [hβ : discrete_topology β] : discrete_topology (α ⊕ β) :=
⟨by unfold sum.topological_space; simp [hα.eq_bot, hβ.eq_bot]⟩

instance sigma.discrete_topology {β : α → Type v} [Πa, topological_space (β a)]
  [h : Πa, discrete_topology (β a)] : discrete_topology (sigma β) :=
⟨by { unfold sigma.topological_space, simp [λ a, (h a).eq_bot] }⟩

section topα

variable [topological_space α]

/-
The 𝓝 filter and the subspace topology.
-/

theorem mem_nhds_subtype (s : set α) (a : {x // x ∈ s}) (t : set {x // x ∈ s}) :
  t ∈ 𝓝 a ↔ ∃ u ∈ 𝓝 (a : α), coe ⁻¹' u ⊆ t :=
mem_nhds_induced coe a t

theorem nhds_subtype (s : set α) (a : {x // x ∈ s}) :
  𝓝 a = comap coe (𝓝 (a : α)) :=
nhds_induced coe a

end topα

end constructions


section prod
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

@[continuity] lemma continuous_fst : continuous (@prod.fst α β) :=
continuous_inf_dom_left continuous_induced_dom

lemma continuous_at_fst {p : α × β} : continuous_at prod.fst p :=
continuous_fst.continuous_at

@[continuity] lemma continuous_snd : continuous (@prod.snd α β) :=
continuous_inf_dom_right continuous_induced_dom

lemma continuous_at_snd {p : α × β} : continuous_at prod.snd p :=
continuous_snd.continuous_at

@[continuity] lemma continuous.prod_mk {f : γ → α} {g : γ → β}
  (hf : continuous f) (hg : continuous g) : continuous (λx, (f x, g x)) :=
continuous_inf_rng (continuous_induced_rng hf) (continuous_induced_rng hg)

@[continuity] lemma continuous.prod.mk (a : α) : continuous (prod.mk a : β → α × β) :=
continuous_const.prod_mk continuous_id'

lemma continuous.prod_map {f : γ → α} {g : δ → β} (hf : continuous f) (hg : continuous g) :
  continuous (λ x : γ × δ, (f x.1, g x.2)) :=
(hf.comp continuous_fst).prod_mk (hg.comp continuous_snd)

lemma filter.eventually.prod_inl_nhds {p : α → Prop} {a : α}  (h : ∀ᶠ x in 𝓝 a, p x) (b : β) :
  ∀ᶠ x in 𝓝 (a, b), p (x : α × β).1 :=
continuous_at_fst h

lemma filter.eventually.prod_inr_nhds {p : β → Prop} {b : β} (h : ∀ᶠ x in 𝓝 b, p x) (a : α) :
  ∀ᶠ x in 𝓝 (a, b), p (x : α × β).2 :=
continuous_at_snd h

lemma filter.eventually.prod_mk_nhds {pa : α → Prop} {a} (ha : ∀ᶠ x in 𝓝 a, pa x)
  {pb : β → Prop} {b} (hb : ∀ᶠ y in 𝓝 b, pb y) :
  ∀ᶠ p in 𝓝 (a, b), pa (p : α × β).1 ∧ pb p.2 :=
(ha.prod_inl_nhds b).and (hb.prod_inr_nhds a)

lemma continuous_swap : continuous (prod.swap : α × β → β × α) :=
continuous.prod_mk continuous_snd continuous_fst

lemma continuous_uncurry_left {f : α → β → γ} (a : α)
  (h : continuous (function.uncurry f)) : continuous (f a) :=
show continuous (function.uncurry f ∘ (λ b, (a, b))), from h.comp (by continuity)

lemma continuous_uncurry_right {f : α → β → γ} (b : β)
  (h : continuous (function.uncurry f)) : continuous (λ a, f a b) :=
show continuous (function.uncurry f ∘ (λ a, (a, b))), from h.comp (by continuity)

lemma continuous_curry {g : α × β → γ} (a : α)
  (h : continuous g) : continuous (function.curry g a) :=
show continuous (g ∘ (λ b, (a, b))), from h.comp (by continuity)

lemma is_open.prod {s : set α} {t : set β} (hs : is_open s) (ht : is_open t) :
  is_open (set.prod s t) :=
is_open.inter (hs.preimage continuous_fst) (ht.preimage continuous_snd)

lemma nhds_prod_eq {a : α} {b : β} : 𝓝 (a, b) = 𝓝 a ×ᶠ 𝓝 b :=
by rw [filter.prod, prod.topological_space, nhds_inf, nhds_induced, nhds_induced]

lemma mem_nhds_prod_iff {a : α} {b : β} {s : set (α × β)} :
  s ∈ 𝓝 (a, b) ↔ ∃ (u ∈ 𝓝 a) (v ∈ 𝓝 b), set.prod u v ⊆ s :=
by rw [nhds_prod_eq, mem_prod_iff]

lemma mem_nhds_prod_iff' {a : α} {b : β} {s : set (α × β)} :
  s ∈ 𝓝 (a, b) ↔ ∃ u v, is_open u ∧ a ∈ u ∧ is_open v ∧ b ∈ v ∧ set.prod u v ⊆ s :=
begin
  rw mem_nhds_prod_iff,
  split,
  { rintros ⟨u, Hu, v, Hv, h⟩,
    rcases mem_nhds_iff.1 Hu with ⟨u', u'u, u'_open, Hu'⟩,
    rcases mem_nhds_iff.1 Hv with ⟨v', v'v, v'_open, Hv'⟩,
    exact ⟨u', v', u'_open, Hu', v'_open, Hv', (set.prod_mono u'u v'v).trans h⟩ },
  { rintros ⟨u, v, u_open, au, v_open, bv, huv⟩,
    exact ⟨u, u_open.mem_nhds au, v, v_open.mem_nhds bv, huv⟩ }
end

lemma filter.has_basis.prod_nhds {ιa ιb : Type*} {pa : ιa → Prop} {pb : ιb → Prop}
  {sa : ιa → set α} {sb : ιb → set β} {a : α} {b : β} (ha : (𝓝 a).has_basis pa sa)
  (hb : (𝓝 b).has_basis pb sb) :
  (𝓝 (a, b)).has_basis (λ i : ιa × ιb, pa i.1 ∧ pb i.2) (λ i, (sa i.1).prod (sb i.2)) :=
by { rw nhds_prod_eq, exact ha.prod hb }

lemma filter.has_basis.prod_nhds' {ιa ιb : Type*} {pa : ιa → Prop} {pb : ιb → Prop}
  {sa : ιa → set α} {sb : ιb → set β} {ab : α × β} (ha : (𝓝 ab.1).has_basis pa sa)
  (hb : (𝓝 ab.2).has_basis pb sb) :
  (𝓝 ab).has_basis (λ i : ιa × ιb, pa i.1 ∧ pb i.2) (λ i, (sa i.1).prod (sb i.2)) :=
by { cases ab, exact ha.prod_nhds hb }

instance [discrete_topology α] [discrete_topology β] : discrete_topology (α × β) :=
⟨eq_of_nhds_eq_nhds $ assume ⟨a, b⟩,
  by rw [nhds_prod_eq, nhds_discrete α, nhds_discrete β, nhds_bot, filter.prod_pure_pure]⟩

lemma prod_mem_nhds_iff {s : set α} {t : set β} {a : α} {b : β} :
  s.prod t ∈ 𝓝 (a, b) ↔ s ∈ 𝓝 a ∧ t ∈ 𝓝 b :=
by rw [nhds_prod_eq, prod_mem_prod_iff]

lemma prod_is_open.mem_nhds {s : set α} {t : set β} {a : α} {b : β}
  (ha : s ∈ 𝓝 a) (hb : t ∈ 𝓝 b) : set.prod s t ∈ 𝓝 (a, b) :=
prod_mem_nhds_iff.2 ⟨ha, hb⟩

lemma nhds_swap (a : α) (b : β) : 𝓝 (a, b) = (𝓝 (b, a)).map prod.swap :=
by rw [nhds_prod_eq, filter.prod_comm, nhds_prod_eq]; refl

lemma filter.tendsto.prod_mk_nhds {γ} {a : α} {b : β} {f : filter γ} {ma : γ → α} {mb : γ → β}
  (ha : tendsto ma f (𝓝 a)) (hb : tendsto mb f (𝓝 b)) :
  tendsto (λc, (ma c, mb c)) f (𝓝 (a, b)) :=
by rw [nhds_prod_eq]; exact filter.tendsto.prod_mk ha hb

lemma filter.eventually.curry_nhds {p : α × β → Prop} {x : α} {y : β} (h : ∀ᶠ x in 𝓝 (x, y), p x) :
  ∀ᶠ x' in 𝓝 x, ∀ᶠ y' in 𝓝 y, p (x', y') :=
by { rw [nhds_prod_eq] at h, exact h.curry }

lemma continuous_at.prod {f : α → β} {g : α → γ} {x : α}
  (hf : continuous_at f x) (hg : continuous_at g x) : continuous_at (λx, (f x, g x)) x :=
hf.prod_mk_nhds hg

lemma continuous_at.prod_map {f : α → γ} {g : β → δ} {p : α × β}
  (hf : continuous_at f p.fst) (hg : continuous_at g p.snd) :
  continuous_at (λ p : α × β, (f p.1, g p.2)) p :=
(hf.comp continuous_at_fst).prod (hg.comp continuous_at_snd)

lemma continuous_at.prod_map' {f : α → γ} {g : β → δ} {x : α} {y : β}
  (hf : continuous_at f x) (hg : continuous_at g y) :
  continuous_at (λ p : α × β, (f p.1, g p.2)) (x, y) :=
have hf : continuous_at f (x, y).fst, from hf,
have hg : continuous_at g (x, y).snd, from hg,
hf.prod_map hg

lemma prod_generate_from_generate_from_eq {α β : Type*} {s : set (set α)} {t : set (set β)}
  (hs : ⋃₀ s = univ) (ht : ⋃₀ t = univ) :
  @prod.topological_space α β (generate_from s) (generate_from t) =
  generate_from {g | ∃u∈s, ∃v∈t, g = set.prod u v} :=
let G := generate_from {g | ∃u∈s, ∃v∈t, g = set.prod u v} in
le_antisymm
  (le_generate_from $ assume g ⟨u, hu, v, hv, g_eq⟩, g_eq.symm ▸
    @is_open.prod _ _ (generate_from s) (generate_from t) _ _
      (generate_open.basic _ hu) (generate_open.basic _ hv))
  (le_inf
    (coinduced_le_iff_le_induced.mp $ le_generate_from $ assume u hu,
      have (⋃v∈t, set.prod u v) = prod.fst ⁻¹' u,
        from calc (⋃v∈t, set.prod u v) = set.prod u univ :
            set.ext $ assume ⟨a, b⟩, by rw ← ht; simp [and.left_comm] {contextual:=tt}
          ... = prod.fst ⁻¹' u : by simp [set.prod, preimage],
      show G.is_open (prod.fst ⁻¹' u),
        from this ▸ @is_open_Union _ _ G _ $ assume v, @is_open_Union _ _ G _ $ assume hv,
          generate_open.basic _ ⟨_, hu, _, hv, rfl⟩)
    (coinduced_le_iff_le_induced.mp $ le_generate_from $ assume v hv,
      have (⋃u∈s, set.prod u v) = prod.snd ⁻¹' v,
        from calc (⋃u∈s, set.prod u v) = set.prod univ v:
            set.ext $ assume ⟨a, b⟩, by rw [←hs]; by_cases b ∈ v; simp [h] {contextual:=tt}
          ... = prod.snd ⁻¹' v : by simp [set.prod, preimage],
      show G.is_open (prod.snd ⁻¹' v),
        from this ▸ @is_open_Union _ _ G _ $ assume u, @is_open_Union _ _ G _ $ assume hu,
          generate_open.basic _ ⟨_, hu, _, hv, rfl⟩))

lemma prod_eq_generate_from :
  prod.topological_space =
  generate_from {g | ∃(s:set α) (t:set β), is_open s ∧ is_open t ∧ g = set.prod s t} :=
le_antisymm
  (le_generate_from $ assume g ⟨s, t, hs, ht, g_eq⟩, g_eq.symm ▸ hs.prod ht)
  (le_inf
    (ball_image_of_ball $ λt ht, generate_open.basic _ ⟨t, univ, by simpa [set.prod_eq] using ht⟩)
    (ball_image_of_ball $ λt ht, generate_open.basic _ ⟨univ, t, by simpa [set.prod_eq] using ht⟩))

lemma is_open_prod_iff {s : set (α×β)} : is_open s ↔
  (∀a b, (a, b) ∈ s → ∃u v, is_open u ∧ is_open v ∧ a ∈ u ∧ b ∈ v ∧ set.prod u v ⊆ s) :=
begin
  rw [is_open_iff_nhds],
  simp_rw [le_principal_iff, prod.forall,
    ((nhds_basis_opens _).prod_nhds (nhds_basis_opens _)).mem_iff, prod.exists, exists_prop],
  simp only [and_assoc, and.left_comm]
end

lemma continuous_uncurry_of_discrete_topology_left [discrete_topology α]
  {f : α → β → γ} (h : ∀ a, continuous (f a)) : continuous (function.uncurry f) :=
continuous_iff_continuous_at.2 $ λ ⟨a, b⟩,
  by simp only [continuous_at, nhds_prod_eq, nhds_discrete α, pure_prod, tendsto_map'_iff, (∘),
    function.uncurry, (h a).tendsto]

/-- Given a neighborhood `s` of `(x, x)`, then `(x, x)` has a square open neighborhood
  that is a subset of `s`. -/
lemma exists_nhds_square {s : set (α × α)} {x : α} (hx : s ∈ 𝓝 (x, x)) :
  ∃U, is_open U ∧ x ∈ U ∧ set.prod U U ⊆ s :=
by simpa [nhds_prod_eq, (nhds_basis_opens x).prod_self.mem_iff, and.assoc, and.left_comm] using hx

/-- `prod.fst` maps neighborhood of `x : α × β` within the section `prod.snd ⁻¹' {x.2}`
to `𝓝 x.1`. -/
lemma map_fst_nhds_within (x : α × β) : map prod.fst (𝓝[prod.snd ⁻¹' {x.2}] x) = 𝓝 x.1 :=
begin
  refine le_antisymm (continuous_at_fst.mono_left inf_le_left) (λ s hs, _),
  rcases x with ⟨x, y⟩,
  rw [mem_map, nhds_within, mem_inf_principal, mem_nhds_prod_iff] at hs,
  rcases hs with ⟨u, hu, v, hv, H⟩,
  simp only [prod_subset_iff, mem_singleton_iff, mem_set_of_eq, mem_preimage] at H,
  exact mem_sets_of_superset hu (λ z hz, H _ hz _ (mem_of_mem_nhds hv) rfl)
end

@[simp] lemma map_fst_nhds (x : α × β) : map prod.fst (𝓝 x) = 𝓝 x.1 :=
le_antisymm continuous_at_fst $ (map_fst_nhds_within x).symm.trans_le (map_mono inf_le_left)

/-- The first projection in a product of topological spaces sends open sets to open sets. -/
lemma is_open_map_fst : is_open_map (@prod.fst α β) :=
is_open_map_iff_nhds_le.2 $ λ x, (map_fst_nhds x).ge

/-- `prod.snd` maps neighborhood of `x : α × β` within the section `prod.fst ⁻¹' {x.1}`
to `𝓝 x.2`. -/
lemma map_snd_nhds_within (x : α × β) : map prod.snd (𝓝[prod.fst ⁻¹' {x.1}] x) = 𝓝 x.2 :=
begin
  refine le_antisymm (continuous_at_snd.mono_left inf_le_left) (λ s hs, _),
  rcases x with ⟨x, y⟩,
  rw [mem_map, nhds_within, mem_inf_principal, mem_nhds_prod_iff] at hs,
  rcases hs with ⟨u, hu, v, hv, H⟩,
  simp only [prod_subset_iff, mem_singleton_iff, mem_set_of_eq, mem_preimage] at H,
  exact mem_sets_of_superset hv (λ z hz, H _ (mem_of_mem_nhds hu) _ hz rfl)
end

@[simp] lemma map_snd_nhds (x : α × β) : map prod.snd (𝓝 x) = 𝓝 x.2 :=
le_antisymm continuous_at_snd $ (map_snd_nhds_within x).symm.trans_le (map_mono inf_le_left)

/-- The second projection in a product of topological spaces sends open sets to open sets. -/
lemma is_open_map_snd : is_open_map (@prod.snd α β) :=
is_open_map_iff_nhds_le.2 $ λ x, (map_snd_nhds x).ge

/-- A product set is open in a product space if and only if each factor is open, or one of them is
empty -/
lemma is_open_prod_iff' {s : set α} {t : set β} :
  is_open (set.prod s t) ↔ (is_open s ∧ is_open t) ∨ (s = ∅) ∨ (t = ∅) :=
begin
  cases (set.prod s t).eq_empty_or_nonempty with h h,
  { simp [h, prod_eq_empty_iff.1 h] },
  { have st : s.nonempty ∧ t.nonempty, from prod_nonempty_iff.1 h,
    split,
    { assume H : is_open (set.prod s t),
      refine or.inl ⟨_, _⟩,
      show is_open s,
      { rw ← fst_image_prod s st.2,
        exact is_open_map_fst _ H },
      show is_open t,
      { rw ← snd_image_prod st.1 t,
        exact is_open_map_snd _ H } },
    { assume H,
      simp only [st.1.ne_empty, st.2.ne_empty, not_false_iff, or_false] at H,
      exact H.1.prod H.2 } }
end

lemma closure_prod_eq {s : set α} {t : set β} :
  closure (set.prod s t) = set.prod (closure s) (closure t) :=
set.ext $ assume ⟨a, b⟩,
have (𝓝 a ×ᶠ 𝓝 b) ⊓ 𝓟 (set.prod s t) = (𝓝 a ⊓ 𝓟 s) ×ᶠ (𝓝 b ⊓ 𝓟 t),
  by rw [←prod_inf_prod, prod_principal_principal],
by simp [closure_eq_cluster_pts, cluster_pt, nhds_prod_eq, this]; exact prod_ne_bot

lemma interior_prod_eq (s : set α) (t : set β) :
  interior (s.prod t) = (interior s).prod (interior t) :=
set.ext $ λ ⟨a, b⟩, by simp only [mem_interior_iff_mem_nhds, mem_prod, prod_mem_nhds_iff]

lemma frontier_prod_eq (s : set α) (t : set β) :
  frontier (s.prod t) = (closure s).prod (frontier t) ∪ (frontier s).prod (closure t) :=
by simp only [frontier, closure_prod_eq, interior_prod_eq, prod_diff_prod]

@[simp] lemma frontier_prod_univ_eq (s : set α) :
  frontier (s.prod (univ : set β)) = (frontier s).prod univ :=
by simp [frontier_prod_eq]

@[simp] lemma frontier_univ_prod_eq (s : set β) :
  frontier ((univ : set α).prod s) = (univ : set α).prod (frontier s) :=
by simp [frontier_prod_eq]

lemma map_mem_closure2 {s : set α} {t : set β} {u : set γ} {f : α → β → γ} {a : α} {b : β}
  (hf : continuous (λp:α×β, f p.1 p.2)) (ha : a ∈ closure s) (hb : b ∈ closure t)
  (hu : ∀a b, a ∈ s → b ∈ t → f a b ∈ u) :
  f a b ∈ closure u :=
have (a, b) ∈ closure (set.prod s t), by rw [closure_prod_eq]; from ⟨ha, hb⟩,
show (λp:α×β, f p.1 p.2) (a, b) ∈ closure u, from
  map_mem_closure hf this $ assume ⟨a, b⟩ ⟨ha, hb⟩, hu a b ha hb

lemma is_closed.prod {s₁ : set α} {s₂ : set β} (h₁ : is_closed s₁) (h₂ : is_closed s₂) :
  is_closed (set.prod s₁ s₂) :=
closure_eq_iff_is_closed.mp $ by simp only [h₁.closure_eq, h₂.closure_eq, closure_prod_eq]

/-- The product of two dense sets is a dense set. -/
lemma dense.prod {s : set α} {t : set β} (hs : dense s) (ht : dense t) :
  dense (s.prod t) :=
λ x, by { rw closure_prod_eq, exact ⟨hs x.1, ht x.2⟩ }

/-- If `f` and `g` are maps with dense range, then `prod.map f g` has dense range. -/
lemma dense_range.prod_map {ι : Type*} {κ : Type*} {f : ι → β} {g : κ → γ}
  (hf : dense_range f) (hg : dense_range g) : dense_range (prod.map f g) :=
by simpa only [dense_range, prod_range_range_eq] using hf.prod hg

lemma inducing.prod_mk {f : α → β} {g : γ → δ} (hf : inducing f) (hg : inducing g) :
  inducing (λx:α×γ, (f x.1, g x.2)) :=
⟨by rw [prod.topological_space, prod.topological_space, hf.induced, hg.induced,
         induced_compose, induced_compose, induced_inf, induced_compose, induced_compose]⟩

lemma embedding.prod_mk {f : α → β} {g : γ → δ} (hf : embedding f) (hg : embedding g) :
  embedding (λx:α×γ, (f x.1, g x.2)) :=
{ inj := assume ⟨x₁, x₂⟩ ⟨y₁, y₂⟩, by simp; exact assume h₁ h₂, ⟨hf.inj h₁, hg.inj h₂⟩,
  ..hf.to_inducing.prod_mk hg.to_inducing }

protected lemma is_open_map.prod {f : α → β} {g : γ → δ} (hf : is_open_map f) (hg : is_open_map g) :
  is_open_map (λ p : α × γ, (f p.1, g p.2)) :=
begin
  rw [is_open_map_iff_nhds_le],
  rintros ⟨a, b⟩,
  rw [nhds_prod_eq, nhds_prod_eq, ← filter.prod_map_map_eq],
  exact filter.prod_mono (is_open_map_iff_nhds_le.1 hf a) (is_open_map_iff_nhds_le.1 hg b)
end

protected lemma open_embedding.prod {f : α → β} {g : γ → δ}
  (hf : open_embedding f) (hg : open_embedding g) : open_embedding (λx:α×γ, (f x.1, g x.2)) :=
open_embedding_of_embedding_open (hf.1.prod_mk hg.1)
  (hf.is_open_map.prod hg.is_open_map)

lemma embedding_graph {f : α → β} (hf : continuous f) : embedding (λx, (x, f x)) :=
embedding_of_embedding_compose (continuous_id.prod_mk hf) continuous_fst embedding_id

end prod

section sum
open sum
variables [topological_space α] [topological_space β] [topological_space γ]

@[continuity] lemma continuous_inl : continuous (@inl α β) :=
continuous_sup_rng_left continuous_coinduced_rng

@[continuity] lemma continuous_inr : continuous (@inr α β) :=
continuous_sup_rng_right continuous_coinduced_rng

@[continuity] lemma continuous_sum_rec {f : α → γ} {g : β → γ}
  (hf : continuous f) (hg : continuous g) : @continuous (α ⊕ β) γ _ _ (@sum.rec α β (λ_, γ) f g) :=
begin
  apply continuous_sup_dom;
  rw continuous_def at hf hg ⊢;
  assumption
end

lemma is_open_sum_iff {s : set (α ⊕ β)} :
  is_open s ↔ is_open (inl ⁻¹' s) ∧ is_open (inr ⁻¹' s) :=
iff.rfl

lemma is_open_map_sum {f : α ⊕ β → γ}
  (h₁ : is_open_map (λ a, f (inl a))) (h₂ : is_open_map (λ b, f (inr b))) :
  is_open_map f :=
begin
  intros u hu,
  rw is_open_sum_iff at hu,
  cases hu with hu₁ hu₂,
  have : u = inl '' (inl ⁻¹' u) ∪ inr '' (inr ⁻¹' u),
  { ext (_|_); simp },
  rw [this, set.image_union, set.image_image, set.image_image],
  exact is_open.union (h₁ _ hu₁) (h₂ _ hu₂)
end

lemma embedding_inl : embedding (@inl α β) :=
{ induced := begin
    unfold sum.topological_space,
    apply le_antisymm,
    { rw ← coinduced_le_iff_le_induced, exact le_sup_left },
    { intros u hu, existsi (inl '' u),
      change
        (is_open (inl ⁻¹' (@inl α β '' u)) ∧
         is_open (inr ⁻¹' (@inl α β '' u))) ∧
        inl ⁻¹' (inl '' u) = u,
      have : inl ⁻¹' (@inl α β '' u) = u :=
        preimage_image_eq u (λ _ _, inl.inj_iff.mp), rw this,
      have : inr ⁻¹' (@inl α β '' u) = ∅ :=
        eq_empty_iff_forall_not_mem.mpr (assume a ⟨b, _, h⟩, inl_ne_inr h), rw this,
      exact ⟨⟨hu, is_open_empty⟩, rfl⟩ }
  end,
  inj := λ _ _, inl.inj_iff.mp }

lemma embedding_inr : embedding (@inr α β) :=
{ induced := begin
    unfold sum.topological_space,
    apply le_antisymm,
    { rw ← coinduced_le_iff_le_induced, exact le_sup_right },
    { intros u hu, existsi (inr '' u),
      change
        (is_open (inl ⁻¹' (@inr α β '' u)) ∧
         is_open (inr ⁻¹' (@inr α β '' u))) ∧
        inr ⁻¹' (inr '' u) = u,
      have : inl ⁻¹' (@inr α β '' u) = ∅ :=
        eq_empty_iff_forall_not_mem.mpr (assume b ⟨a, _, h⟩, inr_ne_inl h), rw this,
      have : inr ⁻¹' (@inr α β '' u) = u :=
        preimage_image_eq u (λ _ _, inr.inj_iff.mp), rw this,
      exact ⟨⟨is_open_empty, hu⟩, rfl⟩ }
  end,
  inj := λ _ _, inr.inj_iff.mp }

lemma is_open_range_inl : is_open (range (inl : α → α ⊕ β)) :=
is_open_sum_iff.2 $ by simp

lemma is_open_range_inr : is_open (range (inr : β → α ⊕ β)) :=
is_open_sum_iff.2 $ by simp

lemma open_embedding_inl : open_embedding (inl : α → α ⊕ β) :=
{ open_range := is_open_range_inl,
  .. embedding_inl }

lemma open_embedding_inr : open_embedding (inr : β → α ⊕ β) :=
{ open_range := is_open_range_inr,
  .. embedding_inr }

end sum

section subtype
variables [topological_space α] [topological_space β] [topological_space γ] {p : α → Prop}

lemma embedding_subtype_coe : embedding (coe : subtype p → α) :=
⟨⟨rfl⟩, subtype.coe_injective⟩

lemma closed_embedding_subtype_coe (h : is_closed {a | p a}) :
  closed_embedding (coe : subtype p → α) :=
⟨embedding_subtype_coe, by rwa [subtype.range_coe_subtype]⟩

@[continuity] lemma continuous_subtype_val : continuous (@subtype.val α p) :=
continuous_induced_dom

lemma continuous_subtype_coe : continuous (coe : subtype p → α) :=
continuous_subtype_val

lemma is_open.open_embedding_subtype_coe {s : set α} (hs : is_open s) :
  open_embedding (coe : s → α) :=
{ induced := rfl,
  inj := subtype.coe_injective,
  open_range := (subtype.range_coe : range coe = s).symm ▸  hs }

lemma is_open.is_open_map_subtype_coe {s : set α} (hs : is_open s) :
  is_open_map (coe : s → α) :=
hs.open_embedding_subtype_coe.is_open_map

lemma is_open_map.restrict {f : α → β} (hf : is_open_map f) {s : set α} (hs : is_open s) :
  is_open_map (s.restrict f) :=
hf.comp hs.is_open_map_subtype_coe

lemma is_closed.closed_embedding_subtype_coe {s : set α} (hs : is_closed s) :
  closed_embedding (coe : {x // x ∈ s} → α) :=
{ induced := rfl,
  inj := subtype.coe_injective,
  closed_range := (subtype.range_coe : range coe = s).symm ▸ hs }

@[continuity] lemma continuous_subtype_mk {f : β → α}
  (hp : ∀x, p (f x)) (h : continuous f) : continuous (λx, (⟨f x, hp x⟩ : subtype p)) :=
continuous_induced_rng h

lemma continuous_inclusion {s t : set α} (h : s ⊆ t) : continuous (inclusion h) :=
continuous_subtype_mk _ continuous_subtype_coe

lemma continuous_at_subtype_coe {p : α → Prop} {a : subtype p} :
  continuous_at (coe : subtype p → α) a :=
continuous_iff_continuous_at.mp continuous_subtype_coe _

lemma map_nhds_subtype_coe_eq {a : α} (ha : p a) (h : {a | p a} ∈ 𝓝 a) :
  map (coe : subtype p → α) (𝓝 ⟨a, ha⟩) = 𝓝 a :=
map_nhds_induced_of_mem $ by simpa only [subtype.coe_mk, subtype.range_coe] using h

lemma nhds_subtype_eq_comap {a : α} {h : p a} :
  𝓝 (⟨a, h⟩ : subtype p) = comap coe (𝓝 a) :=
nhds_induced _ _

lemma tendsto_subtype_rng {β : Type*} {p : α → Prop} {b : filter β} {f : β → subtype p} :
  ∀{a:subtype p}, tendsto f b (𝓝 a) ↔ tendsto (λx, (f x : α)) b (𝓝 (a : α))
| ⟨a, ha⟩ := by rw [nhds_subtype_eq_comap, tendsto_comap_iff, subtype.coe_mk]

lemma continuous_subtype_nhds_cover {ι : Sort*} {f : α → β} {c : ι → α → Prop}
  (c_cover : ∀x:α, ∃i, {x | c i x} ∈ 𝓝 x)
  (f_cont  : ∀i, continuous (λ(x : subtype (c i)), f x)) :
  continuous f :=
continuous_iff_continuous_at.mpr $ assume x,
  let ⟨i, (c_sets : {x | c i x} ∈ 𝓝 x)⟩ := c_cover x in
  let x' : subtype (c i) := ⟨x, mem_of_mem_nhds c_sets⟩ in
  calc map f (𝓝 x) = map f (map coe (𝓝 x')) :
      congr_arg (map f) (map_nhds_subtype_coe_eq _ $ c_sets).symm
    ... = map (λx:subtype (c i), f x) (𝓝 x') : rfl
    ... ≤ 𝓝 (f x) : continuous_iff_continuous_at.mp (f_cont i) x'

lemma continuous_subtype_is_closed_cover {ι : Sort*} {f : α → β} (c : ι → α → Prop)
  (h_lf : locally_finite (λi, {x | c i x}))
  (h_is_closed : ∀i, is_closed {x | c i x})
  (h_cover : ∀x, ∃i, c i x)
  (f_cont  : ∀i, continuous (λ(x : subtype (c i)), f x)) :
  continuous f :=
continuous_iff_is_closed.mpr $
  assume s hs,
  have ∀i, is_closed ((coe : {x | c i x} → α) '' (f ∘ coe ⁻¹' s)),
    from assume i,
    (closed_embedding_subtype_coe (h_is_closed _)).is_closed_map _ (hs.preimage (f_cont i)),
  have is_closed (⋃i, (coe : {x | c i x} → α) '' (f ∘ coe ⁻¹' s)),
    from locally_finite.is_closed_Union
      (h_lf.subset $ assume i x ⟨⟨x', hx'⟩, _, heq⟩, heq ▸ hx')
      this,
  have f ⁻¹' s = (⋃i, (coe : {x | c i x} → α) '' (f ∘ coe ⁻¹' s)),
  begin
    apply set.ext,
    have : ∀ (x : α), f x ∈ s ↔ ∃ (i : ι), c i x ∧ f x ∈ s :=
      λ x, ⟨λ hx, let ⟨i, hi⟩ := h_cover x in ⟨i, hi, hx⟩,
            λ ⟨i, hi, hx⟩, hx⟩,
    simpa [and.comm, @and.left_comm (c _ _), ← exists_and_distrib_right],
  end,
  by rwa [this]

lemma closure_subtype {x : {a // p a}} {s : set {a // p a}}:
  x ∈ closure s ↔ (x : α) ∈ closure ((coe : _ → α) '' s) :=
closure_induced

end subtype

section quotient
variables [topological_space α] [topological_space β] [topological_space γ]
variables {r : α → α → Prop} {s : setoid α}

lemma quotient_map_quot_mk : quotient_map (@quot.mk α r) :=
⟨quot.exists_rep, rfl⟩

@[continuity] lemma continuous_quot_mk : continuous (@quot.mk α r) :=
continuous_coinduced_rng

@[continuity] lemma continuous_quot_lift {f : α → β} (hr : ∀ a b, r a b → f a = f b)
  (h : continuous f) : continuous (quot.lift f hr : quot r → β) :=
continuous_coinduced_dom h

lemma quotient_map_quotient_mk : quotient_map (@quotient.mk α s) :=
quotient_map_quot_mk

lemma continuous_quotient_mk : continuous (@quotient.mk α s) :=
continuous_coinduced_rng

lemma continuous_quotient_lift {f : α → β} (hs : ∀ a b, a ≈ b → f a = f b)
  (h : continuous f) : continuous (quotient.lift f hs : quotient s → β) :=
continuous_coinduced_dom h

end quotient

section pi
variables {ι : Type*} {π : ι → Type*}

@[continuity]
lemma continuous_pi [topological_space α] [∀i, topological_space (π i)] {f : α → Πi:ι, π i}
  (h : ∀i, continuous (λa, f a i)) : continuous f :=
continuous_infi_rng $ assume i, continuous_induced_rng $ h i

@[continuity]
lemma continuous_apply [∀i, topological_space (π i)] (i : ι) :
  continuous (λp:Πi, π i, p i) :=
continuous_infi_dom continuous_induced_dom

lemma continuous_at_apply [∀i, topological_space (π i)] (i : ι) (x : Π i, π i) :
  continuous_at (λ p : Π i, π i, p i) x :=
(continuous_apply i).continuous_at

lemma filter.tendsto.apply [∀i, topological_space (π i)] {l : filter α} {f : α → Π i, π i}
  {x : Π i, π i} (h : tendsto f l (𝓝 x)) (i : ι) :
  tendsto (λ a, f a i) l (𝓝 $ x i) :=
(continuous_at_apply i _).tendsto.comp h

lemma continuous_pi_iff [topological_space α] [∀ i, topological_space (π i)] {f : α → Π i, π i} :
  continuous f ↔ ∀ i, continuous (λ y, f y i) :=
iff.intro (λ h i, (continuous_apply i).comp h) continuous_pi

lemma nhds_pi [t : ∀i, topological_space (π i)] {a : Πi, π i} :
  𝓝 a = (⨅i, comap (λx, x i) (𝓝 (a i))) :=
calc 𝓝 a = (⨅i, @nhds _ (@topological_space.induced _ _ (λx:Πi, π i, x i) (t i)) a) : nhds_infi
  ... = (⨅i, comap (λx, x i) (𝓝 (a i))) : by simp [nhds_induced]

lemma tendsto_pi [t : ∀i, topological_space (π i)] {f : α → Πi, π i} {g : Πi, π i} {u : filter α} :
  tendsto f u (𝓝 g) ↔ ∀ x, tendsto (λ i, f i x) u (𝓝 (g x)) :=
by simp [nhds_pi, filter.tendsto_comap_iff]

lemma continuous_at_pi [∀ i, topological_space (π i)] [topological_space α] {f : α → Π i, π i}
  {x : α} :
  continuous_at f x ↔ ∀ i, continuous_at (λ y, f y i) x :=
tendsto_pi

lemma filter.tendsto.update [∀i, topological_space (π i)] [decidable_eq ι]
  {l : filter α} {f : α → Π i, π i} {x : Π i, π i} (hf : tendsto f l (𝓝 x)) (i : ι)
  {g : α → π i} {xi : π i} (hg : tendsto g l (𝓝 xi)) :
  tendsto (λ a, function.update (f a) i (g a)) l (𝓝 $ function.update x i xi) :=
tendsto_pi.2 $ λ j, by { rcases em (j = i) with rfl|hj; simp [*, hf.apply] }

lemma continuous_at.update [∀i, topological_space (π i)] [topological_space α] [decidable_eq ι]
  {f : α → Π i, π i} {a : α} (hf : continuous_at f a) (i : ι) {g : α → π i}
  (hg : continuous_at g a) :
  continuous_at (λ a, function.update (f a) i (g a)) a :=
hf.update i hg

lemma continuous.update [∀i, topological_space (π i)] [topological_space α] [decidable_eq ι]
  {f : α → Π i, π i} (hf : continuous f) (i : ι) {g : α → π i} (hg : continuous g) :
  continuous (λ a, function.update (f a) i (g a)) :=
continuous_iff_continuous_at.2 $ λ x, hf.continuous_at.update i hg.continuous_at

/-- `function.update f i x` is continuous in `(f, x)`. -/
@[continuity] lemma continuous_update [∀i, topological_space (π i)] [decidable_eq ι] (i : ι) :
  continuous (λ f : (Π j, π j) × π i, function.update f.1 i f.2) :=
continuous_fst.update i continuous_snd

lemma is_open_set_pi [∀a, topological_space (π a)] {i : set ι} {s : Πa, set (π a)}
  (hi : finite i) (hs : ∀a∈i, is_open (s a)) : is_open (pi i s) :=
by rw [pi_def]; exact (is_open_bInter hi $ assume a ha, (hs _ ha).preimage (continuous_apply _))

lemma is_closed_set_pi [∀a, topological_space (π a)] {i : set ι} {s : Πa, set (π a)}
  (hs : ∀a∈i, is_closed (s a)) : is_closed (pi i s) :=
by rw [pi_def];
  exact (is_closed_Inter $ λ a, is_closed_Inter $ λ ha, (hs _ ha).preimage (continuous_apply _))

lemma set_pi_mem_nhds [Π a, topological_space (π a)] {i : set ι} {s : Π a, set (π a)}
  {x : Π a, π a} (hi : finite i) (hs : ∀ a ∈ i, s a ∈ 𝓝 (x a)) :
  pi i s ∈ 𝓝 x :=
by { rw [pi_def, bInter_mem_sets hi], exact λ a ha, (continuous_apply a).continuous_at (hs a ha) }

lemma pi_eq_generate_from [∀a, topological_space (π a)] :
  Pi.topological_space =
  generate_from {g | ∃(s:Πa, set (π a)) (i : finset ι), (∀a∈i, is_open (s a)) ∧ g = pi ↑i s} :=
le_antisymm
  (le_generate_from $ assume g ⟨s, i, hi, eq⟩, eq.symm ▸ is_open_set_pi (finset.finite_to_set _) hi)
  (le_infi $ assume a s ⟨t, ht, s_eq⟩, generate_open.basic _ $
    ⟨function.update (λa, univ) a t, {a}, by simpa using ht, by ext f; simp [s_eq.symm, pi]⟩)

lemma pi_generate_from_eq {g : Πa, set (set (π a))} :
  @Pi.topological_space ι π (λa, generate_from (g a)) =
  generate_from {t | ∃(s:Πa, set (π a)) (i : finset ι), (∀a∈i, s a ∈ g a) ∧ t = pi ↑i s} :=
let G := {t | ∃(s:Πa, set (π a)) (i : finset ι), (∀a∈i, s a ∈ g a) ∧ t = pi ↑i s} in
begin
  rw [pi_eq_generate_from],
  refine le_antisymm (generate_from_mono _) (le_generate_from _),
  exact assume s ⟨t, i, ht, eq⟩, ⟨t, i, assume a ha, generate_open.basic _ (ht a ha), eq⟩,
  { rintros s ⟨t, i, hi, rfl⟩,
    rw [pi_def],
    apply is_open_bInter (finset.finite_to_set _),
    assume a ha, show ((generate_from G).coinduced (λf:Πa, π a, f a)).is_open (t a),
    refine le_generate_from _ _ (hi a ha),
    exact assume s hs, generate_open.basic _ ⟨function.update (λa, univ) a s, {a}, by simp [hs]⟩ }
end

lemma pi_generate_from_eq_fintype {g : Πa, set (set (π a))} [fintype ι] (hg : ∀a, ⋃₀ g a = univ) :
  @Pi.topological_space ι π (λa, generate_from (g a)) =
  generate_from {t | ∃(s:Πa, set (π a)), (∀a, s a ∈ g a) ∧ t = pi univ s} :=
begin
  rw [pi_generate_from_eq],
  refine le_antisymm (generate_from_mono _) (le_generate_from _),
  exact assume s ⟨t, ht, eq⟩, ⟨t, finset.univ, by simp [ht, eq]⟩,
  { rintros s ⟨t, i, ht, rfl⟩,
    apply is_open_iff_forall_mem_open.2 _,
    assume f hf,
    choose c hc using show ∀a, ∃s, s ∈ g a ∧ f a ∈ s,
    { assume a, have : f a ∈ ⋃₀ g a, { rw [hg], apply mem_univ }, simpa },
    refine ⟨pi univ (λa, if a ∈ i then t a else (c : Πa, set (π a)) a), _, _, _⟩,
    { simp [pi_if] },
    { refine generate_open.basic _ ⟨_, assume a, _, rfl⟩,
      by_cases a ∈ i; simp [*, pi] at * },
    { have : f ∈ pi {a | a ∉ i} c, { simp [*, pi] at * },
      simpa [pi_if, hf] } }
end

/-- Suppose `π i` is a family of topological spaces indexed by `i : ι`, and `X` is a type
endowed with a family of maps `f i : X → π i` for every `i : ι`, hence inducing a
map `g : X → Π i, π i`. This lemma shows that infimum of the topologies on `X` induced by
the `f i` as `i : ι` varies is simply the topology on `X` induced by `g : X → Π i, π i`
where `Π i, π i` is endowed with the usual product topology. -/
lemma inducing_infi_to_pi {X : Type*} [∀ i, topological_space (π i)] (f : Π i, X → π i) :
  @inducing X (Π i, π i) (⨅ i, induced (f i) infer_instance) _ (λ x i, f i x) :=
begin
  constructor,
  erw induced_infi,
  congr' 1,
  funext,
  erw induced_compose,
end

variables [fintype ι] [∀ i, topological_space (π i)] [∀ i, discrete_topology (π i)]

/-- A finite product of discrete spaces is discrete. -/
instance Pi.discrete_topology : discrete_topology (Π i, π i) :=
singletons_open_iff_discrete.mp (λ x,
begin
  rw show {x} = ⋂ i, {y : Π i, π i | y i = x i},
  { ext, simp only [function.funext_iff, set.mem_singleton_iff, set.mem_Inter, set.mem_set_of_eq] },
  exact is_open_Inter (λ i, (continuous_apply i).is_open_preimage {x i} (is_open_discrete {x i}))
end)

end pi

section sigma
variables {ι : Type*} {σ : ι → Type*} [Π i, topological_space (σ i)]

@[continuity]
lemma continuous_sigma_mk {i : ι} : continuous (@sigma.mk ι σ i) :=
continuous_supr_rng continuous_coinduced_rng

lemma is_open_sigma_iff {s : set (sigma σ)} : is_open s ↔ ∀ i, is_open (sigma.mk i ⁻¹' s) :=
by simp only [is_open_supr_iff, is_open_coinduced]

lemma is_closed_sigma_iff {s : set (sigma σ)} : is_closed s ↔ ∀ i, is_closed (sigma.mk i ⁻¹' s) :=
by simp [← is_open_compl_iff, is_open_sigma_iff]

lemma is_open_map_sigma_mk {i : ι} : is_open_map (@sigma.mk ι σ i) :=
begin
  intros s hs,
  rw is_open_sigma_iff,
  intro j,
  classical,
  by_cases h : i = j,
  { subst j,
    convert hs,
    exact set.preimage_image_eq _ sigma_mk_injective },
  { convert is_open_empty,
    apply set.eq_empty_of_subset_empty,
    rintro x ⟨y, _, hy⟩,
    have : i = j, by cc,
    contradiction }
end

lemma is_open_range_sigma_mk {i : ι} : is_open (set.range (@sigma.mk ι σ i)) :=
by { rw ←set.image_univ, exact is_open_map_sigma_mk _ is_open_univ }

lemma is_closed_map_sigma_mk {i : ι} : is_closed_map (@sigma.mk ι σ i) :=
begin
  intros s hs,
  rw is_closed_sigma_iff,
  intro j,
  classical,
  by_cases h : i = j,
  { subst j,
    convert hs,
    exact set.preimage_image_eq _ sigma_mk_injective },
  { convert is_closed_empty,
    apply set.eq_empty_of_subset_empty,
    rintro x ⟨y, _, hy⟩,
    have : i = j, by cc,
    contradiction }
end

lemma is_closed_sigma_mk {i : ι} : is_closed (set.range (@sigma.mk ι σ i)) :=
by { rw ←set.image_univ, exact is_closed_map_sigma_mk _ is_closed_univ }

lemma open_embedding_sigma_mk {i : ι} : open_embedding (@sigma.mk ι σ i) :=
open_embedding_of_continuous_injective_open
  continuous_sigma_mk sigma_mk_injective is_open_map_sigma_mk

lemma closed_embedding_sigma_mk {i : ι} : closed_embedding (@sigma.mk ι σ i) :=
closed_embedding_of_continuous_injective_closed
  continuous_sigma_mk sigma_mk_injective is_closed_map_sigma_mk

lemma embedding_sigma_mk {i : ι} : embedding (@sigma.mk ι σ i) :=
closed_embedding_sigma_mk.1

/-- A map out of a sum type is continuous if its restriction to each summand is. -/
@[continuity]
lemma continuous_sigma [topological_space β] {f : sigma σ → β}
  (h : ∀ i, continuous (λ a, f ⟨i, a⟩)) : continuous f :=
continuous_supr_dom (λ i, continuous_coinduced_dom (h i))

@[continuity]
lemma continuous_sigma_map {κ : Type*} {τ : κ → Type*} [Π k, topological_space (τ k)]
  {f₁ : ι → κ} {f₂ : Π i, σ i → τ (f₁ i)} (hf : ∀ i, continuous (f₂ i)) :
  continuous (sigma.map f₁ f₂) :=
continuous_sigma $ λ i,
  show continuous (λ a, sigma.mk (f₁ i) (f₂ i a)),
  from continuous_sigma_mk.comp (hf i)

lemma is_open_map_sigma [topological_space β] {f : sigma σ → β}
  (h : ∀ i, is_open_map (λ a, f ⟨i, a⟩)) : is_open_map f :=
begin
  intros s hs,
  rw is_open_sigma_iff at hs,
  have : s = ⋃ i, sigma.mk i '' (sigma.mk i ⁻¹' s),
  { rw Union_image_preimage_sigma_mk_eq_self },
  rw this,
  rw [image_Union],
  apply is_open_Union,
  intro i,
  rw [image_image],
  exact h i _ (hs i)
end

/-- The sum of embeddings is an embedding. -/
lemma embedding_sigma_map {τ : ι → Type*} [Π i, topological_space (τ i)]
  {f : Π i, σ i → τ i} (hf : ∀ i, embedding (f i)) : embedding (sigma.map id f) :=
begin
  refine ⟨⟨_⟩, function.injective_id.sigma_map (λ i, (hf i).inj)⟩,
  refine le_antisymm
    (continuous_iff_le_induced.mp (continuous_sigma_map (λ i, (hf i).continuous))) _,
  intros s hs,
  replace hs := is_open_sigma_iff.mp hs,
  have : ∀ i, ∃ t, is_open t ∧ f i ⁻¹' t = sigma.mk i ⁻¹' s,
  { intro i,
    apply is_open_induced_iff.mp,
    convert hs i,
    exact (hf i).induced.symm },
  choose t ht using this,
  apply is_open_induced_iff.mpr,
  refine ⟨⋃ i, sigma.mk i '' t i, is_open_Union (λ i, is_open_map_sigma_mk _ (ht i).1), _⟩,
  ext ⟨i, x⟩,
  change (sigma.mk i (f i x) ∈ ⋃ (i : ι), sigma.mk i '' t i) ↔ x ∈ sigma.mk i ⁻¹' s,
  rw [←(ht i).2, mem_Union],
  split,
  { rintro ⟨j, hj⟩,
    rw mem_image at hj,
    rcases hj with ⟨y, hy₁, hy₂⟩,
    rcases sigma.mk.inj_iff.mp hy₂ with ⟨rfl, hy⟩,
    replace hy := eq_of_heq hy,
    subst y,
    exact hy₁ },
  { intro hx,
    use i,
    rw mem_image,
    exact ⟨f i x, hx, rfl⟩ }
end

end sigma

section ulift

@[continuity] lemma continuous_ulift_down [topological_space α] :
  continuous (ulift.down : ulift.{v u} α → α) :=
continuous_induced_dom

@[continuity] lemma continuous_ulift_up [topological_space α] :
  continuous (ulift.up : α → ulift.{v u} α) :=
continuous_induced_rng continuous_id

end ulift

lemma mem_closure_of_continuous [topological_space α] [topological_space β]
  {f : α → β} {a : α} {s : set α} {t : set β}
  (hf : continuous f) (ha : a ∈ closure s) (h : maps_to f s (closure t)) :
  f a ∈ closure t :=
calc f a ∈ f '' closure s : mem_image_of_mem _ ha
  ... ⊆ closure (f '' s) : image_closure_subset_closure_image hf
  ... ⊆ closure t : closure_minimal h.image_subset is_closed_closure

lemma mem_closure_of_continuous2 [topological_space α] [topological_space β] [topological_space γ]
  {f : α → β → γ} {a : α} {b : β} {s : set α} {t : set β} {u : set γ}
  (hf : continuous (λp:α×β, f p.1 p.2)) (ha : a ∈ closure s) (hb : b ∈ closure t)
  (h : ∀a∈s, ∀b∈t, f a b ∈ closure u) :
  f a b ∈ closure u :=
have (a,b) ∈ closure (set.prod s t),
  by simp [closure_prod_eq, ha, hb],
show f (a, b).1 (a, b).2 ∈ closure u,
  from @mem_closure_of_continuous (α×β) _ _ _ (λp:α×β, f p.1 p.2) (a,b) _ u hf this $
    assume ⟨p₁, p₂⟩ ⟨h₁, h₂⟩, h p₁ h₁ p₂ h₂
