/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot
-/

import topology.uniform_space.basic
import tactic.apply_fun

/-!
# Hausdorff properties of uniform spaces. Separation quotient.

This file studies uniform spaces whose underlying topological spaces are separated
(also known as Hausdorff or T₂).
This turns out to be equivalent to asking that the intersection of all entourages
is the diagonal only. This condition actually implies the stronger separation property
that the space is regular (T₃), hence those conditions are equivalent for topologies coming from
a uniform structure.

More generally, the intersection `𝓢 X` of all entourages of `X`, which has type `set (X × X)` is an
equivalence relation on `X`. Points which are equivalent under the relation are basically
undistinguishable from the point of view of the uniform structure. For instance any uniformly
continuous function will send equivalent points to the same value.

The quotient `separation_quotient X` of `X` by `𝓢 X` has a natural uniform structure which is
separated, and satisfies a universal property: every uniformly continuous function
from `X` to a separated uniform space uniquely factors through `separation_quotient X`.
As usual, this allows to turn `separation_quotient` into a functor (but we don't use the
category theory library in this file).

These notions admit relative versions, one can ask that `s : set X` is separated, this
is equivalent to asking that the uniform structure induced on `s` is separated.

## Main definitions

* `separation_relation X : set (X × X)`: the separation relation
* `separated_space X`: a predicate class asserting that `X` is separated
* `is_separated s`: a predicate asserting that `s : set X` is separated
* `separation_quotient X`: the maximal separated quotient of `X`.
* `separation_quotient.lift f`: factors a map `f : X → Y` through the separation quotient of `X`.
* `separation_quotient.map f`: turns a map `f : X → Y` into a map between the separation quotients
  of `X` and `Y`.

## Main results

* `separated_iff_t2`: the equivalence between being separated and being Hausdorff for uniform
  spaces.
* `separation_quotient.uniform_continuous_lift`: factoring a uniformly continuous map through the
  separation quotient gives a uniformly continuous map.
* `separation_quotient.uniform_continuous_map`: maps induced between separation quotients are
  uniformly continuous.

## Notations

Localized in `uniformity`, we have the notation `𝓢 X` for the separation relation
on a uniform space `X`,

## Implementation notes

The separation setoid `separation_setoid` is not declared as a global instance.
It is made a local instance while building the theory of `separation_quotient`.
The factored map `separation_quotient.lift f` is defined without imposing any condition on
`f`, but returns junk if `f` is not uniformly continuous (constant junk hence it is always
uniformly continuous).

-/

open filter topological_space set classical function uniform_space
open_locale classical topological_space uniformity filter
noncomputable theory
set_option eqn_compiler.zeta true

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
variables [uniform_space α] [uniform_space β] [uniform_space γ]


/-!
### Separated uniform spaces
-/

/-- The separation relation is the intersection of all entourages.
  Two points which are related by the separation relation are "indistinguishable"
  according to the uniform structure. -/
protected def separation_rel (α : Type u) [u : uniform_space α] :=
⋂₀ (𝓤 α).sets

localized "notation `𝓢` := separation_rel" in uniformity

lemma separated_equiv : equivalence (λx y, (x, y) ∈ 𝓢 α) :=
⟨assume x, assume s, refl_mem_uniformity,
  assume x y, assume h (s : set (α×α)) hs,
    have preimage prod.swap s ∈ 𝓤 α,
      from symm_le_uniformity hs,
    h _ this,
  assume x y z (hxy : (x, y) ∈ 𝓢 α) (hyz : (y, z) ∈ 𝓢 α)
      s (hs : s ∈ 𝓤 α),
    let ⟨t, ht, (h_ts : comp_rel t t ⊆ s)⟩ := comp_mem_uniformity_sets hs in
    h_ts $ show (x, z) ∈ comp_rel t t,
      from ⟨y, hxy t ht, hyz t ht⟩⟩

/-- A uniform space is separated if its separation relation is trivial (each point
is related only to itself). -/
class separated_space (α : Type u) [uniform_space α] : Prop := (out : 𝓢 α = id_rel)

theorem separated_space_iff {α : Type u} [uniform_space α] :
  separated_space α ↔ 𝓢 α = id_rel :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

theorem separated_def {α : Type u} [uniform_space α] :
  separated_space α ↔ ∀ x y, (∀ r ∈ 𝓤 α, (x, y) ∈ r) → x = y :=
by simp [separated_space_iff, id_rel_subset.2 separated_equiv.1, subset.antisymm_iff];
   simp [subset_def, separation_rel]

theorem separated_def' {α : Type u} [uniform_space α] :
  separated_space α ↔ ∀ x y, x ≠ y → ∃ r ∈ 𝓤 α, (x, y) ∉ r :=
separated_def.trans $ forall_congr $ λ x, forall_congr $ λ y,
by rw ← not_imp_not; simp [not_forall]

lemma eq_of_uniformity {α : Type*} [uniform_space α] [separated_space α] {x y : α}
  (h : ∀ {V}, V ∈ 𝓤 α → (x, y) ∈ V) : x = y :=
separated_def.mp ‹separated_space α› x y (λ _, h)

lemma eq_of_uniformity_basis {α : Type*} [uniform_space α] [separated_space α] {ι : Type*}
  {p : ι → Prop} {s : ι → set (α × α)} (hs : (𝓤 α).has_basis p s) {x y : α}
  (h : ∀ {i}, p i → (x, y) ∈ s i) : x = y :=
eq_of_uniformity (λ V V_in, let ⟨i, hi, H⟩ := hs.mem_iff.mp V_in in H (h hi))

lemma eq_of_forall_symmetric {α : Type*} [uniform_space α] [separated_space α] {x y : α}
  (h : ∀ {V}, V ∈ 𝓤 α → symmetric_rel V → (x, y) ∈ V) : x = y :=
eq_of_uniformity_basis has_basis_symmetric (by simpa [and_imp] using λ _, h)

lemma id_rel_sub_separation_relation (α : Type*) [uniform_space α] : id_rel ⊆ 𝓢 α :=
begin
  unfold separation_rel,
  rw id_rel_subset,
  intros x,
  suffices : ∀ t ∈ 𝓤 α, (x, x) ∈ t, by simpa only [refl_mem_uniformity],
  exact λ t, refl_mem_uniformity,
end

lemma separation_rel_comap  {f : α → β}
  (h : ‹uniform_space α› = uniform_space.comap f ‹uniform_space β›) :
  𝓢 α = (prod.map f f) ⁻¹' 𝓢 β :=
begin
  dsimp [separation_rel],
  rw [uniformity_comap h, (filter.comap_has_basis (prod.map f f) (𝓤 β)).sInter_sets,
      ← preimage_bInter, sInter_eq_bInter],
  refl,
end

protected lemma filter.has_basis.separation_rel {ι : Type*} {p : ι → Prop} {s : ι → set (α × α)}
  (h : has_basis (𝓤 α) p s) :
  𝓢 α = ⋂ i ∈ set_of p, s i :=
by { unfold separation_rel, rw h.sInter_sets }

lemma separation_rel_eq_inter_closure : 𝓢 α = ⋂₀ (closure '' (𝓤 α).sets) :=
by simp [uniformity_has_basis_closure.separation_rel]

lemma is_closed_separation_rel : is_closed (𝓢 α) :=
begin
  rw separation_rel_eq_inter_closure,
  apply is_closed_sInter,
  rintros _ ⟨t, t_in, rfl⟩,
  exact is_closed_closure,
end

lemma separated_iff_t2 : separated_space α ↔ t2_space α :=
begin
  classical,
  split ; intro h,
  { rw [t2_iff_is_closed_diagonal, ← show 𝓢 α = diagonal α, from h.1],
    exact is_closed_separation_rel },
  { rw separated_def',
    intros x y hxy,
    have : 𝓝 x ⊓ 𝓝 y = ⊥,
    { rw t2_iff_nhds at h,
      by_contra H,
      exact hxy (h ⟨H⟩) },
    rcases inf_eq_bot_iff.mp this with ⟨U, U_in, V, V_in, H⟩,
    rcases uniform_space.mem_nhds_iff.mp U_in with ⟨S, S_in, S_sub⟩,
    use [S, S_in],
    change y ∉ ball x S,
    intro y_in,
    have : y ∈ U ∩ V := ⟨S_sub y_in, mem_of_mem_nhds V_in⟩,
    rwa H at this },
end

@[priority 100] -- see Note [lower instance priority]
instance separated_regular [separated_space α] : regular_space α :=
{ t0 := by { haveI := separated_iff_t2.mp ‹_›, exact t1_space.t0_space.t0 },
  regular := λs a hs ha,
    have sᶜ ∈ 𝓝 a,
      from is_open.mem_nhds hs.is_open_compl ha,
    have {p : α × α | p.1 = a → p.2 ∈ sᶜ} ∈ 𝓤 α,
      from mem_nhds_uniformity_iff_right.mp this,
    let ⟨d, hd, h⟩ := comp_mem_uniformity_sets this in
    let e := {y:α| (a, y) ∈ d} in
    have hae : a ∈ closure e, from subset_closure $ refl_mem_uniformity hd,
    have set.prod (closure e) (closure e) ⊆ comp_rel d (comp_rel (set.prod e e) d),
    begin
      rw [←closure_prod_eq, closure_eq_inter_uniformity],
      change (⨅d' ∈ 𝓤 α, _) ≤ comp_rel d (comp_rel _ d),
      exact (infi_le_of_le d $ infi_le_of_le hd $ le_refl _)
    end,
    have e_subset : closure e ⊆ sᶜ,
      from assume a' ha',
        let ⟨x, (hx : (a, x) ∈ d), y, ⟨hx₁, hx₂⟩, (hy : (y, _) ∈ d)⟩ := @this ⟨a, a'⟩ ⟨hae, ha'⟩ in
        have (a, a') ∈ comp_rel d d, from ⟨y, hx₂, hy⟩,
        h this rfl,
    have closure e ∈ 𝓝 a, from (𝓝 a).sets_of_superset (mem_nhds_left a hd) subset_closure,
    have 𝓝 a ⊓ 𝓟 (closure e)ᶜ = ⊥,
      from (@inf_eq_bot_iff_le_compl _ _ _ (𝓟 (closure e)ᶜ) (𝓟 (closure e))
        (by simp [principal_univ, union_comm]) (by simp)).mpr (by simp [this]),
    ⟨(closure e)ᶜ, is_closed_closure.is_open_compl, assume x h₁ h₂, @e_subset x h₂ h₁, this⟩,
    ..@t2_space.t1_space _ _ (separated_iff_t2.mp ‹_›) }

lemma is_closed_of_spaced_out [separated_space α] {V₀ : set (α × α)} (V₀_in : V₀ ∈ 𝓤 α)
  {s : set α} (hs : ∀ {x y}, x ∈ s → y ∈ s → (x, y) ∈ V₀ → x = y) : is_closed s :=
begin
  rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩,
  apply is_closed_of_closure_subset,
  intros x hx,
  rw mem_closure_iff_ball at hx,
  rcases hx V₁_in with ⟨y, hy, hy'⟩,
  suffices : x = y, by rwa this,
  apply eq_of_forall_symmetric,
  intros V V_in V_symm,
  rcases hx (inter_mem_sets V₁_in V_in) with ⟨z, hz, hz'⟩,
  suffices : z = y,
  { rw ← this,
    exact ball_inter_right x _ _ hz },
  exact hs hz' hy' (h_comp $ mem_comp_of_mem_ball V₁_symm (ball_inter_left x _ _ hz) hy)
end

/-!
### Separated sets
-/

/-- A set `s` in a uniform space `α` is separated if the separation relation `𝓢 α`
induces the trivial relation on `s`. -/
def is_separated (s : set α) : Prop := ∀ x y ∈ s, (x, y) ∈ 𝓢 α → x = y

lemma is_separated_def (s : set α) : is_separated s ↔ ∀ x y ∈ s, (x, y) ∈ 𝓢 α → x = y :=
iff.rfl

lemma is_separated_def' (s : set α) : is_separated s ↔ (s.prod s) ∩ 𝓢 α ⊆ id_rel :=
begin
  rw is_separated_def,
  split,
  { rintros h ⟨x, y⟩ ⟨⟨x_in, y_in⟩, H⟩,
    simp [h x y x_in y_in H] },
  { intros h x y x_in y_in xy_in,
    rw ← mem_id_rel,
    exact h ⟨mk_mem_prod x_in y_in, xy_in⟩ }
end


lemma univ_separated_iff : is_separated (univ : set α) ↔ separated_space α :=
begin
  simp only [is_separated, mem_univ, true_implies_iff, separated_space_iff],
  split,
  { intro h,
    exact subset.antisymm (λ ⟨x, y⟩ xy_in, h x y xy_in) (id_rel_sub_separation_relation α), },
  { intros h x y xy_in,
    rwa h at xy_in },
end


lemma is_separated_of_separated_space [separated_space α] (s : set α) : is_separated s :=
begin
  rw [is_separated, separated_space.out],
  tauto,
end

lemma is_separated_iff_induced {s : set α} : is_separated s ↔ separated_space s :=
begin
  rw separated_space_iff,
  change _ ↔ 𝓢 {x // x ∈ s} = _,
  rw [separation_rel_comap rfl, is_separated_def'],
  split; intro h,
  { ext ⟨⟨x, x_in⟩, ⟨y, y_in⟩⟩,
    suffices : (x, y) ∈ 𝓢 α ↔ x = y, by simpa only [mem_id_rel],
    refine ⟨λ H, h ⟨mk_mem_prod x_in y_in, H⟩, _⟩,
    rintro rfl,
    exact id_rel_sub_separation_relation α rfl },
  { rintros ⟨x, y⟩ ⟨⟨x_in, y_in⟩, hS⟩,
    have A : (⟨⟨x, x_in⟩, ⟨y, y_in⟩⟩ : ↥s × ↥s) ∈ prod.map (coe : s → α) (coe : s → α) ⁻¹' 𝓢 α,
      from hS,
    simpa using h.subset A }
end

lemma eq_of_uniformity_inf_nhds_of_is_separated {s : set α} (hs : is_separated s) :
  ∀ {x y : α}, x ∈ s → y ∈ s → cluster_pt (x, y) (𝓤 α) → x = y :=
begin
  intros x y x_in y_in H,
  have : ∀ V ∈ 𝓤 α, (x, y) ∈ closure V,
  { intros V V_in,
    rw mem_closure_iff_cluster_pt,
    have : 𝓤 α ≤ 𝓟 V, by rwa le_principal_iff,
    exact H.mono this },
  apply hs x y x_in y_in,
  simpa [separation_rel_eq_inter_closure],
end

lemma eq_of_uniformity_inf_nhds [separated_space α] :
  ∀ {x y : α}, cluster_pt (x, y) (𝓤 α) → x = y :=
begin
  have : is_separated (univ : set α),
  { rw univ_separated_iff,
    assumption },
  introv,
  simpa using eq_of_uniformity_inf_nhds_of_is_separated this,
end

/-!
### Separation quotient
-/
namespace uniform_space

/-- The separation relation of a uniform space seen as a setoid. -/
def separation_setoid (α : Type u) [uniform_space α] : setoid α :=
⟨λx y, (x, y) ∈ 𝓢 α, separated_equiv⟩

local attribute [instance] separation_setoid

instance separation_setoid.uniform_space {α : Type u} [u : uniform_space α] :
  uniform_space (quotient (separation_setoid α)) :=
{ to_topological_space := u.to_topological_space.coinduced (λx, ⟦x⟧),
  uniformity := map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) u.uniformity,
  refl := le_trans (by simp [quotient.exists_rep]) (filter.map_mono refl_le_uniformity),
  symm := tendsto_map' $
    by simp [prod.swap, (∘)]; exact tendsto_map.comp tendsto_swap_uniformity,
  comp := calc (map (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) u.uniformity).lift' (λs, comp_rel s s) =
          u.uniformity.lift' ((λs, comp_rel s s) ∘ image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧))) :
      map_lift'_eq2 $ monotone_comp_rel monotone_id monotone_id
    ... ≤ u.uniformity.lift' (image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) ∘
            (λs:set (α×α), comp_rel s (comp_rel s s))) :
      lift'_mono' $ assume s hs ⟨a, b⟩ ⟨c, ⟨⟨a₁, a₂⟩, ha, a_eq⟩, ⟨⟨b₁, b₂⟩, hb, b_eq⟩⟩,
      begin
        simp at a_eq,
        simp at b_eq,
        have h : ⟦a₂⟧ = ⟦b₁⟧, { rw [a_eq.right, b_eq.left] },
        have h : (a₂, b₁) ∈ 𝓢 α := quotient.exact h,
        simp [function.comp, set.image, comp_rel, and.comm, and.left_comm, and.assoc],
        exact ⟨a₁, a_eq.left, b₂, b_eq.right, a₂, ha, b₁, h s hs, hb⟩
      end
    ... = map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧))
            (u.uniformity.lift' (λs:set (α×α), comp_rel s (comp_rel s s))) :
      by rw [map_lift'_eq];
        exact monotone_comp_rel monotone_id (monotone_comp_rel monotone_id monotone_id)
    ... ≤ map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) u.uniformity :
      map_mono comp_le_uniformity3,
  is_open_uniformity := assume s,
    have ∀a, ⟦a⟧ ∈ s →
        ({p:α×α | p.1 = a → ⟦p.2⟧ ∈ s} ∈ 𝓤 α ↔
          {p:α×α | p.1 ≈ a → ⟦p.2⟧ ∈ s} ∈ 𝓤 α),
      from assume a ha,
      ⟨assume h,
        let ⟨t, ht, hts⟩ := comp_mem_uniformity_sets h in
        have hts : ∀{a₁ a₂}, (a, a₁) ∈ t → (a₁, a₂) ∈ t → ⟦a₂⟧ ∈ s,
          from assume a₁ a₂ ha₁ ha₂, @hts (a, a₂) ⟨a₁, ha₁, ha₂⟩ rfl,
        have ht' : ∀{a₁ a₂}, a₁ ≈ a₂ → (a₁, a₂) ∈ t,
          from assume a₁ a₂ h, sInter_subset_of_mem ht h,
        u.uniformity.sets_of_superset ht $ assume ⟨a₁, a₂⟩ h₁ h₂, hts (ht' $ setoid.symm h₂) h₁,
        assume h, u.uniformity.sets_of_superset h $ by simp {contextual := tt}⟩,
    begin
      simp [topological_space.coinduced, u.is_open_uniformity, uniformity, forall_quotient_iff],
      exact ⟨λh a ha, (this a ha).mp $ h a ha, λh a ha, (this a ha).mpr $ h a ha⟩
    end }

lemma uniformity_quotient :
  𝓤 (quotient (separation_setoid α)) = (𝓤 α).map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) :=
rfl

lemma uniform_continuous_quotient_mk :
  uniform_continuous (quotient.mk : α → quotient (separation_setoid α)) :=
le_refl _

lemma uniform_continuous_quotient {f : quotient (separation_setoid α) → β}
  (hf : uniform_continuous (λx, f ⟦x⟧)) : uniform_continuous f :=
hf

lemma uniform_continuous_quotient_lift
  {f : α → β} {h : ∀a b, (a, b) ∈ 𝓢 α → f a = f b}
  (hf : uniform_continuous f) : uniform_continuous (λa, quotient.lift f h a) :=
uniform_continuous_quotient hf

lemma uniform_continuous_quotient_lift₂
  {f : α → β → γ} {h : ∀a c b d, (a, b) ∈ 𝓢 α → (c, d) ∈ 𝓢 β → f a c = f b d}
  (hf : uniform_continuous (λp:α×β, f p.1 p.2)) :
  uniform_continuous (λp:_×_, quotient.lift₂ f h p.1 p.2) :=
begin
  rw [uniform_continuous, uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient,
    filter.prod_map_map_eq, filter.tendsto_map'_iff, filter.tendsto_map'_iff],
  rwa [uniform_continuous, uniformity_prod_eq_prod, filter.tendsto_map'_iff] at hf
end

lemma comap_quotient_le_uniformity :
  (𝓤 $ quotient $ separation_setoid α).comap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) ≤ (𝓤 α) :=
assume t' ht',
let ⟨t, ht, tt_t'⟩ := comp_mem_uniformity_sets ht' in
let ⟨s, hs, ss_t⟩ := comp_mem_uniformity_sets ht in
⟨(λp:α×α, (⟦p.1⟧, ⟦p.2⟧)) '' s,
  (𝓤 α).sets_of_superset hs $ assume x hx, ⟨x, hx, rfl⟩,
  assume ⟨a₁, a₂⟩ ⟨⟨b₁, b₂⟩, hb, ab_eq⟩,
  have ⟦b₁⟧ = ⟦a₁⟧ ∧ ⟦b₂⟧ = ⟦a₂⟧, from prod.mk.inj ab_eq,
  have b₁ ≈ a₁ ∧ b₂ ≈ a₂, from and.imp quotient.exact quotient.exact this,
  have ab₁ : (a₁, b₁) ∈ t, from (setoid.symm this.left) t ht,
  have ba₂ : (b₂, a₂) ∈ s, from this.right s hs,
  tt_t' ⟨b₁, show ((a₁, a₂).1, b₁) ∈ t, from ab₁,
    ss_t ⟨b₂, show ((b₁, a₂).1, b₂) ∈ s, from hb, ba₂⟩⟩⟩

lemma comap_quotient_eq_uniformity :
  (𝓤 $ quotient $ separation_setoid α).comap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) = 𝓤 α :=
le_antisymm comap_quotient_le_uniformity le_comap_map


instance separated_separation : separated_space (quotient (separation_setoid α)) :=
⟨set.ext $ assume ⟨a, b⟩, quotient.induction_on₂ a b $ assume a b,
  ⟨assume h,
    have a ≈ b, from assume s hs,
      have s ∈ (𝓤 $ quotient $ separation_setoid α).comap (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)),
        from comap_quotient_le_uniformity hs,
      let ⟨t, ht, hts⟩ := this in
      hts begin dsimp [preimage], exact h t ht end,
    show ⟦a⟧ = ⟦b⟧, from quotient.sound this,

  assume heq : ⟦a⟧ = ⟦b⟧, assume h hs,
  heq ▸ refl_mem_uniformity hs⟩⟩

lemma separated_of_uniform_continuous {f : α → β} {x y : α}
  (H : uniform_continuous f) (h : x ≈ y) : f x ≈ f y :=
assume _ h', h _ (H h')

lemma eq_of_separated_of_uniform_continuous [separated_space β] {f : α → β} {x y : α}
  (H : uniform_continuous f) (h : x ≈ y) : f x = f y :=
separated_def.1 (by apply_instance) _ _ $ separated_of_uniform_continuous H h

/-- The maximal separated quotient of a uniform space `α`. -/
def separation_quotient (α : Type*) [uniform_space α] := quotient (separation_setoid α)

namespace separation_quotient
instance : uniform_space (separation_quotient α) := by dunfold separation_quotient ; apply_instance
instance : separated_space (separation_quotient α) :=
  by dunfold separation_quotient ; apply_instance
instance [inhabited α] : inhabited (separation_quotient α) :=
by unfold separation_quotient; apply_instance

/-- Factoring functions to a separated space through the separation quotient. -/
def lift [separated_space β] (f : α → β) : (separation_quotient α → β) :=
if h : uniform_continuous f then
  quotient.lift f (λ x y, eq_of_separated_of_uniform_continuous h)
else
  λ x, f (nonempty.some ⟨x.out⟩)

lemma lift_mk [separated_space β] {f : α → β} (h : uniform_continuous f) (a : α) :
  lift f ⟦a⟧ = f a :=
by rw [lift, dif_pos h]; refl

lemma uniform_continuous_lift [separated_space β] (f : α → β) : uniform_continuous (lift f) :=
begin
  by_cases hf : uniform_continuous f,
  { rw [lift, dif_pos hf], exact uniform_continuous_quotient_lift hf },
  { rw [lift, dif_neg hf], exact uniform_continuous_of_const (assume a b, rfl) }
end

/-- The separation quotient functor acting on functions. -/
def map (f : α → β) : separation_quotient α → separation_quotient β :=
lift (quotient.mk ∘ f)

lemma map_mk {f : α → β} (h : uniform_continuous f) (a : α) : map f ⟦a⟧ = ⟦f a⟧ :=
by rw [map, lift_mk (uniform_continuous_quotient_mk.comp h)]

lemma uniform_continuous_map (f : α → β) : uniform_continuous (map f) :=
uniform_continuous_lift (quotient.mk ∘ f)

lemma map_unique {f : α → β} (hf : uniform_continuous f)
  {g : separation_quotient α → separation_quotient β}
  (comm : quotient.mk ∘ f = g ∘ quotient.mk) : map f = g :=
by ext ⟨a⟩;
calc map f ⟦a⟧ = ⟦f a⟧ : map_mk hf a
  ... = g ⟦a⟧ : congr_fun comm a

lemma map_id : map (@id α) = id :=
map_unique uniform_continuous_id rfl

lemma map_comp {f : α → β} {g : β → γ} (hf : uniform_continuous f) (hg : uniform_continuous g) :
  map g ∘ map f = map (g ∘ f) :=
(map_unique (hg.comp hf) $ by simp only [(∘), map_mk, hf, hg]).symm

end separation_quotient

lemma separation_prod {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) ≈ (a₂, b₂) ↔ a₁ ≈ a₂ ∧ b₁ ≈ b₂ :=
begin
  split,
  { assume h,
    exact ⟨separated_of_uniform_continuous uniform_continuous_fst h,
           separated_of_uniform_continuous uniform_continuous_snd h⟩ },
  { rintros ⟨eqv_α, eqv_β⟩ r r_in,
    rw uniformity_prod at r_in,
    rcases r_in with ⟨t_α, ⟨r_α, r_α_in, h_α⟩, t_β, ⟨r_β, r_β_in, h_β⟩, H⟩,

    let p_α := λ(p : (α × β) × (α × β)), (p.1.1, p.2.1),
    let p_β := λ(p : (α × β) × (α × β)), (p.1.2, p.2.2),
    have key_α : p_α ((a₁, b₁), (a₂, b₂)) ∈ r_α, { simp [p_α, eqv_α r_α r_α_in] },
    have key_β : p_β ((a₁, b₁), (a₂, b₂)) ∈ r_β, { simp [p_β, eqv_β r_β r_β_in] },
    exact H ⟨h_α key_α, h_β key_β⟩ },
end

instance separated.prod [separated_space α] [separated_space β] : separated_space (α × β) :=
separated_def.2 $ assume x y H, prod.ext
  (eq_of_separated_of_uniform_continuous uniform_continuous_fst H)
  (eq_of_separated_of_uniform_continuous uniform_continuous_snd H)
end uniform_space
