/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import topology.uniform_space.abstract_completion

/-!
# Hausdorff completions of uniform spaces

The goal is to construct a left-adjoint to the inclusion of complete Hausdorff uniform spaces
into all uniform spaces. Any uniform space `α` gets a completion `completion α` and a morphism
(ie. uniformly continuous map) `coe : α → completion α` which solves the universal
mapping problem of factorizing morphisms from `α` to any complete Hausdorff uniform space `β`.
It means any uniformly continuous `f : α → β` gives rise to a unique morphism
`completion.extension f : completion α → β` such that `f = completion.extension f ∘ coe`.
Actually `completion.extension f` is defined for all maps from `α` to `β` but it has the desired
properties only if `f` is uniformly continuous.

Beware that `coe` is not injective if `α` is not Hausdorff. But its image is always
dense. The adjoint functor acting on morphisms is then constructed by the usual abstract nonsense.
For every uniform spaces `α` and `β`, it turns `f : α → β` into a morphism
  `completion.map f : completion α → completion β`
such that
  `coe ∘ f = (completion.map f) ∘ coe`
provided `f` is uniformly continuous. This construction is compatible with composition.

In this file we introduce the following concepts:

* `Cauchy α` the uniform completion of the uniform space `α` (using Cauchy filters). These are not
  minimal filters.

* `completion α := quotient (separation_setoid (Cauchy α))` the Hausdorff completion.

## References

This formalization is mostly based on
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
From a slightly different perspective in order to reuse material in topology.uniform_space.basic.
-/

noncomputable theory
open filter set
universes u v w x

open_locale uniformity classical topological_space filter

/-- Space of Cauchy filters

This is essentially the completion of a uniform space. The embeddings are the neighbourhood filters.
This space is not minimal, the separated uniform space (i.e. quotiented on the intersection of all
entourages) is necessary for this.
-/
def Cauchy (α : Type u) [uniform_space α] : Type u := { f : filter α // cauchy f }

namespace Cauchy

section
parameters {α : Type u} [uniform_space α]
variables {β : Type v} {γ : Type w}
variables [uniform_space β] [uniform_space γ]

def gen (s : set (α × α)) : set (Cauchy α × Cauchy α) :=
{p | s ∈ p.1.val ×ᶠ p.2.val }

lemma monotone_gen : monotone gen :=
monotone_set_of $ assume p, @monotone_mem_sets (α×α) (p.1.val ×ᶠ p.2.val)

private lemma symm_gen : map prod.swap ((𝓤 α).lift' gen) ≤ (𝓤 α).lift' gen :=
calc map prod.swap ((𝓤 α).lift' gen) =
  (𝓤 α).lift' (λs:set (α×α), {p | s ∈ p.2.val ×ᶠ p.1.val }) :
  begin
    delta gen,
    simp [map_lift'_eq, monotone_set_of, monotone_mem_sets,
          function.comp, image_swap_eq_preimage_swap, -subtype.val_eq_coe]
  end
  ... ≤ (𝓤 α).lift' gen :
    uniformity_lift_le_swap
      (monotone_principal.comp (monotone_set_of $ assume p,
        @monotone_mem_sets (α×α) (p.2.val ×ᶠ  p.1.val)))
      begin
        have h := λ(p:Cauchy α×Cauchy α), @filter.prod_comm _ _ (p.2.val) (p.1.val),
        simp [function.comp, h, -subtype.val_eq_coe],
        exact le_refl _
      end

private lemma comp_rel_gen_gen_subset_gen_comp_rel {s t : set (α×α)} : comp_rel (gen s) (gen t) ⊆
  (gen (comp_rel s t) : set (Cauchy α × Cauchy α)) :=
assume ⟨f, g⟩ ⟨h, h₁, h₂⟩,
let ⟨t₁, (ht₁ : t₁ ∈ f.val), t₂, (ht₂ : t₂ ∈ h.val), (h₁ : set.prod t₁ t₂ ⊆ s)⟩ :=
  mem_prod_iff.mp h₁ in
let ⟨t₃, (ht₃ : t₃ ∈ h.val), t₄, (ht₄ : t₄ ∈ g.val), (h₂ : set.prod t₃ t₄ ⊆ t)⟩ :=
  mem_prod_iff.mp h₂ in
have t₂ ∩ t₃ ∈ h.val,
  from inter_mem_sets ht₂ ht₃,
let ⟨x, xt₂, xt₃⟩ :=
  h.property.left.nonempty_of_mem this in
(f.val ×ᶠ g.val).sets_of_superset
  (prod_mem_prod ht₁ ht₄)
  (assume ⟨a, b⟩ ⟨(ha : a ∈ t₁), (hb : b ∈ t₄)⟩,
    ⟨x,
      h₁ (show (a, x) ∈ set.prod t₁ t₂, from ⟨ha, xt₂⟩),
      h₂ (show (x, b) ∈ set.prod t₃ t₄, from ⟨xt₃, hb⟩)⟩)

private lemma comp_gen :
  ((𝓤 α).lift' gen).lift' (λs, comp_rel s s) ≤ (𝓤 α).lift' gen :=
calc ((𝓤 α).lift' gen).lift' (λs, comp_rel s s) =
    (𝓤 α).lift' (λs, comp_rel (gen s) (gen s)) :
  begin
    rw [lift'_lift'_assoc],
    exact monotone_gen,
    exact (monotone_comp_rel monotone_id monotone_id)
  end
  ... ≤ (𝓤 α).lift' (λs, gen $ comp_rel s s) :
    lift'_mono' $ assume s hs, comp_rel_gen_gen_subset_gen_comp_rel
  ... = ((𝓤 α).lift' $ λs:set(α×α), comp_rel s s).lift' gen :
  begin
    rw [lift'_lift'_assoc],
    exact (monotone_comp_rel monotone_id monotone_id),
    exact monotone_gen
  end
  ... ≤ (𝓤 α).lift' gen : lift'_mono comp_le_uniformity (le_refl _)

instance : uniform_space (Cauchy α) :=
uniform_space.of_core
{ uniformity  := (𝓤 α).lift' gen,
  refl        := principal_le_lift' $ assume s hs ⟨a, b⟩ (a_eq_b : a = b),
    a_eq_b ▸ a.property.right hs,
  symm        := symm_gen,
  comp        := comp_gen }

theorem mem_uniformity {s : set (Cauchy α × Cauchy α)} :
  s ∈ 𝓤 (Cauchy α) ↔ ∃ t ∈ 𝓤 α, gen t ⊆ s :=
mem_lift'_sets monotone_gen

theorem mem_uniformity' {s : set (Cauchy α × Cauchy α)} :
  s ∈ 𝓤 (Cauchy α) ↔ ∃ t ∈ 𝓤 α, ∀ f g : Cauchy α, t ∈ f.1 ×ᶠ g.1 → (f, g) ∈ s :=
mem_uniformity.trans $ bex_congr $ λ t h, prod.forall

/-- Embedding of `α` into its completion `Cauchy α` -/
def pure_cauchy (a : α) : Cauchy α :=
⟨pure a, cauchy_pure⟩

lemma uniform_inducing_pure_cauchy : uniform_inducing (pure_cauchy : α → Cauchy α) :=
⟨have (preimage (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) ∘ gen) = id,
      from funext $ assume s, set.ext $ assume ⟨a₁, a₂⟩,
        by simp [preimage, gen, pure_cauchy, prod_principal_principal],
    calc comap (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) ((𝓤 α).lift' gen)
          = (𝓤 α).lift'
              (preimage (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) ∘ gen) :
        comap_lift'_eq monotone_gen
      ... = 𝓤 α : by simp [this]⟩

lemma uniform_embedding_pure_cauchy : uniform_embedding (pure_cauchy : α → Cauchy α) :=
{ inj := assume a₁ a₂ h, pure_injective $ subtype.ext_iff_val.1 h,
  ..uniform_inducing_pure_cauchy }

lemma dense_range_pure_cauchy : dense_range pure_cauchy :=
assume f,
have h_ex : ∀ s ∈ 𝓤 (Cauchy α), ∃y:α, (f, pure_cauchy y) ∈ s, from
  assume s hs,
  let ⟨t'', ht''₁, (ht''₂ : gen t'' ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs in
  let ⟨t', ht'₁, ht'₂⟩ := comp_mem_uniformity_sets ht''₁ in
  have t' ∈ f.val ×ᶠ f.val,
    from f.property.right ht'₁,
  let ⟨t, ht, (h : set.prod t t ⊆ t')⟩ := mem_prod_same_iff.mp this in
  let ⟨x, (hx : x ∈ t)⟩ := f.property.left.nonempty_of_mem ht in
  have t'' ∈ f.val ×ᶠ pure x,
    from mem_prod_iff.mpr ⟨t, ht, {y:α | (x, y) ∈ t'},
      h $ mk_mem_prod hx hx,
      assume ⟨a, b⟩ ⟨(h₁ : a ∈ t), (h₂ : (x, b) ∈ t')⟩,
        ht'₂ $ prod_mk_mem_comp_rel (@h (a, x) ⟨h₁, hx⟩) h₂⟩,
  ⟨x, ht''₂ $ by dsimp [gen]; exact this⟩,
begin
  simp only [closure_eq_cluster_pts, cluster_pt, nhds_eq_uniformity, lift'_inf_principal_eq,
    set.inter_comm _ (range pure_cauchy), mem_set_of_eq],
  exact (lift'_ne_bot_iff $ by exact monotone_inter monotone_const monotone_preimage).mpr
    (assume s hs,
      let ⟨y, hy⟩ := h_ex s hs in
      have pure_cauchy y ∈ range pure_cauchy ∩ {y : Cauchy α | (f, y) ∈ s},
        from ⟨mem_range_self y, hy⟩,
      ⟨_, this⟩)
end

lemma dense_inducing_pure_cauchy : dense_inducing pure_cauchy :=
uniform_inducing_pure_cauchy.dense_inducing dense_range_pure_cauchy

lemma dense_embedding_pure_cauchy : dense_embedding pure_cauchy :=
uniform_embedding_pure_cauchy.dense_embedding dense_range_pure_cauchy

lemma nonempty_Cauchy_iff : nonempty (Cauchy α) ↔ nonempty α :=
begin
  split ; rintro ⟨c⟩,
  { have := eq_univ_iff_forall.1 dense_embedding_pure_cauchy.to_dense_inducing.closure_range c,
    obtain ⟨_, ⟨_, a, _⟩⟩ := mem_closure_iff.1 this _ is_open_univ trivial,
    exact ⟨a⟩ },
  { exact ⟨pure_cauchy c⟩ }
end

section
set_option eqn_compiler.zeta true
instance : complete_space (Cauchy α) :=
complete_space_extension
  uniform_inducing_pure_cauchy
  dense_range_pure_cauchy $
  assume f hf,
  let f' : Cauchy α := ⟨f, hf⟩ in
  have map pure_cauchy f ≤ (𝓤 $ Cauchy α).lift' (preimage (prod.mk f')),
    from le_lift' $ assume s hs,
    let ⟨t, ht₁, (ht₂ : gen t ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs in
    let ⟨t', ht', (h : set.prod t' t' ⊆ t)⟩ := mem_prod_same_iff.mp (hf.right ht₁) in
    have t' ⊆ { y : α | (f', pure_cauchy y) ∈ gen t },
      from assume x hx, (f ×ᶠ pure x).sets_of_superset (prod_mem_prod ht' hx) h,
    f.sets_of_superset ht' $ subset.trans this (preimage_mono ht₂),
  ⟨f', by simp [nhds_eq_uniformity]; assumption⟩
end

instance [inhabited α] : inhabited (Cauchy α) :=
⟨pure_cauchy $ default α⟩

instance [h : nonempty α] : nonempty (Cauchy α) :=
h.rec_on $ assume a, nonempty.intro $ Cauchy.pure_cauchy a

section extend

def extend (f : α → β) : (Cauchy α → β) :=
if uniform_continuous f then
  dense_inducing_pure_cauchy.extend f
else
  λ x, f (classical.inhabited_of_nonempty $ nonempty_Cauchy_iff.1 ⟨x⟩).default

variables [separated_space β]

lemma extend_pure_cauchy {f : α → β} (hf : uniform_continuous f) (a : α) :
  extend f (pure_cauchy a) = f a :=
begin
  rw [extend, if_pos hf],
  exact uniformly_extend_of_ind uniform_inducing_pure_cauchy dense_range_pure_cauchy hf _
end

variables [_root_.complete_space β]

lemma uniform_continuous_extend {f : α → β} : uniform_continuous (extend f) :=
begin
  by_cases hf : uniform_continuous f,
  { rw [extend, if_pos hf],
    exact uniform_continuous_uniformly_extend uniform_inducing_pure_cauchy
      dense_range_pure_cauchy hf },
  { rw [extend, if_neg hf],
    exact uniform_continuous_of_const (assume a b, by congr) }
end

end extend

end

theorem Cauchy_eq {α : Type*} [inhabited α] [uniform_space α] [complete_space α]
  [separated_space α] {f g : Cauchy α} :
  Lim f.1 = Lim g.1 ↔ (f, g) ∈ separation_rel (Cauchy α) :=
begin
  split,
  { intros e s hs,
    rcases Cauchy.mem_uniformity'.1 hs with ⟨t, tu, ts⟩,
    apply ts,
    rcases comp_mem_uniformity_sets tu with ⟨d, du, dt⟩,
    refine mem_prod_iff.2
      ⟨_, f.2.le_nhds_Lim (mem_nhds_right (Lim f.1) du),
       _, g.2.le_nhds_Lim (mem_nhds_left (Lim g.1) du), λ x h, _⟩,
    cases x with a b, cases h with h₁ h₂,
    rw ← e at h₂,
    exact dt ⟨_, h₁, h₂⟩ },
  { intros H,
    refine separated_def.1 (by apply_instance) _ _ (λ t tu, _),
    rcases mem_uniformity_is_closed tu with ⟨d, du, dc, dt⟩,
    refine H {p | (Lim p.1.1, Lim p.2.1) ∈ t}
      (Cauchy.mem_uniformity'.2 ⟨d, du, λ f g h, _⟩),
    rcases mem_prod_iff.1 h with ⟨x, xf, y, yg, h⟩,
    have limc : ∀ (f : Cauchy α) (x ∈ f.1), Lim f.1 ∈ closure x,
    { intros f x xf,
      rw closure_eq_cluster_pts,
      exact f.2.1.mono
        (le_inf f.2.le_nhds_Lim (le_principal_iff.2 xf)) },
    have := dc.closure_subset_iff.2 h,
    rw closure_prod_eq at this,
    refine dt (this ⟨_, _⟩); dsimp; apply limc; assumption }
end

section
local attribute [instance] uniform_space.separation_setoid

lemma separated_pure_cauchy_injective {α : Type*} [uniform_space α] [s : separated_space α] :
  function.injective (λa:α, ⟦pure_cauchy a⟧) | a b h :=
separated_def.1 s _ _ $ assume s hs,
let ⟨t, ht, hts⟩ :=
  by rw [← (@uniform_embedding_pure_cauchy α _).comap_uniformity, filter.mem_comap_sets] at hs;
    exact hs in
have (pure_cauchy a, pure_cauchy b) ∈ t, from quotient.exact h t ht,
@hts (a, b) this

end

end Cauchy

local attribute [instance] uniform_space.separation_setoid

open Cauchy set

namespace uniform_space
variables (α : Type*) [uniform_space α]
variables {β : Type*} [uniform_space β]
variables {γ : Type*} [uniform_space γ]

instance complete_space_separation [h : complete_space α] :
  complete_space (quotient (separation_setoid α)) :=
⟨assume f, assume hf : cauchy f,
  have cauchy (f.comap (λx, ⟦x⟧)), from
    hf.comap' comap_quotient_le_uniformity $ hf.left.comap_of_surj (surjective_quotient_mk _),
  let ⟨x, (hx : f.comap (λx, ⟦x⟧) ≤ 𝓝 x)⟩ := complete_space.complete this in
  ⟨⟦x⟧, (comap_le_comap_iff $ by simp).1
    (hx.trans $ map_le_iff_le_comap.1 continuous_quotient_mk.continuous_at)⟩⟩

/-- Hausdorff completion of `α` -/
def completion := quotient (separation_setoid $ Cauchy α)

namespace completion

instance [inhabited α] : inhabited (completion α) :=
by unfold completion; apply_instance

@[priority 50]
instance : uniform_space (completion α) := by dunfold completion ; apply_instance

instance : complete_space (completion α) := by dunfold completion ; apply_instance

instance : separated_space (completion α) := by dunfold completion ; apply_instance

instance : regular_space (completion α) := separated_regular

/-- Automatic coercion from `α` to its completion. Not always injective. -/
instance : has_coe_t α (completion α) := ⟨quotient.mk ∘ pure_cauchy⟩ -- note [use has_coe_t]

protected lemma coe_eq : (coe : α → completion α) = quotient.mk ∘ pure_cauchy := rfl

lemma comap_coe_eq_uniformity :
  (𝓤 _).comap (λ(p:α×α), ((p.1 : completion α), (p.2 : completion α))) = 𝓤 α :=
begin
  have : (λx:α×α, ((x.1 : completion α), (x.2 : completion α))) =
    (λx:(Cauchy α)×(Cauchy α), (⟦x.1⟧, ⟦x.2⟧)) ∘ (λx:α×α, (pure_cauchy x.1, pure_cauchy x.2)),
  { ext ⟨a, b⟩; simp; refl },
  rw [this, ← filter.comap_comap],
  change filter.comap _ (filter.comap _ (𝓤 $ quotient $ separation_setoid $ Cauchy α)) = 𝓤 α,
  rw [comap_quotient_eq_uniformity, uniform_embedding_pure_cauchy.comap_uniformity]
end

lemma uniform_inducing_coe : uniform_inducing  (coe : α → completion α) :=
⟨comap_coe_eq_uniformity α⟩

variables {α}

lemma dense_range_coe : dense_range (coe : α → completion α) :=
dense_range_pure_cauchy.quotient

variables (α)

def cpkg {α : Type*} [uniform_space α] : abstract_completion α :=
{ space := completion α,
  coe := coe,
  uniform_struct := by apply_instance,
  complete := by apply_instance,
  separation := by apply_instance,
  uniform_inducing := completion.uniform_inducing_coe α,
  dense := completion.dense_range_coe }

instance abstract_completion.inhabited : inhabited (abstract_completion α) :=
⟨cpkg⟩

local attribute [instance]
abstract_completion.uniform_struct abstract_completion.complete abstract_completion.separation

lemma nonempty_completion_iff : nonempty (completion α) ↔ nonempty α :=
cpkg.dense.nonempty_iff.symm

lemma uniform_continuous_coe : uniform_continuous (coe : α → completion α) :=
cpkg.uniform_continuous_coe

lemma continuous_coe : continuous (coe : α → completion α) :=
cpkg.continuous_coe

lemma uniform_embedding_coe [separated_space α] : uniform_embedding  (coe : α → completion α) :=
{ comap_uniformity := comap_coe_eq_uniformity α,
  inj := separated_pure_cauchy_injective }

variable {α}

lemma dense_inducing_coe : dense_inducing (coe : α → completion α) :=
{ dense := dense_range_coe,
  ..(uniform_inducing_coe α).inducing }

open topological_space

instance separable_space_completion [separable_space α] : separable_space (completion α) :=
completion.dense_inducing_coe.separable_space

lemma dense_embedding_coe [separated_space α]: dense_embedding (coe : α → completion α) :=
{ inj := separated_pure_cauchy_injective,
  ..dense_inducing_coe }

lemma dense_range_coe₂ :
  dense_range (λx:α × β, ((x.1 : completion α), (x.2 : completion β))) :=
dense_range_coe.prod_map dense_range_coe

lemma dense_range_coe₃ :
  dense_range (λx:α × (β × γ),
    ((x.1 : completion α), ((x.2.1 : completion β), (x.2.2 : completion γ)))) :=
dense_range_coe.prod_map dense_range_coe₂

@[elab_as_eliminator]
lemma induction_on {p : completion α → Prop}
  (a : completion α) (hp : is_closed {a | p a}) (ih : ∀a:α, p a) : p a :=
is_closed_property dense_range_coe hp ih a

@[elab_as_eliminator]
lemma induction_on₂ {p : completion α → completion β → Prop}
  (a : completion α) (b : completion β)
  (hp : is_closed {x : completion α × completion β | p x.1 x.2})
  (ih : ∀(a:α) (b:β), p a b) : p a b :=
have ∀x : completion α × completion β, p x.1 x.2, from
  is_closed_property dense_range_coe₂ hp $ assume ⟨a, b⟩, ih a b,
this (a, b)

@[elab_as_eliminator]
lemma induction_on₃ {p : completion α → completion β → completion γ → Prop}
  (a : completion α) (b : completion β) (c : completion γ)
  (hp : is_closed {x : completion α × completion β × completion γ | p x.1 x.2.1 x.2.2})
  (ih : ∀(a:α) (b:β) (c:γ), p a b c) : p a b c :=
have ∀x : completion α × completion β × completion γ, p x.1 x.2.1 x.2.2, from
  is_closed_property dense_range_coe₃ hp $ assume ⟨a, b, c⟩, ih a b c,
this (a, b, c)

lemma ext [t2_space β] {f g : completion α → β} (hf : continuous f) (hg : continuous g)
  (h : ∀a:α, f a = g a) : f = g :=
cpkg.funext hf hg h

section extension
variables {f : α → β}

/-- "Extension" to the completion. It is defined for any map `f` but
returns an arbitrary constant value if `f` is not uniformly continuous -/
protected def extension (f : α → β) : completion α → β :=
cpkg.extend f

variables [separated_space β]

@[simp]lemma extension_coe (hf : uniform_continuous f) (a : α) :
  (completion.extension f) a = f a :=
cpkg.extend_coe hf a

variables [complete_space β]

lemma uniform_continuous_extension : uniform_continuous (completion.extension f) :=
cpkg.uniform_continuous_extend

lemma continuous_extension : continuous (completion.extension f) :=
cpkg.continuous_extend

lemma extension_unique (hf : uniform_continuous f) {g : completion α → β}
  (hg : uniform_continuous g) (h : ∀ a : α, f a = g (a : completion α)) :
  completion.extension f = g :=
cpkg.extend_unique hf hg h

@[simp] lemma extension_comp_coe {f : completion α → β} (hf : uniform_continuous f) :
  completion.extension (f ∘ coe) = f :=
cpkg.extend_comp_coe hf
end extension

section map
variables {f : α → β}

/-- Completion functor acting on morphisms -/
protected def map (f : α → β) : completion α → completion β :=
cpkg.map cpkg f

lemma uniform_continuous_map : uniform_continuous (completion.map f) :=
cpkg.uniform_continuous_map cpkg f

lemma continuous_map : continuous (completion.map f) :=
cpkg.continuous_map cpkg f

@[simp] lemma map_coe (hf : uniform_continuous f) (a : α) : (completion.map f) a = f a :=
cpkg.map_coe cpkg hf a

lemma map_unique {f : α → β} {g : completion α → completion β}
  (hg : uniform_continuous g) (h : ∀a:α, ↑(f a) = g a) : completion.map f = g :=
cpkg.map_unique cpkg hg h

@[simp] lemma map_id : completion.map (@id α) = id :=
cpkg.map_id

lemma extension_map [complete_space γ] [separated_space γ] {f : β → γ} {g : α → β}
  (hf : uniform_continuous f) (hg : uniform_continuous g) :
  completion.extension f ∘ completion.map g = completion.extension (f ∘ g) :=
completion.ext (continuous_extension.comp continuous_map) continuous_extension $
  by intro a; simp only [hg, hf, hf.comp hg, (∘), map_coe, extension_coe]

lemma map_comp {g : β → γ} {f : α → β} (hg : uniform_continuous g) (hf : uniform_continuous f) :
  completion.map g ∘ completion.map f = completion.map (g ∘ f) :=
extension_map ((uniform_continuous_coe _).comp hg) hf

end map

/- In this section we construct isomorphisms between the completion of a uniform space and the
completion of its separation quotient -/
section separation_quotient_completion

def completion_separation_quotient_equiv (α : Type u) [uniform_space α] :
  completion (separation_quotient α) ≃ completion α :=
begin
  refine ⟨completion.extension (separation_quotient.lift (coe : α → completion α)),
    completion.map quotient.mk, _, _⟩,
  { assume a,
    refine induction_on a (is_closed_eq (continuous_map.comp continuous_extension) continuous_id) _,
    rintros ⟨a⟩,
    show completion.map quotient.mk
      (completion.extension (separation_quotient.lift coe) ↑⟦a⟧) = ↑⟦a⟧,
    rw [extension_coe (separation_quotient.uniform_continuous_lift _),
      separation_quotient.lift_mk (uniform_continuous_coe α),
      completion.map_coe uniform_continuous_quotient_mk] ; apply_instance },
  { assume a,
    refine completion.induction_on a
      (is_closed_eq (continuous_extension.comp continuous_map) continuous_id) (λ a, _),
    rw [map_coe uniform_continuous_quotient_mk,
      extension_coe (separation_quotient.uniform_continuous_lift _),
      separation_quotient.lift_mk (uniform_continuous_coe α) _] ; apply_instance }
end

lemma uniform_continuous_completion_separation_quotient_equiv :
  uniform_continuous ⇑(completion_separation_quotient_equiv α) :=
uniform_continuous_extension

lemma uniform_continuous_completion_separation_quotient_equiv_symm :
  uniform_continuous ⇑(completion_separation_quotient_equiv α).symm :=
uniform_continuous_map

end separation_quotient_completion

section extension₂
variables (f : α → β → γ)
open function

protected def extension₂ (f : α → β → γ) : completion α → completion β → γ :=
cpkg.extend₂ cpkg f

variables [separated_space γ] {f}

@[simp] lemma extension₂_coe_coe (hf : uniform_continuous₂ f) (a : α) (b : β) :
  completion.extension₂ f a b = f a b :=
cpkg.extension₂_coe_coe cpkg hf a b

variables [complete_space γ] (f)

lemma uniform_continuous_extension₂ : uniform_continuous₂ (completion.extension₂ f) :=
cpkg.uniform_continuous_extension₂ cpkg f

end extension₂

section map₂
open function

protected def map₂ (f : α → β → γ) : completion α → completion β → completion γ :=
cpkg.map₂ cpkg cpkg f

lemma uniform_continuous_map₂ (f : α → β → γ) : uniform_continuous₂ (completion.map₂ f) :=
cpkg.uniform_continuous_map₂ cpkg cpkg f

lemma continuous_map₂ {δ} [topological_space δ] {f : α → β → γ}
  {a : δ → completion α} {b : δ → completion β} (ha : continuous a) (hb : continuous b) :
  continuous (λd:δ, completion.map₂ f (a d) (b d)) :=
cpkg.continuous_map₂ cpkg cpkg ha hb

lemma map₂_coe_coe (a : α) (b : β) (f : α → β → γ) (hf : uniform_continuous₂ f) :
  completion.map₂ f (a : completion α) (b : completion β) = f a b :=
cpkg.map₂_coe_coe cpkg cpkg a b f hf

end map₂
end completion
end uniform_space
