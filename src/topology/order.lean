/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.tactic

/-!
# Ordering on topologies and (co)induced topologies

Topologies on a fixed type `α` are ordered, by reverse inclusion.
That is, for topologies `t₁` and `t₂` on `α`, we write `t₁ ≤ t₂`
if every set open in `t₂` is also open in `t₁`.
(One also calls `t₁` finer than `t₂`, and `t₂` coarser than `t₁`.)

Any function `f : α → β` induces
       `induced f : topological_space β → topological_space α`
and  `coinduced f : topological_space α → topological_space β`.
Continuity, the ordering on topologies and (co)induced topologies are
related as follows:
* The identity map (α, t₁) → (α, t₂) is continuous iff t₁ ≤ t₂.
* A map f : (α, t) → (β, u) is continuous
    iff             t ≤ induced f u   (`continuous_iff_le_induced`)
    iff coinduced f t ≤ u             (`continuous_iff_coinduced_le`).

Topologies on α form a complete lattice, with ⊥ the discrete topology
and ⊤ the indiscrete topology.

For a function f : α → β, (coinduced f, induced f) is a Galois connection
between topologies on α and topologies on β.

## Implementation notes

There is a Galois insertion between topologies on α (with the inclusion ordering)
and all collections of sets in α. The complete lattice structure on topologies
on α is defined as the reverse of the one obtained via this Galois insertion.

## Tags

finer, coarser, induced topology, coinduced topology

-/

open set filter classical
open_locale classical topological_space filter

universes u v w

namespace topological_space
variables {α : Type u}

/-- The open sets of the least topology containing a collection of basic sets. -/
inductive generate_open (g : set (set α)) : set α → Prop
| basic  : ∀s∈g, generate_open s
| univ   : generate_open univ
| inter  : ∀s t, generate_open s → generate_open t → generate_open (s ∩ t)
| sUnion : ∀k, (∀s∈k, generate_open s) → generate_open (⋃₀ k)

/-- The smallest topological space containing the collection `g` of basic sets -/
def generate_from (g : set (set α)) : topological_space α :=
{ is_open        := generate_open g,
  is_open_univ   := generate_open.univ,
  is_open_inter  := generate_open.inter,
  is_open_sUnion := generate_open.sUnion  }

lemma nhds_generate_from {g : set (set α)} {a : α} :
  @nhds α (generate_from g) a = (⨅s∈{s | a ∈ s ∧ s ∈ g}, 𝓟 s) :=
by rw nhds_def; exact le_antisymm
  (infi_le_infi $ assume s, infi_le_infi_const $ assume ⟨as, sg⟩, ⟨as, generate_open.basic _ sg⟩)
  (le_infi $ assume s, le_infi $ assume ⟨as, hs⟩,
    begin
      revert as, clear_, induction hs,
      case generate_open.basic : s hs
      { exact assume as, infi_le_of_le s $ infi_le _ ⟨as, hs⟩ },
      case generate_open.univ
      { rw [principal_univ],
        exact assume _, le_top },
      case generate_open.inter : s t hs' ht' hs ht
      { exact assume ⟨has, hat⟩, calc _ ≤ 𝓟 s ⊓ 𝓟 t : le_inf (hs has) (ht hat)
          ... = _ : inf_principal },
      case generate_open.sUnion : k hk' hk
      { exact λ ⟨t, htk, hat⟩, calc _ ≤ 𝓟 t : hk t htk hat
          ... ≤ _ : le_principal_iff.2 $ subset_sUnion_of_mem htk }
    end)

lemma tendsto_nhds_generate_from {β : Type*} {m : α → β} {f : filter α} {g : set (set β)} {b : β}
  (h : ∀s∈g, b ∈ s → m ⁻¹' s ∈ f) : tendsto m f (@nhds β (generate_from g) b) :=
by rw [nhds_generate_from]; exact
  (tendsto_infi.2 $ assume s, tendsto_infi.2 $ assume ⟨hbs, hsg⟩, tendsto_principal.2 $ h s hsg hbs)

/-- Construct a topology on α given the filter of neighborhoods of each point of α. -/
protected def mk_of_nhds (n : α → filter α) : topological_space α :=
{ is_open        := λs, ∀a∈s, s ∈ n a,
  is_open_univ   := assume x h, univ_mem_sets,
  is_open_inter  := assume s t hs ht x ⟨hxs, hxt⟩, inter_mem_sets (hs x hxs) (ht x hxt),
  is_open_sUnion := assume s hs a ⟨x, hx, hxa⟩,
    mem_sets_of_superset (hs x hx _ hxa) (set.subset_sUnion_of_mem hx) }

lemma nhds_mk_of_nhds (n : α → filter α) (a : α)
  (h₀ : pure ≤ n) (h₁ : ∀{a s}, s ∈ n a → ∃ t ∈ n a, t ⊆ s ∧ ∀a' ∈ t, s ∈ n a') :
  @nhds α (topological_space.mk_of_nhds n) a = n a :=
begin
  letI := topological_space.mk_of_nhds n,
  refine le_antisymm (assume s hs, _) (assume s hs, _),
  { have h₀ : {b | s ∈ n b} ⊆ s := assume b hb, mem_pure_sets.1 $ h₀ b hb,
    have h₁ : {b | s ∈ n b} ∈ 𝓝 a,
    { refine is_open.mem_nhds (assume b (hb : s ∈ n b), _) hs,
      rcases h₁ hb with ⟨t, ht, hts, h⟩,
      exact mem_sets_of_superset ht h },
    exact mem_sets_of_superset h₁ h₀ },
  { rcases (@mem_nhds_iff α (topological_space.mk_of_nhds n) _ _).1 hs with ⟨t, hts, ht, hat⟩,
    exact (n a).sets_of_superset (ht _ hat) hts },
end

end topological_space

section lattice

variables {α : Type u} {β : Type v}

/-- The inclusion ordering on topologies on α. We use it to get a complete
   lattice instance via the Galois insertion method, but the partial order
   that we will eventually impose on `topological_space α` is the reverse one. -/
def tmp_order : partial_order (topological_space α) :=
{ le          := λt s, t.is_open ≤ s.is_open,
  le_antisymm := assume t s h₁ h₂, topological_space_eq $ le_antisymm h₁ h₂,
  le_refl     := assume t, le_refl t.is_open,
  le_trans    := assume a b c h₁ h₂, @le_trans _ _ a.is_open b.is_open c.is_open h₁ h₂ }

local attribute [instance] tmp_order

/- We'll later restate this lemma in terms of the correct order on `topological_space α`. -/
private lemma generate_from_le_iff_subset_is_open {g : set (set α)} {t : topological_space α} :
  topological_space.generate_from g ≤ t ↔ g ⊆ {s | t.is_open s} :=
iff.intro
  (assume ht s hs, ht _ $ topological_space.generate_open.basic s hs)
  (assume hg s hs, hs.rec_on (assume v hv, hg hv)
    t.is_open_univ (assume u v _ _, t.is_open_inter u v) (assume k _, t.is_open_sUnion k))

/-- If `s` equals the collection of open sets in the topology it generates,
  then `s` defines a topology. -/
protected def mk_of_closure (s : set (set α))
  (hs : {u | (topological_space.generate_from s).is_open u} = s) : topological_space α :=
{ is_open        := λu, u ∈ s,
  is_open_univ   := hs ▸ topological_space.generate_open.univ,
  is_open_inter  := hs ▸ topological_space.generate_open.inter,
  is_open_sUnion := hs ▸ topological_space.generate_open.sUnion }

lemma mk_of_closure_sets {s : set (set α)}
  {hs : {u | (topological_space.generate_from s).is_open u} = s} :
  mk_of_closure s hs = topological_space.generate_from s :=
topological_space_eq hs.symm

/-- The Galois insertion between `set (set α)` and `topological_space α` whose lower part
  sends a collection of subsets of α to the topology they generate, and whose upper part
  sends a topology to its collection of open subsets. -/
def gi_generate_from (α : Type*) :
  galois_insertion topological_space.generate_from (λt:topological_space α, {s | t.is_open s}) :=
{ gc        := assume g t, generate_from_le_iff_subset_is_open,
  le_l_u    := assume ts s hs, topological_space.generate_open.basic s hs,
  choice    := λg hg, mk_of_closure g
    (subset.antisymm hg $ generate_from_le_iff_subset_is_open.1 $ le_refl _),
  choice_eq := assume s hs, mk_of_closure_sets }

lemma generate_from_mono {α} {g₁ g₂ : set (set α)} (h : g₁ ⊆ g₂) :
  topological_space.generate_from g₁ ≤ topological_space.generate_from g₂ :=
(gi_generate_from _).gc.monotone_l h

/-- The complete lattice of topological spaces, but built on the inclusion ordering. -/
def tmp_complete_lattice {α : Type u} : complete_lattice (topological_space α) :=
(gi_generate_from α).lift_complete_lattice

/-- The ordering on topologies on the type `α`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
instance : partial_order (topological_space α) :=
{ le          := λ t s, s.is_open ≤ t.is_open,
  le_antisymm := assume t s h₁ h₂, topological_space_eq $ le_antisymm h₂ h₁,
  le_refl     := assume t, le_refl t.is_open,
  le_trans    := assume a b c h₁ h₂, le_trans h₂ h₁ }

lemma le_generate_from_iff_subset_is_open {g : set (set α)} {t : topological_space α} :
  t ≤ topological_space.generate_from g ↔ g ⊆ {s | t.is_open s} :=
generate_from_le_iff_subset_is_open

/-- Topologies on `α` form a complete lattice, with `⊥` the discrete topology
  and `⊤` the indiscrete topology. The infimum of a collection of topologies
  is the topology generated by all their open sets, while the supremem is the
  topology whose open sets are those sets open in every member of the collection. -/
instance : complete_lattice (topological_space α) :=
@order_dual.complete_lattice _ tmp_complete_lattice

/-- A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`. -/
class discrete_topology (α : Type*) [t : topological_space α] : Prop :=
(eq_bot [] : t = ⊥)

@[priority 100]
instance discrete_topology_bot (α : Type*) : @discrete_topology α ⊥ :=
{ eq_bot := rfl }

@[simp] lemma is_open_discrete [topological_space α] [discrete_topology α] (s : set α) :
  is_open s :=
(discrete_topology.eq_bot α).symm ▸ trivial

@[simp] lemma is_closed_discrete [topological_space α] [discrete_topology α] (s : set α) :
  is_closed s :=
is_open_compl_iff.1 $ (discrete_topology.eq_bot α).symm ▸ trivial

lemma continuous_of_discrete_topology [topological_space α] [discrete_topology α]
  [topological_space β] {f : α → β} : continuous f :=
continuous_def.2 $ λs hs, is_open_discrete _

lemma nhds_bot (α : Type*) : (@nhds α ⊥) = pure :=
begin
  refine le_antisymm _ (@pure_le_nhds α ⊥),
  assume a s hs,
  exact @is_open.mem_nhds α ⊥ a s trivial hs
end

lemma nhds_discrete (α : Type*) [topological_space α] [discrete_topology α] : (@nhds α _) = pure :=
(discrete_topology.eq_bot α).symm ▸ nhds_bot α

lemma le_of_nhds_le_nhds {t₁ t₂ : topological_space α} (h : ∀x, @nhds α t₁ x ≤ @nhds α t₂ x) :
  t₁ ≤ t₂ :=
assume s, show @is_open α t₂ s → @is_open α t₁ s,
  by { simp only [is_open_iff_nhds, le_principal_iff],  exact assume hs a ha, h _ $ hs _ ha }

lemma eq_of_nhds_eq_nhds {t₁ t₂ : topological_space α} (h : ∀x, @nhds α t₁ x = @nhds α t₂ x) :
  t₁ = t₂ :=
le_antisymm
  (le_of_nhds_le_nhds $ assume x, le_of_eq $ h x)
  (le_of_nhds_le_nhds $ assume x, le_of_eq $ (h x).symm)

lemma eq_bot_of_singletons_open {t : topological_space α} (h : ∀ x, t.is_open {x}) : t = ⊥ :=
bot_unique $ λ s hs, bUnion_of_singleton s ▸ is_open_bUnion (λ x _, h x)

lemma forall_open_iff_discrete {X : Type*} [topological_space X] :
  (∀ s : set X, is_open s) ↔ discrete_topology X :=
⟨λ h, ⟨by { ext U , show is_open U ↔ true, simp [h U] }⟩, λ a, @is_open_discrete _ _ a⟩

lemma singletons_open_iff_discrete {X : Type*} [topological_space X] :
  (∀ a : X, is_open ({a} : set X)) ↔ discrete_topology X :=
⟨λ h, ⟨eq_bot_of_singletons_open h⟩, λ a _, @is_open_discrete _ _ a _⟩

end lattice

section galois_connection
variables {α : Type*} {β : Type*} {γ : Type*}

/-- Given `f : α → β` and a topology on `β`, the induced topology on `α` is the collection of
  sets that are preimages of some open set in `β`. This is the coarsest topology that
  makes `f` continuous. -/
def topological_space.induced {α : Type u} {β : Type v} (f : α → β) (t : topological_space β) :
  topological_space α :=
{ is_open        := λs, ∃s', t.is_open s' ∧ f ⁻¹' s' = s,
  is_open_univ   := ⟨univ, t.is_open_univ, preimage_univ⟩,
  is_open_inter  := by rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩;
    exact ⟨s'₁ ∩ s'₂, t.is_open_inter _ _ hs₁ hs₂, preimage_inter⟩,
  is_open_sUnion := assume s h,
  begin
    simp only [classical.skolem] at h,
    cases h with f hf,
    apply exists.intro (⋃(x : set α) (h : x ∈ s), f x h),
    simp only [sUnion_eq_bUnion, preimage_Union, (λx h, (hf x h).right)], refine ⟨_, rfl⟩,
    exact (@is_open_Union β _ t _ $ assume i,
      show is_open (⋃h, f i h), from @is_open_Union β _ t _ $ assume h, (hf i h).left)
  end }

lemma is_open_induced_iff [t : topological_space β] {s : set α} {f : α → β} :
  @is_open α (t.induced f) s ↔ (∃t, is_open t ∧ f ⁻¹' t = s) :=
iff.rfl

lemma is_open_induced_iff' [t : topological_space β] {s : set α} {f : α → β} :
  (t.induced f).is_open s ↔ (∃t, is_open t ∧ f ⁻¹' t = s) :=
iff.rfl

lemma is_closed_induced_iff [t : topological_space β] {s : set α} {f : α → β} :
  @is_closed α (t.induced f) s ↔ (∃t, is_closed t ∧ f ⁻¹' t = s) :=
begin
  simp only [← is_open_compl_iff, is_open_induced_iff],
  exact ⟨λ ⟨t, ht, heq⟩, ⟨tᶜ, by rwa compl_compl, by simp [preimage_compl, heq, compl_compl]⟩,
         λ ⟨t, ht, heq⟩, ⟨tᶜ, ht, by simp only [preimage_compl, heq.symm]⟩⟩
end

/-- Given `f : α → β` and a topology on `α`, the coinduced topology on `β` is defined
  such that `s:set β` is open if the preimage of `s` is open. This is the finest topology that
  makes `f` continuous. -/
def topological_space.coinduced {α : Type u} {β : Type v} (f : α → β) (t : topological_space α) :
  topological_space β :=
{ is_open        := λs, t.is_open (f ⁻¹' s),
  is_open_univ   := by rw preimage_univ; exact t.is_open_univ,
  is_open_inter  := assume s₁ s₂ h₁ h₂, by rw preimage_inter; exact t.is_open_inter _ _ h₁ h₂,
  is_open_sUnion := assume s h, by rw [preimage_sUnion]; exact (@is_open_Union _ _ t _ $ assume i,
    show is_open (⋃ (H : i ∈ s), f ⁻¹' i), from
      @is_open_Union _ _ t _ $ assume hi, h i hi) }

lemma is_open_coinduced {t : topological_space α} {s : set β} {f : α → β} :
  @is_open β (topological_space.coinduced f t) s ↔ is_open (f ⁻¹' s) :=
iff.rfl

lemma preimage_nhds_coinduced [topological_space α] {π : α → β} {s : set β}
  {a : α} (hs : s ∈ @nhds β (topological_space.coinduced π ‹_›) (π a)) : π ⁻¹' s ∈ 𝓝 a :=
begin
  letI := topological_space.coinduced π ‹_›,
  rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩,
  exact mem_nhds_iff.mpr ⟨π ⁻¹' V, set.preimage_mono hVs, V_op, mem_V⟩
end

variables {t t₁ t₂ : topological_space α} {t' : topological_space β} {f : α → β} {g : β → α}

lemma continuous.coinduced_le (h : @continuous α β t t' f) :
  t.coinduced f ≤ t' :=
λ s hs, (continuous_def.1 h s hs : _)

lemma coinduced_le_iff_le_induced {f : α → β} {tα : topological_space α}
  {tβ : topological_space β} :
  tα.coinduced f ≤ tβ ↔ tα ≤ tβ.induced f :=
iff.intro
  (assume h s ⟨t, ht, hst⟩, hst ▸ h _ ht)
  (assume h s hs, show tα.is_open (f ⁻¹' s), from h _ ⟨s, hs, rfl⟩)

lemma continuous.le_induced (h : @continuous α β t t' f) :
  t ≤ t'.induced f :=
coinduced_le_iff_le_induced.1 h.coinduced_le

lemma gc_coinduced_induced (f : α → β) :
  galois_connection (topological_space.coinduced f) (topological_space.induced f) :=
assume f g, coinduced_le_iff_le_induced

lemma induced_mono (h : t₁ ≤ t₂) : t₁.induced g ≤ t₂.induced g :=
(gc_coinduced_induced g).monotone_u h

lemma coinduced_mono (h : t₁ ≤ t₂) : t₁.coinduced f ≤ t₂.coinduced f :=
(gc_coinduced_induced f).monotone_l h

@[simp] lemma induced_top : (⊤ : topological_space α).induced g = ⊤ :=
(gc_coinduced_induced g).u_top

@[simp] lemma induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induced g :=
(gc_coinduced_induced g).u_inf

@[simp] lemma induced_infi {ι : Sort w} {t : ι → topological_space α} :
  (⨅i, t i).induced g = (⨅i, (t i).induced g) :=
(gc_coinduced_induced g).u_infi

@[simp] lemma coinduced_bot : (⊥ : topological_space α).coinduced f = ⊥ :=
(gc_coinduced_induced f).l_bot

@[simp] lemma coinduced_sup : (t₁ ⊔ t₂).coinduced f = t₁.coinduced f ⊔ t₂.coinduced f :=
(gc_coinduced_induced f).l_sup

@[simp] lemma coinduced_supr {ι : Sort w} {t : ι → topological_space α} :
  (⨆i, t i).coinduced f = (⨆i, (t i).coinduced f) :=
(gc_coinduced_induced f).l_supr

lemma induced_id [t : topological_space α] : t.induced id = t :=
topological_space_eq $ funext $ assume s, propext $
  ⟨assume ⟨s', hs, h⟩, h ▸ hs, assume hs, ⟨s, hs, rfl⟩⟩

lemma induced_compose [tγ : topological_space γ]
  {f : α → β} {g : β → γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f) :=
topological_space_eq $ funext $ assume s, propext $
  ⟨assume ⟨s', ⟨s, hs, h₂⟩, h₁⟩, h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩,
    assume ⟨s, hs, h⟩, ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩

lemma induced_const [t : topological_space α] {x : α} :
  t.induced (λ y : β, x) = ⊤ :=
le_antisymm le_top (@continuous_const β α ⊤ t x).le_induced

lemma coinduced_id [t : topological_space α] : t.coinduced id = t :=
topological_space_eq rfl

lemma coinduced_compose [tα : topological_space α]
  {f : α → β} {g : β → γ} : (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f) :=
topological_space_eq rfl

end galois_connection

/- constructions using the complete lattice structure -/
section constructions
open topological_space

variables {α : Type u} {β : Type v}

instance inhabited_topological_space {α : Type u} : inhabited (topological_space α) :=
⟨⊤⟩

@[priority 100]
instance subsingleton.unique_topological_space [subsingleton α] :
  unique (topological_space α) :=
{ default := ⊥,
  uniq := λ t, eq_bot_of_singletons_open $ λ x, subsingleton.set_cases
    (@is_open_empty _ t) (@is_open_univ _ t) ({x} : set α) }

@[priority 100]
instance subsingleton.discrete_topology [t : topological_space α] [subsingleton α] :
  discrete_topology α :=
⟨unique.eq_default t⟩

instance : topological_space empty := ⊥
instance : discrete_topology empty := ⟨rfl⟩
instance : topological_space pempty := ⊥
instance : discrete_topology pempty := ⟨rfl⟩
instance : topological_space punit := ⊥
instance : discrete_topology punit := ⟨rfl⟩
instance : topological_space bool := ⊥
instance : discrete_topology bool := ⟨rfl⟩
instance : topological_space ℕ := ⊥
instance : discrete_topology ℕ := ⟨rfl⟩
instance : topological_space ℤ := ⊥
instance : discrete_topology ℤ := ⟨rfl⟩

instance sierpinski_space : topological_space Prop :=
generate_from {{true}}

lemma le_generate_from {t : topological_space α} { g : set (set α) } (h : ∀s∈g, is_open s) :
  t ≤ generate_from g :=
le_generate_from_iff_subset_is_open.2 h

lemma induced_generate_from_eq {α β} {b : set (set β)} {f : α → β} :
  (generate_from b).induced f = topological_space.generate_from (preimage f '' b) :=
le_antisymm
  (le_generate_from $ ball_image_iff.2 $ assume s hs, ⟨s, generate_open.basic _ hs, rfl⟩)
  (coinduced_le_iff_le_induced.1 $ le_generate_from $ assume s hs,
    generate_open.basic _ $ mem_image_of_mem _ hs)

lemma le_induced_generate_from {α β} [t : topological_space α] {b : set (set β)}
  {f : α → β} (h : ∀ (a : set β), a ∈ b → is_open (f ⁻¹' a)) : t ≤ induced f (generate_from b) :=
begin
  rw induced_generate_from_eq,
  apply le_generate_from,
  simp only [mem_image, and_imp, forall_apply_eq_imp_iff₂, exists_imp_distrib],
  exact h,
end

/-- This construction is left adjoint to the operation sending a topology on `α`
  to its neighborhood filter at a fixed point `a : α`. -/
protected def topological_space.nhds_adjoint (a : α) (f : filter α) : topological_space α :=
{ is_open        := λs, a ∈ s → s ∈ f,
  is_open_univ   := assume s, univ_mem_sets,
  is_open_inter  := assume s t hs ht ⟨has, hat⟩, inter_mem_sets (hs has) (ht hat),
  is_open_sUnion := assume k hk ⟨u, hu, hau⟩, mem_sets_of_superset (hk u hu hau)
    (subset_sUnion_of_mem hu) }

lemma gc_nhds (a : α) :
  galois_connection  (topological_space.nhds_adjoint a) (λt, @nhds α t a) :=
assume f t, by { rw le_nhds_iff, exact ⟨λ H s hs has, H _ has hs, λ H s has hs, H _ hs has⟩ }

lemma nhds_mono {t₁ t₂ : topological_space α} {a : α} (h : t₁ ≤ t₂) :
  @nhds α t₁ a ≤ @nhds α t₂ a := (gc_nhds a).monotone_u h

lemma nhds_infi {ι : Sort*} {t : ι → topological_space α} {a : α} :
  @nhds α (infi t) a = (⨅i, @nhds α (t i) a) := (gc_nhds a).u_infi

lemma nhds_Inf {s : set (topological_space α)} {a : α} :
  @nhds α (Inf s) a = (⨅t∈s, @nhds α t a) := (gc_nhds a).u_Inf

lemma nhds_inf {t₁ t₂ : topological_space α} {a : α} :
  @nhds α (t₁ ⊓ t₂) a = @nhds α t₁ a ⊓ @nhds α t₂ a := (gc_nhds a).u_inf

lemma nhds_top {a : α} : @nhds α ⊤ a = ⊤ := (gc_nhds a).u_top

local notation `cont` := @continuous _ _
local notation `tspace` := topological_space
open topological_space

variables {γ : Type*} {f : α → β} {ι : Sort*}

lemma continuous_iff_coinduced_le {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ coinduced f t₁ ≤ t₂ :=
continuous_def.trans iff.rfl

lemma continuous_iff_le_induced {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ t₁ ≤ induced f t₂ :=
iff.trans continuous_iff_coinduced_le (gc_coinduced_induced f _ _)

theorem continuous_generated_from {t : tspace α} {b : set (set β)}
  (h : ∀s∈b, is_open (f ⁻¹' s)) : cont t (generate_from b) f :=
continuous_iff_coinduced_le.2 $ le_generate_from h

@[continuity]
lemma continuous_induced_dom {t : tspace β} : cont (induced f t) t f :=
by { rw continuous_def, assume s h, exact ⟨_, h, rfl⟩ }

lemma continuous_induced_rng {g : γ → α} {t₂ : tspace β} {t₁ : tspace γ}
  (h : cont t₁ t₂ (f ∘ g)) : cont t₁ (induced f t₂) g :=
begin
  rw continuous_def,
  rintros s ⟨t, ht, s_eq⟩,
  simpa [← s_eq] using continuous_def.1 h t ht,
end

lemma continuous_induced_rng' [topological_space α] [topological_space β] [topological_space γ]
  {g : γ → α} (f : α → β) (H : ‹topological_space α› = ‹topological_space β›.induced f)
  (h : continuous (f ∘ g)) : continuous g :=
H.symm ▸ continuous_induced_rng h

lemma continuous_coinduced_rng {t : tspace α} : cont t (coinduced f t) f :=
by { rw continuous_def, assume s h, exact h }

lemma continuous_coinduced_dom {g : β → γ} {t₁ : tspace α} {t₂ : tspace γ}
  (h : cont t₁ t₂ (g ∘ f)) : cont (coinduced f t₁) t₂ g :=
begin
  rw continuous_def at h ⊢,
  assume s hs,
  exact h _ hs
end

lemma continuous_le_dom {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h₁ : t₂ ≤ t₁) (h₂ : cont t₁ t₃ f) : cont t₂ t₃ f :=
begin
  rw continuous_def at h₂ ⊢,
  assume s h,
  exact h₁ _ (h₂ s h)
end

lemma continuous_le_rng {t₁ : tspace α} {t₂ t₃ : tspace β}
  (h₁ : t₂ ≤ t₃) (h₂ : cont t₁ t₂ f) : cont t₁ t₃ f :=
begin
  rw continuous_def at h₂ ⊢,
  assume s h,
  exact h₂ s (h₁ s h)
end

lemma continuous_sup_dom {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h₁ : cont t₁ t₃ f) (h₂ : cont t₂ t₃ f) : cont (t₁ ⊔ t₂) t₃ f :=
begin
  rw continuous_def at h₁ h₂ ⊢,
  assume s h,
  exact ⟨h₁ s h, h₂ s h⟩
end

lemma continuous_sup_rng_left {t₁ : tspace α} {t₃ t₂ : tspace β} :
  cont t₁ t₂ f → cont t₁ (t₂ ⊔ t₃) f :=
continuous_le_rng le_sup_left

lemma continuous_sup_rng_right {t₁ : tspace α} {t₃ t₂ : tspace β} :
  cont t₁ t₃ f → cont t₁ (t₂ ⊔ t₃) f :=
continuous_le_rng le_sup_right

lemma continuous_Sup_dom {t₁ : set (tspace α)} {t₂ : tspace β}
  (h : ∀t∈t₁, cont t t₂ f) : cont (Sup t₁) t₂ f :=
continuous_iff_le_induced.2 $ Sup_le $ assume t ht, continuous_iff_le_induced.1 $ h t ht

lemma continuous_Sup_rng {t₁ : tspace α} {t₂ : set (tspace β)} {t : tspace β}
  (h₁ : t ∈ t₂) (hf : cont t₁ t f) : cont t₁ (Sup t₂) f :=
continuous_iff_coinduced_le.2 $ le_Sup_of_le h₁ $ continuous_iff_coinduced_le.1 hf

lemma continuous_supr_dom {t₁ : ι → tspace α} {t₂ : tspace β}
  (h : ∀i, cont (t₁ i) t₂ f) : cont (supr t₁) t₂ f :=
continuous_Sup_dom $ assume t ⟨i, (t_eq : t₁ i = t)⟩, t_eq ▸ h i

lemma continuous_supr_rng {t₁ : tspace α} {t₂ : ι → tspace β} {i : ι}
  (h : cont t₁ (t₂ i) f) : cont t₁ (supr t₂) f :=
continuous_Sup_rng ⟨i, rfl⟩ h

lemma continuous_inf_rng {t₁ : tspace α} {t₂ t₃ : tspace β}
  (h₁ : cont t₁ t₂ f) (h₂ : cont t₁ t₃ f) : cont t₁ (t₂ ⊓ t₃) f :=
continuous_iff_coinduced_le.2 $ le_inf
  (continuous_iff_coinduced_le.1 h₁)
  (continuous_iff_coinduced_le.1 h₂)

lemma continuous_inf_dom_left {t₁ t₂ : tspace α} {t₃ : tspace β} :
  cont t₁ t₃ f → cont (t₁ ⊓ t₂) t₃ f :=
continuous_le_dom inf_le_left

lemma continuous_inf_dom_right {t₁ t₂ : tspace α} {t₃ : tspace β} :
  cont t₂ t₃ f → cont (t₁ ⊓ t₂) t₃ f :=
continuous_le_dom inf_le_right

lemma continuous_Inf_dom {t₁ : set (tspace α)} {t₂ : tspace β} {t : tspace α} (h₁ : t ∈ t₁) :
  cont t t₂ f → cont (Inf t₁) t₂ f :=
continuous_le_dom $ Inf_le h₁

lemma continuous_Inf_rng {t₁ : tspace α} {t₂ : set (tspace β)}
  (h : ∀t∈t₂, cont t₁ t f) : cont t₁ (Inf t₂) f :=
continuous_iff_coinduced_le.2 $ le_Inf $ assume b hb, continuous_iff_coinduced_le.1 $ h b hb

lemma continuous_infi_dom {t₁ : ι → tspace α} {t₂ : tspace β} {i : ι} :
  cont (t₁ i) t₂ f → cont (infi t₁) t₂ f :=
continuous_le_dom $ infi_le _ _

lemma continuous_infi_rng {t₁ : tspace α} {t₂ : ι → tspace β}
  (h : ∀i, cont t₁ (t₂ i) f) : cont t₁ (infi t₂) f :=
continuous_iff_coinduced_le.2 $ le_infi $ assume i, continuous_iff_coinduced_le.1 $ h i

@[continuity] lemma continuous_bot {t : tspace β} : cont ⊥ t f :=
continuous_iff_le_induced.2 $ bot_le

@[continuity] lemma continuous_top {t : tspace α} : cont t ⊤ f :=
continuous_iff_coinduced_le.2 $ le_top

/- 𝓝 in the induced topology -/

theorem mem_nhds_induced [T : topological_space α] (f : β → α) (a : β) (s : set β) :
  s ∈ @nhds β (topological_space.induced f T) a ↔ ∃ u ∈ 𝓝 (f a), f ⁻¹' u ⊆ s :=
begin
  simp only [mem_nhds_iff, is_open_induced_iff, exists_prop, set.mem_set_of_eq],
  split,
  { rintros ⟨u, usub, ⟨v, openv, ueq⟩, au⟩,
    exact ⟨v, ⟨v, set.subset.refl v, openv, by rwa ←ueq at au⟩, by rw ueq; exact usub⟩ },
  rintros ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩,
  exact ⟨f ⁻¹' v, set.subset.trans (set.preimage_mono vsubu) finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩
end

theorem nhds_induced [T : topological_space α] (f : β → α) (a : β) :
  @nhds β (topological_space.induced f T) a = comap f (𝓝 (f a)) :=
by { ext s, rw [mem_nhds_induced, mem_comap_sets] }

lemma induced_iff_nhds_eq [tα : topological_space α] [tβ : topological_space β] (f : β → α) :
tβ = tα.induced f ↔ ∀ b, 𝓝 b = comap f (𝓝 $ f b) :=
⟨λ h a, h.symm ▸ nhds_induced f a, λ h, eq_of_nhds_eq_nhds $ λ x, by rw [h, nhds_induced]⟩

theorem map_nhds_induced_of_surjective [T : topological_space α]
    {f : β → α} (hf : function.surjective f) (a : β) :
  map f (@nhds β (topological_space.induced f T) a) = 𝓝 (f a) :=
by rw [nhds_induced, map_comap_of_surjective hf]

end constructions

section induced
open topological_space
variables {α : Type*} {β : Type*}
variables [t : topological_space β] {f : α → β}

theorem is_open_induced_eq {s : set α} :
  @is_open _ (induced f t) s ↔ s ∈ preimage f '' {s | is_open s} :=
iff.rfl

theorem is_open_induced {s : set β} (h : is_open s) : (induced f t).is_open (f ⁻¹' s) :=
⟨s, h, rfl⟩

lemma map_nhds_induced_eq (a : α) : map f (@nhds α (induced f t) a) = 𝓝[range f] (f a) :=
by rw [nhds_induced, filter.map_comap, nhds_within]

lemma map_nhds_induced_of_mem {a : α} (h : range f ∈ 𝓝 (f a)) :
  map f (@nhds α (induced f t) a) = 𝓝 (f a) :=
by rw [nhds_induced, filter.map_comap_of_mem h]

lemma closure_induced [t : topological_space β] {f : α → β} {a : α} {s : set α} :
  a ∈ @closure α (topological_space.induced f t) s ↔ f a ∈ closure (f '' s) :=
by simp only [mem_closure_iff_frequently, nhds_induced, frequently_comap, mem_image, and_comm]

end induced

section sierpinski
variables {α : Type*} [topological_space α]

@[simp] lemma is_open_singleton_true : is_open ({true} : set Prop) :=
topological_space.generate_open.basic _ (by simp)

lemma continuous_Prop {p : α → Prop} : continuous p ↔ is_open {x | p x} :=
⟨assume h : continuous p,
  have is_open (p ⁻¹' {true}),
    from is_open_singleton_true.preimage h,
  by simp [preimage, eq_true] at this; assumption,
  assume h : is_open {x | p x},
  continuous_generated_from $ assume s (hs : s ∈ {{true}}),
    by simp at hs; simp [hs, preimage, eq_true, h]⟩

lemma is_open_iff_continuous_mem {s : set α} : is_open s ↔ continuous (λ x, x ∈ s) :=
continuous_Prop.symm

end sierpinski

section infi
variables {α : Type u} {ι : Type v} {t : ι → topological_space α}

lemma is_open_supr_iff {s : set α} : @is_open _ (⨆ i, t i) s ↔ ∀ i, @is_open _ (t i) s :=
begin
  -- s defines a map from α to Prop, which is continuous iff s is open.
  suffices : @continuous _ _ (⨆ i, t i) _ s ↔ ∀ i, @continuous _ _ (t i) _ s,
  { simpa only [continuous_Prop] using this },
  simp only [continuous_iff_le_induced, supr_le_iff]
end

lemma is_closed_infi_iff {s : set α} : @is_closed _ (⨆ i, t i) s ↔ ∀ i, @is_closed _ (t i) s :=
by simp [← is_open_compl_iff, is_open_supr_iff]

end infi
