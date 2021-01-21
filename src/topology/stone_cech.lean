/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import topology.dense_embedding

/-! # Stone-Čech compactification

Construction of the Stone-Čech compactification using ultrafilters.

Parts of the formalization are based on "Ultrafilters and Topology"
by Marius Stekelenburg, particularly section 5.
-/

noncomputable theory

open filter set
open_locale topological_space

universes u v

section ultrafilter
/- The set of ultrafilters on α carries a natural topology which makes
  it the Stone-Čech compactification of α (viewed as a discrete space). -/

/-- Basis for the topology on `ultrafilter α`. -/
def ultrafilter_basis (α : Type u) : set (set (ultrafilter α)) :=
range $ λ s : set α, {u | s ∈ u}

variables {α : Type u}

instance : topological_space (ultrafilter α) :=
topological_space.generate_from (ultrafilter_basis α)

lemma ultrafilter_basis_is_basis :
  topological_space.is_topological_basis (ultrafilter_basis α) :=
⟨begin
   rintros _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ u ⟨ua, ub⟩,
   refine ⟨_, ⟨a ∩ b, rfl⟩, inter_mem_sets ua ub, assume v hv, ⟨_, _⟩⟩;
     apply mem_sets_of_superset hv; simp [inter_subset_right a b]
 end,
 eq_univ_of_univ_subset $ subset_sUnion_of_mem $
   ⟨univ, eq_univ_of_forall (λ u, univ_mem_sets)⟩,
 rfl⟩

/-- The basic open sets for the topology on ultrafilters are open. -/
lemma ultrafilter_is_open_basic (s : set α) :
  is_open {u : ultrafilter α | s ∈ u} :=
topological_space.is_open_of_is_topological_basis ultrafilter_basis_is_basis ⟨s, rfl⟩

/-- The basic open sets for the topology on ultrafilters are also closed. -/
lemma ultrafilter_is_closed_basic (s : set α) :
  is_closed {u : ultrafilter α | s ∈ u} :=
begin
  change is_open _ᶜ,
  convert ultrafilter_is_open_basic sᶜ,
  ext u,
  exact ultrafilter.compl_mem_iff_not_mem.symm
end

/-- Every ultrafilter `u` on `ultrafilter α` converges to a unique
  point of `ultrafilter α`, namely `mjoin u`. -/
lemma ultrafilter_converges_iff {u : ultrafilter (ultrafilter α)} {x : ultrafilter α} :
  ↑u ≤ 𝓝 x ↔ x = mjoin u :=
begin
  rw [eq_comm, ← ultrafilter.coe_le_coe],
  change ↑u ≤ 𝓝 x ↔ ∀ s ∈ x, {v : ultrafilter α | s ∈ v} ∈ u,
  simp only [topological_space.nhds_generate_from, le_infi_iff, ultrafilter_basis,
    le_principal_iff, mem_set_of_eq],
  split,
  { intros h a ha, exact h _ ⟨ha, a, rfl⟩ },
  { rintros h a ⟨xi, a, rfl⟩, exact h _ xi }
end

instance ultrafilter_compact : compact_space (ultrafilter α) :=
⟨compact_iff_ultrafilter_le_nhds.mpr $ assume f _,
   ⟨mjoin f, trivial, ultrafilter_converges_iff.mpr rfl⟩⟩

instance ultrafilter.t2_space : t2_space (ultrafilter α) :=
t2_iff_ultrafilter.mpr $ assume x y f fx fy,
  have hx : x = mjoin f, from ultrafilter_converges_iff.mp fx,
  have hy : y = mjoin f, from ultrafilter_converges_iff.mp fy,
  hx.trans hy.symm

lemma ultrafilter_comap_pure_nhds (b : ultrafilter α) : comap pure (𝓝 b) ≤ b :=
begin
  rw topological_space.nhds_generate_from,
  simp only [comap_infi, comap_principal],
  intros s hs,
  rw ←le_principal_iff,
  refine infi_le_of_le {u | s ∈ u} _,
  refine infi_le_of_le ⟨hs, ⟨s, rfl⟩⟩ _,
  exact principal_mono.2 (λ a, id)
end

section embedding

lemma ultrafilter_pure_injective : function.injective (pure : α → ultrafilter α) :=
begin
  intros x y h,
  have : {x} ∈ (pure x : ultrafilter α) := singleton_mem_pure_sets,
  rw h at this,
  exact (mem_singleton_iff.mp (mem_pure_sets.mp this)).symm
end

open topological_space

/-- The range of `pure : α → ultrafilter α` is dense in `ultrafilter α`. -/
lemma dense_range_pure : dense_range (pure : α → ultrafilter α) :=
λ x, mem_closure_iff_ultrafilter.mpr
       ⟨x.map pure, range_mem_map, ultrafilter_converges_iff.mpr (bind_pure x).symm⟩

/-- The map `pure : α → ultra_filter α` induces on `α` the discrete topology. -/
lemma induced_topology_pure :
  topological_space.induced (pure : α → ultrafilter α) ultrafilter.topological_space = ⊥ :=
begin
  apply eq_bot_of_singletons_open,
  intros x,
  use [{u : ultrafilter α | {x} ∈ u}, ultrafilter_is_open_basic _],
  simp,
end

/-- `pure : α → ultrafilter α` defines a dense inducing of `α` in `ultrafilter α`. -/
lemma dense_inducing_pure : @dense_inducing _ _ ⊥ _ (pure : α → ultrafilter α) :=
by letI : topological_space α := ⊥; exact ⟨⟨induced_topology_pure.symm⟩, dense_range_pure⟩

-- The following refined version will never be used

/-- `pure : α → ultrafilter α` defines a dense embedding of `α` in `ultrafilter α`. -/
lemma dense_embedding_pure : @dense_embedding _ _ ⊥ _ (pure : α → ultrafilter α) :=
by letI : topological_space α := ⊥ ;
exact { inj := ultrafilter_pure_injective, ..dense_inducing_pure }
end embedding

section extension
/- Goal: Any function `α → γ` to a compact Hausdorff space `γ` has a
  unique extension to a continuous function `ultrafilter α → γ`. We
  already know it must be unique because `α → ultrafilter α` is a
  dense embedding and `γ` is Hausdorff. For existence, we will invoke
  `dense_embedding.continuous_extend`. -/

variables {γ : Type*} [topological_space γ]

/-- The extension of a function `α → γ` to a function `ultrafilter α → γ`.
  When `γ` is a compact Hausdorff space it will be continuous. -/
def ultrafilter.extend (f : α → γ) : ultrafilter α → γ :=
by letI : topological_space α := ⊥; exact dense_inducing_pure.extend f

variables [t2_space γ]

lemma ultrafilter_extend_extends (f : α → γ) : ultrafilter.extend f ∘ pure = f :=
begin
  letI : topological_space α := ⊥,
  haveI : discrete_topology α := ⟨rfl⟩,
  exact funext (dense_inducing_pure.extend_eq continuous_of_discrete_topology)
end

variables  [compact_space γ]

lemma continuous_ultrafilter_extend (f : α → γ) : continuous (ultrafilter.extend f) :=
have ∀ (b : ultrafilter α), ∃ c, tendsto f (comap pure (𝓝 b)) (𝓝 c) := assume b,
  -- b.map f is an ultrafilter on γ, which is compact, so it converges to some c in γ.
  let ⟨c, _, h⟩ := compact_univ.ultrafilter_le_nhds (b.map f)
    (by rw [le_principal_iff]; exact univ_mem_sets) in
  ⟨c, le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h⟩,
begin
  letI : topological_space α := ⊥,
  haveI : normal_space γ := normal_of_compact_t2,
  exact dense_inducing_pure.continuous_extend this
end

/-- The value of `ultrafilter.extend f` on an ultrafilter `b` is the
  unique limit of the ultrafilter `b.map f` in `γ`. -/
lemma ultrafilter_extend_eq_iff {f : α → γ} {b : ultrafilter α} {c : γ} :
  ultrafilter.extend f b = c ↔ ↑(b.map f) ≤ 𝓝 c :=
⟨assume h, begin
   -- Write b as an ultrafilter limit of pure ultrafilters, and use
   -- the facts that ultrafilter.extend is a continuous extension of f.
   let b' : ultrafilter (ultrafilter α) := b.map pure,
   have t : ↑b' ≤ 𝓝 b,
     from ultrafilter_converges_iff.mpr (bind_pure _).symm,
   rw ←h,
   have := (continuous_ultrafilter_extend f).tendsto b,
   refine le_trans _ (le_trans (map_mono t) this),
   change _ ≤ map (ultrafilter.extend f ∘ pure) ↑b,
   rw ultrafilter_extend_extends,
   exact le_refl _
 end,
 assume h, by letI : topological_space α := ⊥; exact
   dense_inducing_pure.extend_eq_of_tendsto (le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h)⟩

end extension

end ultrafilter


section stone_cech
/- Now, we start with a (not necessarily discrete) topological space α
  and we want to construct its Stone-Čech compactification. We can
  build it as a quotient of `ultrafilter α` by the relation which
  identifies two points if the extension of every continuous function
  α → γ to a compact Hausdorff space sends the two points to the same
  point of γ. -/

variables (α : Type u) [topological_space α]

instance stone_cech_setoid : setoid (ultrafilter α) :=
{ r := λ x y, ∀ (γ : Type u) [topological_space γ], by exactI
    ∀ [t2_space γ] [compact_space γ] (f : α → γ) (hf : continuous f),
    ultrafilter.extend f x = ultrafilter.extend f y,
  iseqv :=
    ⟨assume x γ tγ h₁ h₂ f hf, rfl,
     assume x y xy γ tγ h₁ h₂ f hf, by exactI (xy γ f hf).symm,
     assume x y z xy yz γ tγ h₁ h₂ f hf, by exactI (xy γ f hf).trans (yz γ f hf)⟩ }

/-- The Stone-Čech compactification of a topological space. -/
def stone_cech : Type u := quotient (stone_cech_setoid α)

variables {α}
instance : topological_space (stone_cech α) := by unfold stone_cech; apply_instance
instance [inhabited α] : inhabited (stone_cech α) := by unfold stone_cech; apply_instance

/-- The natural map from α to its Stone-Čech compactification. -/
def stone_cech_unit (x : α) : stone_cech α := ⟦pure x⟧

/-- The image of stone_cech_unit is dense. (But stone_cech_unit need
  not be an embedding, for example if α is not Hausdorff.) -/
lemma dense_range_stone_cech_unit : dense_range (stone_cech_unit : α → stone_cech α) :=
dense_range_pure.quotient

section extension

variables {γ : Type u} [topological_space γ] [t2_space γ] [compact_space γ]
variables {f : α → γ} (hf : continuous f)

local attribute [elab_with_expected_type] quotient.lift

/-- The extension of a continuous function from α to a compact
  Hausdorff space γ to the Stone-Čech compactification of α. -/
def stone_cech_extend : stone_cech α → γ :=
quotient.lift (ultrafilter.extend f) (λ x y xy, xy γ f hf)

lemma stone_cech_extend_extends : stone_cech_extend hf ∘ stone_cech_unit = f :=
ultrafilter_extend_extends f

lemma continuous_stone_cech_extend : continuous (stone_cech_extend hf) :=
continuous_quot_lift _ (continuous_ultrafilter_extend f)

end extension

lemma convergent_eqv_pure {u : ultrafilter α} {x : α} (ux : ↑u ≤ 𝓝 x) : u ≈ pure x :=
assume γ tγ h₁ h₂ f hf, begin
  resetI,
  transitivity f x, swap, symmetry,
  all_goals { refine ultrafilter_extend_eq_iff.mpr (le_trans (map_mono _) (hf.tendsto _)) },
  { apply pure_le_nhds }, { exact ux }
end

lemma continuous_stone_cech_unit : continuous (stone_cech_unit : α → stone_cech α) :=
continuous_iff_ultrafilter.mpr $ λ x g gx,
  have ↑(g.map pure) ≤ 𝓝 g,
    by rw ultrafilter_converges_iff; exact (bind_pure _).symm,
  have (g.map stone_cech_unit : filter (stone_cech α)) ≤ 𝓝 ⟦g⟧, from
    continuous_at_iff_ultrafilter.mp (continuous_quotient_mk.tendsto g) _ this,
  by rwa (show ⟦g⟧ = ⟦pure x⟧, from quotient.sound $ convergent_eqv_pure gx) at this

instance stone_cech.t2_space : t2_space (stone_cech α) :=
begin
  rw t2_iff_ultrafilter,
  rintros ⟨x⟩ ⟨y⟩ g gx gy,
  apply quotient.sound,
  intros γ tγ h₁ h₂ f hf,
  resetI,
  let ff := stone_cech_extend hf,
  change ff ⟦x⟧ = ff ⟦y⟧,
  have lim := λ (z : ultrafilter α) (gz : (g : filter (stone_cech α)) ≤ 𝓝 ⟦z⟧),
    ((continuous_stone_cech_extend hf).tendsto _).mono_left gz,
  exact tendsto_nhds_unique (lim x gx) (lim y gy)
end

instance stone_cech.compact_space : compact_space (stone_cech α) :=
quotient.compact_space

end stone_cech
