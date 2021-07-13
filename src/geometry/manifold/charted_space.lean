/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.local_homeomorph

/-!
# Charted spaces

A smooth manifold is a topological space `M` locally modelled on a euclidean space (or a euclidean
half-space for manifolds with boundaries, or an infinite dimensional vector space for more general
notions of manifolds), i.e., the manifold is covered by open subsets on which there are local
homeomorphisms (the charts) going to a model space `H`, and the changes of charts should be smooth
maps.

In this file, we introduce a general framework describing these notions, where the model space is an
arbitrary topological space. We avoid the word *manifold*, which should be reserved for the
situation where the model space is a (subset of a) vector space, and use the terminology
*charted space* instead.

If the changes of charts satisfy some additional property (for instance if they are smooth), then
`M` inherits additional structure (it makes sense to talk about smooth manifolds). There are
therefore two different ingredients in a charted space:
* the set of charts, which is data
* the fact that changes of charts belong to some group (in fact groupoid), which is additional Prop.

We separate these two parts in the definition: the charted space structure is just the set of
charts, and then the different smoothness requirements (smooth manifold, orientable manifold,
contact manifold, and so on) are additional properties of these charts. These properties are
formalized through the notion of structure groupoid, i.e., a set of local homeomorphisms stable
under composition and inverse, to which the change of coordinates should belong.

## Main definitions

* `structure_groupoid H` : a subset of local homeomorphisms of `H` stable under composition,
  inverse and restriction (ex: local diffeos).
* `continuous_groupoid H` : the groupoid of all local homeomorphisms of `H`
* `charted_space H M` : charted space structure on `M` modelled on `H`, given by an atlas of
  local homeomorphisms from `M` to `H` whose sources cover `M`. This is a type class.
* `has_groupoid M G` : when `G` is a structure groupoid on `H` and `M` is a charted space
  modelled on `H`, require that all coordinate changes belong to `G`. This is a type class.
* `atlas H M` : when `M` is a charted space modelled on `H`, the atlas of this charted
  space structure, i.e., the set of charts.
* `G.maximal_atlas M` : when `M` is a charted space modelled on `H` and admitting `G` as a
  structure groupoid, one can consider all the local homeomorphisms from `M` to `H` such that
  changing coordinate from any chart to them belongs to `G`. This is a larger atlas, called the
  maximal atlas (for the groupoid `G`).
* `structomorph G M M'` : the type of diffeomorphisms between the charted spaces `M` and `M'` for
  the groupoid `G`. We avoid the word diffeomorphism, keeping it for the smooth category.

As a basic example, we give the instance
`instance charted_space_model_space (H : Type*) [topological_space H] : charted_space H H`
saying that a topological space is a charted space over itself, with the identity as unique chart.
This charted space structure is compatible with any groupoid.

Additional useful definitions:

* `pregroupoid H` : a subset of local mas of `H` stable under composition and
  restriction, but not inverse (ex: smooth maps)
* `groupoid_of_pregroupoid` : construct a groupoid from a pregroupoid, by requiring that a map and
  its inverse both belong to the pregroupoid (ex: construct diffeos from smooth maps)
* `chart_at H x` is a preferred chart at `x : M` when `M` has a charted space structure modelled on
  `H`.
* `G.compatible he he'` states that, for any two charts `e` and `e'` in the atlas, the composition
  of `e.symm` and `e'` belongs to the groupoid `G` when `M` admits `G` as a structure groupoid.
* `G.compatible_of_mem_maximal_atlas he he'` states that, for any two charts `e` and `e'` in the
  maximal atlas associated to the groupoid `G`, the composition of `e.symm` and `e'` belongs to the
  `G` if `M` admits `G` as a structure groupoid.
* `charted_space_core.to_charted_space`: consider a space without a topology, but endowed with a set
  of charts (which are local equivs) for which the change of coordinates are local homeos. Then
  one can construct a topology on the space for which the charts become local homeos, defining
  a genuine charted space structure.

## Implementation notes

The atlas in a charted space is *not* a maximal atlas in general: the notion of maximality depends
on the groupoid one considers, and changing groupoids changes the maximal atlas. With the current
formalization, it makes sense first to choose the atlas, and then to ask whether this precise atlas
defines a smooth manifold, an orientable manifold, and so on. A consequence is that structomorphisms
between `M` and `M'` do *not* induce a bijection between the atlases of `M` and `M'`: the
definition is only that, read in charts, the structomorphism locally belongs to the groupoid under
consideration. (This is equivalent to inducing a bijection between elements of the maximal atlas).
A consequence is that the invariance under structomorphisms of properties defined in terms of the
atlas is not obvious in general, and could require some work in theory (amounting to the fact
that these properties only depend on the maximal atlas, for instance). In practice, this does not
create any real difficulty.

We use the letter `H` for the model space thinking of the case of manifolds with boundary, where the
model space is a half space.

Manifolds are sometimes defined as topological spaces with an atlas of local diffeomorphisms, and
sometimes as spaces with an atlas from which a topology is deduced. We use the former approach:
otherwise, there would be an instance from manifolds to topological spaces, which means that any
instance search for topological spaces would try to find manifold structures involving a yet
unknown model space, leading to problems. However, we also introduce the latter approach,
through a structure `charted_space_core` making it possible to construct a topology out of a set of
local equivs with compatibility conditions (but we do not register it as an instance).

In the definition of a charted space, the model space is written as an explicit parameter as there
can be several model spaces for a given topological space. For instance, a complex manifold
(modelled over `ℂ^n`) will also be seen sometimes as a real manifold modelled over `ℝ^(2n)`.

## Notations

In the locale `manifold`, we denote the composition of local homeomorphisms with `≫ₕ`, and the
composition of local equivs with `≫`.
-/

noncomputable theory
open_locale classical topological_space
open filter
universes u

variables {H : Type u} {H' : Type*} {M : Type*} {M' : Type*} {M'' : Type*}

/- Notational shortcut for the composition of local homeomorphisms and local equivs, i.e.,
`local_homeomorph.trans` and `local_equiv.trans`.
Note that, as is usual for equivs, the composition is from left to right, hence the direction of
the arrow. -/
localized "infixr  ` ≫ₕ `:100 := local_homeomorph.trans" in manifold
localized "infixr  ` ≫ `:100 := local_equiv.trans" in manifold

/- `simp` looks for subsingleton instances at every call. This turns out to be very
inefficient, especially in `simp`-heavy parts of the library such as the manifold code.
Disable two such instances to speed up things.
NB: this is just a hack. TODO: fix `simp` properly. -/
localized "attribute [-instance] unique.subsingleton pi.subsingleton" in manifold

open set local_homeomorph

/-! ### Structure groupoids-/

section groupoid

/-! One could add to the definition of a structure groupoid the fact that the restriction of an
element of the groupoid to any open set still belongs to the groupoid.
(This is in Kobayashi-Nomizu.)
I am not sure I want this, for instance on `H × E` where `E` is a vector space, and the groupoid is
made of functions respecting the fibers and linear in the fibers (so that a charted space over this
groupoid is naturally a vector bundle) I prefer that the members of the groupoid are always
defined on sets of the form `s × E`.  There is a typeclass `closed_under_restriction` for groupoids
which have the restriction property.

The only nontrivial requirement is locality: if a local homeomorphism belongs to the groupoid
around each point in its domain of definition, then it belongs to the groupoid. Without this
requirement, the composition of structomorphisms does not have to be a structomorphism. Note that
this implies that a local homeomorphism with empty source belongs to any structure groupoid, as
it trivially satisfies this condition.

There is also a technical point, related to the fact that a local homeomorphism is by definition a
global map which is a homeomorphism when restricted to its source subset (and its values outside
of the source are not relevant). Therefore, we also require that being a member of the groupoid only
depends on the values on the source.

We use primes in the structure names as we will reformulate them below (without primes) using a
`has_mem` instance, writing `e ∈ G` instead of `e ∈ G.members`.
-/
/-- A structure groupoid is a set of local homeomorphisms of a topological space stable under
composition and inverse. They appear in the definition of the smoothness class of a manifold. -/
structure structure_groupoid (H : Type u) [topological_space H] :=
(members       : set (local_homeomorph H H))
(trans'        : ∀e e' : local_homeomorph H H, e ∈ members → e' ∈ members → e ≫ₕ e' ∈ members)
(symm'         : ∀e : local_homeomorph H H, e ∈ members → e.symm ∈ members)
(id_mem'       : local_homeomorph.refl H ∈ members)
(locality'     : ∀e : local_homeomorph H H, (∀x ∈ e.source, ∃s, is_open s ∧
                  x ∈ s ∧ e.restr s ∈ members) → e ∈ members)
(eq_on_source' : ∀ e e' : local_homeomorph H H, e ∈ members → e' ≈ e → e' ∈ members)

variable [topological_space H]

instance : has_mem (local_homeomorph H H) (structure_groupoid H) :=
⟨λ(e : local_homeomorph H H) (G : structure_groupoid H), e ∈ G.members⟩

lemma structure_groupoid.trans (G : structure_groupoid H) {e e' : local_homeomorph H H}
  (he : e ∈ G) (he' : e' ∈ G) : e ≫ₕ e' ∈ G :=
G.trans' e e' he he'

lemma structure_groupoid.symm (G : structure_groupoid H) {e : local_homeomorph H H} (he : e ∈ G) :
  e.symm ∈ G :=
G.symm' e he

lemma structure_groupoid.id_mem (G : structure_groupoid H) :
  local_homeomorph.refl H ∈ G :=
G.id_mem'

lemma structure_groupoid.locality (G : structure_groupoid H) {e : local_homeomorph H H}
  (h : ∀x ∈ e.source, ∃s, is_open s ∧ x ∈ s ∧ e.restr s ∈ G) :
  e ∈ G :=
G.locality' e h

lemma structure_groupoid.eq_on_source (G : structure_groupoid H) {e e' : local_homeomorph H H}
  (he : e ∈ G) (h : e' ≈ e) : e' ∈ G :=
G.eq_on_source' e e' he h

/-- Partial order on the set of groupoids, given by inclusion of the members of the groupoid -/
instance structure_groupoid.partial_order : partial_order (structure_groupoid H) :=
partial_order.lift structure_groupoid.members
(λa b h, by { cases a, cases b, dsimp at h, induction h, refl })

lemma structure_groupoid.le_iff {G₁ G₂ : structure_groupoid H} :
  G₁ ≤ G₂ ↔ ∀ e, e ∈ G₁ → e ∈ G₂ :=
iff.rfl

/-- The trivial groupoid, containing only the identity (and maps with empty source, as this is
necessary from the definition) -/
def id_groupoid (H : Type u) [topological_space H] : structure_groupoid H :=
{ members := {local_homeomorph.refl H} ∪ {e : local_homeomorph H H | e.source = ∅},
  trans' := λe e' he he', begin
    cases he; simp at he he',
    { simpa only [he, refl_trans]},
    { have : (e ≫ₕ e').source ⊆ e.source := sep_subset _ _,
      rw he at this,
      have : (e ≫ₕ e') ∈ {e : local_homeomorph H H | e.source = ∅} := disjoint_iff.1 this,
      exact (mem_union _ _ _).2 (or.inr this) },
  end,
  symm' := λe he, begin
    cases (mem_union _ _ _).1 he with E E,
    { finish },
    { right,
      simpa only [e.to_local_equiv.image_source_eq_target.symm] with mfld_simps using E},
  end,
  id_mem' := mem_union_left _ rfl,
  locality' := λe he, begin
    cases e.source.eq_empty_or_nonempty with h h,
    { right, exact h },
    { left,
      rcases h with ⟨x, hx⟩,
      rcases he x hx with ⟨s, open_s, xs, hs⟩,
      have x's : x ∈ (e.restr s).source,
      { rw [restr_source, open_s.interior_eq],
        exact ⟨hx, xs⟩ },
      cases hs,
      { replace hs : local_homeomorph.restr e s = local_homeomorph.refl H,
          by simpa only using hs,
        have : (e.restr s).source = univ, by { rw hs, simp },
        change (e.to_local_equiv).source ∩ interior s = univ at this,
        have : univ ⊆ interior s, by { rw ← this, exact inter_subset_right _ _ },
        have : s = univ, by rwa [open_s.interior_eq, univ_subset_iff] at this,
        simpa only [this, restr_univ] using hs },
      { exfalso,
        rw mem_set_of_eq at hs,
        rwa hs at x's } },
  end,
  eq_on_source' := λe e' he he'e, begin
    cases he,
    { left,
      have : e = e',
      { refine eq_of_eq_on_source_univ (setoid.symm he'e) _ _;
        rw set.mem_singleton_iff.1 he ; refl },
      rwa ← this },
    { right,
      change (e.to_local_equiv).source = ∅ at he,
      rwa [set.mem_set_of_eq, he'e.source_eq] }
  end }

/-- Every structure groupoid contains the identity groupoid -/
instance : order_bot (structure_groupoid H) :=
{ bot    := id_groupoid H,
  bot_le := begin
    assume u f hf,
    change f ∈ {local_homeomorph.refl H} ∪ {e : local_homeomorph H H | e.source = ∅} at hf,
    simp only [singleton_union, mem_set_of_eq, mem_insert_iff] at hf,
    cases hf,
    { rw hf,
      apply u.id_mem },
    { apply u.locality,
      assume x hx,
      rw [hf, mem_empty_eq] at hx,
      exact hx.elim }
  end,
  ..structure_groupoid.partial_order }

instance (H : Type u) [topological_space H] : inhabited (structure_groupoid H) :=
⟨id_groupoid H⟩

/-- To construct a groupoid, one may consider classes of local homeos such that both the function
and its inverse have some property. If this property is stable under composition,
one gets a groupoid. `pregroupoid` bundles the properties needed for this construction, with the
groupoid of smooth functions with smooth inverses as an application. -/
structure pregroupoid (H : Type*) [topological_space H] :=
(property : (H → H) → (set H) → Prop)
(comp     : ∀{f g u v}, property f u → property g v → is_open u → is_open v → is_open (u ∩ f ⁻¹' v)
              → property (g ∘ f) (u ∩ f ⁻¹' v))
(id_mem   : property id univ)
(locality : ∀{f u}, is_open u → (∀x∈u, ∃v, is_open v ∧ x ∈ v ∧ property f (u ∩ v)) → property f u)
(congr    : ∀{f g : H → H} {u}, is_open u → (∀x∈u, g x = f x) → property f u → property g u)

/-- Construct a groupoid of local homeos for which the map and its inverse have some property,
from a pregroupoid asserting that this property is stable under composition. -/
def pregroupoid.groupoid (PG : pregroupoid H) : structure_groupoid H :=
{ members   := {e : local_homeomorph H H | PG.property e e.source ∧ PG.property e.symm e.target},
  trans'     := λe e' he he', begin
    split,
    { apply PG.comp he.1 he'.1 e.open_source e'.open_source,
      apply e.continuous_to_fun.preimage_open_of_open e.open_source e'.open_source },
    { apply PG.comp he'.2 he.2 e'.open_target e.open_target,
      apply e'.continuous_inv_fun.preimage_open_of_open e'.open_target e.open_target }
  end,
  symm'     := λe he, ⟨he.2, he.1⟩,
  id_mem'   := ⟨PG.id_mem, PG.id_mem⟩,
  locality' := λe he, begin
    split,
    { apply PG.locality e.open_source (λx xu, _),
      rcases he x xu with ⟨s, s_open, xs, hs⟩,
      refine ⟨s, s_open, xs, _⟩,
      convert hs.1 using 1,
      dsimp [local_homeomorph.restr], rw s_open.interior_eq },
    { apply PG.locality e.open_target (λx xu, _),
      rcases he (e.symm x) (e.map_target xu) with ⟨s, s_open, xs, hs⟩,
      refine ⟨e.target ∩ e.symm ⁻¹' s, _, ⟨xu, xs⟩, _⟩,
      { exact continuous_on.preimage_open_of_open e.continuous_inv_fun e.open_target s_open },
      { rw [← inter_assoc, inter_self],
        convert hs.2 using 1,
        dsimp [local_homeomorph.restr], rw s_open.interior_eq } },
  end,
  eq_on_source' := λe e' he ee', begin
    split,
    { apply PG.congr e'.open_source ee'.2,
      simp only [ee'.1, he.1] },
    { have A := ee'.symm',
      apply PG.congr e'.symm.open_source A.2,
      convert he.2,
      rw A.1,
      refl }
  end }

lemma mem_groupoid_of_pregroupoid {PG : pregroupoid H} {e : local_homeomorph H H} :
  e ∈ PG.groupoid ↔ PG.property e e.source ∧ PG.property e.symm e.target :=
iff.rfl

lemma groupoid_of_pregroupoid_le (PG₁ PG₂ : pregroupoid H)
  (h : ∀f s, PG₁.property f s → PG₂.property f s) : PG₁.groupoid ≤ PG₂.groupoid :=
begin
  refine structure_groupoid.le_iff.2 (λ e he, _),
  rw mem_groupoid_of_pregroupoid at he ⊢,
  exact ⟨h _ _ he.1, h _ _ he.2⟩
end

lemma mem_pregroupoid_of_eq_on_source (PG : pregroupoid H) {e e' : local_homeomorph H H}
  (he' : e ≈ e') (he : PG.property e e.source) : PG.property e' e'.source :=
begin
  rw ← he'.1,
  exact PG.congr e.open_source he'.eq_on.symm he,
end

/-- The pregroupoid of all local maps on a topological space `H` -/
@[reducible] def continuous_pregroupoid (H : Type*) [topological_space H] : pregroupoid H :=
{ property := λf s, true,
  comp     := λf g u v hf hg hu hv huv, trivial,
  id_mem   := trivial,
  locality := λf u u_open h, trivial,
  congr    := λf g u u_open hcongr hf, trivial }

instance (H : Type*) [topological_space H] : inhabited (pregroupoid H) :=
⟨continuous_pregroupoid H⟩

/-- The groupoid of all local homeomorphisms on a topological space `H` -/
def continuous_groupoid (H : Type*) [topological_space H] : structure_groupoid H :=
pregroupoid.groupoid (continuous_pregroupoid H)

/-- Every structure groupoid is contained in the groupoid of all local homeomorphisms -/
instance : order_top (structure_groupoid H) :=
{ top    := continuous_groupoid H,
  le_top := λ u f hf, by { split; exact dec_trivial },
  ..structure_groupoid.partial_order }

/-- A groupoid is closed under restriction if it contains all restrictions of its element local
homeomorphisms to open subsets of the source. -/
class closed_under_restriction (G : structure_groupoid H) : Prop :=
(closed_under_restriction : ∀ {e : local_homeomorph H H}, e ∈ G → ∀ (s : set H), is_open s →
  e.restr s ∈ G)

lemma closed_under_restriction' {G : structure_groupoid H} [closed_under_restriction G]
  {e : local_homeomorph H H} (he : e ∈ G) {s : set H} (hs : is_open s) :
  e.restr s ∈ G :=
closed_under_restriction.closed_under_restriction he s hs

/-- The trivial restriction-closed groupoid, containing only local homeomorphisms equivalent to the
restriction of the identity to the various open subsets. -/
def id_restr_groupoid : structure_groupoid H :=
{ members := {e | ∃ {s : set H} (h : is_open s), e ≈ local_homeomorph.of_set s h},
  trans' := begin
    rintros e e' ⟨s, hs, hse⟩ ⟨s', hs', hse'⟩,
    refine ⟨s ∩ s', is_open.inter hs hs', _⟩,
    have := local_homeomorph.eq_on_source.trans' hse hse',
    rwa local_homeomorph.of_set_trans_of_set at this,
  end,
  symm' := begin
    rintros e ⟨s, hs, hse⟩,
    refine ⟨s, hs, _⟩,
    rw [← of_set_symm],
    exact local_homeomorph.eq_on_source.symm' hse,
  end,
  id_mem' := ⟨univ, is_open_univ, by simp only with mfld_simps⟩,
  locality' := begin
    intros e h,
    refine ⟨e.source, e.open_source, by simp only with mfld_simps, _⟩,
    intros x hx,
    rcases h x hx with ⟨s, hs, hxs, s', hs', hes'⟩,
    have hes : x ∈ (e.restr s).source,
    { rw e.restr_source, refine ⟨hx, _⟩,
      rw hs.interior_eq, exact hxs },
    simpa only with mfld_simps using local_homeomorph.eq_on_source.eq_on hes' hes,
  end,
  eq_on_source' := begin
    rintros e e' ⟨s, hs, hse⟩ hee',
    exact ⟨s, hs, setoid.trans hee' hse⟩,
  end
}

lemma id_restr_groupoid_mem {s : set H} (hs : is_open s) :
  of_set s hs ∈ @id_restr_groupoid H _ := ⟨s, hs, by refl⟩

/-- The trivial restriction-closed groupoid is indeed `closed_under_restriction`. -/
instance closed_under_restriction_id_restr_groupoid :
  closed_under_restriction (@id_restr_groupoid H _) :=
⟨ begin
    rintros e ⟨s', hs', he⟩ s hs,
    use [s' ∩ s, is_open.inter hs' hs],
    refine setoid.trans (local_homeomorph.eq_on_source.restr he s) _,
    exact ⟨by simp only [hs.interior_eq] with mfld_simps, by simp only with mfld_simps⟩,
  end ⟩

/-- A groupoid is closed under restriction if and only if it contains the trivial restriction-closed
groupoid. -/
lemma closed_under_restriction_iff_id_le (G : structure_groupoid H) :
  closed_under_restriction G ↔ id_restr_groupoid ≤ G :=
begin
  split,
  { introsI _i,
    apply structure_groupoid.le_iff.mpr,
    rintros e ⟨s, hs, hes⟩,
    refine G.eq_on_source _ hes,
    convert closed_under_restriction' G.id_mem hs,
    change s = _ ∩ _,
    rw hs.interior_eq,
    simp only with mfld_simps },
  { intros h,
    split,
    intros e he s hs,
    rw ← of_set_trans (e : local_homeomorph H H) hs,
    refine G.trans _ he,
    apply structure_groupoid.le_iff.mp h,
    exact id_restr_groupoid_mem hs },
end

/-- The groupoid of all local homeomorphisms on a topological space `H` is closed under restriction.
-/
instance : closed_under_restriction (continuous_groupoid H) :=
(closed_under_restriction_iff_id_le _).mpr (by convert le_top)

end groupoid


/-! ### Charted spaces -/
/-- A charted space is a topological space endowed with an atlas, i.e., a set of local
homeomorphisms taking value in a model space `H`, called charts, such that the domains of the charts
cover the whole space. We express the covering property by chosing for each `x` a member
`chart_at H x` of the atlas containing `x` in its source: in the smooth case, this is convenient to
construct the tangent bundle in an efficient way.
The model space is written as an explicit parameter as there can be several model spaces for a
given topological space. For instance, a complex manifold (modelled over `ℂ^n`) will also be seen
sometimes as a real manifold over `ℝ^(2n)`.
-/
class charted_space (H : Type*) [topological_space H] (M : Type*) [topological_space M] :=
(atlas []            : set (local_homeomorph M H))
(chart_at []         : M → local_homeomorph M H)
(mem_chart_source [] : ∀x, x ∈ (chart_at x).source)
(chart_mem_atlas []  : ∀x, chart_at x ∈ atlas)

export charted_space
attribute [simp, mfld_simps] mem_chart_source chart_mem_atlas

section charted_space

/-- Any space is a charted_space modelled over itself, by just using the identity chart -/
instance charted_space_self (H : Type*) [topological_space H] : charted_space H H :=
{ atlas            := {local_homeomorph.refl H},
  chart_at         := λx, local_homeomorph.refl H,
  mem_chart_source := λx, mem_univ x,
  chart_mem_atlas  := λx, mem_singleton _ }

/-- In the trivial charted_space structure of a space modelled over itself through the identity, the
atlas members are just the identity -/
@[simp, mfld_simps] lemma charted_space_self_atlas
  {H : Type*} [topological_space H] {e : local_homeomorph H H} :
  e ∈ atlas H H ↔ e = local_homeomorph.refl H :=
by simp [atlas, charted_space.atlas]

/-- In the model space, chart_at is always the identity -/
lemma chart_at_self_eq {H : Type*} [topological_space H] {x : H} :
  chart_at H x = local_homeomorph.refl H :=
by simpa using chart_mem_atlas H x

section

variables (H) [topological_space H] [topological_space M] [charted_space H M]

lemma mem_chart_target (x : M) : chart_at H x x ∈ (chart_at H x).target :=
(chart_at H x).map_source (mem_chart_source _ _)

/-- If a topological space admits an atlas with locally compact charts, then the space itself
is locally compact. -/
lemma charted_space.locally_compact [locally_compact_space H] : locally_compact_space M :=
begin
  have : ∀ (x : M), (𝓝 x).has_basis
      (λ s, s ∈ 𝓝 (chart_at H x x) ∧ is_compact s ∧ s ⊆ (chart_at H x).target)
      (λ s, (chart_at H x).symm '' s),
  { intro x,
    rw [← (chart_at H x).symm_map_nhds_eq (mem_chart_source H x)],
    exact ((compact_basis_nhds (chart_at H x x)).has_basis_self_subset
      (is_open.mem_nhds (chart_at H x).open_target (mem_chart_target H x))).map _ },
  refine locally_compact_space_of_has_basis this _,
  rintro x s ⟨h₁, h₂, h₃⟩,
  exact h₂.image_of_continuous_on ((chart_at H x).continuous_on_symm.mono h₃)
end

open topological_space

lemma charted_space.second_countable_of_countable_cover [second_countable_topology H]
  {s : set M} (hs : (⋃ x (hx : x ∈ s), (chart_at H x).source) = univ)
  (hsc : countable s) :
  second_countable_topology M :=
begin
  haveI : ∀ x : M, second_countable_topology (chart_at H x).source :=
    λ x, (chart_at H x).second_countable_topology_source,
  haveI := hsc.to_encodable,
  rw bUnion_eq_Union at hs,
  exact second_countable_topology_of_countable_cover (λ x : s, (chart_at H (x : M)).open_source) hs
end

lemma charted_space.second_countable_of_sigma_compact [second_countable_topology H]
  [sigma_compact_space M] :
  second_countable_topology M :=
begin
  obtain ⟨s, hsc, hsU⟩ : ∃ s, countable s ∧ (⋃ x (hx : x ∈ s), (chart_at H x).source) = univ :=
    countable_cover_nhds_of_sigma_compact
      (λ x : M, is_open.mem_nhds (chart_at H x).open_source (mem_chart_source H x)),
  exact charted_space.second_countable_of_countable_cover H hsU hsc
end

end

/-- For technical reasons we introduce two type tags:

* `model_prod H H'` is the same as `H × H'`;
* `model_pi H` is the same as `Π i, H i`, where `H : ι → Type*` and `ι` is a finite type.

In both cases the reason is the same, so we explain it only in the case of the product. A charted
space `M` with model `H` is a set of local charts from `M` to `H` covering the space. Every space is
registered as a charted space over itself, using the only chart `id`, in `manifold_model_space`. You
can also define a product of charted space `M` and `M'` (with model space `H × H'`) by taking the
products of the charts. Now, on `H × H'`, there are two charted space structures with model space
`H × H'` itself, the one coming from `manifold_model_space`, and the one coming from the product of
the two `manifold_model_space` on each component. They are equal, but not defeq (because the product
of `id` and `id` is not defeq to `id`), which is bad as we know. This expedient of renaming `H × H'`
solves this problem. -/
library_note "Manifold type tags"

/-- Same thing as `H × H'` We introduce it for technical reasons,
see note [Manifold type tags]. -/
def model_prod (H : Type*) (H' : Type*) := H × H'

/-- Same thing as `Π i, H i` We introduce it for technical reasons,
see note [Manifold type tags]. -/
def model_pi {ι : Type*} (H : ι → Type*) := Π i, H i

section
local attribute [reducible] model_prod

instance model_prod_inhabited [inhabited H] [inhabited H'] :
  inhabited (model_prod H H') :=
prod.inhabited

instance (H : Type*) [topological_space H] (H' : Type*) [topological_space H'] :
  topological_space (model_prod H H') :=
prod.topological_space

/- Next lemma shows up often when dealing with derivatives, register it as simp. -/
@[simp, mfld_simps] lemma model_prod_range_prod_id
  {H : Type*} {H' : Type*} {α : Type*} (f : H → α) :
  range (λ (p : model_prod H H'), (f p.1, p.2)) = set.prod (range f) univ :=
by rw prod_range_univ_eq

end

section

variables {ι : Type*} {Hi : ι → Type*}

instance model_pi_inhabited [Π i, inhabited (Hi i)] :
  inhabited (model_pi Hi) :=
pi.inhabited _

instance [Π i, topological_space (Hi i)] :
  topological_space (model_pi Hi) :=
Pi.topological_space

end

/-- The product of two charted spaces is naturally a charted space, with the canonical
construction of the atlas of product maps. -/
instance prod_charted_space (H : Type*) [topological_space H]
  (M : Type*) [topological_space M] [charted_space H M]
  (H' : Type*) [topological_space H']
  (M' : Type*) [topological_space M'] [charted_space H' M'] :
  charted_space (model_prod H H') (M × M') :=
{ atlas            := image2 local_homeomorph.prod (atlas H M) (atlas H' M'),
  chart_at         := λ x : M × M', (chart_at H x.1).prod (chart_at H' x.2),
  mem_chart_source := λ x, ⟨mem_chart_source _ _, mem_chart_source _ _⟩,
  chart_mem_atlas  := λ x, mem_image2_of_mem (chart_mem_atlas _ _) (chart_mem_atlas _ _) }

section prod_charted_space

variables [topological_space H] [topological_space M] [charted_space H M]
[topological_space H'] [topological_space M'] [charted_space H' M'] {x : M×M'}

@[simp, mfld_simps] lemma prod_charted_space_chart_at :
  (chart_at (model_prod H H') x) = (chart_at H x.fst).prod (chart_at H' x.snd) := rfl

end prod_charted_space

/-- The product of a finite family of charted spaces is naturally a charted space, with the
canonical construction of the atlas of finite product maps. -/
instance pi_charted_space {ι : Type*} [fintype ι] (H : ι → Type*) [Π i, topological_space (H i)]
  (M : ι → Type*) [Π i, topological_space (M i)] [Π i, charted_space (H i) (M i)] :
  charted_space (model_pi H) (Π i, M i) :=
{ atlas := local_homeomorph.pi '' (set.pi univ $ λ i, atlas (H i) (M i)),
  chart_at := λ f, local_homeomorph.pi $ λ i, chart_at (H i) (f i),
  mem_chart_source := λ f i hi, mem_chart_source (H i) (f i),
  chart_mem_atlas := λ f, mem_image_of_mem _ $ λ i hi, chart_mem_atlas (H i) (f i) }

@[simp, mfld_simps] lemma pi_charted_space_chart_at {ι : Type*} [fintype ι] (H : ι → Type*)
  [Π i, topological_space (H i)] (M : ι → Type*) [Π i, topological_space (M i)]
  [Π i, charted_space (H i) (M i)] (f : Π i, M i) :
  chart_at (model_pi H) f = local_homeomorph.pi (λ i, chart_at (H i) (f i)) := rfl

end charted_space

/-! ### Constructing a topology from an atlas -/

/-- Sometimes, one may want to construct a charted space structure on a space which does not yet
have a topological structure, where the topology would come from the charts. For this, one needs
charts that are only local equivs, and continuity properties for their composition.
This is formalised in `charted_space_core`. -/
@[nolint has_inhabited_instance]
structure charted_space_core (H : Type*) [topological_space H] (M : Type*) :=
(atlas            : set (local_equiv M H))
(chart_at         : M → local_equiv M H)
(mem_chart_source : ∀x, x ∈ (chart_at x).source)
(chart_mem_atlas  : ∀x, chart_at x ∈ atlas)
(open_source : ∀e e' : local_equiv M H, e ∈ atlas → e' ∈ atlas → is_open (e.symm.trans e').source)
(continuous_to_fun : ∀e e' : local_equiv M H, e ∈ atlas → e' ∈ atlas →
                       continuous_on (e.symm.trans e') (e.symm.trans e').source)

namespace charted_space_core

variables [topological_space H] (c : charted_space_core H M) {e : local_equiv M H}

/-- Topology generated by a set of charts on a Type. -/
protected def to_topological_space : topological_space M :=
topological_space.generate_from $ ⋃ (e : local_equiv M H) (he : e ∈ c.atlas)
  (s : set H) (s_open : is_open s), {e ⁻¹' s ∩ e.source}

lemma open_source' (he : e ∈ c.atlas) : @is_open M c.to_topological_space e.source :=
begin
  apply topological_space.generate_open.basic,
  simp only [exists_prop, mem_Union, mem_singleton_iff],
  refine ⟨e, he, univ, is_open_univ, _⟩,
  simp only [set.univ_inter, set.preimage_univ]
end

lemma open_target (he : e ∈ c.atlas) : is_open e.target :=
begin
  have E : e.target ∩ e.symm ⁻¹' e.source = e.target :=
  subset.antisymm (inter_subset_left _ _) (λx hx, ⟨hx,
    local_equiv.target_subset_preimage_source _ hx⟩),
  simpa [local_equiv.trans_source, E] using c.open_source e e he he
end

/-- An element of the atlas in a charted space without topology becomes a local homeomorphism
for the topology constructed from this atlas. The `local_homeomorph` version is given in this
definition. -/
protected def local_homeomorph (e : local_equiv M H) (he : e ∈ c.atlas) :
  @local_homeomorph M H c.to_topological_space _ :=
{ open_source := by convert c.open_source' he,
  open_target := by convert c.open_target he,
  continuous_to_fun := begin
    letI : topological_space M := c.to_topological_space,
    rw continuous_on_open_iff (c.open_source' he),
    assume s s_open,
    rw inter_comm,
    apply topological_space.generate_open.basic,
    simp only [exists_prop, mem_Union, mem_singleton_iff],
    exact ⟨e, he, ⟨s, s_open, rfl⟩⟩
  end,
  continuous_inv_fun := begin
    letI : topological_space M := c.to_topological_space,
    apply continuous_on_open_of_generate_from (c.open_target he),
    assume t ht,
    simp only [exists_prop, mem_Union, mem_singleton_iff] at ht,
    rcases ht with ⟨e', e'_atlas, s, s_open, ts⟩,
    rw ts,
    let f := e.symm.trans e',
    have : is_open (f ⁻¹' s ∩ f.source),
      by simpa [inter_comm] using (continuous_on_open_iff (c.open_source e e' he e'_atlas)).1
        (c.continuous_to_fun e e' he e'_atlas) s s_open,
    have A : e' ∘ e.symm ⁻¹' s ∩ (e.target ∩ e.symm ⁻¹' e'.source) =
             e.target ∩ (e' ∘ e.symm ⁻¹' s ∩ e.symm ⁻¹' e'.source),
      by { rw [← inter_assoc, ← inter_assoc], congr' 1, exact inter_comm _ _ },
    simpa [local_equiv.trans_source, preimage_inter, preimage_comp.symm, A] using this
  end,
  ..e }

/-- Given a charted space without topology, endow it with a genuine charted space structure with
respect to the topology constructed from the atlas. -/
def to_charted_space : @charted_space H _ M c.to_topological_space :=
{ atlas := ⋃ (e : local_equiv M H) (he : e ∈ c.atlas), {c.local_homeomorph e he},
  chart_at := λx, c.local_homeomorph (c.chart_at x) (c.chart_mem_atlas x),
  mem_chart_source := λx, c.mem_chart_source x,
  chart_mem_atlas := λx, begin
    simp only [mem_Union, mem_singleton_iff],
    exact ⟨c.chart_at x, c.chart_mem_atlas x, rfl⟩,
  end }

end charted_space_core


/-! ### Charted space with a given structure groupoid -/

section has_groupoid
variables [topological_space H] [topological_space M] [charted_space H M]

section
set_option old_structure_cmd true

/-- A charted space has an atlas in a groupoid `G` if the change of coordinates belong to the
groupoid -/
class has_groupoid {H : Type*} [topological_space H] (M : Type*) [topological_space M]
  [charted_space H M] (G : structure_groupoid H) : Prop :=
(compatible [] : ∀{e e' : local_homeomorph M H}, e ∈ atlas H M → e' ∈ atlas H M → e.symm ≫ₕ e' ∈ G)

end

/-- Reformulate in the `structure_groupoid` namespace the compatibility condition of charts in a
charted space admitting a structure groupoid, to make it more easily accessible with dot
notation. -/
lemma structure_groupoid.compatible {H : Type*} [topological_space H] (G : structure_groupoid H)
  {M : Type*} [topological_space M] [charted_space H M] [has_groupoid M G]
  {e e' : local_homeomorph M H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) :
  e.symm ≫ₕ e' ∈ G :=
has_groupoid.compatible G he he'

lemma has_groupoid_of_le {G₁ G₂ : structure_groupoid H} (h : has_groupoid M G₁) (hle : G₁ ≤ G₂) :
  has_groupoid M G₂ :=
⟨ λ e e' he he', hle ((h.compatible : _) he he') ⟩

lemma has_groupoid_of_pregroupoid (PG : pregroupoid H)
  (h : ∀{e e' : local_homeomorph M H}, e ∈ atlas H M → e' ∈ atlas H M
    → PG.property (e.symm ≫ₕ e') (e.symm ≫ₕ e').source) :
  has_groupoid M (PG.groupoid) :=
⟨assume e e' he he', mem_groupoid_of_pregroupoid.mpr ⟨h he he', h he' he⟩⟩

/-- The trivial charted space structure on the model space is compatible with any groupoid -/
instance has_groupoid_model_space (H : Type*) [topological_space H] (G : structure_groupoid H) :
  has_groupoid H G :=
{ compatible := λe e' he he', begin
    replace he : e ∈ atlas H H := he,
    replace he' : e' ∈ atlas H H := he',
    rw charted_space_self_atlas at he he',
    simp [he, he', structure_groupoid.id_mem]
  end }

/-- Any charted space structure is compatible with the groupoid of all local homeomorphisms -/
instance has_groupoid_continuous_groupoid : has_groupoid M (continuous_groupoid H) :=
⟨begin
  assume e e' he he',
  rw [continuous_groupoid, mem_groupoid_of_pregroupoid],
  simp only [and_self]
end⟩

section maximal_atlas

variables (M) (G : structure_groupoid H)

/-- Given a charted space admitting a structure groupoid, the maximal atlas associated to this
structure groupoid is the set of all local charts that are compatible with the atlas, i.e., such
that changing coordinates with an atlas member gives an element of the groupoid. -/
def structure_groupoid.maximal_atlas : set (local_homeomorph M H) :=
{e | ∀ e' ∈ atlas H M, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G}

variable {M}

/-- The elements of the atlas belong to the maximal atlas for any structure groupoid -/
lemma structure_groupoid.mem_maximal_atlas_of_mem_atlas [has_groupoid M G]
  {e : local_homeomorph M H} (he : e ∈ atlas H M) : e ∈ G.maximal_atlas M :=
λ e' he', ⟨G.compatible he he', G.compatible he' he⟩

lemma structure_groupoid.chart_mem_maximal_atlas [has_groupoid M G]
  (x : M) : chart_at H x ∈ G.maximal_atlas M :=
G.mem_maximal_atlas_of_mem_atlas (chart_mem_atlas H x)

variable {G}

lemma mem_maximal_atlas_iff {e : local_homeomorph M H} :
  e ∈ G.maximal_atlas M ↔ ∀ e' ∈ atlas H M, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G :=
iff.rfl

/-- Changing coordinates between two elements of the maximal atlas gives rise to an element
of the structure groupoid. -/
lemma structure_groupoid.compatible_of_mem_maximal_atlas {e e' : local_homeomorph M H}
  (he : e ∈ G.maximal_atlas M) (he' : e' ∈ G.maximal_atlas M) : e.symm ≫ₕ e' ∈ G :=
begin
  apply G.locality (λ x hx, _),
  set f := chart_at H (e.symm x) with hf,
  let s := e.target ∩ (e.symm ⁻¹' f.source),
  have hs : is_open s,
  { apply e.symm.continuous_to_fun.preimage_open_of_open; apply open_source },
  have xs : x ∈ s, by { dsimp at hx, simp [s, hx] },
  refine ⟨s, hs, xs, _⟩,
  have A : e.symm ≫ₕ f ∈ G := (mem_maximal_atlas_iff.1 he f (chart_mem_atlas _ _)).1,
  have B : f.symm ≫ₕ e' ∈ G := (mem_maximal_atlas_iff.1 he' f (chart_mem_atlas _ _)).2,
  have C : (e.symm ≫ₕ f) ≫ₕ (f.symm ≫ₕ e') ∈ G := G.trans A B,
  have D : (e.symm ≫ₕ f) ≫ₕ (f.symm ≫ₕ e') ≈ (e.symm ≫ₕ e').restr s := calc
    (e.symm ≫ₕ f) ≫ₕ (f.symm ≫ₕ e') = e.symm ≫ₕ (f ≫ₕ f.symm) ≫ₕ e' : by simp [trans_assoc]
    ... ≈ e.symm ≫ₕ (of_set f.source f.open_source) ≫ₕ e' :
      by simp [eq_on_source.trans', trans_self_symm]
    ... ≈ (e.symm ≫ₕ (of_set f.source f.open_source)) ≫ₕ e' : by simp [trans_assoc]
    ... ≈ (e.symm.restr s) ≫ₕ e' : by simp [s, trans_of_set']
    ... ≈ (e.symm ≫ₕ e').restr s : by simp [restr_trans],
  exact G.eq_on_source C (setoid.symm D),
end

variable (G)

/-- In the model space, the identity is in any maximal atlas. -/
lemma structure_groupoid.id_mem_maximal_atlas : local_homeomorph.refl H ∈ G.maximal_atlas H :=
G.mem_maximal_atlas_of_mem_atlas (by simp)

end maximal_atlas

section singleton
variables {α : Type*} [topological_space α]

namespace local_homeomorph

variable (e : local_homeomorph α H)

/-- If a single local homeomorphism `e` from a space `α` into `H` has source covering the whole
space `α`, then that local homeomorphism induces an `H`-charted space structure on `α`.
(This condition is equivalent to `e` being an open embedding of `α` into `H`; see
`open_embedding.singleton_charted_space`.) -/
def singleton_charted_space (h : e.source = set.univ) : charted_space H α :=
{ atlas := {e},
  chart_at := λ _, e,
  mem_chart_source := λ _, by simp only [h] with mfld_simps,
  chart_mem_atlas := λ _, by tauto }

@[simp, mfld_simps] lemma singleton_charted_space_chart_at_eq (h : e.source = set.univ) {x : α} :
  @chart_at H _ α _ (e.singleton_charted_space h) x = e := rfl

lemma singleton_charted_space_chart_at_source
  (h : e.source = set.univ) {x : α} :
  (@chart_at H _ α _ (e.singleton_charted_space h) x).source = set.univ := h

lemma singleton_charted_space_mem_atlas_eq (h : e.source = set.univ)
  (e' : local_homeomorph α H) (h' : e' ∈ (e.singleton_charted_space h).atlas) : e' = e := h'

/-- Given a local homeomorphism `e` from a space `α` into `H`, if its source covers the whole
space `α`, then the induced charted space structure on `α` is `has_groupoid G` for any structure
groupoid `G` which is closed under restrictions. -/
lemma singleton_has_groupoid (h : e.source = set.univ) (G : structure_groupoid H)
  [closed_under_restriction G] : @has_groupoid _ _ _ _ (e.singleton_charted_space h) G :=
{ compatible := begin
    intros e' e'' he' he'',
    rw e.singleton_charted_space_mem_atlas_eq h e' he',
    rw e.singleton_charted_space_mem_atlas_eq h e'' he'',
    refine G.eq_on_source _ e.trans_symm_self,
    have hle : id_restr_groupoid ≤ G := (closed_under_restriction_iff_id_le G).mp (by assumption),
    exact structure_groupoid.le_iff.mp hle _ (id_restr_groupoid_mem _),
  end }

end local_homeomorph

namespace open_embedding

variable [nonempty α]

/-- An open embedding of `α` into `H` induces an `H`-charted space structure on `α`.
See `local_homeomorph.singleton_charted_space` -/
def singleton_charted_space {f : α → H} (h : open_embedding f) :
  charted_space H α := (h.to_local_homeomorph f).singleton_charted_space (by simp)

lemma singleton_charted_space_chart_at_eq {f : α → H} (h : open_embedding f) {x : α} :
  ⇑(@chart_at H _ α _ (h.singleton_charted_space) x) = f := rfl

lemma singleton_has_groupoid {f : α → H} (h : open_embedding f)
  (G : structure_groupoid H) [closed_under_restriction G] :
  @has_groupoid _ _ _ _ h.singleton_charted_space G :=
(h.to_local_homeomorph f).singleton_has_groupoid (by simp) G

end open_embedding

end singleton

namespace topological_space.opens

open topological_space
variables (G : structure_groupoid H) [has_groupoid M G]
variables (s : opens M)

/-- An open subset of a charted space is naturally a charted space. -/
instance : charted_space H s :=
{ atlas := ⋃ (x : s), {@local_homeomorph.subtype_restr _ _ _ _ (chart_at H x.1) s ⟨x⟩},
  chart_at := λ x, @local_homeomorph.subtype_restr _ _ _ _ (chart_at H x.1) s ⟨x⟩,
  mem_chart_source := λ x, by { simp only with mfld_simps, exact (mem_chart_source H x.1) },
  chart_mem_atlas := λ x, by { simp only [mem_Union, mem_singleton_iff], use x } }

/-- If a groupoid `G` is `closed_under_restriction`, then an open subset of a space which is
`has_groupoid G` is naturally `has_groupoid G`. -/
instance [closed_under_restriction G] : has_groupoid s G :=
{ compatible := begin
    rintros e e' ⟨_, ⟨x, hc⟩, he⟩ ⟨_, ⟨x', hc'⟩, he'⟩,
    haveI : nonempty s := ⟨x⟩,
    simp only [hc.symm, mem_singleton_iff, subtype.val_eq_coe] at he,
    simp only [hc'.symm, mem_singleton_iff, subtype.val_eq_coe] at he',
    rw [he, he'],
    convert G.eq_on_source _
      (subtype_restr_symm_trans_subtype_restr s (chart_at H x) (chart_at H x')),
    apply closed_under_restriction',
    { exact G.compatible (chart_mem_atlas H x) (chart_mem_atlas H x') },
    { exact preimage_open_of_open_symm (chart_at H x) s.2 },
  end }

end topological_space.opens

/-! ### Structomorphisms -/

/-- A `G`-diffeomorphism between two charted spaces is a homeomorphism which, when read in the
charts, belongs to `G`. We avoid the word diffeomorph as it is too related to the smooth category,
and use structomorph instead. -/
@[nolint has_inhabited_instance]
structure structomorph (G : structure_groupoid H) (M : Type*) (M' : Type*)
  [topological_space M] [topological_space M'] [charted_space H M] [charted_space H M']
  extends homeomorph M M' :=
(mem_groupoid : ∀c : local_homeomorph M H, ∀c' : local_homeomorph M' H,
  c ∈ atlas H M → c' ∈ atlas H M' → c.symm ≫ₕ to_homeomorph.to_local_homeomorph ≫ₕ c' ∈ G)

variables [topological_space M'] [topological_space M'']
{G : structure_groupoid H} [charted_space H M'] [charted_space H M'']

/-- The identity is a diffeomorphism of any charted space, for any groupoid. -/
def structomorph.refl (M : Type*) [topological_space M] [charted_space H M]
  [has_groupoid M G] : structomorph G M M :=
{ mem_groupoid := λc c' hc hc', begin
    change (local_homeomorph.symm c) ≫ₕ (local_homeomorph.refl M) ≫ₕ c' ∈ G,
    rw local_homeomorph.refl_trans,
    exact has_groupoid.compatible G hc hc'
  end,
  ..homeomorph.refl M }

/-- The inverse of a structomorphism is a structomorphism -/
def structomorph.symm (e : structomorph G M M') : structomorph G M' M :=
{ mem_groupoid := begin
    assume c c' hc hc',
    have : (c'.symm ≫ₕ e.to_homeomorph.to_local_homeomorph ≫ₕ c).symm ∈ G :=
      G.symm (e.mem_groupoid c' c hc' hc),
    rwa [trans_symm_eq_symm_trans_symm, trans_symm_eq_symm_trans_symm, symm_symm, trans_assoc]
      at this,
  end,
  ..e.to_homeomorph.symm}

/-- The composition of structomorphisms is a structomorphism -/
def structomorph.trans (e : structomorph G M M') (e' : structomorph G M' M'') :
  structomorph G M M'' :=
{ mem_groupoid := begin
    /- Let c and c' be two charts in M and M''. We want to show that e' ∘ e is smooth in these
    charts, around any point x. For this, let y = e (c⁻¹ x), and consider a chart g around y.
    Then g ∘ e ∘ c⁻¹ and c' ∘ e' ∘ g⁻¹ are both smooth as e and e' are structomorphisms, so
    their composition is smooth, and it coincides with c' ∘ e' ∘ e ∘ c⁻¹ around x. -/
    assume c c' hc hc',
    refine G.locality (λx hx, _),
    let f₁ := e.to_homeomorph.to_local_homeomorph,
    let f₂ := e'.to_homeomorph.to_local_homeomorph,
    let f  := (e.to_homeomorph.trans e'.to_homeomorph).to_local_homeomorph,
    have feq : f = f₁ ≫ₕ f₂ := homeomorph.trans_to_local_homeomorph _ _,
    -- define the atlas g around y
    let y := (c.symm ≫ₕ f₁) x,
    let g := chart_at H y,
    have hg₁ := chart_mem_atlas H y,
    have hg₂ := mem_chart_source H y,
    let s := (c.symm ≫ₕ f₁).source ∩ (c.symm ≫ₕ f₁) ⁻¹' g.source,
    have open_s : is_open s,
      by apply (c.symm ≫ₕ f₁).continuous_to_fun.preimage_open_of_open; apply open_source,
    have : x ∈ s,
    { split,
      { simp only [trans_source, preimage_univ, inter_univ, homeomorph.to_local_homeomorph_source],
        rw trans_source at hx,
        exact hx.1 },
      { exact hg₂ } },
    refine ⟨s, open_s, this, _⟩,
    let F₁ := (c.symm ≫ₕ f₁ ≫ₕ g) ≫ₕ (g.symm ≫ₕ f₂ ≫ₕ c'),
    have A : F₁ ∈ G := G.trans (e.mem_groupoid c g hc hg₁) (e'.mem_groupoid g c' hg₁ hc'),
    let F₂ := (c.symm ≫ₕ f ≫ₕ c').restr s,
    have : F₁ ≈ F₂ := calc
      F₁ ≈ c.symm ≫ₕ f₁ ≫ₕ (g ≫ₕ g.symm) ≫ₕ f₂ ≫ₕ c' : by simp [F₁, trans_assoc]
      ... ≈ c.symm ≫ₕ f₁ ≫ₕ (of_set g.source g.open_source) ≫ₕ f₂ ≫ₕ c' :
        by simp [eq_on_source.trans', trans_self_symm g]
      ... ≈ ((c.symm ≫ₕ f₁) ≫ₕ (of_set g.source g.open_source)) ≫ₕ (f₂ ≫ₕ c') :
        by simp [trans_assoc]
      ... ≈ ((c.symm ≫ₕ f₁).restr s) ≫ₕ (f₂ ≫ₕ c') : by simp [s, trans_of_set']
      ... ≈ ((c.symm ≫ₕ f₁) ≫ₕ (f₂ ≫ₕ c')).restr s : by simp [restr_trans]
      ... ≈ (c.symm ≫ₕ (f₁ ≫ₕ f₂) ≫ₕ c').restr s : by simp [eq_on_source.restr, trans_assoc]
      ... ≈ F₂ : by simp [F₂, feq],
    have : F₂ ∈ G := G.eq_on_source A (setoid.symm this),
    exact this
  end,
  ..homeomorph.trans e.to_homeomorph e'.to_homeomorph }

end has_groupoid
