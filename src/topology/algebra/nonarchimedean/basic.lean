/-
Copyright (c) 2021 Ashwin Iyengar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Ashwin Iyengar, Patrick Massot
-/
import topology.algebra.ring
import topology.algebra.open_subgroup
import data.set.basic
import group_theory.subgroup

/-!
# Nonarchimedean Topology

In this file we set up the theory of nonarchimedean topological groups and rings.

A nonarchimedean group is a topological group whose topology admits a basis of
open neighborhoods of the identity element in the group consisting of open subgroups.
A nonarchimedean ring is a topological ring whose underlying topological (additive)
group is nonarchimedean.

## Definitions

- `nonarchimedean_add_group`: nonarchimedean additive group.
- `nonarchimedean_group`: nonarchimedean multiplicative group.
- `nonarchimedean_ring`: nonarchimedean ring.

-/

/-- An topological additive group is nonarchimedean if every neighborhood of 0
  contains an open subgroup. -/
class nonarchimedean_add_group (G : Type*)
  [add_group G] [topological_space G] extends topological_add_group G : Prop :=
(is_nonarchimedean : ∀ U ∈ nhds (0 : G), ∃ V : open_add_subgroup G, (V : set G) ⊆ U)

/-- A topological group is nonarchimedean if every neighborhood of 1 contains an open subgroup. -/
@[to_additive]
class nonarchimedean_group (G : Type*)
  [group G] [topological_space G] extends topological_group G : Prop :=
(is_nonarchimedean : ∀ U ∈ nhds (1 : G), ∃ V : open_subgroup G, (V : set G) ⊆ U)

/-- An topological ring is nonarchimedean if its underlying topological additive
  group is nonarchimedean. -/
class nonarchimedean_ring (R : Type*)
  [ring R] [topological_space R] extends topological_ring R : Prop :=
(is_nonarchimedean : ∀ U ∈ nhds (0 : R), ∃ V : open_add_subgroup R, (V : set R) ⊆ U)

/-- Every nonarchimedean ring is naturally a nonarchimedean additive group. -/
@[priority 100] -- see Note [lower instance priority]
instance nonarchimedean_ring.to_nonarchimedean_add_group
  (R : Type*) [ring R] [topological_space R] [t: nonarchimedean_ring R] :
nonarchimedean_add_group R := {..t}

namespace nonarchimedean_group

variables {G : Type*} [group G] [topological_space G] [nonarchimedean_group G]
variables {H : Type*} [group H] [topological_space H] [topological_group H]
variables {K : Type*} [group K] [topological_space K] [nonarchimedean_group K]

/-- If a topological group embeds into a nonarchimedean group, then it
  is nonarchimedean. -/
@[to_additive nonarchimedean_add_group.nonarchimedean_of_emb]
lemma nonarchimedean_of_emb (f : G →* H) (emb : open_embedding f) : nonarchimedean_group H :=
{ is_nonarchimedean := λ U hU, have h₁ : (f ⁻¹' U) ∈ nhds (1 : G), from
    by {apply emb.continuous.tendsto, rwa f.map_one},
  let ⟨V, hV⟩ := is_nonarchimedean (f ⁻¹' U) h₁ in
    ⟨{is_open' := emb.is_open_map _ V.is_open, ..subgroup.map f V},
      set.image_subset_iff.2 hV⟩ }

/-- An open neighborhood of the identity in the cartesian product of two nonarchimedean groups
  contains the cartesian product of an open neighborhood in each group. -/
@[to_additive nonarchimedean_add_group.prod_subset]
lemma prod_subset {U} (hU : U ∈ nhds (1 : G × K)) :
  ∃ (V : open_subgroup G) (W : open_subgroup K), (V : set G).prod (W : set K) ⊆ U :=
begin
  erw [nhds_prod_eq, filter.mem_prod_iff] at hU,
  rcases hU with ⟨U₁, hU₁, U₂, hU₂, h⟩,
  cases is_nonarchimedean _ hU₁ with V hV,
  cases is_nonarchimedean _ hU₂ with W hW,
  use V, use W,
  rw set.prod_subset_iff,
  intros x hX y hY,
  exact set.subset.trans (set.prod_mono hV hW) h (set.mem_sep hX hY),
end

/-- An open neighborhood of the identity in the cartesian square of a nonarchimedean group
  contains the cartesian square of an open neighborhood in the group. -/
@[to_additive nonarchimedean_add_group.prod_self_subset]
lemma prod_self_subset {U} (hU : U ∈ nhds (1 : G × G)) :
  ∃ (V : open_subgroup G), (V : set G).prod (V : set G) ⊆ U :=
let ⟨V, W, h⟩ := prod_subset hU in
  ⟨V ⊓ W, by {refine set.subset.trans (set.prod_mono _ _) ‹_›; simp}⟩

/-- The cartesian product of two nonarchimedean groups is nonarchimedean. -/
@[to_additive]
instance : nonarchimedean_group (G × K) :=
{ is_nonarchimedean := λ U hU, let ⟨V, W, h⟩ := prod_subset hU in ⟨V.prod W, ‹_›⟩ }

end nonarchimedean_group

namespace nonarchimedean_ring

open nonarchimedean_ring
open nonarchimedean_add_group

variables {R S : Type*}
variables [ring R] [topological_space R] [nonarchimedean_ring R]
variables [ring S] [topological_space S] [nonarchimedean_ring S]

/-- The cartesian product of two nonarchimedean rings is nonarchimedean. -/
instance : nonarchimedean_ring (R × S) :=
{ is_nonarchimedean := nonarchimedean_add_group.is_nonarchimedean }

/-- Given an open subgroup `U` and an element `r` of a nonarchimedean ring, there is an open
  subgroup `V` such that `r • V` is contained in `U`. -/
lemma left_mul_subset (U : open_add_subgroup R) (r : R) :
  ∃ V : open_add_subgroup R, r • (V : set R) ⊆ U :=
⟨U.comap (add_monoid_hom.mul_left r) (continuous_mul_left r),
  (U : set R).image_preimage_subset _⟩

/-- An open subgroup of a nonarchimedean ring contains the square of another one. -/
lemma mul_subset (U : open_add_subgroup R) :
  ∃ V : open_add_subgroup R, (V : set R) * V ⊆ U :=
let ⟨V, H⟩ := prod_self_subset (is_open.mem_nhds (is_open.preimage continuous_mul U.is_open)
  begin
    simpa only [set.mem_preimage, open_add_subgroup.mem_coe, prod.snd_zero, mul_zero]
      using U.zero_mem,
  end) in
begin
  use V,
  rintros v ⟨a, b, ha, hb, hv⟩,
  have hy := H (set.mk_mem_prod ha hb),
  simp only [set.mem_preimage, open_add_subgroup.mem_coe] at hy,
  rwa hv at hy
end

end nonarchimedean_ring
