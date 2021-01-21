/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import topology.opens
import category_theory.sites.pretopology
import category_theory.limits.lattice

/-!
# Grothendieck topology on a topological space

Define the Grothendieck topology and the pretopology associated to a topological space, and show
that the pretopology induces the topology.

The covering (pre)sieves on `X` are those for which the union of domains contains `X`.

## Tags

site, Grothendieck topology, space

## References

* [https://ncatlab.org/nlab/show/Grothendieck+topology][nlab]
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We define the two separately, rather than defining the Grothendieck topology as that generated
by the pretopology for the purpose of having nice definitional properties for the sieves.
-/

universe u

namespace opens
variables (T : Type u) [topological_space T]

open category_theory topological_space category_theory.limits

/-- The Grothendieck topology associated to a topological space. -/
def grothendieck_topology : grothendieck_topology (opens T) :=
{ sieves := λ X S, ∀ x ∈ X, ∃ U (f : U ⟶ X), S f ∧ x ∈ U,
  top_mem' := λ X x hx, ⟨_, 𝟙 _, trivial, hx⟩,
  pullback_stable' := λ X Y S f hf y hy,
  begin
    rcases hf y (le_of_hom f hy) with ⟨U, g, hg, hU⟩,
    refine ⟨U ⊓ Y, hom_of_le inf_le_right, _, hU, hy⟩,
    apply S.downward_closed hg (hom_of_le inf_le_left),
  end,
  transitive' := λ X S hS R hR x hx,
  begin
    rcases hS x hx with ⟨U, f, hf, hU⟩,
    rcases hR hf _ hU with ⟨V, g, hg, hV⟩,
    exact ⟨_, g ≫ f, hg, hV⟩,
  end }

/-- The Grothendieck pretopology associated to a topological space. -/
def pretopology : pretopology (opens T) :=
{ coverings := λ X R, ∀ x ∈ X, ∃ U (f : U ⟶ X), R f ∧ x ∈ U,
  has_isos := λ X Y f i x hx,
        by exactI ⟨_, _, presieve.singleton_self _, le_of_hom (inv f) hx⟩,
  pullbacks := λ X Y f S hS x hx,
  begin
    rcases hS _ (le_of_hom f hx) with ⟨U, g, hg, hU⟩,
    refine ⟨_, _, pullback_arrows.mk _ _ hg, _⟩,
    have : U ⊓ Y ≤ pullback g f,
      refine le_of_hom (pullback.lift (hom_of_le inf_le_left) (hom_of_le inf_le_right) rfl),
    apply this ⟨hU, hx⟩,
  end,
  transitive := λ X S Ti hS hTi x hx,
  begin
    rcases hS x hx with ⟨U, f, hf, hU⟩,
    rcases hTi f hf x hU with ⟨V, g, hg, hV⟩,
    exact ⟨_, _, ⟨_, g, f, hf, hg, rfl⟩, hV⟩,
  end }

/--
The pretopology associated to a space induces the Grothendieck topology associated to the space.
-/
@[simp]
lemma pretopology_to_grothendieck :
  pretopology.to_grothendieck _ (opens.pretopology T) = opens.grothendieck_topology T :=
begin
  apply le_antisymm,
  { rintro X S ⟨R, hR, RS⟩ x hx,
    rcases hR x hx with ⟨U, f, hf, hU⟩,
    exact ⟨_, f, RS _ hf, hU⟩ },
  { intros X S hS,
    exact ⟨S, hS, le_refl _⟩ }
end

end opens
