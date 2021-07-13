/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.direct_sum
/-!
# Internal direct sums

The theory of abelian groups `A` equipped with an indexed family
of submodules `G i` for `i : ι`, such that the induced map
`⨁ i, G i →+ A` is an isomorphism of groups.

Variants: abelian monoids with a family of submonoids, R-modules with a family
of sub-R-modules.
-/

namespace direct_sum

open_locale direct_sum

variables {ι : Type*}

/-- The `direct_sum` formed by a collection of `add_submonoid`s of `M` is said to be internal if the
canonical map `(⨁ i, A i) →+ M` is bijective.

See `direct_sum.add_subgroup_is_internal` for the same statement about `add_subgroup`s. -/
def add_submonoid_is_internal {M : Type*} [decidable_eq ι] [add_comm_monoid M]
  (A : ι → add_submonoid M) : Prop :=
function.bijective (direct_sum.to_add_monoid (λ i, (A i).subtype) : (⨁ i, A i) →+ M)

/-- The `direct_sum` formed by a collection of `add_subgroup`s of `M` is said to be internal if the
canonical map `(⨁ i, A i) →+ M` is bijective.

See `direct_sum.submodule_is_internal` for the same statement about `submodules`s. -/
def add_subgroup_is_internal {M : Type*} [decidable_eq ι] [add_comm_group M]
  (A : ι → add_subgroup M) : Prop :=
function.bijective (direct_sum.to_add_monoid (λ i, (A i).subtype) : (⨁ i, A i) →+ M)

lemma add_subgroup_is_internal.to_add_submonoid
  {M : Type*} [decidable_eq ι] [add_comm_group M] (A : ι → add_subgroup M) :
  add_subgroup_is_internal A ↔
    add_submonoid_is_internal (λ i, (A i).to_add_submonoid) :=
iff.rfl

end direct_sum
