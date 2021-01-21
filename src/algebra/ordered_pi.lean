/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import algebra.group.pi
import algebra.ordered_group
/-!
# Pi instances for ordered groups and monoids

This file defines instances for ordered group, monoid, and related structures on Pi types.
-/

universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

namespace pi

@[to_additive]
instance ordered_cancel_comm_monoid [∀ i, ordered_cancel_comm_monoid $ f i] :
  ordered_cancel_comm_monoid (Π i : I, f i) :=
by refine_struct { mul := (*), one := (1 : Π i, f i), le := (≤), lt := (<), .. pi.partial_order };
  tactic.pi_instance_derive_field

@[to_additive]
instance ordered_comm_group [∀ i, ordered_comm_group $ f i] :
  ordered_comm_group (Π i : I, f i) :=
{ mul_le_mul_left := λ x y hxy c i, mul_le_mul_left' (hxy i) _,
  ..pi.comm_group,
  ..pi.partial_order }

end pi
