/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import algebra.group.pi
import algebra.ring.basic

/-!
# Pi instances for ring

This file defines instances for ring, semiring and related structures on Pi Types
-/

namespace pi
universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

instance distrib [Π i, distrib $ f i] : distrib (Π i : I, f i) :=
by refine_struct { add := (+), mul := (*), .. }; tactic.pi_instance_derive_field

instance semiring [∀ i, semiring $ f i] : semiring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := 1, add := (+), mul := (*), .. };
  tactic.pi_instance_derive_field

instance comm_semiring [∀ i, comm_semiring $ f i] : comm_semiring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := 1, add := (+), mul := (*),  .. };
  tactic.pi_instance_derive_field

instance ring [∀ i, ring $ f i] : ring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := 1, add := (+), mul := (*),
  neg := has_neg.neg, .. }; tactic.pi_instance_derive_field

instance comm_ring [∀ i, comm_ring $ f i] : comm_ring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := 1, add := (+), mul := (*),
  neg := has_neg.neg, .. }; tactic.pi_instance_derive_field

/-- A family of ring homomorphisms `f a : γ →+* β a` defines a ring homomorphism
`pi.ring_hom f : γ →+* Π a, β a` given by `pi.ring_hom f x b = f b x`. -/
protected def ring_hom
  {α : Type u} {β : α → Type v} [R : Π a : α, semiring (β a)]
  {γ : Type w} [semiring γ] (f : Π a : α, γ →+* β a) :
  γ →+* Π a, β a :=
{ to_fun := λ x b, f b x,
  map_add' := λ x y, funext $ λ z, (f z).map_add x y,
  map_mul' := λ x y, funext $ λ z, (f z).map_mul x y,
  map_one' := funext $ λ z, (f z).map_one,
  map_zero' := funext $ λ z, (f z).map_zero }

@[simp] lemma ring_hom_apply
  {α : Type u} {β : α → Type v} [R : Π a : α, semiring (β a)]
  {γ : Type w} [semiring γ] (f : Π a : α, γ →+* β a) (g) (a) :
  pi.ring_hom f g a = f a g :=
rfl

end pi

section ring_hom

variable {I : Type*}     -- The indexing type
variable (f : I → Type*) -- The family of types already equipped with instances
variables [Π i, semiring (f i)]

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism. -/
def ring_hom.apply (i : I) : (Π i, f i) →+* f i :=
{ ..(monoid_hom.apply f i),
  ..(add_monoid_hom.apply f i) }

@[simp]
lemma ring_hom.apply_apply (i : I) (g : Π i, f i) : (ring_hom.apply f i) g = g i := rfl

end ring_hom
