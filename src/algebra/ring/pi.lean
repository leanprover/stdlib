import tactic.pi_instances algebra.group.pi algebra.ring.basic

namespace pi
universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

instance mul_zero_class [Π i, mul_zero_class $ f i] : mul_zero_class (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

instance distrib [Π i, distrib $ f i] : distrib (Π i : I, f i) :=
by refine_struct { add := (+), mul := (*), .. }; tactic.pi_instance_derive_field

instance semiring [∀ i, semiring $ f i] : semiring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := 1, add := (+), mul := (*), .. };
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

-- instance is_ring_hom_pi
--   {α : Type u} {β : α → Type v} [R : Π a : α, ring (β a)]
--   {γ : Type w} [ring γ]
--   (f : Π a : α, γ → β a) [Rh : Π a : α, is_ring_hom (f a)] :
--   is_ring_hom (λ x b, f b x) :=
-- (show γ →+* Π a, β a, from pi.ring_hom (λ a, ring_hom.of (f a))).is_ring_hom

end pi

section ring_hom

variable {I : Type*}     -- The indexing type
variable (f : I → Type*) -- The family of types already equipped with instances
variables [Π i, semiring (f i)]

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid homomorphism. -/
def ring_hom.apply (i : I) : (Π i, f i) →+* f i :=
{ ..(monoid_hom.apply f i),
  ..(add_monoid_hom.apply f i) }

@[simp]
lemma ring_hom.apply_apply (i : I) (g : Π i, f i) : (ring_hom.apply f i) g = g i := rfl

end ring_hom
