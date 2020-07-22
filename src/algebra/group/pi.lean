import algebra.ordered_group tactic.pi_instances

universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

namespace pi

@[to_additive] instance has_one [∀ i, has_one $ f i] : has_one (Π i : I, f i) := ⟨λ _, 1⟩
@[simp, to_additive] lemma one_apply [∀ i, has_one $ f i] : (1 : Π i, f i) i = 1 := rfl

@[to_additive]
instance has_mul [∀ i, has_mul $ f i] : has_mul (Π i : I, f i) := ⟨λ f g i, f i * g i⟩
@[simp, to_additive] lemma mul_apply [∀ i, has_mul $ f i] : (x * y) i = x i * y i := rfl

@[to_additive] instance has_inv [∀ i, has_inv $ f i] : has_inv (Π i : I, f i) := ⟨λ f i, (f i)⁻¹⟩
@[simp, to_additive] lemma inv_apply [∀ i, has_inv $ f i] : x⁻¹ i = (x i)⁻¹ := rfl

@[to_additive add_semigroup]
instance semigroup [∀ i, semigroup $ f i] : semigroup (Π i : I, f i) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive add_comm_semigroup]
instance comm_semigroup [∀ i, comm_semigroup $ f i] : comm_semigroup (Π i : I, f i) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive add_monoid]
instance monoid [∀ i, monoid $ f i] : monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive add_comm_monoid]
instance comm_monoid [∀ i, comm_monoid $ f i] : comm_monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive add_group]
instance group [∀ i, group $ f i] : group (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, .. };
  tactic.pi_instance_derive_field

@[simp] lemma sub_apply [∀ i, add_group $ f i] : (x - y) i = x i - y i := rfl

@[to_additive add_comm_group]
instance comm_group [∀ i, comm_group $ f i] : comm_group (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, .. };
  tactic.pi_instance_derive_field

@[to_additive add_left_cancel_semigroup]
instance left_cancel_semigroup [∀ i, left_cancel_semigroup $ f i] :
  left_cancel_semigroup (Π i : I, f i) :=
by refine_struct { mul := (*) }; tactic.pi_instance_derive_field

@[to_additive add_right_cancel_semigroup]
instance right_cancel_semigroup [∀ i, right_cancel_semigroup $ f i] :
  right_cancel_semigroup (Π i : I, f i) :=
by refine_struct { mul := (*) }; tactic.pi_instance_derive_field

@[to_additive ordered_cancel_add_comm_monoid]
instance ordered_cancel_comm_monoid [∀ i, ordered_cancel_comm_monoid $ f i] :
  ordered_cancel_comm_monoid (Π i : I, f i) :=
by refine_struct { mul := (*), one := (1 : Π i, f i), le := (≤), lt := (<), .. pi.partial_order };
  tactic.pi_instance_derive_field

@[to_additive ordered_add_comm_group]
instance ordered_comm_group [∀ i, ordered_comm_group $ f i] :
  ordered_comm_group (Π i : I, f i) :=
{ mul_le_mul_left := λ x y hxy c i, mul_le_mul_left' (hxy i) _,
  ..pi.comm_group,
  ..pi.partial_order }

variables [decidable_eq I]
variables [Π i, has_zero (f i)]

/-- The function supported at `i`, with value `x` there. -/
def single (i : I) (x : f i) : Π i, f i :=
λ i', if h : i' = i then (by { subst h, exact x }) else 0

@[simp]
lemma single_eq_same (i : I) (x : f i) : single i x i = x :=
begin
  dsimp [single],
  split_ifs,
  { refl, },
  { exfalso, exact h rfl, }
end

@[simp]
lemma single_eq_of_ne {i i' : I} (h : i' ≠ i) (x : f i) : single i x i' = 0 :=
begin
  dsimp [single],
  split_ifs with h',
  { exfalso, exact h h', },
  { refl, }
end

end pi

section monoid_hom

variables (f) [Π i, monoid (f i)]

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism. -/
@[to_additive "Evaluation of functions into an indexed collection of additive monoids at a point
is an additive monoid homomorphism."]
def monoid_hom.apply (i : I) : (Π i, f i) →* f i :=
{ to_fun := λ g, g i,
  map_one' := rfl,
  map_mul' := λ x y, rfl, }

@[simp, to_additive]
lemma monoid_hom.apply_apply (i : I) (g : Π i, f i) :
  (monoid_hom.apply f i) g = g i := rfl

end monoid_hom

section add_monoid_single
variables [decidable_eq I] (f) [Π i, add_monoid (f i)]
open pi

/-- The additive monoid homomorphism including a single additive monoid
into a dependent family of additive monoids, as functions supported at a point. -/
def add_monoid_hom.single (i : I) : f i →+ Π i, f i :=
{ to_fun := λ x, single i x,
  map_zero' :=
  begin
    ext i', by_cases h : i' = i,
    { subst h, simp only [single_eq_same], refl, },
    { simp only [h, single_eq_of_ne, ne.def, not_false_iff], refl, },
  end,
  map_add' := λ x y,
  begin
    ext i', by_cases h : i' = i,
    -- FIXME in the next two `simp only`s,
    -- it would be really nice to not have to provide the arguments to `add_apply`.
    { subst h, simp only [single_eq_same, add_apply (single i' x) (single i' y) i'], },
    { simp only [h, add_zero, single_eq_of_ne,
        add_apply (single i x) (single i y) i', ne.def, not_false_iff], },
  end, }

@[simp]
lemma add_monoid_hom.single_apply {i : I} (x : f i) :
  (add_monoid_hom.single f i) x = single i x := rfl

end add_monoid_single
