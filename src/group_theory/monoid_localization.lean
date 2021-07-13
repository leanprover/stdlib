/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import group_theory.congruence
import group_theory.submonoid
import algebra.group.units
import algebra.punit_instances

/-!
# Localizations of commutative monoids

Localizing a commutative ring at one of its submonoids does not rely on the ring's addition, so
we can generalize localizations to commutative monoids.

We characterize the localization of a commutative monoid `M` at a submonoid `S` up to
isomorphism; that is, a commutative monoid `N` is the localization of `M` at `S` iff we can find a
monoid homomorphism `f : M →* N` satisfying 3 properties:
1. For all `y ∈ S`, `f y` is a unit;
2. For all `z : N`, there exists `(x, y) : M × S` such that `z * f y = f x`;
3. For all `x, y : M`, `f x = f y` iff there exists `c ∈ S` such that `x * c = y * c`.

Given such a localization map `f : M →* N`, we can define the surjection
`localization_map.mk'` sending `(x, y) : M × S` to `f x * (f y)⁻¹`, and
`localization_map.lift`, the homomorphism from `N` induced by a homomorphism from `M` which maps
elements of `S` to invertible elements of the codomain. Similarly, given commutative monoids
`P, Q`, a submonoid `T` of `P` and a localization map for `T` from `P` to `Q`, then a homomorphism
`g : M →* P` such that `g(S) ⊆ T` induces a homomorphism of localizations,
`localization_map.map`, from `N` to `Q`.
We treat the special case of localizing away from an element in the sections `away_map` and `away`.

We also define the quotient of `M × S` by the unique congruence relation (equivalence relation
preserving a binary operation) `r` such that for any other congruence relation `s` on `M × S`
satisfying '`∀ y ∈ S`, `(1, 1) ∼ (y, y)` under `s`', we have that `(x₁, y₁) ∼ (x₂, y₂)` by `s`
whenever `(x₁, y₁) ∼ (x₂, y₂)` by `r`. We show this relation is equivalent to the standard
localization relation.
This defines the localization as a quotient type, `localization`, but the majority of
subsequent lemmas in the file are given in terms of localizations up to isomorphism, using maps
which satisfy the characteristic predicate.

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

The infimum form of the localization congruence relation is chosen as 'canonical' here, since it
shortens some proofs.

To apply a localization map `f` as a function, we use `f.to_map`, as coercions don't work well for
this structure.

To reason about the localization as a quotient type, use `mk_eq_monoid_of_mk'` and associated
lemmas. These show the quotient map `mk : M → S → localization S` equals the
surjection `localization_map.mk'` induced by the map
`monoid_of : localization_map S (localization S)` (where `of` establishes the
localization as a quotient type satisfies the characteristic predicate). The lemma
`mk_eq_monoid_of_mk'` hence gives you access to the results in the rest of the file, which are
about the `localization_map.mk'` induced by any localization map.

## Tags
localization, monoid localization, quotient monoid, congruence relation, characteristic predicate,
commutative monoid
-/
set_option old_structure_cmd true
namespace add_submonoid
variables {M : Type*} [add_comm_monoid M] (S : add_submonoid M) (N : Type*) [add_comm_monoid N]

/-- The type of add_monoid homomorphisms satisfying the characteristic predicate: if `f : M →+ N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
@[nolint has_inhabited_instance] structure localization_map
  extends add_monoid_hom M N :=
(map_add_units' : ∀ y : S, is_add_unit (to_fun y))
(surj' : ∀ z : N, ∃ x : M × S, z + to_fun x.2 = to_fun x.1)
(eq_iff_exists' : ∀ x y, to_fun x = to_fun y ↔ ∃ c : S, x + c = y + c)

/-- The add_monoid hom underlying a `localization_map` of `add_comm_monoid`s. -/
add_decl_doc localization_map.to_add_monoid_hom

end add_submonoid

variables {M : Type*} [comm_monoid M] (S : submonoid M) (N : Type*) [comm_monoid N]
          {P : Type*} [comm_monoid P]

namespace submonoid

/-- The type of monoid homomorphisms satisfying the characteristic predicate: if `f : M →* N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
@[nolint has_inhabited_instance] structure localization_map
extends monoid_hom M N :=
(map_units' : ∀ y : S, is_unit (to_fun y))
(surj' : ∀ z : N, ∃ x : M × S, z * to_fun x.2 = to_fun x.1)
(eq_iff_exists' : ∀ x y, to_fun x = to_fun y ↔ ∃ c : S, x * c = y * c)

attribute [to_additive add_submonoid.localization_map] submonoid.localization_map
attribute [to_additive add_submonoid.localization_map.to_add_monoid_hom]
  submonoid.localization_map.to_monoid_hom

/-- The monoid hom underlying a `localization_map`. -/
add_decl_doc localization_map.to_monoid_hom

end submonoid
namespace localization
run_cmd to_additive.map_namespace `localization `add_localization

/-- The congruence relation on `M × S`, `M` a `comm_monoid` and `S` a submonoid of `M`, whose
quotient is the localization of `M` at `S`, defined as the unique congruence relation on
`M × S` such that for any other congruence relation `s` on `M × S` where for all `y ∈ S`,
`(1, 1) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
`(x₁, y₁) ∼ (x₂, y₂)` by `s`. -/
@[to_additive "The congruence relation on `M × S`, `M` an `add_comm_monoid` and `S`
an `add_submonoid` of `M`, whose quotient is the localization of `M` at `S`, defined as the unique
congruence relation on `M × S` such that for any other congruence relation `s` on `M × S` where
for all `y ∈ S`, `(0, 0) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
`(x₁, y₁) ∼ (x₂, y₂)` by `s`."]
def r (S : submonoid M) : con (M × S) :=
Inf {c | ∀ y : S, c 1 (y, y)}

/-- An alternate form of the congruence relation on `M × S`, `M` a `comm_monoid` and `S` a
submonoid of `M`, whose quotient is the localization of `M` at `S`. -/
@[to_additive "An alternate form of the congruence relation on `M × S`, `M` a `comm_monoid` and
`S` a submonoid of `M`, whose quotient is the localization of `M` at `S`."]
def r' : con (M × S) :=
begin
  refine { r := λ a b : M × S, ∃ c : S, a.1 * b.2 * c = b.1 * a.2 * c,
    iseqv := ⟨λ a, ⟨1, rfl⟩, λ a b ⟨c, hc⟩, ⟨c, hc.symm⟩, _⟩,
    .. },
  { rintros a b c ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩,
    use b.2 * t₁ * t₂,
    simp only [submonoid.coe_mul],
    calc a.1 * c.2 * (b.2 * t₁ * t₂) = a.1 * b.2 * t₁ * c.2 * t₂ : by ac_refl
    ... = b.1 * c.2 * t₂ * a.2 * t₁ : by { rw ht₁, ac_refl }
    ... = c.1 * a.2 * (b.2 * t₁ * t₂) : by { rw ht₂, ac_refl } },
  { rintros a b c d ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩,
    use t₁ * t₂,
    calc (a.1 * c.1) * (b.2 * d.2) * (t₁ * t₂) = (a.1 * b.2 * t₁) * (c.1 * d.2 * t₂) :
      by ac_refl
    ... = (b.1 * d.1) * (a.2 * c.2) * (t₁ * t₂) : by { rw [ht₁, ht₂], ac_refl } }
end

/-- The congruence relation used to localize a `comm_monoid` at a submonoid can be expressed
equivalently as an infimum (see `localization.r`) or explicitly
(see `localization.r'`). -/
@[to_additive "The additive congruence relation used to localize an `add_comm_monoid` at a
submonoid can be expressed equivalently as an infimum (see `add_localization.r`) or
explicitly (see `add_localization.r'`)."]
theorem r_eq_r' : r S = r' S :=
le_antisymm (Inf_le $ λ _, ⟨1, by simp⟩) $
  le_Inf $ λ b H ⟨p, q⟩ y ⟨t, ht⟩,
    begin
      rw [← mul_one (p, q), ← mul_one y],
      refine b.trans (b.mul (b.refl _) (H (y.2 * t))) _,
      convert b.symm (b.mul (b.refl y) (H (q * t))) using 1,
      rw [prod.mk_mul_mk, submonoid.coe_mul, ← mul_assoc, ht, mul_left_comm, mul_assoc],
      refl
    end

variables {S}

@[to_additive]
lemma r_iff_exists {x y : M × S} : r S x y ↔ ∃ c : S, x.1 * y.2 * c = y.1 * x.2 * c :=
by rw r_eq_r' S; refl

end localization

/-- The localization of a `comm_monoid` at one of its submonoids (as a quotient type). -/
@[to_additive add_localization "The localization of an `add_comm_monoid` at one
of its submonoids (as a quotient type)."]
def localization := (localization.r S).quotient

namespace localization

@[to_additive] instance inhabited :
  inhabited (localization S) :=
con.quotient.inhabited

@[to_additive] instance : comm_monoid (localization S) :=
(r S).comm_monoid

variables {S}

/-- Given a `comm_monoid` `M` and submonoid `S`, `mk` sends `x : M`, `y ∈ S` to the equivalence
class of `(x, y)` in the localization of `M` at `S`. -/
@[to_additive "Given an `add_comm_monoid` `M` and submonoid `S`, `mk` sends `x : M`, `y ∈ S` to
the equivalence class of `(x, y)` in the localization of `M` at `S`."]
def mk (x : M) (y : S) : localization S := (r S).mk' (x, y)

@[elab_as_eliminator, to_additive]
theorem ind {p : localization S → Prop}
  (H : ∀ (y : M × S), p (mk y.1 y.2)) (x) : p x :=
by rcases x; convert H x; exact prod.mk.eta.symm

@[elab_as_eliminator, to_additive]
theorem induction_on {p : localization S → Prop} (x)
  (H : ∀ (y : M × S), p (mk y.1 y.2)) : p x := ind H x

@[elab_as_eliminator, to_additive]
theorem induction_on₂ {p : localization S → localization S → Prop} (x y)
  (H : ∀ (x y : M × S), p (mk x.1 x.2) (mk y.1 y.2)) : p x y :=
induction_on x $ λ x, induction_on y $ H x

@[elab_as_eliminator, to_additive]
theorem induction_on₃
  {p : localization S → localization S → localization S → Prop} (x y z)
  (H : ∀ (x y z : M × S), p (mk x.1 x.2) (mk y.1 y.2) (mk z.1 z.2)) : p x y z :=
induction_on₂ x y $ λ x y, induction_on z $ H x y

@[to_additive] lemma one_rel (y : S) : r S 1 (y, y) := λ b hb, hb y

@[to_additive] theorem r_of_eq {x y : M × S} (h : y.1 * x.2 = x.1 * y.2) : r S x y :=
r_iff_exists.2 ⟨1, by rw h⟩

end localization

variables {S N}

namespace monoid_hom
/-- Makes a localization map from a `comm_monoid` hom satisfying the characteristic predicate. -/
@[to_additive "Makes a localization map from an `add_comm_monoid` hom satisfying the characteristic
predicate."]
def to_localization_map (f : M →* N) (H1 : ∀ y : S, is_unit (f y))
  (H2 : ∀ z, ∃ x : M × S, z * f x.2 = f x.1) (H3 : ∀ x y, f x = f y ↔ ∃ c : S, x * c = y * c) :
  submonoid.localization_map S N :=
{ map_units' := H1,
  surj' := H2,
  eq_iff_exists' := H3,
  .. f }

end monoid_hom
namespace submonoid
namespace localization_map

/-- Short for `to_monoid_hom`; used to apply a localization map as a function. -/
@[to_additive "Short for `to_add_monoid_hom`; used to apply a localization map as a function."]
abbreviation to_map (f : localization_map S N) := f.to_monoid_hom

@[to_additive, ext] lemma ext {f g : localization_map S N} (h : ∀ x, f.to_map x = g.to_map x) :
  f = g :=
by cases f; cases g; simp only; exact funext h

attribute [ext] add_submonoid.localization_map.ext

@[to_additive] lemma ext_iff {f g : localization_map S N} :
  f = g ↔ ∀ x, f.to_map x = g.to_map x :=
⟨λ h x, h ▸ rfl, ext⟩

@[to_additive] lemma to_map_injective :
  function.injective (@localization_map.to_map _ _ S N _) :=
λ _ _ h, ext $ monoid_hom.ext_iff.1 h

@[to_additive] lemma map_units (f : localization_map S N) (y : S) :
  is_unit (f.to_map y) := f.4 y

@[to_additive] lemma surj (f : localization_map S N) (z : N) :
  ∃ x : M × S, z * f.to_map x.2 = f.to_map x.1 := f.5 z

@[to_additive] lemma eq_iff_exists (f : localization_map S N) {x y} :
  f.to_map x = f.to_map y ↔ ∃ c : S, x * c = y * c := f.6 x y

/-- Given a localization map `f : M →* N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`. -/
@[to_additive "Given a localization map `f : M →+ N`, a section function sending `z : N`
to some `(x, y) : M × S` such that `f x - f y = z`."]
noncomputable def sec (f : localization_map S N) (z : N) : M × S :=
classical.some $ f.surj z

@[to_additive] lemma sec_spec {f : localization_map S N} (z : N) :
  z * f.to_map (f.sec z).2 = f.to_map (f.sec z).1 :=
classical.some_spec $ f.surj z

@[to_additive] lemma sec_spec' {f : localization_map S N} (z : N) :
  f.to_map (f.sec z).1 = f.to_map (f.sec z).2 * z :=
by rw [mul_comm, sec_spec]

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
`w : M, z : N` and `y ∈ S`, we have `w * (f y)⁻¹ = z ↔ w = f y * z`. -/
@[to_additive "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that
`f(S) ⊆ add_units N`, for all `w : M, z : N` and `y ∈ S`, we have `w - f y = z ↔ w = f y + z`."]
lemma mul_inv_left {f : M →* N} (h : ∀ y : S, is_unit (f y))
  (y : S) (w z) : w * ↑(is_unit.lift_right (f.mrestrict S) h y)⁻¹ = z ↔ w = f y * z :=
by rw mul_comm; convert units.inv_mul_eq_iff_eq_mul _;
  exact (is_unit.coe_lift_right (f.mrestrict S) h _).symm

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
`w : M, z : N` and `y ∈ S`, we have `z = w * (f y)⁻¹ ↔ z * f y = w`. -/
@[to_additive "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that
`f(S) ⊆ add_units N`, for all `w : M, z : N` and `y ∈ S`, we have `z = w - f y ↔ z + f y = w`."]
lemma mul_inv_right {f : M →* N} (h : ∀ y : S, is_unit (f y))
  (y : S) (w z) : z = w * ↑(is_unit.lift_right (f.mrestrict S) h y)⁻¹ ↔ z * f y = w :=
by rw [eq_comm, mul_inv_left h, mul_comm, eq_comm]

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that
`f(S) ⊆ units N`, for all `x₁ x₂ : M` and `y₁, y₂ ∈ S`, we have
`f x₁ * (f y₁)⁻¹ = f x₂ * (f y₂)⁻¹ ↔ f (x₁ * y₂) = f (x₂ * y₁)`. -/
@[simp, to_additive "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that
`f(S) ⊆ add_units N`, for all `x₁ x₂ : M` and `y₁, y₂ ∈ S`, we have
`f x₁ - f y₁ = f x₂ - f y₂ ↔ f (x₁ + y₂) = f (x₂ + y₁)`."]
lemma mul_inv {f : M →* N} (h : ∀ y : S, is_unit (f y)) {x₁ x₂} {y₁ y₂ : S} :
  f x₁ * ↑(is_unit.lift_right (f.mrestrict S) h y₁)⁻¹ =
    f x₂ * ↑(is_unit.lift_right (f.mrestrict S) h y₂)⁻¹ ↔ f (x₁ * y₂) = f (x₂ * y₁) :=
by rw [mul_inv_right h, mul_assoc, mul_comm _ (f y₂), ←mul_assoc, mul_inv_left h, mul_comm x₂,
  f.map_mul, f.map_mul]

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
`y, z ∈ S`, we have `(f y)⁻¹ = (f z)⁻¹ → f y = f z`. -/
@[to_additive "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that
`f(S) ⊆ add_units N`, for all `y, z ∈ S`, we have `- (f y) = - (f z) → f y = f z`."]
lemma inv_inj {f : M →* N} (hf : ∀ y : S, is_unit (f y)) {y z}
  (h : (is_unit.lift_right (f.mrestrict S) hf y)⁻¹ = (is_unit.lift_right (f.mrestrict S) hf z)⁻¹) :
  f y = f z :=
by rw [←mul_one (f y), eq_comm, ←mul_inv_left hf y (f z) 1, h];
  convert units.inv_mul _; exact (is_unit.coe_lift_right (f.mrestrict S) hf _).symm

/-- Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
`y ∈ S`, `(f y)⁻¹` is unique. -/
@[to_additive "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that
`f(S) ⊆ add_units N`, for all `y ∈ S`, `- (f y)` is unique."]
lemma inv_unique {f : M →* N} (h : ∀ y : S, is_unit (f y)) {y : S}
  {z} (H : f y * z = 1) : ↑(is_unit.lift_right (f.mrestrict S) h y)⁻¹ = z :=
by rw [←one_mul ↑(_)⁻¹, mul_inv_left, ←H]

variables (f : localization_map S N)

@[to_additive] lemma map_right_cancel {x y} {c : S} (h : f.to_map (c * x) = f.to_map (c * y)) :
  f.to_map x = f.to_map y :=
begin
  rw [f.to_map.map_mul, f.to_map.map_mul] at h,
  cases f.map_units c with u hu,
  rw ←hu at h,
  exact (units.mul_right_inj u).1 h,
end

@[to_additive] lemma map_left_cancel {x y} {c : S} (h : f.to_map (x * c) = f.to_map (y * c)) :
  f.to_map x = f.to_map y :=
f.map_right_cancel $ by rw [mul_comm _ x, mul_comm _ y, h]

/-- Given a localization map `f : M →* N`, the surjection sending `(x, y) : M × S` to
`f x * (f y)⁻¹`. -/
@[to_additive "Given a localization map `f : M →+ N`, the surjection sending `(x, y) : M × S`
to `f x - f y`."]
noncomputable def mk' (f : localization_map S N) (x : M) (y : S) : N :=
f.to_map x * ↑(is_unit.lift_right (f.to_map.mrestrict S) f.map_units y)⁻¹

@[to_additive] lemma mk'_mul (x₁ x₂ : M) (y₁ y₂ : S) :
  f.mk' (x₁ * x₂) (y₁ * y₂) = f.mk' x₁ y₁ * f.mk' x₂ y₂ :=
(mul_inv_left f.map_units _ _ _).2 $
  show _ = _ * (_ * _ * (_ * _)), by
  rw [←mul_assoc, ←mul_assoc, mul_inv_right f.map_units, mul_assoc, mul_assoc,
      mul_comm _ (f.to_map x₂), ←mul_assoc, ←mul_assoc, mul_inv_right f.map_units,
      submonoid.coe_mul, f.to_map.map_mul, f.to_map.map_mul];
  ac_refl

@[to_additive] lemma mk'_one (x) : f.mk' x (1 : S) = f.to_map x :=
by rw [mk', monoid_hom.map_one]; exact mul_one _

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, for all `z : N` we have that if
`x : M, y ∈ S` are such that `z * f y = f x`, then `f x * (f y)⁻¹ = z`. -/
@[simp, to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, for all `z : N`
we have that if `x : M, y ∈ S` are such that `z + f y = f x`, then `f x - f y = z`."]
lemma mk'_sec (z : N) : f.mk' (f.sec z).1 (f.sec z).2 = z :=
show _ * _ = _, by rw [←sec_spec, mul_inv_left, mul_comm]

@[to_additive] lemma mk'_surjective (z : N) : ∃ x (y : S), f.mk' x y = z :=
⟨(f.sec z).1, (f.sec z).2, f.mk'_sec z⟩

@[to_additive] lemma mk'_spec (x) (y : S) :
  f.mk' x y * f.to_map y = f.to_map x :=
show _ * _ * _ = _, by rw [mul_assoc, mul_comm _ (f.to_map y), ←mul_assoc, mul_inv_left, mul_comm]

@[to_additive] lemma mk'_spec' (x) (y : S) :
  f.to_map y * f.mk' x y = f.to_map x :=
by rw [mul_comm, mk'_spec]

@[to_additive] theorem eq_mk'_iff_mul_eq {x} {y : S} {z} :
  z = f.mk' x y ↔ z * f.to_map y = f.to_map x :=
⟨λ H, by rw [H, mk'_spec], λ H, by erw [mul_inv_right, H]; refl⟩

@[to_additive] theorem mk'_eq_iff_eq_mul {x} {y : S} {z} :
  f.mk' x y = z ↔ f.to_map x = z * f.to_map y :=
by rw [eq_comm, eq_mk'_iff_mul_eq, eq_comm]

@[to_additive] lemma mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : S} :
  f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ f.to_map (x₁ * y₂) = f.to_map (x₂ * y₁) :=
⟨λ H, by rw [f.to_map.map_mul, f.mk'_eq_iff_eq_mul.1 H, mul_assoc,
  mul_comm (f.to_map _), ←mul_assoc, mk'_spec, f.to_map.map_mul],
 λ H, by rw [mk'_eq_iff_eq_mul, mk', mul_assoc, mul_comm _ (f.to_map y₁), ←mul_assoc,
  ←f.to_map.map_mul, ←H, f.to_map.map_mul, mul_inv_right f.map_units]⟩

@[to_additive] protected lemma eq {a₁ b₁} {a₂ b₂ : S} :
  f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ ∃ c : S, a₁ * b₂ * c = b₁ * a₂ * c :=
f.mk'_eq_iff_eq.trans $ f.eq_iff_exists

@[to_additive] protected lemma eq' {a₁ b₁} {a₂ b₂ : S} :
  f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ localization.r S (a₁, a₂) (b₁, b₂) :=
by rw [f.eq, localization.r_iff_exists]

@[to_additive] lemma eq_iff_eq (g : localization_map S P) {x y} :
  f.to_map x = f.to_map y ↔ g.to_map x = g.to_map y :=
f.eq_iff_exists.trans g.eq_iff_exists.symm

@[to_additive] lemma mk'_eq_iff_mk'_eq (g : localization_map S P) {x₁ x₂}
  {y₁ y₂ : S} : f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ g.mk' x₁ y₁ = g.mk' x₂ y₂ :=
f.eq'.trans g.eq'.symm

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, for all `x₁ : M` and `y₁ ∈ S`,
if `x₂ : M, y₂ ∈ S` are such that `f x₁ * (f y₁)⁻¹ * f y₂ = f x₂`, then there exists `c ∈ S`
such that `x₁ * y₂ * c = x₂ * y₁ * c`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, for all `x₁ : M`
and `y₁ ∈ S`, if `x₂ : M, y₂ ∈ S` are such that `(f x₁ - f y₁) + f y₂ = f x₂`, then there exists
`c ∈ S` such that `x₁ + y₂ + c = x₂ + y₁ + c`."]
lemma exists_of_sec_mk' (x) (y : S) :
  ∃ c : S, x * (f.sec $ f.mk' x y).2 * c = (f.sec $ f.mk' x y).1 * y * c :=
f.eq_iff_exists.1 $ f.mk'_eq_iff_eq.1 $ (mk'_sec _ _).symm

@[to_additive] lemma mk'_eq_of_eq {a₁ b₁ : M} {a₂ b₂ : S} (H : b₁ * a₂ = a₁ * b₂) :
  f.mk' a₁ a₂ = f.mk' b₁ b₂ :=
f.mk'_eq_iff_eq.2 $ H ▸ rfl

@[simp, to_additive] lemma mk'_self' (y : S) :
  f.mk' (y : M) y = 1 :=
show _ * _ = _, by rw [mul_inv_left, mul_one]

@[simp, to_additive] lemma mk'_self (x) (H : x ∈ S) :
  f.mk' x ⟨x, H⟩ = 1 :=
by convert mk'_self' _ _; refl

@[to_additive] lemma mul_mk'_eq_mk'_of_mul (x₁ x₂) (y : S) :
  f.to_map x₁ * f.mk' x₂ y = f.mk' (x₁ * x₂) y :=
by rw [←mk'_one, ←mk'_mul, one_mul]

@[to_additive] lemma mk'_mul_eq_mk'_of_mul (x₁ x₂) (y : S) :
  f.mk' x₂ y * f.to_map x₁ = f.mk' (x₁ * x₂) y :=
by rw [mul_comm, mul_mk'_eq_mk'_of_mul]

@[to_additive] lemma mul_mk'_one_eq_mk' (x) (y : S) :
  f.to_map x * f.mk' 1 y = f.mk' x y :=
by rw [mul_mk'_eq_mk'_of_mul, mul_one]

@[simp, to_additive] lemma mk'_mul_cancel_right (x : M) (y : S) :
  f.mk' (x * y) y = f.to_map x :=
by rw [←mul_mk'_one_eq_mk', f.to_map.map_mul, mul_assoc, mul_mk'_one_eq_mk', mk'_self', mul_one]

@[to_additive] lemma mk'_mul_cancel_left (x) (y : S) :
  f.mk' ((y : M) * x) y = f.to_map x :=
by rw [mul_comm, mk'_mul_cancel_right]

@[to_additive] lemma is_unit_comp (j : N →* P) (y : S) :
  is_unit (j.comp f.to_map y) :=
⟨units.map j $ is_unit.lift_right (f.to_map.mrestrict S) f.map_units y,
  show j _ = j _, from congr_arg j $
    (is_unit.coe_lift_right (f.to_map.mrestrict S) f.map_units _)⟩

variables {g : M →* P}

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M` and a map of `comm_monoid`s
`g : M →* P` such that `g(S) ⊆ units P`, `f x = f y → g x = g y` for all `x y : M`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M` and a map
of `add_comm_monoid`s `g : M →+ P` such that `g(S) ⊆ add_units P`, `f x = f y → g x = g y`
for all `x y : M`."]
lemma eq_of_eq (hg : ∀ y : S, is_unit (g y)) {x y} (h : f.to_map x = f.to_map y) :
  g x = g y :=
begin
  obtain ⟨c, hc⟩ := f.eq_iff_exists.1 h,
  rw [←mul_one (g x), ←is_unit.mul_lift_right_inv (g.mrestrict S) hg c],
  show _ * (g c * _) = _,
  rw [←mul_assoc, ←g.map_mul, hc, mul_inv_left hg, g.map_mul, mul_comm],
end

/-- Given `comm_monoid`s `M, P`, localization maps `f : M →* N, k : P →* Q` for submonoids
`S, T` respectively, and `g : M →* P` such that `g(S) ⊆ T`, `f x = f y` implies
`k (g x) = k (g y)`. -/
@[to_additive "Given `add_comm_monoid`s `M, P`, localization maps `f : M →+ N, k : P →+ Q` for
submonoids `S, T` respectively, and `g : M →+ P` such that `g(S) ⊆ T`, `f x = f y`
implies `k (g x) = k (g y)`."]
lemma comp_eq_of_eq {T : submonoid P} {Q : Type*} [comm_monoid Q]
  (hg : ∀ y : S, g y ∈ T) (k : localization_map T Q)
  {x y} (h : f.to_map x = f.to_map y) : k.to_map (g x) = k.to_map (g y) :=
f.eq_of_eq (λ y : S, show is_unit (k.to_map.comp g y), from k.map_units ⟨g y, hg y⟩) h

variables (hg : ∀ y : S, is_unit (g y))

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M` and a map of `comm_monoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` sending `z : N` to `g x * (g y)⁻¹`, where `(x, y) : M × S` are such that
`z = f x * (f y)⁻¹`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M` and a map
of `add_comm_monoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism
induced from `N` to `P` sending `z : N` to `g x - g y`, where `(x, y) : M × S` are such that
`z = f x - f y`."]
noncomputable def lift : N →* P :=
{ to_fun := λ z, g (f.sec z).1 * ↑(is_unit.lift_right (g.mrestrict S) hg (f.sec z).2)⁻¹,
  map_one' := by rw [mul_inv_left, mul_one]; exact f.eq_of_eq hg
    (by rw [←sec_spec, one_mul]),
  map_mul' := λ x y,
    begin
      rw [mul_inv_left hg, ←mul_assoc, ←mul_assoc, mul_inv_right hg,
          mul_comm _ (g (f.sec y).1), ←mul_assoc, ←mul_assoc, mul_inv_right hg],
      repeat { rw ←g.map_mul },
      exact f.eq_of_eq hg (by repeat { rw f.to_map.map_mul <|> rw sec_spec' }; ac_refl)
    end }

variables {S g}

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M` and a map of `comm_monoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : M, y ∈ S`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M` and a map
of `add_comm_monoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism
induced from `N` to `P` maps `f x - f y` to `g x - g y` for all `x : M, y ∈ S`."]
lemma lift_mk' (x y) :
  f.lift hg (f.mk' x y) = g x * ↑(is_unit.lift_right (g.mrestrict S) hg y)⁻¹ :=
(mul_inv hg).2 $ f.eq_of_eq hg $ by
  rw [f.to_map.map_mul, f.to_map.map_mul, sec_spec', mul_assoc, f.mk'_spec, mul_comm]

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v : P`, we have
`f.lift hg z = v ↔ g x = g y * v`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, if
an `add_comm_monoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all
`z : N, v : P`, we have `f.lift hg z = v ↔ g x = g y + v`, where `x : M, y ∈ S` are such that
`z + f y = f x`."]
lemma lift_spec (z v) :
  f.lift hg z = v ↔ g (f.sec z).1 = g (f.sec z).2 * v :=
mul_inv_left hg _ _ v

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v w : P`, we have
`f.lift hg z * w = v ↔ g x * w = g y * v`, where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, if
an `add_comm_monoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all
`z : N, v w : P`, we have `f.lift hg z + w = v ↔ g x + w = g y + v`, where `x : M, y ∈ S` are such
that `z + f y = f x`."]
lemma lift_spec_mul (z w v) :
  f.lift hg z * w = v ↔ g (f.sec z).1 * w = g (f.sec z).2 * v :=
begin
  rw mul_comm,
  show _ * (_ * _) = _ ↔ _,
  rw [←mul_assoc, mul_inv_left hg, mul_comm],
end

@[to_additive] lemma lift_mk'_spec (x v) (y : S) :
  f.lift hg (f.mk' x y) = v ↔ g x = g y * v :=
by rw f.lift_mk' hg; exact mul_inv_left hg _ _ _

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`f.lift hg z * g y = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, if
an `add_comm_monoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we
have `f.lift hg z + g y = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`."]
lemma lift_mul_right (z) :
  f.lift hg z * g (f.sec z).2 = g (f.sec z).1 :=
show _ * _ * _ = _, by erw [mul_assoc, is_unit.lift_right_inv_mul, mul_one]

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`g y * f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, if
an `add_comm_monoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we
have `g y + f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`."]
lemma lift_mul_left (z) :
  g (f.sec z).2 * f.lift hg z = g (f.sec z).1 :=
by rw [mul_comm, lift_mul_right]

@[simp, to_additive] lemma lift_eq (x : M) :
  f.lift hg (f.to_map x) = g x :=
by rw [lift_spec, ←g.map_mul]; exact f.eq_of_eq hg (by rw [sec_spec', f.to_map.map_mul])

@[to_additive] lemma lift_eq_iff {x y : M × S} :
  f.lift hg (f.mk' x.1 x.2) = f.lift hg (f.mk' y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) :=
by rw [lift_mk', lift_mk', mul_inv hg]

@[simp, to_additive] lemma  lift_comp : (f.lift hg).comp f.to_map = g :=
by ext; exact f.lift_eq hg _

@[simp, to_additive] lemma lift_of_comp (j : N →* P) :
  f.lift (f.is_unit_comp j) = j :=
begin
  ext,
  rw lift_spec,
  show j _ = j _ * _,
  erw [←j.map_mul, sec_spec'],
end

@[to_additive] lemma epic_of_localization_map {j k : N →* P}
  (h : ∀ a, j.comp f.to_map a = k.comp f.to_map a) : j = k :=
begin
  rw [←f.lift_of_comp j, ←f.lift_of_comp k],
  congr' 1 with x, exact h x,
end

@[to_additive] lemma lift_unique {j : N →* P}
  (hj : ∀ x, j (f.to_map x) = g x) : f.lift hg = j :=
begin
  ext,
  rw [lift_spec, ←hj, ←hj, ←j.map_mul],
  apply congr_arg,
  rw ←sec_spec',
end

@[simp, to_additive] lemma lift_id (x) : f.lift f.map_units x = x :=
monoid_hom.ext_iff.1 (f.lift_of_comp $ monoid_hom.id N) x

/-- Given two localization maps `f : M →* N, k : M →* P` for a submonoid `S ⊆ M`,
the hom from `P` to `N` induced by `f` is left inverse to the hom from `N` to `P`
induced by `k`. -/
@[simp, to_additive] lemma lift_left_inverse {k : localization_map S P} (z : N) :
  k.lift f.map_units (f.lift k.map_units z) = z :=
begin
  rw lift_spec,
  cases f.surj z with x hx,
  conv_rhs {congr, skip, rw f.eq_mk'_iff_mul_eq.2 hx},
  rw [mk', ←mul_assoc, mul_inv_right f.map_units, ←f.to_map.map_mul, ←f.to_map.map_mul],
  apply k.eq_of_eq f.map_units,
  rw [k.to_map.map_mul, k.to_map.map_mul, ←sec_spec, mul_assoc, lift_spec_mul],
  repeat { rw ←k.to_map.map_mul },
  apply f.eq_of_eq k.map_units,
  repeat { rw f.to_map.map_mul },
  rw [sec_spec', ←hx],
  ac_refl,
end

@[to_additive] lemma lift_surjective_iff :
  function.surjective (f.lift hg) ↔ ∀ v : P, ∃ x : M × S, v * g x.2 = g x.1 :=
begin
  split,
    { intros H v,
      obtain ⟨z, hz⟩ := H v,
      obtain ⟨x, hx⟩ := f.surj z,
      use x,
      rw [←hz, f.eq_mk'_iff_mul_eq.2 hx, lift_mk', mul_assoc, mul_comm _ (g ↑x.2)],
      erw [is_unit.mul_lift_right_inv (g.mrestrict S) hg, mul_one] },
  { intros H v,
    obtain ⟨x, hx⟩ := H v,
    use f.mk' x.1 x.2,
    rw [lift_mk', mul_inv_left hg, mul_comm, ←hx] }
end

@[to_additive] lemma lift_injective_iff :
  function.injective (f.lift hg) ↔ ∀ x y, f.to_map x = f.to_map y ↔ g x = g y :=
begin
  split,
    { intros H x y,
      split,
        { exact f.eq_of_eq hg },
      { intro h,
        rw [←f.lift_eq hg, ←f.lift_eq hg] at h,
        exact H h }},
  { intros H z w h,
    obtain ⟨x, hx⟩ := f.surj z,
    obtain ⟨y, hy⟩ := f.surj w,
    rw [←f.mk'_sec z, ←f.mk'_sec w],
    exact (mul_inv f.map_units).2 ((H _ _).2 $ (mul_inv hg).1 h) }
end

variables {T : submonoid P} (hy : ∀ y : S, g y ∈ T) {Q : Type*} [comm_monoid Q]
          (k : localization_map T Q)

/-- Given a `comm_monoid` homomorphism `g : M →* P` where for submonoids `S ⊆ M, T ⊆ P` we have
`g(S) ⊆ T`, the induced monoid homomorphism from the localization of `M` at `S` to the
localization of `P` at `T`: if `f : M →* N` and `k : P →* Q` are localization maps for `S` and
`T` respectively, we send `z : N` to `k (g x) * (k (g y))⁻¹`, where `(x, y) : M × S` are such
that `z = f x * (f y)⁻¹`. -/
@[to_additive "Given a `add_comm_monoid` homomorphism `g : M →+ P` where for submonoids
`S ⊆ M, T ⊆ P` we have `g(S) ⊆ T`, the induced add_monoid homomorphism from the localization of `M`
at `S` to the localization of `P` at `T`: if `f : M →+ N` and `k : P →+ Q` are localization maps
for `S` and `T` respectively, we send `z : N` to `k (g x) - k (g y)`, where `(x, y) : M × S` are
such that `z = f x - f y`."]
noncomputable def map : N →* Q :=
@lift _ _ _ _ _ _ _ f (k.to_map.comp g) $ λ y, k.map_units ⟨g y, hy y⟩

variables {k}

@[to_additive] lemma map_eq (x) :
  f.map hy k (f.to_map x) = k.to_map (g x) := f.lift_eq (λ y, k.map_units ⟨g y, hy y⟩) x

@[simp, to_additive] lemma map_comp :
  (f.map hy k).comp f.to_map = k.to_map.comp g := f.lift_comp $ λ y, k.map_units ⟨g y, hy y⟩

@[to_additive] lemma map_mk' (x) (y : S) :
  f.map hy k (f.mk' x y) = k.mk' (g x) ⟨g y, hy y⟩ :=
begin
  rw [map, lift_mk', mul_inv_left],
  { show k.to_map (g x) = k.to_map (g y) * _,
    rw mul_mk'_eq_mk'_of_mul,
    exact (k.mk'_mul_cancel_left (g x) ⟨(g y), hy y⟩).symm },
end

/-- Given localization maps `f : M →* N, k : P →* Q` for submonoids `S, T` respectively, if a
`comm_monoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
`u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) * u` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive "Given localization maps `f : M →+ N, k : P →+ Q` for submonoids `S, T` respectively,
if an `add_comm_monoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all
`z : N`, `u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) + u` where `x : M, y ∈ S` are such
that `z + f y = f x`."]
lemma map_spec (z u) :
  f.map hy k z = u ↔ k.to_map (g (f.sec z).1) = k.to_map (g (f.sec z).2) * u :=
f.lift_spec (λ y, k.map_units ⟨g y, hy y⟩) _ _

/-- Given localization maps `f : M →* N, k : P →* Q` for submonoids `S, T` respectively, if a
`comm_monoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `f.map hy k z * k (g y) = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive "Given localization maps `f : M →+ N, k : P →+ Q` for submonoids `S, T` respectively,
if an `add_comm_monoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then
for all `z : N`, we have `f.map hy k z + k (g y) = k (g x)` where `x : M, y ∈ S` are such that
`z + f y = f x`."]
lemma map_mul_right (z) :
  f.map hy k z * (k.to_map (g (f.sec z).2)) = k.to_map (g (f.sec z).1) :=
f.lift_mul_right (λ y, k.map_units ⟨g y, hy y⟩) _

/-- Given localization maps `f : M →* N, k : P →* Q` for submonoids `S, T` respectively, if a
`comm_monoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `k (g y) * f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive "Given localization maps `f : M →+ N, k : P →+ Q` for submonoids `S, T` respectively,
if an `add_comm_monoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all
`z : N`, we have `k (g y) + f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that
`z + f y = f x`."]
lemma map_mul_left (z) :
  k.to_map (g (f.sec z).2) * f.map hy k z = k.to_map (g (f.sec z).1) :=
by rw [mul_comm, f.map_mul_right]

@[simp, to_additive] lemma map_id (z : N) :
  f.map (λ y, show monoid_hom.id M y ∈ S, from y.2) f z = z :=
f.lift_id z

/-- If `comm_monoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive "If `add_comm_monoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations,
the composition of the induced maps equals the map of localizations induced by `l ∘ g`."]
lemma map_comp_map {A : Type*} [comm_monoid A] {U : submonoid A} {R} [comm_monoid R]
  (j : localization_map U R) {l : P →* A} (hl : ∀ w : T, l w ∈ U) :
  (k.map hl j).comp (f.map hy k) = f.map (λ x, show l.comp g x ∈ U, from hl ⟨g x, hy x⟩) j :=
begin
  ext z,
  show j.to_map _ * _ = j.to_map (l _) * _,
  { rw [mul_inv_left, ←mul_assoc, mul_inv_right],
    show j.to_map _ * j.to_map (l (g _)) = j.to_map (l _) * _,
    rw [←j.to_map.map_mul, ←j.to_map.map_mul, ←l.map_mul, ←l.map_mul],
    exact k.comp_eq_of_eq hl j
      (by rw [k.to_map.map_mul, k.to_map.map_mul, sec_spec', mul_assoc, map_mul_right]) },
end

/-- If `comm_monoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive "If `add_comm_monoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations,
the composition of the induced maps equals the map of localizations induced by `l ∘ g`."]
lemma map_map {A : Type*} [comm_monoid A] {U : submonoid A} {R} [comm_monoid R]
  (j : localization_map U R) {l : P →* A} (hl : ∀ w : T, l w ∈ U) (x) :
  k.map hl j (f.map hy k x) = f.map (λ x, show l.comp g x ∈ U, from hl ⟨g x, hy x⟩) j x :=
by rw ←f.map_comp_map hy j hl; refl

section away_map

variables (x : M)
/-- Given `x : M`, the type of `comm_monoid` homomorphisms `f : M →* N` such that `N`
is isomorphic to the localization of `M` at the submonoid generated by `x`. -/
@[reducible, to_additive "Given `x : M`, the type of `add_comm_monoid` homomorphisms `f : M →+ N`
such that `N` is isomorphic to the localization of `M` at the submonoid generated by `x`."]
def away_map (N' : Type*) [comm_monoid N'] :=
localization_map (powers x) N'

variables (F : away_map x N)

/-- Given `x : M` and a localization map `F : M →* N` away from `x`, `inv_self` is `(F x)⁻¹`. -/
noncomputable def away_map.inv_self : N :=
F.mk' 1 ⟨x, mem_powers _⟩

/-- Given `x : M`, a localization map `F : M →* N` away from `x`, and a map of `comm_monoid`s
`g : M →* P` such that `g x` is invertible, the homomorphism induced from `N` to `P` sending
`z : N` to `g y * (g x)⁻ⁿ`, where `y : M, n : ℕ` are such that `z = F y * (F x)⁻ⁿ`. -/
noncomputable def away_map.lift (hg : is_unit (g x)) : N →* P :=
F.lift $ λ y, show is_unit (g y.1),
begin
  obtain ⟨n, hn⟩ := y.2,
  rw [←hn, g.map_pow],
  exact is_unit.pow n hg,
end

@[simp] lemma away_map.lift_eq (hg : is_unit (g x)) (a : M) :
  F.lift x hg (F.to_map a) = g a := lift_eq _ _ _

@[simp] lemma away_map.lift_comp (hg : is_unit (g x)) :
  (F.lift x hg).comp F.to_map = g := lift_comp _ _

/-- Given `x y : M` and localization maps `F : M →* N, G : M →* P` away from `x` and `x * y`
respectively, the homomorphism induced from `N` to `P`. -/
noncomputable def away_to_away_right (y : M) (G : away_map (x * y) P) : N →* P :=
F.lift x $ show is_unit (G.to_map x), from
is_unit_of_mul_eq_one (G.to_map x) (G.mk' y ⟨x * y, mem_powers _⟩) $
by rw [mul_mk'_eq_mk'_of_mul, mk'_self]

end away_map
end localization_map
end submonoid
namespace add_submonoid
namespace localization_map
section away_map

variables {A : Type*} [add_comm_monoid A] (x : A) {B : Type*}
  [add_comm_monoid B] (F : away_map x B) {C : Type*} [add_comm_monoid C] {g : A →+ C}

/-- Given `x : A` and a localization map `F : A →+ B` away from `x`, `neg_self` is `- (F x)`. -/
noncomputable def away_map.neg_self : B :=
F.mk' 0 ⟨x, mem_multiples _⟩

/-- Given `x : A`, a localization map `F : A →+ B` away from `x`, and a map of `add_comm_monoid`s
`g : A →+ C` such that `g x` is invertible, the homomorphism induced from `B` to `C` sending
`z : B` to `g y - n • g x`, where `y : A, n : ℕ` are such that `z = F y - n • F x`. -/
noncomputable def away_map.lift (hg : is_add_unit (g x)) : B →+ C :=
F.lift $ λ y, show is_add_unit (g y.1),
begin
  obtain ⟨n, hn⟩ := y.2,
  rw ← hn,
  dsimp,
  rw [g.map_nsmul],
  exact is_add_unit.map (add_monoid_hom.of (nsmul.is_add_monoid_hom n)) hg,
end

@[simp] lemma away_map.lift_eq (hg : is_add_unit (g x)) (a : A) :
  F.lift x hg (F.to_map a) = g a := lift_eq _ _ _

@[simp] lemma away_map.lift_comp (hg : is_add_unit (g x)) :
  (F.lift x hg).comp F.to_map = g := lift_comp _ _

/-- Given `x y : A` and localization maps `F : A →+ B, G : A →+ C` away from `x` and `x + y`
respectively, the homomorphism induced from `B` to `C`. -/
noncomputable def away_to_away_right (y : A) (G : away_map (x + y) C) : B →+ C :=
F.lift x $ show is_add_unit (G.to_map x), from
is_add_unit_of_add_eq_zero (G.to_map x) (G.mk' y ⟨x + y, mem_multiples _⟩) $
by rw [add_mk'_eq_mk'_of_add, mk'_self]

end away_map
end localization_map
end add_submonoid
namespace submonoid
namespace localization_map

variables (f : S.localization_map N) {g : M →* P} (hg : ∀ (y : S), is_unit (g y))
  {T : submonoid P} {Q : Type*} [comm_monoid Q]

/-- If `f : M →* N` and `k : M →* P` are localization maps for a submonoid `S`, we get an
isomorphism of `N` and `P`. -/
@[to_additive "If `f : M →+ N` and `k : M →+ R` are localization maps for a submonoid `S`,
we get an isomorphism of `N` and `R`."]
noncomputable def mul_equiv_of_localizations
  (k : localization_map S P) : N ≃* P :=
⟨f.lift k.map_units, k.lift f.map_units, f.lift_left_inverse,
  k.lift_left_inverse, monoid_hom.map_mul _⟩

@[simp, to_additive] lemma mul_equiv_of_localizations_apply
  {k : localization_map S P} {x} :
  f.mul_equiv_of_localizations k x = f.lift k.map_units x := rfl

@[simp, to_additive] lemma mul_equiv_of_localizations_symm_apply
  {k : localization_map S P} {x} :
  (f.mul_equiv_of_localizations k).symm x = k.lift f.map_units x := rfl

@[to_additive] lemma mul_equiv_of_localizations_symm_eq_mul_equiv_of_localizations
  {k : localization_map S P} :
  (k.mul_equiv_of_localizations f).symm = f.mul_equiv_of_localizations k := rfl

/-- If `f : M →* N` is a localization map for a submonoid `S` and `k : N ≃* P` is an isomorphism
of `comm_monoid`s, `k ∘ f` is a localization map for `M` at `S`. -/
@[to_additive "If `f : M →+ N` is a localization map for a submonoid `S` and `k : N ≃+ P` is an
isomorphism of `add_comm_monoid`s, `k ∘ f` is a localization map for `M` at `S`."]
def of_mul_equiv_of_localizations (k : N ≃* P) : localization_map S P :=
(k.to_monoid_hom.comp f.to_map).to_localization_map (λ y, is_unit_comp f k.to_monoid_hom y)
(λ v, let ⟨z, hz⟩ := k.to_equiv.surjective v in
  let ⟨x, hx⟩ := f.surj z in ⟨x, show v * k _ = k _, by rw [←hx, k.map_mul, ←hz]; refl⟩)
(λ x y, k.apply_eq_iff_eq.trans f.eq_iff_exists)

@[simp, to_additive] lemma of_mul_equiv_of_localizations_apply {k : N ≃* P} (x) :
  (f.of_mul_equiv_of_localizations k).to_map x = k (f.to_map x) := rfl

@[to_additive] lemma of_mul_equiv_of_localizations_eq {k : N ≃* P} :
  (f.of_mul_equiv_of_localizations k).to_map = k.to_monoid_hom.comp f.to_map := rfl

@[to_additive] lemma symm_comp_of_mul_equiv_of_localizations_apply {k : N ≃* P} (x) :
  k.symm ((f.of_mul_equiv_of_localizations k).to_map x) = f.to_map x :=
k.symm_apply_apply (f.to_map x)

@[to_additive] lemma symm_comp_of_mul_equiv_of_localizations_apply' {k : P ≃* N} (x) :
  k ((f.of_mul_equiv_of_localizations k.symm).to_map x) = f.to_map x :=
k.apply_symm_apply (f.to_map x)

@[to_additive] lemma of_mul_equiv_of_localizations_eq_iff_eq {k : N ≃* P} {x y} :
  (f.of_mul_equiv_of_localizations k).to_map x = y ↔ f.to_map x = k.symm y :=
k.to_equiv.eq_symm_apply.symm

@[to_additive add_equiv_of_localizations_right_inv]
lemma mul_equiv_of_localizations_right_inv (k : localization_map S P) :
  f.of_mul_equiv_of_localizations (f.mul_equiv_of_localizations k) = k :=
to_map_injective $ f.lift_comp k.map_units

@[to_additive add_equiv_of_localizations_right_inv_apply, simp]
lemma mul_equiv_of_localizations_right_inv_apply
  {k : localization_map S P} {x} :
  (f.of_mul_equiv_of_localizations (f.mul_equiv_of_localizations k)).to_map x = k.to_map x :=
ext_iff.1 (f.mul_equiv_of_localizations_right_inv k) x

@[to_additive] lemma mul_equiv_of_localizations_left_inv (k : N ≃* P) :
  f.mul_equiv_of_localizations (f.of_mul_equiv_of_localizations k) = k :=
mul_equiv.ext $ monoid_hom.ext_iff.1 $ f.lift_of_comp k.to_monoid_hom

@[simp, to_additive] lemma mul_equiv_of_localizations_left_inv_apply {k : N ≃* P} (x) :
  f.mul_equiv_of_localizations (f.of_mul_equiv_of_localizations k) x = k x :=
by rw mul_equiv_of_localizations_left_inv

@[simp, to_additive] lemma of_mul_equiv_of_localizations_id :
  f.of_mul_equiv_of_localizations (mul_equiv.refl N) = f :=
by ext; refl

@[to_additive] lemma of_mul_equiv_of_localizations_comp {k : N ≃* P} {j : P ≃* Q} :
  (f.of_mul_equiv_of_localizations (k.trans j)).to_map =
    j.to_monoid_hom.comp (f.of_mul_equiv_of_localizations k).to_map :=
by ext; refl

/-- Given `comm_monoid`s `M, P` and submonoids `S ⊆ M, T ⊆ P`, if `f : M →* N` is a localization
map for `S` and `k : P ≃* M` is an isomorphism of `comm_monoid`s such that `k(T) = S`, `f ∘ k`
is a localization map for `T`. -/
@[to_additive "Given `comm_monoid`s `M, P` and submonoids `S ⊆ M, T ⊆ P`, if `f : M →* N` is
a localization map for `S` and `k : P ≃* M` is an isomorphism of `comm_monoid`s such that
`k(T) = S`, `f ∘ k` is a localization map for `T`."]
def of_mul_equiv_of_dom {k : P ≃* M} (H : T.map k.to_monoid_hom = S) :
  localization_map T N :=
let H' : S.comap k.to_monoid_hom = T :=
  H ▸ (set_like.coe_injective $ T.1.preimage_image_eq k.to_equiv.injective) in
(f.to_map.comp k.to_monoid_hom).to_localization_map
  (λ y, let ⟨z, hz⟩ := f.map_units ⟨k y, H ▸ set.mem_image_of_mem k y.2⟩ in ⟨z, hz⟩)
  (λ z, let ⟨x, hx⟩ := f.surj z in let ⟨v, hv⟩ := k.to_equiv.surjective x.1 in
    let ⟨w, hw⟩ := k.to_equiv.surjective x.2 in ⟨(v, ⟨w, H' ▸ show k w ∈ S, from hw.symm ▸ x.2.2⟩),
    show z * f.to_map (k.to_equiv w) = f.to_map (k.to_equiv v), by erw [hv, hw, hx]; refl⟩)
  (λ x y, show f.to_map _ = f.to_map _ ↔ _, by erw f.eq_iff_exists;
    exact ⟨λ ⟨c, hc⟩, let ⟨d, hd⟩ := k.to_equiv.surjective c in
    ⟨⟨d, H' ▸ show k d ∈ S, from hd.symm ▸ c.2⟩, by erw [←hd, ←k.map_mul, ←k.map_mul] at hc;
      exact k.to_equiv.injective hc⟩, λ ⟨c, hc⟩, ⟨⟨k c, H ▸ set.mem_image_of_mem k c.2⟩,
    by erw ←k.map_mul; rw [hc, k.map_mul]; refl⟩⟩)

@[simp, to_additive] lemma of_mul_equiv_of_dom_apply
  {k : P ≃* M} (H : T.map k.to_monoid_hom = S) (x) :
  (f.of_mul_equiv_of_dom H).to_map x = f.to_map (k x) := rfl

@[to_additive] lemma of_mul_equiv_of_dom_eq
  {k : P ≃* M} (H : T.map k.to_monoid_hom = S) :
  (f.of_mul_equiv_of_dom H).to_map = f.to_map.comp k.to_monoid_hom := rfl

@[to_additive] lemma of_mul_equiv_of_dom_comp_symm {k : P ≃* M}
  (H : T.map k.to_monoid_hom = S) (x) :
  (f.of_mul_equiv_of_dom H).to_map (k.symm x) = f.to_map x :=
congr_arg f.to_map $ k.apply_symm_apply x

@[to_additive] lemma of_mul_equiv_of_dom_comp {k : M ≃* P}
  (H : T.map k.symm.to_monoid_hom = S) (x) :
  (f.of_mul_equiv_of_dom H).to_map (k x) = f.to_map x :=
congr_arg f.to_map $ k.symm_apply_apply x

/-- A special case of `f ∘ id = f`, `f` a localization map. -/
@[simp, to_additive "A special case of `f ∘ id = f`, `f` a localization map."]
lemma of_mul_equiv_of_dom_id :
  f.of_mul_equiv_of_dom (show S.map (mul_equiv.refl M).to_monoid_hom = S, from
    submonoid.ext $ λ x, ⟨λ ⟨y, hy, h⟩, h ▸ hy, λ h, ⟨x, h, rfl⟩⟩) = f :=
by ext; refl

/-- Given localization maps `f : M →* N, k : P →* U` for submonoids `S, T` respectively, an
isomorphism `j : M ≃* P` such that `j(S) = T` induces an isomorphism of localizations
`N ≃* U`. -/
@[to_additive "Given localization maps `f : M →+ N, k : P →+ U` for submonoids `S, T` respectively,
an isomorphism `j : M ≃+ P` such that `j(S) = T` induces an isomorphism of
localizations `N ≃+ U`."]
noncomputable def mul_equiv_of_mul_equiv
  (k : localization_map T Q) {j : M ≃* P} (H : S.map j.to_monoid_hom = T) :
  N ≃* Q :=
f.mul_equiv_of_localizations $ k.of_mul_equiv_of_dom H

@[simp, to_additive] lemma mul_equiv_of_mul_equiv_eq_map_apply
  {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) (x) :
  f.mul_equiv_of_mul_equiv k H x =
    f.map (λ y : S, show j.to_monoid_hom y ∈ T, from H ▸ set.mem_image_of_mem j y.2) k x := rfl

@[to_additive] lemma mul_equiv_of_mul_equiv_eq_map
  {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) :
  (f.mul_equiv_of_mul_equiv k H).to_monoid_hom =
    f.map (λ y : S, show j.to_monoid_hom y ∈ T, from H ▸ set.mem_image_of_mem j y.2) k := rfl

@[simp, to_additive] lemma mul_equiv_of_mul_equiv_eq {k : localization_map T Q}
  {j : M ≃* P} (H : S.map j.to_monoid_hom = T) (x) :
  f.mul_equiv_of_mul_equiv k H (f.to_map x) = k.to_map (j x) :=
f.map_eq (λ y : S, H ▸ set.mem_image_of_mem j y.2) _

@[simp, to_additive] lemma mul_equiv_of_mul_equiv_mk' {k : localization_map T Q}
  {j : M ≃* P} (H : S.map j.to_monoid_hom = T) (x y) :
  f.mul_equiv_of_mul_equiv k H (f.mk' x y) = k.mk' (j x) ⟨j y, H ▸ set.mem_image_of_mem j y.2⟩ :=
f.map_mk' (λ y : S, H ▸ set.mem_image_of_mem j y.2) _ _

@[simp, to_additive] lemma of_mul_equiv_of_mul_equiv_apply
  {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) (x) :
  (f.of_mul_equiv_of_localizations (f.mul_equiv_of_mul_equiv k H)).to_map x = k.to_map (j x) :=
ext_iff.1 (f.mul_equiv_of_localizations_right_inv (k.of_mul_equiv_of_dom H)) x

@[to_additive] lemma of_mul_equiv_of_mul_equiv
  {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) :
  (f.of_mul_equiv_of_localizations (f.mul_equiv_of_mul_equiv k H)).to_map =
    k.to_map.comp j.to_monoid_hom :=
monoid_hom.ext $ f.of_mul_equiv_of_mul_equiv_apply H

end localization_map
end submonoid
namespace localization
variables (S)

/-- Natural hom sending `x : M`, `M` a `comm_monoid`, to the equivalence class of
`(x, 1)` in the localization of `M` at a submonoid. -/
@[to_additive "Natural homomorphism sending `x : M`, `M` an `add_comm_monoid`, to the equivalence
class of `(x, 0)` in the localization of `M` at a submonoid."]
def monoid_of : submonoid.localization_map S (localization S) :=
{ map_units' := λ y, is_unit_iff_exists_inv.2 ⟨mk 1 y, (r S).eq.2 $
    show r S (_, 1 * y) 1, by simpa using (r S).symm (one_rel y)⟩,
  surj' := λ z, induction_on z $ λ x, ⟨x, (r S).eq.2 $
    show r S (x.1 * x.2, x.2 * 1) (x.1, 1), by
      rw [mul_comm x.2, ←mul_one (x.1, (1 : S))];
      exact (r S).mul ((r S).refl (x.1, 1)) ((r S).symm $ one_rel x.2)⟩,
  eq_iff_exists' := λ x y, (r S).eq.trans $ r_iff_exists.trans $
    show (∃ (c : S), x * 1 * c = y * 1 * c) ↔ _, by rw [mul_one, mul_one],
  ..(r S).mk'.comp $ monoid_hom.inl M S }

variables {S}

@[to_additive] lemma mk_one_eq_monoid_of_mk (x) : mk x 1 = (monoid_of S).to_map x := rfl

@[to_additive] lemma mk_eq_monoid_of_mk'_apply (x y) : mk x y = (monoid_of S).mk' x y :=
show _ = _ * _, from (submonoid.localization_map.mul_inv_right (monoid_of S).map_units _ _ _).2 $
begin
  rw [←mk_one_eq_monoid_of_mk, ←mk_one_eq_monoid_of_mk,
      show mk x y * mk y 1 = mk (x * y) (1 * y), by rw mul_comm 1 y; refl,
      show mk x 1 = mk (x * 1) ((1 : S) * 1), by rw [mul_one, mul_one]],
  exact (con.eq _).2 (con.symm _ $ (localization.r S).mul
    (con.refl _ (x, 1)) $ one_rel _),
end

@[simp, to_additive] lemma mk_eq_monoid_of_mk' : mk = (monoid_of S).mk' :=
funext $ λ _, funext $ λ _, mk_eq_monoid_of_mk'_apply _ _

variables (f : submonoid.localization_map S N)
/-- Given a localization map `f : M →* N` for a submonoid `S`, we get an isomorphism between
the localization of `M` at `S` as a quotient type and `N`. -/
@[to_additive "Given a localization map `f : M →+ N` for a submonoid `S`, we get an isomorphism
between the localization of `M` at `S` as a quotient type and `N`."]
noncomputable def mul_equiv_of_quotient (f : submonoid.localization_map S N) :
  localization S ≃* N :=
(monoid_of S).mul_equiv_of_localizations f

variables {f}

@[simp, to_additive] lemma mul_equiv_of_quotient_apply (x) :
  mul_equiv_of_quotient f x = (monoid_of S).lift f.map_units x := rfl

@[simp, to_additive] lemma mul_equiv_of_quotient_mk' (x y) :
  mul_equiv_of_quotient f ((monoid_of S).mk' x y) = f.mk' x y :=
(monoid_of S).lift_mk' _ _ _

@[to_additive] lemma mul_equiv_of_quotient_mk (x y) :
  mul_equiv_of_quotient f (mk x y) = f.mk' x y :=
by rw mk_eq_monoid_of_mk'_apply; exact mul_equiv_of_quotient_mk' _ _

@[simp, to_additive] lemma mul_equiv_of_quotient_monoid_of (x) :
  mul_equiv_of_quotient f ((monoid_of S).to_map x) = f.to_map x :=
(monoid_of S).lift_eq _ _

@[simp, to_additive] lemma mul_equiv_of_quotient_symm_mk' (x y) :
  (mul_equiv_of_quotient f).symm (f.mk' x y) = (monoid_of S).mk' x y :=
f.lift_mk' _ _ _

@[to_additive] lemma mul_equiv_of_quotient_symm_mk (x y) :
  (mul_equiv_of_quotient f).symm (f.mk' x y) = mk x y :=
by rw mk_eq_monoid_of_mk'_apply; exact mul_equiv_of_quotient_symm_mk' _ _

@[simp, to_additive] lemma mul_equiv_of_quotient_symm_monoid_of (x) :
  (mul_equiv_of_quotient f).symm (f.to_map x) = (monoid_of S).to_map x :=
f.lift_eq _ _

section away

variables (x : M)

/-- Given `x : M`, the localization of `M` at the submonoid generated by `x`, as a quotient. -/
@[reducible, to_additive "Given `x : M`, the localization of `M` at the submonoid generated
by `x`, as a quotient."]
def away := localization (submonoid.powers x)

/-- Given `x : M`, `inv_self` is `x⁻¹` in the localization (as a quotient type) of `M` at the
submonoid generated by `x`. -/
@[to_additive "Given `x : M`, `neg_self` is `-x` in the localization (as a quotient type) of `M`
at the submonoid generated by `x`."]
def away.inv_self : away x :=
mk 1 ⟨x, submonoid.mem_powers _⟩

/-- Given `x : M`, the natural hom sending `y : M`, `M` a `comm_monoid`, to the equivalence class
of `(y, 1)` in the localization of `M` at the submonoid generated by `x`. -/
@[reducible, to_additive "Given `x : M`, the natural hom sending `y : M`, `M` an `add_comm_monoid`,
to the equivalence class of `(y, 0)` in the localization of `M` at the submonoid
generated by `x`."]
def away.monoid_of : submonoid.localization_map.away_map x (away x) :=
monoid_of (submonoid.powers x)

@[simp, to_additive] lemma away.mk_eq_monoid_of_mk' : mk = (away.monoid_of x).mk' :=
mk_eq_monoid_of_mk'

/-- Given `x : M` and a localization map `f : M →* N` away from `x`, we get an isomorphism between
the localization of `M` at the submonoid generated by `x` as a quotient type and `N`. -/
@[to_additive "Given `x : M` and a localization map `f : M →+ N` away from `x`, we get an
isomorphism between the localization of `M` at the submonoid generated by `x` as a quotient type
and `N`."]
noncomputable def away.mul_equiv_of_quotient (f : submonoid.localization_map.away_map x N) :
  away x ≃* N :=
mul_equiv_of_quotient f

end away
end localization
