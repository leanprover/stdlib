/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Yury Kudryashov
-/
import data.equiv.mul_add

/-!
# Monoid, group etc structures on `M × N`

In this file we define one-binop (`monoid`, `group` etc) structures on `M × N`. We also prove
trivial `simp` lemmas, and define the following operations on `monoid_hom`s:

* `fst M N : M × N →* M`, `snd M N : M × N →* N`: projections `prod.fst` and `prod.snd`
  as `monoid_hom`s;
* `inl M N : M →* M × N`, `inr M N : N →* M × N`: inclusions of first/second monoid
  into the product;
* `f.prod g : `M →* N × P`: sends `x` to `(f x, g x)`;
* `f.coprod g : M × N →* P`: sends `(x, y)` to `f x * g y`;
* `f.prod_map g : M × N → M' × N'`: `prod.map f g` as a `monoid_hom`,
  sends `(x, y)` to `(f x, g y)`.
-/

variables {A : Type*} {B : Type*} {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

namespace prod

@[to_additive]
instance [has_mul M] [has_mul N] : has_mul (M × N) := ⟨λ p q, ⟨p.1 * q.1, p.2 * q.2⟩⟩

@[simp, to_additive]
lemma fst_mul [has_mul M] [has_mul N] (p q : M × N) : (p * q).1 = p.1 * q.1 := rfl
@[simp, to_additive]
lemma snd_mul [has_mul M] [has_mul N] (p q : M × N) : (p * q).2 = p.2 * q.2 := rfl
@[simp, to_additive]
lemma mk_mul_mk [has_mul M] [has_mul N] (a₁ a₂ : M) (b₁ b₂ : N) :
  (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) := rfl

@[to_additive]
instance [has_one M] [has_one N] : has_one (M × N) := ⟨(1, 1)⟩

@[simp, to_additive]
lemma fst_one [has_one M] [has_one N] : (1 : M × N).1 = 1 := rfl
@[simp, to_additive]
lemma snd_one [has_one M] [has_one N] : (1 : M × N).2 = 1 := rfl
@[to_additive]
lemma one_eq_mk [has_one M] [has_one N] : (1 : M × N) = (1, 1) := rfl
@[simp, to_additive]
lemma mk_eq_one [has_one M] [has_one N] {x : M} {y : N} : (x, y) = 1 ↔ x = 1 ∧ y = 1 :=
mk.inj_iff

@[to_additive]
lemma fst_mul_snd [monoid M] [monoid N] (p : M × N) :
  (p.fst, 1) * (1, p.snd) = p :=
ext (mul_one p.1) (one_mul p.2)

@[to_additive]
instance [has_inv M] [has_inv N] : has_inv (M × N) := ⟨λp, (p.1⁻¹, p.2⁻¹)⟩

@[simp, to_additive]
lemma fst_inv [has_inv G] [has_inv H] (p : G × H) : (p⁻¹).1 = (p.1)⁻¹ := rfl
@[simp, to_additive]
lemma snd_inv [has_inv G] [has_inv H] (p : G × H) : (p⁻¹).2 = (p.2)⁻¹ := rfl
@[simp, to_additive]
lemma inv_mk [has_inv G] [has_inv H] (a : G) (b : H) : (a, b)⁻¹ = (a⁻¹, b⁻¹) := rfl

@[to_additive]
instance [has_div M] [has_div N] : has_div (M × N) := ⟨λ p q, ⟨p.1 / q.1, p.2 / q.2⟩⟩

@[simp] lemma fst_sub [add_group A] [add_group B] (a b : A × B) : (a - b).1 = a.1 - b.1 := rfl
@[simp] lemma snd_sub [add_group A] [add_group B] (a b : A × B) : (a - b).2 = a.2 - b.2 := rfl
@[simp] lemma mk_sub_mk [add_group A] [add_group B] (x₁ x₂ : A) (y₁ y₂ : B) :
(x₁, y₁) - (x₂, y₂) = (x₁ - x₂, y₁ - y₂) := rfl

@[to_additive]
instance [semigroup M] [semigroup N] : semigroup (M × N) :=
{ mul_assoc := assume a b c, mk.inj_iff.mpr ⟨mul_assoc _ _ _, mul_assoc _ _ _⟩,
  .. prod.has_mul }

@[to_additive]
instance [monoid M] [monoid N] : monoid (M × N) :=
{ one_mul := assume a, prod.rec_on a $ λa b, mk.inj_iff.mpr ⟨one_mul _, one_mul _⟩,
  mul_one := assume a, prod.rec_on a $ λa b, mk.inj_iff.mpr ⟨mul_one _, mul_one _⟩,
  .. prod.semigroup, .. prod.has_one }

@[to_additive]
instance [group G] [group H] : group (G × H) :=
{ mul_left_inv := assume a, mk.inj_iff.mpr ⟨mul_left_inv _, mul_left_inv _⟩,
  div_eq_mul_inv := λ a b, mk.inj_iff.mpr ⟨div_eq_mul_inv _ _, div_eq_mul_inv _ _⟩,
  .. prod.monoid, .. prod.has_inv, .. prod.has_div }

@[to_additive]
instance [comm_semigroup G] [comm_semigroup H] : comm_semigroup (G × H) :=
{ mul_comm := assume a b, mk.inj_iff.mpr ⟨mul_comm _ _, mul_comm _ _⟩,
  .. prod.semigroup }

@[to_additive]
instance [left_cancel_semigroup G] [left_cancel_semigroup H] :
  left_cancel_semigroup (G × H) :=
{ mul_left_cancel := λ a b c h, prod.ext (mul_left_cancel (prod.ext_iff.1 h).1)
    (mul_left_cancel (prod.ext_iff.1 h).2),
  .. prod.semigroup }

@[to_additive]
instance [right_cancel_semigroup G] [right_cancel_semigroup H] :
  right_cancel_semigroup (G × H) :=
{ mul_right_cancel := λ a b c h, prod.ext (mul_right_cancel (prod.ext_iff.1 h).1)
    (mul_right_cancel (prod.ext_iff.1 h).2),
  .. prod.semigroup }

@[to_additive]
instance [comm_monoid M] [comm_monoid N] : comm_monoid (M × N) :=
{ .. prod.comm_semigroup, .. prod.monoid }

@[to_additive]
instance [comm_group G] [comm_group H] : comm_group (G × H) :=
{ .. prod.comm_semigroup, .. prod.group }

end prod

namespace monoid_hom

variables (M N) [monoid M] [monoid N]

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `M`.-/
@[to_additive "Given additive monoids `A`, `B`, the natural projection homomorphism
from `A × B` to `A`"]
def fst : M × N →* M := ⟨prod.fst, rfl, λ _ _, rfl⟩

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `N`.-/
@[to_additive "Given additive monoids `A`, `B`, the natural projection homomorphism
from `A × B` to `B`"]
def snd : M × N →* N := ⟨prod.snd, rfl, λ _ _, rfl⟩

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `M` to `M × N`. -/
@[to_additive "Given additive monoids `A`, `B`, the natural inclusion homomorphism
from `A` to `A × B`."]
def inl : M →* M × N :=
⟨λ x, (x, 1), rfl, λ _ _, prod.ext rfl (one_mul 1).symm⟩

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `N` to `M × N`. -/
@[to_additive "Given additive monoids `A`, `B`, the natural inclusion homomorphism
from `B` to `A × B`."]
def inr : N →* M × N :=
⟨λ y, (1, y), rfl, λ _ _, prod.ext (one_mul 1).symm rfl⟩

variables {M N}

@[simp, to_additive] lemma coe_fst : ⇑(fst M N) = prod.fst := rfl
@[simp, to_additive] lemma coe_snd : ⇑(snd M N) = prod.snd := rfl

@[simp, to_additive] lemma inl_apply (x) : inl M N x = (x, 1) := rfl
@[simp, to_additive] lemma inr_apply (y) : inr M N y = (1, y) := rfl

@[simp, to_additive] lemma fst_comp_inl : (fst M N).comp (inl M N) = id M := rfl
@[simp, to_additive] lemma snd_comp_inl : (snd M N).comp (inl M N) = 1 := rfl
@[simp, to_additive] lemma fst_comp_inr : (fst M N).comp (inr M N) = 1 := rfl
@[simp, to_additive] lemma snd_comp_inr : (snd M N).comp (inr M N) = id N := rfl

section prod

variable [monoid P]

/-- Combine two `monoid_hom`s `f : M →* N`, `g : M →* P` into `f.prod g : M →* N × P`
given by `(f.prod g) x = (f x, g x)` -/
@[to_additive prod "Combine two `add_monoid_hom`s `f : M →+ N`, `g : M →+ P` into
`f.prod g : M →+ N × P` given by `(f.prod g) x = (f x, g x)`"]
protected def prod (f : M →* N) (g : M →* P) : M →* N × P :=
{ to_fun := λ x, (f x, g x),
  map_one' := prod.ext f.map_one g.map_one,
  map_mul' := λ x y, prod.ext (f.map_mul x y) (g.map_mul x y) }

@[simp, to_additive prod_apply]
lemma prod_apply (f : M →* N) (g : M →* P) (x) : f.prod g x = (f x, g x) := rfl

@[simp, to_additive fst_comp_prod]
lemma fst_comp_prod (f : M →* N) (g : M →* P) : (fst N P).comp (f.prod g) = f :=
ext $ λ x, rfl

@[simp, to_additive snd_comp_prod]
lemma snd_comp_prod (f : M →* N) (g : M →* P) : (snd N P).comp (f.prod g) = g :=
ext $ λ x, rfl

@[simp, to_additive prod_unique]
lemma prod_unique (f : M →* N × P) :
  ((fst N P).comp f).prod ((snd N P).comp f) = f :=
ext $ λ x, by simp only [prod_apply, coe_fst, coe_snd, comp_apply, prod.mk.eta]

end prod

section prod_map

variables {M' : Type*} {N' : Type*} [monoid M'] [monoid N'] [monoid P]
  (f : M →* M') (g : N →* N')

/-- `prod.map` as a `monoid_hom`. -/
@[to_additive prod_map "`prod.map` as an `add_monoid_hom`"]
def prod_map : M × N →* M' × N' := (f.comp (fst M N)).prod (g.comp (snd M N))

@[to_additive prod_map_def]
lemma prod_map_def : prod_map f g = (f.comp (fst M N)).prod (g.comp (snd M N)) := rfl

@[simp, to_additive coe_prod_map]
lemma coe_prod_map : ⇑(prod_map f g) = prod.map f g := rfl

@[to_additive prod_comp_prod_map]
lemma prod_comp_prod_map (f : P →* M) (g : P →* N) (f' : M →* M') (g' : N →* N') :
  (f'.prod_map g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
rfl

end prod_map

section coprod

variables [comm_monoid P] (f : M →* P) (g : N →* P)

/-- Coproduct of two `monoid_hom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 * g p.2`. -/
@[to_additive "Coproduct of two `add_monoid_hom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 + g p.2`."]
def coprod : M × N →* P := f.comp (fst M N) * g.comp (snd M N)

@[simp, to_additive]
lemma coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 := rfl

@[simp, to_additive]
lemma coprod_comp_inl : (f.coprod g).comp (inl M N) = f :=
ext $ λ x, by simp [coprod_apply]

@[simp, to_additive]
lemma coprod_comp_inr : (f.coprod g).comp (inr M N) = g :=
ext $ λ x, by simp [coprod_apply]

@[simp, to_additive] lemma coprod_unique (f : M × N →* P) :
  (f.comp (inl M N)).coprod (f.comp (inr M N)) = f :=
ext $ λ x, by simp [coprod_apply, inl_apply, inr_apply, ← map_mul]

@[simp, to_additive] lemma coprod_inl_inr {M N : Type*} [comm_monoid M] [comm_monoid N] :
  (inl M N).coprod (inr M N) = id (M × N) :=
coprod_unique (id $ M × N)

lemma comp_coprod {Q : Type*} [comm_monoid Q] (h : P →* Q) (f : M →* P) (g : N →* P) :
  h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
ext $ λ x, by simp

end coprod

end monoid_hom

namespace mul_equiv
variables {M N} [monoid M] [monoid N]

/-- The equivalence between `M × N` and `N × M` given by swapping the components is multiplicative. -/
@[to_additive prod_comm "The equivalence between `M × N` and `N × M` given by swapping the components is
additive."]
def prod_comm : M × N ≃* N × M :=
{ map_mul' := λ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩, rfl, ..equiv.prod_comm M N }

@[simp, to_additive coe_prod_comm] lemma coe_prod_comm : ⇑(prod_comm : M × N ≃* N × M) = prod.swap := rfl
@[simp, to_additive coe_prod_comm_symm] lemma coe_prod_comm_symm :
  ⇑((prod_comm : M × N ≃* N × M).symm) = prod.swap := rfl

/-- The monoid equivalence between units of a product of two monoids, and the product of the
    units of each monoid. -/
@[to_additive prod_add_units "The additive monoid equivalence between additive units of a product
of two additive monoids, and the product of the additive units of each additive monoid."]
def prod_units : units (M × N) ≃* units M × units N :=
{ to_fun := (units.map (monoid_hom.fst M N)).prod (units.map (monoid_hom.snd M N)),
  inv_fun := λ u, ⟨(u.1, u.2), (↑u.1⁻¹, ↑u.2⁻¹), by simp, by simp⟩,
  left_inv := λ u, by simp,
  right_inv := λ ⟨u₁, u₂⟩, by simp [units.map],
  map_mul' := monoid_hom.map_mul _ }

end mul_equiv
