/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import algebra.group.basic
import tactic.ext

/-!
# monoid and group homomorphisms

This file defines the bundled structures for monoid and group homomorphisms. Namely, we define
`monoid_hom` (resp., `add_monoid_hom`) to be bundled homomorphisms between multiplicative (resp.,
additive) monoids or groups.

We also define coercion to a function, and  usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.

## Notations

* `→*` for bundled monoid homs (also use for group homs)
* `→+` for bundled add_monoid homs (also use for add_group homs)

## implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `group_hom` -- the idea is that `monoid_hom` is used.
The constructor for `monoid_hom` needs a proof of `map_one` as well
as `map_mul`; a separate constructor `monoid_hom.mk'` will construct
group homs (i.e. monoid homs between groups) given only a proof
that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets.  This is done when the
instances can be inferred because they are implicit arguments to the type `monoid_hom`.  When they
can be inferred from the type it is faster to use this method than to use type class inference.

Historically this file also included definitions of unbundled homomorphism classes; they were
deprecated and moved to `deprecated/group`.

## Tags

monoid_hom, add_monoid_hom

-/

variables {M : Type*} {N : Type*} {P : Type*} -- monoids
  {G : Type*} {H : Type*} -- groups

/-- Bundled add_monoid homomorphisms; use this for bundled add_group homomorphisms too. -/
structure add_monoid_hom (M : Type*) (N : Type*) [add_monoid M] [add_monoid N] :=
(to_fun : M → N)
(map_zero' : to_fun 0 = 0)
(map_add' : ∀ x y, to_fun (x + y) = to_fun x + to_fun y)

infixr ` →+ `:25 := add_monoid_hom

/-- Bundled monoid homomorphisms; use this for bundled group homomorphisms too. -/
@[to_additive add_monoid_hom]
structure monoid_hom (M : Type*) (N : Type*) [monoid M] [monoid N] :=
(to_fun : M → N)
(map_one' : to_fun 1 = 1)
(map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

infixr ` →* `:25 := monoid_hom

@[to_additive]
instance {M : Type*} {N : Type*} {mM : monoid M} {mN : monoid N} : has_coe_to_fun (M →* N) :=
⟨_, monoid_hom.to_fun⟩

namespace monoid_hom
variables {mM : monoid M} {mN : monoid N} {mP : monoid P}
variables [group G] [comm_group H]

include mM mN

@[simp, to_additive]
lemma to_fun_eq_coe (f : M →* N) : f.to_fun = f := rfl

@[simp, to_additive]
lemma coe_mk (f : M → N) (h1 hmul) : ⇑(monoid_hom.mk f h1 hmul) = f := rfl

@[to_additive]
lemma coe_inj ⦃f g : M →* N⦄ (h : (f : M → N) = g) : f = g :=
by cases f; cases g; cases h; refl

@[ext, to_additive]
lemma ext ⦃f g : M →* N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj (funext h)

attribute [ext] _root_.add_monoid_hom.ext

@[to_additive]
lemma ext_iff {f g : M →* N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

/-- If f is a monoid homomorphism then f 1 = 1. -/
@[simp, to_additive]
lemma map_one (f : M →* N) : f 1 = 1 := f.map_one'

/-- If f is a monoid homomorphism then f (a * b) = f a * f b. -/
@[simp, to_additive]
lemma map_mul (f : M →* N) (a b : M) : f (a * b) = f a * f b := f.map_mul' a b

@[to_additive]
lemma map_mul_eq_one (f : M →* N) {a b : M} (h : a * b = 1) : f a * f b = 1 :=
by rw [← f.map_mul, h, f.map_one]

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a right inverse,
then `f x` has a right inverse too. For elements invertible on both sides see `is_unit.map`. -/
@[to_additive "Given an add_monoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has
a right inverse, then `f x` has a right inverse too."]
lemma map_exists_right_inv (f : M →* N) {x : M} (hx : ∃ y, x * y = 1) :
  ∃ y, f x * y = 1 :=
let ⟨y, hy⟩ := hx in ⟨f y, f.map_mul_eq_one hy⟩

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a left inverse,
then `f x` has a left inverse too. For elements invertible on both sides see `is_unit.map`. -/
@[to_additive "Given an add_monoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has
a left inverse, then `f x` has a left inverse too. For elements invertible on both sides see
`is_add_unit.map`."]
lemma map_exists_left_inv (f : M →* N) {x : M} (hx : ∃ y, y * x = 1) :
  ∃ y, y * f x = 1 :=
let ⟨y, hy⟩ := hx in ⟨f y, f.map_mul_eq_one hy⟩

omit mN mM

/-- The identity map from a monoid to itself. -/
@[to_additive]
def id (M : Type*) [monoid M] : M →* M :=
{ to_fun := id,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

@[simp, to_additive] lemma id_apply {M : Type*} [monoid M] (x : M) :
  id M x = x := rfl

include mM mN mP

/-- Composition of monoid morphisms is a monoid morphism. -/
@[to_additive]
def comp (hnp : N →* P) (hmn : M →* N) : M →* P :=
{ to_fun := hnp ∘ hmn,
  map_one' := by simp,
  map_mul' := by simp }

@[simp, to_additive] lemma comp_apply (g : N →* P) (f : M →* N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of monoid homomorphisms is associative. -/
@[to_additive] lemma comp_assoc {Q : Type*} [monoid Q] (f : M →* N) (g : N →* P) (h : P →* Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

@[to_additive]
lemma cancel_right {g₁ g₂ : N →* P} {f : M →* N} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, monoid_hom.ext $ (forall_iff_forall_surj hf).1 (ext_iff.1 h), λ h, h ▸ rfl⟩

@[to_additive]
lemma cancel_left {g : N →* P} {f₁ f₂ : M →* N} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, monoid_hom.ext $ λ x, hg $ by rw [← comp_apply, h, comp_apply], λ h, h ▸ rfl⟩

omit mP

@[simp, to_additive] lemma comp_id (f : M →* N) : f.comp (id M) = f := ext $ λ x, rfl
@[simp, to_additive] lemma id_comp (f : M →* N) : (id N).comp f = f := ext $ λ x, rfl

variables [mM] [mN]

@[to_additive]
protected def one : M →* N :=
{ to_fun := λ _, 1,
  map_one' := rfl,
  map_mul' := λ _ _, (one_mul 1).symm }

@[to_additive]
instance : has_one (M →* N) := ⟨monoid_hom.one⟩

@[simp, to_additive] lemma one_apply (x : M) : (1 : M →* N) x = 1 := rfl

@[to_additive]
instance : inhabited (M →* N) := ⟨1⟩

omit mM mN

/-- The product of two monoid morphisms is a monoid morphism if the target is commutative. -/
@[to_additive]
protected def mul {M N} {mM : monoid M} [comm_monoid N] (f g : M →* N) : M →* N :=
{ to_fun := λ m, f m * g m,
  map_one' := show f 1 * g 1 = 1, by simp,
  map_mul' := begin intros, show f (x * y) * g (x * y) = f x * g x * (f y * g y),
    rw [f.map_mul, g.map_mul, ←mul_assoc, ←mul_assoc, mul_right_comm (f x)], end }

@[to_additive]
instance {M N} {mM : monoid M} [comm_monoid N] : has_mul (M →* N) := ⟨monoid_hom.mul⟩

@[simp, to_additive] lemma mul_apply {M N} {mM : monoid M} {mN : comm_monoid N}
  (f g : M →* N) (x : M) :
  (f * g) x = f x * g x := rfl

/-- (M →* N) is a comm_monoid if N is commutative. -/
@[to_additive add_comm_monoid]
instance {M N} [monoid M] [comm_monoid N] : comm_monoid (M →* N) :=
{ mul := (*),
  mul_assoc := by intros; ext; apply mul_assoc,
  one := 1,
  one_mul := by intros; ext; apply one_mul,
  mul_comm := by intros; ext; apply mul_comm }

/-- `flip` arguments of `f : M →* N →* P` -/
@[to_additive "`flip` arguments of `f : M →+ N →+ P`"]
def flip {mM : monoid M} {mN : monoid N} {mP : comm_monoid P} (f : M →* N →* P) :
  N →* M →* P :=
{ to_fun := λ y, ⟨λ x, f x y, by rw [f.map_one, one_apply], λ x₁ x₂, by rw [f.map_mul, mul_apply]⟩,
  map_one' := ext $ λ x, (f x).map_one,
  map_mul' := λ y₁ y₂, ext $ λ x, (f x).map_mul y₁ y₂ }

@[simp, to_additive] lemma flip_apply {mM : monoid M} {mN : monoid N} {mP : comm_monoid P}
  (f : M →* N →* P) (x : M) (y : N) :
  f.flip y x = f x y :=
rfl

/-- Group homomorphisms preserve inverse. -/
@[simp, to_additive]
theorem map_inv {G H} [group G] [group H] (f : G →* H) (g : G) : f g⁻¹ = (f g)⁻¹ :=
eq_inv_of_mul_eq_one $ by rw [←f.map_mul, inv_mul_self, f.map_one]

/-- Group homomorphisms preserve division. -/
@[simp, to_additive]
theorem map_mul_inv {G H} [group G] [group H] (f : G →* H) (g h : G) :
  f (g * h⁻¹) = (f g) * (f h)⁻¹ := by rw [f.map_mul, f.map_inv]

/-- A group homomorphism is injective iff its kernel is trivial. -/
@[to_additive]
lemma injective_iff {G H} [group G] [group H] (f : G →* H) :
  function.injective f ↔ (∀ a, f a = 1 → a = 1) :=
⟨λ h _, by rw ← f.map_one; exact @h _ _,
  λ h x y hxy, by rw [← inv_inv (f x), inv_eq_iff_mul_eq_one, ← f.map_inv,
      ← f.map_mul] at hxy;
    simpa using inv_eq_of_mul_eq_one (h _ hxy)⟩

include mM
/-- Makes a group homomomorphism from a proof that the map preserves multiplication. -/
@[to_additive]
def mk' (f : M → G) (map_mul : ∀ a b : M, f (a * b) = f a * f b) : M →* G :=
{ to_fun := f,
  map_mul' := map_mul,
  map_one' := mul_self_iff_eq_one.1 $ by rw [←map_mul, mul_one] }

@[simp, to_additive]
lemma coe_mk' {f : M → G} (map_mul : ∀ a b : M, f (a * b) = f a * f b) :
  ⇑(mk' f map_mul) = f := rfl

omit mM

/-- The inverse of a monoid homomorphism is a monoid homomorphism if the target is
    a commutative group.-/
@[to_additive]
protected def inv {M G} {mM : monoid M} [comm_group G] (f : M →* G) : M →* G :=
mk' (λ g, (f g)⁻¹) $ λ a b, by rw [←mul_inv, f.map_mul]

@[to_additive]
instance {M G} [monoid M] [comm_group G] : has_inv (M →* G) := ⟨monoid_hom.inv⟩

@[simp, to_additive] lemma inv_apply {M G} {mM : monoid M} {gG : comm_group G}
  (f : M →* G) (x : M) :
  f⁻¹ x = (f x)⁻¹ := rfl

/-- (M →* G) is a comm_group if G is a comm_group -/
@[to_additive add_comm_group]
instance {M G} [monoid M] [comm_group G] : comm_group (M →* G) :=
{ inv := has_inv.inv,
  mul_left_inv := by intros; ext; apply mul_left_inv,
  ..monoid_hom.comm_monoid }

end monoid_hom

namespace add_monoid_hom

/-- Additive group homomorphisms preserve subtraction. -/
@[simp] theorem map_sub {G H} [add_group G] [add_group H] (f : G →+ H) (g h : G) :
  f (g - h) = (f g) - (f h) := f.map_add_neg g h

end add_monoid_hom
