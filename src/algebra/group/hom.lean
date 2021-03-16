/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import algebra.group.commute
import algebra.group_with_zero.defs

/-!
# monoid and group homomorphisms

This file defines the bundled structures for monoid and group homomorphisms. Namely, we define
`monoid_hom` (resp., `add_monoid_hom`) to be bundled homomorphisms between multiplicative (resp.,
additive) monoids or groups.

We also define coercion to a function, and  usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.

This file also defines the lesser-used (and notation-less) homomorphism types which are used as
building blocks for other homomorphisms:

* `zero_hom`
* `one_hom`
* `add_hom`
* `mul_hom`
* `monoid_with_zero_hom`

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

-- for easy multiple inheritance
set_option old_structure_cmd true

/-- Homomorphism that preserves zero -/
structure zero_hom (M : Type*) (N : Type*) [has_zero M] [has_zero N] :=
(to_fun : M → N)
(map_zero' : to_fun 0 = 0)

/-- Homomorphism that preserves addition -/
structure add_hom (M : Type*) (N : Type*) [has_add M] [has_add N] :=
(to_fun : M → N)
(map_add' : ∀ x y, to_fun (x + y) = to_fun x + to_fun y)

/-- Bundled add_monoid homomorphisms; use this for bundled add_group homomorphisms too. -/
@[ancestor zero_hom add_hom]
structure add_monoid_hom (M : Type*) (N : Type*) [add_monoid M] [add_monoid N]
  extends zero_hom M N, add_hom M N

attribute [nolint doc_blame] add_monoid_hom.to_add_hom
attribute [nolint doc_blame] add_monoid_hom.to_zero_hom

infixr ` →+ `:25 := add_monoid_hom

/-- Homomorphism that preserves one -/
@[to_additive]
structure one_hom (M : Type*) (N : Type*) [has_one M] [has_one N] :=
(to_fun : M → N)
(map_one' : to_fun 1 = 1)

/-- Homomorphism that preserves multiplication -/
@[to_additive]
structure mul_hom (M : Type*) (N : Type*) [has_mul M] [has_mul N] :=
(to_fun : M → N)
(map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

/-- Bundled monoid homomorphisms; use this for bundled group homomorphisms too. -/
@[ancestor one_hom mul_hom, to_additive]
structure monoid_hom (M : Type*) (N : Type*) [monoid M] [monoid N] extends one_hom M N, mul_hom M N

/-- Bundled monoid with zero homomorphisms; use this for bundled group with zero homomorphisms
too. -/
@[ancestor zero_hom monoid_hom]
structure monoid_with_zero_hom (M : Type*) (N : Type*) [monoid_with_zero M] [monoid_with_zero N]
  extends zero_hom M N, monoid_hom M N

attribute [nolint doc_blame] monoid_hom.to_mul_hom
attribute [nolint doc_blame] monoid_hom.to_one_hom
attribute [nolint doc_blame] monoid_with_zero_hom.to_monoid_hom
attribute [nolint doc_blame] monoid_with_zero_hom.to_zero_hom

infixr ` →* `:25 := monoid_hom

-- completely uninteresting lemmas about coercion to function, that all homs need
section coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/
@[to_additive]
instance monoid_hom.has_coe_to_one_hom {mM : monoid M} {mN : monoid N} :
  has_coe (M →* N) (one_hom M N) := ⟨monoid_hom.to_one_hom⟩
@[to_additive]
instance monoid_hom.has_coe_to_mul_hom {mM : monoid M} {mN : monoid N} :
  has_coe (M →* N) (mul_hom M N) := ⟨monoid_hom.to_mul_hom⟩
instance monoid_with_zero_hom.has_coe_to_monoid_hom
  {mM : monoid_with_zero M} {mN : monoid_with_zero N} :
  has_coe (monoid_with_zero_hom M N) (M →* N) := ⟨monoid_with_zero_hom.to_monoid_hom⟩
instance monoid_with_zero_hom.has_coe_to_zero_hom
  {mM : monoid_with_zero M} {mN : monoid_with_zero N} :
  has_coe (monoid_with_zero_hom M N) (zero_hom M N) := ⟨monoid_with_zero_hom.to_zero_hom⟩

/-! The simp-normal form of morphism coercion is `f.to_..._hom`. This choice is primarily because
this is the way things were before the above coercions were introduced. Bundled morphisms defined
elsewhere in Mathlib may choose `↑f` as their simp-normal form instead. -/
@[simp, to_additive]
lemma monoid_hom.coe_eq_to_one_hom {mM : monoid M} {mN : monoid N} (f : M →* N) :
  (f : one_hom M N) = f.to_one_hom := rfl
@[simp, to_additive]
lemma monoid_hom.coe_eq_to_mul_hom {mM : monoid M} {mN : monoid N} (f : M →* N) :
  (f : mul_hom M N) = f.to_mul_hom := rfl
@[simp]
lemma monoid_with_zero_hom.coe_eq_to_monoid_hom {mM : monoid_with_zero M} {mN : monoid_with_zero N}
  (f : monoid_with_zero_hom M N) : (f : M →* N) = f.to_monoid_hom := rfl
@[simp]
lemma monoid_with_zero_hom.coe_eq_to_zero_hom {mM : monoid_with_zero M} {mN : monoid_with_zero N}
  (f : monoid_with_zero_hom M N) : (f : zero_hom M N) = f.to_zero_hom := rfl

@[to_additive]
instance {mM : has_one M} {mN : has_one N} : has_coe_to_fun (one_hom M N) :=
⟨_, one_hom.to_fun⟩
@[to_additive]
instance {mM : has_mul M} {mN : has_mul N} : has_coe_to_fun (mul_hom M N) :=
⟨_, mul_hom.to_fun⟩
@[to_additive]
instance {mM : monoid M} {mN : monoid N} : has_coe_to_fun (M →* N) :=
⟨_, monoid_hom.to_fun⟩
instance {mM : monoid_with_zero M} {mN : monoid_with_zero N} :
  has_coe_to_fun (monoid_with_zero_hom M N) :=
⟨_, monoid_with_zero_hom.to_fun⟩

-- these must come after the coe_to_fun definitions
initialize_simps_projections zero_hom (to_fun → apply)
initialize_simps_projections add_hom (to_fun → apply)
initialize_simps_projections add_monoid_hom (to_fun → apply)

initialize_simps_projections one_hom (to_fun → apply)
initialize_simps_projections mul_hom (to_fun → apply)
initialize_simps_projections monoid_hom (to_fun → apply)
initialize_simps_projections monoid_with_zero_hom (to_fun → apply)

@[simp, to_additive]
lemma one_hom.to_fun_eq_coe [has_one M] [has_one N] (f : one_hom M N) : f.to_fun = f := rfl
@[simp, to_additive]
lemma mul_hom.to_fun_eq_coe [has_mul M] [has_mul N] (f : mul_hom M N) : f.to_fun = f := rfl
@[simp, to_additive]
lemma monoid_hom.to_fun_eq_coe [monoid M] [monoid N] (f : M →* N) : f.to_fun = f := rfl
@[simp]
lemma monoid_with_zero_hom.to_fun_eq_coe [monoid_with_zero M] [monoid_with_zero N]
  (f : monoid_with_zero_hom M N) : f.to_fun = f := rfl

@[simp, to_additive]
lemma one_hom.coe_mk [has_one M] [has_one N]
  (f : M → N) (h1) : ⇑(one_hom.mk f h1) = f := rfl
@[simp, to_additive]
lemma mul_hom.coe_mk [has_mul M] [has_mul N]
  (f : M → N) (hmul) : ⇑(mul_hom.mk f hmul) = f := rfl
@[simp, to_additive]
lemma monoid_hom.coe_mk [monoid M] [monoid N]
  (f : M → N) (h1 hmul) : ⇑(monoid_hom.mk f h1 hmul) = f := rfl
@[simp]
lemma monoid_with_zero_hom.coe_mk [monoid_with_zero M] [monoid_with_zero N]
  (f : M → N) (h0 h1 hmul) : ⇑(monoid_with_zero_hom.mk f h0 h1 hmul) = f := rfl

@[simp, to_additive]
lemma monoid_hom.to_one_hom_coe [monoid M] [monoid N] (f : M →* N) :
  (f.to_one_hom : M → N) = f := rfl
@[simp, to_additive]
lemma monoid_hom.to_mul_hom_coe [monoid M] [monoid N] (f : M →* N) :
  (f.to_mul_hom : M → N) = f := rfl
@[simp]
lemma monoid_with_zero_hom.to_zero_hom_coe [monoid_with_zero M] [monoid_with_zero N]
  (f : monoid_with_zero_hom M N) :
  (f.to_zero_hom : M → N) = f := rfl
@[simp]
lemma monoid_with_zero_hom.to_monoid_hom_coe [monoid_with_zero M] [monoid_with_zero N]
  (f : monoid_with_zero_hom M N) :
  (f.to_monoid_hom : M → N) = f := rfl

@[to_additive]
theorem one_hom.congr_fun [has_one M] [has_one N]
  {f g : one_hom M N} (h : f = g) (x : M) : f x = g x :=
congr_arg (λ h : one_hom M N, h x) h
@[to_additive]
theorem mul_hom.congr_fun [has_mul M] [has_mul N]
  {f g : mul_hom M N} (h : f = g) (x : M) : f x = g x :=
congr_arg (λ h : mul_hom M N, h x) h
@[to_additive]
theorem monoid_hom.congr_fun [monoid M] [monoid N]
  {f g : M →* N} (h : f = g) (x : M) : f x = g x :=
congr_arg (λ h : M →* N, h x) h
theorem monoid_with_zero_hom.congr_fun [monoid_with_zero M] [monoid_with_zero N]
  {f g : monoid_with_zero_hom M N} (h : f = g) (x : M) : f x = g x :=
congr_arg (λ h : monoid_with_zero_hom M N, h x) h

@[to_additive]
theorem one_hom.congr_arg [has_one M] [has_one N]
  (f : one_hom M N) {x y : M} (h : x = y) : f x = f y :=
congr_arg (λ x : M, f x) h
@[to_additive]
theorem mul_hom.congr_arg [has_mul M] [has_mul N]
  (f : mul_hom M N) {x y : M} (h : x = y) : f x = f y :=
congr_arg (λ x : M, f x) h
@[to_additive]
theorem monoid_hom.congr_arg [monoid M] [monoid N]
  (f : M →* N) {x y : M} (h : x = y) : f x = f y :=
congr_arg (λ x : M, f x) h
theorem monoid_with_zero_hom.congr_arg [monoid_with_zero M] [monoid_with_zero N]
  (f : monoid_with_zero_hom M N) {x y : M} (h : x = y) : f x = f y :=
congr_arg (λ x : M, f x) h

@[to_additive]
lemma one_hom.coe_inj [has_one M] [has_one N] ⦃f g : one_hom M N⦄ (h : (f : M → N) = g) : f = g :=
by cases f; cases g; cases h; refl
@[to_additive]
lemma mul_hom.coe_inj [has_mul M] [has_mul N] ⦃f g : mul_hom M N⦄ (h : (f : M → N) = g) : f = g :=
by cases f; cases g; cases h; refl
@[to_additive]
lemma monoid_hom.coe_inj [monoid M] [monoid N] ⦃f g : M →* N⦄ (h : (f : M → N) = g) : f = g :=
by cases f; cases g; cases h; refl
lemma monoid_with_zero_hom.coe_inj [monoid_with_zero M] [monoid_with_zero N]
  ⦃f g : monoid_with_zero_hom M N⦄ (h : (f : M → N) = g) : f = g :=
by cases f; cases g; cases h; refl

@[ext, to_additive]
lemma one_hom.ext [has_one M] [has_one N] ⦃f g : one_hom M N⦄ (h : ∀ x, f x = g x) : f = g :=
one_hom.coe_inj (funext h)
@[ext, to_additive]
lemma mul_hom.ext [has_mul M] [has_mul N] ⦃f g : mul_hom M N⦄ (h : ∀ x, f x = g x) : f = g :=
mul_hom.coe_inj (funext h)
@[ext, to_additive]
lemma monoid_hom.ext [monoid M] [monoid N] ⦃f g : M →* N⦄ (h : ∀ x, f x = g x) : f = g :=
monoid_hom.coe_inj (funext h)
@[ext]
lemma monoid_with_zero_hom.ext [monoid_with_zero M] [monoid_with_zero N]
  ⦃f g : monoid_with_zero_hom M N⦄ (h : ∀ x, f x = g x) : f = g :=
monoid_with_zero_hom.coe_inj (funext h)

attribute [ext] zero_hom.ext add_hom.ext add_monoid_hom.ext

@[to_additive]
lemma one_hom.ext_iff [has_one M] [has_one N] {f g : one_hom M N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, one_hom.ext h⟩
@[to_additive]
lemma mul_hom.ext_iff [has_mul M] [has_mul N] {f g : mul_hom M N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, mul_hom.ext h⟩
@[to_additive]
lemma monoid_hom.ext_iff [monoid M] [monoid N] {f g : M →* N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, monoid_hom.ext h⟩
lemma monoid_with_zero_hom.ext_iff [monoid_with_zero M] [monoid_with_zero N]
  {f g : monoid_with_zero_hom M N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, monoid_with_zero_hom.ext h⟩

@[simp, to_additive]
lemma one_hom.mk_coe [has_one M] [has_one N]
  (f : one_hom M N) (h1) : one_hom.mk f h1 = f :=
one_hom.ext $ λ _, rfl
@[simp, to_additive]
lemma mul_hom.mk_coe [has_mul M] [has_mul N]
  (f : mul_hom M N) (hmul) : mul_hom.mk f hmul = f :=
mul_hom.ext $ λ _, rfl
@[simp, to_additive]
lemma monoid_hom.mk_coe [monoid M] [monoid N]
  (f : M →* N) (h1 hmul) : monoid_hom.mk f h1 hmul = f :=
monoid_hom.ext $ λ _, rfl
@[simp]
lemma monoid_with_zero_hom.mk_coe [monoid_with_zero M] [monoid_with_zero N]
  (f : monoid_with_zero_hom M N) (h0 h1 hmul) : monoid_with_zero_hom.mk f h0 h1 hmul = f :=
monoid_with_zero_hom.ext $ λ _, rfl

end coes

@[simp, to_additive]
lemma one_hom.map_one [has_one M] [has_one N] (f : one_hom M N) : f 1 = 1 := f.map_one'
/-- If `f` is a monoid homomorphism then `f 1 = 1`. -/
@[simp, to_additive]
lemma monoid_hom.map_one [monoid M] [monoid N] (f : M →* N) : f 1 = 1 := f.map_one'
@[simp]
lemma monoid_with_zero_hom.map_one [monoid_with_zero M] [monoid_with_zero N]
  (f : monoid_with_zero_hom M N) : f 1 = 1 := f.map_one'

/-- If `f` is an additive monoid homomorphism then `f 0 = 0`. -/
add_decl_doc add_monoid_hom.map_zero
@[simp]
lemma monoid_with_zero_hom.map_zero [monoid_with_zero M] [monoid_with_zero N]
  (f : monoid_with_zero_hom M N) : f 0 = 0 := f.map_zero'

@[simp, to_additive]
lemma mul_hom.map_mul [has_mul M] [has_mul N]
  (f : mul_hom M N) (a b : M) : f (a * b) = f a * f b := f.map_mul' a b
/-- If `f` is a monoid homomorphism then `f (a * b) = f a * f b`. -/
@[simp, to_additive]
lemma monoid_hom.map_mul [monoid M] [monoid N]
  (f : M →* N) (a b : M) : f (a * b) = f a * f b := f.map_mul' a b
@[simp]
lemma monoid_with_zero_hom.map_mul [monoid_with_zero M] [monoid_with_zero N]
  (f :  monoid_with_zero_hom M N) (a b : M) : f (a * b) = f a * f b := f.map_mul' a b

/-- If `f` is an additive monoid homomorphism then `f (a + b) = f a + f b`. -/
add_decl_doc add_monoid_hom.map_add

namespace monoid_hom
variables {mM : monoid M} {mN : monoid N} {mP : monoid P}
variables [group G] [comm_group H]

include mM mN

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

end monoid_hom

/-- The identity map from a type with 1 to itself. -/
@[to_additive]
def one_hom.id (M : Type*) [has_one M] : one_hom M M :=
{ to_fun := id, map_one' := rfl, }
/-- The identity map from a type with multiplication to itself. -/
@[to_additive]
def mul_hom.id (M : Type*) [has_mul M] : mul_hom M M :=
{ to_fun := id, map_mul' := λ _ _, rfl, }
/-- The identity map from a monoid to itself. -/
@[to_additive]
def monoid_hom.id (M : Type*) [monoid M] : M →* M :=
{ to_fun := id, map_one' := rfl, map_mul' := λ _ _, rfl, }
/-- The identity map from a monoid_with_zero to itself. -/
def monoid_with_zero_hom.id (M : Type*) [monoid_with_zero M] : monoid_with_zero_hom M M :=
{ to_fun := id, map_zero' := rfl, map_one' := rfl, map_mul' := λ _ _, rfl, }

/-- The identity map from an type with zero to itself. -/
add_decl_doc zero_hom.id
/-- The identity map from an type with addition to itself. -/
add_decl_doc add_hom.id
/-- The identity map from an additive monoid to itself. -/
add_decl_doc add_monoid_hom.id

@[simp, to_additive] lemma one_hom.coe_id {M : Type*} [has_one M] :
  (one_hom.id M : M → M) = id := rfl
@[simp, to_additive] lemma mul_hom.coe_id {M : Type*} [has_mul M] :
  (mul_hom.id M : M → M) = id := rfl
@[simp, to_additive] lemma monoid_hom.coe_id {M : Type*} [monoid M] :
  (monoid_hom.id M : M → M) = id := rfl
@[simp] lemma monoid_with_zero_hom.coe_id {M : Type*} [monoid_with_zero M] :
  (monoid_with_zero_hom.id M : M → M) = id := rfl

@[simp, to_additive] lemma one_hom.id_apply {M : Type*} [has_one M] (x : M) :
  one_hom.id M x = x := rfl
@[simp, to_additive] lemma mul_hom.id_apply {M : Type*} [has_mul M] (x : M) :
  mul_hom.id M x = x := rfl
@[simp, to_additive] lemma monoid_hom.id_apply {M : Type*} [monoid M] (x : M) :
  monoid_hom.id M x = x := rfl
@[simp] lemma monoid_with_zero_hom.id_apply {M : Type*} [monoid_with_zero M] (x : M) :
  monoid_with_zero_hom.id M x = x := rfl

/-- Composition of `one_hom`s as a `one_hom`. -/
@[to_additive]
def one_hom.comp [has_one M] [has_one N] [has_one P]
  (hnp : one_hom N P) (hmn : one_hom M N) : one_hom M P :=
{ to_fun := hnp ∘ hmn, map_one' := by simp, }
/-- Composition of `mul_hom`s as a `mul_hom`. -/
@[to_additive]
def mul_hom.comp [has_mul M] [has_mul N] [has_mul P]
  (hnp : mul_hom N P) (hmn : mul_hom M N) : mul_hom M P :=
{ to_fun := hnp ∘ hmn, map_mul' := by simp, }
/-- Composition of monoid morphisms as a monoid morphism. -/
@[to_additive]
def monoid_hom.comp [monoid M] [monoid N] [monoid P] (hnp : N →* P) (hmn : M →* N) : M →* P :=
{ to_fun := hnp ∘ hmn, map_one' := by simp, map_mul' := by simp, }
/-- Composition of `monoid_with_zero_hom`s as a `monoid_with_zero_hom`. -/
def monoid_with_zero_hom.comp [monoid_with_zero M] [monoid_with_zero N] [monoid_with_zero P]
  (hnp : monoid_with_zero_hom N P) (hmn : monoid_with_zero_hom M N) : monoid_with_zero_hom M P :=
{ to_fun := hnp ∘ hmn, map_zero' := by simp, map_one' := by simp, map_mul' := by simp, }

/-- Composition of `zero_hom`s as a `zero_hom`. -/
add_decl_doc zero_hom.comp
/-- Composition of `add_hom`s as a `add_hom`. -/
add_decl_doc add_hom.comp
/-- Composition of additive monoid morphisms as an additive monoid morphism. -/
add_decl_doc add_monoid_hom.comp

@[simp, to_additive] lemma one_hom.coe_comp [has_one M] [has_one N] [has_one P]
  (g : one_hom N P) (f : one_hom M N) :
  ⇑(g.comp f) = g ∘ f := rfl
@[simp, to_additive] lemma mul_hom.coe_comp [has_mul M] [has_mul N] [has_mul P]
  (g : mul_hom N P) (f : mul_hom M N) :
  ⇑(g.comp f) = g ∘ f := rfl
@[simp, to_additive] lemma monoid_hom.coe_comp [monoid M] [monoid N] [monoid P]
  (g : N →* P) (f : M →* N) :
  ⇑(g.comp f) = g ∘ f := rfl
@[simp] lemma monoid_with_zero_hom.coe_comp [monoid_with_zero M] [monoid_with_zero N]
  [monoid_with_zero P]
  (g : monoid_with_zero_hom N P) (f : monoid_with_zero_hom M N) :
  ⇑(g.comp f) = g ∘ f := rfl

@[to_additive] lemma one_hom.comp_apply [has_one M] [has_one N] [has_one P]
  (g : one_hom N P) (f : one_hom M N) (x : M) :
  g.comp f x = g (f x) := rfl
@[to_additive] lemma mul_hom.comp_apply [has_mul M] [has_mul N] [has_mul P]
  (g : mul_hom N P) (f : mul_hom M N) (x : M) :
  g.comp f x = g (f x) := rfl
@[to_additive] lemma monoid_hom.comp_apply [monoid M] [monoid N] [monoid P]
  (g : N →* P) (f : M →* N) (x : M) :
  g.comp f x = g (f x) := rfl
lemma monoid_with_zero_hom.comp_apply [monoid_with_zero M] [monoid_with_zero N] [monoid_with_zero P]
  (g : monoid_with_zero_hom N P) (f : monoid_with_zero_hom M N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of monoid homomorphisms is associative. -/
@[to_additive] lemma one_hom.comp_assoc {Q : Type*} [has_one M] [has_one N] [has_one P] [has_one Q]
  (f : one_hom M N) (g : one_hom N P) (h : one_hom P Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl
@[to_additive] lemma mul_hom.comp_assoc {Q : Type*} [has_mul M] [has_mul N] [has_mul P] [has_mul Q]
  (f : mul_hom M N) (g : mul_hom N P) (h : mul_hom P Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl
@[to_additive] lemma monoid_hom.comp_assoc {Q : Type*} [monoid M] [monoid N] [monoid P] [monoid Q]
  (f : M →* N) (g : N →* P) (h : P →* Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl
lemma monoid_with_zero_hom.comp_assoc {Q : Type*}
  [monoid_with_zero M] [monoid_with_zero N] [monoid_with_zero P] [monoid_with_zero Q]
  (f : monoid_with_zero_hom M N) (g : monoid_with_zero_hom N P) (h : monoid_with_zero_hom P Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

@[to_additive]
lemma one_hom.cancel_right [has_one M] [has_one N] [has_one P]
  {g₁ g₂ : one_hom N P} {f : one_hom M N} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, one_hom.ext $ (forall_iff_forall_surj hf).1 (one_hom.ext_iff.1 h), λ h, h ▸ rfl⟩
@[to_additive]
lemma mul_hom.cancel_right [has_mul M] [has_mul N] [has_mul P]
  {g₁ g₂ : mul_hom N P} {f : mul_hom M N} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, mul_hom.ext $ (forall_iff_forall_surj hf).1 (mul_hom.ext_iff.1 h), λ h, h ▸ rfl⟩
@[to_additive]
lemma monoid_hom.cancel_right [monoid M] [monoid N] [monoid P]
  {g₁ g₂ : N →* P} {f : M →* N} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, monoid_hom.ext $ (forall_iff_forall_surj hf).1 (monoid_hom.ext_iff.1 h), λ h, h ▸ rfl⟩
lemma monoid_with_zero_hom.cancel_right
  [monoid_with_zero M] [monoid_with_zero N] [monoid_with_zero P]
  {g₁ g₂ : monoid_with_zero_hom N P} {f : monoid_with_zero_hom M N} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, monoid_with_zero_hom.ext $ (forall_iff_forall_surj hf).1 (monoid_with_zero_hom.ext_iff.1 h),
 λ h, h ▸ rfl⟩

@[to_additive]
lemma one_hom.cancel_left [has_one M] [has_one N] [has_one P]
  {g : one_hom N P} {f₁ f₂ : one_hom M N} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, one_hom.ext $ λ x, hg $ by rw [← one_hom.comp_apply, h, one_hom.comp_apply],
 λ h, h ▸ rfl⟩
@[to_additive]
lemma mul_hom.cancel_left [has_one M] [has_one N] [has_one P]
  {g : one_hom N P} {f₁ f₂ : one_hom M N} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, one_hom.ext $ λ x, hg $ by rw [← one_hom.comp_apply, h, one_hom.comp_apply],
 λ h, h ▸ rfl⟩
@[to_additive]
lemma monoid_hom.cancel_left [monoid M] [monoid N] [monoid P]
  {g : N →* P} {f₁ f₂ : M →* N} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, monoid_hom.ext $ λ x, hg $ by rw [← monoid_hom.comp_apply, h, monoid_hom.comp_apply],
 λ h, h ▸ rfl⟩
lemma monoid_with_zero_hom.cancel_left
  [monoid_with_zero M] [monoid_with_zero N] [monoid_with_zero P]
  {g : monoid_with_zero_hom N P} {f₁ f₂ : monoid_with_zero_hom M N} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, monoid_with_zero_hom.ext $ λ x, hg $ by rw [
        ← monoid_with_zero_hom.comp_apply, h, monoid_with_zero_hom.comp_apply],
 λ h, h ▸ rfl⟩

@[simp, to_additive] lemma one_hom.comp_id [has_one M] [has_one N]
  (f : one_hom M N) : f.comp (one_hom.id M) = f := one_hom.ext $ λ x, rfl
@[simp, to_additive] lemma mul_hom.comp_id [has_mul M] [has_mul N]
  (f : mul_hom M N) : f.comp (mul_hom.id M) = f := mul_hom.ext $ λ x, rfl
@[simp, to_additive] lemma monoid_hom.comp_id [monoid M] [monoid N]
  (f : M →* N) : f.comp (monoid_hom.id M) = f := monoid_hom.ext $ λ x, rfl
@[simp] lemma monoid_with_zero_hom.comp_id [monoid_with_zero M] [monoid_with_zero N]
  (f : monoid_with_zero_hom M N) : f.comp (monoid_with_zero_hom.id M) = f :=
monoid_with_zero_hom.ext $ λ x, rfl

@[simp, to_additive] lemma one_hom.id_comp [has_one M] [has_one N]
  (f : one_hom M N) : (one_hom.id N).comp f = f := one_hom.ext $ λ x, rfl
@[simp, to_additive] lemma mul_hom.id_comp [has_mul M] [has_mul N]
  (f : mul_hom M N) : (mul_hom.id N).comp f = f := mul_hom.ext $ λ x, rfl
@[simp, to_additive] lemma monoid_hom.id_comp [monoid M] [monoid N]
  (f : M →* N) : (monoid_hom.id N).comp f = f := monoid_hom.ext $ λ x, rfl
@[simp] lemma monoid_with_zero_hom.id_comp [monoid_with_zero M] [monoid_with_zero N]
  (f : monoid_with_zero_hom M N) : (monoid_with_zero_hom.id N).comp f = f :=
monoid_with_zero_hom.ext $ λ x, rfl

section End

namespace monoid

variables (M) [monoid M]

/-- The monoid of endomorphisms. -/
protected def End := M →* M

namespace End

instance : monoid (monoid.End M) :=
{ mul := monoid_hom.comp,
  one := monoid_hom.id M,
  mul_assoc := λ _ _ _, monoid_hom.comp_assoc _ _ _,
  mul_one := monoid_hom.comp_id,
  one_mul := monoid_hom.id_comp }

instance : inhabited (monoid.End M) := ⟨1⟩

instance : has_coe_to_fun (monoid.End M) := ⟨_, monoid_hom.to_fun⟩

end End

@[simp] lemma coe_one : ((1 : monoid.End M) : M → M) = id := rfl
@[simp] lemma coe_mul (f g) : ((f * g : monoid.End M) : M → M) = f ∘ g := rfl

end monoid

namespace add_monoid

variables (A : Type*) [add_monoid A]

/-- The monoid of endomorphisms. -/
protected def End := A →+ A

namespace End

instance : monoid (add_monoid.End A) :=
{ mul := add_monoid_hom.comp,
  one := add_monoid_hom.id A,
  mul_assoc := λ _ _ _, add_monoid_hom.comp_assoc _ _ _,
  mul_one := add_monoid_hom.comp_id,
  one_mul := add_monoid_hom.id_comp }

instance : inhabited (add_monoid.End A) := ⟨1⟩

instance : has_coe_to_fun (add_monoid.End A) := ⟨_, add_monoid_hom.to_fun⟩

end End

@[simp] lemma coe_one : ((1 : add_monoid.End A) : A → A) = id := rfl
@[simp] lemma coe_mul (f g) : ((f * g : add_monoid.End A) : A → A) = f ∘ g := rfl

end add_monoid

end End

/-- `1` is the homomorphism sending all elements to `1`. -/
@[to_additive]
instance [has_one M] [has_one N] : has_one (one_hom M N) := ⟨⟨λ _, 1, rfl⟩⟩
/-- `1` is the multiplicative homomorphism sending all elements to `1`. -/
@[to_additive]
instance [has_mul M] [monoid N] : has_one (mul_hom M N) := ⟨⟨λ _, 1, λ _ _, (one_mul 1).symm⟩⟩
/-- `1` is the monoid homomorphism sending all elements to `1`. -/
@[to_additive]
instance [monoid M] [monoid N] : has_one (M →* N) := ⟨⟨λ _, 1, rfl, λ _ _, (one_mul 1).symm⟩⟩

/-- `0` is the homomorphism sending all elements to `0`. -/
add_decl_doc zero_hom.has_zero
/-- `0` is the additive homomorphism sending all elements to `0`. -/
add_decl_doc add_hom.has_zero
/-- `0` is the additive monoid homomorphism sending all elements to `0`. -/
add_decl_doc add_monoid_hom.has_zero

@[simp, to_additive] lemma one_hom.one_apply [has_one M] [has_one N]
  (x : M) : (1 : one_hom M N) x = 1 := rfl
@[simp, to_additive] lemma monoid_hom.one_apply [monoid M] [monoid N]
  (x : M) : (1 : M →* N) x = 1 := rfl

@[simp, to_additive] lemma one_hom.one_comp [has_one M] [has_one N] [has_one P] (f : one_hom M N) :
  (1 : one_hom N P).comp f = 1 := rfl
@[simp, to_additive] lemma one_hom.comp_one [has_one M] [has_one N] [has_one P] (f : one_hom N P) :
  f.comp (1 : one_hom M N) = 1 :=
by { ext, simp only [one_hom.map_one, one_hom.coe_comp, function.comp_app, one_hom.one_apply] }

@[to_additive]
instance [has_one M] [has_one N] : inhabited (one_hom M N) := ⟨1⟩
@[to_additive]
instance [has_mul M] [monoid N] : inhabited (mul_hom M N) := ⟨1⟩
@[to_additive]
instance [monoid M] [monoid N] : inhabited (M →* N) := ⟨1⟩
-- unlike the other homs, `monoid_with_zero_hom` does not have a `1` or `0`
instance [monoid_with_zero M] : inhabited (monoid_with_zero_hom M M) := ⟨monoid_with_zero_hom.id M⟩

namespace monoid_hom
variables [mM : monoid M] [mN : monoid N] [mP : monoid P]
variables [group G] [comm_group H]

/-- Given two monoid morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid morphism
sending `x` to `f x * g x`. -/
@[to_additive]
instance {M N} {mM : monoid M} [comm_monoid N] : has_mul (M →* N) :=
⟨λ f g,
  { to_fun := λ m, f m * g m,
    map_one' := show f 1 * g 1 = 1, by simp,
    map_mul' := begin intros, show f (x * y) * g (x * y) = f x * g x * (f y * g y),
      rw [f.map_mul, g.map_mul, ←mul_assoc, ←mul_assoc, mul_right_comm (f x)], end }⟩

/-- Given two additive monoid morphisms `f`, `g` to an additive commutative monoid, `f + g` is the
additive monoid morphism sending `x` to `f x + g x`. -/
add_decl_doc add_monoid_hom.has_add

@[simp, to_additive] lemma mul_apply {M N} {mM : monoid M} {mN : comm_monoid N}
  (f g : M →* N) (x : M) :
  (f * g) x = f x * g x := rfl

@[simp, to_additive] lemma one_comp [monoid M] [monoid N] [monoid P] (f : M →* N) :
  (1 : N →* P).comp f = 1 := rfl
@[simp, to_additive] lemma comp_one [monoid M] [monoid N] [monoid P] (f : N →* P) :
  f.comp (1 : M →* N) = 1 :=
by { ext, simp only [map_one, coe_comp, function.comp_app, one_apply] }

@[to_additive] lemma mul_comp [monoid M] [comm_monoid N] [comm_monoid P]
  (g₁ g₂ : N →* P) (f : M →* N) :
  (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl
@[to_additive] lemma comp_mul [monoid M] [comm_monoid N] [comm_monoid P]
  (g : N →* P) (f₁ f₂ : M →* N) :
  g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
by { ext, simp only [mul_apply, function.comp_app, map_mul, coe_comp] }

/-- (M →* N) is a comm_monoid if N is commutative. -/
@[to_additive]
instance {M N} [monoid M] [comm_monoid N] : comm_monoid (M →* N) :=
{ mul := (*),
  mul_assoc := by intros; ext; apply mul_assoc,
  one := 1,
  one_mul := by intros; ext; apply one_mul,
  mul_one := by intros; ext; apply mul_one,
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

/-- Evaluation of a `monoid_hom` at a point as a monoid homomorphism. See also `monoid_hom.apply`
for the evaluation of any function at a point. -/
@[to_additive "Evaluation of an `add_monoid_hom` at a point as an additive monoid homomorphism.
See also `add_monoid_hom.apply` for the evaluation of any function at a point."]
def eval [monoid M] [comm_monoid N] : M →* (M →* N) →* N := (monoid_hom.id (M →* N)).flip

@[simp, to_additive]
lemma eval_apply [monoid M] [comm_monoid N] (x : M) (f : M →* N) : eval x f = f x := rfl

/-- Composition of monoid morphisms (`monoid_hom.comp`) as a monoid morphism. -/
@[to_additive "Composition of additive monoid morphisms
(`add_monoid_hom.comp`) as an additive monoid morphism.", simps]
def comp_hom [monoid M] [comm_monoid N] [comm_monoid P] :
  (N →* P) →* (M →* N) →* (M →* P) :=
{ to_fun := λ g, { to_fun := g.comp, map_one' := comp_one g, map_mul' := comp_mul g },
  map_one' := by { ext1 f, exact one_comp f },
  map_mul' := λ g₁ g₂, by { ext1 f, exact mul_comp g₁ g₂ f } }

/-- If two homomorphism from a group to a monoid are equal at `x`, then they are equal at `x⁻¹`. -/
@[to_additive "If two homomorphism from an additive group to an additive monoid are equal at `x`,
then they are equal at `-x`." ]
lemma eq_on_inv {G} [group G] [monoid M] {f g : G →* M} {x : G} (h : f x = g x) :
  f x⁻¹ = g x⁻¹ :=
left_inv_eq_right_inv (f.map_mul_eq_one $ inv_mul_self x) $
  h.symm ▸ g.map_mul_eq_one $ mul_inv_self x

/-- Group homomorphisms preserve inverse. -/
@[simp, to_additive]
theorem map_inv {G H} [group G] [group H] (f : G →* H) (g : G) : f g⁻¹ = (f g)⁻¹ :=
eq_inv_of_mul_eq_one $ f.map_mul_eq_one $ inv_mul_self g

/-- Group homomorphisms preserve division. -/
@[simp, to_additive]
theorem map_mul_inv {G H} [group G] [group H] (f : G →* H) (g h : G) :
  f (g * h⁻¹) = (f g) * (f h)⁻¹ := by rw [f.map_mul, f.map_inv]

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial. -/
@[to_additive]
lemma injective_iff {G H} [group G] [monoid H] (f : G →* H) :
  function.injective f ↔ (∀ a, f a = 1 → a = 1) :=
⟨λ h x hfx, h $ hfx.trans f.map_one.symm,
 λ h x y hxy, mul_inv_eq_one.1 $ h _ $ by rw [f.map_mul, hxy, ← f.map_mul, mul_inv_self, f.map_one]⟩

include mM
/-- Makes a group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive "Makes an additive group homomorphism from a proof that the map preserves addition."]
def mk' (f : M → G) (map_mul : ∀ a b : M, f (a * b) = f a * f b) : M →* G :=
{ to_fun := f,
  map_mul' := map_mul,
  map_one' := mul_left_eq_self.1 $ by rw [←map_mul, mul_one] }

@[simp, to_additive]
lemma coe_mk' {f : M → G} (map_mul : ∀ a b : M, f (a * b) = f a * f b) :
  ⇑(mk' f map_mul) = f := rfl

omit mM

/-- Makes a group homomorphism from a proof that the map preserves right division `λ x y, x * y⁻¹`.
-/
@[to_additive "Makes an additive group homomorphism from a proof that the map preserves
the operation `λ a b, a + -b`. See also `add_monoid_hom.of_map_sub` for a version using
`λ a b, a - b`."]
def of_map_mul_inv {H : Type*} [group H] (f : G → H)
  (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) :
  G →* H :=
mk' f $ λ x y,
calc f (x * y) = f x * (f $ 1 * 1⁻¹ * y⁻¹)⁻¹ : by simp only [one_mul, one_inv, ← map_div, inv_inv]
... = f x * f y : by { simp only [map_div], simp only [mul_right_inv, one_mul, inv_inv] }

@[simp, to_additive] lemma coe_of_map_mul_inv {H : Type*} [group H] (f : G → H)
  (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) :
  ⇑(of_map_mul_inv f map_div) = f :=
rfl

/-- If `f` is a monoid homomorphism to a commutative group, then `f⁻¹` is the homomorphism sending
`x` to `(f x)⁻¹`. -/
@[to_additive]
instance {M G} [monoid M] [comm_group G] : has_inv (M →* G) :=
⟨λ f, mk' (λ g, (f g)⁻¹) $ λ a b, by rw [←mul_inv, f.map_mul]⟩

/-- If `f` is an additive monoid homomorphism to an additive commutative group, then `-f` is the
homomorphism sending `x` to `-(f x)`. -/
add_decl_doc add_monoid_hom.has_neg

@[simp, to_additive] lemma inv_apply {M G} {mM : monoid M} {gG : comm_group G}
  (f : M →* G) (x : M) :
  f⁻¹ x = (f x)⁻¹ := rfl

@[simp, to_additive] lemma inv_comp {M N A} {mM : monoid M} {gN : monoid N}
  {gA : comm_group A} (φ : N →* A) (ψ : M →* N) : φ⁻¹.comp ψ = (φ.comp ψ)⁻¹ :=
by { ext, simp only [function.comp_app, inv_apply, coe_comp] }

@[simp, to_additive] lemma comp_inv {M A B} {mM : monoid M} {mA : comm_group A}
  {mB : comm_group B} (φ : A →* B) (ψ : M →* A) : φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹ :=
by { ext, simp only [function.comp_app, inv_apply, map_inv, coe_comp] }

/-- If `f` and `g` are monoid homomorphisms to a commutative group, then `f / g` is the homomorphism
sending `x` to `(f x) / (g x)`. -/
@[to_additive]
instance {M G} [monoid M] [comm_group G] : has_div (M →* G) :=
⟨λ f g, mk' (λ x, f x / g x) $ λ a b,
  by simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]⟩

/-- If `f` and `g` are monoid homomorphisms to an additive commutative group, then `f - g`
is the homomorphism sending `x` to `(f x) - (g x)`. -/
add_decl_doc add_monoid_hom.has_sub

@[simp, to_additive] lemma div_apply {M G} {mM : monoid M} {gG : comm_group G}
  (f g : M →* G) (x : M) :
  (f / g) x = f x / g x := rfl

/-- If `G` is a commutative group, then `M →* G` a commutative group too. -/
@[to_additive]
instance {M G} [monoid M] [comm_group G] : comm_group (M →* G) :=
{ inv := has_inv.inv,
  div := has_div.div,
  div_eq_mul_inv := by { intros, ext, apply div_eq_mul_inv },
  mul_left_inv := by intros; ext; apply mul_left_inv,
  ..monoid_hom.comm_monoid }

/-- If `G` is an additive commutative group, then `M →+ G` an additive commutative group too. -/
add_decl_doc add_monoid_hom.add_comm_group

end monoid_hom

namespace add_monoid_hom

variables {A B : Type*} [add_monoid A] [add_comm_group B] [add_group G] [add_group H]

/-- Additive group homomorphisms preserve subtraction. -/
@[simp] theorem map_sub (f : G →+ H) (g h : G) : f (g - h) = (f g) - (f h) :=
by rw [sub_eq_add_neg, sub_eq_add_neg, f.map_add_neg g h]

/-- Define a morphism of additive groups given a map which respects difference. -/
def of_map_sub (f : G → H) (hf : ∀ x y, f (x - y) = f x - f y) : G →+ H :=
of_map_add_neg f (by simpa only [sub_eq_add_neg] using hf)

@[simp] lemma coe_of_map_sub (f : G → H) (hf : ∀ x y, f (x - y) = f x - f y) :
  ⇑(of_map_sub f hf) = f :=
rfl

end add_monoid_hom

section commute

variables [monoid M] [monoid N] {a x y : M}

@[simp, to_additive]
protected lemma semiconj_by.map (h : semiconj_by a x y) (f : M →* N) :
  semiconj_by (f a) (f x) (f y) :=
by simpa only [semiconj_by, f.map_mul] using congr_arg f h

@[simp, to_additive]
protected lemma commute.map (h : commute x y) (f : M →* N) : commute (f x) (f y) := h.map f

end commute
