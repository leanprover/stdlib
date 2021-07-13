/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import algebra.group.defs
import algebra.group.hom
import logic.embedding

/-!
# Definitions of group actions

This file defines a hierarchy of group action type-classes:

* `has_scalar M α` and its additive version `has_vadd G P` are notation typeclasses for
  `•` and `+ᵥ`, respectively;
* `mul_action M α` and its additive version `add_action G P` are typeclasses used for
  actions of multiplicative and additive monoids and groups;
* `distrib_mul_action M A` is a typeclass for an action of a multiplicative monoid on
  an additive monoid such that `a • (b + c) = a • b + a • c` and `a • 0 = 0`.

The hierarchy is extended further by `module`, defined elsewhere.

Also provided are type-classes regarding the interaction of different group actions,

* `smul_comm_class M N α` and its additive version `vadd_comm_class M N α`;
* `is_scalar_tower M N α` (no additive version).

## Notation

- `a • b` is used as notation for `has_scalar.smul a b`.
- `a +ᵥ b` is used as notation for `has_vadd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `group_theory`, to avoid import cycles.
More sophisticated lemmas belong in `group_theory.group_action`.

## Tags

group action
-/

variables {M N G A B α β γ : Type*}

open function

/-- Type class for the `+ᵥ` notation. -/
class has_vadd (G : Type*) (P : Type*) := (vadd : G → P → P)

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
@[to_additive has_vadd]
class has_scalar (M : Type*) (α : Type*) := (smul : M → α → α)

infix ` +ᵥ `:65 := has_vadd.vadd
infixr ` • `:73 := has_scalar.smul

/-- See also `monoid.to_mul_action` and `mul_zero_class.to_smul_with_zero`. -/
@[priority 910, to_additive] -- see Note [lower instance priority]
instance has_mul.to_has_scalar (α : Type*) [has_mul α] : has_scalar α α := ⟨(*)⟩

@[simp, to_additive] lemma smul_eq_mul (α : Type*) [has_mul α] {a a' : α} : a • a' = a * a' := rfl

/-- Type class for additive monoid actions. -/
@[protect_proj] class add_action (G : Type*) (P : Type*) [add_monoid G] extends has_vadd G P :=
(zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p)
(add_vadd : ∀ (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p))

/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
@[protect_proj, to_additive]
class mul_action (α : Type*) (β : Type*) [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)

/-- A typeclass mixin saying that two additive actions on the same space commute. -/
class vadd_comm_class (M N α : Type*) [has_vadd M α] [has_vadd N α] : Prop :=
(vadd_comm : ∀ (m : M) (n : N) (a : α), m +ᵥ (n +ᵥ a) = n +ᵥ (m +ᵥ a))

/-- A typeclass mixin saying that two multiplicative actions on the same space commute. -/
@[to_additive] class smul_comm_class (M N α : Type*) [has_scalar M α] [has_scalar N α] : Prop :=
(smul_comm : ∀ (m : M) (n : N) (a : α), m • n • a = n • m • a)

export mul_action (mul_smul) add_action (add_vadd) smul_comm_class (smul_comm)
  vadd_comm_class (vadd_comm)

attribute [to_additive_reorder 1] has_pow
attribute [to_additive_reorder 1 4] has_pow.pow
attribute [to_additive has_scalar] has_pow
attribute [to_additive has_scalar.smul] has_pow.pow

/--
Frequently, we find ourselves wanting to express a bilinear map `M →ₗ[R] N →ₗ[R] P` or an
equivalence between maps `(M →ₗ[R] N) ≃ₗ[R] (M' →ₗ[R] N')` where the maps have an associated ring
`R`. Unfortunately, using definitions like these requires that `R` satisfy `comm_semiring R`, and
not just `semiring R`. Using `M →ₗ[R] N →+ P` and `(M →ₗ[R] N) ≃+ (M' →ₗ[R] N')` avoids this
problem, but throws away structure that is useful for when we _do_ have a commutative (semi)ring.

To avoid making this compromise, we instead state these definitions as `M →ₗ[R] N →ₗ[S] P` or
`(M →ₗ[R] N) ≃ₗ[S] (M' →ₗ[R] N')` and require `smul_comm_class S R` on the appropriate modules. When
the caller has `comm_semiring R`, they can set `S = R` and `smul_comm_class_self` will populate the
instance. If the caller only has `semiring R` they can still set either `R = ℕ` or `S = ℕ`, and
`add_comm_monoid.nat_smul_comm_class` or `add_comm_monoid.nat_smul_comm_class'` will populate
the typeclass, which is still sufficient to recover a `≃+` or `→+` structure.

An example of where this is used is `linear_map.prod_equiv`.
-/
library_note "bundled maps over different rings"

/-- Commutativity of actions is a symmetric relation. This lemma can't be an instance because this
would cause a loop in the instance search graph. -/
@[to_additive] lemma smul_comm_class.symm (M N α : Type*) [has_scalar M α] [has_scalar N α]
  [smul_comm_class M N α] : smul_comm_class N M α :=
⟨λ a' a b, (smul_comm a a' b).symm⟩

/-- Commutativity of additive actions is a symmetric relation. This lemma can't be an instance
because this would cause a loop in the instance search graph. -/
add_decl_doc vadd_comm_class.symm

@[to_additive] instance smul_comm_class_self (M α : Type*) [comm_monoid M] [mul_action M α] :
  smul_comm_class M M α :=
⟨λ a a' b, by rw [← mul_smul, mul_comm, mul_smul]⟩

/-- An instance of `is_scalar_tower M N α` states that the multiplicative
action of `M` on `α` is determined by the multiplicative actions of `M` on `N`
and `N` on `α`. -/
class is_scalar_tower (M N α : Type*) [has_scalar M N] [has_scalar N α] [has_scalar M α] : Prop :=
(smul_assoc : ∀ (x : M) (y : N) (z : α), (x • y) • z = x • (y • z))

@[simp] lemma smul_assoc {M N} [has_scalar M N] [has_scalar N α] [has_scalar M α]
  [is_scalar_tower M N α] (x : M) (y : N) (z : α) :
  (x • y) • z = x • y • z :=
is_scalar_tower.smul_assoc x y z

section
variables [monoid M] [mul_action M α]

@[to_additive] lemma smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b :=
(mul_smul _ _ _).symm

variable (M)
@[simp, to_additive] theorem one_smul (b : α) : (1 : M) • b = b := mul_action.one_smul _

variables {M}

/-- Pullback a multiplicative action along an injective map respecting `•`.
See note [reducible non-instances]. -/
@[reducible, to_additive "Pullback an additive action along an injective map respecting `+ᵥ`."]
protected def function.injective.mul_action [has_scalar M β] (f : β → α)
  (hf : injective f) (smul : ∀ (c : M) x, f (c • x) = c • f x) :
  mul_action M β :=
{ smul := (•),
  one_smul := λ x, hf $ (smul _ _).trans $ one_smul _ (f x),
  mul_smul := λ c₁ c₂ x, hf $ by simp only [smul, mul_smul] }

/-- Pushforward a multiplicative action along a surjective map respecting `•`.
See note [reducible non-instances]. -/
@[reducible, to_additive "Pushforward an additive action along a surjective map respecting `+ᵥ`."]
protected def function.surjective.mul_action [has_scalar M β] (f : α → β) (hf : surjective f)
  (smul : ∀ (c : M) x, f (c • x) = c • f x) :
  mul_action M β :=
{ smul := (•),
  one_smul := λ y, by { rcases hf y with ⟨x, rfl⟩, rw [← smul, one_smul] },
  mul_smul := λ c₁ c₂ y, by { rcases hf y with ⟨x, rfl⟩, simp only [← smul, mul_smul] } }

section ite

variables (p : Prop) [decidable p]

@[to_additive] lemma ite_smul (a₁ a₂ : M) (b : α) : (ite p a₁ a₂) • b = ite p (a₁ • b) (a₂ • b) :=
by split_ifs; refl

@[to_additive] lemma smul_ite (a : M) (b₁ b₂ : α) : a • (ite p b₁ b₂) = ite p (a • b₁) (a • b₂) :=
by split_ifs; refl

end ite

section

variables (M)

/-- The regular action of a monoid on itself by left multiplication.

This is promoted to a module by `semiring.to_module`. -/
@[priority 910, to_additive] -- see Note [lower instance priority]
instance monoid.to_mul_action : mul_action M M :=
{ smul := (*),
  one_smul := one_mul,
  mul_smul := mul_assoc }

/-- The regular action of a monoid on itself by left addition.

This is promoted to an `add_torsor` by `add_group_is_add_torsor`. -/
add_decl_doc add_monoid.to_add_action

instance is_scalar_tower.left : is_scalar_tower M M α :=
⟨λ x y z, mul_smul x y z⟩

variables {M}

/-- Note that the `smul_comm_class M α α` typeclass argument is usually satisfied by `algebra M α`.
-/
@[to_additive]
lemma mul_smul_comm [has_mul α] (s : M) (x y : α) [smul_comm_class M α α] :
  x * (s • y) = s • (x * y) :=
(smul_comm s x y).symm

/-- Note that the `is_scalar_tower M α α` typeclass argument is usually satisfied by `algebra M α`.
-/
lemma smul_mul_assoc [has_mul α] (r : M) (x y : α) [is_scalar_tower M α α] :
  (r • x) * y = r • (x * y) :=
smul_assoc r x y

/-- Note that the `is_scalar_tower M α α` and `smul_comm_class M α α` typeclass arguments are
usually satisfied by `algebra M α`. -/
lemma smul_mul_smul [has_mul α] (r s : M) (x y : α)
  [is_scalar_tower M α α] [smul_comm_class M α α] :
  (r • x) * (s • y) = (r * s) • (x * y) :=
by rw [smul_mul_assoc, mul_smul_comm, ← smul_assoc, smul_eq_mul]

end

variable (α)

/-- The monoid of endomorphisms.

Note that this is generalized by `category_theory.End` to categories other than `Type u`. -/
def function.End  := α → α

instance : monoid (function.End α) :=
{ one := id,
  mul := (∘),
  mul_assoc := λ f g h, rfl,
  mul_one := λ f, rfl,
  one_mul := λ f, rfl, }

instance : inhabited (function.End α) := ⟨1⟩

variable {α}

namespace mul_action

variables (M α)

/-- Embedding of `α` into functions `M → α` induced by a multiplicative action of `M` on `α`. -/
@[to_additive] def to_fun : α ↪ (M → α) :=
⟨λ y x, x • y, λ y₁ y₂ H, one_smul M y₁ ▸ one_smul M y₂ ▸ by convert congr_fun H 1⟩

/-- Embedding of `α` into functions `M → α` induced by an additive action of `M` on `α`. -/
add_decl_doc add_action.to_fun

variables {M α}

@[simp, to_additive] lemma to_fun_apply (x : M) (y : α) : mul_action.to_fun M α y x = x • y :=
rfl

variable (α)

/-- A multiplicative action of `M` on `α` and a monoid homomorphism `N → M` induce
a multiplicative action of `N` on `α`. -/
@[to_additive] def comp_hom [monoid N] (g : N →* M) :
  mul_action N α :=
{ smul := λ x b, (g x) • b,
  one_smul := by simp [g.map_one, mul_action.one_smul],
  mul_smul := by simp [g.map_mul, mul_action.mul_smul] }

/-- An additive action of `M` on `α` and an additive monoid homomorphism `N → M` induce
an additive action of `N` on `α`. -/
add_decl_doc add_action.comp_hom

variable {α}

/-- The tautological action by `function.End α` on `α`. -/
instance function_End : mul_action (function.End α) α :=
{ smul := ($),
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

/-- The monoid hom representing a monoid action. -/
def to_End_hom : M →* function.End α :=
{ to_fun := (•),
  map_one' := funext (one_smul M),
  map_mul' := λ x y, funext (mul_smul x y) }

/-- The monoid action induced by a monoid hom to `function.End α`-/
def of_End_hom [monoid N] (f : N →* function.End α) : mul_action N α := comp_hom α f

end mul_action

end

section compatible_scalar

@[simp] lemma smul_one_smul {M} (N) [monoid N] [has_scalar M N] [mul_action N α] [has_scalar M α]
  [is_scalar_tower M N α] (x : M) (y : α) :
  (x • (1 : N)) • y = x • y :=
by rw [smul_assoc, one_smul]

end compatible_scalar

/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
class distrib_mul_action (M : Type*) (A : Type*) [monoid M] [add_monoid A]
  extends mul_action M A :=
(smul_add : ∀(r : M) (x y : A), r • (x + y) = r • x + r • y)
(smul_zero : ∀(r : M), r • (0 : A) = 0)

section
variables [monoid M] [add_monoid A] [distrib_mul_action M A]

theorem smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
distrib_mul_action.smul_add _ _ _

@[simp] theorem smul_zero (a : M) : a • (0 : A) = 0 :=
distrib_mul_action.smul_zero _

/-- Pullback a distributive multiplicative action along an injective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.distrib_mul_action [add_monoid B] [has_scalar M B] (f : B →+ A)
  (hf : injective f) (smul : ∀ (c : M) x, f (c • x) = c • f x) :
  distrib_mul_action M B :=
{ smul := (•),
  smul_add := λ c x y, hf $ by simp only [smul, f.map_add, smul_add],
  smul_zero := λ c, hf $ by simp only [smul, f.map_zero, smul_zero],
  .. hf.mul_action f smul }

/-- Pushforward a distributive multiplicative action along a surjective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.distrib_mul_action [add_monoid B] [has_scalar M B] (f : A →+ B)
  (hf : surjective f) (smul : ∀ (c : M) x, f (c • x) = c • f x) :
  distrib_mul_action M B :=
{ smul := (•),
  smul_add := λ c x y, by { rcases hf x with ⟨x, rfl⟩, rcases hf y with ⟨y, rfl⟩,
    simp only [smul_add, ← smul, ← f.map_add] },
  smul_zero := λ c, by simp only [← f.map_zero, ← smul, smul_zero],
  .. hf.mul_action f smul }

variable (A)

/-- Compose a `distrib_mul_action` with a `monoid_hom`, with action `f r' • m` -/
def distrib_mul_action.comp_hom [monoid N] (f : N →* M) :
  distrib_mul_action N A :=
{ smul := (•) ∘ f,
  smul_zero := λ x, smul_zero (f x),
  smul_add := λ x, smul_add (f x),
  .. mul_action.comp_hom A f }

/-- Scalar multiplication by `r` as an `add_monoid_hom`. -/
def const_smul_hom (r : M) : A →+ A :=
{ to_fun := (•) r,
  map_zero' := smul_zero r,
  map_add' := smul_add r }

variable {A}

@[simp] lemma const_smul_hom_apply (r : M) (x : A) :
  const_smul_hom A r x = r • x := rfl

@[simp] lemma const_smul_hom_one :
  const_smul_hom A (1:M) = add_monoid_hom.id _ :=
by { ext, rw [const_smul_hom_apply, one_smul, add_monoid_hom.id_apply] }

end

section
variables [monoid M] [add_group A] [distrib_mul_action M A]

@[simp] theorem smul_neg (r : M) (x : A) : r • (-x) = -(r • x) :=
eq_neg_of_add_eq_zero $ by rw [← smul_add, neg_add_self, smul_zero]

theorem smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y :=
by rw [sub_eq_add_neg, sub_eq_add_neg, smul_add, smul_neg]

end
