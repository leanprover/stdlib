/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.group.hom
import logic.embedding

/-!
# Definitions of group actions

This file defines a heirarchy of group action type-classes:

* `has_scalar α β`
* `mul_action α β`
* `distrib_mul_action α β`

The hierarchy is extended further by `semimodule`, defined elsewhere.

Also provided are type-classes regarding the interaction of different group actions,

* `smul_comm_class M N α`
* `is_scalar_tower M N α`

## Notation

`a • b` is used as notation for `smul a b`.

## Implementation details

This file should avoid depending on other parts of `group_theory`, to avoid import cycles.
More sophisticated lemmas belong in `group_theory.group_action`.
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open function

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)

infixr ` • `:73 := has_scalar.smul

/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
@[protect_proj] class mul_action (α : Type u) (β : Type v) [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)

/-- A typeclass mixin saying that two actions on the same space commute. -/
class smul_comm_class (M N α : Type*) [has_scalar M α] [has_scalar N α] : Prop :=
(smul_comm : ∀ (m : M) (n : N) (a : α), m • n • a = n • m • a)

export mul_action (mul_smul) smul_comm_class (smul_comm)

/-- Commutativity of actions is a symmetric relation. This lemma can't be an instance because this
would cause a loop in the instance search graph. -/
lemma smul_comm_class.symm (M N α : Type*) [has_scalar M α] [has_scalar N α]
  [smul_comm_class M N α] : smul_comm_class N M α :=
⟨λ a' a b, (smul_comm a a' b).symm⟩

instance smul_comm_class_self (M α : Type*) [comm_monoid M] [mul_action M α] :
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
variables [monoid α] [mul_action α β]

lemma smul_smul (a₁ a₂ : α) (b : β) : a₁ • a₂ • b = (a₁ * a₂) • b := (mul_smul _ _ _).symm

variable (α)
@[simp] theorem one_smul (b : β) : (1 : α) • b = b := mul_action.one_smul _

variables {α}

/-- Pullback a multiplicative action along an injective map respecting `•`. -/
protected def function.injective.mul_action [has_scalar α γ] (f : γ → β)
  (hf : injective f) (smul : ∀ (c : α) x, f (c • x) = c • f x) :
  mul_action α γ :=
{ smul := (•),
  one_smul := λ x, hf $ (smul _ _).trans $ one_smul _ (f x),
  mul_smul := λ c₁ c₂ x, hf $ by simp only [smul, mul_smul] }

/-- Pushforward a multiplicative action along a surjective map respecting `•`. -/
protected def function.surjective.mul_action [has_scalar α γ] (f : β → γ) (hf : surjective f)
  (smul : ∀ (c : α) x, f (c • x) = c • f x) :
  mul_action α γ :=
{ smul := (•),
  one_smul := λ y, by { rcases hf y with ⟨x, rfl⟩, rw [← smul, one_smul] },
  mul_smul := λ c₁ c₂ y, by { rcases hf y with ⟨x, rfl⟩, simp only [← smul, mul_smul] } }

section ite

variables (p : Prop) [decidable p]

lemma ite_smul (a₁ a₂ : α) (b : β) : (ite p a₁ a₂) • b = ite p (a₁ • b) (a₂ • b) :=
by split_ifs; refl

lemma smul_ite (a : α) (b₁ b₂ : β) : a • (ite p b₁ b₂) = ite p (a • b₁) (a • b₂) :=
by split_ifs; refl

end ite

namespace mul_action

variables (α)

/-- The regular action of a monoid on itself by left multiplication. -/
def regular : mul_action α α :=
{ smul := λ a₁ a₂, a₁ * a₂,
  one_smul := λ a, one_mul a,
  mul_smul := λ a₁ a₂ a₃, mul_assoc _ _ _, }

section regular

local attribute [instance] regular

instance is_scalar_tower.left : is_scalar_tower α α β :=
⟨λ x y z, mul_smul x y z⟩

end regular

variables (α β)

/-- Embedding induced by action. -/
def to_fun : β ↪ (α → β) :=
⟨λ y x, x • y, λ y₁ y₂ H, one_smul α y₁ ▸ one_smul α y₂ ▸ by convert congr_fun H 1⟩

variables {α β}

@[simp] lemma to_fun_apply (x : α) (y : β) : mul_action.to_fun α β y x = x • y :=
rfl

variable (β)

/-- An action of `α` on `β` and a monoid homomorphism `γ → α` induce an action of `γ` on `β`. -/
def comp_hom [monoid γ] (g : γ →* α) :
  mul_action γ β :=
{ smul := λ x b, (g x) • b,
  one_smul := by simp [g.map_one, mul_action.one_smul],
  mul_smul := by simp [g.map_mul, mul_action.mul_smul] }

end mul_action

end

section compatible_scalar

@[simp] lemma smul_one_smul {M} (N) [monoid N] [has_scalar M N] [mul_action N α] [has_scalar M α]
  [is_scalar_tower M N α] (x : M) (y : α) :
  (x • (1 : N)) • y = x • y :=
by rw [smul_assoc, one_smul]

end compatible_scalar

/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
class distrib_mul_action (α : Type u) (β : Type v) [monoid α] [add_monoid β]
  extends mul_action α β :=
(smul_add : ∀(r : α) (x y : β), r • (x + y) = r • x + r • y)
(smul_zero : ∀(r : α), r • (0 : β) = 0)

section
variables [monoid α] [add_monoid β] [distrib_mul_action α β]

theorem smul_add (a : α) (b₁ b₂ : β) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
distrib_mul_action.smul_add _ _ _

@[simp] theorem smul_zero (a : α) : a • (0 : β) = 0 :=
distrib_mul_action.smul_zero _

/-- Pullback a distributive multiplicative action along an injective additive monoid
homomorphism. -/
protected def function.injective.distrib_mul_action [add_monoid γ] [has_scalar α γ] (f : γ →+ β)
  (hf : injective f) (smul : ∀ (c : α) x, f (c • x) = c • f x) :
  distrib_mul_action α γ :=
{ smul := (•),
  smul_add := λ c x y, hf $ by simp only [smul, f.map_add, smul_add],
  smul_zero := λ c, hf $ by simp only [smul, f.map_zero, smul_zero],
  .. hf.mul_action f smul }

/-- Pushforward a distributive multiplicative action along a surjective additive monoid
homomorphism.-/
protected def function.surjective.distrib_mul_action [add_monoid γ] [has_scalar α γ] (f : β →+ γ)
  (hf : surjective f) (smul : ∀ (c : α) x, f (c • x) = c • f x) :
  distrib_mul_action α γ :=
{ smul := (•),
  smul_add := λ c x y, by { rcases hf x with ⟨x, rfl⟩, rcases hf y with ⟨y, rfl⟩,
    simp only [smul_add, ← smul, ← f.map_add] },
  smul_zero := λ c, by simp only [← f.map_zero, ← smul, smul_zero],
  .. hf.mul_action f smul }

variable (β)

/-- Scalar multiplication by `r` as an `add_monoid_hom`. -/
def const_smul_hom (r : α) : β →+ β :=
{ to_fun := (•) r,
  map_zero' := smul_zero r,
  map_add' := smul_add r }

variable {β}

@[simp] lemma const_smul_hom_apply (r : α) (x : β) :
  const_smul_hom β r x = r • x := rfl

end

section
variables [monoid α] [add_group β] [distrib_mul_action α β]

@[simp] theorem smul_neg (r : α) (x : β) : r • (-x) = -(r • x) :=
eq_neg_of_add_eq_zero $ by rw [← smul_add, neg_add_self, smul_zero]

theorem smul_sub (r : α) (x y : β) : r • (x - y) = r • x - r • y :=
by rw [sub_eq_add_neg, sub_eq_add_neg, smul_add, smul_neg]

end
