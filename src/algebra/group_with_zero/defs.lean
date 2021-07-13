/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.group.defs
import logic.nontrivial

/-!
# Typeclasses for groups with an adjoined zero element

This file provides just the typeclass definitions, and the projection lemmas that expose their
members.

## Main definitions

* `group_with_zero`
* `comm_group_with_zero`
-/

set_option old_structure_cmd true

universe u

-- We have to fix the universe of `G₀` here, since the default argument to
-- `group_with_zero.div'` cannot contain a universe metavariable.
variables {G₀ : Type u} {M₀ M₀' G₀' : Type*}

section

/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
@[protect_proj, ancestor has_mul has_zero]
class mul_zero_class (M₀ : Type*) extends has_mul M₀, has_zero M₀ :=
(zero_mul : ∀ a : M₀, 0 * a = 0)
(mul_zero : ∀ a : M₀, a * 0 = 0)

section mul_zero_class

variables [mul_zero_class M₀] {a b : M₀}

@[ematch, simp] lemma zero_mul (a : M₀) : 0 * a = 0 :=
mul_zero_class.zero_mul a

@[ematch, simp] lemma mul_zero (a : M₀) : a * 0 = 0 :=
mul_zero_class.mul_zero a

variables {ι : Type*} [decidable_eq ι]

lemma pi.single_mul_fun_apply (i j : ι) (a : M₀) (f : ι → M₀) :
  pi.single i a j * f j = pi.single i (a * f i) j :=
pi.apply_single (λ i, (* f i)) (λ i, zero_mul _) _ _ _

lemma pi.fun_mul_single_apply (i j : ι) (f : ι → M₀) (a : M₀) :
  f j * pi.single i a j = pi.single i (f i * a) j :=
pi.apply_single (λ i, ((*) (f i))) (λ i, mul_zero _) _ _ _

lemma pi.single_mul_fun (i : ι) (a : M₀) (f : ι → M₀) :
  pi.single i a * f = pi.single i (a * f i) :=
funext $ λ j, pi.single_mul_fun_apply i j a f

lemma pi.fun_mul_single (i : ι) (f : ι → M₀) (a : M₀) :
  f * pi.single i a = pi.single i (f i * a) :=
funext $ λ j, pi.fun_mul_single_apply i j f a

end mul_zero_class

/-- Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`
for all `a` and `b` of type `G₀`. -/
class no_zero_divisors (M₀ : Type*) [has_mul M₀] [has_zero M₀] : Prop :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0)

export no_zero_divisors (eq_zero_or_eq_zero_of_mul_eq_zero)

/-- A type `S₀` is a "semigroup with zero” if it is a semigroup with zero element, and `0` is left
and right absorbing. -/
@[protect_proj] class semigroup_with_zero (S₀ : Type*) extends semigroup S₀, mul_zero_class S₀.

/- By defining this _after_ `semigroup_with_zero`, we ensure that searches for `mul_zero_class` find
this class first. -/
/-- A typeclass for non-associative monoids with zero elements. -/
@[protect_proj] class mul_zero_one_class (M₀ : Type*) extends mul_one_class M₀, mul_zero_class M₀.

/-- A type `M₀` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
@[protect_proj] class monoid_with_zero (M₀ : Type*) extends monoid M₀, mul_zero_one_class M₀.

@[priority 100] -- see Note [lower instance priority]
instance monoid_with_zero.to_semigroup_with_zero (M₀ : Type*) [monoid_with_zero M₀] :
  semigroup_with_zero M₀ :=
{ ..‹monoid_with_zero M₀› }

/-- A type `M` is a `cancel_monoid_with_zero` if it is a monoid with zero element, `0` is left
and right absorbing, and left/right multiplication by a non-zero element is injective. -/
@[protect_proj] class cancel_monoid_with_zero (M₀ : Type*) extends monoid_with_zero M₀ :=
(mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c)
(mul_right_cancel_of_ne_zero : ∀ {a b c : M₀}, b ≠ 0 → a * b = c * b → a = c)

section cancel_monoid_with_zero

variables [cancel_monoid_with_zero M₀] {a b c : M₀}

lemma mul_left_cancel' (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
cancel_monoid_with_zero.mul_left_cancel_of_ne_zero ha h

lemma mul_right_cancel' (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
cancel_monoid_with_zero.mul_right_cancel_of_ne_zero hb h

lemma mul_right_injective' (ha : a ≠ 0) : function.injective ((*) a) :=
λ b c, mul_left_cancel' ha

lemma mul_left_injective' (hb : b ≠ 0) : function.injective (λ a, a * b) :=
λ a c, mul_right_cancel' hb

end cancel_monoid_with_zero

/-- A type `M` is a commutative “monoid with zero” if it is a commutative monoid with zero
element, and `0` is left and right absorbing. -/
@[protect_proj]
class comm_monoid_with_zero (M₀ : Type*) extends comm_monoid M₀, monoid_with_zero M₀.

/-- A type `M` is a `comm_cancel_monoid_with_zero` if it is a commutative monoid with zero element,
 `0` is left and right absorbing,
  and left/right multiplication by a non-zero element is injective. -/
@[protect_proj] class comm_cancel_monoid_with_zero (M₀ : Type*) extends
  comm_monoid_with_zero M₀, cancel_monoid_with_zero M₀.

/-- A type `G₀` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.

Examples include division rings and the ordered monoids that are the
target of valuations in general valuation theory.-/
class group_with_zero (G₀ : Type u) extends
  monoid_with_zero G₀, div_inv_monoid G₀, nontrivial G₀ :=
(inv_zero : (0 : G₀)⁻¹ = 0)
(mul_inv_cancel : ∀ a:G₀, a ≠ 0 → a * a⁻¹ = 1)

section group_with_zero
variables [group_with_zero G₀]

@[simp] lemma inv_zero : (0 : G₀)⁻¹ = 0 :=
group_with_zero.inv_zero

@[simp] lemma mul_inv_cancel {a : G₀} (h : a ≠ 0) : a * a⁻¹ = 1 :=
group_with_zero.mul_inv_cancel a h

end group_with_zero

/-- A type `G₀` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`. -/
class comm_group_with_zero (G₀ : Type*) extends comm_monoid_with_zero G₀, group_with_zero G₀.

end
