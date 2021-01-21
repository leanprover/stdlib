/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen

A typeclass for the two-sided multiplicative inverse.
-/

import algebra.char_p.basic

/-!
# Invertible elements

This file defines a typeclass `invertible a` for elements `a` with a
multiplicative inverse.

The intent of the typeclass is to provide a way to write e.g. `⅟2` in a ring
like `ℤ[1/2]` where some inverses exist but there is no general `⁻¹` operator;
or to specify that a field has characteristic `≠ 2`.
It is the `Type`-valued analogue to the `Prop`-valued `is_unit`.

This file also includes some instances of `invertible` for specific numbers in
characteristic zero. Some more cases are given as a `def`, to be included only
when needed. To construct instances for concrete numbers,
`invertible_of_nonzero` is a useful definition.

## Notation

 * `⅟a` is `invertible.inv_of a`, the inverse of `a`

## Implementation notes

The `invertible` class lives in `Type`, not `Prop`, to make computation easier.
If multiplication is associative, `invertible` is a subsingleton anyway.

The `simp` normal form tries to normalize `⅟a` to `a ⁻¹`. Otherwise, it pushes
`⅟` inside the expression as much as possible.

## Tags

invertible, inverse element, inv_of, a half, one half, a third, one third, ½, ⅓

-/

universes u

variables {α : Type u}

/-- `invertible a` gives a two-sided multiplicative inverse of `a`. -/
class invertible [has_mul α] [has_one α] (a : α) : Type u :=
(inv_of : α) (inv_of_mul_self : inv_of * a = 1) (mul_inv_of_self : a * inv_of = 1)

-- This notation has the same precedence as `has_inv.inv`.
notation `⅟`:1034 := invertible.inv_of

@[simp]
lemma inv_of_mul_self [has_mul α] [has_one α] (a : α) [invertible a] : ⅟a * a = 1 :=
invertible.inv_of_mul_self

@[simp]
lemma mul_inv_of_self [has_mul α] [has_one α] (a : α) [invertible a] : a * ⅟a = 1 :=
invertible.mul_inv_of_self

@[simp]
lemma inv_of_mul_self_assoc [monoid α] (a b : α) [invertible a] : ⅟a * (a * b) = b :=
by rw [←mul_assoc, inv_of_mul_self, one_mul]

@[simp]
lemma mul_inv_of_self_assoc [monoid α] (a b : α) [invertible a] : a * (⅟a * b) = b :=
by rw [←mul_assoc, mul_inv_of_self, one_mul]

@[simp]
lemma mul_inv_of_mul_self_cancel [monoid α] (a b : α) [invertible b] : a * ⅟b * b = a :=
by simp [mul_assoc]

@[simp]
lemma mul_mul_inv_of_self_cancel [monoid α] (a b : α) [invertible b] : a * b * ⅟b = a :=
by simp [mul_assoc]

lemma inv_of_eq_right_inv [monoid α] {a b : α} [invertible a] (hac : a * b = 1) : ⅟a = b :=
left_inv_eq_right_inv (inv_of_mul_self _) hac

lemma invertible_unique {α : Type u} [monoid α] (a b : α) (h : a = b)
  [invertible a] [invertible b] :
  ⅟a = ⅟b :=
by { apply inv_of_eq_right_inv, rw [h, mul_inv_of_self], }

instance [monoid α] (a : α) : subsingleton (invertible a) :=
⟨ λ ⟨b, hba, hab⟩ ⟨c, hca, hac⟩, by { congr, exact left_inv_eq_right_inv hba hac } ⟩

/-- An `invertible` element is a unit. -/
def unit_of_invertible [monoid α] (a : α) [invertible a] : units α :=
{ val     := a,
  inv     := ⅟a,
  val_inv := by simp,
  inv_val := by simp, }

@[simp] lemma unit_of_invertible_val [monoid α] (a : α) [invertible a] :
  (unit_of_invertible a : α) = a := rfl

@[simp] lemma unit_of_invertible_inv [monoid α] (a : α) [invertible a] :
  (↑(unit_of_invertible a)⁻¹ : α) = ⅟a := rfl

lemma is_unit_of_invertible [monoid α] (a : α) [invertible a] : is_unit a :=
⟨unit_of_invertible a, rfl⟩

/-- Each element of a group is invertible. -/
def invertible_of_group [group α] (a : α) : invertible a :=
⟨a⁻¹, inv_mul_self a, mul_inv_self a⟩

@[simp] lemma inv_of_eq_group_inv [group α] (a : α) [invertible a] : ⅟a = a⁻¹ :=
inv_of_eq_right_inv (mul_inv_self a)

/-- `1` is the inverse of itself -/
def invertible_one [monoid α] : invertible (1 : α) :=
⟨ 1, mul_one _, one_mul _ ⟩

@[simp] lemma inv_of_one [monoid α] [invertible (1 : α)] : ⅟(1 : α) = 1 :=
inv_of_eq_right_inv (mul_one _)

/-- `-⅟a` is the inverse of `-a` -/
def invertible_neg [ring α] (a : α) [invertible a] : invertible (-a) :=
⟨ -⅟a, by simp, by simp ⟩

@[simp] lemma inv_of_neg [ring α] (a : α) [invertible a] [invertible (-a)] : ⅟(-a) = -⅟a :=
inv_of_eq_right_inv (by simp)

@[simp] lemma one_sub_inv_of_two [ring α] [invertible (2:α)] : 1 - (⅟2:α) = ⅟2 :=
(is_unit_of_invertible (2:α)).mul_right_inj.1 $
  by rw [mul_sub, mul_inv_of_self, mul_one, bit0, add_sub_cancel]

/-- `a` is the inverse of `⅟a`. -/
instance invertible_inv_of [has_one α] [has_mul α] {a : α} [invertible a] : invertible (⅟a) :=
⟨ a, mul_inv_of_self a, inv_of_mul_self a ⟩

@[simp] lemma inv_of_inv_of [monoid α] {a : α} [invertible a] [invertible (⅟a)] :
  ⅟(⅟a) = a :=
inv_of_eq_right_inv (inv_of_mul_self _)

/-- `⅟b * ⅟a` is the inverse of `a * b` -/
def invertible_mul [monoid α] (a b : α) [invertible a] [invertible b] : invertible (a * b) :=
⟨ ⅟b * ⅟a, by simp [←mul_assoc], by simp [←mul_assoc] ⟩

@[simp]
lemma inv_of_mul [monoid α] (a b : α) [invertible a] [invertible b] [invertible (a * b)] :
  ⅟(a * b) = ⅟b * ⅟a :=
inv_of_eq_right_inv (by simp [←mul_assoc])

/--
If `r` is invertible and `s = r`, then `s` is invertible.
-/
def invertible.copy [monoid α] {r : α} (hr : invertible r) (s : α) (hs : s = r) : invertible s :=
{ inv_of := ⅟r,
  inv_of_mul_self := by rw [hs, inv_of_mul_self],
  mul_inv_of_self := by rw [hs, mul_inv_of_self] }


lemma commute_inv_of {M : Type*} [has_one M] [has_mul M] (m : M) [invertible m] :
  commute m (⅟m) :=
calc m * ⅟m = 1       : mul_inv_of_self m
        ... = ⅟ m * m : (inv_of_mul_self m).symm

instance invertible_pow {M : Type*} [monoid M] (m : M) [invertible m] (n : ℕ) :
  invertible (m ^ n) :=
{ inv_of := ⅟ m ^ n,
  inv_of_mul_self := by rw [← (commute_inv_of m).symm.mul_pow, inv_of_mul_self, one_pow],
  mul_inv_of_self := by rw [← (commute_inv_of m).mul_pow, mul_inv_of_self, one_pow] }

section group_with_zero

variable [group_with_zero α]

lemma nonzero_of_invertible (a : α) [invertible a] : a ≠ 0 :=
λ ha, zero_ne_one $ calc   0 = ⅟a * a : by simp [ha]
                         ... = 1 : inv_of_mul_self a

/-- `a⁻¹` is an inverse of `a` if `a ≠ 0` -/
def invertible_of_nonzero {a : α} (h : a ≠ 0) : invertible a :=
⟨ a⁻¹, inv_mul_cancel h, mul_inv_cancel h ⟩

@[simp] lemma inv_of_eq_inv (a : α) [invertible a] : ⅟a = a⁻¹ :=
inv_of_eq_right_inv (mul_inv_cancel (nonzero_of_invertible a))

@[simp] lemma inv_mul_cancel_of_invertible (a : α) [invertible a] : a⁻¹ * a = 1 :=
inv_mul_cancel (nonzero_of_invertible a)

@[simp] lemma mul_inv_cancel_of_invertible (a : α) [invertible a] : a * a⁻¹ = 1 :=
mul_inv_cancel (nonzero_of_invertible a)

@[simp] lemma div_mul_cancel_of_invertible (a b : α) [invertible b] : a / b * b = a :=
div_mul_cancel a (nonzero_of_invertible b)

@[simp] lemma mul_div_cancel_of_invertible (a b : α) [invertible b] : a * b / b = a :=
mul_div_cancel a (nonzero_of_invertible b)

@[simp] lemma div_self_of_invertible (a : α) [invertible a] : a / a = 1 :=
div_self (nonzero_of_invertible a)

/-- `b / a` is the inverse of `a / b` -/
def invertible_div (a b : α) [invertible a] [invertible b] : invertible (a / b) :=
⟨b / a, by simp [←mul_div_assoc], by simp [←mul_div_assoc]⟩

@[simp] lemma inv_of_div (a b : α) [invertible a] [invertible b] [invertible (a / b)] :
  ⅟(a / b) = b / a :=
inv_of_eq_right_inv (by simp [←mul_div_assoc])

/-- `a` is the inverse of `a⁻¹` -/
def invertible_inv {a : α} [invertible a] : invertible (a⁻¹) :=
⟨ a, by simp, by simp ⟩

end group_with_zero

/--
Monoid homs preserve invertibility.
-/
def invertible.map {R : Type*} {S : Type*} [monoid R] [monoid S] (f : R →* S)
  (r : R) [invertible r] :
  invertible (f r) :=
{ inv_of := f (⅟r),
  inv_of_mul_self := by rw [← f.map_mul, inv_of_mul_self, f.map_one],
  mul_inv_of_self := by rw [← f.map_mul, mul_inv_of_self, f.map_one] }

section ring_char

/-- A natural number `t` is invertible in a field `K` if the charactistic of `K` does not divide
`t`. -/
def invertible_of_ring_char_not_dvd {K : Type*} [field K]
  {t : ℕ} (not_dvd : ¬(ring_char K ∣ t)) : invertible (t : K) :=
invertible_of_nonzero (λ h, not_dvd ((ring_char.spec K t).mp h))

end ring_char

section char_p

/-- A natural number `t` is invertible in a field `K` of charactistic `p` if `p` does not divide
`t`. -/
def invertible_of_char_p_not_dvd {K : Type*} [field K] {p : ℕ} [char_p K p]
  {t : ℕ} (not_dvd : ¬(p ∣ t)) : invertible (t : K) :=
invertible_of_nonzero (λ h, not_dvd ((char_p.cast_eq_zero_iff K p t).mp h))

instance invertible_of_pos {K : Type*} [field K] [char_zero K] (n : ℕ) [h : fact (0 < n)] :
  invertible (n : K) :=
invertible_of_nonzero $ by simpa [pos_iff_ne_zero] using h

end char_p

section division_ring

variable [division_ring α]

instance invertible_succ [char_zero α] (n : ℕ) : invertible (n.succ : α) :=
invertible_of_nonzero (nat.cast_ne_zero.mpr (nat.succ_ne_zero _))

/-!
A few `invertible n` instances for small numerals `n`. Feel free to add your own
number when you need its inverse.
-/

instance invertible_two [char_zero α] : invertible (2 : α) :=
invertible_of_nonzero (by exact_mod_cast (dec_trivial : 2 ≠ 0))

instance invertible_three [char_zero α] : invertible (3 : α) :=
invertible_of_nonzero (by exact_mod_cast (dec_trivial : 3 ≠ 0))

end division_ring
