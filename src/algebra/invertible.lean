/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import algebra.group.units
import algebra.ring.basic

/-!
# Invertible elements

This file defines a typeclass `invertible a` for elements `a` with a two-sided
multiplicative inverse.

The intent of the typeclass is to provide a way to write e.g. `⅟2` in a ring
like `ℤ[1/2]` where some inverses exist but there is no general `⁻¹` operator;
or to specify that a field has characteristic `≠ 2`.
It is the `Type`-valued analogue to the `Prop`-valued `is_unit`.

For constructions of the invertible element given a characteristic, see
`algebra/char_p/invertible` and other lemmas in that file.

## Notation

 * `⅟a` is `invertible.inv_of a`, the inverse of `a`

## Implementation notes

The `invertible` class lives in `Type`, not `Prop`, to make computation easier.
If multiplication is associative, `invertible` is a subsingleton anyway.

The `simp` normal form tries to normalize `⅟a` to `a ⁻¹`. Otherwise, it pushes
`⅟` inside the expression as much as possible.

Since `invertible a` is not a `Prop` (but it is a `subsingleton`), we have to be careful about
coherence issues: we should avoid having multiple non-defeq instances for `invertible a` in the
same context.  This file plays it safe and uses `def` rather than `instance` for most definitions,
users can choose which instances to use at the point of use.

For example, here's how you can use an `invertible 1` instance:
```lean
variables {α : Type*} [monoid α]

def something_that_needs_inverses (x : α) [invertible x] := sorry

section
local attribute [instance] invertible_one
def something_one := something_that_needs_inverses 1
end
```

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

lemma inv_of_eq_left_inv [monoid α] {a b : α} [invertible a] (hac : b * a = 1) : ⅟a = b :=
(left_inv_eq_right_inv hac (mul_inv_of_self _)).symm

lemma invertible_unique {α : Type u} [monoid α] (a b : α) (h : a = b)
  [invertible a] [invertible b] :
  ⅟a = ⅟b :=
by { apply inv_of_eq_right_inv, rw [h, mul_inv_of_self], }

instance [monoid α] (a : α) : subsingleton (invertible a) :=
⟨ λ ⟨b, hba, hab⟩ ⟨c, hca, hac⟩, by { congr, exact left_inv_eq_right_inv hba hac } ⟩

/-- If `r` is invertible and `s = r`, then `s` is invertible. -/
def invertible.copy [monoid α] {r : α} (hr : invertible r) (s : α) (hs : s = r) : invertible s :=
{ inv_of := ⅟r,
  inv_of_mul_self := by rw [hs, inv_of_mul_self],
  mul_inv_of_self := by rw [hs, mul_inv_of_self] }

/-- An `invertible` element is a unit. -/
@[simps]
def unit_of_invertible [monoid α] (a : α) [invertible a] : units α :=
{ val     := a,
  inv     := ⅟a,
  val_inv := by simp,
  inv_val := by simp, }

lemma is_unit_of_invertible [monoid α] (a : α) [invertible a] : is_unit a :=
⟨unit_of_invertible a, rfl⟩

/-- Units are invertible in their associated monoid. -/
def units.invertible [monoid α] (u : units α) : invertible (u : α) :=
{ inv_of := ↑(u⁻¹), inv_of_mul_self := u.inv_mul, mul_inv_of_self := u.mul_inv }

@[simp] lemma inv_of_units [monoid α] (u : units α) [invertible (u : α)] : ⅟(u : α) = ↑(u⁻¹) :=
inv_of_eq_right_inv u.mul_inv

lemma is_unit.nonempty_invertible [monoid α] {a : α} (h : is_unit a) : nonempty (invertible a) :=
let ⟨x, hx⟩ := h in ⟨x.invertible.copy _ hx.symm⟩

/-- Convert `is_unit` to `invertible` using `classical.choice`.

Prefer `casesI h.nonempty_invertible` over `letI := h.invertible` if you want to avoid choice. -/
noncomputable def is_unit.invertible [monoid α] {a : α} (h : is_unit a) : invertible a :=
classical.choice h.nonempty_invertible

@[simp]
lemma nonempty_invertible_iff_is_unit [monoid α] (a : α) :
  nonempty (invertible a) ↔ is_unit a :=
⟨nonempty.rec $ @is_unit_of_invertible _ _ _, is_unit.nonempty_invertible⟩

/-- Each element of a group is invertible. -/
def invertible_of_group [group α] (a : α) : invertible a :=
⟨a⁻¹, inv_mul_self a, mul_inv_self a⟩

@[simp] lemma inv_of_eq_group_inv [group α] (a : α) [invertible a] : ⅟a = a⁻¹ :=
inv_of_eq_right_inv (mul_inv_self a)

/-- `1` is the inverse of itself -/
def invertible_one [monoid α] : invertible (1 : α) :=
⟨1, mul_one _, one_mul _⟩

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

theorem commute.inv_of_right [monoid α] {a b : α} [invertible b] (h : commute a b) :
  commute a (⅟b) :=
calc a * (⅟b) = (⅟b) * (b * a * (⅟b)) : by simp [mul_assoc]
... = (⅟b) * (a * b * ((⅟b))) : by rw h.eq
... = (⅟b) * a : by simp [mul_assoc]

theorem commute.inv_of_left [monoid α] {a b : α} [invertible b] (h : commute b a) :
  commute (⅟b) a :=
calc (⅟b) * a = (⅟b) * (a * b * (⅟b)) : by simp [mul_assoc]
... = (⅟b) * (b * a * (⅟b)) : by rw h.eq
... = a * (⅟b) : by simp [mul_assoc]

lemma commute_inv_of {M : Type*} [has_one M] [has_mul M] (m : M) [invertible m] :
  commute m (⅟m) :=
calc m * ⅟m = 1       : mul_inv_of_self m
        ... = ⅟ m * m : (inv_of_mul_self m).symm

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
