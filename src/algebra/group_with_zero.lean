/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebra.group.units

/-!
# Groups with an adjoined zero element

This file describes structures that are not usually studied on their own right in mathematics,
namely a special sort of monoid: apart from a distinguished “zero element” they form a group,
or in other words, they are groups with an adjoined zero element.

Examples are:

* division rings;
* the value monoid of a multiplicative valuation;
* in particular, the non-negative real numbers.

## Main definitions

* `group_with_zero`
* `comm_group_with_zero`

## Implementation details

As is usual in mathlib, we extend the inverse function to the zero element,
and require `0⁻¹ = 0`.

-/

set_option old_structure_cmd true

open_locale classical

section prio -- see Note [default priority]
set_option default_priority 100

/-- A type `G` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.

Examples include fields and the ordered monoids that are the
target of valuations in general valuation theory.-/
class group_with_zero (G : Type*)
  extends monoid G, has_inv G, zero_ne_one_class G, mul_zero_class G :=
(inv_zero : (0 : G)⁻¹ = 0)
(mul_inv_cancel : ∀ a:G, a ≠ 0 → a * a⁻¹ = 1)

/-- A type `G` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`. -/
class comm_group_with_zero (G : Type*) extends comm_monoid G, group_with_zero G.

/-- The division operation on a group with zero element. -/
instance group_with_zero.has_div {G : Type*} [group_with_zero G] :
  has_div G := ⟨λ g h, g * h⁻¹⟩

end prio

lemma div_eq_mul_inv {G : Type*} [group_with_zero G] {a b : G} :
  a / b = a * b⁻¹ := rfl

namespace gwz
variables {G : Type*} [group_with_zero G]

@[simp] lemma inv_zero : (0 : G)⁻¹ = 0 :=
group_with_zero.inv_zero G

@[simp] lemma mul_inv_cancel (a : G) (h : a ≠ 0) : a * a⁻¹ = 1 :=
group_with_zero.mul_inv_cancel a h

@[simp] lemma mul_inv_cancel_assoc_left (a b : G) (h : b ≠ 0) :
  (a * b) * b⁻¹ = a :=
calc (a * b) * b⁻¹ = a * (b * b⁻¹) : mul_assoc _ _ _
               ... = a             : by simp [h]

@[simp] lemma mul_inv_cancel_assoc_right (a b : G) (h : a ≠ 0) :
  a * (a⁻¹ * b) = b :=
calc a * (a⁻¹ * b) = (a * a⁻¹) * b : (mul_assoc _ _ _).symm
               ... = b             : by simp [h]

lemma inv_ne_zero {a : G} (h : a ≠ 0) : a⁻¹ ≠ 0 :=
assume a_eq_0, by simpa [a_eq_0] using mul_inv_cancel a h

@[simp] lemma inv_mul_cancel (a : G) (h : a ≠ 0) : a⁻¹ * a = 1 :=
calc a⁻¹ * a = (a⁻¹ * a) * a⁻¹ * a⁻¹⁻¹ : by simp [inv_ne_zero h]
         ... = a⁻¹ * a⁻¹⁻¹             : by simp [h]
         ... = 1                       : by simp [inv_ne_zero h]

@[simp] lemma inv_mul_cancel_assoc_left (a b : G) (h : b ≠ 0) :
  (a * b⁻¹) * b = a :=
calc (a * b⁻¹) * b = a * (b⁻¹ * b) : mul_assoc _ _ _
               ... = a             : by simp [h]

@[simp] lemma inv_mul_cancel_assoc_right (a b : G) (h : a ≠ 0) :
  a⁻¹ * (a * b) = b :=
calc a⁻¹ * (a * b) = (a⁻¹ * a) * b : (mul_assoc _ _ _).symm
               ... = b             : by simp [h]

@[simp] lemma inv_inv (a : G) : a⁻¹⁻¹ = a :=
if h : a = 0 then by simp [h] else
calc a⁻¹⁻¹ = a * (a⁻¹ * a⁻¹⁻¹) : by simp [h]
       ... = a                 : by simp [inv_ne_zero h]

lemma inv_involutive : function.involutive (has_inv.inv : G → G) :=
inv_inv

lemma ne_zero_of_mul_right_eq_one (a b : G) (h : a * b = 1) : a ≠ 0 :=
assume a_eq_0, zero_ne_one (by simpa [a_eq_0] using h : (0:G) = 1)

lemma ne_zero_of_mul_left_eq_one (a b : G) (h : a * b = 1) : b ≠ 0 :=
assume b_eq_0, zero_ne_one (by simpa [b_eq_0] using h : (0:G) = 1)

lemma eq_inv_of_mul_right_eq_one (a b : G) (h : a * b = 1) :
  b = a⁻¹ :=
calc b = a⁻¹ * (a * b) :
        (inv_mul_cancel_assoc_right _ _ $ ne_zero_of_mul_right_eq_one a b h).symm
   ... = a⁻¹ : by simp [h]

lemma eq_inv_of_mul_left_eq_one (a b : G) (h : a * b = 1) :
  a = b⁻¹ :=
calc a = (a * b) * b⁻¹ : (mul_inv_cancel_assoc_left _ _ (ne_zero_of_mul_left_eq_one a b h)).symm
   ... = b⁻¹ : by simp [h]

@[simp] lemma inv_one : (1 : G)⁻¹ = 1 :=
eq.symm $ eq_inv_of_mul_right_eq_one _ _ (mul_one 1)

lemma inv_injective : function.injective (@has_inv.inv G _) :=
begin
  assume g h H,
  rw [← inv_inv g, ← inv_inv h],
  exact congr_arg _ H
end

@[simp] lemma inv_inj (g h : G) :
  g⁻¹ = h⁻¹ ↔ g = h :=
⟨assume H, inv_injective H, congr_arg _⟩

lemma inv_eq_iff {g h : G} : g⁻¹ = h ↔ g⁻¹ = h :=
by rw [← inv_inj, eq_comm, gwz.inv_inv]

@[simp] lemma inv_eq_zero {a : G} : a⁻¹ = 0 ↔ a = 0 :=
classical.by_cases (assume : a = 0, by simp [*]) (assume : a ≠ 0, by simp [*, inv_ne_zero])

@[simp] lemma coe_unit_mul_inv (a : units G) : (a : G) * a⁻¹ = 1 :=
mul_inv_cancel _ $ ne_zero_of_mul_right_eq_one _ (a⁻¹ : units G) $ by simp

@[simp] lemma coe_unit_inv_mul (a : units G) : (a⁻¹ : G) * a = 1 :=
inv_mul_cancel _ $ ne_zero_of_mul_right_eq_one _ (a⁻¹ : units G) $ by simp

@[simp] lemma unit_ne_zero (a : units G) : (a : G) ≠ 0 :=
assume a_eq_0, zero_ne_one $
calc 0 = (a : G) * a⁻¹ : by simp [a_eq_0]
   ... = 1 : by simp

end gwz

namespace units
variables {G : Type*} [group_with_zero G]
variables {a b : G}

/-- Embed an element of a division ring into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments. -/
def mk0 (a : G) (ha : a ≠ 0) : units G :=
⟨a, a⁻¹, gwz.mul_inv_cancel _ ha, gwz.inv_mul_cancel _ ha⟩

@[simp] lemma coe_mk0 {a : G} (h : a ≠ 0) : (mk0 a h : G) = a := rfl

@[simp] theorem inv_eq_inv (u : units G) : (↑u⁻¹ : G) = u⁻¹ :=
(mul_left_inj u).1 $ by { rw [units.mul_inv, gwz.mul_inv_cancel], apply gwz.unit_ne_zero }

@[simp] lemma mk0_coe (u : units G) (h : (u : G) ≠ 0) : mk0 (u : G) h = u :=
units.ext rfl

@[simp] lemma mk0_inj {a b : G} (ha : a ≠ 0) (hb : b ≠ 0) :
  units.mk0 a ha = units.mk0 b hb ↔ a = b :=
⟨λ h, by injection h, λ h, units.ext h⟩

end units

namespace gwz
variables {G : Type*} [group_with_zero G]

lemma mul_eq_zero (a b : G) (h : a * b = 0) : a = 0 ∨ b = 0 :=
begin
  contrapose! h,
  exact unit_ne_zero ((units.mk0 a h.1) * (units.mk0 b h.2))
end

section prio -- see Note [default priority]
set_option default_priority 100

instance : no_zero_divisors G :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := mul_eq_zero,
  .. (‹_› : group_with_zero G) }

end prio

@[simp] lemma mul_eq_zero_iff {a b : G} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
⟨mul_eq_zero a b, by rintro (H|H); simp [H]⟩

lemma mul_ne_zero {a b : G} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
begin
  assume ab0, rw gwz.mul_eq_zero_iff at ab0,
  cases ab0; contradiction
end

lemma mul_ne_zero_iff {a b : G} : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
by { rw ← not_iff_not, push_neg, exact mul_eq_zero_iff }

lemma mul_left_cancel {x : G} (hx : x ≠ 0) {y z : G} (h : x * y = x * z) : y = z :=
calc y = x⁻¹ * (x * y) : by rw inv_mul_cancel_assoc_right _ _ hx
   ... = x⁻¹ * (x * z) : by rw h
   ... = z             : by rw inv_mul_cancel_assoc_right _ _ hx

lemma mul_right_cancel {x : G} (hx : x ≠ 0) {y z : G} (h : y * x = z * x) : y = z :=
calc y = (y * x) * x⁻¹ : by rw mul_inv_cancel_assoc_left _ _ hx
   ... = (z * x) * x⁻¹ : by rw h
   ... = z             : by rw mul_inv_cancel_assoc_left _ _ hx

lemma mul_inv_eq_of_eq_mul {x : G} (hx : x ≠ 0) {y z : G} (h : y = z * x) : y * x⁻¹ = z :=
h.symm ▸ (mul_inv_cancel_assoc_left z x hx)

lemma eq_mul_inv_of_mul_eq {x : G} (hx : x ≠ 0) {y z : G} (h : z * x = y) : z = y * x⁻¹ :=
eq.symm $ mul_inv_eq_of_eq_mul hx h.symm

lemma mul_inv_rev (x y : G) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
begin
  by_cases hx : x = 0, { simp [hx] },
  by_cases hy : y = 0, { simp [hy] },
  symmetry,
  apply eq_inv_of_mul_left_eq_one,
  simp [mul_assoc, hx, hy]
end

theorem inv_comm_of_comm {a b : G} (H : a * b = b * a) : a⁻¹ * b = b * a⁻¹ :=
begin
  have : a⁻¹ * (b * a) * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ :=
    congr_arg (λ x:G, a⁻¹ * x * a⁻¹) H.symm,
  by_cases h : a = 0, { rw [h, inv_zero, zero_mul, mul_zero] },
  rwa [inv_mul_cancel_assoc_right _ _ h, mul_assoc, mul_inv_cancel_assoc_left _ _ h] at this,
end

@[simp] lemma div_self {a : G} (h : a ≠ 0) : a / a = 1 := mul_inv_cancel _ h

@[simp] lemma div_one (a : G) : a / 1 = a :=
show a * 1⁻¹ = a, by rw [inv_one, mul_one]

lemma one_div (a : G) : 1 / a = a⁻¹ := one_mul _

@[simp] lemma zero_div (a : G) : 0 / a = 0 := zero_mul _

@[simp] lemma div_zero (a : G) : a / 0 = 0 :=
show a * 0⁻¹ = 0, by rw [inv_zero, mul_zero]

@[simp] lemma div_mul_cancel (a : G) {b : G} (h : b ≠ 0) : a / b * b = a :=
inv_mul_cancel_assoc_left a b h

@[simp] lemma mul_div_cancel (a : G) {b : G} (h : b ≠ 0) : a * b / b = a :=
mul_inv_cancel_assoc_left a b h

lemma mul_div_assoc {a b c : G} : a * b / c = a * (b / c) :=
mul_assoc _ _ _

local attribute [simp]
div_eq_mul_inv mul_comm mul_assoc
mul_left_comm mul_inv_cancel inv_mul_cancel

lemma div_eq_mul_one_div (a b : G) : a / b = a * (1 / b) :=
by simp

lemma mul_one_div_cancel {a : G} (h : a ≠ 0) : a * (1 / a) = 1 :=
by simp [h]

lemma one_div_mul_cancel {a : G} (h : a ≠ 0) : (1 / a) * a = 1 :=
by simp [h]

lemma one_div_one : 1 / 1 = (1:G) :=
div_self (ne.symm zero_ne_one)

lemma one_div_ne_zero {a : G} (h : a ≠ 0) : 1 / a ≠ 0 :=
assume : 1 / a = 0,
have 0 = (1:G), from eq.symm (by rw [← mul_one_div_cancel h, this, mul_zero]),
absurd this zero_ne_one

lemma mul_ne_zero_comm {a b : G} (h : a * b ≠ 0) : b * a ≠ 0 :=
by { rw mul_ne_zero_iff at h ⊢, rwa and_comm }

lemma eq_one_div_of_mul_eq_one {a b : G} (h : a * b = 1) : b = 1 / a :=
have a ≠ 0, from
   assume : a = 0,
   have 0 = (1:G), by rwa [this, zero_mul] at h,
      absurd this zero_ne_one,
have b = (1 / a) * a * b, by rw [one_div_mul_cancel this, one_mul],
show b = 1 / a, by rwa [mul_assoc, h, mul_one] at this

lemma eq_one_div_of_mul_eq_one_left {a b : G} (h : b * a = 1) : b = 1 / a :=
have a ≠ 0, from
  assume : a = 0,
  have 0 = (1:G), by rwa [this, mul_zero] at h,
    absurd this zero_ne_one,
by rw [← h, mul_div_assoc, div_self this, mul_one]

@[simp] lemma one_div_div (a b : G) : 1 / (a / b) = b / a :=
by rw [one_div, div_eq_mul_inv, mul_inv_rev, inv_inv, div_eq_mul_inv]

@[simp] lemma one_div_one_div (a : G) : 1 / (1 / a) = a :=
by simp

lemma eq_of_one_div_eq_one_div {a b : G} (h : 1 / a = 1 / b) : a = b :=
by rw [← one_div_one_div a, h, one_div_one_div]

end gwz

section not_comm

variables {G : Type*} [group_with_zero G]
variables {a b c : G}

lemma one_div_mul_one_div_rev (a b : G) : (1 / a) * (1 / b) =  1 / (b * a) :=
by simp only [div_eq_mul_inv, one_mul, gwz.mul_inv_rev]

theorem divp_eq_div (a : G) (u : units G) : a /ₚ u = a / u :=
congr_arg _ $ units.inv_eq_inv _

@[simp] theorem divp_mk0 (a : G) {b : G} (hb : b ≠ 0) :
  a /ₚ units.mk0 b hb = a / b :=
divp_eq_div _ _

lemma inv_div : (a / b)⁻¹ = b / a :=
(gwz.mul_inv_rev _ _).trans (by rw gwz.inv_inv; refl)

lemma inv_div_left : a⁻¹ / b = (b * a)⁻¹ :=
(gwz.mul_inv_rev _ _).symm

lemma div_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 :=
gwz.mul_ne_zero ha (gwz.inv_ne_zero hb)

lemma div_ne_zero_iff (hb : b ≠ 0) : a / b ≠ 0 ↔ a ≠ 0 :=
⟨mt (λ h, by rw [h, gwz.zero_div]), λ ha, div_ne_zero ha hb⟩

lemma div_eq_zero_iff (hb : b ≠ 0) : a / b = 0 ↔ a = 0 :=
by haveI := classical.prop_decidable; exact
not_iff_not.1 (div_ne_zero_iff hb)

lemma div_right_inj (hc : c ≠ 0) : a / c = b / c ↔ a = b :=
by rw [← divp_mk0 _ hc, ← divp_mk0 _ hc, divp_right_inj]

lemma gwz.mul_right_inj (hc : c ≠ 0) : a * c = b * c ↔ a = b :=
by rw [← gwz.inv_inv c, ← div_eq_mul_inv, ← div_eq_mul_inv, div_right_inj (gwz.inv_ne_zero hc)]

lemma div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
⟨λ h, by rw [← h, gwz.div_mul_cancel _ hb],
 λ h, by rw [← h, gwz.mul_div_cancel _ hb]⟩

end not_comm

namespace gwz -- comm
variables {G : Type*} [comm_group_with_zero G] {a b c : G}

lemma mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
by rw [gwz.mul_inv_rev, mul_comm]

lemma one_div_mul_one_div (a b : G) : (1 / a) * (1 / b) =  1 / (a * b) :=
by rw [one_div_mul_one_div_rev, mul_comm b]

lemma div_mul_right {a : G} (b : G) (ha : a ≠ 0) : a / (a * b) = 1 / b :=
eq.symm (calc
    1 / b = a * ((1 / a) * (1 / b)) : by rw [← mul_assoc, gwz.one_div a, mul_inv_cancel a ha, one_mul]
      ... = a * (1 / (b * a))       : by rw one_div_mul_one_div_rev
      ... = a * (a * b)⁻¹           : by rw [← one_div, mul_comm a b])

lemma div_mul_left {a b : G} (hb : b ≠ 0) : b / (a * b) = 1 / a :=
by rw [mul_comm a, div_mul_right _ hb]

lemma mul_div_cancel_left {a : G} (b : G) (ha : a ≠ 0) : a * b / a = b :=
by rw [mul_comm a, (mul_div_cancel _ ha)]

lemma mul_div_cancel' (a : G) {b : G} (hb : b ≠ 0) : b * (a / b) = a :=
by rw [mul_comm, (div_mul_cancel _ hb)]

local attribute [simp] mul_assoc mul_comm mul_left_comm

lemma div_mul_div (a b c d : G) :
      (a / b) * (c / d) = (a * c) / (b * d) :=
by { simp [div_eq_mul_inv], rw [gwz.mul_inv_rev, mul_comm d⁻¹] }

lemma mul_div_mul_left (a b : G) {c : G} (hc : c ≠ 0) :
      (c * a) / (c * b) = a / b :=
by rw [← div_mul_div, div_self hc, one_mul]

lemma mul_div_mul_right (a b : G) {c : G} (hc : c ≠ 0) :
      (a * c) / (b * c) = a / b :=
by rw [mul_comm a, mul_comm b, mul_div_mul_left _ _ hc]

lemma div_mul_eq_mul_div (a b c : G) : (b / c) * a = (b * a) / c :=
by simp [div_eq_mul_inv]

lemma div_mul_eq_mul_div_comm (a b c : G) :
      (b / c) * a = b * (a / c) :=
by rw [div_mul_eq_mul_div, ← one_mul c, ← div_mul_div,
       div_one, one_mul]

lemma mul_eq_mul_of_div_eq_div (a : G) {b : G} (c : G) {d : G} (hb : b ≠ 0)
      (hd : d ≠ 0) (h : a / b = c / d) : a * d = c * b :=
by rw [← mul_one (a*d), mul_assoc, mul_comm d, ← mul_assoc, ← div_self hb,
       ← div_mul_eq_mul_div_comm, h, div_mul_eq_mul_div, div_mul_cancel _ hd]

lemma div_div_eq_mul_div (a b c : G) :
      a / (b / c) = (a * c) / b :=
by rw [div_eq_mul_one_div, one_div_div, ← mul_div_assoc]

lemma div_div_eq_div_mul (a b c : G) :
      (a / b) / c = a / (b * c) :=
by rw [div_eq_mul_one_div, div_mul_div, mul_one]

lemma div_div_div_div_eq (a : G) {b c d : G} :
      (a / b) / (c / d) = (a * d) / (b * c) :=
by rw [div_div_eq_mul_div, div_mul_eq_mul_div,
       div_div_eq_div_mul]

lemma div_mul_eq_div_mul_one_div (a b c : G) :
      a / (b * c) = (a / b) * (1 / c) :=
by rw [← div_div_eq_div_mul, ← div_eq_mul_one_div]

lemma eq_of_mul_eq_mul_of_nonzero_left {a b c : G} (h : a ≠ 0) (h₂ : a * b = a * c) : b = c :=
by rw [← one_mul b, ← div_self h, div_mul_eq_mul_div, h₂, mul_div_cancel_left _ h]

lemma eq_of_mul_eq_mul_of_nonzero_right {a b c : G} (h : c ≠ 0) (h2 : a * c = b * c) : a = b :=
by rw [← mul_one a, ← div_self h, ← mul_div_assoc, h2, mul_div_cancel _ h]

lemma ne_zero_of_one_div_ne_zero {a : G} (h : 1 / a ≠ 0) : a ≠ 0 :=
assume ha : a = 0, begin rw [ha, div_zero] at h, contradiction end

lemma eq_zero_of_one_div_eq_zero {a : G} (h : 1 / a = 0) : a = 0 :=
classical.by_cases
  (assume ha, ha)
  (assume ha, false.elim ((one_div_ne_zero ha) h))

lemma div_helper {a : G} (b : G) (h : a ≠ 0) : (1 / (a * b)) * a = 1 / b :=
by rw [div_mul_eq_mul_div, one_mul, div_mul_right _ h]

end gwz

section comm
open gwz
variables {G : Type*} [comm_group_with_zero G] {a b c d : G}

lemma div_eq_inv_mul : a / b = b⁻¹ * a := mul_comm _ _

lemma mul_div_right_comm (a b c : G) : (a * b) / c = (a / c) * b :=
by rw [div_eq_mul_inv, mul_assoc, mul_comm b, ← mul_assoc]; refl

lemma mul_comm_div (a b c : G) : (a / b) * c = a * (c / b) :=
by rw [← gwz.mul_div_assoc, mul_div_right_comm]

lemma div_mul_comm (a b c : G) : (a / b) * c = (c / b) * a :=
by rw [gwz.div_mul_eq_mul_div, mul_comm, mul_div_right_comm]

lemma mul_div_comm (a b c : G) : a * (b / c) = b * (a / c) :=
by rw [← gwz.mul_div_assoc, mul_comm, gwz.mul_div_assoc]

lemma gwz.div_right_comm (a : G) : (a / b) / c = (a / c) / b :=
by rw [gwz.div_div_eq_div_mul, gwz.div_div_eq_div_mul, mul_comm]

lemma gwz.div_div_div_cancel_right (a : G) (hc : c ≠ 0) : (a / c) / (b / c) = a / b :=
by rw [gwz.div_div_eq_mul_div, div_mul_cancel _ hc]

lemma div_mul_div_cancel (a : G) (hc : c ≠ 0) : (a / c) * (c / b) = a / b :=
by rw [← gwz.mul_div_assoc, gwz.div_mul_cancel _ hc]

lemma div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
calc a / b = c / d ↔ a / b * (b * d) = c / d * (b * d) :
by rw [mul_right_inj (mul_ne_zero hb hd)]
               ... ↔ a * d = c * b :
by rw [← mul_assoc, gwz.div_mul_cancel _ hb,
      ← mul_assoc, mul_right_comm, gwz.div_mul_cancel _ hd]

lemma div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b :=
by simpa using @div_eq_div_iff _ _ a b c 1 hb one_ne_zero

lemma eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a :=
by simpa using @div_eq_div_iff _ _ c 1 a b one_ne_zero hb

lemma gwz.div_div_cancel (ha : a ≠ 0) : a / (a / b) = b :=
by rw [div_eq_mul_inv, inv_div, mul_div_cancel' _ ha]

end comm
