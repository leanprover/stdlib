/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import algebra.ring.basic
import algebra.group_with_zero

/-!
# Division (semi)rings, (semi)fields

In this file we define four typeclasses:

* `division_semiring` is a nontrivial `semiring` with multiplicative inverses for nonzero elements;
* `division_ring` is a nontrivial `ring` with multiplicative inverses for nonzero elements,
  e.g., quaternions;
* `semifield` is a commutative `division_semiring`, e.g., non-negative real numbers `ℝ≥0`;
* `field` is a commutative `division_ring`, e.g., `ℚ`, `ℝ`, `ℂ`, `ℤ_[p]` etc.

## Tags

division ring, field
-/
open set

set_option old_structure_cmd true

universe u
variables {K : Type u}

/-- A `division_semiring` is a `semiring` with multiplicative inverses for nonzero elements. -/
@[protect_proj, ancestor semiring div_inv_monoid nontrivial]
class division_semiring (K : Type u) extends semiring K, div_inv_monoid K, nontrivial K :=
(mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : K)⁻¹ = 0)

section division_semiring

variables [division_semiring K] {a b : K}

/-- Every division semiring is a `group_with_zero`. -/
@[priority 100] -- see Note [lower instance priority]
instance division_semiring.to_group_with_zero :
  group_with_zero K :=
{ .. ‹division_semiring K› }

lemma inverse_eq_has_inv : (ring.inverse : K → K) = has_inv.inv :=
begin
  ext x,
  by_cases hx : x = 0,
  { simp [hx] },
  { exact (units.mk0 x hx).inverse_eq }
end

@[field_simps] lemma div_add_div_same (a b c : K) : a / c + b / c = (a + b) / c :=
by simpa only [div_eq_mul_inv] using (add_mul a b (c⁻¹)).symm

lemma same_add_div {a b : K} (h : b ≠ 0) : (b + a) / b = 1 + a / b :=
by simpa only [← @div_self _ _ b h] using (div_add_div_same b a b).symm

lemma one_add_div {a b : K} (h : b ≠ 0 ) : 1 + a / b = (b + a) / b := (same_add_div h).symm

lemma div_add_same {a b : K} (h : b ≠ 0) : (a + b) / b = a / b + 1 :=
by simpa only [← @div_self _ _ b h] using (div_add_div_same a b b).symm

lemma div_add_one {a b : K} (h : b ≠ 0) : a / b + 1 = (a + b) / b := (div_add_same h).symm

lemma add_div (a b c : K) : (a + b) / c = a / c + b / c :=
(div_add_div_same _ _ _).symm

lemma one_div_mul_add_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
  (1 / a) * (a + b) * (1 / b) = 1 / a + 1 / b :=
by rw [mul_add, one_div_mul_cancel ha, add_mul, one_mul, mul_assoc, mul_one_div_cancel hb, mul_one,
  add_comm]

lemma add_div_eq_mul_add_div (a b : K) {c : K} (hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
(eq_div_iff_mul_eq hc).2 $ by rw [right_distrib, (div_mul_cancel _ hc)]

@[field_simps] lemma add_div' (a b c : K) (hc : c ≠ 0) : b + a / c = (b * c + a) / c :=
by rw [add_div, mul_div_cancel _ hc]

@[field_simps] lemma div_add' (a b c : K) (hc : c ≠ 0) : a / c + b = (a + b * c) / c :=
by rwa [add_comm, add_div', add_comm]

end division_semiring

/-- A `division_ring` is a `ring` with multiplicative inverses for nonzero elements -/
@[protect_proj, ancestor ring div_inv_monoid nontrivial]
class division_ring (K : Type u) extends ring K, div_inv_monoid K, nontrivial K :=
(mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : K)⁻¹ = 0)

section division_ring
variables [division_ring K] {a b : K}

attribute [field_simps] inv_eq_one_div

@[priority 100] -- see Note [lower instance priority]
instance division_ring.to_division_semiring :
  division_semiring K :=
{ .. ‹division_ring K›, .. (infer_instance : semiring K) }

local attribute [simp]
  division_def mul_comm mul_assoc
  mul_left_comm mul_inv_cancel inv_mul_cancel

lemma one_div_neg_one_eq_neg_one : (1:K) / (-1) = -1 :=
have (-1) * (-1) = (1:K), by rw [neg_mul_neg, one_mul],
eq.symm (eq_one_div_of_mul_eq_one this)

lemma one_div_neg_eq_neg_one_div (a : K) : 1 / (- a) = - (1 / a) :=
calc
  1 / (- a) = 1 / ((-1) * a)        : by rw neg_eq_neg_one_mul
        ... = (1 / a) * (1 / (- 1)) : by rw one_div_mul_one_div_rev
        ... = (1 / a) * (-1)        : by rw one_div_neg_one_eq_neg_one
        ... = - (1 / a)             : by rw [mul_neg_eq_neg_mul_symm, mul_one]

lemma div_neg_eq_neg_div (a b : K) : b / (- a) = - (b / a) :=
calc
  b / (- a) = b * (1 / (- a)) : by rw [← inv_eq_one_div, division_def]
        ... = b * -(1 / a)    : by rw one_div_neg_eq_neg_one_div
        ... = -(b * (1 / a))  : by rw neg_mul_eq_mul_neg
        ... = - (b / a)       : by rw mul_one_div

lemma neg_div (a b : K) : (-b) / a = - (b / a) :=
by rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]

@[field_simps] lemma neg_div' {K : Type*} [division_ring K] (a b : K) : - (b / a) = (-b) / a :=
by simp [neg_div]

lemma neg_div_neg_eq (a b : K) : (-a) / (-b) = a / b :=
by rw [div_neg_eq_neg_div, neg_div, neg_neg]

lemma div_sub_div_same (a b c : K) : (a / c) - (b / c) = (a - b) / c :=
by rw [sub_eq_add_neg, ← neg_div, div_add_div_same, sub_eq_add_neg]

lemma same_sub_div {a b : K} (h : b ≠ 0) : (b - a) / b = 1 - a / b :=
by simpa only [← @div_self _ _ b h] using (div_sub_div_same b a b).symm

lemma one_sub_div {a b : K} (h : b ≠ 0) : 1 - a / b = (b - a) / b := (same_sub_div h).symm

lemma div_sub_same {a b : K} (h : b ≠ 0) : (a - b) / b = a / b - 1 :=
by simpa only [← @div_self _ _ b h] using (div_sub_div_same a b b).symm

lemma div_sub_one {a b : K} (h : b ≠ 0) : a / b - 1 = (a - b) / b := (div_sub_same h).symm

lemma neg_inv : - a⁻¹ = (- a)⁻¹ :=
by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

lemma sub_div (a b c : K) : (a - b) / c = a / c - b / c :=
(div_sub_div_same _ _ _).symm

lemma div_neg (a : K) : a / -b = -(a / b) :=
by rw [← div_neg_eq_neg_div]

lemma inv_neg : (-a)⁻¹ = -(a⁻¹) :=
by rw neg_inv

lemma one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
          (1 / a) * (b - a) * (1 / b) = 1 / a - 1 / b :=
by rw [(mul_sub_left_distrib (1 / a)), (one_div_mul_cancel ha), mul_sub_right_distrib,
       one_mul, mul_assoc, (mul_one_div_cancel hb), mul_one]

@[priority 100] -- see Note [lower instance priority]
instance division_ring.to_domain : domain K :=
{ ..‹division_ring K›, ..(by apply_instance : semiring K),
  ..(by apply_instance : no_zero_divisors K) }

end division_ring

/-- A `semifield` is a `comm_semiring` with multiplicative inverses for nonzero elements -/
@[protect_proj, ancestor comm_semiring division_semiring]
class semifield (K : Type u) extends comm_semiring K, division_semiring K

section semifield

variables [semifield K] {a b c d : K}

/-- Every semifield is a `comm_group_with_zero`. -/
@[priority 100] -- see Note [lower instance priority]
instance semifield.to_comm_group_with_zero : comm_group_with_zero K :=
{ .. ‹semifield K› }

lemma one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) :=
by rw [← one_div_mul_add_mul_one_div_eq_one_div_add_one_div ha hb, div_mul_comm', mul_one,
  div_mul_div, mul_one]

lemma div_add_div (a c : K) (hb : b ≠ 0) (hd : d ≠ 0) :
  (a / b) + (c / d) = ((a * d) + (b * c)) / (b * d) :=
by rw [← mul_div_mul_right _ b hd, ← mul_div_mul_left c d hb, div_add_div_same]

lemma inv_add_inv {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) :=
by rw [inv_eq_one_div, inv_eq_one_div, one_div_add_one_div ha hb]

end semifield

/-- A `field` is a `comm_ring` with multiplicative inverses for nonzero elements -/
@[protect_proj, ancestor comm_ring division_ring]
class field (K : Type u) extends comm_ring K, division_ring K

section field

variable [field K]

@[priority 100] -- see Note [lower instance priority]
instance field.to_semifield : semifield K :=
{ .. ‹field K›, .. (infer_instance : semiring K) }

local attribute [simp] mul_assoc mul_comm mul_left_comm

@[field_simps] lemma div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
  (a / b) - (c / d) = ((a * d) - (b * c)) / (b * d) :=
begin
  simp [sub_eq_add_neg],
  rw [neg_eq_neg_one_mul, ← mul_div_assoc, div_add_div _ _ hb hd,
      ← mul_assoc, mul_comm b, mul_assoc, ← neg_eq_neg_one_mul]
end

lemma inv_sub_inv {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = (b - a) / (a * b) :=
by rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ ha hb, one_mul, mul_one]

@[field_simps] lemma sub_div' (a b c : K) (hc : c ≠ 0) : b - a / c = (b * c - a) / c :=
by simpa using div_sub_div b a one_ne_zero hc

@[field_simps] lemma div_sub' (a b c : K) (hc : c ≠ 0) : a / c - b = (a - c * b) / c :=
by simpa using div_sub_div a b hc one_ne_zero

@[priority 100] -- see Note [lower instance priority]
instance field.to_integral_domain : integral_domain K :=
{ ..‹field K›, ..division_ring.to_domain }

end field

section is_field

/-- A predicate to express that a ring is a field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms.
Additionaly, this is useful when trying to prove that
a particular ring structure extends to a field. -/
structure is_field (R : Type u) [ring R] : Prop :=
(exists_pair_ne : ∃ (x y : R), x ≠ y)
(mul_comm : ∀ (x y : R), x * y = y * x)
(mul_inv_cancel : ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1)

/-- Transferring from field to is_field -/
lemma field.to_is_field (R : Type u) [field R] : is_field R :=
{ mul_inv_cancel := λ a ha, ⟨a⁻¹, field.mul_inv_cancel ha⟩,
  ..‹field R› }

open_locale classical

/-- Transferring from is_field to field -/
noncomputable def is_field.to_field (R : Type u) [ring R] (h : is_field R) : field R :=
{ inv := λ a, if ha : a = 0 then 0 else classical.some (is_field.mul_inv_cancel h ha),
  inv_zero := dif_pos rfl,
  mul_inv_cancel := λ a ha,
    begin
      convert classical.some_spec (is_field.mul_inv_cancel h ha),
      exact dif_neg ha
    end,
  .. ‹ring R›, ..h }

/-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `is_field` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
lemma uniq_inv_of_is_field (R : Type u) [ring R] (hf : is_field R) :
  ∀ (x : R), x ≠ 0 → ∃! (y : R), x * y = 1 :=
begin
  intros x hx,
  apply exists_unique_of_exists_of_unique,
  { exact hf.mul_inv_cancel hx },
  { intros y z hxy hxz,
    calc y = y * (x * z) : by rw [hxz, mul_one]
       ... = (x * y) * z : by rw [← mul_assoc, hf.mul_comm y x]
       ... = z           : by rw [hxy, one_mul] }
end

end is_field

namespace ring_hom

section

variables {R : Type*} [semiring R] [division_semiring K] (f : R →+* K)

@[simp] lemma map_units_inv (u : units R) :
  f ↑u⁻¹ = (f ↑u)⁻¹ :=
(f : R →* K).map_units_inv u

end

section

variables {R K' : Type*} [division_semiring K] [semiring R] [nontrivial R]
  [division_semiring K'] (f : K →+* R) (g : K →+* K') {x y : K}

lemma map_ne_zero : f x ≠ 0 ↔ x ≠ 0 := f.to_monoid_with_zero_hom.map_ne_zero

@[simp] lemma map_eq_zero : f x = 0 ↔ x = 0 := f.to_monoid_with_zero_hom.map_eq_zero

variables (x y)

lemma map_inv : g x⁻¹ = (g x)⁻¹ := g.to_monoid_with_zero_hom.map_inv' x

lemma map_div : g (x / y) = g x / g y := g.to_monoid_with_zero_hom.map_div x y

end

protected lemma injective {R} [division_ring K] [semiring R] [nontrivial R] (f : K →+* R) :
  function.injective f := f.injective_iff.2 $ λ x, f.map_eq_zero.1

end ring_hom

section noncomputable_defs

variables {R : Type*} [nontrivial R]

/-- Constructs a `division_ring` structure on a `ring` consisting only of units and 0. -/
noncomputable def division_ring_of_is_unit_or_eq_zero [hR : ring R]
  (h : ∀ (a : R), is_unit a ∨ a = 0) : division_ring R :=
{ .. (group_with_zero_of_is_unit_or_eq_zero h), .. hR }

/-- Constructs a `field` structure on a `comm_ring` consisting only of units and 0. -/
noncomputable def field_of_is_unit_or_eq_zero [hR : comm_ring R]
  (h : ∀ (a : R), is_unit a ∨ a = 0) : field R :=
{ .. (group_with_zero_of_is_unit_or_eq_zero h), .. hR }

end noncomputable_defs
