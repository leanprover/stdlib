/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.ordered_monoid

/-!
# Ordered groups

This file develops the basics of ordered groups.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/

set_option old_structure_cmd true

universe u
variable {α : Type u}

@[to_additive]
instance group.covariant_class_le.to_contravariant_class_le
  [group α] [has_le α] [covariant_class α α (*) (≤)] : contravariant_class α α (*) (≤) :=
{ elim := λ a b c bc, calc  b = a⁻¹ * (a * b) : eq_inv_mul_of_mul_eq rfl
                          ... ≤ a⁻¹ * (a * c) : mul_le_mul_left' bc a⁻¹
                          ... = c             : inv_mul_cancel_left a c }

@[to_additive]
instance group.swap.covariant_class_le.to_contravariant_class_le [group α] [has_le α]
  [covariant_class α α (function.swap (*)) (≤)] : contravariant_class α α (function.swap (*)) (≤) :=
{ elim := λ a b c bc, calc  b = b * a * a⁻¹ : eq_mul_inv_of_mul_eq rfl
                          ... ≤ c * a * a⁻¹ : mul_le_mul_right' bc a⁻¹
                          ... = c           : mul_inv_eq_of_eq_mul rfl }

@[to_additive]
instance group.covariant_class_lt.to_contravariant_class_lt
  [group α] [has_lt α] [covariant_class α α (*) (<)] : contravariant_class α α (*) (<) :=
{ elim := λ a b c bc, calc  b = a⁻¹ * (a * b) : eq_inv_mul_of_mul_eq rfl
                          ... < a⁻¹ * (a * c) : mul_lt_mul_left' bc a⁻¹
                          ... = c             : inv_mul_cancel_left a c }

@[to_additive]
instance group.swap.covariant_class_lt.to_contravariant_class_lt [group α] [has_lt α]
  [covariant_class α α (function.swap (*)) (<)] : contravariant_class α α (function.swap (*)) (<) :=
{ elim := λ a b c bc, calc  b = b * a * a⁻¹ : eq_mul_inv_of_mul_eq rfl
                          ... < c * a * a⁻¹ : mul_lt_mul_right' bc a⁻¹
                          ... = c           : mul_inv_eq_of_eq_mul rfl }

/-- An ordered additive commutative group is an additive commutative group
with a partial order in which addition is strictly monotone. -/
@[protect_proj, ancestor add_comm_group partial_order]
class ordered_add_comm_group (α : Type u) extends add_comm_group α, partial_order α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)

/-- An ordered commutative group is an commutative group
with a partial order in which multiplication is strictly monotone. -/
@[protect_proj, ancestor comm_group partial_order]
class ordered_comm_group (α : Type u) extends comm_group α, partial_order α :=
(mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)

attribute [to_additive] ordered_comm_group

@[to_additive]
instance units.covariant_class [ordered_comm_monoid α] :
  covariant_class (units α) (units α) (*) (≤) :=
{ elim := λ a b c bc, show (a : α) * b ≤ a * c, from mul_le_mul_left' bc _ }

@[to_additive]
instance ordered_comm_group.to_covariant_class_left_le (α : Type u) [ordered_comm_group α] :
  covariant_class α α (*) (≤) :=
{ elim := λ a b c bc, ordered_comm_group.mul_le_mul_left b c bc a }

/--The units of an ordered commutative monoid form an ordered commutative group. -/
@[to_additive]
instance units.ordered_comm_group [ordered_comm_monoid α] : ordered_comm_group (units α) :=
{ mul_le_mul_left := λ a b h c, (mul_le_mul_left' (h : (a : α) ≤ b) _ :  (c : α) * a ≤ c * b),
  .. units.partial_order,
  .. (infer_instance : comm_group (units α)) }

section ordered_comm_group
variables [ordered_comm_group α] {a b c d : α}

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance ordered_comm_group.to_ordered_cancel_comm_monoid (α : Type u)
  [s : ordered_comm_group α] :
  ordered_cancel_comm_monoid α :=
{ mul_left_cancel       := λ a b c, (mul_right_inj a).mp,
  le_of_mul_le_mul_left := λ a b c, (mul_le_mul_iff_left a).mp,
  ..s }

@[priority 100, to_additive]
instance ordered_comm_group.has_exists_mul_of_le (α : Type u)
  [ordered_comm_group α] :
  has_exists_mul_of_le α :=
⟨λ a b hab, ⟨b * a⁻¹, (mul_inv_cancel_comm_assoc a b).symm⟩⟩

@[to_additive neg_le_neg]
lemma inv_le_inv' (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
have 1 ≤ a⁻¹ * b,           from mul_left_inv a ▸ mul_le_mul_left' h _,
have 1 * b⁻¹ ≤ a⁻¹ * b * b⁻¹, from mul_le_mul_right' this _,
by rwa [mul_inv_cancel_right, one_mul] at this

@[to_additive]
lemma le_of_inv_le_inv (h : b⁻¹ ≤ a⁻¹) : a ≤ b :=
suffices (a⁻¹)⁻¹ ≤ (b⁻¹)⁻¹, from
  begin simp [inv_inv] at this, assumption end,
inv_le_inv' h

@[to_additive]
lemma one_le_of_inv_le_one (h : a⁻¹ ≤ 1) : 1 ≤ a :=
have a⁻¹ ≤ 1⁻¹, by rwa one_inv,
le_of_inv_le_inv this

@[to_additive]
lemma inv_le_one_of_one_le (h : 1 ≤ a) : a⁻¹ ≤ 1 :=
have a⁻¹ ≤ 1⁻¹, from inv_le_inv' h,
by rwa one_inv at this

@[to_additive nonpos_of_neg_nonneg]
lemma le_one_of_one_le_inv (h : 1 ≤ a⁻¹) : a ≤ 1 :=
have 1⁻¹ ≤ a⁻¹, by rwa one_inv,
le_of_inv_le_inv this

@[to_additive neg_nonneg_of_nonpos]
lemma one_le_inv_of_le_one (h : a ≤ 1) : 1 ≤ a⁻¹ :=
have 1⁻¹ ≤ a⁻¹, from inv_le_inv' h,
by rwa one_inv at this

@[to_additive neg_lt_neg]
lemma inv_lt_inv' (h : a < b) : b⁻¹ < a⁻¹ :=
have 1 < a⁻¹ * b, from mul_left_inv a ▸ mul_lt_mul_left' h (a⁻¹),
have 1 * b⁻¹ < a⁻¹ * b * b⁻¹, from mul_lt_mul_right' this (b⁻¹),
by rwa [mul_inv_cancel_right, one_mul] at this

@[to_additive]
lemma lt_of_inv_lt_inv (h : b⁻¹ < a⁻¹) : a < b :=
inv_inv a ▸ inv_inv b ▸ inv_lt_inv' h

@[to_additive]
lemma one_lt_of_inv_inv (h : a⁻¹ < 1) : 1 < a :=
have a⁻¹ < 1⁻¹, by rwa one_inv,
lt_of_inv_lt_inv this

@[to_additive]
lemma inv_inv_of_one_lt (h : 1 < a) : a⁻¹ < 1 :=
have a⁻¹ < 1⁻¹, from inv_lt_inv' h,
by rwa one_inv at this

@[to_additive neg_of_neg_pos]
lemma inv_of_one_lt_inv (h : 1 < a⁻¹) : a < 1 :=
have 1⁻¹ < a⁻¹, by rwa one_inv,
lt_of_inv_lt_inv this

@[to_additive neg_pos_of_neg]
lemma one_lt_inv_of_inv (h : a < 1) : 1 < a⁻¹ :=
have 1⁻¹ < a⁻¹, from inv_lt_inv' h,
by rwa one_inv at this

@[to_additive]
lemma le_inv_of_le_inv (h : a ≤ b⁻¹) : b ≤ a⁻¹ :=
begin
  have h := inv_le_inv' h,
  rwa inv_inv at h
end

@[to_additive]
lemma inv_le_of_inv_le (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
begin
  have h := inv_le_inv' h,
  rwa inv_inv at h
end

@[to_additive]
lemma lt_inv_of_lt_inv (h : a < b⁻¹) : b < a⁻¹ :=
begin
  have h := inv_lt_inv' h,
  rwa inv_inv at h
end

@[to_additive]
lemma inv_lt_of_inv_lt (h : a⁻¹ < b) : b⁻¹ < a :=
begin
  have h := inv_lt_inv' h,
  rwa inv_inv at h
end

@[to_additive]
lemma mul_le_of_le_inv_mul (h : b ≤ a⁻¹ * c) : a * b ≤ c :=
begin
  have h := mul_le_mul_left' h a,
  rwa mul_inv_cancel_left at h
end

@[to_additive]
lemma le_inv_mul_of_mul_le (h : a * b ≤ c) : b ≤ a⁻¹ * c :=
begin
  have h := mul_le_mul_left' h a⁻¹,
  rwa inv_mul_cancel_left at h
end

@[to_additive]
lemma le_mul_of_inv_mul_le (h : b⁻¹ * a ≤ c) : a ≤ b * c :=
begin
  have h := mul_le_mul_left' h b,
  rwa mul_inv_cancel_left at h
end

@[to_additive]
lemma inv_mul_le_of_le_mul (h : a ≤ b * c) : b⁻¹ * a ≤ c :=
begin
  have h := mul_le_mul_left' h b⁻¹,
  rwa inv_mul_cancel_left at h
end

@[to_additive]
lemma le_mul_of_inv_mul_le_left (h : b⁻¹ * a ≤ c) : a ≤ b * c :=
le_mul_of_inv_mul_le h

@[to_additive]
lemma inv_mul_le_left_of_le_mul (h : a ≤ b * c) : b⁻¹ * a ≤ c :=
inv_mul_le_of_le_mul h

@[to_additive]
lemma le_mul_of_inv_mul_le_right (h : c⁻¹ * a ≤ b) : a ≤ b * c :=
by { rw mul_comm, exact le_mul_of_inv_mul_le h }

@[to_additive]
lemma inv_mul_le_right_of_le_mul (h : a ≤ b * c) : c⁻¹ * a ≤ b :=
by { rw mul_comm at h, apply inv_mul_le_left_of_le_mul h }

@[to_additive]
lemma mul_lt_of_lt_inv_mul (h : b < a⁻¹ * c) : a * b < c :=
begin
  have h := mul_lt_mul_left' h a,
  rwa mul_inv_cancel_left at h
end

@[to_additive]
lemma lt_inv_mul_of_mul_lt (h : a * b < c) : b < a⁻¹ * c :=
begin
  have h := mul_lt_mul_left' h (a⁻¹),
  rwa inv_mul_cancel_left at h
end

@[to_additive]
lemma lt_mul_of_inv_mul_lt (h : b⁻¹ * a < c) : a < b * c :=
begin
  have h := mul_lt_mul_left' h b,
  rwa mul_inv_cancel_left at h
end

@[to_additive]
lemma inv_mul_lt_of_lt_mul (h : a < b * c) : b⁻¹ * a < c :=
begin
  have h := mul_lt_mul_left' h (b⁻¹),
  rwa inv_mul_cancel_left at h
end

@[to_additive]
lemma lt_mul_of_inv_mul_lt_left (h : b⁻¹ * a < c) : a < b * c :=
lt_mul_of_inv_mul_lt h

@[to_additive]
lemma inv_mul_lt_left_of_lt_mul (h : a < b * c) : b⁻¹ * a < c :=
inv_mul_lt_of_lt_mul h

@[to_additive]
lemma lt_mul_of_inv_mul_lt_right (h : c⁻¹ * a < b) : a < b * c :=
by { rw mul_comm, exact lt_mul_of_inv_mul_lt h }

@[to_additive]
lemma inv_mul_lt_right_of_lt_mul (h : a < b * c) : c⁻¹ * a < b :=
by { rw mul_comm at h, exact inv_mul_lt_of_lt_mul h }

@[simp, to_additive]
lemma inv_lt_one_iff_one_lt : a⁻¹ < 1 ↔ 1 < a :=
⟨ one_lt_of_inv_inv, inv_inv_of_one_lt ⟩

@[simp, to_additive]
lemma inv_le_inv_iff : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
have a * b * a⁻¹ ≤ a * b * b⁻¹ ↔ a⁻¹ ≤ b⁻¹, from mul_le_mul_iff_left _,
by { rw [mul_inv_cancel_right, mul_comm a, mul_inv_cancel_right] at this, rw [this] }

@[to_additive neg_le]
lemma inv_le' : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
have a⁻¹ ≤ (b⁻¹)⁻¹ ↔ b⁻¹ ≤ a, from inv_le_inv_iff,
by rwa inv_inv at this

@[to_additive le_neg]
lemma le_inv' : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
have (a⁻¹)⁻¹ ≤ b⁻¹ ↔ b ≤ a⁻¹, from inv_le_inv_iff,
by rwa inv_inv at this

@[to_additive neg_le_iff_add_nonneg]
lemma inv_le_iff_one_le_mul : a⁻¹ ≤ b ↔ 1 ≤ b * a :=
(mul_le_mul_iff_right a).symm.trans $ by rw inv_mul_self

@[to_additive neg_le_iff_add_nonneg']
lemma inv_le_iff_one_le_mul' : a⁻¹ ≤ b ↔ 1 ≤ a * b :=
(mul_le_mul_iff_left a).symm.trans $ by rw mul_inv_self

@[to_additive]
lemma inv_lt_iff_one_lt_mul : a⁻¹ < b ↔ 1 < b * a :=
(mul_lt_mul_iff_right a).symm.trans $ by rw inv_mul_self

@[to_additive]
lemma inv_lt_iff_one_lt_mul' : a⁻¹ < b ↔ 1 < a * b :=
(mul_lt_mul_iff_left a).symm.trans $ by rw mul_inv_self

@[to_additive]
lemma le_inv_iff_mul_le_one : a ≤ b⁻¹ ↔ a * b ≤ 1 :=
(mul_le_mul_iff_right b).symm.trans $ by rw inv_mul_self

@[to_additive]
lemma le_inv_iff_mul_le_one' : a ≤ b⁻¹ ↔ b * a ≤ 1 :=
(mul_le_mul_iff_left b).symm.trans $ by rw mul_inv_self

@[to_additive]
lemma lt_inv_iff_mul_lt_one : a < b⁻¹ ↔ a * b < 1 :=
(mul_lt_mul_iff_right b).symm.trans $ by rw inv_mul_self

@[to_additive]
lemma lt_inv_iff_mul_lt_one' : a < b⁻¹ ↔ b * a < 1 :=
(mul_lt_mul_iff_left b).symm.trans $ by rw mul_inv_self

@[simp, to_additive neg_nonpos]
lemma inv_le_one' : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
have a⁻¹ ≤ 1⁻¹ ↔ 1 ≤ a, from inv_le_inv_iff,
by rwa one_inv at this

@[simp, to_additive neg_nonneg]
lemma one_le_inv' : 1 ≤ a⁻¹ ↔ a ≤ 1 :=
have 1⁻¹ ≤ a⁻¹ ↔ a ≤ 1, from inv_le_inv_iff,
by rwa one_inv at this

@[to_additive]
lemma inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
le_trans (inv_le_one'.2 h) h

@[to_additive]
lemma self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
le_trans h (one_le_inv'.2 h)

@[simp, to_additive]
lemma inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a :=
have a * b * a⁻¹ < a * b * b⁻¹ ↔ a⁻¹ < b⁻¹, from mul_lt_mul_iff_left _,
by { rw [mul_inv_cancel_right, mul_comm a, mul_inv_cancel_right] at this, rw [this] }

@[to_additive neg_lt_zero]
lemma inv_lt_one' : a⁻¹ < 1 ↔ 1 < a :=
have a⁻¹ < 1⁻¹ ↔ 1 < a, from inv_lt_inv_iff,
by rwa one_inv at this

@[to_additive neg_pos]
lemma one_lt_inv' : 1 < a⁻¹ ↔ a < 1 :=
have 1⁻¹ < a⁻¹ ↔ a < 1, from inv_lt_inv_iff,
by rwa one_inv at this

@[to_additive neg_lt]
lemma inv_lt' : a⁻¹ < b ↔ b⁻¹ < a :=
have a⁻¹ < (b⁻¹)⁻¹ ↔ b⁻¹ < a, from inv_lt_inv_iff,
by rwa inv_inv at this

@[to_additive lt_neg]
lemma lt_inv' : a < b⁻¹ ↔ b < a⁻¹ :=
have (a⁻¹)⁻¹ < b⁻¹ ↔ b < a⁻¹, from inv_lt_inv_iff,
by rwa inv_inv at this

@[to_additive]
lemma inv_lt_self (h : 1 < a) : a⁻¹ < a :=
(inv_lt_one'.2 h).trans h

@[to_additive]
lemma le_inv_mul_iff_mul_le : b ≤ a⁻¹ * c ↔ a * b ≤ c :=
have a⁻¹ * (a * b) ≤ a⁻¹ * c ↔ a * b ≤ c, from mul_le_mul_iff_left _,
by rwa inv_mul_cancel_left at this

@[simp, to_additive]
lemma inv_mul_le_iff_le_mul : b⁻¹ * a ≤ c ↔ a ≤ b * c :=
have b⁻¹ * a ≤ b⁻¹ * (b * c) ↔ a ≤ b * c, from mul_le_mul_iff_left _,
by rwa inv_mul_cancel_left at this

@[to_additive]
lemma mul_inv_le_iff_le_mul : a * c⁻¹ ≤ b ↔ a ≤ b * c :=
by rw [mul_comm a, mul_comm b, inv_mul_le_iff_le_mul]

@[simp, to_additive]
lemma mul_inv_le_iff_le_mul' : a * b⁻¹ ≤ c ↔ a ≤ b * c :=
by rw [← inv_mul_le_iff_le_mul, mul_comm]

@[to_additive]
lemma inv_mul_le_iff_le_mul' : c⁻¹ * a ≤ b ↔ a ≤ b * c :=
by rw [inv_mul_le_iff_le_mul, mul_comm]

@[simp, to_additive]
lemma lt_inv_mul_iff_mul_lt : b < a⁻¹ * c ↔ a * b < c :=
have a⁻¹ * (a * b) < a⁻¹ * c ↔ a * b < c, from mul_lt_mul_iff_left _,
by rwa inv_mul_cancel_left at this

@[simp, to_additive]
lemma inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c :=
have b⁻¹ * a < b⁻¹ * (b * c) ↔ a < b * c, from mul_lt_mul_iff_left _,
by rwa inv_mul_cancel_left at this

@[to_additive]
lemma inv_mul_lt_iff_lt_mul_right : c⁻¹ * a < b ↔ a < b * c :=
by rw [inv_mul_lt_iff_lt_mul, mul_comm]

@[to_additive add_neg_le_add_neg_iff]
lemma mul_inv_le_mul_inv_iff' : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
begin
  split; intro h; have := λ x y, mul_le_mul_right' (mul_le_mul_right' h x) y,
  { simpa [mul_assoc] using this b d },
  { simpa [mul_assoc] using this d⁻¹ b⁻¹ },
end

@[to_additive add_neg_lt_add_neg_iff]
lemma div_lt_div_iff' : a * b⁻¹ < c * d⁻¹ ↔ a * d < c * b :=
begin
  split; intro h; have := λ x y, mul_lt_mul_right' (mul_lt_mul_right' h x) y,
  { simpa [mul_assoc] using this b d },
  { simpa [mul_assoc] using this d⁻¹ b⁻¹ },
end

@[to_additive add_neg_le_add_neg_left]
lemma div_le_div_left' : a * b⁻¹ ≤ a * c⁻¹ ↔ c ≤ b :=
div_le_div_iff'.trans $ mul_le_mul_iff_left a

@[to_additive add_neg_le_add_neg_right]
lemma div_le_div_right' : a * b⁻¹ ≤ c * b⁻¹ ↔ a ≤ c :=
div_le_div_iff'.trans $ mul_le_mul_iff_right b

@[to_additive add_neg_lt_add_neg_left]
lemma div_lt_div_left' : a * b⁻¹ < a * c⁻¹ ↔ c < b :=
div_lt_div_iff'.trans $ mul_lt_mul_iff_left a

@[to_additive add_neg_lt_add_neg_right]
lemma div_lt_div_right' : a * b⁻¹ < c * b⁻¹ ↔ a < c :=
div_lt_div_iff'.trans $ mul_lt_mul_iff_right b

@[simp, to_additive sub_le_self_iff]
lemma div_le_self_iff' (a : α) {b : α} : a / b ≤ a ↔ 1 ≤ b :=
by simp [div_eq_mul_inv]

@[simp, to_additive sub_lt_self_iff]
lemma div_lt_self_iff' (a : α) {b : α} : a / b < a ↔ 1 < b :=
by simp [div_eq_mul_inv]

/-- Pullback an `ordered_comm_group` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.ordered_add_comm_group
"Pullback an `ordered_add_comm_group` under an injective map."]
def function.injective.ordered_comm_group {β : Type*}
  [has_one β] [has_mul β] [has_inv β] [has_div β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) :
  ordered_comm_group β :=
{ ..partial_order.lift f hf,
  ..hf.ordered_comm_monoid f one mul,
  ..hf.comm_group f one mul inv div }

end ordered_comm_group

section ordered_add_comm_group
variables [ordered_add_comm_group α] {a b c d : α}

lemma sub_le_sub (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
by simpa only [sub_eq_add_neg] using add_le_add hab (neg_le_neg hcd)

lemma sub_lt_sub (hab : a < b) (hcd : c < d) : a - d < b - c :=
by simpa only [sub_eq_add_neg] using add_lt_add hab (neg_lt_neg hcd)

alias sub_le_self_iff ↔ _ sub_le_self

alias sub_lt_self_iff ↔ _ sub_lt_self

lemma sub_le_sub_iff : a - b ≤ c - d ↔ a + d ≤ c + b :=
by simpa only [sub_eq_add_neg] using add_neg_le_add_neg_iff

lemma sub_lt_sub_iff : a - b < c - d ↔ a + d < c + b :=
by simpa only [sub_eq_add_neg] using add_neg_lt_add_neg_iff

@[simp]
lemma sub_le_sub_iff_left (a : α) {b c : α} : a - b ≤ a - c ↔ c ≤ b :=
by simpa only [sub_eq_add_neg] using add_neg_le_add_neg_left

lemma sub_le_sub_left (h : a ≤ b) (c : α) : c - b ≤ c - a :=
(sub_le_sub_iff_left c).2 h

@[simp]
lemma sub_le_sub_iff_right (c : α) : a - c ≤ b - c ↔ a ≤ b :=
by simpa only [sub_eq_add_neg] using add_neg_le_add_neg_right

lemma sub_le_sub_right (h : a ≤ b) (c : α) : a - c ≤ b - c :=
(sub_le_sub_iff_right c).2 h

@[simp]
lemma sub_lt_sub_iff_left (a : α) {b c : α} : a - b < a - c ↔ c < b :=
by simpa only [sub_eq_add_neg] using add_neg_lt_add_neg_left

lemma sub_lt_sub_left (h : a < b) (c : α) : c - b < c - a :=
(sub_lt_sub_iff_left c).2 h

@[simp]
lemma sub_lt_sub_iff_right (c : α) : a - c < b - c ↔ a < b :=
by simpa only [sub_eq_add_neg] using add_neg_lt_add_neg_right

lemma sub_lt_sub_right (h : a < b) (c : α) : a - c < b - c :=
(sub_lt_sub_iff_right c).2 h

@[simp] lemma sub_nonneg : 0 ≤ a - b ↔ b ≤ a :=
by rw [← sub_self a, sub_le_sub_iff_left]

alias sub_nonneg ↔ le_of_sub_nonneg sub_nonneg_of_le

@[simp] lemma sub_nonpos : a - b ≤ 0 ↔ a ≤ b :=
by rw [← sub_self b,  sub_le_sub_iff_right]

alias sub_nonpos ↔ le_of_sub_nonpos sub_nonpos_of_le

@[simp] lemma sub_pos : 0 < a - b ↔ b < a :=
by rw [← sub_self a, sub_lt_sub_iff_left]

alias sub_pos ↔ lt_of_sub_pos sub_pos_of_lt

@[simp] lemma sub_lt_zero : a - b < 0 ↔ a < b :=
by rw [← sub_self b, sub_lt_sub_iff_right]

alias sub_lt_zero ↔ lt_of_sub_neg sub_neg_of_lt

lemma le_sub_iff_add_le' : b ≤ c - a ↔ a + b ≤ c :=
by rw [sub_eq_add_neg, add_comm, le_neg_add_iff_add_le]

lemma le_sub_iff_add_le : a ≤ c - b ↔ a + b ≤ c :=
by rw [le_sub_iff_add_le', add_comm]

alias le_sub_iff_add_le ↔ add_le_of_le_sub_right le_sub_right_of_add_le

lemma sub_le_iff_le_add' : a - b ≤ c ↔ a ≤ b + c :=
by rw [sub_eq_add_neg, add_comm, neg_add_le_iff_le_add]

alias le_sub_iff_add_le' ↔ add_le_of_le_sub_left le_sub_left_of_add_le

lemma sub_le_iff_le_add : a - c ≤ b ↔ a ≤ b + c :=
by rw [sub_le_iff_le_add', add_comm]

@[simp] lemma neg_le_sub_iff_le_add : -b ≤ a - c ↔ c ≤ a + b :=
le_sub_iff_add_le.trans neg_add_le_iff_le_add'

lemma neg_le_sub_iff_le_add' : -a ≤ b - c ↔ c ≤ a + b :=
by rw [neg_le_sub_iff_le_add, add_comm]

lemma sub_le : a - b ≤ c ↔ a - c ≤ b :=
sub_le_iff_le_add'.trans sub_le_iff_le_add.symm

theorem le_sub : a ≤ b - c ↔ c ≤ b - a :=
le_sub_iff_add_le'.trans le_sub_iff_add_le.symm

lemma lt_sub_iff_add_lt' : b < c - a ↔ a + b < c :=
by rw [sub_eq_add_neg, add_comm, lt_neg_add_iff_add_lt]

alias lt_sub_iff_add_lt' ↔ add_lt_of_lt_sub_left lt_sub_left_of_add_lt

lemma lt_sub_iff_add_lt : a < c - b ↔ a + b < c :=
by rw [lt_sub_iff_add_lt', add_comm]

alias lt_sub_iff_add_lt ↔ add_lt_of_lt_sub_right lt_sub_right_of_add_lt

lemma sub_lt_iff_lt_add' : a - b < c ↔ a < b + c :=
by rw [sub_eq_add_neg, add_comm, neg_add_lt_iff_lt_add]

alias sub_lt_iff_lt_add' ↔ lt_add_of_sub_left_lt sub_left_lt_of_lt_add

lemma sub_lt_iff_lt_add : a - c < b ↔ a < b + c :=
by rw [sub_lt_iff_lt_add', add_comm]

alias sub_lt_iff_lt_add ↔ lt_add_of_sub_right_lt sub_right_lt_of_lt_add

@[simp] lemma neg_lt_sub_iff_lt_add : -b < a - c ↔ c < a + b :=
lt_sub_iff_add_lt.trans neg_add_lt_iff_lt_add_right

lemma neg_lt_sub_iff_lt_add' : -a < b - c ↔ c < a + b :=
by rw [neg_lt_sub_iff_lt_add, add_comm]

lemma sub_lt : a - b < c ↔ a - c < b :=
sub_lt_iff_lt_add'.trans sub_lt_iff_lt_add.symm

theorem lt_sub : a < b - c ↔ c < b - a :=
lt_sub_iff_add_lt'.trans lt_sub_iff_add_lt.symm

end ordered_add_comm_group

/-!

### Linearly ordered commutative groups

-/

/-- A linearly ordered additive commutative group is an
additive commutative group with a linear order in which
addition is monotone. -/
@[protect_proj, ancestor ordered_add_comm_group linear_order]
class linear_ordered_add_comm_group (α : Type u) extends ordered_add_comm_group α, linear_order α

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.` -/
@[protect_proj, ancestor linear_ordered_add_comm_monoid_with_top sub_neg_monoid nontrivial]
class linear_ordered_add_comm_group_with_top (α : Type*)
  extends linear_ordered_add_comm_monoid_with_top α, sub_neg_monoid α, nontrivial α :=
(neg_top : - (⊤ : α) = ⊤)
(add_neg_cancel : ∀ a:α, a ≠ ⊤ → a + (- a) = 0)

/-- A linearly ordered commutative group is a
commutative group with a linear order in which
multiplication is monotone. -/
@[protect_proj, ancestor ordered_comm_group linear_order, to_additive]
class linear_ordered_comm_group (α : Type u) extends ordered_comm_group α, linear_order α

section linear_ordered_comm_group
variables [linear_ordered_comm_group α] {a b c : α}

@[priority 100, to_additive] -- see Note [lower instance priority]
instance linear_ordered_comm_group.to_linear_ordered_cancel_comm_monoid :
  linear_ordered_cancel_comm_monoid α :=
{ le_of_mul_le_mul_left := λ x y z, le_of_mul_le_mul_left',
  mul_left_cancel := λ x y z, mul_left_cancel,
  ..‹linear_ordered_comm_group α› }

/-- Pullback a `linear_ordered_comm_group` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.linear_ordered_add_comm_group
"Pullback a `linear_ordered_add_comm_group` under an injective map."]
def function.injective.linear_ordered_comm_group {β : Type*}
  [has_one β] [has_mul β] [has_inv β] [has_div β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y)  :
  linear_ordered_comm_group β :=
{ ..linear_order.lift f hf,
  ..hf.ordered_comm_group f one mul inv div }

@[to_additive linear_ordered_add_comm_group.add_lt_add_left]
lemma linear_ordered_comm_group.mul_lt_mul_left'
  (a b : α) (h : a < b) (c : α) : c * a < c * b :=
mul_lt_mul_left' h c

@[to_additive min_neg_neg]
lemma min_inv_inv' (a b : α) : min (a⁻¹) (b⁻¹) = (max a b)⁻¹ :=
eq.symm $ @monotone.map_max α (order_dual α) _ _ has_inv.inv a b $ λ a b, inv_le_inv'

@[to_additive max_neg_neg]
lemma max_inv_inv' (a b : α) : max (a⁻¹) (b⁻¹) = (min a b)⁻¹ :=
eq.symm $ @monotone.map_min α (order_dual α) _ _ has_inv.inv a b $ λ a b, inv_le_inv'

@[to_additive min_sub_sub_right]
lemma min_div_div_right' (a b c : α) : min (a / c) (b / c) = min a b / c :=
by simpa only [div_eq_mul_inv] using min_mul_mul_right a b (c⁻¹)

@[to_additive max_sub_sub_right]
lemma max_div_div_right' (a b c : α) : max (a / c) (b / c) = max a b / c :=
by simpa only [div_eq_mul_inv] using max_mul_mul_right a b (c⁻¹)

@[to_additive min_sub_sub_left]
lemma min_div_div_left' (a b c : α) : min (a / b) (a / c) = a / max b c :=
by simp only [div_eq_mul_inv, min_mul_mul_left, min_inv_inv']

@[to_additive max_sub_sub_left]
lemma max_div_div_left' (a b c : α) : max (a / b) (a / c) = a / min b c :=
by simp only [div_eq_mul_inv, max_mul_mul_left, max_inv_inv']

@[to_additive max_zero_sub_eq_self]
lemma max_one_div_eq_self' (a : α) : max a 1 / max (a⁻¹) 1 = a :=
begin
  rcases le_total a 1,
  { rw [max_eq_right h, max_eq_left, one_div, inv_inv], { rwa [le_inv', one_inv] } },
  { rw [max_eq_left, max_eq_right, div_eq_mul_inv, one_inv, mul_one],
    { rwa [inv_le', one_inv] }, exact h }
end

@[to_additive eq_zero_of_neg_eq]
lemma eq_one_of_inv_eq' (h : a⁻¹ = a) : a = 1 :=
match lt_trichotomy a 1 with
| or.inl h₁ :=
  have 1 < a, from h ▸ one_lt_inv_of_inv h₁,
  absurd h₁ this.asymm
| or.inr (or.inl h₁) := h₁
| or.inr (or.inr h₁) :=
  have a < 1, from h ▸ inv_inv_of_one_lt h₁,
  absurd h₁ this.asymm
end

@[to_additive exists_zero_lt]
lemma exists_one_lt' [nontrivial α] : ∃ (a:α), 1 < a :=
begin
  obtain ⟨y, hy⟩ := decidable.exists_ne (1 : α),
  cases hy.lt_or_lt,
  { exact ⟨y⁻¹, one_lt_inv'.mpr h⟩ },
  { exact ⟨y, h⟩ }
end

@[priority 100, to_additive] -- see Note [lower instance priority]
instance linear_ordered_comm_group.to_no_top_order [nontrivial α] :
  no_top_order α :=
⟨ begin
    obtain ⟨y, hy⟩ : ∃ (a:α), 1 < a := exists_one_lt',
    exact λ a, ⟨a * y, lt_mul_of_one_lt_right' a hy⟩
  end ⟩

@[priority 100, to_additive] -- see Note [lower instance priority]
instance linear_ordered_comm_group.to_no_bot_order [nontrivial α] : no_bot_order α :=
⟨ begin
    obtain ⟨y, hy⟩ : ∃ (a:α), 1 < a := exists_one_lt',
    exact λ a, ⟨a / y, (div_lt_self_iff' a).mpr hy⟩
  end ⟩

end linear_ordered_comm_group

section linear_ordered_add_comm_group

variables [linear_ordered_add_comm_group α] {a b c : α}

@[simp]
lemma sub_le_sub_flip : a - b ≤ b - a ↔ a ≤ b :=
begin
  rw [sub_le_iff_le_add, sub_add_eq_add_sub, le_sub_iff_add_le],
  split,
  { intro h,
    by_contra H,
    rw not_le at H,
    apply not_lt.2 h,
    exact add_lt_add H H, },
  { intro h,
    exact add_le_add h h, }
end

@[simp] lemma max_zero_sub_max_neg_zero_eq_self (a : α) :
  max a 0 - max (-a) 0 = a :=
by { rcases le_total a 0 with h|h; simp [h] }

lemma le_of_forall_pos_le_add [densely_ordered α] (h : ∀ ε : α, 0 < ε → a ≤ b + ε) : a ≤ b :=
le_of_forall_le_of_dense $ λ c hc,
calc a ≤ b + (c - b) : h _ (sub_pos_of_lt hc)
   ... = c           : add_sub_cancel'_right _ _

lemma le_iff_forall_pos_le_add [densely_ordered α] : a ≤ b ↔ ∀ ε, 0 < ε → a ≤ b + ε :=
⟨λ h ε ε_pos, le_add_of_le_of_nonneg h ε_pos.le, le_of_forall_pos_le_add⟩

lemma le_of_forall_pos_lt_add (h : ∀ ε : α, 0 < ε → a < b + ε) : a ≤ b :=
le_of_not_lt $ λ h₁, by simpa using h _ (sub_pos_of_lt h₁)

lemma le_iff_forall_pos_lt_add : a ≤ b ↔ ∀ ε, 0 < ε → a < b + ε :=
⟨λ h ε, lt_add_of_le_of_pos h, le_of_forall_pos_lt_add⟩

/-- `abs a` is the absolute value of `a`. -/
def abs (a : α) : α := max a (-a)

lemma abs_choice (x : α) : abs x = x ∨ abs x = -x := max_choice _ _

lemma abs_of_nonneg (h : 0 ≤ a) : abs a = a :=
max_eq_left $ (neg_nonpos.2 h).trans h

lemma abs_of_pos (h : 0 < a) : abs a = a :=
abs_of_nonneg h.le

lemma abs_of_nonpos (h : a ≤ 0) : abs a = -a :=
max_eq_right $ h.trans (neg_nonneg.2 h)

lemma abs_of_neg (h : a < 0) : abs a = -a :=
abs_of_nonpos h.le

@[simp] lemma abs_zero : abs 0 = (0:α) :=
abs_of_nonneg le_rfl

@[simp] lemma abs_neg (a : α) : abs (-a) = abs a :=
begin unfold abs, rw [max_comm, neg_neg] end

@[simp] lemma abs_pos : 0 < abs a ↔ a ≠ 0 :=
begin
  rcases lt_trichotomy a 0 with (ha|rfl|ha),
  { simp [abs_of_neg ha, neg_pos, ha.ne, ha] },
  { simp },
  { simp [abs_of_pos ha, ha, ha.ne.symm] }
end

lemma abs_pos_of_pos (h : 0 < a) : 0 < abs a := abs_pos.2 h.ne.symm

lemma abs_pos_of_neg (h : a < 0) : 0 < abs a := abs_pos.2 h.ne

lemma abs_sub_comm (a b : α) : abs (a - b) = abs (b - a) :=
by rw [← neg_sub, abs_neg]

lemma abs_le' : abs a ≤ b ↔ a ≤ b ∧ -a ≤ b := max_le_iff

lemma abs_le : abs a ≤ b ↔ - b ≤ a ∧ a ≤ b :=
by rw [abs_le', and.comm, neg_le]

lemma neg_le_of_abs_le (h : abs a ≤ b) : -b ≤ a := (abs_le.mp h).1

lemma le_of_abs_le (h : abs a ≤ b) : a ≤ b := (abs_le.mp h).2

lemma le_abs : a ≤ abs b ↔ a ≤ b ∨ a ≤ -b := le_max_iff

lemma le_abs_self (a : α) : a ≤ abs a := le_max_left _ _

lemma neg_le_abs_self (a : α) : -a ≤ abs a := le_max_right _ _

lemma neg_abs_le_self (a : α) : -abs a ≤ a :=
neg_le.mpr $ neg_le_abs_self a

lemma abs_nonneg (a : α) : 0 ≤ abs a :=
(le_total 0 a).elim (λ h, h.trans (le_abs_self a)) (λ h, (neg_nonneg.2 h).trans $ neg_le_abs_self a)

@[simp] lemma abs_abs (a : α) : abs (abs a) = abs a :=
abs_of_nonneg $ abs_nonneg a

@[simp] lemma abs_eq_zero : abs a = 0 ↔ a = 0 :=
decidable.not_iff_not.1 $ ne_comm.trans $ (abs_nonneg a).lt_iff_ne.symm.trans abs_pos

@[simp] lemma abs_nonpos_iff {a : α} : abs a ≤ 0 ↔ a = 0 :=
(abs_nonneg a).le_iff_eq.trans abs_eq_zero

lemma abs_lt : abs a < b ↔ - b < a ∧ a < b :=
max_lt_iff.trans $ and.comm.trans $ by rw [neg_lt]

lemma neg_lt_of_abs_lt (h : abs a < b) : -b < a := (abs_lt.mp h).1

lemma lt_of_abs_lt (h : abs a < b) : a < b := (abs_lt.mp h).2

lemma lt_abs : a < abs b ↔ a < b ∨ a < -b := lt_max_iff

lemma max_sub_min_eq_abs' (a b : α) : max a b - min a b = abs (a - b) :=
begin
  cases le_total a b with ab ba,
  { rw [max_eq_right ab, min_eq_left ab, abs_of_nonpos, neg_sub], rwa sub_nonpos },
  { rw [max_eq_left ba, min_eq_right ba, abs_of_nonneg], rwa sub_nonneg }
end

lemma max_sub_min_eq_abs (a b : α) : max a b - min a b = abs (b - a) :=
by { rw abs_sub_comm, exact max_sub_min_eq_abs' _ _ }

/--
The **triangle inequality** in `linear_ordered_add_comm_group`s.
-/
lemma abs_add (a b : α) : abs (a + b) ≤ abs a + abs b :=
abs_le.2 ⟨(neg_add (abs a) (abs b)).symm ▸
  add_le_add (neg_le.2 $ neg_le_abs_self _) (neg_le.2 $ neg_le_abs_self _),
  add_le_add (le_abs_self _) (le_abs_self _)⟩

theorem abs_sub (a b : α) :
  abs (a - b) ≤ abs a + abs b :=
by { rw [sub_eq_add_neg, ←abs_neg b], exact abs_add a _ }

lemma abs_sub_le_iff : abs (a - b) ≤ c ↔ a - b ≤ c ∧ b - a ≤ c :=
by rw [abs_le, neg_le_sub_iff_le_add, @sub_le_iff_le_add' _ _ b, and_comm]

lemma abs_sub_lt_iff : abs (a - b) < c ↔ a - b < c ∧ b - a < c :=
by rw [abs_lt, neg_lt_sub_iff_lt_add, @sub_lt_iff_lt_add' _ _ b, and_comm]

lemma sub_le_of_abs_sub_le_left (h : abs (a - b) ≤ c) : b - c ≤ a :=
sub_le.1 $ (abs_sub_le_iff.1 h).2

lemma sub_le_of_abs_sub_le_right (h : abs (a - b) ≤ c) : a - c ≤ b :=
sub_le_of_abs_sub_le_left (abs_sub_comm a b ▸ h)

lemma sub_lt_of_abs_sub_lt_left (h : abs (a - b) < c) : b - c < a :=
sub_lt.1 $ (abs_sub_lt_iff.1 h).2

lemma sub_lt_of_abs_sub_lt_right (h : abs (a - b) < c) : a - c < b :=
sub_lt_of_abs_sub_lt_left (abs_sub_comm a b ▸ h)

lemma abs_sub_abs_le_abs_sub (a b : α) : abs a - abs b ≤ abs (a - b) :=
sub_le_iff_le_add.2 $
calc abs a = abs (a - b + b)     : by rw [sub_add_cancel]
       ... ≤ abs (a - b) + abs b : abs_add _ _

lemma abs_abs_sub_abs_le_abs_sub (a b : α) : abs (abs a - abs b) ≤ abs (a - b) :=
abs_sub_le_iff.2 ⟨abs_sub_abs_le_abs_sub _ _, by rw abs_sub_comm; apply abs_sub_abs_le_abs_sub⟩

lemma eq_or_eq_neg_of_abs_eq (h : abs a = b) : a = b ∨ a = -b :=
by simpa only [← h, eq_comm, eq_neg_iff_eq_neg] using abs_choice a

lemma abs_eq (hb : 0 ≤ b) : abs a = b ↔ a = b ∨ a = -b :=
begin
  refine ⟨eq_or_eq_neg_of_abs_eq, _⟩,
  rintro (rfl|rfl); simp only [abs_neg, abs_of_nonneg hb]
end

lemma abs_eq_abs : abs a = abs b ↔ a = b ∨ a = -b :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain rfl | rfl := eq_or_eq_neg_of_abs_eq h;
    simpa only [neg_eq_iff_neg_eq, neg_inj, or.comm, @eq_comm _ (-b)] using abs_choice b },
  { cases h; simp only [h, abs_neg] },
end

lemma abs_le_max_abs_abs (hab : a ≤ b)  (hbc : b ≤ c) : abs b ≤ max (abs a) (abs c) :=
abs_le'.2
  ⟨by simp [hbc.trans (le_abs_self c)],
   by simp [(neg_le_neg hab).trans (neg_le_abs_self a)]⟩

theorem abs_le_abs (h₀ : a ≤ b) (h₁ : -a ≤ b) : abs a ≤ abs b :=
(abs_le'.2 ⟨h₀, h₁⟩).trans (le_abs_self b)

lemma abs_max_sub_max_le_abs (a b c : α) : abs (max a c - max b c) ≤ abs (a - b) :=
begin
  simp_rw [abs_le, le_sub_iff_add_le, sub_le_iff_le_add, ← max_add_add_left],
  split; apply max_le_max; simp only [← le_sub_iff_add_le, ← sub_le_iff_le_add, sub_self, neg_le,
    neg_le_abs_self, neg_zero, abs_nonneg, le_abs_self]
end

lemma eq_of_abs_sub_eq_zero {a b : α} (h : abs (a - b) = 0) : a = b :=
sub_eq_zero.1 $ abs_eq_zero.1 h

lemma abs_by_cases (P : α → Prop) {a : α} (h1 : P a) (h2 : P (-a)) : P (abs a) :=
sup_ind _ _ h1 h2

lemma abs_sub_le (a b c : α) : abs (a - c) ≤ abs (a - b) + abs (b - c) :=
calc
    abs (a - c) = abs (a - b + (b - c))     : by rw [sub_add_sub_cancel]
            ... ≤ abs (a - b) + abs (b - c) : abs_add _ _

lemma abs_add_three (a b c : α) : abs (a + b + c) ≤ abs a + abs b + abs c :=
(abs_add _ _).trans (add_le_add_right (abs_add _ _) _)

lemma dist_bdd_within_interval {a b lb ub : α} (hal : lb ≤ a) (hau : a ≤ ub)
      (hbl : lb ≤ b) (hbu : b ≤ ub) : abs (a - b) ≤ ub - lb :=
abs_sub_le_iff.2 ⟨sub_le_sub hau hbl, sub_le_sub hbu hal⟩

lemma eq_of_abs_sub_nonpos (h : abs (a - b) ≤ 0) : a = b :=
eq_of_abs_sub_eq_zero (le_antisymm h (abs_nonneg (a - b)))

instance with_top.linear_ordered_add_comm_group_with_top :
  linear_ordered_add_comm_group_with_top (with_top α) :=
{ neg := option.map (λ a : α, -a),
  neg_top := @option.map_none _ _ (λ a : α, -a),
  add_neg_cancel := begin
    rintro (a | a) ha,
    { exact (ha rfl).elim },
    exact with_top.coe_add.symm.trans (with_top.coe_eq_coe.2 (add_neg_self a)),
  end,
  .. with_top.linear_ordered_add_comm_monoid_with_top,
  .. option.nontrivial }

end linear_ordered_add_comm_group

/-- This is not so much a new structure as a construction mechanism
  for ordered groups, by specifying only the "positive cone" of the group. -/
class nonneg_add_comm_group (α : Type*) extends add_comm_group α :=
(nonneg : α → Prop)
(pos : α → Prop := λ a, nonneg a ∧ ¬ nonneg (neg a))
(pos_iff : ∀ a, pos a ↔ nonneg a ∧ ¬ nonneg (-a) . order_laws_tac)
(zero_nonneg : nonneg 0)
(add_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a + b))
(nonneg_antisymm : ∀ {a}, nonneg a → nonneg (-a) → a = 0)

namespace nonneg_add_comm_group
variable [s : nonneg_add_comm_group α]
include s

@[reducible, priority 100] -- see Note [lower instance priority]
instance to_ordered_add_comm_group : ordered_add_comm_group α :=
{ le := λ a b, nonneg (b - a),
  lt := λ a b, pos (b - a),
  lt_iff_le_not_le := λ a b, by simp; rw [pos_iff]; simp,
  le_refl := λ a, by simp [zero_nonneg],
  le_trans := λ a b c nab nbc, by simp [-sub_eq_add_neg];
    rw ← sub_add_sub_cancel; exact add_nonneg nbc nab,
  le_antisymm := λ a b nab nba, eq_of_sub_eq_zero $
    nonneg_antisymm nba (by rw neg_sub; exact nab),
  add_le_add_left := λ a b nab c, by simpa [(≤), preorder.le] using nab,
  ..s }

theorem nonneg_def {a : α} : nonneg a ↔ 0 ≤ a :=
show _ ↔ nonneg _, by simp

theorem pos_def {a : α} : pos a ↔ 0 < a :=
show _ ↔ pos _, by simp

theorem not_zero_pos : ¬ pos (0 : α) :=
mt pos_def.1 (lt_irrefl _)

theorem zero_lt_iff_nonneg_nonneg {a : α} :
  0 < a ↔ nonneg a ∧ ¬ nonneg (-a) :=
pos_def.symm.trans (pos_iff _)

theorem nonneg_total_iff :
  (∀ a : α, nonneg a ∨ nonneg (-a)) ↔
  (∀ a b : α, a ≤ b ∨ b ≤ a) :=
⟨λ h a b, by have := h (b - a); rwa [neg_sub] at this,
 λ h a, by rw [nonneg_def, nonneg_def, neg_nonneg]; apply h⟩

/--
A `nonneg_add_comm_group` is a `linear_ordered_add_comm_group`
if `nonneg` is total and decidable.
-/
def to_linear_ordered_add_comm_group
  [decidable_pred (@nonneg α _)]
  (nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a))
  : linear_ordered_add_comm_group α :=
{ le := (≤),
  lt := (<),
  le_total := nonneg_total_iff.1 nonneg_total,
  decidable_le := by apply_instance,
  decidable_lt := by apply_instance,
  ..@nonneg_add_comm_group.to_ordered_add_comm_group _ s }

end nonneg_add_comm_group

namespace order_dual

instance [ordered_add_comm_group α] : ordered_add_comm_group (order_dual α) :=
{ add_left_neg := λ a : α, add_left_neg a,
  sub := λ a b, (a - b : α),
  ..order_dual.ordered_add_comm_monoid,
  ..show add_comm_group α, by apply_instance }

instance [linear_ordered_add_comm_group α] :
  linear_ordered_add_comm_group (order_dual α) :=
{ add_le_add_left := λ a b h c, by exact add_le_add_left h _,
  ..order_dual.linear_order α,
  ..show add_comm_group α, by apply_instance }

end order_dual

namespace prod

variables {G H : Type*}

@[to_additive]
instance [ordered_comm_group G] [ordered_comm_group H] :
  ordered_comm_group (G × H) :=
{ .. prod.comm_group, .. prod.partial_order G H, .. prod.ordered_cancel_comm_monoid }

end prod

section type_tags

instance [ordered_add_comm_group α] : ordered_comm_group (multiplicative α) :=
{ ..multiplicative.comm_group,
  ..multiplicative.ordered_comm_monoid }

instance [ordered_comm_group α] : ordered_add_comm_group (additive α) :=
{ ..additive.add_comm_group,
  ..additive.ordered_add_comm_monoid }

instance [linear_ordered_add_comm_group α] : linear_ordered_comm_group (multiplicative α) :=
{ ..multiplicative.linear_order,
  ..multiplicative.ordered_comm_group }

instance [linear_ordered_comm_group α] : linear_ordered_add_comm_group (additive α) :=
{ ..additive.linear_order,
  ..additive.ordered_add_comm_group }

end type_tags
