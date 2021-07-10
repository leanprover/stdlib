/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.ordered_monoid
import order.rel_iso

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
instance ordered_comm_group.to_covariant_class_left_le (α : Type u) [ordered_comm_group α] :
  covariant_class α α (*) (≤) :=
{ elim := λ a b c bc, ordered_comm_group.mul_le_mul_left b c bc a }

/--The units of an ordered commutative monoid form an ordered commutative group. -/
@[to_additive]
instance units.ordered_comm_group [ordered_comm_monoid α] : ordered_comm_group (units α) :=
{ mul_le_mul_left := λ a b h c, (mul_le_mul_left' (h : (a : α) ≤ b) _ :  (c : α) * a ≤ c * b),
  .. units.partial_order,
  .. (infer_instance : comm_group (units α)) }

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

section group
variables [group α]

section typeclasses_left_le
variables [has_le α] [covariant_class α α (*) (≤)] {a b c d : α}

/--  Uses `left` co(ntra)variant. -/
@[simp, to_additive left.neg_nonpos_iff]
lemma left.inv_le_one_iff :
  a⁻¹ ≤ 1 ↔ 1 ≤ a :=
by { rw [← mul_le_mul_iff_left a], simp }

/--  Uses `left` co(ntra)variant. -/
@[simp, to_additive left.nonneg_neg_iff]
lemma left.one_le_inv_iff :
  1 ≤ a⁻¹ ↔ a ≤ 1 :=
by { rw [← mul_le_mul_iff_left a], simp }

@[simp, to_additive]
lemma le_inv_mul_iff_mul_le : b ≤ a⁻¹ * c ↔ a * b ≤ c :=
by { rw ← mul_le_mul_iff_left a, simp }

@[simp, to_additive]
lemma inv_mul_le_iff_le_mul : b⁻¹ * a ≤ c ↔ a ≤ b * c :=
by rw [← mul_le_mul_iff_left b, mul_inv_cancel_left]

@[to_additive neg_le_iff_add_nonneg']
lemma inv_le_iff_one_le_mul' : a⁻¹ ≤ b ↔ 1 ≤ a * b :=
(mul_le_mul_iff_left a).symm.trans $ by rw mul_inv_self

@[to_additive]
lemma le_inv_iff_mul_le_one_left : a ≤ b⁻¹ ↔ b * a ≤ 1 :=
(mul_le_mul_iff_left b).symm.trans $ by rw mul_inv_self

@[to_additive]
lemma le_inv_mul_iff_le : 1 ≤ b⁻¹ * a ↔ b ≤ a :=
by rw [← mul_le_mul_iff_left b, mul_one, mul_inv_cancel_left]

@[to_additive]
lemma inv_mul_le_one_iff : a⁻¹ * b ≤ 1 ↔ b ≤ a :=
trans (inv_mul_le_iff_le_mul) $ by rw mul_one

end typeclasses_left_le

section typeclasses_left_lt
variables [has_lt α] [covariant_class α α (*) (<)] {a b c : α}

/--  Uses `left` co(ntra)variant. -/
@[simp, to_additive left.neg_pos_iff]
lemma left.one_lt_inv_iff :
  1 < a⁻¹ ↔ a < 1 :=
by rw [← mul_lt_mul_iff_left a, mul_inv_self, mul_one]

/--  Uses `left` co(ntra)variant. -/
@[simp, to_additive left.neg_neg_iff]
lemma left.inv_lt_one_iff :
  a⁻¹ < 1 ↔ 1 < a :=
by rw [← mul_lt_mul_iff_left a, mul_inv_self, mul_one]

@[simp, to_additive]
lemma lt_inv_mul_iff_mul_lt : b < a⁻¹ * c ↔ a * b < c :=
by { rw [← mul_lt_mul_iff_left a], simp }

@[simp, to_additive]
lemma inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c :=
by rw [← mul_lt_mul_iff_left b, mul_inv_cancel_left]

@[to_additive]
lemma inv_lt_iff_one_lt_mul' : a⁻¹ < b ↔ 1 < a * b :=
(mul_lt_mul_iff_left a).symm.trans $ by rw mul_inv_self

@[to_additive]
lemma lt_inv_iff_mul_lt_one' : a < b⁻¹ ↔ b * a < 1 :=
(mul_lt_mul_iff_left b).symm.trans $ by rw mul_inv_self

@[to_additive]
lemma lt_inv_mul_iff_lt : 1 < b⁻¹ * a ↔ b < a :=
by rw [← mul_lt_mul_iff_left b, mul_one, mul_inv_cancel_left]

@[to_additive]
lemma inv_mul_lt_one_iff : a⁻¹ * b < 1 ↔ b < a :=
trans (inv_mul_lt_iff_lt_mul) $ by rw mul_one

end typeclasses_left_lt

section typeclasses_right_le
variables [has_le α] [covariant_class α α (function.swap (*)) (≤)] {a b c : α}

/--  Uses `right` co(ntra)variant. -/
@[simp, to_additive right.neg_nonpos_iff]
lemma right.inv_le_one_iff :
  a⁻¹ ≤ 1 ↔ 1 ≤ a :=
by { rw [← mul_le_mul_iff_right a], simp }

/--  Uses `right` co(ntra)variant. -/
@[simp, to_additive right.nonneg_neg_iff]
lemma right.one_le_inv_iff :
  1 ≤ a⁻¹ ↔ a ≤ 1 :=
by { rw [← mul_le_mul_iff_right a], simp }

@[to_additive neg_le_iff_add_nonneg]
lemma inv_le_iff_one_le_mul : a⁻¹ ≤ b ↔ 1 ≤ b * a :=
(mul_le_mul_iff_right a).symm.trans $ by rw inv_mul_self

@[to_additive]
lemma le_inv_iff_mul_le_one_right : a ≤ b⁻¹ ↔ a * b ≤ 1 :=
(mul_le_mul_iff_right b).symm.trans $ by rw inv_mul_self

@[simp, to_additive]
lemma mul_inv_le_iff_le_mul : a * b⁻¹ ≤ c ↔ a ≤ c * b :=
(mul_le_mul_iff_right b).symm.trans $ by rw inv_mul_cancel_right

@[simp, to_additive]
lemma le_mul_inv_iff_mul_le : c ≤ a * b⁻¹ ↔ c * b ≤ a :=
(mul_le_mul_iff_right b).symm.trans $ by rw inv_mul_cancel_right

@[simp, to_additive]
lemma mul_inv_le_one_iff_le : a * b⁻¹ ≤ 1 ↔ a ≤ b :=
mul_inv_le_iff_le_mul.trans $ by rw one_mul

@[to_additive]
lemma le_mul_inv_iff_le : 1 ≤ a * b⁻¹ ↔ b ≤ a :=
by rw [← mul_le_mul_iff_right b, one_mul, inv_mul_cancel_right]

@[to_additive]
lemma mul_inv_le_one_iff : b * a⁻¹ ≤ 1 ↔ b ≤ a :=
trans (mul_inv_le_iff_le_mul) $ by rw one_mul

end typeclasses_right_le

section typeclasses_right_lt
variables [has_lt α] [covariant_class α α (function.swap (*)) (<)] {a b c : α}

/--  Uses `right` co(ntra)variant. -/
@[simp, to_additive right.neg_neg_iff]
lemma right.inv_lt_one_iff :
  a⁻¹ < 1 ↔ 1 < a :=
by rw [← mul_lt_mul_iff_right a, inv_mul_self, one_mul]

/--  Uses `right` co(ntra)variant. -/
@[simp, to_additive right.neg_pos_iff]
lemma right.one_lt_inv_iff :
  1 < a⁻¹ ↔ a < 1 :=
by rw [← mul_lt_mul_iff_right a, inv_mul_self, one_mul]

@[to_additive]
lemma inv_lt_iff_one_lt_mul : a⁻¹ < b ↔ 1 < b * a :=
(mul_lt_mul_iff_right a).symm.trans $ by rw inv_mul_self

@[to_additive]
lemma lt_inv_iff_mul_lt_one : a < b⁻¹ ↔ a * b < 1 :=
(mul_lt_mul_iff_right b).symm.trans $ by rw inv_mul_self

@[simp, to_additive]
lemma mul_inv_lt_iff_lt_mul : a * b⁻¹ < c ↔ a < c * b :=
by rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right]

@[simp, to_additive]
lemma lt_mul_inv_iff_mul_lt : c < a * b⁻¹ ↔ c * b < a :=
(mul_lt_mul_iff_right b).symm.trans $ by rw inv_mul_cancel_right

@[simp, to_additive]
lemma inv_mul_lt_one_iff_lt : a * b⁻¹ < 1 ↔ a < b :=
by rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right, one_mul]

@[to_additive]
lemma lt_mul_inv_iff_lt : 1 < a * b⁻¹ ↔ b < a :=
by rw [← mul_lt_mul_iff_right b, one_mul, inv_mul_cancel_right]

@[to_additive]
lemma mul_inv_lt_one_iff : b * a⁻¹ < 1 ↔ b < a :=
trans (mul_inv_lt_iff_lt_mul) $ by rw one_mul

end typeclasses_right_lt

section typeclasses_left_right_le
variables [has_le α] [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (≤)]
  {a b c d : α}

@[simp, to_additive]
lemma inv_le_inv_iff : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
by { rw [← mul_le_mul_iff_left a, ← mul_le_mul_iff_right b], simp }

alias neg_le_neg_iff ↔ le_of_neg_le_neg _

@[to_additive]
lemma inv_le_of_inv_le (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
inv_le_inv_iff.mp (
  calc  a⁻¹ ≤ b     : h
        ... = b⁻¹⁻¹ : (inv_inv _).symm)

@[to_additive neg_le]
lemma inv_le' : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
by rw [← inv_le_inv_iff, inv_inv]

@[to_additive le_neg]
lemma le_inv' : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
by rw [← inv_le_inv_iff, inv_inv]

@[to_additive]
lemma mul_inv_le_inv_mul_iff : a * b⁻¹ ≤ d⁻¹ * c ↔ d * a ≤ c * b :=
by rw [← mul_le_mul_iff_left d, ← mul_le_mul_iff_right b, mul_inv_cancel_left, mul_assoc,
    inv_mul_cancel_right]

@[simp, to_additive] lemma div_le_self_iff (a : α) {b : α} : a / b ≤ a ↔ 1 ≤ b :=
by simp [div_eq_mul_inv]

alias sub_le_self_iff ↔ _ sub_le_self

end typeclasses_left_right_le

section typeclasses_left_right_lt
variables [has_lt α] [covariant_class α α (*) (<)] [covariant_class α α (function.swap (*)) (<)]
  {a b c d : α}

@[simp, to_additive]
lemma inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a :=
by { rw [← mul_lt_mul_iff_left a, ← mul_lt_mul_iff_right b], simp }

@[to_additive]
lemma lt_inv_of_lt_inv (h : a < b⁻¹) : b < a⁻¹ :=
inv_lt_inv_iff.mp (
  calc  a⁻¹⁻¹ = a   : inv_inv a
          ... < b⁻¹ : h)

@[to_additive]
lemma inv_lt_of_inv_lt (h : a⁻¹ < b) : b⁻¹ < a :=
inv_lt_inv_iff.mp (
    calc  a⁻¹ < b : h
          ... = b⁻¹⁻¹   : (inv_inv b).symm)

@[to_additive neg_lt]
lemma inv_lt' : a⁻¹ < b ↔ b⁻¹ < a :=
by rw [← inv_lt_inv_iff, inv_inv]

@[to_additive lt_neg]
lemma lt_inv' : a < b⁻¹ ↔ b < a⁻¹ :=
by rw [← inv_lt_inv_iff, inv_inv]

@[to_additive]
lemma mul_inv_lt_inv_mul_iff : a * b⁻¹ < d⁻¹ * c ↔ d * a < c * b :=
by rw [← mul_lt_mul_iff_left d, ← mul_lt_mul_iff_right b, mul_inv_cancel_left, mul_assoc,
    inv_mul_cancel_right]

@[simp, to_additive] lemma div_lt_self_iff (a : α) {b : α} : a / b < a ↔ 1 < b :=
by simp [div_eq_mul_inv]

alias sub_lt_self_iff ↔ _ sub_lt_self

end typeclasses_left_right_lt

section pre_order
variable [preorder α]

section left_le
variables [covariant_class α α (*) (≤)] {a : α}

@[to_additive]
lemma left.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
le_trans (left.inv_le_one_iff.mpr h) h

alias left.neg_le_self ← neg_le_self

@[to_additive]
lemma left.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
le_trans h (left.one_le_inv_iff.mpr h)

end left_le

section left_lt
variables [covariant_class α α (*) (<)] {a : α}

@[to_additive]
lemma left.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
(left.inv_lt_one_iff.mpr h).trans h

alias left.neg_lt_self ← neg_lt_self

@[to_additive]
lemma left.self_lt_inv (h : a < 1) : a < a⁻¹ :=
lt_trans h (left.one_lt_inv_iff.mpr h)

end left_lt

section right_le
variables [covariant_class α α (function.swap (*)) (≤)] {a : α}

@[to_additive]
lemma right.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
le_trans (right.inv_le_one_iff.mpr h) h

@[to_additive]
lemma right.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
le_trans h (right.one_le_inv_iff.mpr h)

end right_le

section right_lt
variables [covariant_class α α (function.swap (*)) (<)] {a : α}

@[to_additive]
lemma right.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
(right.inv_lt_one_iff.mpr h).trans h

@[to_additive]
lemma right.self_lt_inv (h : a < 1) : a < a⁻¹ :=
lt_trans h (right.one_lt_inv_iff.mpr h)

end right_lt

end pre_order

end group

section comm_group
variables [comm_group α]

section has_le
variables [has_le α] [covariant_class α α (*) (≤)] {a b c d : α}

@[to_additive]
lemma inv_mul_le_iff_le_mul' : c⁻¹ * a ≤ b ↔ a ≤ b * c :=
by rw [inv_mul_le_iff_le_mul, mul_comm]

@[simp, to_additive]
lemma mul_inv_le_iff_le_mul' : a * b⁻¹ ≤ c ↔ a ≤ b * c :=
by rw [← inv_mul_le_iff_le_mul, mul_comm]

@[to_additive add_neg_le_add_neg_iff]
lemma mul_inv_le_mul_inv_iff' : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
by rw [mul_comm c, mul_inv_le_inv_mul_iff, mul_comm]

end has_le

section has_lt
variables [has_lt α] [covariant_class α α (*) (<)] {a b c d : α}

@[to_additive]
lemma inv_mul_lt_iff_lt_mul' : c⁻¹ * a < b ↔ a < b * c :=
by rw [inv_mul_lt_iff_lt_mul, mul_comm]

@[simp, to_additive]
lemma mul_inv_lt_iff_le_mul' : a * b⁻¹ < c ↔ a < b * c :=
by rw [← inv_mul_lt_iff_lt_mul, mul_comm]

@[to_additive add_neg_lt_add_neg_iff]
lemma mul_inv_lt_mul_inv_iff' : a * b⁻¹ < c * d⁻¹ ↔ a * d < c * b :=
by rw [mul_comm c, mul_inv_lt_inv_mul_iff, mul_comm]

end has_lt

end comm_group

alias le_inv' ↔ le_inv_of_le_inv _
attribute [to_additive] le_inv_of_le_inv

alias left.inv_le_one_iff ↔ one_le_of_inv_le_one _
attribute [to_additive] one_le_of_inv_le_one

alias left.one_le_inv_iff ↔ le_one_of_one_le_inv _
attribute [to_additive nonpos_of_neg_nonneg] le_one_of_one_le_inv

alias inv_lt_inv_iff ↔ lt_of_inv_lt_inv _
attribute [to_additive] lt_of_inv_lt_inv

alias left.inv_lt_one_iff ↔ one_lt_of_inv_lt_one _
attribute [to_additive] one_lt_of_inv_lt_one

alias left.inv_lt_one_iff ← inv_lt_one_iff_one_lt
attribute [to_additive] inv_lt_one_iff_one_lt

alias left.inv_lt_one_iff ← inv_lt_one'
attribute [to_additive neg_lt_zero] inv_lt_one'

alias left.one_lt_inv_iff ↔  inv_of_one_lt_inv _
attribute [to_additive neg_of_neg_pos] inv_of_one_lt_inv

alias left.one_lt_inv_iff ↔ _ one_lt_inv_of_inv
attribute [to_additive neg_pos_of_neg] one_lt_inv_of_inv

alias le_inv_mul_iff_mul_le ↔ mul_le_of_le_inv_mul _
attribute [to_additive] mul_le_of_le_inv_mul

alias le_inv_mul_iff_mul_le ↔ _ le_inv_mul_of_mul_le
attribute [to_additive] le_inv_mul_of_mul_le

alias inv_mul_le_iff_le_mul ↔ _ inv_mul_le_of_le_mul
attribute [to_additive] inv_mul_le_iff_le_mul

alias lt_inv_mul_iff_mul_lt ↔ mul_lt_of_lt_inv_mul _
attribute [to_additive] mul_lt_of_lt_inv_mul

alias lt_inv_mul_iff_mul_lt ↔ _ lt_inv_mul_of_mul_lt
attribute [to_additive] lt_inv_mul_of_mul_lt

alias inv_mul_lt_iff_lt_mul ↔ lt_mul_of_inv_mul_lt inv_mul_lt_of_lt_mul
attribute [to_additive] lt_mul_of_inv_mul_lt
attribute [to_additive] inv_mul_lt_of_lt_mul

alias lt_mul_of_inv_mul_lt ← lt_mul_of_inv_mul_lt_left
attribute [to_additive] lt_mul_of_inv_mul_lt_left

alias left.inv_le_one_iff ← inv_le_one'
attribute [to_additive neg_nonpos] inv_le_one'

alias left.one_le_inv_iff ← one_le_inv'
attribute [to_additive neg_nonneg] one_le_inv'

alias left.one_lt_inv_iff ← one_lt_inv'
attribute [to_additive neg_pos] one_lt_inv'

alias mul_lt_mul_left' ← ordered_comm_group.mul_lt_mul_left'
attribute [to_additive ordered_add_comm_group.add_lt_add_left] ordered_comm_group.mul_lt_mul_left'

alias le_of_mul_le_mul_left' ← ordered_comm_group.le_of_mul_le_mul_left
attribute [to_additive ordered_add_comm_group.le_of_add_le_add_left]
  ordered_comm_group.le_of_mul_le_mul_left

alias lt_of_mul_lt_mul_left' ← ordered_comm_group.lt_of_mul_lt_mul_left
attribute [to_additive ordered_add_comm_group.lt_of_add_lt_add_left]
  ordered_comm_group.lt_of_mul_lt_mul_left

/-- Pullback an `ordered_comm_group` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.ordered_add_comm_group
"Pullback an `ordered_add_comm_group` under an injective map."]
def function.injective.ordered_comm_group [ordered_comm_group α] {β : Type*}
  [has_one β] [has_mul β] [has_inv β] [has_div β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) :
  ordered_comm_group β :=
{ ..partial_order.lift f hf,
  ..hf.ordered_comm_monoid f one mul,
  ..hf.comm_group f one mul inv div }

/-  Most of the lemmas that are primed in this section appear in ordered_field. -/
/-  I (DT) did not try to minimise the assumptions. -/
section group
variables [group α] [has_le α]

section right
variables [covariant_class α α (function.swap (*)) (≤)] {a b c d : α}

@[simp, to_additive]
lemma div_le_div_iff_right (c : α) : a / c ≤ b / c ↔ a ≤ b :=
by simpa only [div_eq_mul_inv] using mul_le_mul_iff_right _

@[to_additive sub_le_sub_right]
lemma div_le_div_right' (h : a ≤ b) (c : α) : a / c ≤ b / c :=
(div_le_div_iff_right c).2 h

@[simp, to_additive sub_nonneg]
lemma one_le_div' : 1 ≤ a / b ↔ b ≤ a :=
by rw [← mul_le_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_nonneg ↔ le_of_sub_nonneg sub_nonneg_of_le

@[simp, to_additive sub_nonpos]
lemma div_le_one' : a / b ≤ 1 ↔ a ≤ b :=
by rw [← mul_le_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_nonpos ↔ le_of_sub_nonpos sub_nonpos_of_le

@[to_additive]
lemma le_div_iff_mul_le : a ≤ c / b ↔ a * b ≤ c :=
by rw [← mul_le_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]

alias le_sub_iff_add_le ↔ add_le_of_le_sub_right le_sub_right_of_add_le

@[to_additive]
lemma div_le_iff_le_mul : a / c ≤ b ↔ a ≤ b * c :=
by rw [← mul_le_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]

/-- `equiv.mul_right` as an order_iso. -/
@[simps {simp_rhs := tt}]
def order_iso.mul_right (a : α) : α ≃o α :=
{ map_rel_iff' := λ _ _, mul_le_mul_iff_right a, ..equiv.mul_right a }

end right

section left
variables [covariant_class α α (*) (≤)]

/-- `equiv.mul_left` as an order_iso. -/
@[simps {simp_rhs := tt}]
def order_iso.mul_left (a : α) : α ≃o α :=
{ map_rel_iff' := λ _ _, mul_le_mul_iff_left a, ..equiv.mul_left a }

variables [covariant_class α α (function.swap (*)) (≤)] {a b c : α}

@[simp, to_additive]
lemma div_le_div_iff_left (a : α) : a / b ≤ a / c ↔ c ≤ b :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_le_mul_iff_left a⁻¹, inv_mul_cancel_left,
    inv_mul_cancel_left, inv_le_inv_iff]

@[to_additive sub_le_sub_left]
lemma div_le_div_left' (h : a ≤ b) (c : α) : c / b ≤ c / a :=
(div_le_div_iff_left c).2 h

end left

end group

section comm_group
variables [comm_group α]

section has_le
variables [has_le α] [covariant_class α α (*) (≤)] {a b c d : α}

@[to_additive sub_le_sub_iff]
lemma div_le_div_iff' : a / b ≤ c / d ↔ a * d ≤ c * b :=
by simpa only [div_eq_mul_inv] using mul_inv_le_mul_inv_iff'

@[to_additive]
lemma le_div_iff_mul_le' : b ≤ c / a ↔ a * b ≤ c :=
by rw [le_div_iff_mul_le, mul_comm]

alias le_sub_iff_add_le' ↔ add_le_of_le_sub_left le_sub_left_of_add_le

@[to_additive]
lemma div_le_iff_le_mul' : a / b ≤ c ↔ a ≤ b * c :=
by rw [div_le_iff_le_mul, mul_comm]

alias sub_le_iff_le_add' ↔ le_add_of_sub_left_le sub_left_le_of_le_add

@[simp, to_additive]
lemma inv_le_div_iff_le_mul : b⁻¹ ≤ a / c ↔ c ≤ a * b :=
le_div_iff_mul_le.trans inv_mul_le_iff_le_mul'

@[to_additive]
lemma inv_le_div_iff_le_mul' : a⁻¹ ≤ b / c ↔ c ≤ a * b :=
by rw [inv_le_div_iff_le_mul, mul_comm]

@[to_additive sub_le]
lemma div_le'' : a / b ≤ c ↔ a / c ≤ b :=
div_le_iff_le_mul'.trans div_le_iff_le_mul.symm

@[to_additive le_sub]
lemma le_div'' : a ≤ b / c ↔ c ≤ b / a :=
le_div_iff_mul_le'.trans le_div_iff_mul_le.symm

end has_le

section preorder
variables [preorder α] [covariant_class α α (*) (≤)] {a b c d : α}

@[to_additive sub_le_sub]
lemma div_le_div'' (hab : a ≤ b) (hcd : c ≤ d) :
  a / d ≤ b / c :=
begin
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm b, mul_inv_le_inv_mul_iff, mul_comm],
  exact mul_le_mul' hab hcd
end

end preorder

end comm_group

/-  Most of the lemmas that are primed in this section appear in ordered_field. -/
/-  I (DT) did not try to minimise the assumptions. -/
section group
variables [group α] [has_lt α]

section right
variables [covariant_class α α (function.swap (*)) (<)] {a b c d : α}

@[simp, to_additive]
lemma div_lt_div_iff_right (c : α) : a / c < b / c ↔ a < b :=
by simpa only [div_eq_mul_inv] using mul_lt_mul_iff_right _

@[to_additive sub_lt_sub_right]
lemma div_lt_div_right' (h : a < b) (c : α) : a / c < b / c :=
(div_lt_div_iff_right c).2 h

@[simp, to_additive sub_pos]
lemma one_lt_div' : 1 < a / b ↔ b < a :=
by rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_pos ↔ lt_of_sub_pos sub_pos_of_lt

@[simp, to_additive sub_neg]
lemma div_lt_one' : a / b < 1 ↔ a < b :=
by rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_neg ↔ lt_of_sub_neg sub_neg_of_lt

alias sub_neg ← sub_lt_zero

@[to_additive]
lemma lt_div_iff_mul_lt : a < c / b ↔ a * b < c :=
by rw [← mul_lt_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]

alias lt_sub_iff_add_lt ↔ add_lt_of_lt_sub_right lt_sub_right_of_add_lt

@[to_additive]
lemma div_lt_iff_lt_mul : a / c < b ↔ a < b * c :=
by rw [← mul_lt_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_lt_iff_lt_add ↔ lt_add_of_sub_right_lt sub_right_lt_of_lt_add

end right

section left
variables [covariant_class α α (*) (<)] [covariant_class α α (function.swap (*)) (<)] {a b c : α}

@[simp, to_additive]
lemma div_lt_div_iff_left (a : α) : a / b < a / c ↔ c < b :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_lt_mul_iff_left a⁻¹, inv_mul_cancel_left,
    inv_mul_cancel_left, inv_lt_inv_iff]

@[simp, to_additive]
lemma inv_lt_div_iff_lt_mul : a⁻¹ < b / c ↔ c < a * b :=
by rw [div_eq_mul_inv, lt_mul_inv_iff_mul_lt, inv_mul_lt_iff_lt_mul]

@[to_additive sub_lt_sub_left]
lemma div_lt_div_left' (h : a < b) (c : α) : c / b < c / a :=
(div_lt_div_iff_left c).2 h

end left

end group

section comm_group
variables [comm_group α]

section has_lt
variables [has_lt α] [covariant_class α α (*) (<)] {a b c d : α}

@[to_additive sub_lt_sub_iff]
lemma div_lt_div_iff' : a / b < c / d ↔ a * d < c * b :=
by simpa only [div_eq_mul_inv] using mul_inv_lt_mul_inv_iff'

@[to_additive]
lemma lt_div_iff_mul_lt' : b < c / a ↔ a * b < c :=
by rw [lt_div_iff_mul_lt, mul_comm]

alias lt_sub_iff_add_lt' ↔ add_lt_of_lt_sub_left lt_sub_left_of_add_lt

@[to_additive]
lemma div_lt_iff_lt_mul' : a / b < c ↔ a < b * c :=
by rw [div_lt_iff_lt_mul, mul_comm]

alias sub_lt_iff_lt_add' ↔ lt_add_of_sub_left_lt sub_left_lt_of_lt_add

@[to_additive]
lemma inv_lt_div_iff_lt_mul' : b⁻¹ < a / c ↔ c < a * b :=
lt_div_iff_mul_lt.trans inv_mul_lt_iff_lt_mul'

@[to_additive sub_lt]
lemma div_lt'' : a / b < c ↔ a / c < b :=
div_lt_iff_lt_mul'.trans div_lt_iff_lt_mul.symm

@[to_additive lt_sub]
lemma lt_div'' : a < b / c ↔ c < b / a :=
lt_div_iff_mul_lt'.trans lt_div_iff_mul_lt.symm

end has_lt

section preorder
variables [preorder α] [covariant_class α α (*) (<)] {a b c d : α}

@[to_additive sub_lt_sub]
lemma div_lt_div'' (hab : a < b) (hcd : c < d) :
  a / d < b / c :=
begin
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm b, mul_inv_lt_inv_mul_iff, mul_comm],
  exact mul_lt_mul_of_lt_of_lt hab hcd
end

end preorder

end comm_group

section linear_order
variables [group α] [linear_order α] [covariant_class α α (*) (≤)]

section variable_names
variables {a b c : α}

@[to_additive]
lemma le_of_forall_one_lt_lt_mul (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b :=
le_of_not_lt (λ h₁, lt_irrefl a (by simpa using (h _ (lt_inv_mul_iff_lt.mpr h₁))))

@[to_additive]
lemma le_iff_forall_one_lt_lt_mul : a ≤ b ↔ ∀ ε, 1 < ε → a < b * ε :=
⟨λ h ε, lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul⟩

/-  I (DT) introduced this lemma to prove (the additive version `sub_le_sub_flip` of)
`div_le_div_flip` below.  Now I wonder what is the point of either of these lemmas... -/
@[to_additive]
lemma div_le_inv_mul_iff [covariant_class α α (function.swap (*)) (≤)] :
  a / b ≤ a⁻¹ * b ↔ a ≤ b :=
begin
  rw [div_eq_mul_inv, mul_inv_le_inv_mul_iff],
  exact ⟨λ h, not_lt.mp (λ k, not_lt.mpr h (mul_lt_mul''' k k)), λ h, mul_le_mul' h h⟩,
end

/-  What is the point of this lemma?  See comment about `div_le_inv_mul_iff` above. -/
@[simp, to_additive]
lemma div_le_div_flip {α : Type*} [comm_group α] [linear_order α] [covariant_class α α (*) (≤)]
  {a b : α}:
  a / b ≤ b / a ↔ a ≤ b :=
begin
  rw [div_eq_mul_inv b, mul_comm],
  exact div_le_inv_mul_iff,
end

@[simp, to_additive] lemma max_one_div_max_inv_one_eq_self (a : α) :
  max a 1 / max a⁻¹ 1 = a :=
by { rcases le_total a 1 with h|h; simp [h] }

alias max_zero_sub_max_neg_zero_eq_self ← max_zero_sub_eq_self

end variable_names

section densely_ordered
variables [densely_ordered α] {a b c : α}

@[to_additive]
lemma le_of_forall_one_lt_le_mul (h : ∀ ε : α, 1 < ε → a ≤ b * ε) : a ≤ b :=
le_of_forall_le_of_dense $ λ c hc,
calc a ≤ b * (b⁻¹ * c) : h _ (lt_inv_mul_iff_lt.mpr hc)
   ... = c            : mul_inv_cancel_left b c

@[to_additive]
lemma le_iff_forall_one_lt_le_mul : a ≤ b ↔ ∀ ε, 1 < ε → a ≤ b * ε :=
⟨λ h ε ε_pos, le_mul_of_le_of_one_le h ε_pos.le, le_of_forall_one_lt_le_mul⟩

end densely_ordered

end linear_order

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
eq.symm $ @monotone.map_max α (order_dual α) _ _ has_inv.inv a b $ λ a b, inv_le_inv_iff.mpr

@[to_additive max_neg_neg]
lemma max_inv_inv' (a b : α) : max (a⁻¹) (b⁻¹) = (min a b)⁻¹ :=
eq.symm $ @monotone.map_min α (order_dual α) _ _ has_inv.inv a b $ λ a b, inv_le_inv_iff.mpr

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

@[to_additive eq_zero_of_neg_eq]
lemma eq_one_of_inv_eq' (h : a⁻¹ = a) : a = 1 :=
match lt_trichotomy a 1 with
| or.inl h₁ :=
  have 1 < a, from h ▸ one_lt_inv_of_inv h₁,
  absurd h₁ this.asymm
| or.inr (or.inl h₁) := h₁
| or.inr (or.inr h₁) :=
  have a < 1, from h ▸ inv_lt_one'.mpr h₁,
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
    exact λ a, ⟨a / y, (div_lt_self_iff a).mpr hy⟩
  end ⟩

end linear_ordered_comm_group

section covariant_add_le

section has_neg
variables [has_neg α] [linear_order α] {a b: α}

/-- `abs a` is the absolute value of `a`. -/
def abs {α : Type*} [has_neg α] [linear_order α] (a : α) : α := max a (-a)

lemma abs_choice (x : α) : abs x = x ∨ abs x = -x := max_choice _ _

lemma abs_le' : abs a ≤ b ↔ a ≤ b ∧ -a ≤ b := max_le_iff

lemma le_abs : a ≤ abs b ↔ a ≤ b ∨ a ≤ -b := le_max_iff

lemma le_abs_self (a : α) : a ≤ abs a := le_max_left _ _

lemma neg_le_abs_self (a : α) : -a ≤ abs a := le_max_right _ _

lemma lt_abs : a < abs b ↔ a < b ∨ a < -b := lt_max_iff

theorem abs_le_abs (h₀ : a ≤ b) (h₁ : -a ≤ b) : abs a ≤ abs b :=
(abs_le'.2 ⟨h₀, h₁⟩).trans (le_abs_self b)

lemma abs_by_cases (P : α → Prop) {a : α} (h1 : P a) (h2 : P (-a)) : P (abs a) :=
sup_ind _ _ h1 h2

end has_neg

section add_group
variables [add_group α] [linear_order α]

@[simp] lemma abs_neg (a : α) : abs (-a) = abs a :=
begin unfold abs, rw [max_comm, neg_neg] end

lemma eq_or_eq_neg_of_abs_eq {a b : α} (h : abs a = b) : a = b ∨ a = -b :=
by simpa only [← h, eq_comm, eq_neg_iff_eq_neg] using abs_choice a

lemma abs_eq_abs {a b : α} : abs a = abs b ↔ a = b ∨ a = -b :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain rfl | rfl := eq_or_eq_neg_of_abs_eq h;
    simpa only [neg_eq_iff_neg_eq, neg_inj, or.comm, @eq_comm _ (-b)] using abs_choice b },
  { cases h; simp only [h, abs_neg] },
end

lemma abs_sub_comm (a b : α) : abs (a - b) = abs (b - a) :=
calc  abs (a - b) = abs (- (b - a)) : congr_arg _ (neg_sub b a).symm
              ... = abs (b - a)     : abs_neg (b - a)

variables [covariant_class α α (+) (≤)] {a b c : α}

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

@[simp] lemma abs_pos : 0 < abs a ↔ a ≠ 0 :=
begin
  rcases lt_trichotomy a 0 with (ha|rfl|ha),
  { simp [abs_of_neg ha, neg_pos, ha.ne, ha] },
  { simp },
  { simp [abs_of_pos ha, ha, ha.ne.symm] }
end

lemma abs_pos_of_pos (h : 0 < a) : 0 < abs a := abs_pos.2 h.ne.symm

lemma abs_pos_of_neg (h : a < 0) : 0 < abs a := abs_pos.2 h.ne

lemma neg_abs_le_self (a : α) : -abs a ≤ a :=
begin
  cases le_total 0 a with h h,
  { calc -abs a = - a   : congr_arg (has_neg.neg) (abs_of_nonneg h)
            ... ≤ 0     : neg_nonpos.mpr h
            ... ≤ a     : h },
  { calc -abs a = - - a : congr_arg (has_neg.neg) (abs_of_nonpos h)
            ... ≤ a     : (neg_neg a).le }
end

lemma abs_nonneg (a : α) : 0 ≤ abs a :=
(le_total 0 a).elim (λ h, h.trans (le_abs_self a)) (λ h, (neg_nonneg.2 h).trans $ neg_le_abs_self a)

@[simp] lemma abs_abs (a : α) : abs (abs a) = abs a :=
abs_of_nonneg $ abs_nonneg a

@[simp] lemma abs_eq_zero : abs a = 0 ↔ a = 0 :=
decidable.not_iff_not.1 $ ne_comm.trans $ (abs_nonneg a).lt_iff_ne.symm.trans abs_pos

@[simp] lemma abs_nonpos_iff {a : α} : abs a ≤ 0 ↔ a = 0 :=
(abs_nonneg a).le_iff_eq.trans abs_eq_zero

variable [covariant_class α α (function.swap (+)) (≤)]

lemma abs_lt : abs a < b ↔ - b < a ∧ a < b :=
max_lt_iff.trans $ and.comm.trans $ by rw [neg_lt]

lemma neg_lt_of_abs_lt (h : abs a < b) : -b < a := (abs_lt.mp h).1

lemma lt_of_abs_lt (h : abs a < b) : a < b := (abs_lt.mp h).2

lemma max_sub_min_eq_abs' (a b : α) : max a b - min a b = abs (a - b) :=
begin
  cases le_total a b with ab ba,
  { rw [max_eq_right ab, min_eq_left ab, abs_of_nonpos, neg_sub], rwa sub_nonpos },
  { rw [max_eq_left ba, min_eq_right ba, abs_of_nonneg], rwa sub_nonneg }
end

lemma max_sub_min_eq_abs (a b : α) : max a b - min a b = abs (b - a) :=
by { rw abs_sub_comm, exact max_sub_min_eq_abs' _ _ }

end add_group

section add_comm_group
variables [add_comm_group α] [linear_order α] [covariant_class α α (+) (≤)] {a b c d : α}

lemma abs_le : abs a ≤ b ↔ - b ≤ a ∧ a ≤ b :=
by rw [abs_le', and.comm, neg_le]

lemma neg_le_of_abs_le (h : abs a ≤ b) : -b ≤ a := (abs_le.mp h).1

lemma le_of_abs_le (h : abs a ≤ b) : a ≤ b := (abs_le.mp h).2

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
by rw [abs_le, neg_le_sub_iff_le_add, sub_le_iff_le_add', and_comm, sub_le_iff_le_add']

lemma abs_sub_lt_iff : abs (a - b) < c ↔ a - b < c ∧ b - a < c :=
by rw [abs_lt, neg_lt_sub_iff_lt_add', sub_lt_iff_lt_add', and_comm, sub_lt_iff_lt_add']

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

lemma abs_eq (hb : 0 ≤ b) : abs a = b ↔ a = b ∨ a = -b :=
begin
  refine ⟨eq_or_eq_neg_of_abs_eq, _⟩,
  rintro (rfl|rfl); simp only [abs_neg, abs_of_nonneg hb]
end

lemma abs_le_max_abs_abs (hab : a ≤ b)  (hbc : b ≤ c) : abs b ≤ max (abs a) (abs c) :=
abs_le'.2
  ⟨by simp [hbc.trans (le_abs_self c)],
   by simp [(neg_le_neg_iff.mpr hab).trans (neg_le_abs_self a)]⟩

lemma eq_of_abs_sub_eq_zero {a b : α} (h : abs (a - b) = 0) : a = b :=
sub_eq_zero.1 $ abs_eq_zero.1 h

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

lemma abs_max_sub_max_le_abs (a b c : α) : abs (max a c - max b c) ≤ abs (a - b) :=
begin
  simp_rw [abs_le, le_sub_iff_add_le, sub_le_iff_le_add, ← max_add_add_left],
  split; apply max_le_max; simp only [← le_sub_iff_add_le, ← sub_le_iff_le_add, sub_self, neg_le,
    neg_le_abs_self, neg_zero, abs_nonneg, le_abs_self]
end

end add_comm_group

end covariant_add_le

section linear_ordered_add_comm_group
variable [linear_ordered_add_comm_group α]

instance with_top.linear_ordered_add_comm_group_with_top :
  linear_ordered_add_comm_group_with_top (with_top α) :=
{ neg            := option.map (λ a : α, -a),
  neg_top        := @option.map_none _ _ (λ a : α, -a),
  add_neg_cancel := begin
    rintro (a | a) ha,
    { exact (ha rfl).elim },
    { exact with_top.coe_add.symm.trans (with_top.coe_eq_coe.2 (add_neg_self a)) }
  end,
  .. with_top.linear_ordered_add_comm_monoid_with_top,
  .. option.nontrivial }

end linear_ordered_add_comm_group

/-- This is not so much a new structure as a construction mechanism
  for ordered groups, by specifying only the "positive cone" of the group. -/
class nonneg_add_comm_group (α : Type*) extends add_comm_group α :=
(nonneg          : α → Prop)
(pos             : α → Prop := λ a, nonneg a ∧ ¬ nonneg (neg a))
(pos_iff         : ∀ a, pos a ↔ nonneg a ∧ ¬ nonneg (-a) . order_laws_tac)
(zero_nonneg     : nonneg 0)
(add_nonneg      : ∀ {a b}, nonneg a → nonneg b → nonneg (a + b))
(nonneg_antisymm : ∀ {a}, nonneg a → nonneg (-a) → a = 0)

namespace nonneg_add_comm_group
variable [s : nonneg_add_comm_group α]
include s

@[reducible, priority 100] -- see Note [lower instance priority]
instance to_ordered_add_comm_group : ordered_add_comm_group α :=
{ le               := λ a b, nonneg (b - a),
  lt               := λ a b, pos (b - a),
  lt_iff_le_not_le := λ a b, by simp; rw [pos_iff]; simp,
  le_refl          := λ a, by simp [zero_nonneg],
  le_trans         := λ a b c nab nbc, by simp [-sub_eq_add_neg];
    rw ← sub_add_sub_cancel; exact add_nonneg nbc nab,
  le_antisymm      := λ a b nab nba, eq_of_sub_eq_zero $
    nonneg_antisymm nba (by rw neg_sub; exact nab),
  add_le_add_left  := λ a b nab c, by simpa [(≤), preorder.le] using nab,
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

section norm_num_lemmas
/- The following lemmas are stated so that the `norm_num` tactic can use them with the
expected signatures.  -/
variables [ordered_comm_group α] {a b : α}

@[to_additive neg_le_neg]
lemma inv_le_inv' : a ≤ b → b⁻¹ ≤ a⁻¹ :=
inv_le_inv_iff.mpr

@[to_additive neg_lt_neg]
lemma inv_lt_inv' : a < b → b⁻¹ < a⁻¹ :=
inv_lt_inv_iff.mpr

/-  The additive version is also a `linarith` lemma. -/
@[to_additive]
theorem inv_lt_one_of_one_lt : 1 < a → a⁻¹ < 1 :=
inv_lt_one_iff_one_lt.mpr

/-  The additive version is also a `linarith` lemma. -/
@[to_additive]
lemma inv_le_one_of_one_le : 1 ≤ a → a⁻¹ ≤ 1 :=
inv_le_one'.mpr

@[to_additive neg_nonneg_of_nonpos]
lemma one_le_inv_of_le_one :  a ≤ 1 → 1 ≤ a⁻¹ :=
one_le_inv'.mpr

end norm_num_lemmas
