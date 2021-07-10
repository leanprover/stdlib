/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa
-/

import algebra.covariant_and_contravariant
import order.basic

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.

## Remark

No monoid is actually present in this file: all assumptions have been generalized to `has_mul` or
`mul_one_class`.

-/

-- TODO: If possible, uniformize lemma names, taking special care of `'`,
-- after the `ordered`-refactor is done.

variables {α : Type*}
section has_mul
variables [has_mul α]

section has_le
variables [has_le α]

@[simp, to_additive]
lemma mul_le_mul_iff_left [covariant_class α α (*) (≤)] [contravariant_class α α (*) (≤)]
  (a : α) {b c : α} :
  a * b ≤ a * c ↔ b ≤ c :=
rel_iff_cov α α (*) (≤) a

@[simp, to_additive]
lemma mul_le_mul_iff_right
  [covariant_class α α (function.swap (*)) (≤)] [contravariant_class α α (function.swap (*)) (≤)]
  (a : α) {b c : α} :
  b * a ≤ c * a ↔ b ≤ c :=
rel_iff_cov α α (function.swap (*)) (≤) a

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_left]
lemma mul_le_mul_left' [covariant_class α α (*) (≤)] {b c : α} (bc : b ≤ c) (a : α) :
  a * b ≤ a * c :=
covariant_class.elim _ bc

@[to_additive le_of_add_le_add_left]
lemma le_of_mul_le_mul_left' [contravariant_class α α (*) (≤)]
  {a b c : α} (bc : a * b ≤ a * c) :
  b ≤ c :=
contravariant_class.elim _ bc

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_right]
lemma mul_le_mul_right' [covariant_class α α (function.swap (*)) (≤)]
  {b c : α} (bc : b ≤ c) (a : α) :
  b * a ≤ c * a :=
covariant_class.elim a bc

@[to_additive le_of_add_le_add_right]
lemma le_of_mul_le_mul_right' [contravariant_class α α (function.swap (*)) (≤)]
  {a b c : α} (bc : b * a ≤ c * a) :
  b ≤ c :=
contravariant_class.elim a bc

end has_le

section has_lt
variables [has_lt α]

@[simp, to_additive]
lemma mul_lt_mul_iff_left [covariant_class α α (*) (<)] [contravariant_class α α (*) (<)]
  (a : α) {b c : α} :
  a * b < a * c ↔ b < c :=
rel_iff_cov α α (*) (<) a

@[simp, to_additive]
lemma mul_lt_mul_iff_right
  [covariant_class α α (function.swap (*)) (<)] [contravariant_class α α (function.swap (*)) (<)]
  (a : α) {b c : α} :
  b * a < c * a ↔ b < c :=
rel_iff_cov α α (function.swap (*)) (<) a

@[to_additive add_lt_add_left]
lemma mul_lt_mul_left' [covariant_class α α (*) (<)] {b c : α} (bc : b < c) (a : α) :
  a * b < a * c :=
covariant_class.elim _ bc

@[to_additive lt_of_add_lt_add_left]
lemma lt_of_mul_lt_mul_left' [contravariant_class α α (*) (<)]
  {a b c : α} (bc : a * b < a * c) :
  b < c :=
contravariant_class.elim _ bc

@[to_additive add_lt_add_right]
lemma mul_lt_mul_right' [covariant_class α α (function.swap (*)) (<)]
  {b c : α} (bc : b < c) (a : α) :
  b * a < c * a :=
covariant_class.elim a bc

@[to_additive lt_of_add_lt_add_right]
lemma lt_of_mul_lt_mul_right' [contravariant_class α α (function.swap (*)) (<)]
  {a b c : α} (bc : b * a < c * a) :
  b < c :=
contravariant_class.elim a bc

end has_lt

end has_mul

-- using one
section mul_one_class
variables [mul_one_class α]

section has_le
variables [has_le α]

@[simp, to_additive le_add_iff_nonneg_right]
lemma le_mul_iff_one_le_right'
  [covariant_class α α (*) (≤)] [contravariant_class α α (*) (≤)]
  (a : α) {b : α} : a ≤ a * b ↔ 1 ≤ b :=
iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[simp, to_additive add_le_iff_nonpos_right]
lemma mul_le_iff_le_one_right'
  [covariant_class α α (*) (≤)] [contravariant_class α α (*) (≤)]
  (a : α) {b : α} :
  a * b ≤ a ↔ b ≤ 1 :=
iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[simp, to_additive le_add_iff_nonneg_left]
lemma le_mul_iff_one_le_left'
  [covariant_class α α (function.swap (*)) (≤)] [contravariant_class α α (function.swap (*)) (≤)]
  (a : α) {b : α} :
  a ≤ b * a ↔ 1 ≤ b :=
iff.trans (by rw one_mul) (mul_le_mul_iff_right a)

@[simp, to_additive add_le_iff_nonpos_left]
lemma mul_le_iff_le_one_left'
  [covariant_class α α (function.swap (*)) (≤)] [contravariant_class α α (function.swap (*)) (≤)]
  {a b : α} :
  a * b ≤ b ↔ a ≤ 1 :=
iff.trans (by rw one_mul) (mul_le_mul_iff_right b)

end has_le

section has_lt
variable [has_lt α]

@[to_additive lt_add_of_pos_right]
lemma lt_mul_of_one_lt_right'
  [covariant_class α α (*) (<)]
  (a : α) {b : α} (h : 1 < b) : a < a * b :=
calc a = a * 1 : (mul_one _).symm
   ... < a * b : mul_lt_mul_left' h a

@[simp, to_additive lt_add_iff_pos_right]
lemma lt_mul_iff_one_lt_right'
  [covariant_class α α (*) (<)] [contravariant_class α α (*) (<)]
  (a : α) {b : α} :
  a < a * b ↔ 1 < b :=
iff.trans (by rw mul_one) (mul_lt_mul_iff_left a)

@[simp, to_additive add_lt_iff_neg_left]
lemma mul_lt_iff_lt_one_left'
  [covariant_class α α (*) (<)] [contravariant_class α α (*) (<)] {a b : α} :
  a * b < a ↔ b < 1 :=
iff.trans (by rw mul_one) (mul_lt_mul_iff_left a)

@[simp, to_additive lt_add_iff_pos_left]
lemma lt_mul_iff_one_lt_left'
  [covariant_class α α (function.swap (*)) (<)] [contravariant_class α α (function.swap (*)) (<)]
  (a : α) {b : α} : a < b * a ↔ 1 < b :=
iff.trans (by rw one_mul) (mul_lt_mul_iff_right a)

@[simp, to_additive add_lt_iff_neg_right]
lemma mul_lt_iff_lt_one_right'
  [covariant_class α α (function.swap (*)) (<)] [contravariant_class α α (function.swap (*)) (<)]
  {a : α} (b : α) :
  a * b < b ↔ a < 1 :=
iff.trans (by rw one_mul) (mul_lt_mul_iff_right b)

end has_lt

section preorder
variable [preorder α]

@[to_additive]
lemma mul_le_of_le_of_le_one [covariant_class α α (*) (≤)]
  {a b c : α} (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' ha b
        ... = b     : mul_one b
        ... ≤ c     : hbc

alias mul_le_of_le_of_le_one ← mul_le_one'
attribute [to_additive add_nonpos] mul_le_one'

@[to_additive]
lemma lt_mul_of_lt_of_one_le [covariant_class α α (*) (≤)]
  {a b c : α} (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
calc  b < c     : hbc
    ... = c * 1 : (mul_one c).symm
    ... ≤ c * a : mul_le_mul_left' ha c

@[to_additive]
lemma mul_lt_of_lt_of_le_one [covariant_class α α (*) (≤)]
  {a b c : α} (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' ha b
        ... = b     : mul_one b
        ... < c     : hbc

@[to_additive]
lemma lt_mul_of_le_of_one_lt [covariant_class α α (*) (<)]
  {a b c : α} (hbc : b ≤ c) (ha : 1 < a) : b < c * a :=
calc  b ≤ c     : hbc
    ... = c * 1 : (mul_one c).symm
    ... < c * a : mul_lt_mul_left' ha c

@[to_additive]
lemma mul_lt_of_le_one_of_lt [covariant_class α α (function.swap (*)) (≤)]
  {a b c : α} (ha : a ≤ 1) (hb : b < c) : a * b < c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' ha b
        ... = b     : one_mul b
        ... < c     : hb

@[to_additive]
lemma mul_le_of_le_one_of_le [covariant_class α α (function.swap (*)) (≤)]
  {a b c : α} (ha : a ≤ 1) (hbc : b ≤ c) :
  a * b ≤ c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' ha b
        ... = b     : one_mul b
        ... ≤ c     : hbc

@[to_additive]
lemma le_mul_of_one_le_of_le [covariant_class α α (function.swap (*)) (≤)]
  {a b c: α} (ha : 1 ≤ a) (hbc : b ≤ c) : b ≤ a * c :=
calc  b ≤ c     : hbc
    ... = 1 * c : (one_mul c).symm
    ... ≤ a * c : mul_le_mul_right' ha c

/--
Assume monotonicity on the `left`. The lemma assuming `right` is `right.mul_lt_one`. -/
@[to_additive]
lemma left.mul_lt_one [covariant_class α α (*) (<)]
  {a b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
calc  a * b < a * 1 : mul_lt_mul_left' hb a
        ... = a     : mul_one a
        ... < 1     : ha

/--
Assume monotonicity on the `right`. The lemma assuming `left` is `left.mul_lt_one`. -/
@[to_additive]
lemma right.mul_lt_one [covariant_class α α (function.swap (*)) (<)]
  {a b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
calc  a * b < 1 * b : mul_lt_mul_right' ha b
        ... = b     : one_mul b
        ... < 1     : hb

@[to_additive]
lemma mul_lt_of_le_of_lt_one
  [covariant_class α α (*) (<)] [covariant_class α α (function.swap (*)) (≤)]
  {a b c: α} (hbc : b ≤ c) (ha : a < 1) : b * a < c :=
calc  b * a ≤ c * a : mul_le_mul_right' hbc a
        ... < c * 1 : mul_lt_mul_left' ha c
        ... = c     : mul_one c

@[to_additive]
lemma mul_lt_of_lt_one_of_le [covariant_class α α (function.swap (*)) (<)]
  {a b c : α} (ha : a < 1) (hbc : b ≤ c) : a * b < c :=
calc  a * b < 1 * b : mul_lt_mul_right' ha b
        ... = b     : one_mul b
        ... ≤ c     : hbc

@[to_additive]
lemma lt_mul_of_one_lt_of_le [covariant_class α α (function.swap (*)) (<)]
  {a b c : α} (ha : 1 < a) (hbc : b ≤ c) : b < a * c :=
calc  b ≤ c     : hbc
    ... = 1 * c : (one_mul c).symm
    ... < a * c : mul_lt_mul_right' ha c

/-- Assumes left covariance. -/
@[to_additive]
lemma le_mul_of_le_of_le_one [covariant_class α α (*) (≤)]
  {a b c : α} (ha : c ≤ a) (hb : 1 ≤ b) : c ≤ a * b :=
calc  c ≤ a     : ha
    ... = a * 1 : (mul_one a).symm
    ... ≤ a * b : mul_le_mul_left' hb a

/-  This lemma is present to mimick the name of an existing one. -/
@[to_additive add_nonneg]
lemma one_le_mul [covariant_class α α (*) (≤)]
  {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
le_mul_of_le_of_le_one ha hb

/-- Assumes left covariance. -/
@[to_additive]
lemma lt_mul_of_lt_of_one_lt [covariant_class α α (*) (<)]
  {a b c : α} (ha : c < a) (hb : 1 < b) : c < a * b :=
calc  c < a     : ha
    ... = a * 1 : (mul_one _).symm
    ... < a * b : mul_lt_mul_left' hb a

/-- Assumes left covariance. -/
@[to_additive]
lemma left.mul_lt_one_of_lt_of_lt_one [covariant_class α α (*) (<)]
  {a b c : α} (ha : a < c) (hb : b < 1) : a * b < c :=
calc  a * b < a * 1 : mul_lt_mul_left' hb a
        ... = a     : mul_one a
        ... < c     : ha

/-- Assumes right covariance. -/
@[to_additive]
lemma right.mul_lt_one_of_lt_of_lt_one [covariant_class α α (function.swap (*)) (<)]
  {a b c : α} (ha : a < 1) (hb : b < c) : a * b < c :=
calc  a * b < 1 * b : mul_lt_mul_right' ha b
        ... = b     : one_mul b
        ... < c     : hb

/-- Assumes right covariance. -/
@[to_additive right.add_nonneg]
lemma right.one_le_mul [covariant_class α α (function.swap (*)) (≤)]
  {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
calc  1 ≤ b     : hb
    ... = 1 * b : (one_mul b).symm
    ... ≤ a * b : mul_le_mul_right' ha b

/-- Assumes right covariance. -/
@[to_additive right.add_pos]
lemma right.one_lt_mul [covariant_class α α (function.swap (*)) (<)]
  {b : α} (hb : 1 < b) {a: α} (ha : 1 < a) : 1 < a * b :=
calc  1 < b     : hb
    ... = 1 * b : (one_mul _).symm
    ... < a * b : mul_lt_mul_right' ha b

end preorder


@[to_additive le_add_of_nonneg_right]
lemma le_mul_of_one_le_right' [has_le α] [covariant_class α α (*) (≤)] {a b : α} (h : 1 ≤ b) :
  a ≤ a * b :=
calc  a = a * 1  : (mul_one _).symm
    ... ≤ a * b  : mul_le_mul_left' h a

@[to_additive add_le_of_nonpos_right]
lemma mul_le_of_le_one_right' [has_le α] [covariant_class α α (*) (≤)] {a b : α} (h : b ≤ 1) :
  a * b ≤ a :=
calc  a * b ≤ a * 1 : mul_le_mul_left' h a
        ... = a     : mul_one a

end mul_one_class

/- This is not instance, since we want to have an instance from `left_cancel_semigroup`s
to the appropriate `covariant_class`. -/
/--  A semigroup with a partial order and satisfying `left_cancel_semigroup`
(i.e. `a * c < b * c → a < b`) is a `left_cancel semigroup`. -/
@[to_additive
"An additive semigroup with a partial order and satisfying `left_cancel_add_semigroup`
(i.e. `c + a < c + b → a < b`) is a `left_cancel add_semigroup`."]
def contravariant.to_left_cancel_semigroup [semigroup α] [partial_order α]
  [contravariant_class α α ((*) : α → α → α) (≤)] :
  left_cancel_semigroup α :=
{ mul_left_cancel := λ a b c bc,
    (le_of_mul_le_mul_left' bc.le).antisymm (le_of_mul_le_mul_left' bc.ge),
  ..‹semigroup α› }

/- This is not instance, since we want to have an instance from `right_cancel_semigroup`s
to the appropriate `covariant_class`. -/
/--  A semigroup with a partial order and satisfying `right_cancel_semigroup`
(i.e. `a * c < b * c → a < b`) is a `right_cancel semigroup`. -/
@[to_additive
"An additive semigroup with a partial order and satisfying `right_cancel_add_semigroup`
(`a + c < b + c → a < b`) is a `right_cancel add_semigroup`."]
def contravariant.to_right_cancel_semigroup [semigroup α] [partial_order α]
  [contravariant_class α α (function.swap (*) : α → α → α) (≤)] :
  right_cancel_semigroup α :=
{ mul_right_cancel := λ a b c bc,
    le_antisymm (le_of_mul_le_mul_right' bc.le) (le_of_mul_le_mul_right' bc.ge)
  ..‹semigroup α› }

variables {a b c d : α}

section left
variables [preorder α]

section has_mul
variables [has_mul α]

@[to_additive]
lemma mul_lt_mul_of_lt_of_lt
  [covariant_class α α (*) (<)] [covariant_class α α (function.swap (*)) (<)]
  (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
calc  a * c < a * d : mul_lt_mul_left' h₂ a
        ... < b * d : mul_lt_mul_right' h₁ d

section contravariant_mul_lt_left_le_right
variables [covariant_class α α (*) (<)] [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma mul_lt_mul_of_le_of_lt
  (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
(mul_le_mul_right' h₁ _).trans_lt (mul_lt_mul_left' h₂ b)

@[to_additive add_lt_add]
lemma mul_lt_mul''' (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
mul_lt_mul_of_le_of_lt h₁.le h₂

end contravariant_mul_lt_left_le_right

variable [covariant_class α α (*) (≤)]

@[to_additive]
lemma mul_lt_of_mul_lt_left (h : a * b < c) (hle : d ≤ b) :
  a * d < c :=
(mul_le_mul_left' hle a).trans_lt h

@[to_additive]
lemma mul_le_of_mul_le_left (h : a * b ≤ c) (hle : d ≤ b) :
  a * d ≤ c :=
@act_rel_of_rel_of_act_rel _ _ _ (≤) _ ⟨λ _ _ _, le_trans⟩ a _ _ _ hle h

@[to_additive]
lemma lt_mul_of_lt_mul_left (h : a < b * c) (hle : c ≤ d) :
  a < b * d :=
h.trans_le (mul_le_mul_left' hle b)

@[to_additive]
lemma le_mul_of_le_mul_left (h : a ≤ b * c) (hle : c ≤ d) :
  a ≤ b * d :=
@rel_act_of_rel_of_rel_act _ _ _ (≤) _ ⟨λ _ _ _, le_trans⟩ b _ _ _ hle h

@[to_additive]
lemma mul_lt_mul_of_lt_of_le [covariant_class α α (function.swap (*)) (<)]
  (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
(mul_le_mul_left' h₂ _).trans_lt (mul_lt_mul_right' h₁ d)

end has_mul

/-!  Here we start using properties of one, on the left. -/
section mul_one_class
variables [mul_one_class α] [covariant_class α α (*) (≤)]

@[to_additive]
lemma lt_of_mul_lt_of_one_le_left (h : a * b < c) (hle : 1 ≤ b) : a < c :=
(le_mul_of_one_le_right' hle).trans_lt h

@[to_additive]
lemma le_of_mul_le_of_one_le_left (h : a * b ≤ c) (hle : 1 ≤ b) : a ≤ c :=
(le_mul_of_one_le_right' hle).trans h

@[to_additive]
lemma lt_of_lt_mul_of_le_one_left (h : a < b * c) (hle : c ≤ 1) : a < b :=
h.trans_le (mul_le_of_le_one_right' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_left (h : a ≤ b * c) (hle : c ≤ 1) : a ≤ b :=
h.trans (mul_le_of_le_one_right' hle)

@[to_additive]
theorem mul_lt_of_lt_of_lt_one (bc : b < c) (a1 : a < 1) :
  b * a < c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' a1.le _
        ... = b     : mul_one b
        ... < c     : bc

end mul_one_class

end left

section right

section preorder
variables [preorder α]

section has_mul
variables [has_mul α]

variable [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma mul_lt_of_mul_lt_right (h : a * b < c) (hle : d ≤ a) :
  d * b < c :=
(mul_le_mul_right' hle b).trans_lt h

@[to_additive]
lemma mul_le_of_mul_le_right (h : a * b ≤ c) (hle : d ≤ a) :
  d * b ≤ c :=
(mul_le_mul_right' hle b).trans h

@[to_additive]
lemma lt_mul_of_lt_mul_right (h : a < b * c) (hle : b ≤ d) :
  a < d * c :=
h.trans_le (mul_le_mul_right' hle c)

@[to_additive]
lemma le_mul_of_le_mul_right (h : a ≤ b * c) (hle : b ≤ d) :
  a ≤ d * c :=
h.trans (mul_le_mul_right' hle c)

variable [covariant_class α α (*) (≤)]

@[to_additive add_le_add]
lemma mul_le_mul' (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
(mul_le_mul_left' h₂ _).trans (mul_le_mul_right' h₁ d)

@[to_additive]
lemma mul_le_mul_three {e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) :
  a * b * c ≤ d * e * f :=
mul_le_mul' (mul_le_mul' h₁ h₂) h₃

end has_mul

/-!  Here we start using properties of one, on the right. -/
section mul_one_class
variables [mul_one_class α]

section le_right
variable [covariant_class α α (function.swap (*)) (≤)]

@[to_additive le_add_of_nonneg_left]
lemma le_mul_of_one_le_left' (h : 1 ≤ b) : a ≤ b * a :=
calc  a = 1 * a : (one_mul a).symm
    ... ≤ b * a : mul_le_mul_right' h a

@[to_additive add_le_of_nonpos_left]
lemma mul_le_of_le_one_left' (h : b ≤ 1) : b * a ≤ a :=
calc  b * a ≤ 1 * a : mul_le_mul_right' h a
        ... = a     : one_mul a

@[to_additive]
lemma lt_of_mul_lt_of_one_le_right (h : a * b < c) (hle : 1 ≤ a) : b < c :=
(le_mul_of_one_le_left' hle).trans_lt h

@[to_additive]
lemma le_of_mul_le_of_one_le_right (h : a * b ≤ c) (hle : 1 ≤ a) : b ≤ c :=
(le_mul_of_one_le_left' hle).trans h

@[to_additive]
lemma lt_of_lt_mul_of_le_one_right (h : a < b * c) (hle : b ≤ 1) : a < c :=
h.trans_le (mul_le_of_le_one_left' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_right (h : a ≤ b * c) (hle : b ≤ 1) : a ≤ c :=
h.trans (mul_le_of_le_one_left' hle)

theorem mul_lt_of_lt_one_of_lt (a1 : a < 1) (bc : b < c) :
  a * b < c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' a1.le _
        ... = b : one_mul b
        ... < c : bc

end le_right

section lt_right

@[to_additive lt_add_of_pos_left]
lemma lt_mul_of_one_lt_left' [covariant_class α α (function.swap (*)) (<)]
  (a : α) {b : α} (h : 1 < b) : a < b * a :=
calc a = 1 * a : (one_mul _).symm
   ... < b * a : mul_lt_mul_right' h a

end lt_right

end mul_one_class

end preorder

end right

section preorder
variables [preorder α]

section mul_one_class
variables [mul_one_class α]

section covariant_left
variable [covariant_class α α (*) (≤)]

@[to_additive add_pos_of_pos_of_nonneg]
lemma one_lt_mul_of_lt_of_le' (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
lt_of_lt_of_le ha $ le_mul_of_one_le_right' hb

@[to_additive add_pos]
lemma one_lt_mul' (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
one_lt_mul_of_lt_of_le' ha hb.le

@[to_additive]
lemma lt_mul_of_lt_of_one_le' (hbc : b < c) (ha : 1 ≤ a) :
  b < c * a :=
hbc.trans_le $ le_mul_of_one_le_right' ha

@[to_additive]
lemma lt_mul_of_lt_of_one_lt' (hbc : b < c) (ha : 1 < a) :
  b < c * a :=
lt_mul_of_lt_of_one_le' hbc ha.le

@[to_additive]
lemma le_mul_of_le_of_one_le (hbc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
calc  b ≤ c : hbc
    ... = c * 1 : (mul_one c).symm
    ... ≤ c * a : mul_le_mul_left' ha c

@[to_additive add_nonneg]
lemma one_le_mul_right (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
calc  1 ≤ a     : ha
    ... = a * 1 : (mul_one a).symm
    ... ≤ a * b : mul_le_mul_left' hb a

end covariant_left

section covariant_right
variable [covariant_class α α (function.swap (*)) (≤)]

@[to_additive add_pos_of_nonneg_of_pos]
lemma one_lt_mul_of_le_of_lt' (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_of_lt_of_le hb $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_one_le_of_lt (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
hbc.trans_le $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_one_lt_of_lt (ha : 1 < a) (hbc : b < c) : b < a * c :=
lt_mul_of_one_le_of_lt ha.le hbc

end covariant_right

end mul_one_class

end preorder

section partial_order

/-!  Properties assuming `partial_order`. -/
variables [mul_one_class α] [partial_order α]
  [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma mul_eq_one_iff' (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
iff.intro
  (assume hab : a * b = 1,
   have a ≤ 1, from hab ▸ le_mul_of_le_of_one_le le_rfl hb,
   have a = 1, from le_antisymm this ha,
   have b ≤ 1, from hab ▸ le_mul_of_one_le_of_le ha le_rfl,
   have b = 1, from le_antisymm this hb,
   and.intro ‹a = 1› ‹b = 1›)
  (assume ⟨ha', hb'⟩, by rw [ha', hb', mul_one])

end partial_order

section mono
variables [has_mul α] {β : Type*} {f g : β → α}

section has_le
variables [preorder α] [preorder β]

@[to_additive monotone.const_add]
lemma monotone.const_mul' [covariant_class α α (*) (≤)] (hf : monotone f) (a : α) :
  monotone (λ x, a * f x) :=
λ x y h, mul_le_mul_left' (hf h) a

@[to_additive monotone.add_const]
lemma monotone.mul_const' [covariant_class α α (function.swap (*)) (≤)]
  (hf : monotone f) (a : α) : monotone (λ x, f x * a) :=
λ x y h, mul_le_mul_right' (hf h) a

end has_le

variables [preorder α] [preorder β]
@[to_additive monotone.add]
lemma monotone.mul' [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (≤)]
  (hf : monotone f) (hg : monotone g) : monotone (λ x, f x * g x) :=
λ x y h, mul_le_mul' (hf h) (hg h)

end mono

section strict_mono
variables [has_mul α] {β : Type*} {f g : β → α}

section left
variables [has_lt α] [covariant_class α α (*) (<)] [has_lt β]

@[to_additive strict_mono.const_add]
lemma strict_mono.const_mul' (hf : strict_mono f) (c : α) :
  strict_mono (λ x, c * f x) :=
λ a b ab, mul_lt_mul_left' (hf ab) c

end left

section right
variables [has_lt α] [covariant_class α α (function.swap (*)) (<)] [has_lt β]

@[to_additive strict_mono.add_const]
lemma strict_mono.mul_const' (hf : strict_mono f) (c : α) :
  strict_mono (λ x, f x * c) :=
λ a b ab, mul_lt_mul_right' (hf ab) c

end right

variables [preorder α]

@[to_additive monotone.add_strict_mono]
lemma monotone.mul_strict_mono' [covariant_class α α (*) (<)]
  [covariant_class α α (function.swap (*)) (≤)] {β : Type*} [preorder β]
  {f g : β → α} (hf : monotone f) (hg : strict_mono g) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul_of_le_of_lt (hf h.le) (hg h)
variables [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (<)] [preorder β]

@[to_additive strict_mono.add_monotone]
lemma strict_mono.mul_monotone' (hf : strict_mono f) (hg : monotone g) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

end strict_mono
