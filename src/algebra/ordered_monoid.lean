/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.group.with_one
import algebra.group.type_tags
import algebra.group.prod
import algebra.order_functions
import order.bounded_lattice

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.

-/

set_option old_structure_cmd true

universe u
variable {α : Type u}

/-- An ordered commutative monoid is a commutative monoid
with a partial order such that
  * `a ≤ b → c * a ≤ c * b` (multiplication is monotone)
  * `a * b < a * c → b < c`.
-/
@[protect_proj, ancestor comm_monoid partial_order]
class ordered_comm_monoid (α : Type*) extends comm_monoid α, partial_order α :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c)

/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that
  * `a ≤ b → c + a ≤ c + b` (addition is monotone)
  * `a + b < a + c → b < c`.
-/
@[protect_proj, ancestor add_comm_monoid partial_order]
class ordered_add_comm_monoid (α : Type*) extends add_comm_monoid α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(lt_of_add_lt_add_left : ∀ a b c : α, a + b < a + c → b < c)

attribute [to_additive] ordered_comm_monoid

/-- A linearly ordered additive commutative monoid. -/
@[protect_proj, ancestor linear_order ordered_add_comm_monoid]
class linear_ordered_add_comm_monoid (α : Type*)
  extends linear_order α, ordered_add_comm_monoid α :=
(lt_of_add_lt_add_left := λ x y z, by {
  apply imp_of_not_imp_not,
  intro h,
  apply not_lt_of_le,
  apply add_le_add_left,
  -- type-class inference uses `a : linear_order α` which it can't unfold, unless we provide this!
  -- `lt_iff_le_not_le` gets filled incorrectly with `autoparam` if we don't provide that field.
  letI : linear_order α := by refine { le := le, lt := lt, lt_iff_le_not_le := _, .. }; assumption,
  exact le_of_not_lt h })

/-- A linearly ordered commutative monoid. -/
@[protect_proj, ancestor linear_order ordered_comm_monoid, to_additive]
class linear_ordered_comm_monoid (α : Type*)
  extends linear_order α, ordered_comm_monoid α :=
(lt_of_mul_lt_mul_left := λ x y z, by {
  apply imp_of_not_imp_not,
  intro h,
  apply not_lt_of_le,
  apply mul_le_mul_left,
  -- type-class inference uses `a : linear_order α` which it can't unfold, unless we provide this!
  -- `lt_iff_le_not_le` gets filled incorrectly with `autoparam` if we don't provide that field.
  letI : linear_order α := by refine { le := le, lt := lt, lt_iff_le_not_le := _, .. }; assumption,
  exact le_of_not_lt h })

/-- A linearly ordered commutative monoid with a zero element. -/
class linear_ordered_comm_monoid_with_zero (α : Type*)
  extends linear_ordered_comm_monoid α, comm_monoid_with_zero α :=
(zero_le_one : (0 : α) ≤ 1)

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.` -/
@[protect_proj, ancestor linear_ordered_add_comm_monoid order_top]
class linear_ordered_add_comm_monoid_with_top (α : Type*)
  extends linear_ordered_add_comm_monoid α, order_top α :=
(top_add' : ∀ x : α, ⊤ + x = ⊤)

section linear_ordered_add_comm_monoid_with_top
variables [linear_ordered_add_comm_monoid_with_top α] {a b : α}

@[simp]
lemma top_add (a : α) : ⊤ + a = ⊤ := linear_ordered_add_comm_monoid_with_top.top_add' a

@[simp]
lemma add_top (a : α) : a + ⊤ = ⊤ :=
by rw [add_comm, top_add]

end linear_ordered_add_comm_monoid_with_top

section ordered_comm_monoid
variables [ordered_comm_monoid α] {a b c d : α}

@[to_additive add_le_add_left]
lemma mul_le_mul_left' (h : a ≤ b) (c) : c * a ≤ c * b :=
ordered_comm_monoid.mul_le_mul_left a b h c

@[to_additive add_le_add_right]
lemma mul_le_mul_right' (h : a ≤ b) (c) : a * c ≤ b * c :=
by { convert mul_le_mul_left' h c using 1; rw mul_comm }

@[to_additive]
lemma mul_lt_of_mul_lt_left (h : a * b < c) (hle : d ≤ b) : a * d < c :=
(mul_le_mul_left' hle a).trans_lt h

@[to_additive]
lemma mul_lt_of_mul_lt_right (h : a * b < c) (hle : d ≤ a) : d * b < c :=
(mul_le_mul_right' hle b).trans_lt h

@[to_additive]
lemma mul_le_of_mul_le_left (h : a * b ≤ c) (hle : d ≤ b) : a * d ≤ c :=
(mul_le_mul_left' hle a).trans h

@[to_additive]
lemma mul_le_of_mul_le_right (h : a * b ≤ c) (hle : d ≤ a) : d * b ≤ c :=
(mul_le_mul_right' hle b).trans h

@[to_additive]
lemma lt_mul_of_lt_mul_left (h : a < b * c) (hle : c ≤ d) : a < b * d :=
h.trans_le (mul_le_mul_left' hle b)

@[to_additive]
lemma lt_mul_of_lt_mul_right (h : a < b * c) (hle : b ≤ d) : a < d * c :=
h.trans_le (mul_le_mul_right' hle c)

@[to_additive]
lemma le_mul_of_le_mul_left (h : a ≤ b * c) (hle : c ≤ d) : a ≤ b * d :=
h.trans (mul_le_mul_left' hle b)

@[to_additive]
lemma le_mul_of_le_mul_right (h : a ≤ b * c) (hle : b ≤ d) : a ≤ d * c :=
h.trans (mul_le_mul_right' hle c)

@[to_additive lt_of_add_lt_add_left]
lemma lt_of_mul_lt_mul_left' : a * b < a * c → b < c :=
ordered_comm_monoid.lt_of_mul_lt_mul_left a b c

@[to_additive lt_of_add_lt_add_right]
lemma lt_of_mul_lt_mul_right' (h : a * b < c * b) : a < c :=
lt_of_mul_lt_mul_left'
  (show b * a < b * c, begin rw [mul_comm b a, mul_comm b c], assumption end)

@[to_additive add_le_add]
lemma mul_le_mul' (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
(mul_le_mul_right' h₁ _).trans $ mul_le_mul_left' h₂ _

@[to_additive]
lemma mul_le_mul_three {e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) : a * b * c ≤ d * e * f :=
mul_le_mul' (mul_le_mul' h₁ h₂) h₃

-- here we start using properties of one.
@[to_additive le_add_of_nonneg_right]
lemma le_mul_of_one_le_right' (h : 1 ≤ b) : a ≤ a * b :=
by simpa only [mul_one] using mul_le_mul_left' h a

@[to_additive le_add_of_nonneg_left]
lemma le_mul_of_one_le_left' (h : 1 ≤ b) : a ≤ b * a :=
by simpa only [one_mul] using mul_le_mul_right' h a

@[to_additive add_le_of_nonpos_right]
lemma mul_le_of_le_one_right' (h : b ≤ 1) : a * b ≤ a :=
by simpa only [mul_one] using mul_le_mul_left' h a

@[to_additive add_le_of_nonpos_left]
lemma mul_le_of_le_one_left' (h : b ≤ 1) : b * a ≤ a :=
by simpa only [one_mul] using mul_le_mul_right' h a

@[to_additive]
lemma lt_of_mul_lt_of_one_le_left (h : a * b < c) (hle : 1 ≤ b) : a < c :=
(le_mul_of_one_le_right' hle).trans_lt h

@[to_additive]
lemma lt_of_mul_lt_of_one_le_right (h : a * b < c) (hle : 1 ≤ a) : b < c :=
(le_mul_of_one_le_left' hle).trans_lt h

@[to_additive]
lemma le_of_mul_le_of_one_le_left (h : a * b ≤ c) (hle : 1 ≤ b) : a ≤ c :=
(le_mul_of_one_le_right' hle).trans h

@[to_additive]
lemma le_of_mul_le_of_one_le_right (h : a * b ≤ c) (hle : 1 ≤ a) : b ≤ c :=
(le_mul_of_one_le_left' hle).trans h

@[to_additive]
lemma lt_of_lt_mul_of_le_one_left (h : a < b * c) (hle : c ≤ 1) : a < b :=
h.trans_le (mul_le_of_le_one_right' hle)

@[to_additive]
lemma lt_of_lt_mul_of_le_one_right (h : a < b * c) (hle : b ≤ 1) : a < c :=
h.trans_le (mul_le_of_le_one_left' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_left (h : a ≤ b * c) (hle : c ≤ 1) : a ≤ b :=
h.trans (mul_le_of_le_one_right' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_right (h : a ≤ b * c) (hle : b ≤ 1) : a ≤ c :=
h.trans (mul_le_of_le_one_left' hle)

@[to_additive]
lemma le_mul_of_one_le_of_le (ha : 1 ≤ a) (hbc : b ≤ c) : b ≤ a * c :=
one_mul b ▸ mul_le_mul' ha hbc

@[to_additive]
lemma le_mul_of_le_of_one_le (hbc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
mul_one b ▸ mul_le_mul' hbc ha

@[to_additive add_nonneg]
lemma one_le_mul (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
le_mul_of_one_le_of_le ha hb

@[to_additive add_pos_of_pos_of_nonneg]
lemma one_lt_mul_of_lt_of_le' (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
lt_of_lt_of_le ha $ le_mul_of_one_le_right' hb

@[to_additive add_pos_of_nonneg_of_pos]
lemma one_lt_mul_of_le_of_lt' (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_of_lt_of_le hb $ le_mul_of_one_le_left' ha

@[to_additive add_pos]
lemma one_lt_mul' (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
one_lt_mul_of_lt_of_le' ha hb.le

@[to_additive add_nonpos]
lemma mul_le_one' (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
one_mul (1:α) ▸ (mul_le_mul' ha hb)

@[to_additive]
lemma mul_le_of_le_one_of_le' (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
one_mul c ▸ mul_le_mul' ha hbc

@[to_additive]
lemma mul_le_of_le_of_le_one' (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
mul_one c ▸ mul_le_mul' hbc ha

@[to_additive]
lemma mul_lt_one_of_lt_one_of_le_one' (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
(mul_le_of_le_of_le_one' le_rfl hb).trans_lt ha

@[to_additive]
lemma mul_lt_one_of_le_one_of_lt_one' (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
(mul_le_of_le_one_of_le' ha le_rfl).trans_lt hb

@[to_additive]
lemma mul_lt_one' (ha : a < 1) (hb : b < 1) : a * b < 1 :=
mul_lt_one_of_le_one_of_lt_one' ha.le hb

@[to_additive]
lemma lt_mul_of_one_le_of_lt' (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
hbc.trans_le $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_lt_of_one_le' (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
hbc.trans_le $ le_mul_of_one_le_right' ha

@[to_additive]
lemma lt_mul_of_one_lt_of_lt' (ha : 1 < a) (hbc : b < c) : b < a * c :=
lt_mul_of_one_le_of_lt' ha.le hbc

@[to_additive]
lemma lt_mul_of_lt_of_one_lt' (hbc : b < c) (ha : 1 < a) : b < c * a :=
lt_mul_of_lt_of_one_le' hbc ha.le

@[to_additive]
lemma mul_lt_of_le_one_of_lt' (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
lt_of_le_of_lt (mul_le_of_le_one_of_le' ha le_rfl) hbc

@[to_additive]
lemma mul_lt_of_lt_of_le_one' (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
lt_of_le_of_lt (mul_le_of_le_of_le_one' le_rfl ha) hbc

@[to_additive]
lemma mul_lt_of_lt_one_of_lt' (ha : a < 1) (hbc : b < c) : a * b < c :=
mul_lt_of_le_one_of_lt' ha.le hbc

@[to_additive]
lemma mul_lt_of_lt_of_lt_one' (hbc : b < c) (ha : a < 1) : b * a < c :=
mul_lt_of_lt_of_le_one' hbc ha.le

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

/-- Pullback an `ordered_comm_monoid` under an injective map. -/
@[to_additive function.injective.ordered_add_comm_monoid
"Pullback an `ordered_add_comm_monoid` under an injective map."]
def function.injective.ordered_comm_monoid {β : Type*}
  [has_one β] [has_mul β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  ordered_comm_monoid β :=
{ mul_le_mul_left := λ a b ab c,
    show f (c * a) ≤ f (c * b), by simp [mul, mul_le_mul_left' ab],
  lt_of_mul_lt_mul_left :=
    λ a b c bc, @lt_of_mul_lt_mul_left' _ _ (f a) _ _ (by rwa [← mul, ← mul]),
  ..partial_order.lift f hf,
  ..hf.comm_monoid f one mul }

section mono

variables {β : Type*} [preorder β] {f g : β → α}

@[to_additive monotone.add]
lemma monotone.mul' (hf : monotone f) (hg : monotone g) : monotone (λ x, f x * g x) :=
λ x y h, mul_le_mul' (hf h) (hg h)

@[to_additive monotone.add_const]
lemma monotone.mul_const' (hf : monotone f) (a : α) : monotone (λ x, f x * a) :=
hf.mul' monotone_const

@[to_additive monotone.const_add]
lemma monotone.const_mul' (hf : monotone f) (a : α) : monotone (λ x, a * f x) :=
monotone_const.mul' hf

end mono

end ordered_comm_monoid

/-- Pullback a `linear_ordered_comm_monoid` under an injective map. -/
@[to_additive function.injective.linear_ordered_add_comm_monoid
"Pullback an `ordered_add_comm_monoid` under an injective map."]
def function.injective.linear_ordered_comm_monoid [linear_ordered_comm_monoid α] {β : Type*}
  [has_one β] [has_mul β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  linear_ordered_comm_monoid β :=
{ .. hf.ordered_comm_monoid f one mul,
  .. linear_order.lift f hf }

lemma bit0_pos [ordered_add_comm_monoid α] {a : α} (h : 0 < a) : 0 < bit0 a :=
add_pos h h

namespace units

@[to_additive]
instance [monoid α] [preorder α] : preorder (units α) :=
preorder.lift (coe : units α → α)

@[simp, norm_cast, to_additive]
theorem coe_le_coe [monoid α] [preorder α] {a b : units α} :
  (a : α) ≤ b ↔ a ≤ b := iff.rfl

-- should `to_additive` do this?
attribute [norm_cast] add_units.coe_le_coe

@[simp, norm_cast, to_additive]
theorem coe_lt_coe [monoid α] [preorder α] {a b : units α} :
  (a : α) < b ↔ a < b := iff.rfl

attribute [norm_cast] add_units.coe_lt_coe

@[to_additive]
instance [monoid α] [partial_order α] : partial_order (units α) :=
partial_order.lift coe units.ext

@[to_additive]
instance [monoid α] [linear_order α] : linear_order (units α) :=
linear_order.lift coe units.ext

@[simp, norm_cast, to_additive]
theorem max_coe [monoid α] [linear_order α] {a b : units α} :
  (↑(max a b) : α) = max a b :=
by by_cases b ≤ a; simp [max, h]

attribute [norm_cast] add_units.max_coe

@[simp, norm_cast, to_additive]
theorem min_coe [monoid α] [linear_order α] {a b : units α} :
  (↑(min a b) : α) = min a b :=
by by_cases a ≤ b; simp [min, h]

attribute [norm_cast] add_units.min_coe

end units

namespace with_zero

local attribute [semireducible] with_zero

instance [preorder α] : preorder (with_zero α) := with_bot.preorder

instance [partial_order α] : partial_order (with_zero α) := with_bot.partial_order

instance [partial_order α] : order_bot (with_zero α) := with_bot.order_bot

lemma zero_le [partial_order α] (a : with_zero α) : 0 ≤ a := order_bot.bot_le a

lemma zero_lt_coe [partial_order α] (a : α) : (0 : with_zero α) < a := with_bot.bot_lt_coe a

@[simp, norm_cast] lemma coe_lt_coe [partial_order α] {a b : α} : (a : with_zero α) < b ↔ a < b :=
with_bot.coe_lt_coe

@[simp, norm_cast] lemma coe_le_coe [partial_order α] {a b : α} : (a : with_zero α) ≤ b ↔ a ≤ b :=
with_bot.coe_le_coe

instance [lattice α] : lattice (with_zero α) := with_bot.lattice

instance [linear_order α] : linear_order (with_zero α) := with_bot.linear_order

lemma mul_le_mul_left {α : Type u}
  [ordered_comm_monoid α] :
  ∀ (a b : with_zero α),
    a ≤ b → ∀ (c : with_zero α), c * a ≤ c * b :=
begin
  rintro (_ | a) (_ | b) h (_ | c),
  { apply with_zero.zero_le },
  { apply with_zero.zero_le },
  { apply with_zero.zero_le },
  { apply with_zero.zero_le },
  { apply with_zero.zero_le },
  { exact false.elim (not_lt_of_le h (with_zero.zero_lt_coe a))},
  { apply with_zero.zero_le },
  { simp_rw [some_eq_coe] at h ⊢,
    norm_cast at h ⊢,
    exact mul_le_mul_left' h c }
end

lemma lt_of_mul_lt_mul_left  {α : Type u}
  [ordered_comm_monoid α] :
  ∀ (a b c : with_zero α), a * b < a * c → b < c :=
begin
  rintro (_ | a) (_ | b) (_ | c) h,
  { exact false.elim (lt_irrefl none h) },
  { exact false.elim (lt_irrefl none h) },
  { exact false.elim (lt_irrefl none h) },
  { exact false.elim (lt_irrefl none h) },
  { exact false.elim (lt_irrefl none h) },
  { exact with_zero.zero_lt_coe c },
  { exact false.elim (not_le_of_lt h (with_zero.zero_le _)) },
  { simp_rw [some_eq_coe] at h ⊢,
    norm_cast at h ⊢,
    apply lt_of_mul_lt_mul_left' h }
end

instance [ordered_comm_monoid α] : ordered_comm_monoid (with_zero α) :=
{ mul_le_mul_left := with_zero.mul_le_mul_left,
  lt_of_mul_lt_mul_left := with_zero.lt_of_mul_lt_mul_left,
  ..with_zero.comm_monoid_with_zero,
  ..with_zero.partial_order
}

/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.

Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/

/--
If `0` is the least element in `α`, then `with_zero α` is an `ordered_add_comm_monoid`.
-/
def ordered_add_comm_monoid [ordered_add_comm_monoid α]
  (zero_le : ∀ a : α, 0 ≤ a) : ordered_add_comm_monoid (with_zero α) :=
begin
  suffices, refine {
    add_le_add_left := this,
    ..with_zero.partial_order,
    ..with_zero.add_comm_monoid, .. },
  { intros a b c h,
    have h' := lt_iff_le_not_le.1 h,
    rw lt_iff_le_not_le at ⊢,
    refine ⟨λ b h₂, _, λ h₂, h'.2 $ this _ _ h₂ _⟩,
    cases h₂, cases c with c,
    { cases h'.2 (this _ _ bot_le a) },
    { refine ⟨_, rfl, _⟩,
      cases a with a,
      { exact with_bot.some_le_some.1 h'.1 },
      { exact le_of_lt (lt_of_add_lt_add_left $
          with_bot.some_lt_some.1 h), } } },
  { intros a b h c ca h₂,
    cases b with b,
    { rw le_antisymm h bot_le at h₂,
      exact ⟨_, h₂, le_refl _⟩ },
    cases a with a,
    { change c + 0 = some ca at h₂,
      simp at h₂, simp [h₂],
      exact ⟨_, rfl, by simpa using add_le_add_left (zero_le b) _⟩ },
    { simp at h,
      cases c with c; change some _ = _ at h₂;
        simp [-add_comm] at h₂; subst ca; refine ⟨_, rfl, _⟩,
      { exact h },
      { exact add_le_add_left h _ } } }
end

end with_zero

namespace with_top

section has_one

variables [has_one α]

@[to_additive] instance : has_one (with_top α) := ⟨(1 : α)⟩

@[simp, to_additive] lemma coe_one : ((1 : α) : with_top α) = 1 := rfl

@[simp, to_additive] lemma coe_eq_one {a : α} : (a : with_top α) = 1 ↔ a = 1 :=
coe_eq_coe

@[simp, to_additive] theorem one_eq_coe {a : α} : 1 = (a : with_top α) ↔ a = 1 :=
by rw [eq_comm, coe_eq_one]

attribute [norm_cast] coe_one coe_eq_one coe_zero coe_eq_zero one_eq_coe zero_eq_coe

@[simp, to_additive] theorem top_ne_one : ⊤ ≠ (1 : with_top α) .
@[simp, to_additive] theorem one_ne_top : (1 : with_top α) ≠ ⊤ .

end has_one

instance [has_add α] : has_add (with_top α) :=
⟨λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a + b))⟩

local attribute [reducible] with_zero

instance [add_semigroup α] : add_semigroup (with_top α) :=
{ add := (+),
  add_assoc := by rintros ⟨_|_⟩ ⟨_|_⟩ ⟨_|_⟩; refl <|> exact congr_arg some (add_assoc _ _ _) }

@[norm_cast] lemma coe_add [has_add α] {a b : α} : ((a + b : α) : with_top α) = a + b := rfl

@[norm_cast] lemma coe_bit0 [has_add α] {a : α} : ((bit0 a : α) : with_top α) = bit0 a := rfl

@[norm_cast]
lemma coe_bit1 [has_add α] [has_one α] {a : α} : ((bit1 a : α) : with_top α) = bit1 a := rfl

@[simp] lemma add_top [has_add α] : ∀{a : with_top α}, a + ⊤ = ⊤
| none := rfl
| (some a) := rfl

@[simp] lemma top_add [has_add α] {a : with_top α} : ⊤ + a = ⊤ := rfl

lemma add_eq_top [has_add α] {a b : with_top α} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
by {cases a; cases b; simp [none_eq_top, some_eq_coe, ←with_top.coe_add, ←with_zero.coe_add]}

lemma add_lt_top [has_add α] [partial_order α] {a b : with_top α} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ :=
by simp [lt_top_iff_ne_top, add_eq_top, not_or_distrib]

lemma add_eq_coe [has_add α] : ∀ {a b : with_top α} {c : α},
  a + b = c ↔ ∃ (a' b' : α), ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
| none b c := by simp [none_eq_top]
| (some a) none c := by simp [none_eq_top]
| (some a) (some b) c :=
    by simp only [some_eq_coe, ← coe_add, coe_eq_coe, exists_and_distrib_left, exists_eq_left]

instance [add_comm_semigroup α] : add_comm_semigroup (with_top α) :=
{ add_comm := by rintros ⟨_|_⟩ ⟨_|_⟩; refl <|> exact congr_arg some (add_comm _ _),
  ..with_top.add_semigroup }

instance [add_monoid α] : add_monoid (with_top α) :=
{ zero := some 0,
  zero_add := by rintros ⟨_|_⟩; refl <|> exact congr_arg some (zero_add _),
  add_zero := by rintros ⟨_|_⟩; refl <|> exact congr_arg some (add_zero _),
  ..with_top.add_semigroup }

instance [add_comm_monoid α] : add_comm_monoid (with_top α) :=
{ ..with_top.add_monoid, ..with_top.add_comm_semigroup }

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (with_top α) :=
{ add_le_add_left :=
    begin
      rintros a b h (_|c), { simp [none_eq_top] },
      rcases b with (_|b), { simp [none_eq_top] },
      rcases le_coe_iff.1 h with ⟨a, rfl, h⟩,
      simp only [some_eq_coe, ← coe_add, coe_le_coe] at h ⊢,
      exact add_le_add_left h c
    end,
  lt_of_add_lt_add_left :=
    begin
      intros a b c h,
      rcases lt_iff_exists_coe.1 h with ⟨ab, hab, hlt⟩,
      rcases add_eq_coe.1 hab with ⟨a, b, rfl, rfl, rfl⟩,
      rw coe_lt_iff,
      rintro c rfl,
      exact lt_of_add_lt_add_left (coe_lt_coe.1 hlt)
    end,
  ..with_top.partial_order, ..with_top.add_comm_monoid }

instance [linear_ordered_add_comm_monoid α] :
  linear_ordered_add_comm_monoid_with_top (with_top α) :=
{ top_add' := λ x, with_top.top_add,
  ..with_top.order_top,
  ..with_top.linear_order,
  ..with_top.ordered_add_comm_monoid,
  ..option.nontrivial }

/-- Coercion from `α` to `with_top α` as an `add_monoid_hom`. -/
def coe_add_hom [add_monoid α] : α →+ with_top α :=
⟨coe, rfl, λ _ _, rfl⟩

@[simp] lemma coe_coe_add_hom [add_monoid α] : ⇑(coe_add_hom : α →+ with_top α) = coe := rfl

@[simp] lemma zero_lt_top [ordered_add_comm_monoid α] : (0 : with_top α) < ⊤ :=
coe_lt_top 0

@[simp, norm_cast] lemma zero_lt_coe [ordered_add_comm_monoid α] (a : α) :
  (0 : with_top α) < a ↔ 0 < a :=
coe_lt_coe

end with_top

namespace with_bot

instance [has_zero α] : has_zero (with_bot α) := with_top.has_zero
instance [has_one α] : has_one (with_bot α) := with_top.has_one
instance [add_semigroup α] : add_semigroup (with_bot α) := with_top.add_semigroup
instance [add_comm_semigroup α] : add_comm_semigroup (with_bot α) := with_top.add_comm_semigroup
instance [add_monoid α] : add_monoid (with_bot α) := with_top.add_monoid
instance [add_comm_monoid α] : add_comm_monoid (with_bot α) :=  with_top.add_comm_monoid

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (with_bot α) :=
begin
  suffices, refine {
    add_le_add_left := this,
    ..with_bot.partial_order,
    ..with_bot.add_comm_monoid, ..},
  { intros a b c h,
    have h' := h,
    rw lt_iff_le_not_le at h' ⊢,
    refine ⟨λ b h₂, _, λ h₂, h'.2 $ this _ _ h₂ _⟩,
    cases h₂, cases a with a,
    { exact (not_le_of_lt h).elim bot_le },
    cases c with c,
    { exact (not_le_of_lt h).elim bot_le },
    { exact ⟨_, rfl, le_of_lt (lt_of_add_lt_add_left $
        with_bot.some_lt_some.1 h)⟩ } },
  { intros a b h c ca h₂,
    cases c with c, {cases h₂},
    cases a with a; cases h₂,
    cases b with b, {cases le_antisymm h bot_le},
    simp at h,
    exact ⟨_, rfl, add_le_add_left h _⟩, }
end

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_zero [has_zero α] : ((0 : α) : with_bot α) = 0 := rfl

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_one [has_one α] : ((1 : α) : with_bot α) = 1 := rfl

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_eq_zero {α : Type*}
  [add_monoid α] {a : α} : (a : with_bot α) = 0 ↔ a = 0 :=
by norm_cast

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_add [add_semigroup α] (a b : α) : ((a + b : α) : with_bot α) = a + b := by norm_cast

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_bit0 [add_semigroup α] {a : α} : ((bit0 a : α) : with_bot α) = bit0 a :=
by norm_cast

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_bit1 [add_semigroup α] [has_one α] {a : α} : ((bit1 a : α) : with_bot α) = bit1 a :=
by norm_cast

@[simp] lemma bot_add [ordered_add_comm_monoid α] (a : with_bot α) : ⊥ + a = ⊥ := rfl

@[simp] lemma add_bot [ordered_add_comm_monoid α] (a : with_bot α) : a + ⊥ = ⊥ := by cases a; refl

end with_bot

/-- A canonically ordered additive monoid is an ordered commutative additive monoid
  in which the ordering coincides with the subtractibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
  This is satisfied by the natural numbers, for example, but not
  the integers or other nontrivial `ordered_add_comm_group`s. -/
@[protect_proj, ancestor ordered_add_comm_monoid order_bot]
class canonically_ordered_add_monoid (α : Type*) extends ordered_add_comm_monoid α, order_bot α :=
(le_iff_exists_add : ∀ a b : α, a ≤ b ↔ ∃ c, b = a + c)

/-- A canonically ordered monoid is an ordered commutative monoid
  in which the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a * c`.
  Example seem rare; it seems more likely that the `order_dual`
  of a naturally-occurring lattice satisfies this than the lattice
  itself (for example, dual of the lattice of ideals of a PID or
  Dedekind domain satisfy this; collections of all things ≤ 1 seem to
  be more natural that collections of all things ≥ 1).
-/
@[protect_proj, ancestor ordered_comm_monoid order_bot, to_additive]
class canonically_ordered_monoid (α : Type*) extends ordered_comm_monoid α, order_bot α :=
(le_iff_exists_mul : ∀ a b : α, a ≤ b ↔ ∃ c, b = a * c)

section canonically_ordered_monoid

variables [canonically_ordered_monoid α] {a b c d : α}

@[to_additive]
lemma le_iff_exists_mul : a ≤ b ↔ ∃c, b = a * c :=
canonically_ordered_monoid.le_iff_exists_mul a b

@[to_additive]
lemma self_le_mul_right (a b : α) : a ≤ a * b :=
le_iff_exists_mul.mpr ⟨b, rfl⟩

@[to_additive]
lemma self_le_mul_left (a b : α) : a ≤ b * a :=
by { rw [mul_comm], exact self_le_mul_right a b }

@[simp, to_additive zero_le] lemma one_le (a : α) : 1 ≤ a := le_iff_exists_mul.mpr ⟨a, by simp⟩

@[simp, to_additive] lemma bot_eq_one : (⊥ : α) = 1 :=
le_antisymm bot_le (one_le ⊥)

@[simp, to_additive] lemma mul_eq_one_iff : a * b = 1 ↔ a = 1 ∧ b = 1 :=
mul_eq_one_iff' (one_le _) (one_le _)

@[simp, to_additive] lemma le_one_iff_eq_one : a ≤ 1 ↔ a = 1 :=
iff.intro
  (assume h, le_antisymm h (one_le a))
  (assume h, h ▸ le_refl a)

@[to_additive] lemma one_lt_iff_ne_one : 1 < a ↔ a ≠ 1 :=
iff.intro ne_of_gt $ assume hne, lt_of_le_of_ne (one_le _) hne.symm

@[to_additive] lemma exists_pos_mul_of_lt (h : a < b) : ∃ c > 1, a * c = b :=
begin
  obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le,
  refine ⟨c, one_lt_iff_ne_one.2 _, hc.symm⟩,
  rintro rfl,
  simpa [hc, lt_irrefl] using h
end

@[to_additive] lemma le_mul_left (h : a ≤ c) : a ≤ b * c :=
calc a = 1 * a : by simp
  ... ≤ b * c : mul_le_mul' (one_le _) h

@[to_additive] lemma le_mul_right (h : a ≤ b) : a ≤ b * c :=
calc a = a * 1 : by simp
  ... ≤ b * c : mul_le_mul' h (one_le _)

local attribute [semireducible] with_zero

-- This instance looks absurd: a monoid already has a zero
/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
instance with_zero.canonically_ordered_add_monoid {α : Type u} [canonically_ordered_add_monoid α] :
  canonically_ordered_add_monoid (with_zero α) :=
{ le_iff_exists_add := λ a b, begin
    cases a with a,
    { exact iff_of_true bot_le ⟨b, (zero_add b).symm⟩ },
    cases b with b,
    { exact iff_of_false
        (mt (le_antisymm bot_le) (by simp))
        (λ ⟨c, h⟩, by cases c; cases h) },
    { simp [le_iff_exists_add, -add_comm],
      split; intro h; rcases h with ⟨c, h⟩,
      { exact ⟨some c, congr_arg some h⟩ },
      { cases c; cases h,
        { exact ⟨_, (add_zero _).symm⟩ },
        { exact ⟨_, rfl⟩ } } }
  end,
  bot    := 0,
  bot_le := assume a a' h, option.no_confusion h,
  .. with_zero.ordered_add_comm_monoid zero_le }

instance with_top.canonically_ordered_add_monoid {α : Type u} [canonically_ordered_add_monoid α] :
  canonically_ordered_add_monoid (with_top α) :=
{ le_iff_exists_add := assume a b,
  match a, b with
  | a, none     := show a ≤ ⊤ ↔ ∃c, ⊤ = a + c, by simp; refine ⟨⊤, _⟩; cases a; refl
  | (some a), (some b) := show (a:with_top α) ≤ ↑b ↔ ∃c:with_top α, ↑b = ↑a + c,
    begin
      simp [canonically_ordered_add_monoid.le_iff_exists_add, -add_comm],
      split,
      { rintro ⟨c, rfl⟩, refine ⟨c, _⟩, norm_cast },
      { exact assume h, match b, h with _, ⟨some c, rfl⟩ := ⟨_, rfl⟩ end }
    end
  | none, some b := show (⊤ : with_top α) ≤ b ↔ ∃c:with_top α, ↑b = ⊤ + c, by simp
  end,
  .. with_top.order_bot,
  .. with_top.ordered_add_comm_monoid }

end canonically_ordered_monoid

/-- A canonically linear-ordered additive monoid is a canonically ordered additive monoid
    whose ordering is a linear order. -/
@[protect_proj, ancestor canonically_ordered_add_monoid linear_order]
class canonically_linear_ordered_add_monoid (α : Type*)
      extends canonically_ordered_add_monoid α, linear_order α

/-- A canonically linear-ordered monoid is a canonically ordered monoid
    whose ordering is a linear order. -/
@[protect_proj, ancestor canonically_ordered_monoid linear_order, to_additive]
class canonically_linear_ordered_monoid (α : Type*)
      extends canonically_ordered_monoid α, linear_order α

section canonically_linear_ordered_monoid
variables

@[priority 100, to_additive]  -- see Note [lower instance priority]
instance canonically_linear_ordered_monoid.semilattice_sup_bot
  [canonically_linear_ordered_monoid α] : semilattice_sup_bot α :=
{ ..lattice_of_linear_order, ..canonically_ordered_monoid.to_order_bot α }

instance with_top.canonically_linear_ordered_add_monoid
  (α : Type*) [canonically_linear_ordered_add_monoid α] :
    canonically_linear_ordered_add_monoid (with_top α) :=
{ .. (infer_instance : canonically_ordered_add_monoid (with_top α)),
  .. (infer_instance : linear_order (with_top α)) }

@[to_additive] lemma min_mul_distrib [canonically_linear_ordered_monoid α] (a b c : α) :
  min a (b * c) = min a (min a b * min a c) :=
begin
  cases le_total a b with hb hb,
  { simp [hb, le_mul_right] },
  { cases le_total a c with hc hc,
    { simp [hc, le_mul_left] },
    { simp [hb, hc] } }
end

@[to_additive] lemma min_mul_distrib' [canonically_linear_ordered_monoid α] (a b c : α) :
  min (a * b) c = min (min a c * min b c) c :=
by simpa [min_comm _ c] using min_mul_distrib c a b

end canonically_linear_ordered_monoid

/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and monotone. -/
@[protect_proj, ancestor add_cancel_comm_monoid partial_order]
class ordered_cancel_add_comm_monoid (α : Type u)
      extends add_cancel_comm_monoid α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c)

/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and monotone. -/
@[protect_proj, ancestor cancel_comm_monoid partial_order, to_additive]
class ordered_cancel_comm_monoid (α : Type u)
      extends cancel_comm_monoid α, partial_order α :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c)

section ordered_cancel_comm_monoid
variables [ordered_cancel_comm_monoid α] {a b c d : α}

@[to_additive le_of_add_le_add_left]
lemma le_of_mul_le_mul_left' : ∀ {a b c : α}, a * b ≤ a * c → b ≤ c :=
ordered_cancel_comm_monoid.le_of_mul_le_mul_left

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance ordered_cancel_comm_monoid.to_ordered_comm_monoid : ordered_comm_monoid α :=
{ lt_of_mul_lt_mul_left := λ a b c h, lt_of_le_not_le (le_of_mul_le_mul_left' h.le) $
      mt (λ h, ordered_cancel_comm_monoid.mul_le_mul_left _ _ h _) (not_le_of_gt h),
  ..‹ordered_cancel_comm_monoid α› }

@[to_additive add_lt_add_left]
lemma mul_lt_mul_left' (h : a < b) (c : α) : c * a < c * b :=
lt_of_le_not_le (mul_le_mul_left' h.le _) $
  mt le_of_mul_le_mul_left' (not_le_of_gt h)

@[to_additive add_lt_add_right]
lemma mul_lt_mul_right' (h : a < b) (c : α) : a * c < b * c :=
begin
 rw [mul_comm a c, mul_comm b c],
 exact (mul_lt_mul_left' h c)
end

@[to_additive add_lt_add]
lemma mul_lt_mul''' (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
lt_trans (mul_lt_mul_right' h₁ c) (mul_lt_mul_left' h₂ b)

@[to_additive]
lemma mul_lt_mul_of_le_of_lt (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
lt_of_le_of_lt (mul_le_mul_right' h₁ _) (mul_lt_mul_left' h₂ b)

@[to_additive]
lemma mul_lt_mul_of_lt_of_le (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
lt_of_lt_of_le (mul_lt_mul_right' h₁ c) (mul_le_mul_left' h₂ _)

@[to_additive lt_add_of_pos_right]
lemma lt_mul_of_one_lt_right' (a : α) {b : α} (h : 1 < b) : a < a * b :=
have a * 1 < a * b, from mul_lt_mul_left' h a,
by rwa [mul_one] at this

@[to_additive lt_add_of_pos_left]
lemma lt_mul_of_one_lt_left' (a : α) {b : α} (h : 1 < b) : a < b * a :=
have 1 * a < b * a, from mul_lt_mul_right' h a,
by rwa [one_mul] at this

@[to_additive le_of_add_le_add_right]
lemma le_of_mul_le_mul_right' (h : a * b ≤ c * b) : a ≤ c :=
le_of_mul_le_mul_left'
  (show b * a ≤ b * c, begin rw [mul_comm b a, mul_comm b c], assumption end)

@[to_additive]
lemma mul_lt_one (ha : a < 1) (hb : b < 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul''' ha hb)

@[to_additive]
lemma mul_lt_one_of_lt_one_of_le_one (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul_of_lt_of_le ha hb)

@[to_additive]
lemma mul_lt_one_of_le_one_of_lt_one (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul_of_le_of_lt ha hb)

@[to_additive]
lemma lt_mul_of_one_lt_of_le (ha : 1 < a) (hbc : b ≤ c) : b < a * c :=
one_mul b ▸ mul_lt_mul_of_lt_of_le ha hbc

@[to_additive]
lemma lt_mul_of_le_of_one_lt (hbc : b ≤ c) (ha : 1 < a) : b < c * a :=
mul_one b ▸ mul_lt_mul_of_le_of_lt hbc ha

@[to_additive]
lemma mul_le_of_le_one_of_le (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
one_mul c ▸ mul_le_mul' ha hbc

@[to_additive]
lemma mul_le_of_le_of_le_one (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
mul_one c ▸ mul_le_mul' hbc ha

@[to_additive]
lemma mul_lt_of_lt_one_of_le (ha : a < 1) (hbc : b ≤ c) : a * b < c :=
one_mul c ▸ mul_lt_mul_of_lt_of_le ha hbc

@[to_additive]
lemma mul_lt_of_le_of_lt_one (hbc : b ≤ c) (ha : a < 1) : b * a < c :=
mul_one c ▸ mul_lt_mul_of_le_of_lt hbc ha

@[to_additive]
lemma lt_mul_of_one_le_of_lt (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
one_mul b ▸ mul_lt_mul_of_le_of_lt ha hbc

@[to_additive]
lemma lt_mul_of_lt_of_one_le (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
mul_one b ▸ mul_lt_mul_of_lt_of_le hbc ha

@[to_additive]
lemma lt_mul_of_one_lt_of_lt (ha : 1 < a) (hbc : b < c) : b < a * c :=
one_mul b ▸ mul_lt_mul''' ha hbc

@[to_additive]
lemma lt_mul_of_lt_of_one_lt (hbc : b < c) (ha : 1 < a) : b < c * a :=
mul_one b ▸ mul_lt_mul''' hbc ha

@[to_additive]
lemma mul_lt_of_le_one_of_lt (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
one_mul c ▸ mul_lt_mul_of_le_of_lt ha hbc

@[to_additive]
lemma mul_lt_of_lt_of_le_one (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
mul_one c ▸ mul_lt_mul_of_lt_of_le hbc ha

@[to_additive]
lemma mul_lt_of_lt_one_of_lt (ha : a < 1) (hbc : b < c) : a * b < c :=
one_mul c ▸ mul_lt_mul''' ha hbc

@[to_additive]
lemma mul_lt_of_lt_of_lt_one (hbc : b < c) (ha : a < 1) : b * a < c :=
mul_one c ▸ mul_lt_mul''' hbc ha

@[simp, to_additive]
lemma mul_le_mul_iff_left (a : α) {b c : α} : a * b ≤ a * c ↔ b ≤ c :=
⟨le_of_mul_le_mul_left', λ h, mul_le_mul_left' h _⟩

@[simp, to_additive]
lemma mul_le_mul_iff_right (c : α) : a * c ≤ b * c ↔ a ≤ b :=
mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_iff_left c

@[simp, to_additive]
lemma mul_lt_mul_iff_left (a : α) {b c : α} : a * b < a * c ↔ b < c :=
⟨lt_of_mul_lt_mul_left', λ h, mul_lt_mul_left' h _⟩

@[simp, to_additive]
lemma mul_lt_mul_iff_right (c : α) : a * c < b * c ↔ a < b :=
mul_comm c a ▸ mul_comm c b ▸ mul_lt_mul_iff_left c

@[simp, to_additive le_add_iff_nonneg_right]
lemma le_mul_iff_one_le_right' (a : α) {b : α} : a ≤ a * b ↔ 1 ≤ b :=
have a * 1 ≤ a * b ↔ 1 ≤ b, from mul_le_mul_iff_left a,
by rwa mul_one at this

@[simp, to_additive le_add_iff_nonneg_left]
lemma le_mul_iff_one_le_left' (a : α) {b : α} : a ≤ b * a ↔ 1 ≤ b :=
by rw [mul_comm, le_mul_iff_one_le_right']

@[simp, to_additive lt_add_iff_pos_right]
lemma lt_mul_iff_one_lt_right' (a : α) {b : α} : a < a * b ↔ 1 < b :=
have a * 1 < a * b ↔ 1 < b, from mul_lt_mul_iff_left a,
by rwa mul_one at this

@[simp, to_additive lt_add_iff_pos_left]
lemma lt_mul_iff_one_lt_left' (a : α) {b : α} : a < b * a ↔ 1 < b :=
by rw [mul_comm, lt_mul_iff_one_lt_right']

@[simp, to_additive add_le_iff_nonpos_left]
lemma mul_le_iff_le_one_left' : a * b ≤ b ↔ a ≤ 1 :=
by { convert mul_le_mul_iff_right b, rw [one_mul] }

@[simp, to_additive add_le_iff_nonpos_right]
lemma mul_le_iff_le_one_right' : a * b ≤ a ↔ b ≤ 1 :=
by { convert mul_le_mul_iff_left a, rw [mul_one] }

@[simp, to_additive add_lt_iff_neg_right]
lemma mul_lt_iff_lt_one_right' : a * b < b ↔ a < 1 :=
by { convert mul_lt_mul_iff_right b, rw [one_mul] }

@[simp, to_additive add_lt_iff_neg_left]
lemma mul_lt_iff_lt_one_left' : a * b < a ↔ b < 1 :=
by { convert mul_lt_mul_iff_left a, rw [mul_one] }

@[to_additive]
lemma mul_eq_one_iff_eq_one_of_one_le
  (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
⟨λ hab : a * b = 1,
by split; apply le_antisymm; try {assumption};
   rw ← hab; simp [ha, hb],
λ ⟨ha', hb'⟩, by rw [ha', hb', mul_one]⟩

/-- Pullback an `ordered_cancel_comm_monoid` under an injective map. -/
@[to_additive function.injective.ordered_cancel_add_comm_monoid
"Pullback an `ordered_cancel_add_comm_monoid` under an injective map."]
def function.injective.ordered_cancel_comm_monoid {β : Type*}
  [has_one β] [has_mul β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  ordered_cancel_comm_monoid β :=
{ le_of_mul_le_mul_left := λ a b c (ab : f (a * b) ≤ f (a * c)),
    (by { rw [mul, mul] at ab, exact le_of_mul_le_mul_left' ab }),
  ..hf.left_cancel_semigroup f mul,
  ..hf.right_cancel_semigroup f mul,
  ..hf.ordered_comm_monoid f one mul }

section mono

variables {β : Type*} [preorder β] {f g : β → α}

@[to_additive monotone.add_strict_mono]
lemma monotone.mul_strict_mono' (hf : monotone f) (hg : strict_mono g) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul_of_le_of_lt (hf $ le_of_lt h) (hg h)

@[to_additive strict_mono.add_monotone]
lemma strict_mono.mul_monotone' (hf : strict_mono f) (hg : monotone g) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul_of_lt_of_le (hf h) (hg $ le_of_lt h)

@[to_additive strict_mono.add_const]
lemma strict_mono.mul_const' (hf : strict_mono f) (c : α) :
  strict_mono (λ x, f x * c) :=
hf.mul_monotone' monotone_const

@[to_additive strict_mono.const_add]
lemma strict_mono.const_mul' (hf : strict_mono f) (c : α) :
  strict_mono (λ x, c * f x) :=
monotone_const.mul_strict_mono' hf

end mono

end ordered_cancel_comm_monoid

section ordered_cancel_add_comm_monoid

variable [ordered_cancel_add_comm_monoid α]

lemma with_top.add_lt_add_iff_left :
  ∀{a b c : with_top α}, a < ⊤ → (a + c < a + b ↔ c < b)
| none := assume b c h, (lt_irrefl ⊤ h).elim
| (some a) :=
  begin
    assume b c h,
    cases b; cases c;
      simp [with_top.none_eq_top, with_top.some_eq_coe, with_top.coe_lt_top, with_top.coe_lt_coe],
    { norm_cast, exact with_top.coe_lt_top _ },
    { norm_cast, exact add_lt_add_iff_left _ }
  end

lemma with_bot.add_lt_add_iff_left :
  ∀{a b c : with_bot α}, ⊥ < a → (a + c < a + b ↔ c < b)
| none := assume b c h, (lt_irrefl ⊥ h).elim
| (some a) :=
  begin
    assume b c h,
    cases b; cases c;
      simp [with_bot.none_eq_bot, with_bot.some_eq_coe, with_bot.bot_lt_coe, with_bot.coe_lt_coe],
    { norm_cast, exact with_bot.bot_lt_coe _ },
    { norm_cast, exact add_lt_add_iff_left _ }
  end

local attribute [reducible] with_zero

lemma with_top.add_lt_add_iff_right
  {a b c : with_top α} : a < ⊤ → (c + a < b + a ↔ c < b) :=
by simpa [add_comm] using @with_top.add_lt_add_iff_left _ _ a b c

lemma with_bot.add_lt_add_iff_right
  {a b c : with_bot α} : ⊥ < a → (c + a < b + a ↔ c < b) :=
by simpa [add_comm] using @with_bot.add_lt_add_iff_left _ _ a b c

end ordered_cancel_add_comm_monoid

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/
@[to_additive]
lemma fn_min_mul_fn_max {β} [linear_order α] [comm_semigroup β] (f : α → β) (n m : α) :
  f (min n m) * f (max n m) = f n * f m :=
by { cases le_total n m with h h; simp [h, mul_comm] }

@[to_additive]
lemma min_mul_max [linear_order α] [comm_semigroup α] (n m : α) :
  min n m * max n m = n * m :=
fn_min_mul_fn_max id n m

/-- A linearly ordered cancellative additive commutative monoid
is an additive commutative monoid with a decidable linear order
in which addition is cancellative and monotone. -/
@[protect_proj, ancestor ordered_cancel_add_comm_monoid linear_ordered_add_comm_monoid]
class linear_ordered_cancel_add_comm_monoid (α : Type u)
  extends ordered_cancel_add_comm_monoid α, linear_ordered_add_comm_monoid α

/-- A linearly ordered cancellative commutative monoid
is a commutative monoid with a linear order
in which multiplication is cancellative and monotone. -/
@[protect_proj, ancestor ordered_cancel_comm_monoid linear_ordered_comm_monoid, to_additive]
class linear_ordered_cancel_comm_monoid (α : Type u)
  extends ordered_cancel_comm_monoid α, linear_ordered_comm_monoid α

section linear_ordered_cancel_comm_monoid

variables [linear_ordered_cancel_comm_monoid α]

@[to_additive] lemma min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c :=
(monotone_id.const_mul' a).map_min.symm

@[to_additive]
lemma min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c :=
(monotone_id.mul_const' c).map_min.symm

@[to_additive]
lemma max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
(monotone_id.const_mul' a).map_max.symm

@[to_additive]
lemma max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
(monotone_id.mul_const' c).map_max.symm

@[to_additive]
lemma min_le_mul_of_one_le_right {a b : α} (hb : 1 ≤ b) : min a b ≤ a * b :=
min_le_iff.2 $ or.inl $ le_mul_of_one_le_right' hb

@[to_additive]
lemma min_le_mul_of_one_le_left {a b : α} (ha : 1 ≤ a) : min a b ≤ a * b :=
min_le_iff.2 $ or.inr $ le_mul_of_one_le_left' ha

@[to_additive]
lemma max_le_mul_of_one_le {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : max a b ≤ a * b :=
max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

/-- Pullback a `linear_ordered_cancel_comm_monoid` under an injective map. -/
@[to_additive function.injective.linear_ordered_cancel_add_comm_monoid
"Pullback a `linear_ordered_cancel_add_comm_monoid` under an injective map."]
def function.injective.linear_ordered_cancel_comm_monoid {β : Type*}
  [has_one β] [has_mul β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  linear_ordered_cancel_comm_monoid β :=
{ ..hf.linear_ordered_comm_monoid f one mul,
  ..hf.ordered_cancel_comm_monoid f one mul }

end linear_ordered_cancel_comm_monoid

namespace order_dual

@[to_additive]
instance [ordered_comm_monoid α] : ordered_comm_monoid (order_dual α) :=
{ mul_le_mul_left := λ a b h c, @mul_le_mul_left' α _ b a h _,
  lt_of_mul_lt_mul_left := λ a b c h, @lt_of_mul_lt_mul_left' α _ a c b h,
  ..order_dual.partial_order α,
  ..show comm_monoid α, by apply_instance }


@[to_additive]
instance [ordered_cancel_comm_monoid α] : ordered_cancel_comm_monoid (order_dual α) :=
{ le_of_mul_le_mul_left := λ a b c : α, le_of_mul_le_mul_left',
  mul_left_cancel := @mul_left_cancel α _,
  mul_right_cancel := @mul_right_cancel α _,
  ..order_dual.ordered_comm_monoid }

@[to_additive]
instance [linear_ordered_cancel_comm_monoid α] :
  linear_ordered_cancel_comm_monoid (order_dual α) :=
{ .. order_dual.linear_order α,
  .. order_dual.ordered_cancel_comm_monoid }

end order_dual

namespace prod

variables {M N : Type*}

@[to_additive]
instance [ordered_cancel_comm_monoid M] [ordered_cancel_comm_monoid N] :
  ordered_cancel_comm_monoid (M × N) :=
{ mul_le_mul_left := λ a b h c, ⟨mul_le_mul_left' h.1 _, mul_le_mul_left' h.2 _⟩,
  le_of_mul_le_mul_left := λ a b c h, ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩,
 .. prod.comm_monoid, .. prod.left_cancel_semigroup, .. prod.right_cancel_semigroup,
 .. prod.partial_order M N }

end prod

section type_tags
open multiplicative additive

@[simps]
instance [preorder α] : preorder (multiplicative α) :=
{ le := λ x y, x.to_add ≤ y.to_add,
  lt := λ x y, x.to_add < y.to_add,
  lt_iff_le_not_le := by { equiv_rw multiplicative.to_add, simpa using @lt_iff_le_not_le _ _ },
  le_refl := by { equiv_rw multiplicative.to_add, simpa using le_refl },
  le_trans := by { equiv_rw multiplicative.to_add, simpa using @le_trans _ _ } }

@[simps]
instance [preorder α] : preorder (additive α) :=
{ le := λ x y, x.to_mul ≤ y.to_mul,
  lt := λ x y, x.to_mul < y.to_mul,
  lt_iff_le_not_le := by { equiv_rw additive.to_mul, simpa using @lt_iff_le_not_le _ _ },
  le_refl := by { equiv_rw additive.to_mul, simpa using le_refl },
  le_trans := by { equiv_rw additive.to_mul, simpa using @le_trans _ _ } }

instance [partial_order α] : partial_order (multiplicative α) :=
{ le_antisymm := by { equiv_rw multiplicative.to_add, simpa using @le_antisymm _ _ },
  ..multiplicative.preorder }

instance [partial_order α] : partial_order (additive α) :=
{ le_antisymm := by { equiv_rw additive.to_mul, simpa using @le_antisymm _ _ },
  ..additive.preorder }

instance [linear_order α] : linear_order (multiplicative α) :=
{ le_total := by { equiv_rw multiplicative.to_add, simpa using @le_total _ _ },
  decidable_le := λ _ _, by { simp, apply_instance },
  ..multiplicative.partial_order }

@[simp]
lemma multiplicative.to_add_max [linear_order α] {a b : multiplicative α} :
  to_add (max a b) = max (to_add a) (to_add b) :=
by simp [max]; split_ifs; refl

@[simp]
lemma multiplicative.of_add_max [linear_order α] {a b : α} :
  of_add (max a b) = max (of_add a) (of_add b) :=
by simp [max]; split_ifs; refl

@[simp]
lemma multiplicative.to_add_min [linear_order α] {a b : multiplicative α} :
  to_add (min a b) = min (to_add a) (to_add b) :=
by simp [min]; split_ifs; refl

@[simp]
lemma multiplicative.of_add_min [linear_order α] {a b : α} :
  of_add (min a b) = min (of_add a) (of_add b) :=
by simp [min]; split_ifs; refl

instance [linear_order α] : linear_order (additive α) :=
{ le_total := by { equiv_rw additive.to_mul, simpa using @le_total _ _ },
  decidable_le := λ _ _, by { simp, apply_instance },
  ..additive.partial_order }

@[simp]
lemma additive.to_mul_max [linear_order α] {a b : additive α} :
  to_mul (max a b) = max (to_mul a) (to_mul b) :=
by simp [max]; split_ifs; refl

@[simp]
lemma additive.of_mul_max [linear_order α] {a b : α} :
  of_mul (max a b) = max (of_mul a) (of_mul b) :=
by simp [max]; split_ifs; refl

@[simp]
lemma additive.to_mul_min [linear_order α] {a b : additive α} :
  to_mul (min a b) = min (to_mul a) (to_mul b) :=
by simp [min]; split_ifs; refl

@[simp]
lemma additive.of_mul_min [linear_order α] {a b : α} :
  of_mul (min a b) = min (of_mul a) (of_mul b) :=
by simp [min]; split_ifs; refl

instance [ordered_add_comm_monoid α] : ordered_comm_monoid (multiplicative α) :=
{ mul_le_mul_left := begin
    equiv_rw multiplicative.to_add,
    intros x y h, equiv_rw multiplicative.to_add, revert x y, -- TODO: equiv_rw bug
    simpa using @add_le_add_left _ _
  end,
  lt_of_mul_lt_mul_left := begin
    equiv_rw multiplicative.to_add,
    simpa using @lt_of_add_lt_add_left _ _
  end,
  ..multiplicative.partial_order,
  ..multiplicative.comm_monoid }

instance [ordered_comm_monoid α] : ordered_add_comm_monoid (additive α) :=
{ add_le_add_left := begin
    equiv_rw additive.to_mul,
    intros x y h, equiv_rw additive.to_mul, revert x y, -- TODO: equiv_rw bug
    simpa using @mul_le_mul_left' _ _
  end,
  lt_of_add_lt_add_left := begin
    equiv_rw additive.to_mul,
    simpa using @lt_of_mul_lt_mul_left' _ _
  end,
  ..additive.partial_order,
  ..additive.add_comm_monoid }

instance [ordered_cancel_add_comm_monoid α] : ordered_cancel_comm_monoid (multiplicative α) :=
{ le_of_mul_le_mul_left := by { equiv_rw multiplicative.to_add, simp },
  ..multiplicative.right_cancel_semigroup,
  ..multiplicative.left_cancel_semigroup,
  ..multiplicative.ordered_comm_monoid }

instance [ordered_cancel_comm_monoid α] : ordered_cancel_add_comm_monoid (additive α) :=
{ le_of_add_le_add_left := by { equiv_rw additive.to_mul, simp },
  ..additive.add_right_cancel_semigroup,
  ..additive.add_left_cancel_semigroup,
  ..additive.ordered_add_comm_monoid }

instance [linear_ordered_add_comm_monoid α] : linear_ordered_comm_monoid (multiplicative α) :=
{ ..multiplicative.linear_order,
  ..multiplicative.ordered_comm_monoid }

instance [linear_ordered_comm_monoid α] : linear_ordered_add_comm_monoid (additive α) :=
{ ..additive.linear_order,
  ..additive.ordered_add_comm_monoid }

end type_tags
