/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.group.units
import algebra.group.with_one
import algebra.group.type_tags
import order.bounded_lattice

set_option old_structure_cmd true
set_option default_priority 100 -- see Note [default priority]

/-!
# Ordered monoids and groups
-/

universe u
variable {α : Type u}

/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that addition is an order embedding, i.e.
  `a + b ≤ a + c ↔ b ≤ c`. These monoids are automatically cancellative. -/
class ordered_add_comm_monoid (α : Type*) extends add_comm_monoid α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(lt_of_add_lt_add_left : ∀ a b c : α, a + b < a + c → b < c)

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid α] {a b c d : α}

lemma add_le_add_left' (h : a ≤ b) : c + a ≤ c + b :=
ordered_add_comm_monoid.add_le_add_left a b h c

lemma add_le_add_right' (h : a ≤ b) : a + c ≤ b + c :=
add_comm c a ▸ add_comm c b ▸ add_le_add_left' h

lemma lt_of_add_lt_add_left' : a + b < a + c → b < c :=
ordered_add_comm_monoid.lt_of_add_lt_add_left a b c

lemma add_le_add' (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
le_trans (add_le_add_right' h₁) (add_le_add_left' h₂)

lemma le_add_of_nonneg_right' (h : 0 ≤ b) : a ≤ a + b :=
have a + b ≥ a + 0, from add_le_add_left' h,
by rwa add_zero at this

lemma le_add_of_nonneg_left' (h : 0 ≤ b) : a ≤ b + a :=
have 0 + a ≤ b + a, from add_le_add_right' h,
by rwa zero_add at this

lemma lt_of_add_lt_add_right' (h : a + b < c + b) : a < c :=
lt_of_add_lt_add_left'
  (show b + a < b + c, begin rw [add_comm b a, add_comm b c], assumption end)

-- here we start using properties of zero.
lemma le_add_of_nonneg_of_le' (ha : 0 ≤ a) (hbc : b ≤ c) : b ≤ a + c :=
zero_add b ▸ add_le_add' ha hbc

lemma le_add_of_le_of_nonneg' (hbc : b ≤ c) (ha : 0 ≤ a) : b ≤ c + a :=
add_zero b ▸ add_le_add' hbc ha

lemma add_nonneg' (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
le_add_of_nonneg_of_le' ha hb

lemma add_pos_of_pos_of_nonneg' (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
lt_of_lt_of_le ha $ le_add_of_nonneg_right' hb

lemma add_pos' (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
add_pos_of_pos_of_nonneg' ha $ le_of_lt hb

lemma add_pos_of_nonneg_of_pos' (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
lt_of_lt_of_le hb $ le_add_of_nonneg_left' ha

lemma add_nonpos' (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
zero_add (0:α) ▸ (add_le_add' ha hb)

lemma add_le_of_nonpos_of_le' (ha : a ≤ 0) (hbc : b ≤ c) : a + b ≤ c :=
zero_add c ▸ add_le_add' ha hbc

lemma add_le_of_le_of_nonpos' (hbc : b ≤ c) (ha : a ≤ 0) : b + a ≤ c :=
add_zero c ▸ add_le_add' hbc ha

lemma add_neg_of_neg_of_nonpos' (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
lt_of_le_of_lt (add_le_of_le_of_nonpos' (le_refl _) hb) ha

lemma add_neg_of_nonpos_of_neg' (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
lt_of_le_of_lt (add_le_of_nonpos_of_le' ha (le_refl _)) hb

lemma add_neg' (ha : a < 0) (hb : b < 0) : a + b < 0 :=
add_neg_of_nonpos_of_neg' (le_of_lt ha) hb

lemma lt_add_of_nonneg_of_lt' (ha : 0 ≤ a) (hbc : b < c) : b < a + c :=
lt_of_lt_of_le hbc $ le_add_of_nonneg_left' ha

lemma lt_add_of_lt_of_nonneg' (hbc : b < c) (ha : 0 ≤ a) : b < c + a :=
lt_of_lt_of_le hbc $ le_add_of_nonneg_right' ha

lemma lt_add_of_pos_of_lt' (ha : 0 < a) (hbc : b < c) : b < a + c :=
lt_add_of_nonneg_of_lt' (le_of_lt ha) hbc

lemma lt_add_of_lt_of_pos' (hbc : b < c) (ha : 0 < a) : b < c + a :=
lt_add_of_lt_of_nonneg' hbc (le_of_lt ha)

lemma add_lt_of_nonpos_of_lt' (ha : a ≤ 0) (hbc : b < c) : a + b < c :=
lt_of_le_of_lt (add_le_of_nonpos_of_le' ha (le_refl _)) hbc

lemma add_lt_of_lt_of_nonpos' (hbc : b < c) (ha : a ≤ 0)  : b + a < c :=
lt_of_le_of_lt (add_le_of_le_of_nonpos' (le_refl _) ha) hbc

lemma add_lt_of_neg_of_lt' (ha : a < 0) (hbc : b < c) : a + b < c :=
add_lt_of_nonpos_of_lt' (le_of_lt ha) hbc

lemma add_lt_of_lt_of_neg' (hbc : b < c) (ha : a < 0) : b + a < c :=
add_lt_of_lt_of_nonpos' hbc (le_of_lt ha)

lemma add_eq_zero_iff' (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b = 0 ↔ a = 0 ∧ b = 0 :=
iff.intro
  (assume hab : a + b = 0,
   have a ≤ 0, from hab ▸ le_add_of_le_of_nonneg' (le_refl _) hb,
   have a = 0, from le_antisymm this ha,
   have b ≤ 0, from hab ▸ le_add_of_nonneg_of_le' ha (le_refl _),
   have b = 0, from le_antisymm this hb,
   and.intro ‹a = 0› ‹b = 0›)
  (assume ⟨ha', hb'⟩, by rw [ha', hb', add_zero])

lemma bit0_pos {a : α} (h : 0 < a) : 0 < bit0 a :=
add_pos' h h

section mono

variables {β : Type*} [preorder β] {f g : β → α}

lemma monotone.add (hf : monotone f) (hg : monotone g) : monotone (λ x, f x + g x) :=
λ x y h, add_le_add' (hf h) (hg h)

lemma monotone.add_const (hf : monotone f) (a : α) : monotone (λ x, f x + a) :=
hf.add monotone_const

lemma monotone.const_add (hf : monotone f) (a : α) : monotone (λ x, a + f x) :=
monotone_const.add hf

end mono

end ordered_add_comm_monoid

namespace units

instance [monoid α] [i : preorder α] : preorder (units α) :=
preorder.lift (coe : units α → α) i

@[simp] theorem coe_le_coe [monoid α] [preorder α] {a b : units α} :
  (a : α) ≤ b ↔ a ≤ b := iff.rfl

@[simp] theorem coe_lt_coe [monoid α] [preorder α] {a b : units α} :
  (a : α) < b ↔ a < b := iff.rfl

instance [monoid α] [i : partial_order α] : partial_order (units α) :=
partial_order.lift (coe : units α → α) (by ext) i

instance [monoid α] [i : linear_order α] : linear_order (units α) :=
linear_order.lift (coe : units α → α) (by ext) i

instance [monoid α] [i : decidable_linear_order α] : decidable_linear_order (units α) :=
decidable_linear_order.lift (coe : units α → α) (by ext) i

theorem max_coe [monoid α] [decidable_linear_order α] {a b : units α} :
  (↑(max a b) : α) = max a b :=
by by_cases a ≤ b; simp [max, h]

theorem min_coe [monoid α] [decidable_linear_order α] {a b : units α} :
  (↑(min a b) : α) = min a b :=
by by_cases a ≤ b; simp [min, h]

end units

namespace with_zero

instance [preorder α] : preorder (with_zero α) := with_bot.preorder
instance [partial_order α] : partial_order (with_zero α) := with_bot.partial_order
instance [partial_order α] : order_bot (with_zero α) := with_bot.order_bot
instance [lattice α] : lattice (with_zero α) := with_bot.lattice
instance [linear_order α] : linear_order (with_zero α) := with_bot.linear_order
instance [decidable_linear_order α] :
 decidable_linear_order (with_zero α) := with_bot.decidable_linear_order

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
      { exact le_of_lt (lt_of_add_lt_add_left' $
          with_bot.some_lt_some.1 h), } } },
  { intros a b h c ca h₂,
    cases b with b,
    { rw le_antisymm h bot_le at h₂,
      exact ⟨_, h₂, le_refl _⟩ },
    cases a with a,
    { change c + 0 = some ca at h₂,
      simp at h₂, simp [h₂],
      exact ⟨_, rfl, by simpa using add_le_add_left' (zero_le b)⟩ },
    { simp at h,
      cases c with c; change some _ = _ at h₂;
        simp [-add_comm] at h₂; subst ca; refine ⟨_, rfl, _⟩,
      { exact h },
      { exact add_le_add_left' h } } }
end

end with_zero

namespace with_top

instance [add_semigroup α] : add_semigroup (with_top α) :=
{ add := λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a + b)),
  ..@additive.add_semigroup _ $ @with_zero.semigroup (multiplicative α) _ }

lemma coe_add [add_semigroup α] {a b : α} : ((a + b : α) : with_top α) = a + b := rfl

instance [add_comm_semigroup α] : add_comm_semigroup (with_top α) :=
{ ..@additive.add_comm_semigroup _ $
    @with_zero.comm_semigroup (multiplicative α) _ }

instance [add_monoid α] : add_monoid (with_top α) :=
{ zero := some 0,
  add := (+),
  ..@additive.add_monoid _ $ @with_zero.monoid (multiplicative α) _ }

instance [add_comm_monoid α] : add_comm_monoid (with_top α) :=
{ zero := 0,
  add := (+),
  ..@additive.add_comm_monoid _ $
    @with_zero.comm_monoid (multiplicative α) _ }

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (with_top α) :=
begin
  suffices, refine {
    add_le_add_left := this,
    ..with_top.partial_order,
    ..with_top.add_comm_monoid, ..},
  { intros a b c h,
    have h' := h,
    rw lt_iff_le_not_le at h' ⊢,
    refine ⟨λ c h₂, _, λ h₂, h'.2 $ this _ _ h₂ _⟩,
    cases h₂, cases a with a,
    { exact (not_le_of_lt h).elim le_top },
    cases b with b,
    { exact (not_le_of_lt h).elim le_top },
    { exact ⟨_, rfl, le_of_lt (lt_of_add_lt_add_left' $
        with_top.some_lt_some.1 h)⟩ } },
  { intros a b h c ca h₂,
    cases c with c, {cases h₂},
    cases b with b; cases h₂,
    cases a with a, {cases le_antisymm h le_top },
    simp at h,
    exact ⟨_, rfl, add_le_add_left' h⟩, }
end

@[simp] lemma zero_lt_top [ordered_add_comm_monoid α] : (0 : with_top α) < ⊤ :=
coe_lt_top 0

@[simp] lemma zero_lt_coe [ordered_add_comm_monoid α] (a : α) : (0 : with_top α) < a ↔ 0 < a :=
coe_lt_coe

@[simp] lemma add_top [ordered_add_comm_monoid α] : ∀{a : with_top α}, a + ⊤ = ⊤
| none := rfl
| (some a) := rfl

@[simp] lemma top_add [ordered_add_comm_monoid α] {a : with_top α} : ⊤ + a = ⊤ := rfl

lemma add_eq_top [ordered_add_comm_monoid α] (a b : with_top α) : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
by cases a; cases b; simp [none_eq_top, some_eq_coe, coe_add.symm]

lemma add_lt_top [ordered_add_comm_monoid α] (a b : with_top α) : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ :=
begin
  apply not_iff_not.1,
  simp [lt_top_iff_ne_top, add_eq_top],
  finish,
  apply classical.dec _,
  apply classical.dec _,
end

end with_top

namespace with_bot

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
    { exact ⟨_, rfl, le_of_lt (lt_of_add_lt_add_left' $
        with_bot.some_lt_some.1 h)⟩ } },
  { intros a b h c ca h₂,
    cases c with c, {cases h₂},
    cases a with a; cases h₂,
    cases b with b, {cases le_antisymm h bot_le},
    simp at h,
    exact ⟨_, rfl, add_le_add_left' h⟩, }
end

@[simp] lemma coe_zero [add_monoid α] : ((0 : α) : with_bot α) = 0 := rfl

@[simp] lemma coe_add [add_semigroup α] (a b : α) : ((a + b : α) : with_bot α) = a + b := rfl

@[simp] lemma bot_add [ordered_add_comm_monoid α] (a : with_bot α) : ⊥ + a = ⊥ := rfl

@[simp] lemma add_bot [ordered_add_comm_monoid α] (a : with_bot α) : a + ⊥ = ⊥ := by cases a; refl

instance has_one [has_one α] : has_one (with_bot α) := ⟨(1 : α)⟩

@[simp] lemma coe_one [has_one α] : ((1 : α) : with_bot α) = 1 := rfl

end with_bot

/-- A canonically ordered monoid is an ordered commutative monoid
  in which the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
  This is satisfied by the natural numbers, for example, but not
  the integers or other ordered groups. -/
class canonically_ordered_add_monoid (α : Type*) extends ordered_add_comm_monoid α, order_bot α :=
(le_iff_exists_add : ∀a b:α, a ≤ b ↔ ∃c, b = a + c)

section canonically_ordered_add_monoid
variables [canonically_ordered_add_monoid α] {a b c d : α}

lemma le_iff_exists_add : a ≤ b ↔ ∃c, b = a + c :=
canonically_ordered_add_monoid.le_iff_exists_add a b

@[simp] lemma zero_le (a : α) : 0 ≤ a := le_iff_exists_add.mpr ⟨a, by simp⟩

@[simp] lemma bot_eq_zero : (⊥ : α) = 0 :=
le_antisymm bot_le (zero_le ⊥)

@[simp] lemma add_eq_zero_iff : a + b = 0 ↔ a = 0 ∧ b = 0 :=
add_eq_zero_iff' (zero_le _) (zero_le _)

@[simp] lemma le_zero_iff_eq : a ≤ 0 ↔ a = 0 :=
iff.intro
  (assume h, le_antisymm h (zero_le a))
  (assume h, h ▸ le_refl a)

protected lemma zero_lt_iff_ne_zero : 0 < a ↔ a ≠ 0 :=
iff.intro ne_of_gt $ assume hne, lt_of_le_of_ne (zero_le _) hne.symm

lemma le_add_left (h : a ≤ c) : a ≤ b + c :=
calc a = 0 + a : by simp
  ... ≤ b + c : add_le_add' (zero_le _) h

lemma le_add_right (h : a ≤ b) : a ≤ b + c :=
calc a = a + 0 : by simp
  ... ≤ b + c : add_le_add' h (zero_le _)

instance with_zero.canonically_ordered_add_monoid :
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

instance with_top.canonically_ordered_add_monoid : canonically_ordered_add_monoid (with_top α) :=
{ le_iff_exists_add := assume a b,
  match a, b with
  | a, none     := show a ≤ ⊤ ↔ ∃c, ⊤ = a + c, by simp; refine ⟨⊤, _⟩; cases a; refl
  | (some a), (some b) := show (a:with_top α) ≤ ↑b ↔ ∃c:with_top α, ↑b = ↑a + c,
    begin
      simp [canonically_ordered_add_monoid.le_iff_exists_add, -add_comm],
      split,
      { rintro ⟨c, rfl⟩, refine ⟨c, _⟩, simp [with_top.coe_add] },
      { exact assume h, match b, h with _, ⟨some c, rfl⟩ := ⟨_, rfl⟩ end }
    end
  | none, some b := show (⊤ : with_top α) ≤ b ↔ ∃c:with_top α, ↑b = ⊤ + c, by simp
  end,
  .. with_top.order_bot,
  .. with_top.ordered_add_comm_monoid }

end canonically_ordered_add_monoid

class ordered_cancel_add_comm_monoid (α : Type u)
      extends add_comm_monoid α, add_left_cancel_semigroup α,
              add_right_cancel_semigroup α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c)

section ordered_cancel_add_comm_monoid
variables [ordered_cancel_add_comm_monoid α] {a b c d : α}

lemma add_le_add_left : ∀ {a b : α} (h : a ≤ b) (c : α), c + a ≤ c + b :=
ordered_cancel_add_comm_monoid.add_le_add_left

lemma le_of_add_le_add_left : ∀ {a b c : α}, a + b ≤ a + c → b ≤ c :=
ordered_cancel_add_comm_monoid.le_of_add_le_add_left

lemma add_lt_add_left (h : a < b) (c : α) : c + a < c + b :=
lt_of_le_not_le (add_le_add_left (le_of_lt h) _) $
  mt le_of_add_le_add_left (not_le_of_gt h)

lemma lt_of_add_lt_add_left (h : a + b < a + c) : b < c :=
lt_of_le_not_le (le_of_add_le_add_left (le_of_lt h)) $
  mt (λ h, add_le_add_left h _) (not_le_of_gt h)

lemma add_le_add_right (h : a ≤ b) (c : α) : a + c ≤ b + c :=
add_comm c a ▸ add_comm c b ▸ add_le_add_left h c

theorem add_lt_add_right (h : a < b) (c : α) : a + c < b + c :=
begin
 rw [add_comm a c, add_comm b c],
 exact (add_lt_add_left h c)
end

lemma add_le_add {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
le_trans (add_le_add_right h₁ c) (add_le_add_left h₂ b)

lemma le_add_of_nonneg_right (h : b ≥ 0) : a ≤ a + b :=
have a + b ≥ a + 0, from add_le_add_left h a,
by rwa add_zero at this

lemma le_add_of_nonneg_left (h : b ≥ 0) : a ≤ b + a :=
have 0 + a ≤ b + a, from add_le_add_right h a,
by rwa zero_add at this

lemma add_lt_add (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
lt_trans (add_lt_add_right h₁ c) (add_lt_add_left h₂ b)

lemma add_lt_add_of_le_of_lt (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d :=
lt_of_le_of_lt (add_le_add_right h₁ c) (add_lt_add_left h₂ b)

lemma add_lt_add_of_lt_of_le (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
lt_of_lt_of_le (add_lt_add_right h₁ c) (add_le_add_left h₂ b)

lemma lt_add_of_pos_right (a : α) {b : α} (h : b > 0) : a < a + b :=
have a + 0 < a + b, from add_lt_add_left h a,
by rwa [add_zero] at this

lemma lt_add_of_pos_left (a : α) {b : α} (h : b > 0) : a < b + a :=
have 0 + a < b + a, from add_lt_add_right h a,
by rwa [zero_add] at this

lemma le_of_add_le_add_right (h : a + b ≤ c + b) : a ≤ c :=
le_of_add_le_add_left
  (show b + a ≤ b + c, begin rw [add_comm b a, add_comm b c], assumption end)

lemma lt_of_add_lt_add_right (h : a + b < c + b) : a < c :=
lt_of_add_lt_add_left
  (show b + a < b + c, begin rw [add_comm b a, add_comm b c], assumption end)

-- here we start using properties of zero.
lemma add_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
zero_add (0:α) ▸ (add_le_add ha hb)

lemma add_pos (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  zero_add (0:α) ▸ (add_lt_add ha hb)

lemma add_pos_of_pos_of_nonneg (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
zero_add (0:α) ▸ (add_lt_add_of_lt_of_le ha hb)

lemma add_pos_of_nonneg_of_pos (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
zero_add (0:α) ▸ (add_lt_add_of_le_of_lt ha hb)

lemma add_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
zero_add (0:α) ▸ (add_le_add ha hb)

lemma add_neg (ha : a < 0) (hb : b < 0) : a + b < 0 :=
zero_add (0:α) ▸ (add_lt_add ha hb)

lemma add_neg_of_neg_of_nonpos (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
zero_add (0:α) ▸ (add_lt_add_of_lt_of_le ha hb)

lemma add_neg_of_nonpos_of_neg (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
zero_add (0:α) ▸ (add_lt_add_of_le_of_lt ha hb)

lemma add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg
    (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b = 0 ↔ a = 0 ∧ b = 0 :=
iff.intro
  (assume hab : a + b = 0,
   have ha' : a ≤ 0, from
   calc
       a     = a + 0 : by rw add_zero
         ... ≤ a + b : add_le_add_left hb _
         ... = 0     : hab,
   have haz : a = 0, from le_antisymm ha' ha,
   have hb' : b ≤ 0, from
   calc
      b     = 0 + b : by rw zero_add
        ... ≤ a + b : by exact add_le_add_right ha _
        ... = 0     : hab,
   have hbz : b = 0, from le_antisymm hb' hb,
   and.intro haz hbz)
  (assume ⟨ha', hb'⟩,
   by rw [ha', hb', add_zero])

lemma le_add_of_nonneg_of_le (ha : 0 ≤ a) (hbc : b ≤ c) : b ≤ a + c :=
zero_add b ▸ add_le_add ha hbc

lemma le_add_of_le_of_nonneg (hbc : b ≤ c) (ha : 0 ≤ a) : b ≤ c + a :=
add_zero b ▸ add_le_add hbc ha

lemma lt_add_of_pos_of_le (ha : 0 < a) (hbc : b ≤ c) : b < a + c :=
zero_add b ▸ add_lt_add_of_lt_of_le ha hbc

lemma lt_add_of_le_of_pos (hbc : b ≤ c) (ha : 0 < a) : b < c + a :=
add_zero b ▸ add_lt_add_of_le_of_lt hbc ha

lemma add_le_of_nonpos_of_le (ha : a ≤ 0) (hbc : b ≤ c) : a + b ≤ c :=
zero_add c ▸ add_le_add ha hbc

lemma add_le_of_le_of_nonpos (hbc : b ≤ c) (ha : a ≤ 0) : b + a ≤ c :=
add_zero c ▸ add_le_add hbc ha

lemma add_lt_of_neg_of_le (ha : a < 0) (hbc : b ≤ c) : a + b < c :=
zero_add c ▸ add_lt_add_of_lt_of_le ha hbc

lemma add_lt_of_le_of_neg (hbc : b ≤ c) (ha : a < 0) : b + a < c :=
add_zero c ▸ add_lt_add_of_le_of_lt hbc ha

lemma lt_add_of_nonneg_of_lt (ha : 0 ≤ a) (hbc : b < c) : b < a + c :=
zero_add b ▸ add_lt_add_of_le_of_lt ha hbc

lemma lt_add_of_lt_of_nonneg (hbc : b < c) (ha : 0 ≤ a) : b < c + a :=
add_zero b ▸ add_lt_add_of_lt_of_le hbc ha

lemma lt_add_of_pos_of_lt (ha : 0 < a) (hbc : b < c) : b < a + c :=
zero_add b ▸ add_lt_add ha hbc

lemma lt_add_of_lt_of_pos (hbc : b < c) (ha : 0 < a) : b < c + a :=
add_zero b ▸ add_lt_add hbc ha

lemma add_lt_of_nonpos_of_lt (ha : a ≤ 0) (hbc : b < c) : a + b < c :=
zero_add c ▸ add_lt_add_of_le_of_lt ha hbc

lemma add_lt_of_lt_of_nonpos (hbc : b < c) (ha : a ≤ 0)  : b + a < c :=
add_zero c ▸ add_lt_add_of_lt_of_le hbc ha

lemma add_lt_of_neg_of_lt (ha : a < 0) (hbc : b < c) : a + b < c :=
zero_add c ▸ add_lt_add ha hbc

lemma add_lt_of_lt_of_neg (hbc : b < c) (ha : a < 0) : b + a < c :=
add_zero c ▸ add_lt_add hbc ha

instance ordered_cancel_add_comm_monoid.to_ordered_add_comm_monoid : ordered_add_comm_monoid α :=
{ lt_of_add_lt_add_left := @lt_of_add_lt_add_left _ _, ..‹ordered_cancel_add_comm_monoid α› }

instance ordered_cancel_add_comm_monoid.to_add_left_cancel_monoid :
  add_left_cancel_monoid α := {
  ..show add_monoid α, by apply_instance,
  ..‹ordered_cancel_add_comm_monoid α› }

@[simp] lemma add_le_add_iff_left (a : α) {b c : α} : a + b ≤ a + c ↔ b ≤ c :=
⟨le_of_add_le_add_left, λ h, add_le_add_left h _⟩

@[simp] lemma add_le_add_iff_right (c : α) : a + c ≤ b + c ↔ a ≤ b :=
add_comm c a ▸ add_comm c b ▸ add_le_add_iff_left c

@[simp] lemma add_lt_add_iff_left (a : α) {b c : α} : a + b < a + c ↔ b < c :=
⟨lt_of_add_lt_add_left, λ h, add_lt_add_left h _⟩

@[simp] lemma add_lt_add_iff_right (c : α) : a + c < b + c ↔ a < b :=
add_comm c a ▸ add_comm c b ▸ add_lt_add_iff_left c

@[simp] lemma le_add_iff_nonneg_right (a : α) {b : α} : a ≤ a + b ↔ 0 ≤ b :=
have a + 0 ≤ a + b ↔ 0 ≤ b, from add_le_add_iff_left a,
by rwa add_zero at this

@[simp] lemma le_add_iff_nonneg_left (a : α) {b : α} : a ≤ b + a ↔ 0 ≤ b :=
by rw [add_comm, le_add_iff_nonneg_right]

@[simp] lemma lt_add_iff_pos_right (a : α) {b : α} : a < a + b ↔ 0 < b :=
have a + 0 < a + b ↔ 0 < b, from add_lt_add_iff_left a,
by rwa add_zero at this

@[simp] lemma lt_add_iff_pos_left (a : α) {b : α} : a < b + a ↔ 0 < b :=
by rw [add_comm, lt_add_iff_pos_right]

@[simp] lemma add_le_iff_nonpos_left : a + b ≤ b ↔ a ≤ 0 :=
by { convert add_le_add_iff_right b, rw [zero_add] }

@[simp] lemma add_le_iff_nonpos_right : a + b ≤ a ↔ b ≤ 0 :=
by { convert add_le_add_iff_left a, rw [add_zero] }

@[simp] lemma add_lt_iff_neg_right : a + b < b ↔ a < 0 :=
by { convert add_lt_add_iff_right b, rw [zero_add] }

@[simp] lemma add_lt_iff_neg_left : a + b < a ↔ b < 0 :=
by { convert add_lt_add_iff_left a, rw [add_zero] }

lemma add_eq_zero_iff_eq_zero_of_nonneg
  (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b = 0 ↔ a = 0 ∧ b = 0 :=
⟨λ hab : a + b = 0,
by split; apply le_antisymm; try {assumption};
   rw ← hab; simp [ha, hb],
λ ⟨ha', hb'⟩, by rw [ha', hb', add_zero]⟩

lemma with_top.add_lt_add_iff_left :
  ∀{a b c : with_top α}, a < ⊤ → (a + c < a + b ↔ c < b)
| none := assume b c h, (lt_irrefl ⊤ h).elim
| (some a) :=
  begin
    assume b c h,
    cases b; cases c;
      simp [with_top.none_eq_top, with_top.some_eq_coe, with_top.coe_lt_top, with_top.coe_lt_coe],
    { rw [← with_top.coe_add], exact with_top.coe_lt_top _ },
    { rw [← with_top.coe_add, ← with_top.coe_add, with_top.coe_lt_coe],
      exact add_lt_add_iff_left _ }
  end

lemma with_top.add_lt_add_iff_right
  {a b c : with_top α} : a < ⊤ → (c + a < b + a ↔ c < b) :=
by simpa [add_comm] using @with_top.add_lt_add_iff_left _ _ a b c

section mono

variables {β : Type*} [preorder β] {f g : β → α}

lemma monotone.add_strict_mono (hf : monotone f) (hg : strict_mono g) :
  strict_mono (λ x, f x + g x) :=
λ x y h, add_lt_add_of_le_of_lt (hf $ le_of_lt h) (hg h)

lemma strict_mono.add_monotone (hf : strict_mono f) (hg : monotone g) :
  strict_mono (λ x, f x + g x) :=
λ x y h, add_lt_add_of_lt_of_le (hf h) (hg $ le_of_lt h)

end mono

end ordered_cancel_add_comm_monoid

class ordered_add_comm_group (α : Type u) extends add_comm_group α, partial_order α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)

section ordered_add_comm_group
variables [ordered_add_comm_group α] {a b c d : α}

lemma ordered_add_comm_group.add_lt_add_left (a b : α) (h : a < b) (c : α) : c + a < c + b :=
begin
  rw lt_iff_le_not_le at h ⊢,
  split,
  { apply ordered_add_comm_group.add_le_add_left _ _ h.1 },
  { intro w,
    have w : -c + (c + b) ≤ -c + (c + a) := ordered_add_comm_group.add_le_add_left _ _ w _,
    simp only [add_zero, add_comm, add_left_neg, add_left_comm] at w,
    exact h.2 w },
end

lemma ordered_add_comm_group.le_of_add_le_add_left (h : a + b ≤ a + c) : b ≤ c :=
have -a + (a + b) ≤ -a + (a + c), from ordered_add_comm_group.add_le_add_left _ _ h _,
begin simp [neg_add_cancel_left] at this, assumption end

lemma ordered_add_comm_group.lt_of_add_lt_add_left (h : a + b < a + c) : b < c :=
have -a + (a + b) < -a + (a + c), from ordered_add_comm_group.add_lt_add_left _ _ h _,
begin simp [neg_add_cancel_left] at this, assumption end

instance ordered_add_comm_group.to_ordered_cancel_add_comm_monoid (α : Type u)
  [s : ordered_add_comm_group α] : ordered_cancel_add_comm_monoid α :=
{ add_left_cancel       := @add_left_cancel α _,
  add_right_cancel      := @add_right_cancel α _,
  le_of_add_le_add_left := @ordered_add_comm_group.le_of_add_le_add_left α _,
  ..s }

lemma neg_le_neg (h : a ≤ b) : -b ≤ -a :=
have 0 ≤ -a + b,           from add_left_neg a ▸ add_le_add_left h (-a),
have 0 + -b ≤ -a + b + -b, from add_le_add_right this (-b),
by rwa [add_neg_cancel_right, zero_add] at this

lemma le_of_neg_le_neg (h : -b ≤ -a) : a ≤ b :=
suffices -(-a) ≤ -(-b), from
  begin simp [neg_neg] at this, assumption end,
neg_le_neg h

lemma nonneg_of_neg_nonpos (h : -a ≤ 0) : 0 ≤ a :=
have -a ≤ -0, by rwa neg_zero,
le_of_neg_le_neg this

lemma neg_nonpos_of_nonneg (h : 0 ≤ a) : -a ≤ 0 :=
have -a ≤ -0, from neg_le_neg h,
by rwa neg_zero at this

lemma nonpos_of_neg_nonneg (h : 0 ≤ -a) : a ≤ 0 :=
have -0 ≤ -a, by rwa neg_zero,
le_of_neg_le_neg this

lemma neg_nonneg_of_nonpos (h : a ≤ 0) : 0 ≤ -a :=
have -0 ≤ -a, from neg_le_neg h,
by rwa neg_zero at this

lemma neg_lt_neg (h : a < b) : -b < -a :=
have 0 < -a + b, from add_left_neg a ▸ add_lt_add_left h (-a),
have 0 + -b < -a + b + -b, from add_lt_add_right this (-b),
by rwa [add_neg_cancel_right, zero_add] at this

lemma lt_of_neg_lt_neg (h : -b < -a) : a < b :=
neg_neg a ▸ neg_neg b ▸ neg_lt_neg h

lemma pos_of_neg_neg (h : -a < 0) : 0 < a :=
have -a < -0, by rwa neg_zero,
lt_of_neg_lt_neg this

lemma neg_neg_of_pos (h : 0 < a) : -a < 0 :=
have -a < -0, from neg_lt_neg h,
by rwa neg_zero at this

lemma neg_of_neg_pos (h : 0 < -a) : a < 0 :=
have -0 < -a, by rwa neg_zero,
lt_of_neg_lt_neg this

lemma neg_pos_of_neg (h : a < 0) : 0 < -a :=
have -0 < -a, from neg_lt_neg h,
by rwa neg_zero at this

lemma le_neg_of_le_neg (h : a ≤ -b) : b ≤ -a :=
begin
  have h := neg_le_neg h,
  rwa neg_neg at h
end

lemma neg_le_of_neg_le (h : -a ≤ b) : -b ≤ a :=
begin
  have h := neg_le_neg h,
  rwa neg_neg at h
end

lemma lt_neg_of_lt_neg (h : a < -b) : b < -a :=
begin
  have h := neg_lt_neg h,
  rwa neg_neg at h
end

lemma neg_lt_of_neg_lt (h : -a < b) : -b < a :=
begin
  have h := neg_lt_neg h,
  rwa neg_neg at h
end

lemma sub_nonneg_of_le (h : b ≤ a) : 0 ≤ a - b :=
begin
  have h := add_le_add_right h (-b),
  rwa add_right_neg at h
end

lemma le_of_sub_nonneg (h : 0 ≤ a - b) : b ≤ a :=
begin
  have h := add_le_add_right h b,
  rwa [sub_add_cancel, zero_add] at h
end

lemma sub_nonpos_of_le (h : a ≤ b) : a - b ≤ 0 :=
begin
  have h := add_le_add_right h (-b),
  rwa add_right_neg at h
end

lemma le_of_sub_nonpos (h : a - b ≤ 0) : a ≤ b :=
begin
  have h := add_le_add_right h b,
  rwa [sub_add_cancel, zero_add] at h
end

lemma sub_pos_of_lt (h : b < a) : 0 < a - b :=
begin
  have h := add_lt_add_right h (-b),
  rwa add_right_neg at h
end

lemma lt_of_sub_pos (h : 0 < a - b) : b < a :=
begin
  have h := add_lt_add_right h b,
  rwa [sub_add_cancel, zero_add] at h
end

lemma sub_neg_of_lt (h : a < b) : a - b < 0 :=
begin
  have h := add_lt_add_right h (-b),
  rwa add_right_neg at h
end

lemma lt_of_sub_neg (h : a - b < 0) : a < b :=
begin
  have h := add_lt_add_right h b,
  rwa [sub_add_cancel, zero_add] at h
end

lemma add_le_of_le_neg_add (h : b ≤ -a + c) : a + b ≤ c :=
begin
  have h := add_le_add_left h a,
  rwa add_neg_cancel_left at h
end

lemma le_neg_add_of_add_le (h : a + b ≤ c) : b ≤ -a + c :=
begin
  have h := add_le_add_left h (-a),
  rwa neg_add_cancel_left at h
end

lemma add_le_of_le_sub_left (h : b ≤ c - a) : a + b ≤ c :=
begin
  have h := add_le_add_left h a,
  rwa [← add_sub_assoc, add_comm a c, add_sub_cancel] at h
end

lemma le_sub_left_of_add_le (h : a + b ≤ c) : b ≤ c - a :=
begin
  have h := add_le_add_right h (-a),
  rwa [add_comm a b, add_neg_cancel_right] at h
end

lemma add_le_of_le_sub_right (h : a ≤ c - b) : a + b ≤ c :=
begin
  have h := add_le_add_right h b,
  rwa sub_add_cancel at h
end

lemma le_sub_right_of_add_le (h : a + b ≤ c) : a ≤ c - b :=
begin
  have h := add_le_add_right h (-b),
  rwa add_neg_cancel_right at h
end

lemma le_add_of_neg_add_le (h : -b + a ≤ c) : a ≤ b + c :=
begin
  have h := add_le_add_left h b,
  rwa add_neg_cancel_left at h
end

lemma neg_add_le_of_le_add (h : a ≤ b + c) : -b + a ≤ c :=
begin
  have h := add_le_add_left h (-b),
  rwa neg_add_cancel_left at h
end

lemma le_add_of_sub_left_le (h : a - b ≤ c) : a ≤ b + c :=
begin
  have h := add_le_add_right h b,
  rwa [sub_add_cancel, add_comm] at h
end

lemma sub_left_le_of_le_add (h : a ≤ b + c) : a - b ≤ c :=
begin
  have h := add_le_add_right h (-b),
  rwa [add_comm b c, add_neg_cancel_right] at h
end

lemma le_add_of_sub_right_le (h : a - c ≤ b) : a ≤ b + c :=
begin
  have h := add_le_add_right h c,
  rwa sub_add_cancel at h
end

lemma sub_right_le_of_le_add (h : a ≤ b + c) : a - c ≤ b :=
begin
  have h := add_le_add_right h (-c),
  rwa add_neg_cancel_right at h
end

lemma le_add_of_neg_add_le_left (h : -b + a ≤ c) : a ≤ b + c :=
begin
  rw add_comm at h,
  exact le_add_of_sub_left_le h
end

lemma neg_add_le_left_of_le_add (h : a ≤ b + c) : -b + a ≤ c :=
begin
  rw add_comm,
  exact sub_left_le_of_le_add h
end

lemma le_add_of_neg_add_le_right (h : -c + a ≤ b) : a ≤ b + c :=
begin
  rw add_comm at h,
  exact le_add_of_sub_right_le h
end

lemma neg_add_le_right_of_le_add (h : a ≤ b + c) : -c + a ≤ b :=
begin
  rw add_comm at h,
  apply neg_add_le_left_of_le_add h
end

lemma le_add_of_neg_le_sub_left (h : -a ≤ b - c) : c ≤ a + b :=
le_add_of_neg_add_le_left (add_le_of_le_sub_right h)

lemma neg_le_sub_left_of_le_add (h : c ≤ a + b) : -a ≤ b - c :=
begin
  have h := le_neg_add_of_add_le (sub_left_le_of_le_add h),
  rwa add_comm at h
end

lemma le_add_of_neg_le_sub_right (h : -b ≤ a - c) : c ≤ a + b :=
le_add_of_sub_right_le (add_le_of_le_sub_left h)

lemma neg_le_sub_right_of_le_add (h : c ≤ a + b) : -b ≤ a - c :=
le_sub_left_of_add_le (sub_right_le_of_le_add h)

lemma sub_le_of_sub_le (h : a - b ≤ c) : a - c ≤ b :=
sub_left_le_of_le_add (le_add_of_sub_right_le h)

lemma sub_le_sub_left (h : a ≤ b) (c : α) : c - b ≤ c - a :=
add_le_add_left (neg_le_neg h) c

lemma sub_le_sub_right (h : a ≤ b) (c : α) : a - c ≤ b - c :=
add_le_add_right h (-c)

lemma sub_le_sub (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
add_le_add hab (neg_le_neg hcd)

lemma add_lt_of_lt_neg_add (h : b < -a + c) : a + b < c :=
begin
  have h := add_lt_add_left h a,
  rwa add_neg_cancel_left at h
end

lemma lt_neg_add_of_add_lt (h : a + b < c) : b < -a + c :=
begin
  have h := add_lt_add_left h (-a),
  rwa neg_add_cancel_left at h
end

lemma add_lt_of_lt_sub_left (h : b < c - a) : a + b < c :=
begin
  have h := add_lt_add_left h a,
  rwa [← add_sub_assoc, add_comm a c, add_sub_cancel] at h
end

lemma lt_sub_left_of_add_lt (h : a + b < c) : b < c - a :=
begin
  have h := add_lt_add_right h (-a),
  rwa [add_comm a b, add_neg_cancel_right] at h
end

lemma add_lt_of_lt_sub_right (h : a < c - b) : a + b < c :=
begin
  have h := add_lt_add_right h b,
  rwa sub_add_cancel at h
end

lemma lt_sub_right_of_add_lt (h : a + b < c) : a < c - b :=
begin
  have h := add_lt_add_right h (-b),
  rwa add_neg_cancel_right at h
end

lemma lt_add_of_neg_add_lt (h : -b + a < c) : a < b + c :=
begin
  have h := add_lt_add_left h b,
  rwa add_neg_cancel_left at h
end

lemma neg_add_lt_of_lt_add (h : a < b + c) : -b + a < c :=
begin
  have h := add_lt_add_left h (-b),
  rwa neg_add_cancel_left at h
end

lemma lt_add_of_sub_left_lt (h : a - b < c) : a < b + c :=
begin
  have h := add_lt_add_right h b,
  rwa [sub_add_cancel, add_comm] at h
end

lemma sub_left_lt_of_lt_add (h : a < b + c) : a - b < c :=
begin
  have h := add_lt_add_right h (-b),
  rwa [add_comm b c, add_neg_cancel_right] at h
end

lemma lt_add_of_sub_right_lt (h : a - c < b) : a < b + c :=
begin
  have h := add_lt_add_right h c,
  rwa sub_add_cancel at h
end

lemma sub_right_lt_of_lt_add (h : a < b + c) : a - c < b :=
begin
  have h := add_lt_add_right h (-c),
  rwa add_neg_cancel_right at h
end

lemma lt_add_of_neg_add_lt_left (h : -b + a < c) : a < b + c :=
begin
  rw add_comm at h,
  exact lt_add_of_sub_left_lt h
end

lemma neg_add_lt_left_of_lt_add (h : a < b + c) : -b + a < c :=
begin
  rw add_comm,
  exact sub_left_lt_of_lt_add h
end

lemma lt_add_of_neg_add_lt_right (h : -c + a < b) : a < b + c :=
begin
  rw add_comm at h,
  exact lt_add_of_sub_right_lt h
end

lemma neg_add_lt_right_of_lt_add (h : a < b + c) : -c + a < b :=
begin
  rw add_comm at h,
  apply neg_add_lt_left_of_lt_add h
end

lemma lt_add_of_neg_lt_sub_left (h : -a < b - c) : c < a + b :=
lt_add_of_neg_add_lt_left (add_lt_of_lt_sub_right h)

lemma neg_lt_sub_left_of_lt_add (h : c < a + b) : -a < b - c :=
begin
  have h := lt_neg_add_of_add_lt (sub_left_lt_of_lt_add h),
  rwa add_comm at h
end

lemma lt_add_of_neg_lt_sub_right (h : -b < a - c) : c < a + b :=
lt_add_of_sub_right_lt (add_lt_of_lt_sub_left h)

lemma neg_lt_sub_right_of_lt_add (h : c < a + b) : -b < a - c :=
lt_sub_left_of_add_lt (sub_right_lt_of_lt_add h)

lemma sub_lt_of_sub_lt (h : a - b < c) : a - c < b :=
sub_left_lt_of_lt_add (lt_add_of_sub_right_lt h)

lemma sub_lt_sub_left (h : a < b) (c : α) : c - b < c - a :=
add_lt_add_left (neg_lt_neg h) c

lemma sub_lt_sub_right (h : a < b) (c : α) : a - c < b - c :=
add_lt_add_right h (-c)

lemma sub_lt_sub (hab : a < b) (hcd : c < d) : a - d < b - c :=
add_lt_add hab (neg_lt_neg hcd)

lemma sub_lt_sub_of_le_of_lt (hab : a ≤ b) (hcd : c < d) : a - d < b - c :=
add_lt_add_of_le_of_lt hab (neg_lt_neg hcd)

lemma sub_lt_sub_of_lt_of_le (hab : a < b) (hcd : c ≤ d) : a - d < b - c :=
add_lt_add_of_lt_of_le hab (neg_le_neg hcd)

lemma sub_le_self (a : α) {b : α} (h : b ≥ 0) : a - b ≤ a :=
calc
  a - b = a + -b : rfl
    ... ≤ a + 0  : add_le_add_left (neg_nonpos_of_nonneg h) _
    ... = a      : by rw add_zero

lemma sub_lt_self (a : α) {b : α} (h : b > 0) : a - b < a :=
calc
  a - b = a + -b : rfl
    ... < a + 0  : add_lt_add_left (neg_neg_of_pos h) _
    ... = a      : by rw add_zero

lemma add_le_add_three {a b c d e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) :
      a + b + c ≤ d + e + f :=
begin
  apply le_trans,
  apply add_le_add,
  apply add_le_add,
  assumption',
  apply le_refl
end

@[simp] lemma neg_neg_iff_pos : -a < 0 ↔ 0 < a :=
⟨ pos_of_neg_neg, neg_neg_of_pos ⟩

@[simp] lemma neg_le_neg_iff : -a ≤ -b ↔ b ≤ a :=
have a + b - a ≤ a + b - b ↔ -a ≤ -b, from add_le_add_iff_left _,
by simp at this; simp [this]

lemma neg_le : -a ≤ b ↔ -b ≤ a :=
have -a ≤ -(-b) ↔ -b ≤ a, from neg_le_neg_iff,
by rwa neg_neg at this

lemma le_neg : a ≤ -b ↔ b ≤ -a :=
have -(-a) ≤ -b ↔ b ≤ -a, from neg_le_neg_iff,
by rwa neg_neg at this

lemma neg_le_iff_add_nonneg : -a ≤ b ↔ 0 ≤ a + b :=
(add_le_add_iff_left a).symm.trans $ by rw add_neg_self

lemma le_neg_iff_add_nonpos : a ≤ -b ↔ a + b ≤ 0 :=
(add_le_add_iff_right b).symm.trans $ by rw neg_add_self

@[simp] lemma neg_nonpos : -a ≤ 0 ↔ 0 ≤ a :=
have -a ≤ -0 ↔ 0 ≤ a, from neg_le_neg_iff,
by rwa neg_zero at this

@[simp] lemma neg_nonneg : 0 ≤ -a ↔ a ≤ 0 :=
have -0 ≤ -a ↔ a ≤ 0, from neg_le_neg_iff,
by rwa neg_zero at this

lemma neg_le_self (h : 0 ≤ a) : -a ≤ a :=
le_trans (neg_nonpos.2 h) h

lemma self_le_neg (h : a ≤ 0) : a ≤ -a :=
le_trans h (neg_nonneg.2 h)

@[simp] lemma neg_lt_neg_iff : -a < -b ↔ b < a :=
have a + b - a < a + b - b ↔ -a < -b, from add_lt_add_iff_left _,
by simp at this; simp [this]

lemma neg_lt_zero : -a < 0 ↔ 0 < a :=
have -a < -0 ↔ 0 < a, from neg_lt_neg_iff,
by rwa neg_zero at this

lemma neg_pos : 0 < -a ↔ a < 0 :=
have -0 < -a ↔ a < 0, from neg_lt_neg_iff,
by rwa neg_zero at this

lemma neg_lt : -a < b ↔ -b < a :=
have -a < -(-b) ↔ -b < a, from neg_lt_neg_iff,
by rwa neg_neg at this

lemma lt_neg : a < -b ↔ b < -a :=
have -(-a) < -b ↔ b < -a, from neg_lt_neg_iff,
by rwa neg_neg at this

@[simp]
lemma sub_le_sub_iff_left (a : α) {b c : α} : a - b ≤ a - c ↔ c ≤ b :=
(add_le_add_iff_left _).trans neg_le_neg_iff

@[simp]
lemma sub_le_sub_iff_right (c : α) : a - c ≤ b - c ↔ a ≤ b :=
add_le_add_iff_right _

@[simp]
lemma sub_lt_sub_iff_left (a : α) {b c : α} : a - b < a - c ↔ c < b :=
(add_lt_add_iff_left _).trans neg_lt_neg_iff

@[simp]
lemma sub_lt_sub_iff_right (c : α) : a - c < b - c ↔ a < b :=
add_lt_add_iff_right _

@[simp] lemma sub_nonneg : 0 ≤ a - b ↔ b ≤ a :=
have a - a ≤ a - b ↔ b ≤ a, from sub_le_sub_iff_left a,
by rwa sub_self at this

@[simp] lemma sub_nonpos : a - b ≤ 0 ↔ a ≤ b :=
have a - b ≤ b - b ↔ a ≤ b, from sub_le_sub_iff_right b,
by rwa sub_self at this

@[simp] lemma sub_pos : 0 < a - b ↔ b < a :=
have a - a < a - b ↔ b < a, from sub_lt_sub_iff_left a,
by rwa sub_self at this

@[simp] lemma sub_lt_zero : a - b < 0 ↔ a < b :=
have a - b < b - b ↔ a < b, from sub_lt_sub_iff_right b,
by rwa sub_self at this

lemma le_neg_add_iff_add_le : b ≤ -a + c ↔ a + b ≤ c :=
have -a + (a + b) ≤ -a + c ↔ a + b ≤ c, from add_le_add_iff_left _,
by rwa neg_add_cancel_left at this

lemma le_sub_iff_add_le' : b ≤ c - a ↔ a + b ≤ c :=
by rw [sub_eq_add_neg, add_comm, le_neg_add_iff_add_le]

lemma le_sub_iff_add_le : a ≤ c - b ↔ a + b ≤ c :=
by rw [le_sub_iff_add_le', add_comm]

@[simp] lemma neg_add_le_iff_le_add : -b + a ≤ c ↔ a ≤ b + c :=
have -b + a ≤ -b + (b + c) ↔ a ≤ b + c, from add_le_add_iff_left _,
by rwa neg_add_cancel_left at this

lemma sub_le_iff_le_add' : a - b ≤ c ↔ a ≤ b + c :=
by rw [sub_eq_add_neg, add_comm, neg_add_le_iff_le_add]

lemma sub_le_iff_le_add : a - c ≤ b ↔ a ≤ b + c :=
by rw [sub_le_iff_le_add', add_comm]

lemma add_neg_le_iff_le_add : a + -c ≤ b ↔ a ≤ b + c :=
sub_le_iff_le_add

@[simp] lemma add_neg_le_iff_le_add' : a + -b ≤ c ↔ a ≤ b + c :=
sub_le_iff_le_add'

lemma neg_add_le_iff_le_add' : -c + a ≤ b ↔ a ≤ b + c :=
by rw [neg_add_le_iff_le_add, add_comm]

@[simp] lemma neg_le_sub_iff_le_add : -b ≤ a - c ↔ c ≤ a + b :=
le_sub_iff_add_le.trans neg_add_le_iff_le_add'

lemma neg_le_sub_iff_le_add' : -a ≤ b - c ↔ c ≤ a + b :=
by rw [neg_le_sub_iff_le_add, add_comm]

lemma sub_le : a - b ≤ c ↔ a - c ≤ b :=
sub_le_iff_le_add'.trans sub_le_iff_le_add.symm

theorem le_sub : a ≤ b - c ↔ c ≤ b - a :=
le_sub_iff_add_le'.trans le_sub_iff_add_le.symm

@[simp] lemma lt_neg_add_iff_add_lt : b < -a + c ↔ a + b < c :=
have -a + (a + b) < -a + c ↔ a + b < c, from add_lt_add_iff_left _,
by rwa neg_add_cancel_left at this

lemma lt_sub_iff_add_lt' : b < c - a ↔ a + b < c :=
by rw [sub_eq_add_neg, add_comm, lt_neg_add_iff_add_lt]

lemma lt_sub_iff_add_lt : a < c - b ↔ a + b < c :=
by rw [lt_sub_iff_add_lt', add_comm]

@[simp] lemma neg_add_lt_iff_lt_add : -b + a < c ↔ a < b + c :=
have -b + a < -b + (b + c) ↔ a < b + c, from add_lt_add_iff_left _,
by rwa neg_add_cancel_left at this

lemma sub_lt_iff_lt_add' : a - b < c ↔ a < b + c :=
by rw [sub_eq_add_neg, add_comm, neg_add_lt_iff_lt_add]

lemma sub_lt_iff_lt_add : a - c < b ↔ a < b + c :=
by rw [sub_lt_iff_lt_add', add_comm]

lemma neg_add_lt_iff_lt_add_right : -c + a < b ↔ a < b + c :=
by rw [neg_add_lt_iff_lt_add, add_comm]

@[simp] lemma neg_lt_sub_iff_lt_add : -b < a - c ↔ c < a + b :=
lt_sub_iff_add_lt.trans neg_add_lt_iff_lt_add_right

lemma neg_lt_sub_iff_lt_add' : -a < b - c ↔ c < a + b :=
by rw [neg_lt_sub_iff_lt_add, add_comm]

lemma sub_lt : a - b < c ↔ a - c < b :=
sub_lt_iff_lt_add'.trans sub_lt_iff_lt_add.symm

theorem lt_sub : a < b - c ↔ c < b - a :=
lt_sub_iff_add_lt'.trans lt_sub_iff_add_lt.symm

lemma sub_le_self_iff (a : α) {b : α} : a - b ≤ a ↔ 0 ≤ b :=
sub_le_iff_le_add'.trans (le_add_iff_nonneg_left _)

lemma sub_lt_self_iff (a : α) {b : α} : a - b < a ↔ 0 < b :=
sub_lt_iff_lt_add'.trans (lt_add_iff_pos_left _)

end ordered_add_comm_group

/--
The `add_lt_add_left` field of `ordered_add_comm_group` is redundant, but it is in core so
we can't remove it for now. This alternative constructor is the best we can do.
-/
def ordered_add_comm_group.mk' {α : Type u} [add_comm_group α] [partial_order α]
  (add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b) :
  ordered_add_comm_group α :=
{ add_le_add_left := add_le_add_left,
  ..(by apply_instance : add_comm_group α),
  ..(by apply_instance : partial_order α)  }

class decidable_linear_ordered_cancel_add_comm_monoid (α : Type u)
  extends ordered_cancel_add_comm_monoid α, decidable_linear_order α

section decidable_linear_ordered_cancel_add_comm_monoid
variables [decidable_linear_ordered_cancel_add_comm_monoid α]

lemma min_add_add_left (a b c : α) : min (a + b) (a + c) = a + min b c :=
eq.symm (eq_min
  (show a + min b c ≤ a + b, from add_le_add_left (min_le_left _ _)  _)
  (show a + min b c ≤ a + c, from add_le_add_left (min_le_right _ _)  _)
  (assume d,
    assume : d ≤ a + b,
    assume : d ≤ a + c,
    decidable.by_cases
      (assume : b ≤ c, by rwa [min_eq_left this])
      (assume : ¬ b ≤ c, by rwa [min_eq_right (le_of_lt (lt_of_not_ge this))])))

lemma min_add_add_right (a b c : α) : min (a + c) (b + c) = min a b + c :=
begin rw [add_comm a c, add_comm b c, add_comm _ c], apply min_add_add_left end

lemma max_add_add_left (a b c : α) : max (a + b) (a + c) = a + max b c :=
eq.symm (eq_max
  (add_le_add_left (le_max_left _ _)  _)
  (add_le_add_left (le_max_right _ _) _)
  (assume d,
    assume : a + b ≤ d,
    assume : a + c ≤ d,
    decidable.by_cases
      (assume : b ≤ c, by rwa [max_eq_right this])
      (assume : ¬ b ≤ c, by rwa [max_eq_left (le_of_lt (lt_of_not_ge this))])))

lemma max_add_add_right (a b c : α) : max (a + c) (b + c) = max a b + c :=
begin rw [add_comm a c, add_comm b c, add_comm _ c], apply max_add_add_left end

end decidable_linear_ordered_cancel_add_comm_monoid

class decidable_linear_ordered_add_comm_group (α : Type u)
  extends add_comm_group α, decidable_linear_order α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)

instance decidable_linear_ordered_comm_group.to_ordered_add_comm_group (α : Type u)
  [s : decidable_linear_ordered_add_comm_group α] : ordered_add_comm_group α :=
{ add := s.add, ..s }

section decidable_linear_ordered_add_comm_group
variables [decidable_linear_ordered_add_comm_group α]

@[priority 100] -- see Note [lower instance priority]
instance decidable_linear_ordered_add_comm_group.to_decidable_linear_ordered_cancel_add_comm_monoid :
  decidable_linear_ordered_cancel_add_comm_monoid α :=
{ le_of_add_le_add_left := λ x y z, le_of_add_le_add_left,
  add_left_cancel := λ x y z, add_left_cancel,
  add_right_cancel := λ x y z, add_right_cancel,
  ..‹decidable_linear_ordered_add_comm_group α› }

lemma decidable_linear_ordered_add_comm_group.add_lt_add_left
  (a b : α) (h : a < b) (c : α) : c + a < c + b :=
ordered_add_comm_group.add_lt_add_left a b h c

lemma max_neg_neg (a b : α) : max (-a) (-b) = - min a b  :=
eq.symm (eq_max
  (show -a ≤ -(min a b), from neg_le_neg $ min_le_left a b)
  (show -b ≤ -(min a b), from neg_le_neg $ min_le_right a b)
  (assume d,
    assume H₁ : -a ≤ d,
    assume H₂ : -b ≤ d,
    have H : -d ≤ min a b,
      from le_min (neg_le_of_neg_le  H₁) (neg_le_of_neg_le H₂),
    show -(min a b) ≤ d, from neg_le_of_neg_le H))

lemma min_eq_neg_max_neg_neg (a b : α) : min a b = - max (-a) (-b) :=
by rw [max_neg_neg, neg_neg]

lemma min_neg_neg (a b : α) : min (-a) (-b) = - max a b :=
by rw [min_eq_neg_max_neg_neg, neg_neg, neg_neg]

lemma max_eq_neg_min_neg_neg (a b : α) : max a b = - min (-a) (-b) :=
by rw [min_neg_neg, neg_neg]

def abs (a : α) : α := max a (-a)

lemma abs_of_nonneg {a : α} (h : a ≥ 0) : abs a = a :=
have h' : -a ≤ a, from le_trans (neg_nonpos_of_nonneg h) h,
max_eq_left h'

lemma abs_of_pos {a : α} (h : a > 0) : abs a = a :=
abs_of_nonneg (le_of_lt h)

lemma abs_of_nonpos {a : α} (h : a ≤ 0) : abs a = -a :=
have h' : a ≤ -a, from le_trans h (neg_nonneg_of_nonpos h),
max_eq_right h'

lemma abs_of_neg {a : α} (h : a < 0) : abs a = -a :=
abs_of_nonpos (le_of_lt h)

lemma abs_zero : abs 0 = (0:α) :=
abs_of_nonneg (le_refl _)

lemma abs_neg (a : α) : abs (-a) = abs a :=
begin unfold abs, rw [max_comm, neg_neg] end

lemma abs_pos_of_pos {a : α} (h : a > 0) : abs a > 0 :=
by rwa (abs_of_pos h)

lemma abs_pos_of_neg {a : α} (h : a < 0) : abs a > 0 :=
abs_neg a ▸ abs_pos_of_pos (neg_pos_of_neg h)

lemma abs_sub (a b : α) : abs (a - b) = abs (b - a) :=
by rw [← neg_sub, abs_neg]

lemma ne_zero_of_abs_ne_zero {a : α} (h : abs a ≠ 0) : a ≠ 0 :=
assume ha, h (eq.symm ha ▸ abs_zero)

/- these assume a linear order -/

lemma eq_zero_of_neg_eq {a : α} (h : -a = a) : a = 0 :=
match lt_trichotomy a 0 with
| or.inl h₁ :=
  have a > 0, from h ▸ neg_pos_of_neg h₁,
  absurd h₁ (lt_asymm this)
| or.inr (or.inl h₁) := h₁
| or.inr (or.inr h₁) :=
  have a < 0, from h ▸ neg_neg_of_pos h₁,
  absurd h₁ (lt_asymm this)
end

lemma abs_nonneg (a : α) : abs a ≥ 0 :=
or.elim (le_total 0 a)
  (assume h : 0 ≤ a, by rwa (abs_of_nonneg h))
  (assume h : a ≤ 0, calc
       0 ≤ -a    : neg_nonneg_of_nonpos h
     ... = abs a : eq.symm (abs_of_nonpos h))

lemma abs_abs (a : α) : abs (abs a) = abs a :=
abs_of_nonneg $ abs_nonneg a

lemma le_abs_self (a : α) : a ≤ abs a :=
or.elim (le_total 0 a)
  (assume h : 0 ≤ a,
   begin rw [abs_of_nonneg h] end)
  (assume h : a ≤ 0, le_trans h $ abs_nonneg a)

lemma neg_le_abs_self (a : α) : -a ≤ abs a :=
abs_neg a ▸ le_abs_self (-a)

lemma eq_zero_of_abs_eq_zero {a : α} (h : abs a = 0) : a = 0 :=
have h₁ : a ≤ 0, from h ▸ le_abs_self a,
have h₂ : -a ≤ 0, from h ▸ abs_neg a ▸ le_abs_self (-a),
le_antisymm h₁ (nonneg_of_neg_nonpos h₂)

lemma eq_of_abs_sub_eq_zero {a b : α} (h : abs (a - b) = 0) : a = b :=
have a - b = 0, from eq_zero_of_abs_eq_zero h,
show a = b, from eq_of_sub_eq_zero this

lemma abs_pos_of_ne_zero {a : α} (h : a ≠ 0) : abs a > 0 :=
or.elim (lt_or_gt_of_ne h) abs_pos_of_neg abs_pos_of_pos

lemma abs_by_cases (P : α → Prop) {a : α} (h1 : P a) (h2 : P (-a)) : P (abs a) :=
or.elim (le_total 0 a)
  (assume h : 0 ≤ a, eq.symm (abs_of_nonneg h) ▸ h1)
  (assume h : a ≤ 0, eq.symm (abs_of_nonpos h) ▸ h2)

lemma abs_le_of_le_of_neg_le {a b : α} (h1 : a ≤ b) (h2 : -a ≤ b) : abs a ≤ b :=
abs_by_cases (λ x : α, x ≤ b) h1 h2

lemma abs_lt_of_lt_of_neg_lt {a b : α} (h1 : a < b) (h2 : -a < b) : abs a < b :=
abs_by_cases (λ x : α, x < b) h1 h2

private lemma aux1 {a b : α} (h1 : a + b ≥ 0) (h2 : a ≥ 0) : abs (a + b) ≤ abs a + abs b :=
decidable.by_cases
  (assume h3 : b ≥ 0, calc
    abs (a + b) ≤ abs (a + b)   : by apply le_refl
            ... = a + b         : by rw (abs_of_nonneg h1)
            ... = abs a + b     : by rw (abs_of_nonneg h2)
            ... = abs a + abs b : by rw (abs_of_nonneg h3))
 (assume h3 : ¬ b ≥ 0,
  have h4 : b ≤ 0, from le_of_lt (lt_of_not_ge h3),
  calc
    abs (a + b) = a + b         : by rw (abs_of_nonneg h1)
            ... = abs a + b     : by rw (abs_of_nonneg h2)
            ... ≤ abs a + 0     : add_le_add_left h4 _
            ... ≤ abs a + -b    : add_le_add_left (neg_nonneg_of_nonpos h4) _
            ... = abs a + abs b : by rw (abs_of_nonpos h4))

private lemma aux2 {a b : α} (h1 : a + b ≥ 0) : abs (a + b) ≤ abs a + abs b :=
or.elim (le_total b 0)
 (assume h2 : b ≤ 0,
  have h3 : ¬ a < 0, from
    assume h4 : a < 0,
    have h5 : a + b < 0,
      begin
        have aux := add_lt_add_of_lt_of_le h4 h2,
        rwa [add_zero] at aux
      end,
    not_lt_of_ge h1 h5,
  aux1 h1 (le_of_not_gt h3))
 (assume h2 : 0 ≤ b,
  begin
    have h3 : abs (b + a) ≤ abs b + abs a,
    begin
      rw add_comm at h1,
      exact aux1 h1 h2
    end,
    rw [add_comm, add_comm (abs a)],
    exact h3
  end)

lemma abs_add_le_abs_add_abs (a b : α) : abs (a + b) ≤ abs a + abs b :=
or.elim (le_total 0 (a + b))
  (assume h2 : 0 ≤ a + b, aux2 h2)
  (assume h2 : a + b ≤ 0,
   have h3 : -a + -b = -(a + b), by rw neg_add,
   have h4 : -(a + b) ≥ 0, from neg_nonneg_of_nonpos h2,
   have h5   : -a + -b ≥ 0, begin rw [← h3] at h4, exact h4 end,
   calc
      abs (a + b) = abs (-a + -b)   : by rw [← abs_neg, neg_add]
              ... ≤ abs (-a) + abs (-b) : aux2 h5
              ... = abs a + abs b       : by rw [abs_neg, abs_neg])

lemma abs_sub_abs_le_abs_sub (a b : α) : abs a - abs b ≤ abs (a - b) :=
have h1 : abs a - abs b + abs b ≤ abs (a - b) + abs b, from
calc
   abs a - abs b + abs b = abs a                 : by rw sub_add_cancel
                     ... = abs (a - b + b)       : by rw sub_add_cancel
                     ... ≤ abs (a - b) + abs b   : by apply abs_add_le_abs_add_abs,
le_of_add_le_add_right h1

lemma abs_sub_le (a b c : α) : abs (a - c) ≤ abs (a - b) + abs (b - c) :=
calc
    abs (a - c) = abs (a - b + (b - c))     : by rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg,
                                                    add_assoc, neg_add_cancel_left]
            ... ≤ abs (a - b) + abs (b - c) : by apply abs_add_le_abs_add_abs

lemma abs_add_three (a b c : α) : abs (a + b + c) ≤ abs a + abs b + abs c :=
begin
  apply le_trans,
  apply abs_add_le_abs_add_abs,
  apply le_trans,
  apply add_le_add_right,
  apply abs_add_le_abs_add_abs,
  apply le_refl
end

lemma dist_bdd_within_interval {a b lb ub : α} (h : lb < ub) (hal : lb ≤ a) (hau : a ≤ ub)
      (hbl : lb ≤ b) (hbu : b ≤ ub) : abs (a - b) ≤ ub - lb :=
begin
  cases (decidable.em (b ≤ a)) with hba hba,
  rw (abs_of_nonneg (sub_nonneg_of_le hba)),
  apply sub_le_sub,
  apply hau,
  apply hbl,
  rw [abs_of_neg (sub_neg_of_lt (lt_of_not_ge hba)), neg_sub],
  apply sub_le_sub,
  apply hbu,
  apply hal
end

lemma decidable_linear_ordered_add_comm_group.eq_of_abs_sub_nonpos
  {a b : α} (h : abs (a - b) ≤ 0) : a = b :=
eq_of_abs_sub_eq_zero (le_antisymm h (abs_nonneg (a - b)))

end decidable_linear_ordered_add_comm_group

set_option old_structure_cmd true
section prio
set_option default_priority 100 -- see Note [default priority]
/-- This is not so much a new structure as a construction mechanism
  for ordered groups, by specifying only the "positive cone" of the group. -/
class nonneg_add_comm_group (α : Type*) extends add_comm_group α :=
(nonneg : α → Prop)
(pos : α → Prop := λ a, nonneg a ∧ ¬ nonneg (neg a))
(pos_iff : ∀ a, pos a ↔ nonneg a ∧ ¬ nonneg (-a) . order_laws_tac)
(zero_nonneg : nonneg 0)
(add_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a + b))
(nonneg_antisymm : ∀ {a}, nonneg a → nonneg (-a) → a = 0)
end prio

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
A `nonneg_add_comm_group` is a `decidable_linear_ordered_add_comm_group`
if `nonneg` is total and decidable.
-/
def to_decidable_linear_ordered_add_comm_group
  [decidable_pred (@nonneg α _)]
  (nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a))
  : decidable_linear_ordered_add_comm_group α :=
{ le := (≤),
  lt := (<),
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  le_refl := @le_refl _ _,
  le_trans := @le_trans _ _,
  le_antisymm := @le_antisymm _ _,
  le_total := nonneg_total_iff.1 nonneg_total,
  decidable_le := by apply_instance,
  decidable_lt := by apply_instance,
  ..@nonneg_add_comm_group.to_ordered_add_comm_group _ s }

end nonneg_add_comm_group

namespace order_dual

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (order_dual α) :=
{ add_le_add_left := λ a b h c, @add_le_add_left' α _ b a c h,
  lt_of_add_lt_add_left := λ a b c h, @lt_of_add_lt_add_left' α _ a c b h,
  ..order_dual.partial_order α,
  ..show add_comm_monoid α, by apply_instance }

instance [ordered_cancel_add_comm_monoid α] : ordered_cancel_add_comm_monoid (order_dual α) :=
{ le_of_add_le_add_left := λ a b c : α, le_of_add_le_add_left,
  add_left_cancel := @add_left_cancel α _,
  add_right_cancel := @add_right_cancel α _,
  ..order_dual.ordered_add_comm_monoid }

instance [ordered_add_comm_group α] : ordered_add_comm_group (order_dual α) :=
{ add_left_neg := λ a : α, add_left_neg a,
  ..order_dual.ordered_add_comm_monoid,
  ..show add_comm_group α, by apply_instance }

end order_dual
