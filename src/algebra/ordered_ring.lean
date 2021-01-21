/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import data.set.intervals.basic

set_option old_structure_cmd true

universe u
variable {α : Type u}

/-- An `ordered_semiring α` is a semiring `α` with a partial order such that
multiplication with a positive number and addition are monotone. -/
@[protect_proj]
class ordered_semiring (α : Type u) extends semiring α, ordered_cancel_add_comm_monoid α :=
(zero_le_one : 0 ≤ (1 : α))
(mul_lt_mul_of_pos_left :  ∀ a b c : α, a < b → 0 < c → c * a < c * b)
(mul_lt_mul_of_pos_right : ∀ a b c : α, a < b → 0 < c → a * c < b * c)

section ordered_semiring
variables [ordered_semiring α] {a b c d : α}

lemma zero_le_one : 0 ≤ (1:α) :=
ordered_semiring.zero_le_one

lemma zero_le_two : 0 ≤ (2:α) :=
add_nonneg zero_le_one zero_le_one

section nontrivial

variables [nontrivial α]

lemma zero_lt_one : 0 < (1 : α) :=
lt_of_le_of_ne zero_le_one zero_ne_one

lemma zero_lt_two : 0 < (2:α) := add_pos zero_lt_one zero_lt_one

@[field_simps] lemma two_ne_zero : (2:α) ≠ 0 :=
ne.symm (ne_of_lt zero_lt_two)

lemma one_lt_two : 1 < (2:α) :=
calc (2:α) = 1+1 : one_add_one_eq_two
     ...   > 1+0 : add_lt_add_left zero_lt_one _
     ...   = 1   : add_zero 1

lemma one_le_two : 1 ≤ (2:α) := one_lt_two.le

lemma zero_lt_three : 0 < (3:α) := add_pos zero_lt_two zero_lt_one

lemma zero_lt_four : 0 < (4:α) := add_pos zero_lt_two zero_lt_two

end nontrivial

lemma mul_lt_mul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
ordered_semiring.mul_lt_mul_of_pos_left a b c h₁ h₂

lemma mul_lt_mul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
ordered_semiring.mul_lt_mul_of_pos_right a b c h₁ h₂

lemma mul_le_mul_of_nonneg_left (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
begin
  cases classical.em (b ≤ a), { simp [h.antisymm h₁] },
  cases classical.em (c ≤ 0), { simp [h_1.antisymm h₂] },
  exact (mul_lt_mul_of_pos_left (h₁.lt_of_not_le h) (h₂.lt_of_not_le h_1)).le,
end

lemma mul_le_mul_of_nonneg_right (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c :=
begin
  cases classical.em (b ≤ a), { simp [h.antisymm h₁] },
  cases classical.em (c ≤ 0), { simp [h_1.antisymm h₂] },
  exact (mul_lt_mul_of_pos_right (h₁.lt_of_not_le h) (h₂.lt_of_not_le h_1)).le,
end

-- TODO: there are four variations, depending on which variables we assume to be nonneg
lemma mul_le_mul (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) : a * b ≤ c * d :=
calc
  a * b ≤ c * b : mul_le_mul_of_nonneg_right hac nn_b
    ... ≤ c * d : mul_le_mul_of_nonneg_left hbd nn_c

lemma mul_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
have h : 0 * b ≤ a * b, from mul_le_mul_of_nonneg_right ha hb,
by rwa [zero_mul] at h

lemma mul_nonpos_of_nonneg_of_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 :=
have h : a * b ≤ a * 0, from mul_le_mul_of_nonneg_left hb ha,
by rwa mul_zero at h

lemma mul_nonpos_of_nonpos_of_nonneg (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 :=
have h : a * b ≤ 0 * b, from mul_le_mul_of_nonneg_right ha hb,
by rwa zero_mul at h

lemma mul_lt_mul (hac : a < c) (hbd : b ≤ d) (pos_b : 0 < b) (nn_c : 0 ≤ c) : a * b < c * d :=
calc
  a * b < c * b : mul_lt_mul_of_pos_right hac pos_b
    ... ≤ c * d : mul_le_mul_of_nonneg_left hbd nn_c

lemma mul_lt_mul' (h1 : a ≤ c) (h2 : b < d) (h3 : 0 ≤ b) (h4 : 0 < c) : a * b < c * d :=
calc
   a * b ≤ c * b : mul_le_mul_of_nonneg_right h1 h3
     ... < c * d : mul_lt_mul_of_pos_left h2 h4

lemma mul_pos (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
have h : 0 * b < a * b, from mul_lt_mul_of_pos_right ha hb,
by rwa zero_mul at h

lemma mul_neg_of_pos_of_neg (ha : 0 < a) (hb : b < 0) : a * b < 0 :=
have h : a * b < a * 0, from mul_lt_mul_of_pos_left hb ha,
by rwa mul_zero at h

lemma mul_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a * b < 0 :=
have h : a * b < 0 * b, from mul_lt_mul_of_pos_right ha hb,
by rwa zero_mul at  h

lemma mul_self_lt_mul_self (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
mul_lt_mul' h2.le h2 h1 $ h1.trans_lt h2

lemma strict_mono_incr_on_mul_self : strict_mono_incr_on (λ x : α, x * x) (set.Ici 0) :=
λ x hx y hy hxy, mul_self_lt_mul_self hx hxy

lemma mul_self_le_mul_self (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
mul_le_mul h2 h2 h1 $ h1.trans h2

lemma mul_lt_mul'' (h1 : a < c) (h2 : b < d) (h3 : 0 ≤ a) (h4 : 0 ≤ b) : a * b < c * d :=
(lt_or_eq_of_le h4).elim
  (λ b0, mul_lt_mul h1 h2.le b0 $ h3.trans h1.le)
  (λ b0, by rw [← b0, mul_zero]; exact
    mul_pos (h3.trans_lt h1) (h4.trans_lt h2))

lemma le_mul_of_one_le_right (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ b * a :=
suffices b * 1 ≤ b * a, by rwa mul_one at this,
mul_le_mul_of_nonneg_left h hb

lemma le_mul_of_one_le_left (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b :=
suffices 1 * b ≤ a * b, by rwa one_mul at this,
mul_le_mul_of_nonneg_right h hb

section
variable [nontrivial α]

lemma bit1_pos (h : 0 ≤ a) : 0 < bit1 a :=
lt_add_of_le_of_pos (add_nonneg h h) zero_lt_one

lemma lt_add_one (a : α) : a < a + 1 :=
lt_add_of_le_of_pos le_rfl zero_lt_one

lemma lt_one_add (a : α) : a < 1 + a :=
by { rw [add_comm], apply lt_add_one }

end

lemma bit1_pos' (h : 0 < a) : 0 < bit1 a :=
begin
  nontriviality,
  exact bit1_pos h.le,
end

lemma one_lt_mul (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
begin
  nontriviality,
  exact (one_mul (1 : α)) ▸ mul_lt_mul' ha hb zero_le_one (zero_lt_one.trans_le ha)
end

lemma mul_le_one (ha : a ≤ 1) (hb' : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
begin rw ← one_mul (1 : α), apply mul_le_mul; {assumption <|> apply zero_le_one} end

lemma one_lt_mul_of_le_of_lt (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
begin
  nontriviality,
  calc 1 = 1 * 1 : by rw one_mul
     ... < a * b : mul_lt_mul' ha hb zero_le_one (zero_lt_one.trans_le ha)
end

lemma one_lt_mul_of_lt_of_le (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
begin
  nontriviality,
  calc 1 = 1 * 1 : by rw one_mul
    ... < a * b : mul_lt_mul ha hb zero_lt_one $ zero_le_one.trans ha.le
end

lemma mul_le_of_le_one_right (ha : 0 ≤ a) (hb1 : b ≤ 1) : a * b ≤ a :=
calc a * b ≤ a * 1 : mul_le_mul_of_nonneg_left hb1 ha
... = a : mul_one a

lemma mul_le_of_le_one_left (hb : 0 ≤ b) (ha1 : a ≤ 1) : a * b ≤ b :=
calc a * b ≤ 1 * b : mul_le_mul ha1 le_rfl hb zero_le_one
... = b : one_mul b

lemma mul_lt_one_of_nonneg_of_lt_one_left (ha0 : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
calc a * b ≤ a : mul_le_of_le_one_right ha0 hb
... < 1 : ha

lemma mul_lt_one_of_nonneg_of_lt_one_right (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b < 1) : a * b < 1 :=
calc a * b ≤ b : mul_le_of_le_one_left hb0 ha
... < 1 : hb

end ordered_semiring

section ordered_comm_semiring

/-- An `ordered_comm_semiring α` is a commutative semiring `α` with a partial order such that
multiplication with a positive number and addition are monotone. -/
@[protect_proj]
class ordered_comm_semiring (α : Type u) extends ordered_semiring α, comm_semiring α

end ordered_comm_semiring

/--
A `linear_ordered_semiring α` is a nontrivial semiring `α` with a linear order
such that multiplication with a positive number and addition are monotone.
-/
-- It's not entirely clear we should assume `nontrivial` at this point;
-- it would be reasonable to explore changing this,
-- but be warned that the instances involving `domain` may cause
-- typeclass search loops.
@[protect_proj]
class linear_ordered_semiring (α : Type u) extends ordered_semiring α, linear_order α, nontrivial α

section linear_ordered_semiring
variables [linear_ordered_semiring α] {a b c d : α}

-- `norm_num` expects the lemma stating `0 < 1` to have a single typeclass argument
-- (see `norm_num.prove_pos_nat`).
-- Rather than working out how to relax that assumption,
-- we provide a synonym for `zero_lt_one` (which needs both `ordered_semiring α` and `nontrivial α`)
-- with only a `linear_ordered_semiring` typeclass argument.
lemma zero_lt_one' : 0 < (1 : α) := zero_lt_one

lemma lt_of_mul_lt_mul_left (h : c * a < c * b) (hc : 0 ≤ c) : a < b :=
lt_of_not_ge
  (assume h1 : b ≤ a,
   have h2 : c * b ≤ c * a, from mul_le_mul_of_nonneg_left h1 hc,
   h2.not_lt h)

lemma lt_of_mul_lt_mul_right (h : a * c < b * c) (hc : 0 ≤ c) : a < b :=
lt_of_not_ge
  (assume h1 : b ≤ a,
   have h2 : b * c ≤ a * c, from mul_le_mul_of_nonneg_right h1 hc,
   h2.not_lt h)

lemma le_of_mul_le_mul_left (h : c * a ≤ c * b) (hc : 0 < c) : a ≤ b :=
le_of_not_gt
  (assume h1 : b < a,
   have h2 : c * b < c * a, from mul_lt_mul_of_pos_left h1 hc,
   h2.not_le h)

lemma le_of_mul_le_mul_right (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b :=
le_of_not_gt
  (assume h1 : b < a,
   have h2 : b * c < a * c, from mul_lt_mul_of_pos_right h1 hc,
   h2.not_le h)

lemma pos_and_pos_or_neg_and_neg_of_mul_pos (hab : 0 < a * b) :
  (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) :=
begin
  rcases lt_trichotomy 0 a with (ha|rfl|ha),
  { refine or.inl ⟨ha, _⟩,
    contrapose! hab,
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hab },
  { rw [zero_mul] at hab, exact hab.false.elim },
  { refine or.inr ⟨ha, _⟩,
    contrapose! hab,
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hab }
end

lemma nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg (hab : 0 ≤ a * b) :
    (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0) :=
begin
  contrapose! hab,
  rcases lt_trichotomy 0 a with (ha|rfl|ha),
  exacts [mul_neg_of_pos_of_neg ha (hab.1 ha.le), ((hab.1 le_rfl).asymm (hab.2 le_rfl)).elim,
    mul_neg_of_neg_of_pos ha (hab.2 ha.le)]
end

lemma pos_of_mul_pos_left (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_right $ λ h, h.1.not_le ha).2

lemma pos_of_mul_pos_right (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_right $ λ h, h.2.not_le hb).1

lemma nonneg_of_mul_nonneg_left (h : 0 ≤ a * b) (h1 : 0 < a) : 0 ≤ b :=
le_of_not_gt (assume h2 : b < 0, (mul_neg_of_pos_of_neg h1 h2).not_le h)

lemma nonneg_of_mul_nonneg_right (h : 0 ≤ a * b) (h1 : 0 < b) : 0 ≤ a :=
le_of_not_gt (assume h2 : a < 0, (mul_neg_of_neg_of_pos h2 h1).not_le h)

lemma neg_of_mul_neg_left (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
lt_of_not_ge (assume h2 : b ≥ 0, (mul_nonneg h1 h2).not_lt h)

lemma neg_of_mul_neg_right (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
lt_of_not_ge (assume h2 : a ≥ 0, (mul_nonneg h2 h1).not_lt h)

lemma nonpos_of_mul_nonpos_left (h : a * b ≤ 0) (h1 : 0 < a) : b ≤ 0 :=
le_of_not_gt (assume h2 : b > 0, (mul_pos h1 h2).not_le h)

lemma nonpos_of_mul_nonpos_right (h : a * b ≤ 0) (h1 : 0 < b) : a ≤ 0 :=
le_of_not_gt (assume h2 : a > 0, (mul_pos h2 h1).not_le h)

@[simp] lemma mul_le_mul_left (h : 0 < c) : c * a ≤ c * b ↔ a ≤ b :=
⟨λ h', le_of_mul_le_mul_left h' h, λ h', mul_le_mul_of_nonneg_left h' h.le⟩

@[simp] lemma mul_le_mul_right (h : 0 < c) : a * c ≤ b * c ↔ a ≤ b :=
⟨λ h', le_of_mul_le_mul_right h' h, λ h', mul_le_mul_of_nonneg_right h' h.le⟩

@[simp] lemma mul_lt_mul_left (h : 0 < c) : c * a < c * b ↔ a < b :=
⟨lt_imp_lt_of_le_imp_le $ λ h', mul_le_mul_of_nonneg_left h' h.le,
 λ h', mul_lt_mul_of_pos_left h' h⟩

@[simp] lemma mul_lt_mul_right (h : 0 < c) : a * c < b * c ↔ a < b :=
⟨lt_imp_lt_of_le_imp_le $ λ h', mul_le_mul_of_nonneg_right h' h.le,
 λ h', mul_lt_mul_of_pos_right h' h⟩

@[simp] lemma zero_le_mul_left (h : 0 < c) : 0 ≤ c * b ↔ 0 ≤ b :=
by { convert mul_le_mul_left h, simp }

@[simp] lemma zero_le_mul_right (h : 0 < c) : 0 ≤ b * c ↔ 0 ≤ b :=
by { convert mul_le_mul_right h, simp }

@[simp] lemma zero_lt_mul_left (h : 0 < c) : 0 < c * b ↔ 0 < b :=
by { convert mul_lt_mul_left h, simp }

@[simp] lemma zero_lt_mul_right (h : 0 < c) : 0 < b * c ↔ 0 < b :=
by { convert mul_lt_mul_right h, simp }

section
variables [nontrivial α]

@[simp] lemma bit0_le_bit0 : bit0 a ≤ bit0 b ↔ a ≤ b :=
by rw [bit0, bit0, ← two_mul, ← two_mul, mul_le_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma bit0_lt_bit0 : bit0 a < bit0 b ↔ a < b :=
by rw [bit0, bit0, ← two_mul, ← two_mul, mul_lt_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma bit1_le_bit1 : bit1 a ≤ bit1 b ↔ a ≤ b :=
(add_le_add_iff_right 1).trans bit0_le_bit0

@[simp] lemma bit1_lt_bit1 : bit1 a < bit1 b ↔ a < b :=
(add_lt_add_iff_right 1).trans bit0_lt_bit0

@[simp] lemma one_le_bit1 : (1 : α) ≤ bit1 a ↔ 0 ≤ a :=
by rw [bit1, le_add_iff_nonneg_left, bit0, ← two_mul, zero_le_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma one_lt_bit1 : (1 : α) < bit1 a ↔ 0 < a :=
by rw [bit1, lt_add_iff_pos_left, bit0, ← two_mul, zero_lt_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma zero_le_bit0 : (0 : α) ≤ bit0 a ↔ 0 ≤ a :=
by rw [bit0, ← two_mul, zero_le_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma zero_lt_bit0 : (0 : α) < bit0 a ↔ 0 < a :=
by rw [bit0, ← two_mul, zero_lt_mul_left (zero_lt_two : 0 < (2:α))]

end

lemma le_mul_iff_one_le_left (hb : 0 < b) : b ≤ a * b ↔ 1 ≤ a :=
suffices 1 * b ≤ a * b ↔ 1 ≤ a, by rwa one_mul at this,
mul_le_mul_right hb

lemma lt_mul_iff_one_lt_left (hb : 0 < b) : b < a * b ↔ 1 < a :=
suffices 1 * b < a * b ↔ 1 < a, by rwa one_mul at this,
mul_lt_mul_right hb

lemma le_mul_iff_one_le_right (hb : 0 < b) : b ≤ b * a ↔ 1 ≤ a :=
suffices b * 1 ≤ b * a ↔ 1 ≤ a, by rwa mul_one at this,
mul_le_mul_left hb

lemma lt_mul_iff_one_lt_right (hb : 0 < b) : b < b * a ↔ 1 < a :=
suffices b * 1 < b * a ↔ 1 < a, by rwa mul_one at this,
mul_lt_mul_left hb

lemma lt_mul_of_one_lt_right (hb : 0 < b) : 1 < a → b < b * a :=
(lt_mul_iff_one_lt_right hb).2

theorem mul_nonneg_iff_right_nonneg_of_pos (h : 0 < a) : 0 ≤ b * a ↔ 0 ≤ b :=
⟨assume : 0 ≤ b * a, nonneg_of_mul_nonneg_right this h, assume : 0 ≤ b, mul_nonneg this h.le⟩

lemma mul_le_iff_le_one_left (hb : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
⟨ λ h, le_of_not_lt (mt (lt_mul_iff_one_lt_left hb).2 h.not_lt),
  λ h, le_of_not_lt (mt (lt_mul_iff_one_lt_left hb).1 h.not_lt) ⟩

lemma mul_lt_iff_lt_one_left (hb : 0 < b) : a * b < b ↔ a < 1 :=
⟨ λ h, lt_of_not_ge (mt (le_mul_iff_one_le_left hb).2 h.not_le),
  λ h, lt_of_not_ge (mt (le_mul_iff_one_le_left hb).1 h.not_le) ⟩

lemma mul_le_iff_le_one_right (hb : 0 < b) : b * a ≤ b ↔ a ≤ 1 :=
⟨ λ h, le_of_not_lt (mt (lt_mul_iff_one_lt_right hb).2 h.not_lt),
  λ h, le_of_not_lt (mt (lt_mul_iff_one_lt_right hb).1 h.not_lt) ⟩

lemma mul_lt_iff_lt_one_right (hb : 0 < b) : b * a < b ↔ a < 1 :=
⟨ λ h, lt_of_not_ge (mt (le_mul_iff_one_le_right hb).2 h.not_le),
  λ h, lt_of_not_ge (mt (le_mul_iff_one_le_right hb).1 h.not_le) ⟩

lemma nonpos_of_mul_nonneg_left (h : 0 ≤ a * b) (hb : b < 0) : a ≤ 0 :=
le_of_not_gt (λ ha, absurd h (mul_neg_of_pos_of_neg ha hb).not_le)

lemma nonpos_of_mul_nonneg_right (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0 :=
le_of_not_gt (λ hb, absurd h (mul_neg_of_neg_of_pos ha hb).not_le)

lemma neg_of_mul_pos_left (h : 0 < a * b) (hb : b ≤ 0) : a < 0 :=
lt_of_not_ge (λ ha, absurd h (mul_nonpos_of_nonneg_of_nonpos ha hb).not_lt)

lemma neg_of_mul_pos_right (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
lt_of_not_ge (λ hb, absurd h (mul_nonpos_of_nonpos_of_nonneg ha hb).not_lt)

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_semiring.to_no_top_order {α : Type*} [linear_ordered_semiring α] :
  no_top_order α :=
⟨assume a, ⟨a + 1, lt_add_of_pos_right _ zero_lt_one⟩⟩

end linear_ordered_semiring

section mono
variables {β : Type*} [linear_ordered_semiring α] [preorder β] {f g : β → α} {a : α}

lemma monotone_mul_left_of_nonneg (ha : 0 ≤ a) : monotone (λ x, a*x) :=
assume b c b_le_c, mul_le_mul_of_nonneg_left b_le_c ha

lemma monotone_mul_right_of_nonneg (ha : 0 ≤ a) : monotone (λ x, x*a) :=
assume b c b_le_c, mul_le_mul_of_nonneg_right b_le_c ha

lemma monotone.mul_const (hf : monotone f) (ha : 0 ≤ a) :
  monotone (λ x, (f x) * a) :=
(monotone_mul_right_of_nonneg ha).comp hf

lemma monotone.const_mul (hf : monotone f) (ha : 0 ≤ a) :
  monotone (λ x, a * (f x)) :=
(monotone_mul_left_of_nonneg ha).comp hf

lemma monotone.mul (hf : monotone f) (hg : monotone g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
  monotone (λ x, f x * g x) :=
λ x y h, mul_le_mul (hf h) (hg h) (hg0 x) (hf0 y)

lemma strict_mono_mul_left_of_pos (ha : 0 < a) : strict_mono (λ x, a * x) :=
assume b c b_lt_c, (mul_lt_mul_left ha).2 b_lt_c

lemma strict_mono_mul_right_of_pos (ha : 0 < a) : strict_mono (λ x, x * a) :=
assume b c b_lt_c, (mul_lt_mul_right ha).2 b_lt_c

lemma strict_mono.mul_const (hf : strict_mono f) (ha : 0 < a) :
  strict_mono (λ x, (f x) * a) :=
(strict_mono_mul_right_of_pos ha).comp hf

lemma strict_mono.const_mul (hf : strict_mono f) (ha : 0 < a) :
  strict_mono (λ x, a * (f x)) :=
(strict_mono_mul_left_of_pos ha).comp hf

lemma strict_mono.mul_monotone (hf : strict_mono f) (hg : monotone g) (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 < g x) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul (hf h) (hg h.le) (hg0 x) (hf0 y)

lemma monotone.mul_strict_mono (hf : monotone f) (hg : strict_mono g) (hf0 : ∀ x, 0 < f x)
  (hg0 : ∀ x, 0 ≤ g x) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul' (hf h.le) (hg h) (hg0 x) (hf0 y)

lemma strict_mono.mul (hf : strict_mono f) (hg : strict_mono g) (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 ≤ g x) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul'' (hf h) (hg h) (hf0 x) (hg0 x)

end mono

section linear_ordered_semiring
variables [linear_ordered_semiring α] {a b c : α}

@[simp] lemma decidable.mul_le_mul_left (h : 0 < c) : c * a ≤ c * b ↔ a ≤ b :=
decidable.le_iff_le_iff_lt_iff_lt.2 $ mul_lt_mul_left h

@[simp] lemma decidable.mul_le_mul_right (h : 0 < c) : a * c ≤ b * c ↔ a ≤ b :=
decidable.le_iff_le_iff_lt_iff_lt.2 $ mul_lt_mul_right h

lemma mul_max_of_nonneg (b c : α) (ha : 0 ≤ a) : a * max b c = max (a * b) (a * c) :=
(monotone_mul_left_of_nonneg ha).map_max

lemma mul_min_of_nonneg (b c : α) (ha : 0 ≤ a) : a * min b c = min (a * b) (a * c) :=
(monotone_mul_left_of_nonneg ha).map_min

lemma max_mul_of_nonneg (a b : α) (hc : 0 ≤ c) : max a b * c = max (a * c) (b * c) :=
(monotone_mul_right_of_nonneg hc).map_max

lemma min_mul_of_nonneg (a b : α) (hc : 0 ≤ c) : min a b * c = min (a * c) (b * c) :=
(monotone_mul_right_of_nonneg hc).map_min

end linear_ordered_semiring

/-- An `ordered_ring α` is a ring `α` with a partial order such that
multiplication with a positive number and addition are monotone. -/
@[protect_proj]
class ordered_ring (α : Type u) extends ring α, ordered_add_comm_group α :=
(zero_le_one : 0 ≤ (1 : α))
(mul_pos     : ∀ a b : α, 0 < a → 0 < b → 0 < a * b)

section ordered_ring
variables [ordered_ring α] {a b c : α}

lemma ordered_ring.mul_nonneg (a b : α) (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) : 0 ≤ a * b :=
begin
  cases classical.em (a ≤ 0), { simp [le_antisymm h h₁] },
  cases classical.em (b ≤ 0), { simp [le_antisymm h_1 h₂] },
  exact (le_not_le_of_lt (ordered_ring.mul_pos a b (h₁.lt_of_not_le h) (h₂.lt_of_not_le h_1))).left,
end

lemma ordered_ring.mul_le_mul_of_nonneg_left (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
begin
  rw [← sub_nonneg, ← mul_sub],
  exact ordered_ring.mul_nonneg c (b - a) h₂ (sub_nonneg.2 h₁),
end

lemma ordered_ring.mul_le_mul_of_nonneg_right (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c :=
begin
  rw [← sub_nonneg, ← sub_mul],
  exact ordered_ring.mul_nonneg _ _ (sub_nonneg.2 h₁) h₂,
end

lemma ordered_ring.mul_lt_mul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
begin
  rw [← sub_pos, ← mul_sub],
  exact ordered_ring.mul_pos _ _ h₂ (sub_pos.2 h₁),
end

lemma ordered_ring.mul_lt_mul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
begin
  rw [← sub_pos, ← sub_mul],
  exact ordered_ring.mul_pos _ _ (sub_pos.2 h₁) h₂,
end

@[priority 100] -- see Note [lower instance priority]
instance ordered_ring.to_ordered_semiring : ordered_semiring α :=
{ mul_zero                   := mul_zero,
  zero_mul                   := zero_mul,
  add_left_cancel            := @add_left_cancel α _,
  add_right_cancel           := @add_right_cancel α _,
  le_of_add_le_add_left      := @le_of_add_le_add_left α _,
  mul_lt_mul_of_pos_left     := @ordered_ring.mul_lt_mul_of_pos_left α _,
  mul_lt_mul_of_pos_right    := @ordered_ring.mul_lt_mul_of_pos_right α _,
  ..‹ordered_ring α› }

lemma mul_le_mul_of_nonpos_left {a b c : α} (h : b ≤ a) (hc : c ≤ 0) : c * a ≤ c * b :=
have -c ≥ 0,              from neg_nonneg_of_nonpos hc,
have -c * b ≤ -c * a,     from mul_le_mul_of_nonneg_left h this,
have -(c * b) ≤ -(c * a), by rwa [← neg_mul_eq_neg_mul, ← neg_mul_eq_neg_mul] at this,
le_of_neg_le_neg this

lemma mul_le_mul_of_nonpos_right {a b c : α} (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c :=
have -c ≥ 0,              from neg_nonneg_of_nonpos hc,
have b * -c ≤ a * -c,     from mul_le_mul_of_nonneg_right h this,
have -(b * c) ≤ -(a * c), by rwa [← neg_mul_eq_mul_neg, ← neg_mul_eq_mul_neg] at this,
le_of_neg_le_neg this

lemma mul_nonneg_of_nonpos_of_nonpos {a b : α} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b :=
have 0 * b ≤ a * b, from mul_le_mul_of_nonpos_right ha hb,
by rwa zero_mul at this

lemma mul_lt_mul_of_neg_left {a b c : α} (h : b < a) (hc : c < 0) : c * a < c * b :=
have -c > 0,              from neg_pos_of_neg hc,
have -c * b < -c * a,     from mul_lt_mul_of_pos_left h this,
have -(c * b) < -(c * a), by rwa [← neg_mul_eq_neg_mul, ← neg_mul_eq_neg_mul] at this,
lt_of_neg_lt_neg this

lemma mul_lt_mul_of_neg_right {a b c : α} (h : b < a) (hc : c < 0) : a * c < b * c :=
have -c > 0,              from neg_pos_of_neg hc,
have b * -c < a * -c,     from mul_lt_mul_of_pos_right h this,
have -(b * c) < -(a * c), by rwa [← neg_mul_eq_mul_neg, ← neg_mul_eq_mul_neg] at this,
lt_of_neg_lt_neg this

lemma mul_pos_of_neg_of_neg {a b : α} (ha : a < 0) (hb : b < 0) : 0 < a * b :=
have 0 * b < a * b, from mul_lt_mul_of_neg_right ha hb,
by rwa zero_mul at this

end ordered_ring

section ordered_comm_ring

/-- An `ordered_comm_ring α` is a commutative ring `α` with a partial order such that
multiplication with a positive number and addition are monotone. -/
@[protect_proj]
class ordered_comm_ring (α : Type u) extends ordered_ring α, ordered_comm_semiring α, comm_ring α

end ordered_comm_ring

/-- A `linear_ordered_ring α` is a ring `α` with a linear order such that
multiplication with a positive number and addition are monotone. -/
@[protect_proj] class linear_ordered_ring (α : Type u)
  extends ordered_ring α, linear_order α, nontrivial α

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_ring.to_linear_ordered_add_comm_group [s : linear_ordered_ring α] :
  linear_ordered_add_comm_group α :=
{ .. s }

section linear_ordered_ring
variables [linear_ordered_ring α] {a b c : α}

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_ring.to_linear_ordered_semiring : linear_ordered_semiring α :=
{ mul_zero                   := mul_zero,
  zero_mul                   := zero_mul,
  add_left_cancel            := @add_left_cancel α _,
  add_right_cancel           := @add_right_cancel α _,
  le_of_add_le_add_left      := @le_of_add_le_add_left α _,
  mul_lt_mul_of_pos_left     := @mul_lt_mul_of_pos_left α _,
  mul_lt_mul_of_pos_right    := @mul_lt_mul_of_pos_right α _,
  le_total                   := linear_ordered_ring.le_total,
  ..‹linear_ordered_ring α› }

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_ring.to_domain : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero :=
    begin
      intros a b hab,
      contrapose! hab,
      cases (lt_or_gt_of_ne hab.1) with ha ha; cases (lt_or_gt_of_ne hab.2) with hb hb,
      exacts [(mul_pos_of_neg_of_neg ha hb).ne.symm, (mul_neg_of_neg_of_pos ha hb).ne,
        (mul_neg_of_pos_of_neg ha hb).ne, (mul_pos ha hb).ne.symm]
    end,
  .. ‹linear_ordered_ring α› }

@[simp] lemma abs_one : abs (1 : α) = 1 := abs_of_pos zero_lt_one
@[simp] lemma abs_two : abs (2 : α) = 2 := abs_of_pos zero_lt_two

lemma abs_mul (a b : α) : abs (a * b) = abs a * abs b :=
begin
  rw [abs_eq (mul_nonneg (abs_nonneg a) (abs_nonneg b))],
  cases le_total a 0 with ha ha; cases le_total b 0 with hb hb;
    simp [abs_of_nonpos, abs_of_nonneg, *]
end

/-- `abs` as a `monoid_with_zero_hom`. -/
def abs_hom : monoid_with_zero_hom α α := ⟨abs, abs_zero, abs_one, abs_mul⟩

@[simp] lemma abs_mul_abs_self (a : α) : abs a * abs a = a * a :=
abs_by_cases (λ x, x * x = a * a) rfl (neg_mul_neg a a)

@[simp] lemma abs_mul_self (a : α) : abs (a * a) = a * a :=
by rw [abs_mul, abs_mul_abs_self]

lemma mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 :=
⟨pos_and_pos_or_neg_and_neg_of_mul_pos,
  λ h, h.elim (and_imp.2 mul_pos) (and_imp.2 mul_pos_of_neg_of_neg)⟩

lemma mul_neg_iff : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b :=
by rw [← neg_pos, neg_mul_eq_mul_neg, mul_pos_iff, neg_pos, neg_lt_zero]

lemma mul_nonneg_iff : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg,
  λ h, h.elim (and_imp.2 mul_nonneg) (and_imp.2 mul_nonneg_of_nonpos_of_nonpos)⟩

lemma mul_nonpos_iff : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b :=
by rw [← neg_nonneg, neg_mul_eq_mul_neg, mul_nonneg_iff, neg_nonneg, neg_nonpos]

lemma mul_self_nonneg (a : α) : 0 ≤ a * a :=
abs_mul_self a ▸ abs_nonneg _

@[simp] lemma neg_le_self_iff : -a ≤ a ↔ 0 ≤ a :=
by simp [neg_le_iff_add_nonneg, ← two_mul, mul_nonneg_iff, zero_le_one, (@zero_lt_two α _ _).not_le]

@[simp] lemma neg_lt_self_iff : -a < a ↔ 0 < a :=
by simp [neg_lt_iff_pos_add, ← two_mul, mul_pos_iff, zero_lt_one, (@zero_lt_two α _ _).not_lt]

@[simp] lemma le_neg_self_iff : a ≤ -a ↔ a ≤ 0 :=
calc a ≤ -a ↔ -(-a) ≤ -a : by rw neg_neg
... ↔ 0 ≤ -a : neg_le_self_iff
... ↔ a ≤ 0 : neg_nonneg

@[simp] lemma lt_neg_self_iff : a < -a ↔ a < 0 :=
calc a < -a ↔ -(-a) < -a : by rw neg_neg
... ↔ 0 < -a : neg_lt_self_iff
... ↔ a < 0 : neg_pos

@[simp] lemma abs_eq_self : abs a = a ↔ 0 ≤ a := by simp [abs]

@[simp] lemma abs_eq_neg_self : abs a = -a ↔ a ≤ 0 := by simp [abs]

lemma gt_of_mul_lt_mul_neg_left (h : c * a < c * b) (hc : c ≤ 0) : b < a :=
have nhc : 0 ≤ -c, from neg_nonneg_of_nonpos hc,
have h2 : -(c * b) < -(c * a), from neg_lt_neg h,
have h3 : (-c) * b < (-c) * a, from calc
     (-c) * b = - (c * b)    : by rewrite neg_mul_eq_neg_mul
          ... < -(c * a)     : h2
          ... = (-c) * a     : by rewrite neg_mul_eq_neg_mul,
lt_of_mul_lt_mul_left h3 nhc

lemma neg_one_lt_zero : -1 < (0:α) := neg_lt_zero.2 zero_lt_one

lemma le_of_mul_le_of_one_le {a b c : α} (h : a * c ≤ b) (hb : 0 ≤ b) (hc : 1 ≤ c) :
  a ≤ b :=
have h' : a * c ≤ b * c, from calc
     a * c ≤ b : h
       ... = b * 1 : by rewrite mul_one
       ... ≤ b * c : mul_le_mul_of_nonneg_left hc hb,
le_of_mul_le_mul_right h' (zero_lt_one.trans_le hc)

lemma nonneg_le_nonneg_of_squares_le {a b : α} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b :=
le_of_not_gt (λhab, (mul_self_lt_mul_self hb hab).not_le h)

lemma mul_self_le_mul_self_iff {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a ≤ b ↔ a * a ≤ b * b :=
⟨mul_self_le_mul_self h1, nonneg_le_nonneg_of_squares_le h2⟩

lemma mul_self_lt_mul_self_iff {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b :=
((@strict_mono_incr_on_mul_self α _).lt_iff_lt h1 h2).symm

lemma mul_self_inj {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a * a = b * b ↔ a = b :=
(@strict_mono_incr_on_mul_self α _).inj_on.eq_iff h1 h2

@[simp] lemma mul_le_mul_left_of_neg {a b c : α} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a :=
⟨le_imp_le_of_lt_imp_lt $ λ h', mul_lt_mul_of_neg_left h' h,
  λ h', mul_le_mul_of_nonpos_left h' h.le⟩

@[simp] lemma mul_le_mul_right_of_neg {a b c : α} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
⟨le_imp_le_of_lt_imp_lt $ λ h', mul_lt_mul_of_neg_right h' h,
  λ h', mul_le_mul_of_nonpos_right h' h.le⟩

@[simp] lemma mul_lt_mul_left_of_neg {a b c : α} (h : c < 0) : c * a < c * b ↔ b < a :=
lt_iff_lt_of_le_iff_le (mul_le_mul_left_of_neg h)

@[simp] lemma mul_lt_mul_right_of_neg {a b c : α} (h : c < 0) : a * c < b * c ↔ b < a :=
lt_iff_lt_of_le_iff_le (mul_le_mul_right_of_neg h)

lemma sub_one_lt (a : α) : a - 1 < a :=
sub_lt_iff_lt_add.2 (lt_add_one a)

lemma mul_self_pos {a : α} (ha : a ≠ 0) : 0 < a * a :=
by rcases lt_trichotomy a 0 with h|h|h;
   [exact mul_pos_of_neg_of_neg h h, exact (ha h).elim, exact mul_pos h h]

lemma mul_self_le_mul_self_of_le_of_neg_le {x y : α} (h₁ : x ≤ y) (h₂ : -x ≤ y) : x * x ≤ y * y :=
begin
  rw [← abs_mul_abs_self x],
  exact mul_self_le_mul_self (abs_nonneg x) (abs_le.2 ⟨neg_le.2 h₂, h₁⟩)
end

lemma nonneg_of_mul_nonpos_left {a b : α} (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a :=
le_of_not_gt (λ ha, absurd h (mul_pos_of_neg_of_neg ha hb).not_le)

lemma nonneg_of_mul_nonpos_right {a b : α} (h : a * b ≤ 0) (ha : a < 0) : 0 ≤ b :=
le_of_not_gt (λ hb, absurd h (mul_pos_of_neg_of_neg ha hb).not_le)

lemma pos_of_mul_neg_left {a b : α} (h : a * b < 0) (hb : b ≤ 0) : 0 < a :=
lt_of_not_ge (λ ha, absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_lt)

lemma pos_of_mul_neg_right {a b : α} (h : a * b < 0) (ha : a ≤ 0) : 0 < b :=
lt_of_not_ge (λ hb, absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_lt)

/-- The sum of two squares is zero iff both elements are zero. -/
lemma mul_self_add_mul_self_eq_zero {x y : α} : x * x + y * y = 0 ↔ x = 0 ∧ y = 0 :=
by rw [add_eq_zero_iff', mul_self_eq_zero, mul_self_eq_zero]; apply mul_self_nonneg

lemma eq_zero_of_mul_self_add_mul_self_eq_zero (h : a * a + b * b = 0) : a = 0 :=
(mul_self_add_mul_self_eq_zero.mp h).left

lemma abs_eq_iff_mul_self_eq : abs a = abs b ↔ a * a = b * b :=
begin
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b],
  exact (mul_self_inj (abs_nonneg a) (abs_nonneg b)).symm,
end

lemma abs_lt_iff_mul_self_lt : abs a < abs b ↔ a * a < b * b :=
begin
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b],
  exact mul_self_lt_mul_self_iff (abs_nonneg a) (abs_nonneg b)
end

lemma abs_le_iff_mul_self_le : abs a ≤ abs b ↔ a * a ≤ b * b :=
begin
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b],
  exact mul_self_le_mul_self_iff (abs_nonneg a) (abs_nonneg b)
end

lemma abs_le_one_iff_mul_self_le_one : abs a ≤ 1 ↔ a * a ≤ 1 :=
by simpa only [abs_one, one_mul] using @abs_le_iff_mul_self_le α _ a 1

end linear_ordered_ring

/-- A `linear_ordered_comm_ring α` is a commutative ring `α` with a linear order
such that multiplication with a positive number and addition are monotone. -/
@[protect_proj]
class linear_ordered_comm_ring (α : Type u) extends linear_ordered_ring α, comm_monoid α

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_comm_ring.to_ordered_comm_ring [d : linear_ordered_comm_ring α] :
  ordered_comm_ring α :=
-- One might hope that `{ ..linear_ordered_ring.to_linear_ordered_semiring, ..d }`
-- achieved the same result here.
-- Unfortunately with that definition we see mismatched instances in `algebra.star.chsh`.
let s : linear_ordered_semiring α := @linear_ordered_ring.to_linear_ordered_semiring α _ in
{ zero_mul                   := @linear_ordered_semiring.zero_mul α s,
  mul_zero                   := @linear_ordered_semiring.mul_zero α s,
  add_left_cancel            := @linear_ordered_semiring.add_left_cancel α s,
  add_right_cancel           := @linear_ordered_semiring.add_right_cancel α s,
  le_of_add_le_add_left      := @linear_ordered_semiring.le_of_add_le_add_left α s,
  mul_lt_mul_of_pos_left     := @linear_ordered_semiring.mul_lt_mul_of_pos_left α s,
  mul_lt_mul_of_pos_right    := @linear_ordered_semiring.mul_lt_mul_of_pos_right α s,
  ..d }

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_comm_ring.to_integral_domain [s : linear_ordered_comm_ring α] :
  integral_domain α :=
{ ..linear_ordered_ring.to_domain, ..s }

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_comm_ring.to_linear_ordered_semiring [d : linear_ordered_comm_ring α] :
   linear_ordered_semiring α :=
let s : linear_ordered_semiring α := @linear_ordered_ring.to_linear_ordered_semiring α _ in
{ zero_mul                   := @linear_ordered_semiring.zero_mul α s,
  mul_zero                   := @linear_ordered_semiring.mul_zero α s,
  add_left_cancel            := @linear_ordered_semiring.add_left_cancel α s,
  add_right_cancel           := @linear_ordered_semiring.add_right_cancel α s,
  le_of_add_le_add_left      := @linear_ordered_semiring.le_of_add_le_add_left α s,
  mul_lt_mul_of_pos_left     := @linear_ordered_semiring.mul_lt_mul_of_pos_left α s,
  mul_lt_mul_of_pos_right    := @linear_ordered_semiring.mul_lt_mul_of_pos_right α s,
  ..d }

section linear_ordered_comm_ring

variables [linear_ordered_comm_ring α] {a b c d : α}

lemma max_mul_mul_le_max_mul_max (b c : α) (ha : 0 ≤ a) (hd: 0 ≤ d) :
  max (a * b) (d * c) ≤ max a c * max d b :=
have ba : b * a ≤ max d b * max c a,
  from mul_le_mul (le_max_right d b) (le_max_right c a) ha (le_trans hd (le_max_left d b)),
have cd : c * d ≤ max a c * max b d,
  from mul_le_mul (le_max_right a c) (le_max_right b d) hd (le_trans ha (le_max_left a c)),
max_le
  (by simpa [mul_comm, max_comm] using ba)
  (by simpa [mul_comm, max_comm] using cd)

lemma abs_sub_square (a b : α) : abs (a - b) * abs (a - b) = a * a + b * b - (1 + 1) * a * b :=
begin
  rw abs_mul_abs_self,
  simp [left_distrib, right_distrib, add_assoc, add_comm, add_left_comm, mul_comm, sub_eq_add_neg],
end

end linear_ordered_comm_ring

/-- Extend `nonneg_add_comm_group` to support ordered rings
  specified by their nonnegative elements -/
class nonneg_ring (α : Type*) extends ring α, nonneg_add_comm_group α :=
(one_nonneg : nonneg 1)
(mul_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a * b))
(mul_pos : ∀ {a b}, pos a → pos b → pos (a * b))

/-- Extend `nonneg_add_comm_group` to support linearly ordered rings
  specified by their nonnegative elements -/
class linear_nonneg_ring (α : Type*) extends domain α, nonneg_add_comm_group α :=
(one_pos : pos 1)
(mul_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a * b))
(nonneg_total : ∀ a, nonneg a ∨ nonneg (-a))

namespace nonneg_ring
open nonneg_add_comm_group
variable [nonneg_ring α]

/-- `to_linear_nonneg_ring` shows that a `nonneg_ring` with a total order is a `domain`,
hence a `linear_nonneg_ring`. -/
def to_linear_nonneg_ring [nontrivial α]
  (nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a))
  : linear_nonneg_ring α :=
{ one_pos := (pos_iff 1).mpr ⟨one_nonneg, λ h, zero_ne_one (nonneg_antisymm one_nonneg h).symm⟩,
  nonneg_total := nonneg_total,
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    suffices ∀ {a} b : α, nonneg a → a * b = 0 → a = 0 ∨ b = 0,
    from λ a b, (nonneg_total a).elim (this b)
      (λ na, by simpa using this b na),
    suffices ∀ {a b : α}, nonneg a → nonneg b → a * b = 0 → a = 0 ∨ b = 0,
    from λ a b na, (nonneg_total b).elim (this na)
      (λ nb, by simpa using this na nb),
    λ a b na nb z, classical.by_cases
      (λ nna : nonneg (-a), or.inl (nonneg_antisymm na nna))
      (λ pa, classical.by_cases
        (λ nnb : nonneg (-b), or.inr (nonneg_antisymm nb nnb))
        (λ pb, absurd z $ ne_of_gt $ pos_def.1 $ mul_pos
          ((pos_iff _).2 ⟨na, pa⟩)
          ((pos_iff _).2 ⟨nb, pb⟩))),
  ..‹nontrivial α›,
  ..‹nonneg_ring α› }

end nonneg_ring

namespace linear_nonneg_ring
open nonneg_add_comm_group
variable [linear_nonneg_ring α]

@[priority 100] -- see Note [lower instance priority]
instance to_nonneg_ring : nonneg_ring α :=
{ one_nonneg := ((pos_iff _).mp one_pos).1,
  mul_pos := λ a b pa pb,
  let ⟨a1, a2⟩ := (pos_iff a).1 pa,
      ⟨b1, b2⟩ := (pos_iff b).1 pb in
  have ab : nonneg (a * b), from mul_nonneg a1 b1,
  (pos_iff _).2 ⟨ab, λ hn,
    have a * b = 0, from nonneg_antisymm ab hn,
    (eq_zero_or_eq_zero_of_mul_eq_zero _ _ this).elim
      (ne_of_gt (pos_def.1 pa))
      (ne_of_gt (pos_def.1 pb))⟩,
  ..‹linear_nonneg_ring α› }

/-- Construct `linear_order` from `linear_nonneg_ring`. This is not an instance
because we don't use it in `mathlib`. -/
local attribute [instance]
def to_linear_order [decidable_pred (nonneg : α → Prop)] : linear_order α :=
{ le_total := nonneg_total_iff.1 nonneg_total,
  decidable_le := by apply_instance,
  decidable_lt := by apply_instance,
  ..‹linear_nonneg_ring α›, ..(infer_instance : ordered_add_comm_group α) }

/-- Construct `linear_ordered_ring` from `linear_nonneg_ring`.
This is not an instance because we don't use it in `mathlib`. -/
local attribute [instance]
def to_linear_ordered_ring [decidable_pred (nonneg : α → Prop)] : linear_ordered_ring α :=
{ mul_pos := by simp [pos_def.symm]; exact @nonneg_ring.mul_pos _ _,
  zero_le_one := le_of_lt $ lt_of_not_ge $ λ (h : nonneg (0 - 1)), begin
    rw [zero_sub] at h,
    have := mul_nonneg h h, simp at this,
    exact zero_ne_one (nonneg_antisymm this h).symm
  end,
  ..‹linear_nonneg_ring α›, ..(infer_instance : ordered_add_comm_group α),
  ..(infer_instance : linear_order α) }

/-- Convert a `linear_nonneg_ring` with a commutative multiplication and
decidable non-negativity into a `linear_ordered_comm_ring` -/
def to_linear_ordered_comm_ring
  [decidable_pred (@nonneg α _)]
  [comm : @is_commutative α (*)]
  : linear_ordered_comm_ring α :=
{ mul_comm := is_commutative.comm,
  ..@linear_nonneg_ring.to_linear_ordered_ring _ _ _ }

end linear_nonneg_ring

/-- A canonically ordered commutative semiring is an ordered, commutative semiring
in which `a ≤ b` iff there exists `c` with `b = a + c`. This is satisfied by the
natural numbers, for example, but not the integers or other ordered groups. -/
@[protect_proj]
class canonically_ordered_comm_semiring (α : Type*) extends
  canonically_ordered_add_monoid α, comm_semiring α :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)

namespace canonically_ordered_semiring
variables [canonically_ordered_comm_semiring α] {a b : α}

open canonically_ordered_add_monoid (le_iff_exists_add)

@[priority 100] -- see Note [lower instance priority]
instance canonically_ordered_comm_semiring.to_no_zero_divisors :
  no_zero_divisors α :=
⟨canonically_ordered_comm_semiring.eq_zero_or_eq_zero_of_mul_eq_zero⟩

lemma mul_le_mul {a b c d : α} (hab : a ≤ b) (hcd : c ≤ d) : a * c ≤ b * d :=
begin
  rcases (le_iff_exists_add _ _).1 hab with ⟨b, rfl⟩,
  rcases (le_iff_exists_add _ _).1 hcd with ⟨d, rfl⟩,
  suffices : a * c ≤ a * c + (a * d + b * c + b * d), by simpa [mul_add, add_mul, add_assoc],
  exact (le_iff_exists_add _ _).2 ⟨_, rfl⟩
end

lemma mul_le_mul_left' {b c : α} (h : b ≤ c) (a : α) : a * b ≤ a * c :=
mul_le_mul le_rfl h

lemma mul_le_mul_right' {b c : α} (h : b ≤ c) (a : α) : b * a ≤ c * a :=
mul_le_mul h le_rfl

/-- A version of `zero_lt_one : 0 < 1` for a `canonically_ordered_comm_semiring`. -/
lemma zero_lt_one [nontrivial α] : (0:α) < 1 := (zero_le 1).lt_of_ne zero_ne_one

lemma mul_pos : 0 < a * b ↔ (0 < a) ∧ (0 < b) :=
by simp only [pos_iff_ne_zero, ne.def, mul_eq_zero, not_or_distrib]

end canonically_ordered_semiring

namespace with_top

instance [nonempty α] : nontrivial (with_top α) :=
option.nontrivial

variable [decidable_eq α]

section has_mul

variables [has_zero α] [has_mul α]

instance : mul_zero_class (with_top α) :=
{ zero := 0,
  mul := λm n, if m = 0 ∨ n = 0 then 0 else m.bind (λa, n.bind $ λb, ↑(a * b)),
  zero_mul := assume a, if_pos $ or.inl rfl,
  mul_zero := assume a, if_pos $ or.inr rfl }

lemma mul_def {a b : with_top α} :
  a * b = if a = 0 ∨ b = 0 then 0 else a.bind (λa, b.bind $ λb, ↑(a * b)) := rfl

@[simp] lemma mul_top {a : with_top α} (h : a ≠ 0) : a * ⊤ = ⊤ :=
by cases a; simp [mul_def, h]; refl

@[simp] lemma top_mul {a : with_top α} (h : a ≠ 0) : ⊤ * a = ⊤ :=
by cases a; simp [mul_def, h]; refl

@[simp] lemma top_mul_top : (⊤ * ⊤ : with_top α) = ⊤ :=
top_mul top_ne_zero

end has_mul

section mul_zero_class

variables [mul_zero_class α]

@[norm_cast] lemma coe_mul {a b : α} : (↑(a * b) : with_top α) = a * b :=
decidable.by_cases (assume : a = 0, by simp [this]) $ assume ha,
decidable.by_cases (assume : b = 0, by simp [this]) $ assume hb,
by { simp [*, mul_def], refl }

lemma mul_coe {b : α} (hb : b ≠ 0) : ∀{a : with_top α}, a * b = a.bind (λa:α, ↑(a * b))
| none     := show (if (⊤:with_top α) = 0 ∨ (b:with_top α) = 0 then 0 else ⊤ : with_top α) = ⊤,
    by simp [hb]
| (some a) := show ↑a * ↑b = ↑(a * b), from coe_mul.symm

@[simp] lemma mul_eq_top_iff {a b : with_top α} : a * b = ⊤ ↔ (a ≠ 0 ∧ b = ⊤) ∨ (a = ⊤ ∧ b ≠ 0) :=
begin
  cases a; cases b; simp only [none_eq_top, some_eq_coe],
  { simp [← coe_mul] },
  { suffices : ⊤ * (b : with_top α) = ⊤ ↔ b ≠ 0, by simpa,
    by_cases hb : b = 0; simp [hb] },
  { suffices : (a : with_top α) * ⊤ = ⊤ ↔ a ≠ 0, by simpa,
    by_cases ha : a = 0; simp [ha] },
  { simp [← coe_mul] }
end

end mul_zero_class

section no_zero_divisors

variables [mul_zero_class α] [no_zero_divisors α]

instance : no_zero_divisors (with_top α) :=
⟨λ a b, by cases a; cases b; dsimp [mul_def]; split_ifs;
  simp [*, none_eq_top, some_eq_coe, mul_eq_zero] at *⟩

end no_zero_divisors

variables [canonically_ordered_comm_semiring α]

private lemma comm (a b : with_top α) : a * b = b * a :=
begin
  by_cases ha : a = 0, { simp [ha] },
  by_cases hb : b = 0, { simp [hb] },
  simp [ha, hb, mul_def, option.bind_comm a b, mul_comm]
end

private lemma distrib' (a b c : with_top α) : (a + b) * c = a * c + b * c :=
begin
  cases c,
  { show (a + b) * ⊤ = a * ⊤ + b * ⊤,
    by_cases ha : a = 0; simp [ha] },
  { show (a + b) * c = a * c + b * c,
    by_cases hc : c = 0, { simp [hc] },
    simp [mul_coe hc], cases a; cases b,
    repeat { refl <|> exact congr_arg some (add_mul _ _ _) } }
end

private lemma assoc (a b c : with_top α) : (a * b) * c = a * (b * c) :=
begin
  cases a,
  { by_cases hb : b = 0; by_cases hc : c = 0;
      simp [*, none_eq_top] },
  cases b,
  { by_cases ha : a = 0; by_cases hc : c = 0;
      simp [*, none_eq_top, some_eq_coe] },
  cases c,
  { by_cases ha : a = 0; by_cases hb : b = 0;
      simp [*, none_eq_top, some_eq_coe] },
  simp [some_eq_coe, coe_mul.symm, mul_assoc]
end

-- `nontrivial α` is needed here as otherwise
-- we have `1 * ⊤ = ⊤` but also `= 0 * ⊤ = 0`.
private lemma one_mul' [nontrivial α] : ∀a : with_top α, 1 * a = a
| none     := show ((1:α) : with_top α) * ⊤ = ⊤, by simp [-with_top.coe_one]
| (some a) := show ((1:α) : with_top α) * a = a, by simp [coe_mul.symm, -with_top.coe_one]

instance [nontrivial α] : canonically_ordered_comm_semiring (with_top α) :=
{ one             := (1 : α),
  right_distrib   := distrib',
  left_distrib    := assume a b c, by rw [comm, distrib', comm b, comm c]; refl,
  mul_assoc       := assoc,
  mul_comm        := comm,
  one_mul         := one_mul',
  mul_one         := assume a, by rw [comm, one_mul'],
  .. with_top.add_comm_monoid, .. with_top.mul_zero_class,
  .. with_top.canonically_ordered_add_monoid,
  .. with_top.no_zero_divisors, .. with_top.nontrivial }

lemma mul_lt_top [nontrivial α] {a b : with_top α} (ha : a < ⊤) (hb : b < ⊤) : a * b < ⊤ :=
begin
  lift a to α using ne_top_of_lt ha,
  lift b to α using ne_top_of_lt hb,
  simp only [← coe_mul, coe_lt_top]
end

end with_top
