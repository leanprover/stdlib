/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/

import algebra.ordered_ring

/-
Results copied from the core library to mathlib by Johan Commelin
-/

namespace nat

instance : zero_ne_one_class ℕ :=
{ zero := 0, one := 1, zero_ne_one := nat.zero_ne_one }

instance : comm_semiring nat :=
{ add            := nat.add,
  add_assoc      := nat.add_assoc,
  zero           := nat.zero,
  zero_add       := nat.zero_add,
  add_comm       := nat.add_comm,
  mul            := nat.mul,
  mul_assoc      := nat.mul_assoc,
  one            := nat.succ nat.zero,
  one_mul        := nat.one_mul,
  mul_one        := nat.mul_one,
  left_distrib   := nat.left_distrib,
  right_distrib  := nat.right_distrib,
  zero_mul       := nat.zero_mul,
  mul_zero       := nat.mul_zero,
  mul_comm       := nat.mul_comm }

instance : decidable_linear_ordered_semiring nat :=
{ add_left_cancel            := @nat.add_left_cancel,
  add_right_cancel           := @nat.add_right_cancel,
  lt                         := nat.lt,
  add_le_add_left            := @nat.add_le_add_left,
  le_of_add_le_add_left      := @nat.le_of_add_le_add_left,
  zero_lt_one                := zero_lt_succ 0,
  mul_lt_mul_of_pos_left     := @nat.mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right    := @nat.mul_lt_mul_of_pos_right,
  decidable_eq               := nat.decidable_eq,
  ..nat.comm_semiring, ..nat.decidable_linear_order }

-- all the fields are already included in the decidable_linear_ordered_semiring instance
instance : decidable_linear_ordered_cancel_add_comm_monoid ℕ :=
{ add_left_cancel := @nat.add_left_cancel,
  ..nat.decidable_linear_ordered_semiring }

/- Extra instances to short-circuit type class resolution -/
instance : add_comm_monoid nat    := by apply_instance
instance : add_monoid nat         := by apply_instance
instance : monoid nat             := by apply_instance
instance : comm_monoid nat        := by apply_instance
instance : comm_semigroup nat     := by apply_instance
instance : semigroup nat          := by apply_instance
instance : add_comm_semigroup nat := by apply_instance
instance : add_semigroup nat      := by apply_instance
instance : distrib nat            := by apply_instance
instance : semiring nat           := by apply_instance
instance : ordered_semiring nat   := by apply_instance

theorem mul_self_le_mul_self {n m : ℕ} (h : n ≤ m) : n * n ≤ m * m :=
mul_le_mul h h (zero_le _) (zero_le _)

theorem mul_self_lt_mul_self : Π {n m : ℕ}, n < m → n * n < m * m
| 0        m h := mul_pos h h
| (succ n) m h := mul_lt_mul h (le_of_lt h) (succ_pos _) (zero_le _)

theorem mul_self_le_mul_self_iff {n m : ℕ} : n ≤ m ↔ n * n ≤ m * m :=
⟨mul_self_le_mul_self, λh, decidable.by_contradiction $
  λhn, not_lt_of_ge h $ mul_self_lt_mul_self $ lt_of_not_ge hn⟩

theorem mul_self_lt_mul_self_iff {n m : ℕ} : n < m ↔ n * n < m * m :=
iff.trans (lt_iff_not_ge _ _) $ iff.trans (not_iff_not_of_iff mul_self_le_mul_self_iff) $
  iff.symm (lt_iff_not_ge _ _)

theorem le_mul_self : Π (n : ℕ), n ≤ n * n
| 0     := le_refl _
| (n+1) := let t := mul_le_mul_left (n+1) (succ_pos n) in by simp at t; exact t

theorem eq_of_mul_eq_mul_right {n m k : ℕ} (Hm : m > 0) (H : n * m = k * m) : n = k :=
by rw [mul_comm n m, mul_comm k m] at H; exact eq_of_mul_eq_mul_left Hm H

theorem one_add (n : ℕ) : 1 + n = succ n := by simp [add_comm]

end nat
