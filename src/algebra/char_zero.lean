/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Natural homomorphism from the natural numbers into a monoid with one.
-/
import data.fintype.basic

/-- Typeclass for monoids with characteristic zero.
  (This is usually stated on fields but it makes sense for any additive monoid with 1.) -/
class char_zero (R : Type*) [add_monoid R] [has_one R] : Prop :=
(cast_injective : function.injective (coe : ℕ → R))

theorem char_zero_of_inj_zero {R : Type*} [add_left_cancel_monoid R] [has_one R]
  (H : ∀ n:ℕ, (n:R) = 0 → n = 0) : char_zero R :=
⟨λ m n, begin
   assume h,
   wlog hle : m ≤ n,
   rcases nat.le.dest hle with ⟨k, rfl⟩,
   rw [nat.cast_add, eq_comm, add_eq_left_iff] at h,
   rw [H k h, add_zero]
 end⟩

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_semiring.to_char_zero {R : Type*}
  [linear_ordered_semiring R] : char_zero R :=
⟨nat.strict_mono_cast.injective⟩

namespace nat
variables {R : Type*} [add_monoid R] [has_one R] [char_zero R]

theorem cast_injective : function.injective (coe : ℕ → R) :=
char_zero.cast_injective

@[simp, norm_cast] theorem cast_inj {m n : ℕ} : (m : R) = n ↔ m = n :=
cast_injective.eq_iff

@[simp, norm_cast] theorem cast_eq_zero {n : ℕ} : (n : R) = 0 ↔ n = 0 :=
by rw [← cast_zero, cast_inj]

@[norm_cast] theorem cast_ne_zero {n : ℕ} : (n : R) ≠ 0 ↔ n ≠ 0 :=
not_congr cast_eq_zero

lemma cast_add_one_ne_zero (n : ℕ) : (n + 1 : R) ≠ 0 :=
by exact_mod_cast n.succ_ne_zero

@[simp, norm_cast]
theorem cast_dvd_char_zero {k : Type*} [field k] [char_zero k] {m n : ℕ}
  (n_dvd : n ∣ m) : ((m / n : ℕ) : k) = m / n :=
begin
  by_cases hn : n = 0,
  { subst hn,
    simp },
  { exact cast_dvd n_dvd (cast_ne_zero.mpr hn), },
end

end nat

section

variables (M : Type*) [add_monoid M] [has_one M] [char_zero M]

@[priority 100] -- see Note [lower instance priority]
instance char_zero.infinite : infinite M :=
infinite.of_injective coe nat.cast_injective

variable {M}

@[field_simps] lemma two_ne_zero' : (2:M) ≠ 0 :=
have ((2:ℕ):M) ≠ 0, from nat.cast_ne_zero.2 dec_trivial,
by rwa [nat.cast_two] at this

end

section
variables {R : Type*} [semiring R] [no_zero_divisors R] [char_zero R]

lemma add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0 :=
by simp only [(two_mul a).symm, mul_eq_zero, two_ne_zero', false_or]

lemma bit0_eq_zero {a : R} : bit0 a = 0 ↔ a = 0 := add_self_eq_zero
end

section
variables {R : Type*} [division_ring R] [char_zero R]

@[simp] lemma half_add_self (a : R) : (a + a) / 2 = a :=
by rw [← mul_two, mul_div_cancel a two_ne_zero']

@[simp] lemma add_halves' (a : R) : a / 2 + a / 2 = a :=
by rw [← add_div, half_add_self]

lemma sub_half (a : R) : a - a / 2 = a / 2 :=
by rw [sub_eq_iff_eq_add, add_halves']

lemma half_sub (a : R) : a / 2 - a = - (a / 2) :=
by rw [← neg_sub, sub_half]

end

namespace with_top

instance {R : Type*} [add_monoid R] [has_one R] [char_zero R] : char_zero (with_top R) :=
{ cast_injective := λ m n h, by rwa [← coe_nat, ← coe_nat n, coe_eq_coe, nat.cast_inj] at h }

end with_top
