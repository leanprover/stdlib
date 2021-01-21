/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.char_zero

/-!
# Injectivity of `int.cast` into characteristic zero rings.

-/

variables {α : Type*}

open nat

namespace int

@[simp]
theorem cast_eq_zero [add_group α] [has_one α] [char_zero α] {n : ℤ} : (n : α) = 0 ↔ n = 0 :=
⟨λ h, begin cases n,
  { exact congr_arg coe (nat.cast_eq_zero.1 h) },
  { rw [cast_neg_succ_of_nat, neg_eq_zero, ← cast_succ, nat.cast_eq_zero] at h,
    contradiction }
end, λ h, by rw [h, cast_zero]⟩

@[simp, norm_cast] theorem cast_inj [add_group α] [has_one α] [char_zero α] {m n : ℤ} :
  (m : α) = n ↔ m = n :=
by rw [← sub_eq_zero, ← cast_sub, cast_eq_zero, sub_eq_zero]

theorem cast_injective [add_group α] [has_one α] [char_zero α] : function.injective (coe : ℤ → α)
| m n := cast_inj.1

theorem cast_ne_zero [add_group α] [has_one α] [char_zero α] {n : ℤ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
not_congr cast_eq_zero

end int
