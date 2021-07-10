/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

/-!
# More `char` instances

This file provides a `linear_order` instance on `char`. `char` is the type of Unicode scalar values.
-/

instance : linear_order char :=
{ le_refl := λ a, @le_refl ℕ _ _,
  le_trans := λ a b c, @le_trans ℕ _ _ _ _,
  le_antisymm := λ a b h₁ h₂,
    char.eq_of_veq $ le_antisymm h₁ h₂,
  le_total := λ a b, @le_total ℕ _ _ _,
  lt_iff_le_not_le := λ a b, @lt_iff_le_not_le ℕ _ _ _,
  decidable_le := char.decidable_le,
  decidable_eq := char.decidable_eq,
  decidable_lt := char.decidable_lt,
  ..char.has_le, ..char.has_lt }

lemma char.of_nat_to_nat {c : char} (h : is_valid_char c.to_nat) :
  char.of_nat c.to_nat = c :=
begin
  rw [char.of_nat, dif_pos h],
  cases c,
  simp [char.to_nat]
end
