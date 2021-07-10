/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import analysis.normed_space.basic

/-!
# The integers as normed ring

This file contains basic facts about the integers as normed ring.

Recall that `∥n∥` denotes the norm of `n` as real number.
This norm is always nonnegative, so we can bundle the norm together with this fact,
to obtain a term of type `nnreal` (the nonnegative real numbers).
The resulting nonnegative real number is denoted by `∥n∥₊`.
-/

open_locale big_operators

namespace int

lemma nnnorm_coe_units (e : units ℤ) : ∥(e : ℤ)∥₊ = 1 :=
begin
  obtain (rfl|rfl) := int.units_eq_one_or e;
  simp only [units.coe_neg_one, units.coe_one, nnnorm_neg, nnnorm_one],
end

lemma norm_coe_units (e : units ℤ) : ∥(e : ℤ)∥ = 1 :=
by rw [← coe_nnnorm, int.nnnorm_coe_units, nnreal.coe_one]

@[simp] lemma nnnorm_coe_nat (n : ℕ) : ∥(n : ℤ)∥₊ = n := real.nnnorm_coe_nat _

@[simp] lemma norm_coe_nat (n : ℕ) : ∥(n : ℤ)∥ = n := real.norm_coe_nat _

@[simp] lemma to_nat_add_to_nat_neg_eq_nnnorm (n : ℤ) : ↑(n.to_nat) + ↑((-n).to_nat) = ∥n∥₊ :=
by rw [← nat.cast_add, to_nat_add_to_nat_neg_eq_nat_abs, nnreal.coe_nat_abs]

@[simp] lemma to_nat_add_to_nat_neg_eq_norm (n : ℤ) : ↑(n.to_nat) + ↑((-n).to_nat) = ∥n∥ :=
by simpa only [nnreal.coe_nat_cast, nnreal.coe_add]
  using congr_arg (coe : _ → ℝ) (to_nat_add_to_nat_neg_eq_nnnorm n)

end int
