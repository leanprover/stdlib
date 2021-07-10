/-
Copyright (c) 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Yury Kudryashov
-/
import data.real.basic

/-!
# Sum of the Reciprocals of the Triangular Numbers

This file proves Theorem 42 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

We interpret “triangular numbers” as naturals of the form $\frac{k(k+1)}{2}$ for natural `k`.
We prove that the sum of the first `n` triangular numbers is equal to $2 - \frac2n$.

## Tags

discrete_sum
-/

open_locale big_operators
open finset

/-- **Sum of the Reciprocals of the Triangular Numbers** -/
lemma inverse_triangle_sum :
  ∀ n, ∑ k in range n, (2 : ℚ) / (k * (k + 1)) = if n = 0 then 0 else 2 - (2 : ℚ) / n :=
begin
  refine sum_range_induction _ _ (if_pos rfl) _,
  rintro (_|n), { rw [if_neg, if_pos]; norm_num },
  simp_rw [if_neg (nat.succ_ne_zero _), nat.succ_eq_add_one],
  have A : (n + 1 + 1 : ℚ) ≠ 0, by { norm_cast, norm_num },
  push_cast,
  field_simp [nat.cast_add_one_ne_zero],
  ring
end
