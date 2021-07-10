/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.fintype.card_embedding

/-!
# Birthday Problem

This file proves Theorem 93 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

As opposed to the standard probabilistic statement, we instead state the birthday problem
in terms of injective functions. The general result about `fintype.card (α ↪ β)` which this proof
uses is `fintype.card_embedding_eq`.
-/

local notation `‖` x `‖` := fintype.card x

/-- **Birthday Problem** -/
theorem birthday :
  2 * ‖fin 23 ↪ fin 365‖ < ‖fin 23 → fin 365‖ ∧ 2 * ‖fin 22 ↪ fin 365‖ > ‖fin 22 → fin 365‖ :=
begin
  simp only [nat.desc_factorial, fintype.card_fin, fintype.card_embedding_eq, fintype.card_fun],
  norm_num
end
