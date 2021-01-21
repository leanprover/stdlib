/-
Copyright (c) 2020 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Bryan Gin-ge Chen
-/
import data.nat.prime
/-!
# Lemmas about nat.prime using `int`s
-/

open nat

namespace int

lemma not_prime_of_int_mul {a b : ℤ} {c : ℕ}
  (ha : 1 < a.nat_abs) (hb : 1 < b.nat_abs) (hc : a*b = (c : ℤ)) : ¬ prime c :=
not_prime_mul' (nat_abs_mul_nat_abs_eq hc) ha hb

end int
