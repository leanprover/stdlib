/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes

# Sums of two squares

Proof of Fermat's theorem on the sum of two squares. Every prime congruent to 1 mod 4 is the sum
of two squares
-/

import data.zsqrtd.gaussian_int

open gaussian_int principal_ideal_domain

namespace nat
namespace prime

lemma sum_two_squares {p : ℕ} (hp : p.prime) (hp1 : p % 4 = 1) :
  ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
sum_two_squares_of_nat_prime_of_not_irreducible hp
  (by rw [irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime hp, hp1]; norm_num)

end prime
end nat
