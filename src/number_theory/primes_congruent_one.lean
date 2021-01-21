/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Riccardo Brasca
-/

import ring_theory.polynomial.cyclotomic
import topology.algebra.polynomial

/-!
# Primes congruent to one

We prove that, for any positive `k : ℕ`, there are infinitely many primes `p` such that
`p ≡ 1 [MOD k]`.
-/

namespace nat

open polynomial nat filter

/-- For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. -/
lemma exists_prime_ge_modeq_one (k n : ℕ) (hpos : 0 < k) :
  ∃ (p : ℕ), nat.prime p ∧ n ≤ p ∧ p ≡ 1 [MOD k] :=
begin
  have hli : tendsto (abs ∘ (λ (a : ℕ), abs(a : ℚ))) at_top at_top,
  { simp only [(∘), abs_cast],
    exact nat.strict_mono_cast.monotone.tendsto_at_top_at_top exists_nat_ge },
  have hcff : (int.cast_ring_hom ℚ) (cyclotomic k ℤ).leading_coeff ≠ 0,
  { simp only [cyclotomic.monic, ring_hom.eq_int_cast, monic.leading_coeff, int.cast_one, ne.def,
     not_false_iff, one_ne_zero] },
  obtain ⟨a, ha⟩ := tendsto_at_top_at_top.1 (tendsto_abv_eval₂_at_top (int.cast_ring_hom ℚ) abs
    (cyclotomic k ℤ) (degree_cyclotomic_pos k ℤ hpos) hcff hli) 2,
  let b := a * (k * n.factorial),
  have hgt : 1 < (eval ↑(a * (k * n.factorial)) (cyclotomic k ℤ)).nat_abs,
  { suffices hgtabs : 1 < abs (eval ↑b (cyclotomic k ℤ)),
    { rw [int.abs_eq_nat_abs] at hgtabs,
      exact_mod_cast hgtabs },
    suffices hgtrat : 1 < abs (eval ↑b (cyclotomic k ℚ)),
    { rw [← map_cyclotomic_int k ℚ, ← int.cast_coe_nat, ← int.coe_cast_ring_hom, eval_map,
        eval₂_hom, int.coe_cast_ring_hom] at hgtrat,
      assumption_mod_cast },
    suffices hleab : a ≤ b,
    { replace ha := lt_of_lt_of_le one_lt_two (ha b hleab),
      rwa [← eval_map, map_cyclotomic_int k ℚ, abs_cast] at ha },
    exact le_mul_of_pos_right (mul_pos hpos (factorial_pos n)) },
  let p := min_fac (eval ↑b (cyclotomic k ℤ)).nat_abs,
  letI hprime : fact p.prime := min_fac_prime (ne_of_lt hgt).symm,
  have hroot : is_root (cyclotomic k (zmod p)) (cast_ring_hom (zmod p) b),
  { rw [is_root.def, ← map_cyclotomic_int k (zmod p), eval_map, coe_cast_ring_hom,
    ← int.cast_coe_nat, ← int.coe_cast_ring_hom, eval₂_hom, int.coe_cast_ring_hom,
      zmod.int_coe_zmod_eq_zero_iff_dvd _ _],
    apply int.dvd_nat_abs.1,
    exact_mod_cast min_fac_dvd (eval ↑b (cyclotomic k ℤ)).nat_abs },
  refine exists.intro p (id ⟨hprime, ⟨_, _⟩⟩),
  { by_contra habs,
    exact ((prime.dvd_iff_not_coprime hprime).1 (dvd_factorial (min_fac_pos _) (le_of_not_ge habs)))
      (coprime.coprime_mul_left_right (coprime.coprime_mul_left_right (coprime_of_root_cyclotomic
      hpos hroot).symm)) },
  { have hdiv := order_of_dvd_of_pow_eq_one (zmod.units_pow_card_sub_one_eq_one p
      (zmod.unit_of_coprime b (coprime_of_root_cyclotomic hpos hroot))),
    rw [order_of_root_cyclotomic hpos ((prime.coprime_iff_not_dvd hprime).1
      ((coprime.coprime_mul_right_right (coprime.coprime_mul_left_right
      (coprime_of_root_cyclotomic hpos hroot).symm)))) hroot] at hdiv,
    exact ((modeq.modeq_iff_dvd' (le_of_lt (prime.one_lt hprime))).2 hdiv).symm }
end

lemma frequently_at_top_modeq_one (k : ℕ) (hpos : 0 < k) :
  ∃ᶠ p in at_top, nat.prime p ∧ p ≡ 1 [MOD k] :=
begin
  refine frequently_at_top.2 (λ n, _),
  obtain ⟨p, hp⟩ := exists_prime_ge_modeq_one k n hpos,
  exact ⟨p, ⟨hp.2.1, hp.1, hp.2.2⟩⟩
end

lemma infinite_set_of_prime_modeq_one (k : ℕ) (hpos : 0 < k) :
  set.infinite {p : ℕ | nat.prime p ∧ p ≡ 1 [MOD k]} :=
frequently_at_top_iff_infinite.1 (frequently_at_top_modeq_one k hpos)

end nat
