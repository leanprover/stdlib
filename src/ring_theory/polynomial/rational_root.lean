/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import ring_theory.polynomial.scale_roots
import ring_theory.localization

/-!
# Rational root theorem and integral root theorem

This file contains the rational root theorem and integral root theorem.
The rational root theorem for a unique factorization domain `A`
with localization `S`, states that the roots of `p : polynomial A` in `A`'s
field of fractions are of the form `x / y` with `x y : A`, `x ∣ p.coeff 0` and
`y ∣ p.leading_coeff`.
The corollary is the integral root theorem `is_integer_of_is_root_of_monic`:
if `p` is monic, its roots must be integers.
Finally, we use this to show unique factorization domains are integrally closed.

## References

 * https://en.wikipedia.org/wiki/Rational_root_theorem
-/

section scale_roots

variables {A K R S : Type*} [integral_domain A] [field K] [comm_ring R] [comm_ring S]
variables {M : submonoid A} [algebra A S] [is_localization M S] [algebra A K] [is_fraction_ring A K]

open finsupp is_fraction_ring is_localization polynomial

lemma scale_roots_aeval_eq_zero_of_aeval_mk'_eq_zero {p : polynomial A} {r : A} {s : M}
  (hr : aeval (mk' S r s) p = 0) :
  aeval (algebra_map A S r) (scale_roots p s) = 0 :=
begin
  convert scale_roots_eval₂_eq_zero (algebra_map A S) hr,
  rw [aeval_def, mk'_spec' _ r s]
end

lemma num_is_root_scale_roots_of_aeval_eq_zero
  [unique_factorization_monoid A] {p : polynomial A} {x : K} (hr : aeval x p = 0) :
  is_root (scale_roots p (denom A x)) (num A x) :=
begin
  apply is_root_of_eval₂_map_eq_zero (is_fraction_ring.injective A K),
  refine scale_roots_aeval_eq_zero_of_aeval_mk'_eq_zero _,
  rw mk'_num_denom,
  exact hr
end

end scale_roots

section rational_root_theorem

variables {A K : Type*} [integral_domain A] [unique_factorization_monoid A] [field K]
variables [algebra A K] [is_fraction_ring A K]

open is_fraction_ring is_localization polynomial unique_factorization_monoid

/-- Rational root theorem part 1:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the numerator of `r` divides the constant coefficient -/
theorem num_dvd_of_is_root {p : polynomial A} {r : K} (hr : aeval r p = 0) :
  num A r ∣ p.coeff 0 :=
begin
  suffices : num A r ∣ (scale_roots p (denom A r)).coeff 0,
  { simp only [coeff_scale_roots, nat.sub_zero] at this,
    haveI := classical.prop_decidable,
    by_cases hr : num A r = 0,
    { obtain ⟨u, hu⟩ := (is_unit_denom_of_num_eq_zero hr).pow p.nat_degree,
      rw ←hu at this,
      exact units.dvd_mul_right.mp this },
    { refine dvd_of_dvd_mul_left_of_no_prime_factors hr _ this,
      intros q dvd_num dvd_denom_pow hq,
      apply hq.not_unit,
      exact num_denom_reduced A r dvd_num (hq.dvd_of_dvd_pow dvd_denom_pow) } },
  convert dvd_term_of_is_root_of_dvd_terms 0 (num_is_root_scale_roots_of_aeval_eq_zero hr) _,
  { rw [pow_zero, mul_one] },
  intros j hj,
  apply dvd_mul_of_dvd_right,
  convert pow_dvd_pow (num A r) (nat.succ_le_of_lt (bot_lt_iff_ne_bot.mpr hj)),
  exact (pow_one _).symm
end

/-- Rational root theorem part 2:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the denominator of `r` divides the leading coefficient -/
theorem denom_dvd_of_is_root {p : polynomial A} {r : K} (hr : aeval r p = 0) :
  (denom A r : A) ∣ p.leading_coeff :=
begin
  suffices : (denom A r : A) ∣ p.leading_coeff * num A r ^ p.nat_degree,
  { refine dvd_of_dvd_mul_left_of_no_prime_factors
      (mem_non_zero_divisors_iff_ne_zero.mp (denom A r).2) _ this,
    intros q dvd_denom dvd_num_pow hq,
    apply hq.not_unit,
    exact num_denom_reduced A r (hq.dvd_of_dvd_pow dvd_num_pow) dvd_denom },
  rw ←coeff_scale_roots_nat_degree,
  apply dvd_term_of_is_root_of_dvd_terms _ (num_is_root_scale_roots_of_aeval_eq_zero hr),
  intros j hj,
  by_cases h : j < p.nat_degree,
  { rw coeff_scale_roots,
    refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_right _ _) _,
    convert pow_dvd_pow _ (nat.succ_le_iff.mpr (nat.lt_sub_left_of_add_lt _)),
    { exact (pow_one _).symm },
    simpa using h },
  rw [←nat_degree_scale_roots p (denom A r)] at *,
  rw [coeff_eq_zero_of_nat_degree_lt (lt_of_le_of_ne (le_of_not_gt h) hj.symm), zero_mul],
  exact dvd_zero _
end

/-- Integral root theorem:
if `r : f.codomain` is a root of a monic polynomial over the ufd `A`,
then `r` is an integer -/
theorem is_integer_of_is_root_of_monic {p : polynomial A} (hp : monic p) {r : K}
  (hr : aeval r p = 0) : is_integer A r :=
is_integer_of_is_unit_denom (is_unit_of_dvd_one _ (hp ▸ denom_dvd_of_is_root hr))

namespace unique_factorization_monoid

lemma integer_of_integral {x : K} :
  is_integral A x → is_integer A x :=
λ ⟨p, hp, hx⟩, is_integer_of_is_root_of_monic hp hx

lemma integrally_closed : integral_closure A K = ⊥ :=
eq_bot_iff.mpr (λ x hx, algebra.mem_bot.mpr (integer_of_integral hx))

end unique_factorization_monoid

end rational_root_theorem
