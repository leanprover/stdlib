/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import ring_theory.ideal.operations
import data.polynomial.ring_division
import ring_theory.prime
/-!
# Eisenstein's criterion

A proof of a slight generalisation of Eisenstein's criterion for the irreducibility of
a polynomial over an integral domain.
-/

open polynomial ideal.quotient
variables {R : Type*} [integral_domain R]

namespace polynomial
namespace eisenstein_criterion_aux
/- Section for auxiliary lemmas used in the proof of `irreducible_of_eisenstein_criterion`-/

lemma map_eq_C_mul_X_pow_of_forall_coeff_mem {f : polynomial R} {P : ideal R}
  (hfP : ∀ (n : ℕ), ↑n < f.degree → f.coeff n ∈ P) (hf0 : f ≠ 0) :
  map (mk P) f = C ((mk P) f.leading_coeff) * X ^ f.nat_degree :=
polynomial.ext (λ n, begin
  rcases lt_trichotomy ↑n (degree f) with h | h | h,
  { erw [coeff_map, eq_zero_iff_mem.2 (hfP n h), coeff_C_mul, coeff_X_pow, if_neg, mul_zero],
    rintro rfl, exact not_lt_of_ge degree_le_nat_degree h },
  { have : nat_degree f = n, from nat_degree_eq_of_degree_eq_some h.symm,
    rw [coeff_C_mul, coeff_X_pow, if_pos this.symm, mul_one, leading_coeff, this, coeff_map] },
  { rw [coeff_eq_zero_of_degree_lt, coeff_eq_zero_of_degree_lt],
    { refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) _,
      rwa ← degree_eq_nat_degree hf0 },
    { exact lt_of_le_of_lt (degree_map_le _) h } }
end)

lemma le_nat_degree_of_map_eq_mul_X_pow {n : ℕ}
  {P : ideal R} (hP : P.is_prime) {q : polynomial R} {c : polynomial P.quotient}
  (hq : map (mk P) q = c * X ^ n) (hc0 : c.degree = 0) : n ≤ q.nat_degree :=
with_bot.coe_le_coe.1
  (calc ↑n = degree (q.map (mk P)) :
      by rw [hq, degree_mul, hc0, zero_add, degree_pow, degree_X, nsmul_one, nat.cast_with_bot]
      ... ≤ degree q : degree_map_le _
      ... ≤ nat_degree q : degree_le_nat_degree)

lemma eval_zero_mem_ideal_of_eq_mul_X_pow {n : ℕ} {P : ideal R}
  {q : polynomial R} {c : polynomial P.quotient}
  (hq : map (mk P) q = c * X ^ n) (hn0 : 0 < n) : eval 0 q ∈ P :=
by rw [← coeff_zero_eq_eval_zero, ← eq_zero_iff_mem, ← coeff_map,
    coeff_zero_eq_eval_zero, hq, eval_mul, eval_pow, eval_X, zero_pow hn0, mul_zero]

lemma is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit {p q : polynomial R}
  (hu : ∀ (x : R), C x ∣ p * q → is_unit x) (hpm : p.nat_degree = 0) :
  is_unit p :=
begin
  rw [eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpm), is_unit_C],
  refine hu _ _,
  rw [← eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpm)],
  exact dvd_mul_right _ _
end

end eisenstein_criterion_aux

open eisenstein_criterion_aux

/-- If `f` is a non constant polynomial with coefficients in `R`, and `P` is a prime ideal in `R`,
then if every coefficient in `R` except the leading coefficient is in `P`, and
the trailing coefficient is not in `P^2` and no non units in `R` divide `f`, then `f` is
irreducible. -/
theorem irreducible_of_eisenstein_criterion {f : polynomial R} {P : ideal R} (hP : P.is_prime)
  (hfl : f.leading_coeff ∉ P)
  (hfP : ∀ n : ℕ, ↑n < degree f → f.coeff n ∈ P)
  (hfd0 : 0 < degree f) (h0 : f.coeff 0 ∉ P^2)
  (hu : ∀ x : R, C x ∣ f → is_unit x) : irreducible f :=
have hf0 : f ≠ 0, from λ _, by simp only [*, not_true, submodule.zero_mem, coeff_zero] at *,
have hf : f.map (mk P) = C (mk P (leading_coeff f)) * X ^ nat_degree f,
  from map_eq_C_mul_X_pow_of_forall_coeff_mem hfP hf0,
have hfd0 : 0 < f.nat_degree, from with_bot.coe_lt_coe.1
  (lt_of_lt_of_le hfd0 degree_le_nat_degree),
⟨mt degree_eq_zero_of_is_unit (λ h, by simp only [*, lt_irrefl] at *),
begin
  rintros p q rfl,
  rw [map_mul] at hf,
  rcases mul_eq_mul_prime_pow (show prime (X : polynomial (ideal.quotient P)),
    from prime_of_degree_eq_one_of_monic degree_X monic_X) hf with
      ⟨m, n, b, c, hmnd, hbc, hp, hq⟩,
  have hmn : 0 < m → 0 < n → false,
  { assume hm0 hn0,
    refine h0 _,
    rw [coeff_zero_eq_eval_zero, eval_mul, pow_two],
    exact ideal.mul_mem_mul
      (eval_zero_mem_ideal_of_eq_mul_X_pow hp hm0)
      (eval_zero_mem_ideal_of_eq_mul_X_pow hq hn0) },
  have hpql0 : (mk P) (p * q).leading_coeff ≠ 0,
  { rwa [ne.def, eq_zero_iff_mem] },
  have hp0 : p ≠ 0, from λ h, by simp only [*, zero_mul, eq_self_iff_true, not_true, ne.def] at *,
  have hq0 : q ≠ 0, from λ h, by simp only [*, eq_self_iff_true, not_true, ne.def, mul_zero] at *,
  have hbc0 : degree b = 0 ∧ degree c = 0,
  { apply_fun degree at hbc,
    rwa [degree_C hpql0, degree_mul, eq_comm, nat.with_bot.add_eq_zero_iff] at hbc },
  have hmp : m ≤ nat_degree p,
    from le_nat_degree_of_map_eq_mul_X_pow hP hp hbc0.1,
  have hnq : n ≤ nat_degree q,
    from le_nat_degree_of_map_eq_mul_X_pow hP hq hbc0.2,
  have hpmqn : p.nat_degree = m ∧ q.nat_degree = n,
  { rw [nat_degree_mul hp0 hq0] at hmnd,
    clear_except hmnd hmp hnq,
    omega },
  obtain rfl | rfl : m = 0 ∨ n = 0,
  { rwa [pos_iff_ne_zero, pos_iff_ne_zero, imp_false, not_not,
      ← or_iff_not_imp_left] at hmn },
  { exact or.inl (is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit hu hpmqn.1) },
  { exact or.inr (is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit
      (by simpa only [mul_comm] using hu) hpmqn.2) }
end⟩

end polynomial
