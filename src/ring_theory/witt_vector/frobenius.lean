/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.nat.multiplicity
import ring_theory.witt_vector.is_poly


/-!
## The Frobenius operator

If `R` has characteristic `p`, then there is a ring endomorphism `frobenius R p`
that raises `r : R` to the power `p`.
By applying `witt_vector.map` to `frobenius R p`, we obtain a ring endomorphism `𝕎 R →+* 𝕎 R`.
It turns out that this endomorphism can be described by polynomials over `ℤ`
that do not depend on `R` or the fact that it has characteristic `p`.
In this way, we obtain a Frobenius endomorphism `witt_vector.frobenius_fun : 𝕎 R → 𝕎 R`
for every commutative ring `R`.

Unfortunately, the aforementioned polynomials can not be obtained using the machinery
of `witt_structure_int` that was developed in `structure_polynomial.lean`.
We therefore have to define the polynomials by hand, and check that they have the required property.

In case `R` has characteristic `p`, we show in `frobenius_fun_eq_map_frobenius`
that `witt_vector.frobenius_fun` is equal to `witt_vector.map (frobenius R p)`.

### Main definitions and results

* `frobenius_poly`: the polynomials that describe the coefficients of `frobenius_fun`;
* `frobenius_fun`: the Frobenius endomorphism on Witt vectors;
* `frobenius_fun_is_poly`: the tautological assertion that Frobenius is a polynomial function;
* `frobenius_fun_eq_map_frobenius`: the fact that in characteristic `p`, Frobenius is equal to
  `witt_vector.map (frobenius R p)`.

TODO: Show that `witt_vector.frobenius_fun` is a ring homomorphism,
and bundle it into `witt_vector.frobenius`.

-/

namespace witt_vector

variables {p : ℕ} {R S : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]
local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector

noncomputable theory
open mv_polynomial finset
open_locale big_operators

variables (p)
include hp

/-- The rational polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`.
These polynomials actually have integral coefficients,
see `frobenius_poly` and `map_frobenius_poly`. -/
def frobenius_poly_rat (n : ℕ) : mv_polynomial ℕ ℚ :=
bind₁ (witt_polynomial p ℚ ∘ λ n, n + 1) (X_in_terms_of_W p ℚ n)

lemma bind₁_frobenius_poly_rat_witt_polynomial (n : ℕ) :
  bind₁ (frobenius_poly_rat p) (witt_polynomial p ℚ n) = (witt_polynomial p ℚ (n+1)) :=
begin
  delta frobenius_poly_rat,
  rw [← bind₁_bind₁, bind₁_X_in_terms_of_W_witt_polynomial, bind₁_X_right],
end

/-- An auxilliary definition, to avoid an excessive amount of finiteness proofs
for `multiplicity p n`. -/
private def pnat_multiplicity (n : ℕ+) : ℕ :=
(multiplicity p n).get $ multiplicity.finite_nat_iff.mpr $ ⟨ne_of_gt hp.one_lt, n.2⟩

local notation `v` := pnat_multiplicity

/-- An auxilliary polynomial over the integers, that satisfies
`(frobenius_poly_aux p n - X n ^ p) / p = frobenius_poly p n`.
This makes it easy to show that `frobenius_poly p n` is congruent to `X n ^ p`
modulo `p`. -/
noncomputable def frobenius_poly_aux : ℕ → mv_polynomial ℕ ℤ
| n := X (n + 1) - ∑ i : fin n, have _ := i.is_lt,
  ∑ j in range (p ^ (n - i)),
    (X i ^ p) ^ (p ^ (n - i) - (j + 1)) *
      (frobenius_poly_aux i) ^ (j + 1) *
      C ↑((p ^ (n - i)).choose (j + 1) / (p ^ (n - i - v p ⟨j + 1, nat.succ_pos j⟩)) *
      ↑p ^ (j - v p ⟨j + 1, nat.succ_pos j⟩) : ℕ)

lemma frobenius_poly_aux_eq (n : ℕ) :
  frobenius_poly_aux p n =
  X (n + 1) - ∑ i in range n, ∑ j in range (p ^ (n - i)),
    (X i ^ p) ^ (p ^ (n - i) - (j + 1)) *
    (frobenius_poly_aux p i) ^ (j + 1) *
    C ↑((p ^ (n - i)).choose (j + 1) / (p ^ (n - i - v p ⟨j + 1, nat.succ_pos j⟩)) *
      ↑p ^ (j - v p ⟨j + 1, nat.succ_pos j⟩) : ℕ) :=
by { rw [frobenius_poly_aux, ← fin.sum_univ_eq_sum_range] }

/-- The polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`. -/
def frobenius_poly (n : ℕ) : mv_polynomial ℕ ℤ :=
X n ^ p + C ↑p * (frobenius_poly_aux p n)

/-
Our next goal is to prove
```
lemma map_frobenius_poly (n : ℕ) :
  mv_polynomial.map (int.cast_ring_hom ℚ) (frobenius_poly p n) = frobenius_poly_rat p n
```
This lemma has a rather long proof, but it mostly boils down to applying induction,
and then using the following two key facts at the right point.
-/

/-- A key divisibility fact for the proof of `witt_vector.map_frobenius_poly`. -/
lemma map_frobenius_poly.key₁ (n j : ℕ) (hj : j < p ^ (n)) :
  p ^ (n - v p ⟨j + 1, j.succ_pos⟩) ∣ (p ^ n).choose (j + 1) :=
begin
  apply multiplicity.pow_dvd_of_le_multiplicity,
  have aux : (multiplicity p ((p ^ n).choose (j + 1))).dom,
  { rw [← multiplicity.finite_iff_dom, multiplicity.finite_nat_iff],
    exact ⟨hp.ne_one, nat.choose_pos hj⟩, },
  rw [← enat.coe_get aux, enat.coe_le_coe, nat.sub_le_left_iff_le_add,
      ← enat.coe_le_coe, enat.coe_add, pnat_multiplicity, enat.coe_get, enat.coe_get, add_comm],
  exact (nat.prime.multiplicity_choose_prime_pow hp hj j.succ_pos).ge,
end

/-- A key numerical identity needed for the proof of `witt_vector.map_frobenius_poly`. -/
lemma map_frobenius_poly.key₂ {n i j : ℕ} (hi : i < n) (hj : j < p ^ (n - i)) :
  j - (v p ⟨j + 1, j.succ_pos⟩) + n =
    i + j + (n - i - v p ⟨j + 1, j.succ_pos⟩) :=
begin
  generalize h : (v p ⟨j + 1, j.succ_pos⟩) = m,
  suffices : m ≤ n - i ∧ m ≤ j,
  { cases this, unfreezingI { clear_dependent p }, omega },
  split,
  { rw [← h, ← enat.coe_le_coe, pnat_multiplicity, enat.coe_get,
        ← (nat.prime.multiplicity_choose_prime_pow hp hj j.succ_pos)],
    apply le_add_left, refl },
  { obtain ⟨c, hc⟩ : p ^ m ∣ j + 1,
    { rw [← h], exact multiplicity.pow_multiplicity_dvd _, },
    obtain ⟨c, rfl⟩ : ∃ k : ℕ, c = k + 1,
    { apply nat.exists_eq_succ_of_ne_zero, rintro rfl, simpa only using hc },
    rw [mul_add, mul_one] at hc,
    apply nat.le_of_lt_succ,
    calc m < p ^ m : nat.lt_pow_self hp.one_lt m
       ... ≤ j + 1 : by { rw ← nat.sub_eq_of_eq_add hc, apply nat.sub_le } }
end

lemma map_frobenius_poly (n : ℕ) :
  mv_polynomial.map (int.cast_ring_hom ℚ) (frobenius_poly p n) = frobenius_poly_rat p n :=
begin
  rw [frobenius_poly, ring_hom.map_add, ring_hom.map_mul, ring_hom.map_pow, map_C, map_X,
      ring_hom.eq_int_cast, int.cast_coe_nat, frobenius_poly_rat],
  apply nat.strong_induction_on n, clear n,
  intros n IH,
  rw [X_in_terms_of_W_eq],
  simp only [alg_hom.map_sum, alg_hom.map_sub, alg_hom.map_mul, alg_hom.map_pow, bind₁_C_right],
  have h1 : (↑p ^ n) * (⅟ (↑p : ℚ) ^ n) = 1 := by rw [←mul_pow, mul_inv_of_self, one_pow],
  rw [bind₁_X_right, function.comp_app, witt_polynomial_eq_sum_C_mul_X_pow, sum_range_succ,
      sum_range_succ, nat.sub_self, nat.add_sub_cancel_left, pow_zero, pow_one, pow_one, sub_mul,
      add_mul, add_mul, mul_assoc, mul_assoc, mul_comm _ (C (⅟ ↑p ^ n)), mul_comm _ (C (⅟ ↑p ^ n)),
      ←mul_assoc, ←mul_assoc, ←C_mul, ←C_mul, pow_succ, mul_assoc ↑p (↑p ^ n) (⅟ ↑p ^ n), h1,
      mul_one, C_1, one_mul, ←add_assoc, add_comm _ (X n ^ p), add_assoc, ←add_sub, add_right_inj],
  rw [frobenius_poly_aux_eq, ring_hom.map_sub, map_X, mul_sub, ←add_sub, sub_eq_add_neg,
      add_right_inj, neg_eq_iff_neg_eq, neg_sub],
  simp only [ring_hom.map_sum, mul_sum, sum_mul, ←sum_sub_distrib],
  apply sum_congr rfl,
  intros i hi,
  rw mem_range at hi,
  rw [← IH i hi],
  clear IH,
  rw [add_comm (X i ^ p), add_pow, sum_range_succ', pow_zero, nat.sub_zero, nat.choose_zero_right,
      one_mul, nat.cast_one, mul_one, mul_add, add_mul, nat.succ_sub (le_of_lt hi),
      nat.succ_eq_add_one (n - i), pow_succ, pow_mul, add_sub_cancel, mul_sum, sum_mul],
  apply sum_congr rfl,
  intros j hj,
  rw mem_range at hj,
  rw [ring_hom.map_mul, ring_hom.map_mul, ring_hom.map_pow, ring_hom.map_pow, ring_hom.map_pow,
      ring_hom.map_pow, ring_hom.map_pow, map_C, map_X, mul_pow],
  rw [mul_comm (C ↑p ^ i), mul_comm _ ((X i ^ p) ^ _), mul_comm (C ↑p ^ (j + 1)), mul_comm (C ↑p)],
  simp only [mul_assoc],
  apply congr_arg,
  apply congr_arg,
  rw [←C_eq_coe_nat],
  simp only [←ring_hom.map_pow, ←C_mul],
  rw C_inj,
  simp only [inv_of_eq_inv, ring_hom.eq_int_cast, inv_pow', int.cast_coe_nat, nat.cast_mul],
  rw [rat.coe_nat_div _ _ (map_frobenius_poly.key₁ p (n - i) j hj)],
  simp only [nat.cast_pow, pow_add, pow_one],
  suffices : ((p ^ (n - i)).choose (j + 1) * p ^ (j - v p ⟨j + 1, j.succ_pos⟩) * p * p ^ n : ℚ) =
    p ^ j * p * ((p ^ (n - i)).choose (j + 1) * p ^ i) * p ^ (n - i - v p ⟨j + 1, j.succ_pos⟩),
  { have aux : ∀ k : ℕ, (p ^ k : ℚ) ≠ 0,
    { intro, apply pow_ne_zero, exact_mod_cast hp.ne_zero },
    simpa [aux, -one_div] with field_simps using this.symm },
  rw [mul_comm _ (p : ℚ), mul_assoc, mul_assoc, ← pow_add, map_frobenius_poly.key₂ p hi hj],
  ring_exp
end

lemma frobenius_poly_zmod (n : ℕ) :
  mv_polynomial.map (int.cast_ring_hom (zmod p)) (frobenius_poly p n) = X n ^ p :=
begin
  rw [frobenius_poly, ring_hom.map_add, ring_hom.map_pow, ring_hom.map_mul, map_X, map_C],
  simp only [int.cast_coe_nat, add_zero, ring_hom.eq_int_cast, zmod.cast_self, zero_mul, C_0],
end

@[simp]
lemma bind₁_frobenius_poly_witt_polynomial (n : ℕ) :
  bind₁ (frobenius_poly p) (witt_polynomial p ℤ n) = (witt_polynomial p ℤ (n+1)) :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [map_bind₁, map_frobenius_poly, bind₁_frobenius_poly_rat_witt_polynomial,
    map_witt_polynomial],
end


variables {p}

/-- `frobenius_fun` is the function underlying the ring endomorphism
`frobenius : 𝕎 R →+* frobenius 𝕎 R`. -/
def frobenius_fun (x : 𝕎 R) : 𝕎 R :=
mk p $ λ n, mv_polynomial.aeval x.coeff (frobenius_poly p n)

lemma coeff_frobenius_fun (x : 𝕎 R) (n : ℕ) :
  coeff (frobenius_fun x) n = mv_polynomial.aeval x.coeff (frobenius_poly p n) :=
by rw [frobenius_fun, coeff_mk]

variables (p)

/-- `frobenius_fun` is tautologically a polynomial function.

See also `frobenius_is_poly`. -/
@[is_poly] lemma frobenius_fun_is_poly : is_poly p (λ R _Rcr, @frobenius_fun p R _ _Rcr) :=
⟨frobenius_poly p, by { introsI, funext n, apply coeff_frobenius_fun }⟩

variable {p}

@[ghost_simps] lemma ghost_component_frobenius_fun (n : ℕ) (x : 𝕎 R) :
  ghost_component n (frobenius_fun x) = ghost_component (n + 1) x :=
by simp only [ghost_component_apply, frobenius_fun, coeff_mk,
    ← bind₁_frobenius_poly_witt_polynomial, aeval_bind₁]

/--
If `R` has characteristic `p`, then there is a ring endomorphism
that raises `r : R` to the power `p`.
By applying `witt_vector.map` to this endomorphism,
we obtain a ring endomorphism `frobenius R p : 𝕎 R →+* 𝕎 R`.

The underlying function of this morphism is `witt_vector.frobenius_fun`.
-/
def frobenius : 𝕎 R →+* 𝕎 R :=
{ to_fun := frobenius_fun,
  map_zero' :=
  begin
    refine is_poly.ext
      ((frobenius_fun_is_poly p).comp (witt_vector.zero_is_poly))
      ((witt_vector.zero_is_poly).comp (frobenius_fun_is_poly p)) _ _ 0,
    ghost_simp
  end,
  map_one' :=
  begin
    refine is_poly.ext
      ((frobenius_fun_is_poly p).comp (witt_vector.one_is_poly))
      ((witt_vector.one_is_poly).comp (frobenius_fun_is_poly p)) _ _ 0,
    ghost_simp
  end,
  map_add' := by ghost_calc _ _; ghost_simp,
  map_mul' := by ghost_calc _ _; ghost_simp }

lemma coeff_frobenius (x : 𝕎 R) (n : ℕ) :
  coeff (frobenius x) n = mv_polynomial.aeval x.coeff (frobenius_poly p n) :=
coeff_frobenius_fun _ _

@[ghost_simps] lemma ghost_component_frobenius (n : ℕ) (x : 𝕎 R) :
  ghost_component n (frobenius x) = ghost_component (n + 1) x :=
ghost_component_frobenius_fun _ _

variables (p)

/-- `frobenius` is tautologically a polynomial function. -/
@[is_poly] lemma frobenius_is_poly : is_poly p (λ R _Rcr, @frobenius p R _ _Rcr) :=
frobenius_fun_is_poly _

section char_p
variables [char_p R p]

@[simp]
lemma coeff_frobenius_char_p (x : 𝕎 R) (n : ℕ) :
  coeff (frobenius x) n = (x.coeff n) ^ p :=
begin
  rw [coeff_frobenius],
  -- outline of the calculation, proofs follow below
  calc aeval (λ k, x.coeff k) (frobenius_poly p n)
      = aeval (λ k, x.coeff k)
          (mv_polynomial.map (int.cast_ring_hom (zmod p)) (frobenius_poly p n)) : _
  ... = aeval (λ k, x.coeff k) (X n ^ p : mv_polynomial ℕ (zmod p)) : _
  ... = (x.coeff n) ^ p : _,
  { conv_rhs { rw [aeval_eq_eval₂_hom, eval₂_hom_map_hom] },
    apply eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
  { rw frobenius_poly_zmod },
  { rw [alg_hom.map_pow, aeval_X] }
end

lemma frobenius_eq_map_frobenius :
  @frobenius p R _ _ = map (_root_.frobenius R p) :=
begin
  ext x n,
  simp only [coeff_frobenius_char_p, map_coeff, frobenius_def],
end

@[simp]
lemma frobenius_zmodp (x : 𝕎 (zmod p)) :
  (frobenius x) = x :=
by simp only [ext_iff, coeff_frobenius_char_p, zmod.pow_card, eq_self_iff_true, forall_const]

end char_p

end witt_vector
