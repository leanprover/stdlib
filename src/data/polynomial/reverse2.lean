/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.polynomial.ring_division
import algebra.big_operators.nat_antidiagonal

/-!
# Reverse of a univariate polynomial

In this file we define an alternate version of `reverse`.
The difference between the old `reverse` and the new `reverse'` is that the old
`reverse` will decrease the degree if the polynomial is divisible by `X`.
We also define `norm2`, which is the sum of the squares of the coefficients of a polynomial.
It is also a coefficient of `p * p.reverse'`.

## Main definitions

- `p.reverse'`
- `p.norm2`

## Main results

- `reverse'_mul_of_domain`: `reverse'` preserves multiplication.
- `reverse'_irreducible_test`: an irreducibility criterion involving `reverse'`
- `norm2_eq_mul_reverse_coeff`: `norm2` is a coefficient of `p * p.reverse'`

-/

namespace polynomial

variables {R : Type*} [semiring R] (p : polynomial R)

section reverse'

/-- reverse of a polynomial -/
noncomputable def reverse' := p.reverse * X ^ p.nat_trailing_degree

lemma reverse'_zero : (0 : polynomial R).reverse' = 0 := rfl

lemma reverse'_monomial (n : ℕ) (a : R) : (monomial n a).reverse' = (monomial n a) :=
begin
  by_cases ha : a = 0,
  { rw [ha, monomial_zero_right, reverse'_zero] },
  { rw [reverse', reverse, nat_degree_monomial n a ha, nat_trailing_degree_monomial ha,
        ←C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, rev_at_le (le_refl n),
        nat.sub_self, pow_zero, mul_one] },
end

lemma reverse'_C (a : R) : (C a).reverse' = C a :=
reverse'_monomial 0 a

lemma reverse'_X : X.reverse' = (X : polynomial R) :=
reverse'_monomial 1 (1 : R)

lemma reverse'_nat_degree : p.reverse'.nat_degree = p.nat_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, reverse'_zero] },
  by_cases hR : nontrivial R,
  { haveI := hR,
    rw [reverse', nat_degree_mul', reverse_nat_degree, nat_degree_X_pow,
        nat.sub_add_cancel p.nat_trailing_degree_le_nat_degree],
    rwa [leading_coeff_X_pow, mul_one, reverse_leading_coeff, ne, trailing_coeff_eq_zero] },
  { haveI := not_nontrivial_iff_subsingleton.mp hR,
    exact congr_arg nat_degree (subsingleton.elim p.reverse' p) },
end

lemma reverse'_nat_trailing_degree : p.reverse'.nat_trailing_degree = p.nat_trailing_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, reverse'_zero] },
  { rw [reverse', nat_trailing_degree_mul_X_pow ((mt reverse_eq_zero.mp) hp),
        reverse_nat_trailing_degree, zero_add] },
end

lemma coeff_reverse' (n : ℕ) :
  p.reverse'.coeff n = p.coeff (rev_at (p.nat_degree + p.nat_trailing_degree) n) :=
begin
  by_cases h2 : p.nat_degree < n,
  { rw [coeff_eq_zero_of_nat_degree_lt (by rwa reverse'_nat_degree)],
    by_cases h1 : n ≤ p.nat_degree + p.nat_trailing_degree,
    { rw [rev_at_le h1, coeff_eq_zero_of_lt_nat_trailing_degree],
      exact (nat.sub_lt_left_iff_lt_add h1).mpr (nat.add_lt_add_right h2 _) },
    { rw [←rev_at_fun_eq, rev_at_fun, if_neg h1, coeff_eq_zero_of_nat_degree_lt h2] } },
  rw not_lt at h2,
  rw [rev_at_le (h2.trans (nat.le_add_right _ _))],
  by_cases h3 : p.nat_trailing_degree ≤ n,
  { rw [←nat.sub_add_eq_add_sub h2, ←nat.sub_sub_assoc h2 h3, reverse', coeff_mul_X_pow',
        if_pos h3, coeff_reverse, rev_at_le ((nat.sub_le_self _ _).trans h2)] },
  rw not_le at h3,
  rw coeff_eq_zero_of_nat_degree_lt (nat.lt_sub_right_iff_add_lt.mpr (nat.add_lt_add_left h3 _)),
  exact coeff_eq_zero_of_lt_nat_trailing_degree (by rwa reverse'_nat_trailing_degree),
end

lemma reverse'_eval_one : p.reverse'.eval 1 = p.eval 1 :=
begin
  simp_rw [eval_eq_finset_sum, one_pow, mul_one, reverse'_nat_degree],
  refine finset.sum_bij_ne_zero _ _ _ _ _,
  { exact λ n hn hp, rev_at (p.nat_degree + p.nat_trailing_degree) n },
  { intros n hn hp,
    rw finset.mem_range_succ_iff at *,
    rw rev_at_le (hn.trans (nat.le_add_right _ _)),
    rw [nat.sub_le_iff, add_comm, nat.add_sub_cancel, ←reverse'_nat_trailing_degree],
    exact nat_trailing_degree_le_of_ne_zero hp },
  { exact λ n₁ n₂ hn₁ hp₁ hn₂ hp₂ h, by rw [←@rev_at_invol _ n₁, h, rev_at_invol] },
  { intros n hn hp,
    use rev_at (p.nat_degree + p.nat_trailing_degree) n,
    refine ⟨_, _, rev_at_invol.symm⟩,
    { rw finset.mem_range_succ_iff at *,
      rw rev_at_le (hn.trans (nat.le_add_right _ _)),
      rw [nat.sub_le_iff, add_comm, nat.add_sub_cancel],
      exact nat_trailing_degree_le_of_ne_zero hp },
    { change p.reverse'.coeff _ ≠ 0,
      rwa [coeff_reverse', rev_at_invol] } },
  { exact λ n hn hp, p.coeff_reverse' n },
end

lemma reverse'_reverse' : p.reverse'.reverse' = p :=
polynomial.ext (λ n, by rw [coeff_reverse', coeff_reverse',
  reverse'_nat_degree, reverse'_nat_trailing_degree, rev_at_invol])

lemma reverse'_eq_zero : p.reverse' = 0 ↔ p = 0 :=
⟨λ h, by rw [←p.reverse'_reverse', h, reverse'_zero], λ h, by rw [h, reverse'_zero]⟩

lemma reverse'_trailing_coeff : p.reverse'.trailing_coeff = p.leading_coeff :=
by rw [leading_coeff, trailing_coeff, reverse'_nat_trailing_degree, coeff_reverse',
  rev_at_le (nat.le_add_left _ _), nat.add_sub_cancel]

lemma reverse'_leading_coeff : p.reverse'.leading_coeff = p.trailing_coeff :=
by rw [←p.reverse'_reverse', reverse'_trailing_coeff, p.reverse'_reverse']

lemma reverse'_mul_of_domain {R : Type*} [integral_domain R] (p q : polynomial R) :
  (p * q).reverse' = p.reverse' * q.reverse' :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, reverse'_zero, zero_mul] },
  by_cases hq : q = 0,
  { rw [hq, mul_zero, reverse'_zero, mul_zero] },
  rw [reverse', reverse', reverse', reverse_mul_of_domain, nat_trailing_degree_mul hp hq, pow_add],
  ring,
end

lemma reverse'_smul {R : Type*} [integral_domain R] (p : polynomial R) (a : R) :
  (a • p).reverse' = a • p.reverse' :=
by rw [←C_mul', ←C_mul', reverse'_mul_of_domain, reverse'_C]

lemma reverse'_neg {R : Type*} [ring R] (p : polynomial R) : (-p).reverse' = -(p.reverse') :=
by rw [reverse', reverse', reverse_neg, nat_trailing_degree_neg, neg_mul_eq_neg_mul]

lemma reverse'_irreducible_test {R : Type*} [integral_domain R] {f : polynomial R}
  (h1 : ¬ is_unit f)
  (h2 : ∀ k, f * f.reverse' = k * k.reverse' → k = f ∨ k = -f ∨ k = f.reverse' ∨ k = -f.reverse')
  (h3 : ∀ g, g ∣ f → g ∣ f.reverse' → is_unit g) : irreducible f :=
begin
  split,
  { exact h1 },
  { intros g h fgh,
    let k := g * h.reverse',
    have key : f * f.reverse' = k * k.reverse',
    { rw [fgh, reverse'_mul_of_domain, reverse'_mul_of_domain, reverse'_reverse',
          mul_assoc, mul_comm h, mul_comm g.reverse', mul_assoc, ←mul_assoc] },
    have g_dvd_f : g ∣ f,
    { rw fgh,
      exact dvd_mul_right g h },
    have h_dvd_f : h ∣ f,
    { rw fgh,
      exact dvd_mul_left h g },
    have g_dvd_k : g ∣ k,
    { exact dvd_mul_right g h.reverse' },
    have h_dvd_k_rev : h ∣ k.reverse',
    { rw [reverse'_mul_of_domain, reverse'_reverse'],
      exact dvd_mul_left h g.reverse' },
    have hk := h2 k key,
    rcases hk with hk | hk | hk | hk,
    { exact or.inr (h3 h h_dvd_f (by rwa ← hk)) },
    { exact or.inr (h3 h h_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, reverse'_neg, dvd_neg])) },
    { exact or.inl (h3 g g_dvd_f (by rwa ← hk)) },
    { exact or.inl (h3 g g_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, dvd_neg])) } },
end

end reverse'

section norm2

/-- the sum of the square of the coefficients of a polynomial -/
def norm2 := p.support.sum (λ k, (p.coeff k) ^ 2)

lemma norm2_eq_sum_of_support {s : finset ℕ}
  (h : p.support ⊆ s) : p.norm2 = s.sum (λ k, (p.coeff k) ^ 2) :=
finset.sum_subset h (λ k h1 h2, by rw [not_mem_support_iff_coeff_zero.mp h2, pow_two, zero_mul])

lemma norm2_monomial (k : ℕ) (a : R) : (monomial k a).norm2 = a ^ 2 :=
by rw [norm2_eq_sum_of_support _ (support_monomial' k a),
  finset.sum_singleton, coeff_monomial, if_pos rfl]

lemma norm2_C (a : R) : (C a).norm2 = a ^ 2 := norm2_monomial 0 a

lemma norm2_zero : (0 : polynomial R).norm2 = 0 := by rw [←C_0, norm2_C, pow_two, zero_mul]

lemma norm2_eq_zero {R : Type*} [linear_ordered_ring R] {p : polynomial R} :
  p.norm2 = 0 ↔ p = 0 :=
begin
  split,
  { rw [norm2, finset.sum_eq_zero_iff_of_nonneg (λ k hk, pow_two_nonneg (p.coeff k))],
    simp_rw [pow_eq_zero_iff zero_lt_two, mem_support_iff_coeff_ne_zero, not_imp_self],
    rw polynomial.ext_iff,
    exact id },
  { intro hp,
    rw [hp, norm2_zero] },
end

lemma norm2_eq_mul_reverse_coeff :
  p.norm2 = (p * p.reverse').coeff (p.nat_degree + p.nat_trailing_degree) :=
begin
  have h : p.support ⊆ finset.range (p.nat_degree + p.nat_trailing_degree).succ :=
  λ x hx, finset.mem_range_succ_iff.mpr ((le_nat_degree_of_ne_zero
    (mem_support_iff_coeff_ne_zero.mp hx)).trans (nat.le_add_right _ _)),
  rw [eq_comm, p.norm2_eq_sum_of_support h, coeff_mul,
      finset.nat.sum_antidiagonal_eq_sum_range_succ_mk],
  apply finset.sum_congr rfl,
  intros k hk,
  rw [pow_two, coeff_reverse', ←rev_at_le (finset.mem_range_succ_iff.mp hk), rev_at_invol],
end

-- `p.nat_degree` can be recovered from `p * p.reverse'`
lemma nat_degree_mul_reverse' {R : Type*} [integral_domain R] (p : polynomial R) :
  (p * p.reverse').nat_degree = 2 * p.nat_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, nat_degree_zero, mul_zero] },
  { rw [nat_degree_mul hp (mt p.reverse'_eq_zero.mp hp), reverse'_nat_degree, two_mul] },
end

-- `p.nat_trailing_degree` can be recovered from `p * p.reverse'`
lemma nat_trailing_degree_mul_reverse' {R : Type*} [integral_domain R] (p : polynomial R) :
  (p * p.reverse').nat_trailing_degree = 2 * p.nat_trailing_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, nat_trailing_degree_zero, mul_zero] },
  { rw [nat_trailing_degree_mul hp (mt p.reverse'_eq_zero.mp hp),
        reverse'_nat_trailing_degree, two_mul] },
end

-- `p.norm2` can be recovered from `p * p.reverse'`
lemma central_coeff_mul_reverse' {R : Type*} [integral_domain R] (p : polynomial R) :
  (p * p.reverse').coeff (((p * p.reverse').nat_degree +
    (p * p.reverse').nat_trailing_degree) / 2) = p.norm2 :=
by rw [nat_degree_mul_reverse', nat_trailing_degree_mul_reverse',  ←mul_add,
  nat.mul_div_cancel_left _ zero_lt_two, norm2_eq_mul_reverse_coeff]

lemma norm2_nonneg {R : Type*} [linear_ordered_ring R] (p : polynomial R) :
  0 ≤ norm2 p :=
finset.sum_nonneg (λ _ _, pow_two_nonneg _)

lemma coeff_sq_le_norm2 {R : Type*} [linear_ordered_ring R] (p : polynomial R) (k : ℕ) :
  p.coeff k ^ 2 ≤ p.norm2 :=
begin
  rw [norm2, ←finset.sum_insert_of_eq_zero_if_not_mem],
  exact (le_of_eq (finset.sum_singleton.symm)).trans (finset.sum_le_sum_of_subset_of_nonneg
    (finset.singleton_subset_iff.mpr (finset.mem_insert_self k p.support))
    (λ j _ _, pow_two_nonneg (p.coeff j))),
  exact λ h, (pow_eq_zero_iff zero_lt_two).mpr (not_mem_support_iff_coeff_zero.mp h),
end

lemma norm2_eq_card_support (hp : ∀ k, p.coeff k ≠ 0 → p.coeff k ^ 2 = 1) :
  p.norm2 = p.support.card :=
begin
  rw [←ring_hom.eq_nat_cast (nat.cast_ring_hom R), finset.card_eq_sum_ones, ring_hom.map_sum],
  simp only [ring_hom.map_one],
  exact finset.sum_congr rfl (λ k hk, hp k (mem_support_iff_coeff_ne_zero.mp hk)),
end

lemma coeff_sq_eq_one_of_norm2_le_three (p : polynomial ℤ) (hp : p.norm2 ≤ 3) (k : ℕ)
  (hk : p.coeff k ≠ 0) : p.coeff k ^ 2 = 1 :=
begin
  replace hp := (p.coeff_sq_le_norm2 k).trans hp,
  rw [←int.nat_abs_pow_two, ←int.coe_nat_pow, ←int.coe_nat_one, int.coe_nat_inj',
      pow_two, nat.mul_eq_one_iff, and_self],
  apply le_antisymm,
  { rwa [←nat.lt_succ_iff, ←nat.pow_lt_iff_lt_left one_le_two, ←int.coe_nat_lt_coe_nat_iff,
        int.coe_nat_pow, int.nat_abs_pow_two, ←int.le_sub_one_iff] },
  { rwa [nat.succ_le_iff, pos_iff_ne_zero, ne, int.nat_abs_eq_zero] },
end

lemma card_support_eq_three_of_norm2_eq_three (p : polynomial ℤ) (hp : p.norm2 = 3) :
  p.support.card = 3 :=
nat.cast_inj.mp
  ((p.norm2_eq_card_support (p.coeff_sq_eq_one_of_norm2_le_three (le_of_eq hp))).symm.trans hp)

end norm2

end polynomial
