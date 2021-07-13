/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.polynomial.ring_division
import algebra.big_operators.nat_antidiagonal
import linear_algebra.quadratic_form

/-!
# "Mirror" of a univariate polynomial

In this file we define `polynomial.mirror`, a variant of `polynomial.reverse`. The difference
between `reverse` and `mirror` is that `reverse` will decrease the degree if the polynomial is
divisible by `X`. We also define `polynomial.norm2`, which is the sum of the squares of the
coefficients of a polynomial. It is also a coefficient of `p * p.mirror`.

## Main definitions

- `polynomial.mirror`
- `polynomial.norm2`

## Main results

- `polynomial.mirror_mul_of_domain`: `mirror` preserves multiplication.
- `polynomial.irreducible_of_mirror`: an irreducibility criterion involving `mirror`
- `polynomial.norm2_eq_mul_reverse_coeff`: `norm2` is a coefficient of `p * p.mirror`

-/

namespace polynomial

section mirror

variables {R : Type*} [semiring R] (p : polynomial R)

/-- mirror of a polynomial: reverses the coefficients while preserving `polynomial.nat_degree` -/
noncomputable def mirror := p.reverse * X ^ p.nat_trailing_degree

@[simp] lemma mirror_zero : (0 : polynomial R).mirror = 0 := by simp [mirror]

lemma mirror_monomial (n : ℕ) (a : R) : (monomial n a).mirror = (monomial n a) :=
begin
  by_cases ha : a = 0,
  { rw [ha, monomial_zero_right, mirror_zero] },
  { rw [mirror, reverse, nat_degree_monomial n a ha, nat_trailing_degree_monomial ha,
        ←C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, rev_at_le (le_refl n),
        nat.sub_self, pow_zero, mul_one] },
end

lemma mirror_C (a : R) : (C a).mirror = C a :=
mirror_monomial 0 a

lemma mirror_X : X.mirror = (X : polynomial R) :=
mirror_monomial 1 (1 : R)

lemma mirror_nat_degree : p.mirror.nat_degree = p.nat_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, mirror_zero] },
  by_cases hR : nontrivial R,
  { haveI := hR,
    rw [mirror, nat_degree_mul', reverse_nat_degree, nat_degree_X_pow,
        nat.sub_add_cancel p.nat_trailing_degree_le_nat_degree],
    rwa [leading_coeff_X_pow, mul_one, reverse_leading_coeff, ne, trailing_coeff_eq_zero] },
  { haveI := not_nontrivial_iff_subsingleton.mp hR,
    exact congr_arg nat_degree (subsingleton.elim p.mirror p) },
end

lemma mirror_nat_trailing_degree : p.mirror.nat_trailing_degree = p.nat_trailing_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, mirror_zero] },
  { rw [mirror, nat_trailing_degree_mul_X_pow ((mt reverse_eq_zero.mp) hp),
        reverse_nat_trailing_degree, zero_add] },
end

lemma coeff_mirror (n : ℕ) :
  p.mirror.coeff n = p.coeff (rev_at (p.nat_degree + p.nat_trailing_degree) n) :=
begin
  by_cases h2 : p.nat_degree < n,
  { rw [coeff_eq_zero_of_nat_degree_lt (by rwa mirror_nat_degree)],
    by_cases h1 : n ≤ p.nat_degree + p.nat_trailing_degree,
    { rw [rev_at_le h1, coeff_eq_zero_of_lt_nat_trailing_degree],
      exact (nat.sub_lt_left_iff_lt_add h1).mpr (nat.add_lt_add_right h2 _) },
    { rw [←rev_at_fun_eq, rev_at_fun, if_neg h1, coeff_eq_zero_of_nat_degree_lt h2] } },
  rw not_lt at h2,
  rw [rev_at_le (h2.trans (nat.le_add_right _ _))],
  by_cases h3 : p.nat_trailing_degree ≤ n,
  { rw [←nat.sub_add_eq_add_sub h2, ←nat.sub_sub_assoc h2 h3, mirror, coeff_mul_X_pow',
        if_pos h3, coeff_reverse, rev_at_le ((nat.sub_le_self _ _).trans h2)] },
  rw not_le at h3,
  rw coeff_eq_zero_of_nat_degree_lt (nat.lt_sub_right_iff_add_lt.mpr (nat.add_lt_add_left h3 _)),
  exact coeff_eq_zero_of_lt_nat_trailing_degree (by rwa mirror_nat_trailing_degree),
end

--TODO: Extract `finset.sum_range_rev_at` lemma.
lemma mirror_eval_one : p.mirror.eval 1 = p.eval 1 :=
begin
  simp_rw [eval_eq_finset_sum, one_pow, mul_one, mirror_nat_degree],
  refine finset.sum_bij_ne_zero _ _ _ _ _,
  { exact λ n hn hp, rev_at (p.nat_degree + p.nat_trailing_degree) n },
  { intros n hn hp,
    rw finset.mem_range_succ_iff at *,
    rw rev_at_le (hn.trans (nat.le_add_right _ _)),
    rw [nat.sub_le_iff, add_comm, nat.add_sub_cancel, ←mirror_nat_trailing_degree],
    exact nat_trailing_degree_le_of_ne_zero hp },
  { exact λ n₁ n₂ hn₁ hp₁ hn₂ hp₂ h, by rw [←@rev_at_invol _ n₁, h, rev_at_invol] },
  { intros n hn hp,
    use rev_at (p.nat_degree + p.nat_trailing_degree) n,
    refine ⟨_, _, rev_at_invol.symm⟩,
    { rw finset.mem_range_succ_iff at *,
      rw rev_at_le (hn.trans (nat.le_add_right _ _)),
      rw [nat.sub_le_iff, add_comm, nat.add_sub_cancel],
      exact nat_trailing_degree_le_of_ne_zero hp },
    { change p.mirror.coeff _ ≠ 0,
      rwa [coeff_mirror, rev_at_invol] } },
  { exact λ n hn hp, p.coeff_mirror n },
end

lemma mirror_mirror : p.mirror.mirror = p :=
polynomial.ext (λ n, by rw [coeff_mirror, coeff_mirror,
  mirror_nat_degree, mirror_nat_trailing_degree, rev_at_invol])

lemma mirror_eq_zero : p.mirror = 0 ↔ p = 0 :=
⟨λ h, by rw [←p.mirror_mirror, h, mirror_zero], λ h, by rw [h, mirror_zero]⟩

lemma mirror_trailing_coeff : p.mirror.trailing_coeff = p.leading_coeff :=
by rw [leading_coeff, trailing_coeff, mirror_nat_trailing_degree, coeff_mirror,
  rev_at_le (nat.le_add_left _ _), nat.add_sub_cancel]

lemma mirror_leading_coeff : p.mirror.leading_coeff = p.trailing_coeff :=
by rw [←p.mirror_mirror, mirror_trailing_coeff, p.mirror_mirror]

lemma mirror_mul_of_domain {R : Type*} [integral_domain R] (p q : polynomial R) :
  (p * q).mirror = p.mirror * q.mirror :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, mirror_zero, zero_mul] },
  by_cases hq : q = 0,
  { rw [hq, mul_zero, mirror_zero, mul_zero] },
  rw [mirror, mirror, mirror, reverse_mul_of_domain, nat_trailing_degree_mul hp hq, pow_add],
  ring,
end

lemma mirror_smul {R : Type*} [integral_domain R] (p : polynomial R) (a : R) :
  (a • p).mirror = a • p.mirror :=
by rw [←C_mul', ←C_mul', mirror_mul_of_domain, mirror_C]

lemma mirror_neg {R : Type*} [ring R] (p : polynomial R) : (-p).mirror = -(p.mirror) :=
by rw [mirror, mirror, reverse_neg, nat_trailing_degree_neg, neg_mul_eq_neg_mul]

lemma irreducible_of_mirror {R : Type*} [integral_domain R] {f : polynomial R}
  (h1 : ¬ is_unit f)
  (h2 : ∀ k, f * f.mirror = k * k.mirror → k = f ∨ k = -f ∨ k = f.mirror ∨ k = -f.mirror)
  (h3 : ∀ g, g ∣ f → g ∣ f.mirror → is_unit g) : irreducible f :=
begin
  split,
  { exact h1 },
  { intros g h fgh,
    let k := g * h.mirror,
    have key : f * f.mirror = k * k.mirror,
    { rw [fgh, mirror_mul_of_domain, mirror_mul_of_domain, mirror_mirror,
          mul_assoc, mul_comm h, mul_comm g.mirror, mul_assoc, ←mul_assoc] },
    have g_dvd_f : g ∣ f,
    { rw fgh,
      exact dvd_mul_right g h },
    have h_dvd_f : h ∣ f,
    { rw fgh,
      exact dvd_mul_left h g },
    have g_dvd_k : g ∣ k,
    { exact dvd_mul_right g h.mirror },
    have h_dvd_k_rev : h ∣ k.mirror,
    { rw [mirror_mul_of_domain, mirror_mirror],
      exact dvd_mul_left h g.mirror },
    have hk := h2 k key,
    rcases hk with hk | hk | hk | hk,
    { exact or.inr (h3 h h_dvd_f (by rwa ← hk)) },
    { exact or.inr (h3 h h_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, mirror_neg, dvd_neg])) },
    { exact or.inl (h3 g g_dvd_f (by rwa ← hk)) },
    { exact or.inl (h3 g g_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, dvd_neg])) } },
end

end mirror

section norm2

variables {R : Type*} [comm_ring R] (p q : polynomial R)

def norm2_fun : polynomial R → R := λ p, p.sum (λ k c, c ^ 2)

lemma norm2_fun_def : p.norm2_fun = p.sum (λ k c, c ^ 2) := rfl

lemma norm2_fun_eq_sum_of_support {s : finset ℕ} (h : p.support ⊆ s) :
  p.norm2_fun = s.sum (λ k, (p.coeff k) ^ 2) :=
finset.sum_subset h (λ k h1 h2, by
{ rw [finsupp.not_mem_support_iff.mp h2], exact zero_pow zero_lt_two })

lemma smul_norm2_fun (a : R) : (a • p).norm2_fun = a * a * p.norm2_fun :=
begin
  rw [norm2_fun_def, norm2_fun_def, finsupp.sum_smul_index, finsupp.mul_sum],
  congr,
  { exact _root_.funext (λ _, _root_.funext (λ _, by ring)) },
  { exact λ k, zero_pow zero_lt_two },
end

lemma polar_norm2_fun {s : finset ℕ} (hp : p.support ⊆ s) (hq : q.support ⊆ s) :
  quadratic_form.polar norm2_fun p q = s.sum (λ k, 2 * (p.coeff k) * (q.coeff k)) :=
begin
  rw [quadratic_form.polar, (p + q).norm2_fun_eq_sum_of_support,
      p.norm2_fun_eq_sum_of_support hp, q.norm2_fun_eq_sum_of_support hq,
      sub_eq_iff_eq_add', sub_eq_iff_eq_add', ←finset.sum_add_distrib, ←finset.sum_add_distrib],
  apply finset.sum_congr rfl,
  { intros k hk,
    rw coeff_add,
    ring },
  { apply finset.subset.trans finsupp.support_add _,
    convert (finset.union_subset hp hq) },
end

/-- the sum of the square of the coefficients of a polynomial -/
noncomputable def norm2 : quadratic_form R (polynomial R) :=
quadratic_form.mk_left norm2_fun (λ a p, p.smul_norm2_fun a)
begin
  intros p q r,
  let s := p.support ∪ q.support ∪ r.support,
  have hpq : p.support ∪ q.support ⊆ s := finset.subset_union_left _ _,
  have hp : p.support ⊆ s := finset.subset.trans (finset.subset_union_left _ _) hpq,
  have hq : q.support ⊆ s := finset.subset.trans (finset.subset_union_right _ _) hpq,
  have hr : r.support ⊆ s := finset.subset_union_right _ _,
  replace hpq : (p + q).support ⊆ s,
  { refine finset.subset.trans finsupp.support_add _,
    convert hpq },
  rw [(p + q).polar_norm2_fun r hpq hr, p.polar_norm2_fun r hp hr,
      q.polar_norm2_fun r hq hr, ←finset.sum_add_distrib],
  apply finset.sum_congr rfl,
  intros k hk,
  rw coeff_add,
  ring,
end
begin
  intros a p q,
  let s := p.support ∪ q.support,
  have hp : p.support ⊆ s := finset.subset_union_left _ _,
  have hq : q.support ⊆ s := finset.subset_union_right _ _,
  have hap : (a • p).support ⊆ s := finset.subset.trans finsupp.support_smul hp,
  rw [(a • p).polar_norm2_fun q hap hq, p.polar_norm2_fun q hp hq, finset.mul_sum],
  apply finset.sum_congr rfl,
  intros k hk,
  rw coeff_smul,
  ring,
end

lemma norm2_eq_sum_of_support {s : finset ℕ}
  (h : p.support ⊆ s) : p.norm2 = s.sum (λ k, (p.coeff k) ^ 2) :=
p.norm2_fun_eq_sum_of_support h

lemma norm2_monomial (k : ℕ) (a : R) : (monomial k a).norm2 = a ^ 2 :=
by rw [norm2_eq_sum_of_support _ (support_monomial' k a),
  finset.sum_singleton, coeff_monomial, if_pos rfl]

lemma norm2_C (a : R) : (C a).norm2 = a ^ 2 := norm2_monomial 0 a

lemma norm2_zero : (0 : polynomial R).norm2 = 0 := by rw [←C_0, norm2_C, pow_two, zero_mul]

lemma norm2_eq_mul_reverse_coeff :
  p.norm2 = (p * p.mirror).coeff (p.nat_degree + p.nat_trailing_degree) :=
begin
  have h : p.support ⊆ finset.range (p.nat_degree + p.nat_trailing_degree).succ :=
  λ x hx, finset.mem_range_succ_iff.mpr ((le_nat_degree_of_ne_zero
    (mem_support_iff_coeff_ne_zero.mp hx)).trans (nat.le_add_right _ _)),
  rw [eq_comm, p.norm2_eq_sum_of_support h, coeff_mul,
      finset.nat.sum_antidiagonal_eq_sum_range_succ_mk],
  apply finset.sum_congr rfl,
  intros k hk,
  rw [pow_two, coeff_mirror, ←rev_at_le (finset.mem_range_succ_iff.mp hk), rev_at_invol],
end

-- `p.nat_degree` can be recovered from `p * p.mirror`
lemma nat_degree_mul_mirror {R : Type*} [integral_domain R] (p : polynomial R) :
  (p * p.mirror).nat_degree = 2 * p.nat_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, nat_degree_zero, mul_zero] },
  { rw [nat_degree_mul hp (mt p.mirror_eq_zero.mp hp), mirror_nat_degree, two_mul] },
end

-- `p.nat_trailing_degree` can be recovered from `p * p.mirror`
lemma nat_trailing_degree_mul_mirror {R : Type*} [integral_domain R] (p : polynomial R) :
  (p * p.mirror).nat_trailing_degree = 2 * p.nat_trailing_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, nat_trailing_degree_zero, mul_zero] },
  { rw [nat_trailing_degree_mul hp (mt p.mirror_eq_zero.mp hp),
        mirror_nat_trailing_degree, two_mul] },
end

-- `p.norm2` can be recovered from `p * p.mirror`
lemma central_coeff_mul_mirror {R : Type*} [integral_domain R] (p : polynomial R) :
  (p * p.mirror).coeff (((p * p.mirror).nat_degree +
    (p * p.mirror).nat_trailing_degree) / 2) = p.norm2 :=
by rw [nat_degree_mul_mirror, nat_trailing_degree_mul_mirror,  ←mul_add,
  nat.mul_div_cancel_left _ zero_lt_two, norm2_eq_mul_reverse_coeff]

lemma norm2_nonneg {R : Type*} [linear_ordered_comm_ring R] (p : polynomial R) :
  0 ≤ norm2 p :=
finset.sum_nonneg (λ n _, pow_two_nonneg (p.coeff n))

lemma norm2.anisotropic {R : Type*} [linear_ordered_comm_ring R] [no_zero_divisors R] :
  (norm2 : quadratic_form R (polynomial R)).anisotropic :=
begin
  intros p hp,
  ext n,
  by_cases hn : n ∈ p.support,
  { exact pow_eq_zero ((finset.sum_eq_zero_iff_of_nonneg
      (λ m _, pow_two_nonneg (p.coeff m))).mp hp n hn) },
  { rw [not_mem_support_iff_coeff_zero.mp hn, coeff_zero] },
end

lemma norm2.pos_def {R : Type*} [linear_ordered_comm_ring R] [no_zero_divisors R] :
  (norm2 : quadratic_form R (polynomial R)).pos_def :=
λ p hp, lt_of_le_of_ne p.norm2_nonneg (ne.symm (mt (norm2.anisotropic p) hp))

lemma norm2_eq_zero {R : Type*} [linear_ordered_comm_ring R] {p : polynomial R} :
  p.norm2 = 0 ↔ p = 0 :=
⟨norm2.anisotropic p, λ h, (congr_arg norm2 h).trans norm2_zero⟩

lemma coeff_sq_le_norm2 {R : Type*} [linear_ordered_comm_ring R] (p : polynomial R) (k : ℕ) :
  p.coeff k ^ 2 ≤ p.norm2 :=
begin
  change _ ≤ finset.sum _ _,
  rw ← finset.sum_insert_of_eq_zero_if_not_mem,
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
