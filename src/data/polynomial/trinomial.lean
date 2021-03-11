/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.polynomial.reverse2
import analysis.complex.polynomial

/-!
# Bundled Trinomials

In this file we define an bundled trinomial, which are easier to
work with than a sum of monomials.

## Main definitions

- `polynomial.trinomial`
- `trinomial.of_polynomial`: unbundle a trinomial
- `polynomial.to_trinomial`: bundle a trinomial

## Main results

- `reverse'_irreducible_test'`: an irreducibility criterion for unit trinomials
- `reverse'_irreducible_test''`: an irreducibility criterion for unit trinomials
- `selmer_irreducible`: the polynomial `X ^ n - X - 1` is irreducible for all `n ≠ 1`

-/

namespace polynomial

/-- bundled trinomial -/
structure trinomial (R : Type*) [semiring R] :=
(a b c : R) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (i j k : ℕ) (hij : i < j) (hjk : j < k)

instance (R : Type*) [semiring R] [nontrivial R] : inhabited (trinomial R) :=
⟨trinomial.mk 1 1 1 one_ne_zero one_ne_zero one_ne_zero 0 1 2 zero_lt_one one_lt_two⟩

namespace trinomial

variables {R : Type*} [semiring R] (t : trinomial R)

lemma hik : t.i < t.k := t.hij.trans t.hjk

@[ext] lemma ext {s t : trinomial R} (ha : s.a = t.a) (hb : s.b = t.b) (hc : s.c = t.c)
  (hi : s.i = t.i) (hj : s.j = t.j) (hk : s.k = t.k) : s = t :=
begin
  cases s,
  cases t,
  exact mk.inj_eq.mpr ⟨ha, hb, hc, hi, hj, hk⟩,
end

/-- unbundle a trinomial -/
noncomputable def to_polynomial : polynomial R :=
(monomial t.i t.a) + (monomial t.j t.b) + (monomial t.k t.c)

lemma coeff_i : t.to_polynomial.coeff t.i = t.a :=
by rw [to_polynomial, coeff_add, coeff_add, coeff_monomial, coeff_monomial, coeff_monomial,
  if_neg (ne_of_gt t.hij), add_zero, if_neg (ne_of_gt t.hik), add_zero, if_pos rfl]

lemma coeff_j : t.to_polynomial.coeff t.j = t.b :=
by rw [to_polynomial, coeff_add, coeff_add, coeff_monomial, coeff_monomial, coeff_monomial,
  if_neg (ne_of_lt t.hij), zero_add, if_neg (ne_of_gt t.hjk), add_zero, if_pos rfl]

lemma coeff_k : t.to_polynomial.coeff t.k = t.c :=
by rw [to_polynomial, coeff_add, coeff_add, coeff_monomial, coeff_monomial, coeff_monomial,
  if_neg (ne_of_lt t.hik), zero_add, if_neg (ne_of_lt t.hjk), zero_add, if_pos rfl]

lemma eval_one : t.to_polynomial.eval 1 = t.a + t.b + t.c :=
by simp_rw [to_polynomial, eval_add, eval_monomial, one_pow, mul_one]

lemma support : t.to_polynomial.support = {t.i, t.j, t.k} :=
begin
  apply finset.subset.antisymm,
  { apply finset.subset.trans finsupp.support_add,
    apply finset.union_subset,
    apply finset.subset.trans finsupp.support_add,
    apply finset.union_subset,
    all_goals
    { apply finset.subset.trans (support_monomial' _ _) (finset.singleton_subset_iff.mpr _),
      rw [finset.mem_insert, finset.mem_insert, finset.mem_singleton] },
    { exact or.inl rfl },
    { exact or.inr (or.inl rfl) },
    { exact or.inr (or.inr rfl) } },
  { rw [finset.insert_subset, finset.insert_subset, finset.singleton_subset_iff,
        mem_support_iff_coeff_ne_zero, t.coeff_i, mem_support_iff_coeff_ne_zero, t.coeff_j,
        mem_support_iff_coeff_ne_zero, t.coeff_k],
    exact ⟨t.ha, t.hb, t.hc⟩ },
end

lemma norm2 : t.to_polynomial.norm2 = t.a ^ 2 + t.b ^ 2 + t.c ^ 2 :=
by rw [norm2, support, finset.sum_insert (mt finset.mem_insert.mp (not_or (ne_of_lt t.hij)
  (mt finset.mem_singleton.mp (ne_of_lt t.hik)))), finset.sum_insert (mt finset.mem_singleton.mp
  (ne_of_lt t.hjk)), finset.sum_singleton, t.coeff_i, t.coeff_j, t.coeff_k, add_assoc]

lemma card_support : t.to_polynomial.support.card = 3 :=
by rw [t.support, finset.card_insert_of_not_mem (mt finset.mem_insert.mp (not_or (ne_of_lt t.hij)
  (mt finset.mem_singleton.mp (ne_of_lt t.hik)))), finset.card_insert_of_not_mem
  (mt finset.mem_singleton.mp (ne_of_lt t.hjk)), finset.card_singleton]

lemma ne_zero (t : trinomial R) : t.to_polynomial ≠ 0 :=
λ h, nat.bit1_ne_zero 1 (t.card_support.symm.trans (finsupp.card_support_eq_zero.mpr h))

/-- turn a polynomial into a trinomial -/
noncomputable def of_polynomial {p : polynomial R} (h0 : p.support.card = 3) :
  trinomial R :=
let h1 := erase_lead_card_support h0,
  h2 := erase_lead_card_support h1,
  h3 := erase_lead_card_support h2,
  h0' := λ h, nat.bit1_ne_zero 1 (h0.symm.trans (finsupp.card_support_eq_zero.mpr h)),
  h1' := λ h, two_ne_zero (h1.symm.trans (finsupp.card_support_eq_zero.mpr h)),
  h2' := λ h, one_ne_zero (h2.symm.trans (finsupp.card_support_eq_zero.mpr h)),
  h3' := finsupp.card_support_eq_zero.mp h3 in
{ a := p.erase_lead.erase_lead.leading_coeff,
  b := p.erase_lead.leading_coeff,
  c := p.leading_coeff,
  ha := mt leading_coeff_eq_zero.mp h2',
  hb := mt leading_coeff_eq_zero.mp h1',
  hc := mt leading_coeff_eq_zero.mp h0',
  i := p.erase_lead.erase_lead.nat_degree,
  j := p.erase_lead.nat_degree,
  k := p.nat_degree,
  hij := erase_lead_nat_degree_lt (ge_of_eq h1),
  hjk := erase_lead_nat_degree_lt ((nat.le_succ 2).trans (ge_of_eq h0)) }

lemma of_polynomial_to_polynomial {p : polynomial R} (h0 : p.support.card = 3) :
  (of_polynomial h0).to_polynomial = p :=
begin
  conv_rhs
  { rw ← p.erase_lead_add_monomial_nat_degree_leading_coeff,
    rw ← p.erase_lead.erase_lead_add_monomial_nat_degree_leading_coeff,
    rw ← p.erase_lead.erase_lead.erase_lead_add_monomial_nat_degree_leading_coeff,
    rw [finsupp.card_support_eq_zero.mp (erase_lead_card_support
        (erase_lead_card_support (erase_lead_card_support h0))), zero_add] },
  refl,
end

lemma to_polynomial_of_polynomial : of_polynomial t.card_support = t :=
begin
  have h1 : t.to_polynomial = (monomial t.i t.a) + (monomial t.j t.b) + (monomial t.k t.c) := rfl,
  have h2 : t.to_polynomial.nat_degree = t.k,
  { simp_rw [nat_degree_eq_support_max' t.ne_zero, t.support],
    rw [finset.max'_insert, finset.max'_insert, finset.max'_singleton],
    rw [max_eq_left (le_of_lt t.hjk), max_eq_left (le_of_lt t.hik)] },
  have h3 : t.to_polynomial.leading_coeff = t.c,
  { rw [leading_coeff, h2, h1, coeff_add, coeff_add,
        coeff_monomial, coeff_monomial, coeff_monomial,
        if_neg (ne_of_lt t.hik), if_neg (ne_of_lt t.hjk), if_pos rfl, zero_add, zero_add] },
  have h4 : t.to_polynomial.erase_lead = (monomial t.i t.a) + (monomial t.j t.b),
  { rw [erase_lead, h2, h1, monomial_def, monomial_def, monomial_def, finsupp.erase_add,
        finsupp.erase_add, finsupp.erase_single_ne (ne_of_gt t.hik),
        finsupp.erase_single_ne (ne_of_gt t.hjk), finsupp.erase_single, add_zero] },
  have h5 : t.to_polynomial.erase_lead.nat_degree = t.j,
  { rw [h4, ←degree_eq_iff_nat_degree_eq_of_pos (lt_of_le_of_lt t.i.zero_le t.hij),
        degree_add_eq_right_of_degree_lt, degree_monomial t.j t.hb],
    rw [degree_monomial t.i t.ha, degree_monomial t.j t.hb],
    exact with_bot.coe_lt_coe.mpr t.hij },
  have h6 : t.to_polynomial.erase_lead.leading_coeff = t.b,
  { rw [leading_coeff, h5, h4, coeff_add, coeff_monomial, coeff_monomial,
        if_neg (ne_of_lt t.hij), if_pos rfl, zero_add] },
  have h7 : t.to_polynomial.erase_lead.erase_lead = (monomial t.i t.a),
  { rw [erase_lead, h5, h4, monomial_def, monomial_def, finsupp.erase_add,
        finsupp.erase_single_ne (ne_of_gt t.hij), finsupp.erase_single, add_zero] },
  have h8 : t.to_polynomial.erase_lead.erase_lead.nat_degree = t.i,
  { rw [h7, nat_degree_monomial t.i t.a t.ha] },
  have h9 : t.to_polynomial.erase_lead.erase_lead.leading_coeff = t.a,
  { rw [leading_coeff, h8, h7, coeff_monomial, if_pos rfl] },
  exact ext h9 h6 h3 h8 h5 h2,
end

lemma to_polynomial_inj {s t : trinomial R} :
  s.to_polynomial = t.to_polynomial ↔ s = t :=
begin
  split,
  { intro h,
    rw [←s.to_polynomial_of_polynomial, ←t.to_polynomial_of_polynomial],
    simp_rw h },
  { intro h,
    rw h }
end

lemma support_card_eq_three_iff {p : polynomial R} :
  p.support.card = 3 ↔ ∃ t : trinomial R, p = t.to_polynomial :=
begin
  split,
  { exact λ h, ⟨of_polynomial h, (of_polynomial_to_polynomial h).symm⟩ },
  { rintros ⟨t, rfl⟩,
    exact t.card_support },
end

lemma nat_degree : t.to_polynomial.nat_degree = t.k :=
congr_arg k t.to_polynomial_of_polynomial

lemma leading_coeff : t.to_polynomial.leading_coeff = t.c :=
congr_arg c t.to_polynomial_of_polynomial

lemma nat_trailing_degree : t.to_polynomial.nat_trailing_degree = t.i :=
begin
  simp_rw [nat_trailing_degree_eq_support_min' t.ne_zero, t.support],
  rw [finset.min'_insert, finset.min'_insert, finset.min'_singleton],
  rw [min_eq_right (le_of_lt t.hjk), min_eq_right (le_of_lt t.hij)],
end

lemma trailing_coeff : t.to_polynomial.trailing_coeff = t.a :=
by rw [trailing_coeff, nat_trailing_degree, to_polynomial, coeff_add, coeff_add,
  coeff_monomial, coeff_monomial, coeff_monomial,
  if_pos rfl, if_neg (ne_of_gt t.hik), if_neg (ne_of_gt t.hij), add_zero, add_zero]

/-- twist a trinomial by a unit -/
def twist (u : units R) : trinomial R :=
{ a := u * t.a,
  b := u * t.b,
  c := u * t.c,
  ha := mt u.mul_right_eq_zero.mp t.ha,
  hb := mt u.mul_right_eq_zero.mp t.hb,
  hc := mt u.mul_right_eq_zero.mp t.hc,
  i := t.i,
  j := t.j,
  k := t.k,
  hij := t.hij,
  hjk := t.hjk }

lemma twist_one : t.twist 1 = t :=
ext (one_mul _) (one_mul _) (one_mul _) rfl rfl rfl

lemma twist_twist (u v : units R) : (t.twist v).twist u = t.twist (u * v) :=
ext (mul_assoc _ _ _).symm (mul_assoc _ _ _).symm (mul_assoc _ _ _).symm rfl rfl rfl

instance : mul_action (units R) (trinomial R) :=
{ smul := λ u t, t.twist u,
  one_smul := twist_one,
  mul_smul := λ u v t, (t.twist_twist u v).symm }

lemma smul_to_polynomial (u : units R) : (u • t).to_polynomial = (u : R) • t.to_polynomial :=
by { simp_rw [to_polynomial, smul_add, smul_monomial], refl }

lemma neg_to_polynomial {R : Type*} [ring R] (t : trinomial R) :
  ((-1 : units R) • t).to_polynomial = -t.to_polynomial :=
by rw [smul_to_polynomial, units.coe_neg_one, ←C_mul', C_neg, C_1, neg_one_mul]

lemma neg_neg {R : Type*} [ring R] (t : trinomial R) : (-1 : units R) • (-1 : units R) • t = t :=
by rw [smul_smul, units.neg_mul_neg, one_mul, one_smul]

/-- reverse a trinomial -/
def reverse : trinomial R :=
{ a := t.c,
  b := t.b,
  c := t.a,
  ha := t.hc,
  hb := t.hb,
  hc := t.ha,
  i := t.i,
  j := t.i + t.k - t.j,
  k := t.k,
  hij := nat.lt_sub_right_of_add_lt (nat.add_lt_add_left t.hjk t.i),
  hjk := (nat.sub_lt_left_iff_lt_add ((le_of_lt t.hjk).trans (nat.le_add_left t.k t.i))).mpr
    (nat.add_lt_add_right t.hij t.k) }

lemma reverse_smul (u : units R) : (u • t).reverse = u • t.reverse := rfl

lemma reverse_to_polynomial : t.reverse.to_polynomial = t.to_polynomial.reverse' :=
begin
  rw [reverse', t.nat_trailing_degree, polynomial.reverse, t.nat_degree],
  simp_rw [to_polynomial, reflect_add, ←C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow,
    C_mul_X_pow_eq_monomial, X_pow_eq_monomial t.i, add_mul, monomial_mul_monomial, mul_one],
  rw [rev_at_le (le_of_lt t.hik), nat.sub_add_cancel (le_of_lt t.hik)],
  rw [rev_at_le (le_of_lt t.hjk), nat.sub_add_eq_add_sub (le_of_lt t.hjk), nat.add_comm t.k t.i],
  rw [rev_at_le (le_refl t.k), nat.sub_self, zero_add],
  rw [add_assoc (monomial t.k t.a), add_comm (monomial t.k t.a), add_comm _ (monomial t.i t.c)],
  refl,
end

lemma reverse_reverse : t.reverse.reverse = t :=
by rw [←to_polynomial_inj, reverse_to_polynomial, reverse_to_polynomial, reverse'_reverse']

section main_proof

section rel

variables {S : Type*} [ring S] (q r s : trinomial S)

/-- two trinomial are related if they are the same up to negation and reverse -/
def rel :=
s = r ∨ s = (-1 : units S) • r ∨ s = r.reverse ∨ s = (-1 : units S) • r.reverse

@[refl] lemma rel_refl : rel s s := or.inl rfl

lemma rel_of_neg_rel : rel ((-1 : units S) • r) s → rel r s :=
begin
  rintro (h | h | h | h),
  { exact or.inr (or.inl h) },
  { exact or.inl (by rw [h, neg_neg]) },
  { exact or.inr (or.inr (or.inr (by rw [h, reverse_smul]))) },
  { exact or.inr (or.inr (or.inl (by rw [h, reverse_smul, neg_neg]))) },
end

lemma neg_rel : rel ((-1 : units S) • r) s ↔ rel r s :=
begin
  split,
  { exact rel_of_neg_rel r s },
  { exact λ h, rel_of_neg_rel ((-1 : units S) • r) s (by rwa neg_neg) },
end

lemma rel_of_reverse_rel : rel r.reverse s → rel r s :=
begin
  rintro (h | h | h | h),
  { exact or.inr (or.inr (or.inl h)) },
  { exact or.inr (or.inr (or.inr h)) },
  { exact or.inl (h.trans r.reverse_reverse) },
  { exact or.inr (or.inl (h.trans (congr_arg _ r.reverse_reverse))) },
end

lemma reverse_rel : rel r.reverse s ↔ rel r s :=
begin
  split,
  { exact rel_of_reverse_rel r s },
  { exact λ h, rel_of_reverse_rel r.reverse s (by rwa r.reverse_reverse) },
end

@[symm] lemma rel_symm : rel r s → rel s r :=
begin
  rintro (h | h | h | h),
  all_goals { simp only [h, neg_rel, reverse_rel] },
end

@[trans] lemma rel_trans : rel q r → rel r s → rel q s :=
begin
  rintros (h | h | h | h),
  all_goals { simp only [h, neg_rel, reverse_rel], exact id },
end

lemma rel_comm : rel r s ↔ rel s r := ⟨rel_symm r s, rel_symm s r⟩

lemma rel_neg : rel r ((-1 : units S) • s) ↔ rel r s :=
by rw [rel_comm, neg_rel, rel_comm]

lemma rel_reverse : rel r s.reverse ↔ rel r s :=
by rw [rel_comm, reverse_rel, rel_comm]

lemma unit_rel (r s : trinomial ℤ) (u : units ℤ) : rel (u • r) s ↔ rel r s :=
begin
  cases int.units_eq_one_or u with hu hu,
  { rw [hu, one_smul] },
  { rw [hu, neg_rel] },
end

lemma rel_unit (r s : trinomial ℤ) (u : units ℤ) : rel r (u • s) ↔ rel r s :=
begin
  cases int.units_eq_one_or u with hu hu,
  { rw [hu, one_smul] },
  { rw [hu, rel_neg] },
end

end rel

end main_proof

end trinomial

end polynomial
