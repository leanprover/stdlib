/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.polynomial.reverse2
import analysis.complex.polynomial
import ring_theory.polynomial.gauss_lemma

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

lemma monomial_add_monomial_eq_monomial_add_monomial_iff {R : Type*} [ring R]
  {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) {i j k l : ℕ} :
  (monomial i a) + (monomial j b) = (monomial k a) + (monomial l b) ↔
  ((i = k ∧ j = l) ∨ (a = b ∧ i = l ∧ j = k) ∨ (a + b = 0 ∧ i = j ∧ k = l)) :=
begin
  split,
  { intro h,
    by_cases hjl : j = l,
    { exact or.inl ⟨by rwa [hjl, add_left_inj, monomial_left_inj ha] at h, hjl⟩ },
    { have key := congr_arg (λ x : polynomial R, x.coeff l) h,
      simp_rw [coeff_add, coeff_monomial, if_pos rfl, if_neg hjl, add_zero] at key,
      by_cases hil : i = l,
      { by_cases hkl : k = l,
        { rw [if_pos hil, if_pos hkl, self_eq_add_right] at key,
          exact false.elim (hb key) },
        { rw [if_pos hil, if_neg hkl, zero_add] at key,
          rw [key, hil, add_comm, add_left_inj, monomial_left_inj hb] at h,
          exact or.inr (or.inl ⟨key, hil, h⟩) } },
      { by_cases hkl : k = l,
        { rw [if_neg hil, if_pos hkl, eq_comm] at key,
          rw [hkl, ←monomial_add, key, monomial_zero_right, add_eq_zero_iff_eq_neg,
              ←monomial_neg, ←add_eq_zero_iff_eq_neg.mp key, monomial_left_inj ha] at h,
          exact or.inr (or.inr ⟨key, h, hkl⟩) },
        { rw [if_neg hil, if_neg hkl, zero_add, eq_comm] at key,
          exact false.elim (hb key) } } } },
  { rintros (⟨hik, hkl⟩ | ⟨hab, hil, hjk⟩ | ⟨hab, hij, hkl⟩),
    { rw [hik, hkl] },
    { rw [hab, hil, hjk, add_comm] },
    { rw [hij, hkl, ←monomial_add, ←monomial_add, hab,
          monomial_zero_right, monomial_zero_right] } },
end

lemma mul_reverse'_filter {R : Type*} [integral_domain R] (p : trinomial R) :
  (p.to_polynomial * p.to_polynomial.reverse').filter (set.Ioo (p.k + p.i) (p.k + p.k)) =
    (monomial (p.k + (p.k + p.i - p.j)) (p.b * p.c)) + (monomial (p.k + p.j) (p.b * p.a)) :=
begin
  rw [←reverse_to_polynomial, reverse, to_polynomial, to_polynomial],
  simp_rw [mul_add, add_mul, monomial_mul_monomial, monomial_def, finsupp.filter_add, ←add_assoc],
  rw [mul_comm p.c p.b, add_comm p.i p.k, add_comm p.j p.k, add_comm p.i (p.k + p.i - p.j)],
  rw [finsupp.filter_single_of_neg, finsupp.filter_single_of_neg, finsupp.filter_single_of_neg,
      finsupp.filter_single_of_neg, finsupp.filter_single_of_neg, finsupp.filter_single_of_pos,
      finsupp.filter_single_of_neg, finsupp.filter_single_of_pos, finsupp.filter_single_of_neg],
  simp_rw [zero_add, add_zero],
  { exact not_and_of_not_right _ (lt_irrefl _) },
  { exact ⟨add_lt_add_left p.hij p.k, add_lt_add_left p.hjk p.k⟩ },
  { exact not_and_of_not_left _ (lt_irrefl _) },
  { exact ⟨add_lt_add_left (nat.lt_sub_left_iff_add_lt.mpr (add_lt_add_right p.hjk p.i)) p.k,
      add_lt_add_left ((nat.sub_lt_right_iff_lt_add ((le_of_lt p.hjk).trans
      (nat.le_add_right _ _))).mpr (add_lt_add_left p.hij p.k)) p.k⟩ },
  { exact not_and_of_not_left _ (not_lt_of_le (le_of_eq
      (nat.add_sub_cancel' ((le_of_lt p.hjk).trans (nat.le_add_right _ _))))) },
  { exact not_and_of_not_left _ (not_lt_of_le (add_le_add_right
      (nat.sub_le_right_iff_le_add.mpr (add_le_add_left (le_of_lt p.hij) _)) _)) },
  { exact not_and_of_not_left _ (lt_irrefl _) },
  { exact not_and_of_not_left _ (not_lt_of_gt (add_lt_add_right p.hjk p.i)) },
  { exact not_and_of_not_left _ (not_lt_of_gt (add_lt_add_right p.hik p.i)) },
end

lemma key_lemma_aux2 {R : Type*} [integral_domain R] (p q : trinomial R) (hpqa : p.a = q.a)
  (hpqb : p.b = q.b) (hpqc : p.c = q.c)
  (hpq : p.to_polynomial * p.to_polynomial.reverse' = q.to_polynomial * q.to_polynomial.reverse') :
  rel p q :=
begin
  have hpqi : p.i = q.i,
  { replace hpq := congr_arg polynomial.nat_trailing_degree hpq,
    rw [nat_trailing_degree_mul_reverse', nat_trailing_degree_mul_reverse',
        nat_trailing_degree, nat_trailing_degree] at hpq,
    exact mul_left_cancel' two_ne_zero hpq },
  have hpqk : p.k = q.k,
  { replace hpq := congr_arg polynomial.nat_degree hpq,
    rw [nat_degree_mul_reverse', nat_degree_mul_reverse', nat_degree, nat_degree] at hpq,
    exact mul_left_cancel' two_ne_zero hpq },
  have key : (monomial (p.k + (p.k + p.i - p.j)) (p.b * p.c)) + (monomial (p.k + p.j) (p.b * p.a))
    = (monomial (q.k + (q.k + q.i - q.j)) (q.b * q.c)) + (monomial (q.k + q.j) (q.b * q.a)),
  { rw [←mul_reverse'_filter, ←mul_reverse'_filter, hpq, hpqi, hpqk] },
  rw [hpqa, hpqb, hpqc, hpqi, hpqk, monomial_add_monomial_eq_monomial_add_monomial_iff
      (mul_ne_zero q.hb q.hc) (mul_ne_zero q.hb q.ha)] at key,
  simp_rw add_right_inj at key,
  rcases key with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩),
  { exact or.inl (ext hpqa hpqb hpqc hpqi h2 hpqk).symm },
  { rw [mul_right_inj' q.hb] at h1,
    rw [add_comm, ←hpqi, ←hpqk] at h2,
    exact or.inr (or.inr (or.inl (eq.symm
      (ext (hpqc.trans h1) hpqb (hpqa.trans h1.symm) hpqi h2 hpqk)))) },
  { rw [nat.sub_eq_iff_eq_add ((le_of_lt q.hjk).trans (nat.le_add_right _ _)), ←two_mul] at h3,
    rw [nat.sub_eq_iff_eq_add, ←two_mul, h3, nat.mul_right_inj zero_lt_two, eq_comm] at h2,
    exact or.inl (ext hpqa hpqb hpqc hpqi h2 hpqk).symm,
    exact (le_of_lt p.hjk).trans ((le_of_eq hpqk).trans (nat.le_add_right _ _)) },
end

/- I don't expect anyone to want to use this lemma in positive characteristic, but this lemma
  does generalize to odd characteristic (with the same proof) -/
lemma key_lemma_aux1 {R : Type*} [integral_domain R] [char_zero R]
  (p q : trinomial R) (hpqa : p.a = q.a)
  (hpq : p.to_polynomial * p.to_polynomial.reverse' = q.to_polynomial * q.to_polynomial.reverse') :
  rel p q :=
begin
  have hpqc : p.c = q.c,
  { replace hpq := congr_arg polynomial.leading_coeff hpq,
    simp_rw [leading_coeff_mul, reverse'_leading_coeff, leading_coeff, trailing_coeff] at hpq,
    rwa [hpqa, mul_eq_mul_right_iff, or_iff_not_imp_right, imp_iff_right q.ha] at hpq },
  have key1 : p.to_polynomial.norm2 = q.to_polynomial.norm2,
  { rw [←central_coeff_mul_reverse', hpq, central_coeff_mul_reverse'] },
  rw [p.norm2, q.norm2, hpqa, hpqc, add_left_inj, add_right_inj] at key1,
  cases eq_or_eq_neg_of_pow_two_eq_pow_two _ _ key1 with hpqb hpqb,
  { exact key_lemma_aux2 p q hpqa hpqb hpqc hpq },
  have key2 := congr_arg (eval 1) hpq,
  rw [eval_mul, eval_mul, reverse'_eval_one, reverse'_eval_one, ←pow_two, ←pow_two,
    p.eval_one, q.eval_one, hpqa, hpqc] at key2,
  cases eq_or_eq_neg_of_pow_two_eq_pow_two _ _ key2 with hpqb hqac,
  { rw [add_left_inj, add_right_inj] at hpqb,
    exact key_lemma_aux2 p q hpqa hpqb hpqc hpq },
  { rw [add_comm q.a, add_comm q.a, add_assoc, add_assoc, neg_add, hpqb, add_right_inj,
        eq_neg_iff_add_eq_zero, add_self_eq_zero] at hqac,
    rw [←rel_reverse, ←rel_neg],
    apply key_lemma_aux2,
    { exact hpqa.trans ((add_eq_zero_iff_eq_neg.mp hqac).trans (neg_one_mul q.c).symm) },
    { exact hpqb.trans (neg_one_mul q.b).symm },
    { exact hpqc.trans ((neg_one_mul q.a).trans (add_eq_zero_iff_neg_eq.mp hqac)).symm },
    { rw [neg_to_polynomial, reverse'_neg, neg_mul_neg, reverse_to_polynomial, reverse'_reverse',
          hpq, mul_comm] } },
end

lemma key_lemma {p q : trinomial ℤ}
  (hp : is_unit (p.a * p.c) ∨ irreducible (p.a * p.c))
  (hpq : p.to_polynomial * p.to_polynomial.reverse' = q.to_polynomial * q.to_polynomial.reverse') :
  rel p q :=
begin
  have h := @algebra.smul_mul_smul _ _ _ _ (@polynomial.algebra_of_algebra ℤ ℤ _ _ (algebra.id ℤ)),
  have hp' : ∀ x y, p.a * p.c = x * y → is_unit x ∨ is_unit y := or.elim hp (λ h1 x y h2, or.inl
    (is_unit_of_mul_is_unit_left ((congr_arg is_unit h2).mp h1))) irreducible.is_unit_or_is_unit,
  have key : p.a * p.c = q.a * q.c,
  { replace hpq := congr_arg polynomial.leading_coeff hpq,
    simp_rw [leading_coeff_mul, reverse'_leading_coeff, leading_coeff, trailing_coeff] at hpq,
    rwa [mul_comm p.a p.c, mul_comm q.a q.c] },
  rcases (hp' p.a p.c rfl) with ⟨u1, hu1⟩ | ⟨u1, hu1⟩,
  { rcases (hp' q.a q.c key) with ⟨u2, hu2⟩ | ⟨u2, hu2⟩,
    { have key' := key_lemma_aux1 (u1 • p.reverse) (u2 • q.reverse)
        (by rwa [←hu1, ←hu2] at key)
        (by simp_rw [smul_to_polynomial, reverse_to_polynomial, reverse'_smul, reverse'_reverse',
          h, int.units_coe_mul_self, mul_comm, hpq]),
      rwa [unit_rel, rel_unit, reverse_rel, rel_reverse] at key' },
    { have key' := key_lemma_aux1 (u1 • p.reverse) (u2 • q)
        (by rwa [←hu1, ←hu2, mul_comm q.a] at key)
        (by simp_rw [smul_to_polynomial, reverse_to_polynomial, reverse'_smul, reverse'_reverse',
          h, int.units_coe_mul_self, mul_comm, hpq]),
      rwa [unit_rel, rel_unit, reverse_rel] at key' } },
  { rcases (hp' q.a q.c key) with ⟨u2, hu2⟩ | ⟨u2, hu2⟩,
    { have key' := key_lemma_aux1 (u1 • p) (u2 • q.reverse)
        (by rwa [←hu1, ←hu2, mul_comm p.a] at key)
        (by simp_rw [smul_to_polynomial, reverse_to_polynomial, reverse'_smul, reverse'_reverse',
          h, int.units_coe_mul_self, mul_comm, hpq]),
      rwa [unit_rel, rel_unit, rel_reverse] at key' },
    { have key' := key_lemma_aux1 (u1 • p) (u2 • q)
        (by rwa [←hu1, ←hu2, mul_comm p.a, mul_comm q.a] at key)
        (by simp_rw [smul_to_polynomial, reverse'_smul,
          h, int.units_coe_mul_self, hpq]),
      rwa [unit_rel, rel_unit] at key' } },
end

lemma reverse'_irreducible_test' {f : polynomial ℤ}
  (h1 : f.norm2 = 3)
  (h2 : ∀ g, g ∣ f → g ∣ f.reverse' → is_unit g) : irreducible f :=
begin
  obtain ⟨t, rfl⟩ := support_card_eq_three_iff.mp
    (f.card_support_eq_three_of_norm2_eq_three h1),
  refine reverse'_irreducible_test (λ h3, _) _ h2,
  { obtain ⟨r, ⟨u, rfl⟩, h4⟩ := is_unit_iff.mp h3,
    rw [←h4, norm2_C, ←units.coe_pow, int.units_pow_two, units.coe_one] at h1,
    exact ne_of_lt (int.add_lt_add zero_lt_one one_lt_two) h1 },
  { intros g hg,
    have hg' : g.norm2 = 3,
    { rwa [←central_coeff_mul_reverse', ←hg, central_coeff_mul_reverse'] },
    obtain ⟨s, rfl⟩ := support_card_eq_three_iff.mp
      (g.card_support_eq_three_of_norm2_eq_three hg'),
    simp_rw [←reverse_to_polynomial, ←neg_to_polynomial, to_polynomial_inj],
    refine rel_symm s t (key_lemma _ hg.symm),
    apply or.inl,
    have key1 := s.to_polynomial.coeff_sq_eq_one_of_norm2_le_three (le_of_eq hg') s.i,
    have key2 := s.to_polynomial.coeff_sq_eq_one_of_norm2_le_three (le_of_eq hg') s.k,
    rw [s.coeff_i, pow_two] at key1,
    rw [s.coeff_k, pow_two] at key2,
    exact is_unit.mul (is_unit_of_mul_eq_one s.a s.a (key1 s.ha))
      (is_unit_of_mul_eq_one s.c s.c (key2 s.hc)) },
end

lemma reverse'_irreducible_test'' {f : polynomial ℤ}
  (h1 : f.norm2 = 3)
  (h2 : ∀ z : ℂ, ¬ (aeval z f = 0 ∧ aeval z f.reverse' = 0)) : irreducible f :=
begin
  have hf : f ≠ 0,
  { rw [ne, ←norm2_eq_zero, h1],
    exact int.bit1_ne_zero 1 },
  apply reverse'_irreducible_test' h1,
  intros g hg1 hg2,
  suffices : ¬ (0 < g.nat_degree),
  { rw [not_lt, nat.le_zero_iff] at this,
    rw [eq_C_of_nat_degree_eq_zero this, is_unit_C, ←this],
    cases hg1 with h fgh,
    apply @is_unit_of_mul_is_unit_left _ _ g.leading_coeff h.leading_coeff,
    rw [←leading_coeff_mul, ←fgh],
    exact is_unit_of_pow_eq_one _ _ (f.coeff_sq_eq_one_of_norm2_le_three
      (le_of_eq h1) f.nat_degree (mt leading_coeff_eq_zero.mp hf)) zero_lt_two },
  intro h,
  have inj : function.injective (algebra_map ℤ ℂ) := int.cast_injective,
  rw [nat_degree_pos_iff_degree_pos, ←degree_map' inj] at h,
  cases complex.exists_root h with z hz,
  apply h2 z,
  rw [is_root, eval_map, ←aeval_def] at hz,
  split,
  { cases hg1 with g' hg',
    rw [hg', aeval_mul, hz, zero_mul] },
  { cases hg2 with g' hg',
    rw [hg', aeval_mul, hz, zero_mul] },
end

lemma selmer_coprime_lemma (n : ℕ) (z : ℂ) : ¬ (z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) :=
begin
  rintros ⟨h1, h2⟩,
  rw h1 at h2,
  have h3 : (z - 1) * (z + 1 + z ^ 2) = 0,
  { rw [h2, mul_zero] },
  replace h3 : z ^ 3 = 1,
  { rw [←sub_eq_zero, ←h3],
    ring },
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2,
  { rw [←nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one],
    have : n % 3 < 3 := nat.mod_lt n zero_lt_three,
    interval_cases n % 3,
    all_goals { rw h },
    { exact or.inl (pow_zero z) },
    { exact or.inr (or.inl (pow_one z)) },
    { exact or.inr (or.inr rfl) } },
  have z_ne_zero : z ≠ 0,
  { intro h,
    rw [h, zero_pow (zero_lt_three)] at h3,
    exact zero_ne_one h3 },
  rcases key with key | key | key,
  { rw [key, self_eq_add_left] at h1,
    exact z_ne_zero h1 },
  { rw [key, self_eq_add_right] at h1,
    exact one_ne_zero h1 },
  { rw [←key, h1, add_self_eq_zero, ←h1] at h2,
    exact z_ne_zero (pow_eq_zero h2) },
end

lemma selmer_irreducible {n : ℕ} (hn1 : n ≠ 1) : irreducible (X ^ n - X - 1 : polynomial ℤ) :=
begin
  by_cases hn0 : n = 0,
  { rw [hn0, pow_zero, sub_sub, add_comm, ←sub_sub, sub_self, zero_sub],
    exact irreducible_of_associated ⟨-1, mul_neg_one X⟩ irreducible_X },
  have hn : 1 < n := nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩,
  let p := mk (-(1 : ℤ)) (-(1 : ℤ)) (1 : ℤ) (neg_ne_zero.mpr one_ne_zero)
    (neg_ne_zero.mpr one_ne_zero) (one_ne_zero) 0 1 n zero_lt_one hn,
  have h1 : p.to_polynomial = X ^ n - X - 1,
  { simp_rw [to_polynomial, ←C_mul_X_pow_eq_monomial, C_neg, C_1],
    ring },
  have h2 : p.to_polynomial.reverse' = 1 - X ^ (n - 1) - X ^ n,
  { simp_rw [←reverse_to_polynomial, reverse, to_polynomial, ←C_mul_X_pow_eq_monomial,
      C_neg, C_1, nat.zero_add],
    ring },
  rw ← h1,
  apply reverse'_irreducible_test'' (by { rw p.norm2, norm_num }),
  rw [h2, h1],
  rintros z ⟨hz1, hz2⟩,
  rw [alg_hom.map_sub, alg_hom.map_sub, alg_hom.map_pow, aeval_X, aeval_one,
      sub_sub, sub_eq_zero] at hz1,
  rw [alg_hom.map_sub, alg_hom.map_sub, alg_hom.map_pow, alg_hom.map_pow,
      aeval_X, aeval_one, sub_sub, sub_eq_zero, hz1, ←add_assoc, self_eq_add_left] at hz2,
  replace hz2 : z ^ n + z ^ 2 = 0,
  { rw [←nat.sub_add_cancel (le_of_lt hn), pow_succ, pow_two, ←mul_add, hz2, mul_zero] },
  exact selmer_coprime_lemma n z ⟨hz1, hz2⟩,
end

lemma selmer_irreducible' {n : ℕ} (hn1 : n ≠ 1) : irreducible (X ^ n - X - 1 : polynomial ℚ) :=
begin
  by_cases hn0 : n = 0,
  { rw [hn0, pow_zero, sub_sub, add_comm, ←sub_sub, sub_self, zero_sub],
    exact irreducible_of_associated ⟨-1, mul_neg_one X⟩ irreducible_X },
  have hn : 1 < n := nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩,
  let p := mk (-(1 : ℤ)) (-(1 : ℤ)) (1 : ℤ) (neg_ne_zero.mpr one_ne_zero)
    (neg_ne_zero.mpr one_ne_zero) (one_ne_zero) 0 1 n zero_lt_one hn,
  have hp : p.to_polynomial = X ^ n - X - 1,
  { simp_rw [to_polynomial, ←C_mul_X_pow_eq_monomial, C_neg, C_1],
    ring },
  have h := (is_primitive.int.irreducible_iff_irreducible_map_cast _).mp (selmer_irreducible hn1),
  { rwa [map_sub, map_sub, map_pow, map_one, map_X] at h },
  { rw ← hp,
    exact monic.is_primitive p.leading_coeff },
end

end main_proof

end trinomial

end polynomial
