/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.polynomial.mirror
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

- `irreducible_of_mirror'`: an irreducibility criterion for unit trinomials
- `irreducible_of_mirror''`: an irreducibility criterion for unit trinomials
- `selmer_irreducible`: the polynomial `X ^ n - X - 1` is irreducible for all `n ≠ 1`

-/

namespace polynomial

/-- bundled trinomial $aX^i + bX^j + cX^k$ -/
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

@[simp] lemma coeff_i : t.to_polynomial.coeff t.i = t.a :=
by rw [to_polynomial, coeff_add, coeff_add, coeff_monomial, coeff_monomial, coeff_monomial,
  if_neg (ne_of_gt t.hij), add_zero, if_neg (ne_of_gt t.hik), add_zero, if_pos rfl]

@[simp] lemma coeff_j : t.to_polynomial.coeff t.j = t.b :=
by rw [to_polynomial, coeff_add, coeff_add, coeff_monomial, coeff_monomial, coeff_monomial,
  if_neg (ne_of_lt t.hij), zero_add, if_neg (ne_of_gt t.hjk), add_zero, if_pos rfl]

@[simp] lemma coeff_k : t.to_polynomial.coeff t.k = t.c :=
by rw [to_polynomial, coeff_add, coeff_add, coeff_monomial, coeff_monomial, coeff_monomial,
  if_neg (ne_of_lt t.hik), zero_add, if_neg (ne_of_lt t.hjk), zero_add, if_pos rfl]

@[simp] lemma eval_one : t.to_polynomial.eval 1 = t.a + t.b + t.c :=
by simp_rw [to_polynomial, eval_add, eval_monomial, one_pow, mul_one]

@[simp] lemma support : t.to_polynomial.support = {t.i, t.j, t.k} :=
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

@[simp] lemma norm2 : t.to_polynomial.norm2 = t.a ^ 2 + t.b ^ 2 + t.c ^ 2 :=
by rw [norm2, support, finset.sum_insert (mt finset.mem_insert.mp (not_or (ne_of_lt t.hij)
  (mt finset.mem_singleton.mp (ne_of_lt t.hik)))), finset.sum_insert (mt finset.mem_singleton.mp
  (ne_of_lt t.hjk)), finset.sum_singleton, t.coeff_i, t.coeff_j, t.coeff_k, add_assoc]

@[simp] lemma card_support : t.to_polynomial.support.card = 3 :=
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

@[simp] lemma to_polynomial_of_polynomial : of_polynomial t.card_support = t :=
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

@[simp] lemma to_polynomial_inj {s t : trinomial R} :
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

@[simp] lemma nat_degree : t.to_polynomial.nat_degree = t.k :=
congr_arg k t.to_polynomial_of_polynomial

@[simp] lemma leading_coeff : t.to_polynomial.leading_coeff = t.c :=
congr_arg c t.to_polynomial_of_polynomial

@[simp] lemma nat_trailing_degree : t.to_polynomial.nat_trailing_degree = t.i :=
begin
  simp_rw [nat_trailing_degree_eq_support_min' t.ne_zero, t.support],
  rw [finset.min'_insert, finset.min'_insert, finset.min'_singleton],
  rw [min_eq_right (le_of_lt t.hjk), min_eq_right (le_of_lt t.hij)],
end

@[simp] lemma trailing_coeff : t.to_polynomial.trailing_coeff = t.a :=
by rw [trailing_coeff, nat_trailing_degree, to_polynomial, coeff_add, coeff_add,
  coeff_monomial, coeff_monomial, coeff_monomial,
  if_pos rfl, if_neg (ne_of_gt t.hik), if_neg (ne_of_gt t.hij), add_zero, add_zero]

end trinomial

end polynomial
