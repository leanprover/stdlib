/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import field_theory.splitting_field
import ring_theory.roots_of_unity
import algebra.polynomial.big_operators
import number_theory.arithmetic_function
import data.polynomial.lifts
import analysis.complex.roots_of_unity
import field_theory.separable

/-!
# Cyclotomic polynomials.

For `n : ℕ` and an integral domain `R`, we define a modified version of the `n`-th cyclotomic
polynomial with coefficients in `R`, denoted `cyclotomic' n R`, as `∏ (X - μ)`, where `μ` varies
over the primitive `n`th roots of unity. If there is a primitive `n`th root of unity in `R` then
this the standard definition. We then define the standard cyclotomic polynomial `cyclotomic n R`
with coefficients in any ring `R`.

## Main definition

* `cyclotomic n R` : the `n`-th cyclotomic polynomial with coefficients in `R`.

## Main results

* `int_coeff_of_cycl` : If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K`
comes from a polynomial with integer coefficients.
* `deg_of_cyclotomic` : The degree of `cyclotomic n` is `totient n`.
* `prod_cyclotomic_eq_X_pow_sub_one` : `X ^ n - 1 = ∏ (cyclotomic i)`, where `i` divides `n`.
* `cyclotomic_eq_prod_X_pow_sub_one_pow_moebius` : The Möbius inversion formula for
  `cyclotomic n R` over an abstract fraction field for `polynomial R`.
* `cyclotomic.irreducible` : `cyclotomic n ℤ` is irreducible.

## Implementation details

Our definition of `cyclotomic' n R` makes sense in any integral domain `R`, but the interesting
results hold if there is a primitive `n`-th root of unity in `R`. In particular, our definition is
not the standard one unless there is a primitive `n`th root of unity in `R`. For example,
`cyclotomic' 3 ℤ = 1`, since there are no primitive cube roots of unity in `ℤ`. The main example is
`R = ℂ`, we decided to work in general since the difficulties are essentially the same.
To get the standard cyclotomic polynomials, we use `int_coeff_of_cycl`, with `R = ℂ`, to get a
polynomial with integer coefficients and then we map it to `polynomial R`, for any ring `R`.
To prove `cyclotomic.irreducible`, the irreducibility of `cyclotomic n ℤ`, we show in
`minpoly_primitive_root_eq_cyclotomic` that `cyclotomic n ℤ` is the minimal polynomial of
any `n`-th primitive root of unity `μ : K`, where `K` is a field of characteristic `0`.
-/

open_locale classical big_operators
noncomputable theory

universe u

namespace polynomial

section cyclotomic'

section integral_domain

variables {R : Type*} [integral_domain R]

/-- The modified `n`-th cyclotomic polynomial with coefficients in `R`, it is the usual cyclotomic
polynomial if there is a primitive `n`-th root of unity in `R`. -/
def cyclotomic' (n : ℕ) (R : Type*) [integral_domain R] : polynomial R :=
∏ μ in primitive_roots n R, (X - C μ)

/-- The zeroth modified cyclotomic polyomial is `1`. -/
@[simp] lemma cyclotomic'_zero (R : Type*) [integral_domain R] : cyclotomic' 0 R = 1 :=
by simp only [cyclotomic', finset.prod_empty, is_primitive_root.primitive_roots_zero]

/-- The first modified cyclotomic polyomial is `X - 1`. -/
@[simp] lemma cyclotomic'_one (R : Type*) [integral_domain R] : cyclotomic' 1 R = X - 1 :=
begin
  simp only [cyclotomic', finset.prod_singleton, ring_hom.map_one,
  is_primitive_root.primitive_roots_one]
end

/-- The second modified cyclotomic polyomial is `X + 1` if the characteristic of `R` is not `2`. -/
@[simp] lemma cyclotomic'_two (R : Type*) [integral_domain R] (p : ℕ) [char_p R p] (hp : p ≠ 2) :
  cyclotomic' 2 R = X + 1 :=
begin
  rw [cyclotomic'],
  have prim_root_two : primitive_roots 2 R = {(-1 : R)},
  { apply finset.eq_singleton_iff_unique_mem.2,
    split,
    { simp only [is_primitive_root.neg_one p hp, nat.succ_pos', mem_primitive_roots] },
    { intros x hx,
      rw [mem_primitive_roots zero_lt_two] at hx,
      exact is_primitive_root.eq_neg_one_of_two_right hx } },
  simp only [prim_root_two, finset.prod_singleton, ring_hom.map_neg, ring_hom.map_one,
  sub_neg_eq_add]
end

/-- `cyclotomic' n R` is monic. -/
lemma cyclotomic'.monic (n : ℕ) (R : Type*) [integral_domain R] : (cyclotomic' n R).monic :=
monic_prod_of_monic _ _ $ λ z hz, monic_X_sub_C _

/-- `cyclotomic' n R` is different from `0`. -/
lemma cyclotomic'_ne_zero (n : ℕ) (R : Type*) [integral_domain R] : cyclotomic' n R ≠ 0 :=
(cyclotomic'.monic n R).ne_zero

/-- The natural degree of `cyclotomic' n R` is `totient n` if there is a primitive root of
unity in `R`. -/
lemma nat_degree_cyclotomic' {ζ : R} {n : ℕ} (h : is_primitive_root ζ n) :
  (cyclotomic' n R).nat_degree = nat.totient n :=
begin
  cases nat.eq_zero_or_pos n with hzero hpos,
  { simp only [hzero, cyclotomic'_zero, nat.totient_zero, nat_degree_one] },
  rw [cyclotomic'],
  rw nat_degree_prod (primitive_roots n R) (λ (z : R), (X - C z)),
  simp only [is_primitive_root.card_primitive_roots h hpos, mul_one,
  nat_degree_X_sub_C,
  nat.cast_id, finset.sum_const, nsmul_eq_mul],
  intros z hz,
  exact X_sub_C_ne_zero z
end

/-- The degree of `cyclotomic' n R` is `totient n` if there is a primitive root of unity in `R`. -/
lemma degree_cyclotomic' {ζ : R} {n : ℕ} (h : is_primitive_root ζ n) :
  (cyclotomic' n R).degree = nat.totient n :=
by simp only [degree_eq_nat_degree (cyclotomic'_ne_zero n R), nat_degree_cyclotomic' h]

/-- The roots of `cyclotomic' n R` are the primitive `n`-th roots of unity. -/
lemma roots_of_cyclotomic (n : ℕ) (R : Type*) [integral_domain R] :
  (cyclotomic' n R).roots = (primitive_roots n R).val :=
by { rw cyclotomic', exact roots_prod_X_sub_C (primitive_roots n R) }

end integral_domain

section field

variables {K : Type*} [field K]

/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n - 1 = ∏ (X - μ)`, where `μ`
varies over the `n`-th roots of unity. -/
lemma X_pow_sub_one_eq_prod {ζ : K} {n : ℕ} (hpos : 0 < n) (h : is_primitive_root ζ n) :
  X ^ n - 1 = ∏ ζ in nth_roots_finset n K, (X - C ζ) :=
begin
  rw [nth_roots_finset, ← multiset.to_finset_eq (is_primitive_root.nth_roots_nodup h)],
  simp only [finset.prod_mk, ring_hom.map_one],
  rw [nth_roots],
  have hmonic : (X ^ n - C (1 : K)).monic := monic_X_pow_sub_C (1 : K) (ne_of_lt hpos).symm,
  symmetry,
  apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic,
  rw [@nat_degree_X_pow_sub_C K _ _ n 1, ← nth_roots],
  exact is_primitive_root.card_nth_roots h
end

/-- `cyclotomic' n K` splits. -/
lemma cyclotomic'_splits (n : ℕ) : splits (ring_hom.id K) (cyclotomic' n K) :=
begin
  apply splits_prod (ring_hom.id K),
  intros z hz,
  simp only [splits_X_sub_C (ring_hom.id K)]
end

/-- If there is a primitive `n`-th root of unity in `K`, then `X ^ n - 1`splits. -/
lemma X_pow_sub_one_splits {ζ : K} {n : ℕ} (h : is_primitive_root ζ n) :
  splits (ring_hom.id K) (X ^ n - C (1 : K)) :=
begin
  by_cases hzero : n = 0,
  { simp only [hzero, ring_hom.map_one, splits_zero, pow_zero, sub_self] },
  rw [splits_iff_card_roots, ← nth_roots, is_primitive_root.card_nth_roots h,
    nat_degree_X_pow_sub_C],
end

/-- If there is a primitive `n`-th root of unity in `K`, then
`∏ i in nat.divisors n, cyclotomic' i K = X ^ n - 1`. -/
lemma prod_cyclotomic'_eq_X_pow_sub_one {ζ : K} {n : ℕ} (hpos : 0 < n) (h : is_primitive_root ζ n) :
  ∏ i in nat.divisors n, cyclotomic' i K = X ^ n - 1 :=
begin
  rw [X_pow_sub_one_eq_prod hpos h],
  have rwcyc : ∀ i ∈ nat.divisors n, cyclotomic' i K = ∏ μ in primitive_roots i K, (X - C μ),
  { intros i hi,
    simp only [cyclotomic'] },
  conv_lhs { apply_congr,
             skip,
             simp [rwcyc, H] },
  rw ← finset.prod_bUnion,
  { simp only [is_primitive_root.nth_roots_one_eq_bUnion_primitive_roots hpos h] },
  intros x hx y hy hdiff,
  simp only [nat.mem_divisors, and_true, ne.def, pnat.ne_zero, not_false_iff] at hx hy,
  refine is_primitive_root.disjoint _ _ hdiff,
  { exact @nat.pos_of_mem_divisors n x (nat.mem_divisors.2 hx) },
  { exact @nat.pos_of_mem_divisors n y (nat.mem_divisors.2 hy) }
end

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic' n K = (X ^ k - 1) /ₘ (∏ i in nat.proper_divisors k, cyclotomic' i K)`. -/
lemma cyclotomic'_eq_X_pow_sub_one_div {ζ : K} {n : ℕ} (hpos: 0 < n) (h : is_primitive_root ζ n) :
  cyclotomic' n K = (X ^ n - 1) /ₘ (∏ i in nat.proper_divisors n, cyclotomic' i K) :=
begin
  rw [←prod_cyclotomic'_eq_X_pow_sub_one hpos h,
  nat.divisors_eq_proper_divisors_insert_self_of_pos hpos,
  finset.prod_insert nat.proper_divisors.not_self_mem],
  have prod_monic : (∏ i in nat.proper_divisors n, cyclotomic' i K).monic,
  { apply monic_prod_of_monic,
    intros i hi,
    exact cyclotomic'.monic i K },
  rw (div_mod_by_monic_unique (cyclotomic' n K) 0 prod_monic _).1,
  simp only [degree_zero, zero_add],
  split,
  { rw mul_comm },
  rw [bot_lt_iff_ne_bot],
  intro h,
  exact monic.ne_zero prod_monic (degree_eq_bot.1 h)
end

/-- If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K` comes from a
polynomial with integer coefficients. -/
lemma int_coeff_of_cyclotomic {ζ : K} {n : ℕ} (h : is_primitive_root ζ n) :
  (∃ (P : polynomial ℤ), map (int.cast_ring_hom K) P = cyclotomic' n K ∧
  P.degree = (cyclotomic' n K).degree ∧ P.monic) :=
begin
  refine lifts_and_degree_eq_and_monic _ (cyclotomic'.monic n K),
  revert h ζ,
  apply nat.strong_induction_on n,
  intros k hk z hzeta,
  cases nat.eq_zero_or_pos k with hzero hpos,
  { use 1,
    simp only [hzero, cyclotomic'_zero, set.mem_univ, subsemiring.coe_top, eq_self_iff_true,
    map_one, ring_hom.coe_of, and_self], },
  by_cases hone : k = 1,
  { use X - 1,
    simp only [hone, cyclotomic'_one K, set.mem_univ, pnat.one_coe, subsemiring.coe_top,
    eq_self_iff_true, map_X, map_one, ring_hom.coe_of, and_self, map_sub] },
  let B : polynomial K := ∏ i in nat.proper_divisors k, cyclotomic' i K,
  have Bmo : B.monic,
  { apply monic_prod_of_monic,
    intros i hi,
    exact (cyclotomic'.monic i K) },
  have Bint : B ∈ lifts (int.cast_ring_hom K),
  { refine subsemiring.prod_mem (lifts (int.cast_ring_hom K)) _,
    intros x hx,
    have xsmall := (nat.mem_proper_divisors.1 hx).2,
    obtain ⟨d, hd⟩ := (nat.mem_proper_divisors.1 hx).1,
    rw [mul_comm] at hd,
  exact hk x xsmall (is_primitive_root.pow hpos hzeta hd) },
  replace Bint := lifts_and_degree_eq_and_monic Bint Bmo,
  obtain ⟨B₁, hB₁, hB₁deg, hB₁mo⟩ := Bint,
  let Q₁ : polynomial ℤ := (X ^ k - 1) /ₘ B₁,
  have huniq : 0 + B * cyclotomic' k K = X ^ k - 1 ∧ (0 : polynomial K).degree < B.degree,
  { split,
    { rw [zero_add, mul_comm, ←(prod_cyclotomic'_eq_X_pow_sub_one hpos hzeta),
      nat.divisors_eq_proper_divisors_insert_self_of_pos hpos],
      simp only [true_and, finset.prod_insert, not_lt, nat.mem_proper_divisors, dvd_refl] },
    rw [degree_zero, bot_lt_iff_ne_bot],
    intro habs,
    exact (monic.ne_zero Bmo) (degree_eq_bot.1 habs) },
  replace huniq := div_mod_by_monic_unique (cyclotomic' k K) (0 : polynomial K) Bmo huniq,
  simp only [lifts, ring_hom.coe_of, ring_hom.mem_srange],
  use Q₁,
  rw [(map_div_by_monic (int.cast_ring_hom K) hB₁mo), hB₁, ← huniq.1],
  simp
end

/-- If `K` is of characteristic `0` and there is a primitive `n`-th root of unity in `K`,
then `cyclotomic n K` comes from a unique polynomial with integer coefficients. -/
lemma unique_int_coeff_of_cycl [char_zero K] {ζ : K} {n : ℕ+} (h : is_primitive_root ζ n) :
  (∃! (P : polynomial ℤ), map (int.cast_ring_hom K) P = cyclotomic' n K) :=
begin
  obtain ⟨P, hP⟩ := int_coeff_of_cyclotomic h,
  rw exists_unique,
  use [P, hP.1],
  intros Q hQ,
  have mapinj : function.injective (map (int.cast_ring_hom K)),
  { apply map_injective,
    simp only [int.cast_injective, int.coe_cast_ring_hom] },
  rw [function.injective] at mapinj,
  apply mapinj,
  rw [hP.1, hQ]
end

end field

end cyclotomic'

section cyclotomic

/-- The `n`-th cyclotomic polynomial with coefficients in `R`. -/
def cyclotomic (n : ℕ) (R : Type*) [ring R] : polynomial R :=
if h : n = 0 then 1 else map (int.cast_ring_hom R) (classical.some (int_coeff_of_cyclotomic
  (complex.is_primitive_root_exp n h)))

lemma int_cyclotomic_rw {n : ℕ} (h : n ≠ 0) :
  cyclotomic n ℤ = (classical.some (int_coeff_of_cyclotomic (complex.is_primitive_root_exp n h))) :=
begin
  simp only [cyclotomic, h, dif_neg, not_false_iff],
  ext i,
  simp only [coeff_map, int.cast_id, ring_hom.eq_int_cast]
end

/-- `cyclotomic n R` comes from `cyclotomic n ℤ`. -/
lemma map_cyclotomic_int (n : ℕ) (R : Type*) [ring R] :
  map (int.cast_ring_hom R) (cyclotomic n ℤ) = cyclotomic n R :=
begin
  by_cases hzero : n = 0,
  { simp only [hzero, cyclotomic, dif_pos, map_one] },
  simp only [cyclotomic, int_cyclotomic_rw, hzero, ne.def, dif_neg, not_false_iff]
end

lemma int_cyclotomic_spec (n : ℕ) : map (int.cast_ring_hom ℂ) (cyclotomic n ℤ) = cyclotomic' n ℂ ∧
  (cyclotomic n ℤ).degree = (cyclotomic' n ℂ).degree ∧ (cyclotomic n ℤ).monic  :=
begin
  by_cases hzero : n = 0,
  { simp only [hzero, cyclotomic, degree_one, monic_one, cyclotomic'_zero, dif_pos,
  eq_self_iff_true, map_one, and_self] },
  rw int_cyclotomic_rw hzero,
  exact classical.some_spec (int_coeff_of_cyclotomic (complex.is_primitive_root_exp n hzero))
end

lemma int_cyclotomic_unique {n : ℕ} {P : polynomial ℤ} (h : map (int.cast_ring_hom ℂ) P =
  cyclotomic' n ℂ) : P = cyclotomic n ℤ :=
begin
  have mapinj : function.injective (map (int.cast_ring_hom ℂ)),
  { apply map_injective,
    simp only [int.cast_injective, int.coe_cast_ring_hom] },
  apply mapinj,
  rw [h, (int_cyclotomic_spec n).1]
end

/-- The definition of `cyclotomic n R` commutes with any ring homomorphism. -/
@[simp] lemma map_cyclotomic (n : ℕ) {R S : Type*} [ring R] [ring S] (f : R →+* S) :
  map f (cyclotomic n R) = cyclotomic n S :=
begin
  rw [←map_cyclotomic_int n R, ←map_cyclotomic_int n S],
  ext i,
  simp only [coeff_map, ring_hom.eq_int_cast, ring_hom.map_int_cast]
end

/-- The zeroth cyclotomic polyomial is `1`. -/
@[simp] lemma cyclotomic_zero (R : Type*) [ring R] : cyclotomic 0 R = 1 :=
by simp only [cyclotomic, dif_pos]

/-- The first cyclotomic polyomial is `X - 1`. -/
@[simp] lemma cyclotomic_one (R : Type*) [ring R] : cyclotomic 1 R = X - 1 :=
begin
  have hspec : map (int.cast_ring_hom ℂ) (X - 1) = cyclotomic' 1 ℂ,
  { simp only [cyclotomic'_one, pnat.one_coe, map_X, map_one, map_sub] },
  symmetry,
  rw [←map_cyclotomic_int, ←(int_cyclotomic_unique hspec)],
  simp only [map_X, map_one, map_sub]
end

/-- The second cyclotomic polyomial is `X + 1`. -/
@[simp] lemma cyclotomic_two (R : Type*) [ring R] : cyclotomic 2 R = X + 1 :=
begin
  have hspec : map (int.cast_ring_hom ℂ) (X + 1) = cyclotomic' 2 ℂ,
  { simp only [cyclotomic'_two ℂ 0 two_ne_zero.symm, map_add, map_X, map_one] },
  symmetry,
  rw [←map_cyclotomic_int, ←(int_cyclotomic_unique hspec)],
  simp only [map_add, map_X, map_one]
end

/-- `cyclotomic n` is monic. -/
lemma cyclotomic.monic (n : ℕ) (R : Type*) [ring R] : (cyclotomic n R).monic :=
begin
  rw ←map_cyclotomic_int,
  apply monic_map,
  exact (int_cyclotomic_spec n).2.2
end

/-- `cyclotomic n R` is different from `0`. -/
lemma cyclotomic_ne_zero (n : ℕ) (R : Type*) [ring R] [nontrivial R] : cyclotomic n R ≠ 0 :=
monic.ne_zero (cyclotomic.monic n R)

/-- The degree of `cyclotomic n` is `totient n`. -/
lemma degree_cyclotomic (n : ℕ) (R : Type*) [ring R] [nontrivial R] :
  (cyclotomic n R).degree = nat.totient n :=
begin
  rw ←map_cyclotomic_int,
  rw degree_map_eq_of_leading_coeff_ne_zero (int.cast_ring_hom R) _,
  { cases n with k,
    { simp only [cyclotomic, degree_one, dif_pos, nat.totient_zero, with_top.coe_zero]},
    rw [←degree_cyclotomic' (complex.is_primitive_root_exp k.succ (nat.succ_ne_zero k))],
    exact (int_cyclotomic_spec k.succ).2.1 },
  simp only [(int_cyclotomic_spec n).right.right, ring_hom.eq_int_cast, monic.leading_coeff,
  int.cast_one, ne.def, not_false_iff, one_ne_zero]
end

/-- The natural degree of `cyclotomic n` is `totient n`. -/
lemma nat_degree_cyclotomic (n : ℕ) (R : Type*) [ring R] [nontrivial R] :
  (cyclotomic n R).nat_degree = nat.totient n :=
begin
  have hdeg := degree_cyclotomic n R,
  rw degree_eq_nat_degree (cyclotomic_ne_zero n R) at hdeg,
  norm_cast at hdeg,
  exact hdeg
end

/-- The degree of `cyclotomic n R` is positive. -/
lemma degree_cyclotomic_pos (n : ℕ) (R : Type*) (hpos : 0 < n) [ring R] [nontrivial R] :
  0 < (cyclotomic n R).degree := by
{ rw degree_cyclotomic n R; exact_mod_cast (nat.totient_pos hpos) }

/-- `∏ i in nat.divisors n, cyclotomic i R = X ^ n - 1`. -/
lemma prod_cyclotomic_eq_X_pow_sub_one {n : ℕ} (hpos : 0 < n) (R : Type*) [comm_ring R] :
  ∏ i in nat.divisors n, cyclotomic i R = X ^ n - 1 :=
begin
  have integer : ∏ i in nat.divisors n, cyclotomic i ℤ = X ^ n - 1,
  { have mapinj : function.injective (map (int.cast_ring_hom ℂ)),
    { apply map_injective,
      simp only [int.cast_injective, int.coe_cast_ring_hom] },
    apply mapinj,
    rw map_prod (int.cast_ring_hom ℂ) (λ i, cyclotomic i ℤ),
    simp only [int_cyclotomic_spec, map_pow, nat.cast_id, map_X, map_one, ring_hom.coe_of, map_sub],
    exact prod_cyclotomic'_eq_X_pow_sub_one hpos
    (complex.is_primitive_root_exp n (ne_of_lt hpos).symm) },
  have coerc : X ^ n - 1 = map (int.cast_ring_hom R) (X ^ n - 1),
  { simp only [map_pow, map_X, map_one, map_sub] },
  have h : ∀ i ∈ n.divisors, cyclotomic i R = map (int.cast_ring_hom R) (cyclotomic i ℤ),
  { intros i hi,
    exact (map_cyclotomic_int i R).symm },
  rw [finset.prod_congr (refl n.divisors) h, coerc, ←map_prod (int.cast_ring_hom R)
  (λ i, cyclotomic i ℤ), integer]
end

section arithmetic_function
open nat.arithmetic_function
open_locale arithmetic_function

/-- `cyclotomic n R` can be expressed as a product in a fraction field of `polynomial R`
  using Möbius inversion. -/
lemma cyclotomic_eq_prod_X_pow_sub_one_pow_moebius {n : ℕ} (hpos : 0 < n)
  (R : Type*) [comm_ring R] [nontrivial R]
  {K : Type*} [field K] [algebra (polynomial R) K] [is_fraction_ring (polynomial R) K] :
  algebra_map _ K (cyclotomic n R) =
    ∏ i in n.divisors_antidiagonal, (algebra_map (polynomial R) K (X ^ i.snd - 1)) ^ μ i.fst :=
begin
  have h : ∀ (n : ℕ), 0 < n →
    ∏ i in nat.divisors n, algebra_map _ K (cyclotomic i R) = algebra_map _ _ (X ^ n - 1),
  { intros n hn,
    rw [← prod_cyclotomic_eq_X_pow_sub_one hn R, ring_hom.map_prod] },
  rw (prod_eq_iff_prod_pow_moebius_eq_of_nonzero (λ n hn, _) (λ n hn, _)).1 h n hpos;
  rw [ne.def, is_fraction_ring.to_map_eq_zero_iff],
  { apply cyclotomic_ne_zero },
  { apply monic.ne_zero,
    apply monic_X_pow_sub_C _ (ne_of_gt hn) }
end

end arithmetic_function

/-- We have
`cyclotomic n R = (X ^ k - 1) /ₘ (∏ i in nat.proper_divisors k, cyclotomic i K)`. -/
lemma cyclotomic_eq_X_pow_sub_one_div {R : Type*} [comm_ring R] [nontrivial R] {n : ℕ}
  (hpos: 0 < n) : cyclotomic n R = (X ^ n - 1) /ₘ (∏ i in nat.proper_divisors n, cyclotomic i R) :=
begin
  rw [←prod_cyclotomic_eq_X_pow_sub_one hpos,
  nat.divisors_eq_proper_divisors_insert_self_of_pos hpos,
  finset.prod_insert nat.proper_divisors.not_self_mem],
  have prod_monic : (∏ i in nat.proper_divisors n, cyclotomic i R).monic,
  { apply monic_prod_of_monic,
    intros i hi,
    exact cyclotomic.monic i R },
  rw (div_mod_by_monic_unique (cyclotomic n R) 0 prod_monic _).1,
  simp only [degree_zero, zero_add],
  split,
  { rw mul_comm },
  rw [bot_lt_iff_ne_bot],
  intro h,
  exact monic.ne_zero prod_monic (degree_eq_bot.1 h)
end

/-- If `m` is a proper divisor of `n`, then `X ^ m - 1` divides
`∏ i in nat.proper_divisors n, cyclotomic i R`. -/
lemma X_pow_sub_one_dvd_prod_cyclotomic (R : Type*) [comm_ring R] {n m : ℕ} (hpos : 0 < n)
  (hm : m ∣ n) (hdiff : m ≠ n) : X ^ m - 1 ∣ ∏ i in nat.proper_divisors n, cyclotomic i R :=
begin
  replace hm := nat.mem_proper_divisors.2 ⟨hm, lt_of_le_of_ne (nat.divisor_le (nat.mem_divisors.2
    ⟨hm, (ne_of_lt hpos).symm⟩)) hdiff⟩,
  rw [← finset.sdiff_union_of_subset (nat.divisors_subset_proper_divisors (ne_of_lt hpos).symm
    (nat.mem_proper_divisors.1 hm).1 (ne_of_lt (nat.mem_proper_divisors.1 hm).2)),
    finset.prod_union finset.sdiff_disjoint, prod_cyclotomic_eq_X_pow_sub_one
    (nat.pos_of_mem_proper_divisors hm)],
  exact ⟨(∏ (x : ℕ) in n.proper_divisors \ m.divisors, cyclotomic x R), by rw mul_comm⟩
end

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic n K = ∏ μ in primitive_roots n R, (X - C μ)`. In particular,
`cyclotomic n K = cyclotomic' n K` -/
lemma cyclotomic_eq_prod_X_sub_primitive_roots {K : Type*} [field K] {ζ : K} {n : ℕ}
  (h : is_primitive_root ζ n) :
  cyclotomic n K = ∏ μ in primitive_roots n K, (X - C μ) :=
begin
  rw ←cyclotomic',
  revert h ζ,
  apply nat.strong_induction_on n,
  intros k hk z hz,
  cases nat.eq_zero_or_pos k with hzero hpos,
  { simp only [hzero, cyclotomic'_zero, cyclotomic_zero] },
  have h : ∀ i ∈ k.proper_divisors, cyclotomic i K = cyclotomic' i K,
  { intros i hi,
    obtain ⟨d, hd⟩ := (nat.mem_proper_divisors.1 hi).1,
    rw mul_comm at hd,
    exact hk i (nat.mem_proper_divisors.1 hi).2 (is_primitive_root.pow hpos hz hd) },
  rw [@cyclotomic_eq_X_pow_sub_one_div _ _ (field.to_nontrivial K) _ hpos,
  cyclotomic'_eq_X_pow_sub_one_div hpos hz, finset.prod_congr (refl k.proper_divisors) h]
end

/-- Any `n`-th primitive root of unity is a root of `cyclotomic n ℤ`.-/
lemma is_root_cyclotomic {n : ℕ} {K : Type*} [field K] (hpos : 0 < n) {μ : K}
  (h : is_primitive_root μ n) : is_root (cyclotomic n K) μ :=
begin
  rw [← mem_roots (cyclotomic_ne_zero n K),
  cyclotomic_eq_prod_X_sub_primitive_roots h, roots_prod_X_sub_C, ← finset.mem_def],
  rwa [← mem_primitive_roots hpos] at h,
end

lemma eq_cyclotomic_iff {R : Type*} [comm_ring R] [nontrivial R] {n : ℕ} (hpos: 0 < n)
  (P : polynomial R) :
  P = cyclotomic n R ↔ P * (∏ i in nat.proper_divisors n, polynomial.cyclotomic i R) = X ^ n - 1 :=
begin
  split,
  { intro hcycl,
    rw [hcycl, ← finset.prod_insert (@nat.proper_divisors.not_self_mem n),
      ← nat.divisors_eq_proper_divisors_insert_self_of_pos hpos],
    exact prod_cyclotomic_eq_X_pow_sub_one hpos R },
  { intro hP,
    have prod_monic : (∏ i in nat.proper_divisors n, cyclotomic i R).monic,
    { apply monic_prod_of_monic,
      intros i hi,
      exact cyclotomic.monic i R },
    rw [@cyclotomic_eq_X_pow_sub_one_div R _ _ _ hpos,
      (div_mod_by_monic_unique P 0 prod_monic _).1],
    split,
    { rwa [zero_add, mul_comm] },
    rw [degree_zero, bot_lt_iff_ne_bot],
    intro h,
    exact monic.ne_zero prod_monic (degree_eq_bot.1 h) },
end

/-- If `p` is prime, then `cyclotomic p R = geom_sum X p`. -/
lemma cyclotomic_eq_geom_sum {R : Type*} [comm_ring R] [nontrivial R] {p : ℕ}
  (hp : nat.prime p) : cyclotomic p R = geom_sum X p :=
begin
  symmetry,
  refine (eq_cyclotomic_iff hp.pos _).mpr _,
  simp only [nat.prime.proper_divisors hp, geom_sum_mul, finset.prod_singleton, cyclotomic_one],
end

/-- The constant term of `cyclotomic n R` is `1` if `2 ≤ n`. -/
lemma cyclotomic_coeff_zero (R : Type*) [comm_ring R] {n : ℕ} (hn : 2 ≤ n) :
  (cyclotomic n R).coeff 0 = 1 :=
begin
  induction n using nat.strong_induction_on with n hi,
  have hprod : (∏ i in nat.proper_divisors n, (polynomial.cyclotomic i R).coeff 0) = -1,
  { rw [←finset.insert_erase (nat.one_mem_proper_divisors_iff_one_lt.2
      (lt_of_lt_of_le one_lt_two hn)), finset.prod_insert (finset.not_mem_erase 1 _),
      cyclotomic_one R],
    have hleq : ∀ j ∈ n.proper_divisors.erase 1, 2 ≤ j,
    { intros j hj,
      apply nat.succ_le_of_lt,
      exact (ne.le_iff_lt ((finset.mem_erase.1 hj).1).symm).mp (nat.succ_le_of_lt
      (nat.pos_of_mem_proper_divisors (finset.mem_erase.1 hj).2)) },
    have hcongr : ∀ j ∈ n.proper_divisors.erase 1, (cyclotomic j R).coeff 0 = 1,
    { intros j hj,
      exact hi j (nat.mem_proper_divisors.1 (finset.mem_erase.1 hj).2).2 (hleq j hj) },
    have hrw : ∏ (x : ℕ) in n.proper_divisors.erase 1, (cyclotomic x R).coeff 0 = 1,
    { rw finset.prod_congr (refl (n.proper_divisors.erase 1)) hcongr,
      simp only [finset.prod_const_one] },
    simp only [hrw, mul_one, zero_sub, coeff_one_zero, coeff_X_zero, coeff_sub] },
  have heq : (X ^ n - 1).coeff 0 = -(cyclotomic n R).coeff 0,
  { rw [←prod_cyclotomic_eq_X_pow_sub_one (lt_of_lt_of_le zero_lt_two hn),
      nat.divisors_eq_proper_divisors_insert_self_of_pos (lt_of_lt_of_le zero_lt_two hn),
      finset.prod_insert nat.proper_divisors.not_self_mem, mul_coeff_zero, coeff_zero_prod, hprod,
      mul_neg_eq_neg_mul_symm, mul_one] },
  have hzero : (X ^ n - 1).coeff 0 = (-1 : R),
  { rw coeff_zero_eq_eval_zero _,
    simp only [zero_pow (lt_of_lt_of_le zero_lt_two hn), eval_X, eval_one, zero_sub, eval_pow,
      eval_sub] },
  rw hzero at heq,
  exact neg_inj.mp (eq.symm heq)
end

/-- If `(a : ℕ)` is a root of `cyclotomic n (zmod p)`, where `p` is a prime, then `a` and `p` are
coprime. -/
lemma coprime_of_root_cyclotomic {n : ℕ} (hpos : 0 < n) {p : ℕ} [hprime : fact p.prime] {a : ℕ}
  (hroot : is_root (cyclotomic n (zmod p)) (nat.cast_ring_hom (zmod p) a)) :
  a.coprime p :=
begin
  apply nat.coprime.symm,
  rw [hprime.1.coprime_iff_not_dvd],
  by_contra h,
  replace h := (zmod.nat_coe_zmod_eq_zero_iff_dvd a p).2 h,
  rw [is_root.def, ring_hom.eq_nat_cast, h, ← coeff_zero_eq_eval_zero] at hroot,
  by_cases hone : n = 1,
  { simp only [hone, cyclotomic_one, zero_sub, coeff_one_zero, coeff_X_zero, neg_eq_zero,
    one_ne_zero, coeff_sub] at hroot,
    exact hroot },
  rw [cyclotomic_coeff_zero (zmod p) (nat.succ_le_of_lt (lt_of_le_of_ne
    (nat.succ_le_of_lt hpos) (ne.symm hone)))] at hroot,
  exact one_ne_zero hroot
end

end cyclotomic

section order

/-- If `(a : ℕ)` is a root of `cyclotomic n (zmod p)`, then the multiplicative order of `a` modulo
`p` divides `n`. -/
lemma order_of_root_cyclotomic_dvd {n : ℕ} (hpos : 0 < n) {p : ℕ} [fact p.prime]
  {a : ℕ} (hroot : is_root (cyclotomic n (zmod p)) (nat.cast_ring_hom (zmod p) a)) :
  order_of (zmod.unit_of_coprime a (coprime_of_root_cyclotomic hpos hroot)) ∣ n :=
begin
  apply order_of_dvd_of_pow_eq_one,
  suffices hpow : eval (nat.cast_ring_hom (zmod p) a) (X ^ n - 1 : polynomial (zmod p)) = 0,
  { simp only [eval_X, eval_one, eval_pow, eval_sub, ring_hom.eq_nat_cast] at hpow,
    apply units.coe_eq_one.1,
    simp only [sub_eq_zero.mp hpow, zmod.coe_unit_of_coprime, units.coe_pow] },
  rw [is_root.def] at hroot,
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos (zmod p),
    nat.divisors_eq_proper_divisors_insert_self_of_pos hpos,
    finset.prod_insert nat.proper_divisors.not_self_mem, eval_mul, hroot, zero_mul]
end

/-- If `(a : ℕ)` is a root of `cyclotomic n (zmod p)`, where `p` is a prime that does not divide
`n`, then the multiplicative order of `a` modulo `p` is exactly `n`. -/
lemma order_of_root_cyclotomic {n : ℕ} (hpos : 0 < n) {p : ℕ} [fact p.prime] {a : ℕ}
  (hn : ¬ p ∣ n) (hroot : is_root (cyclotomic n (zmod p)) (nat.cast_ring_hom (zmod p) a)) :
  order_of (zmod.unit_of_coprime a (coprime_of_root_cyclotomic hpos hroot)) = n :=
begin
  set m := order_of (zmod.unit_of_coprime a (coprime_of_root_cyclotomic hpos hroot)),
  have ha := coprime_of_root_cyclotomic hpos hroot,
  have hdivcycl : map (int.cast_ring_hom (zmod p)) (X - a) ∣ (cyclotomic n (zmod p)),
  { replace hrootdiv := dvd_iff_is_root.2 hroot,
    simp only [C_eq_nat_cast, ring_hom.eq_nat_cast] at hrootdiv,
    simp only [hrootdiv, map_nat_cast, map_X, map_sub] },
  by_contra hdiff,
  have hdiv : map (int.cast_ring_hom (zmod p)) (X - a) ∣
    ∏ i in nat.proper_divisors n, cyclotomic i (zmod p),
  { suffices hdivm : map (int.cast_ring_hom (zmod p)) (X - a) ∣ X ^ m - 1,
    { exact dvd_trans hdivm (X_pow_sub_one_dvd_prod_cyclotomic (zmod p) hpos
        (order_of_root_cyclotomic_dvd hpos hroot) hdiff) },
    rw [map_sub, map_X, map_nat_cast, ← C_eq_nat_cast, dvd_iff_is_root, is_root.def, eval_sub,
      eval_pow, eval_one, eval_X, sub_eq_zero, ← zmod.coe_unit_of_coprime a ha, ← units.coe_pow,
      units.coe_eq_one],
    exact pow_order_of_eq_one (zmod.unit_of_coprime a ha) },
  have habs : (map (int.cast_ring_hom (zmod p)) (X - a)) ^ 2 ∣ X ^ n - 1,
  { obtain ⟨P, hP⟩ := hdivcycl,
    obtain ⟨Q, hQ⟩ := hdiv,
    rw [← prod_cyclotomic_eq_X_pow_sub_one hpos, nat.divisors_eq_proper_divisors_insert_self_of_pos
      hpos, finset.prod_insert nat.proper_divisors.not_self_mem, hP, hQ],
    exact ⟨P * Q, by ring⟩ },
  have hnzero : ↑n ≠ (0 : (zmod p)),
  { intro ha,
    exact hn (int.coe_nat_dvd.1 ((zmod.int_coe_zmod_eq_zero_iff_dvd n p).1 ha)) },
  rw [sq] at habs,
  replace habs := squarefree_X_pow_sub_C (1 : (zmod p)) hnzero one_ne_zero
    (map (int.cast_ring_hom (zmod p)) (X - a)) habs,
  simp only [map_nat_cast, map_X, map_sub] at habs,
  replace habs := degree_eq_zero_of_is_unit habs,
  rw [← C_eq_nat_cast, degree_X_sub_C] at habs,
  norm_cast at habs
end

end order

end polynomial

section minpoly

open is_primitive_root polynomial complex

/-- The minimal polynomial of a primitive `n`-th root of unity `μ` divides `cyclotomic n ℤ`. -/
lemma minpoly_primitive_root_dvd_cyclotomic {n : ℕ} {K : Type*} [field K] {μ : K}
  (h : is_primitive_root μ n) (hpos : 0 < n) [char_zero K] :
  minpoly ℤ μ ∣ cyclotomic n ℤ :=
begin
  apply minpoly.gcd_domain_dvd ℚ (is_integral h hpos) (cyclotomic.monic n ℤ).is_primitive,
  simpa [aeval_def, eval₂_eq_eval_map, is_root.def] using is_root_cyclotomic hpos h
end

/-- `cyclotomic n ℤ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
lemma cyclotomic_eq_minpoly {n : ℕ} {K : Type*} [field K] {μ : K}
  (h : is_primitive_root μ n) (hpos : 0 < n) [char_zero K] :
  cyclotomic n ℤ = minpoly ℤ μ :=
begin
  refine eq_of_monic_of_dvd_of_nat_degree_le (minpoly.monic (is_integral h hpos))
    (cyclotomic.monic n ℤ) (minpoly_primitive_root_dvd_cyclotomic h hpos) _,
  simpa [nat_degree_cyclotomic n ℤ] using totient_le_degree_minpoly h hpos
end

/-- `cyclotomic n ℤ` is irreducible. -/
lemma cyclotomic.irreducible {n : ℕ} (hpos : 0 < n) : irreducible (cyclotomic n ℤ) :=
begin
  have h0 := (ne_of_lt hpos).symm,
  rw [cyclotomic_eq_minpoly (is_primitive_root_exp n h0) hpos],
  apply minpoly.irreducible,
  exact (is_primitive_root_exp n h0).is_integral hpos,
end

end minpoly
