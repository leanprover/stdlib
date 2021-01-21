/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Riccardo Brasca
-/

import data.polynomial.algebra_map
import algebra.algebra.subalgebra
import algebra.polynomial.big_operators

/-!
# Polynomials that lift

Given semirings `R` and `S` with a morphism `f : R →+* S`, we define a subsemiring `lifts` of
`polynomial S` by the image of `ring_hom.of (map f)`.
Then, we prove that a polynomial that lifts can always be lifted to a polynomial of the same degree
and that a monic polynomial that lifts can be lifted to a monic polynomial (of the same degree).

## Main definition

* `lifts (f : R →+* S)` : the subsemiring of polynomials that lift.

## Main results

* `lifts_and_degree_eq` : A polynomial lifts if and only if it can be lifted to a polynomial
of the same degree.
* `lifts_and_degree_eq_and_monic` : A monic polynomial lifts if and only if it can be lifted to a
monic polynomial of the same degree.
* `lifts_iff_alg` : if `R` is commutative, a polynomial lifts if and only if it is in the image of
`map_alg`, where `map_alg : polynomial R →ₐ[R] polynomial S` is the only `R`-algebra map
that sends `X` to `X`.

## Implementation details

In general `R` and `S` are semiring, so `lifts` is a semiring. In the case of rings, see
`lifts_iff_lifts_ring`.

Since we do not assume `R` to be commutative, we cannot say in general that the set of polynomials
that lift is a subalgebra. (By `lift_iff` this is true if `R` is commutative.)

-/

open_locale classical big_operators
noncomputable theory

namespace polynomial
universes u v w

section semiring

variables {R : Type u} [semiring R] {S : Type v} [semiring S] {f : R →+* S}

/-- We define the subsemiring of polynomials that lifts as the image of `ring_hom.of (map f)`. -/
def lifts (f : R →+* S) : subsemiring (polynomial S) := ring_hom.srange (ring_hom.of (map f))

lemma mem_lifts (p : polynomial S) : p ∈ lifts f ↔ ∃ (q : polynomial R), map f q = p :=
by simp only [lifts, ring_hom.coe_of, ring_hom.mem_srange]

lemma lifts_iff_set_range (p : polynomial S) : p ∈ lifts f ↔ p ∈ set.range (map f) :=
by simp only [lifts, set.mem_range, ring_hom.coe_of, ring_hom.mem_srange]

lemma lifts_iff_coeff_lifts (p : polynomial S) : p ∈ lifts f ↔ ∀ (n : ℕ), p.coeff n ∈ set.range f :=
by rw [lifts_iff_set_range, mem_map_range]

/--If `(r : R)`, then `C (f r)` lifts. -/
lemma C_mem_lifts (f : R →+* S) (r : R) : (C (f r)) ∈ lifts f :=
⟨C r, by simp only [map_C, set.mem_univ, subsemiring.coe_top, eq_self_iff_true,
  ring_hom.coe_of, and_self]⟩

/-- If `(s : S)` is in the image of `f`, then `C s` lifts. -/
lemma C'_mem_lifts {f : R →+* S} {s : S} (h : s ∈ set.range f) : (C s) ∈ lifts f :=
begin
  obtain ⟨r, rfl⟩ := set.mem_range.1 h,
  use C r,
  simp only [map_C, set.mem_univ, subsemiring.coe_top, eq_self_iff_true, ring_hom.coe_of, and_self]
end

/-- The polynomial `X` lifts. -/
lemma X_mem_lifts (f : R →+* S) : (X : polynomial S) ∈ lifts f :=
⟨X, by simp only [set.mem_univ, subsemiring.coe_top, eq_self_iff_true, map_X,
  ring_hom.coe_of, and_self]⟩

/-- The polynomial `X ^ n` lifts. -/
lemma X_pow_mem_lifts (f : R →+* S) (n : ℕ) : (X ^ n : polynomial S) ∈ lifts f :=
⟨X ^ n, by simp only [map_pow, set.mem_univ, subsemiring.coe_top, eq_self_iff_true, map_X,
  ring_hom.coe_of, and_self]⟩

/-- If `p` lifts and `(r : R)` then `r * p` lifts. -/
lemma base_mul_mem_lifts {p : polynomial S} (r : R) (hp : p ∈ lifts f) : C (f r) * p ∈ lifts f :=
begin
  simp only [lifts, ring_hom.coe_of, ring_hom.mem_srange] at hp ⊢,
  obtain ⟨p₁, rfl⟩ := hp,
  use C r * p₁,
  simp only [map_C, map_mul]
end

/-- If `(s : S)` is in the image of `f`, then `monomial n s` lifts. -/
lemma monomial_mem_lifts {s : S} (n : ℕ) (h : s ∈ set.range f) : (monomial n s) ∈ lifts f :=
begin
  obtain ⟨r, rfl⟩ := set.mem_range.1 h,
  use monomial n r,
  simp only [set.mem_univ, map_monomial, subsemiring.coe_top, eq_self_iff_true, ring_hom.coe_of,
  and_self],
end

/-- If `p` lifts then `p.erase n` lifts. -/
lemma erase_mem_lifts {p : polynomial S} (n : ℕ) (h : p ∈ lifts f) : p.erase n ∈ lifts f :=
begin
  rw [lifts_iff_set_range, mem_map_range, coeff] at h ⊢,
  intros k,
  by_cases hk : k = n,
  { use 0,
    simp only [hk, ring_hom.map_zero, finsupp.erase_same] },
  obtain ⟨i, hi⟩ := h k,
  use i,
  simp only [hi, hk, finsupp.erase_ne, ne.def, not_false_iff],
end

section lift_deg

lemma monomial_mem_lifts_and_degree_eq {s : S} {n : ℕ} (hl : monomial n s ∈ lifts f) :
  ∃ (q : polynomial R), map f q = (monomial n s) ∧ q.degree = (monomial n s).degree :=
begin
  by_cases hzero : s = 0,
  { use 0,
    simp only [hzero, degree_zero, eq_self_iff_true, and_self, monomial_zero_right, map_zero] },
  rw lifts_iff_set_range at hl,
  obtain ⟨q, hq⟩ := hl,
  replace hq := (ext_iff.1 hq) n,
  have hcoeff : f (q.coeff n) = s,
  { simp [coeff_monomial] at hq,
    exact hq },
  use (monomial n (q.coeff n)),
  split,
  { simp only [hcoeff, map_monomial] },
  have hqzero : q.coeff n ≠ 0,
  { intro habs,
    simp only [habs, ring_hom.map_zero] at hcoeff,
    exact hzero hcoeff.symm },
  repeat {rw single_eq_C_mul_X},
  simp only [hzero, hqzero, ne.def, not_false_iff, degree_C_mul_X_pow],
end

/-- A polynomial lifts if and only if it can be lifted to a polynomial of the same degree. -/
lemma mem_lifts_and_degree_eq {p : polynomial S} (hlifts : p ∈ lifts f) :
  ∃ (q : polynomial R), map f q = p ∧ q.degree = p.degree :=
begin
  generalize' hd : p.nat_degree = d,
  revert hd p,
  apply nat.strong_induction_on d,
  intros n hn p hlifts hdeg,
  by_cases erase_zero : p.erase_lead = 0,
  { rw [← erase_lead_add_monomial_nat_degree_leading_coeff p, erase_zero, zero_add, leading_coeff],
    exact monomial_mem_lifts_and_degree_eq (monomial_mem_lifts p.nat_degree
    ((lifts_iff_coeff_lifts p).1 hlifts p.nat_degree)) },
  have deg_erase := or.resolve_right (erase_lead_nat_degree_lt_or_erase_lead_eq_zero p) erase_zero,
  have pzero : p ≠ 0,
  { intro habs,
    exfalso,
    rw [habs, erase_lead_zero, eq_self_iff_true, not_true] at erase_zero,
    exact erase_zero },
  have lead_zero : p.coeff p.nat_degree ≠ 0,
  { rw [← leading_coeff, ne.def, leading_coeff_eq_zero]; exact pzero },
  obtain ⟨lead, hlead⟩ := monomial_mem_lifts_and_degree_eq (monomial_mem_lifts p.nat_degree
    ((lifts_iff_coeff_lifts p).1 hlifts p.nat_degree)),
  have deg_lead : lead.degree = p.nat_degree,
  { rw [hlead.2, single_eq_C_mul_X, degree_C_mul_X_pow p.nat_degree lead_zero] },
  rw hdeg at deg_erase,
  obtain ⟨erase, herase⟩ := hn p.erase_lead.nat_degree deg_erase
    (erase_mem_lifts p.nat_degree hlifts) (refl p.erase_lead.nat_degree),
  use erase + lead,
  split,
  { simp only [hlead, herase, map_add],
    nth_rewrite 0 erase_lead_add_monomial_nat_degree_leading_coeff p },
  rw [←hdeg, erase_lead] at deg_erase,
  replace deg_erase := lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 deg_erase),
  rw [← deg_lead, ← herase.2] at deg_erase,
  rw [degree_add_eq_right_of_degree_lt deg_erase, deg_lead, degree_eq_nat_degree pzero]
end

end lift_deg

section monic

/-- A monic polynomial lifts if and only if it can be lifted to a monic polynomial
of the same degree. -/
lemma lifts_and_degree_eq_and_monic [nontrivial S] {p : polynomial S} (hlifts :p ∈ lifts f)
  (hmonic : p.monic) : ∃ (q : polynomial R), map f q = p ∧ q.degree = p.degree ∧ q.monic :=
begin
  by_cases Rtrivial : nontrivial R,
  swap,
  { rw not_nontrivial_iff_subsingleton at Rtrivial,
    obtain ⟨q, hq⟩ := mem_lifts_and_degree_eq hlifts,
    use q,
    exact ⟨hq.1, hq.2, @monic_of_subsingleton _ _ Rtrivial q⟩ },
  by_cases er_zero : p.erase_lead = 0,
  { rw [← erase_lead_add_C_mul_X_pow p, er_zero, zero_add, monic.def.1 hmonic, C_1, one_mul],
    use X ^ p.nat_degree,
    repeat {split},
    { simp only [map_pow, map_X] },
    { rw [@degree_X_pow R _ Rtrivial, degree_X_pow] },
    {exact monic_pow monic_X p.nat_degree } },
  obtain ⟨q, hq⟩ := mem_lifts_and_degree_eq (erase_mem_lifts p.nat_degree hlifts),
  have deg_er : p.erase_lead.nat_degree < p.nat_degree :=
    or.resolve_right (erase_lead_nat_degree_lt_or_erase_lead_eq_zero p) er_zero,
  replace deg_er := with_bot.coe_lt_coe.2 deg_er,
  rw [← degree_eq_nat_degree er_zero, erase_lead, ← hq.2,
    ← @degree_X_pow R _ Rtrivial p.nat_degree] at deg_er,
  use q + X ^ p.nat_degree,
  repeat {split},
  { simp only [hq, map_add, map_pow, map_X],
    nth_rewrite 3 [← erase_lead_add_C_mul_X_pow p],
    rw [erase_lead, monic.leading_coeff hmonic, C_1, one_mul] },
  { rw [degree_add_eq_right_of_degree_lt deg_er, @degree_X_pow R _ Rtrivial p.nat_degree,
    degree_eq_nat_degree (monic.ne_zero hmonic)] },
  { rw [monic.def, leading_coeff_add_of_degree_lt deg_er],
    exact monic_pow monic_X p.nat_degree }
end

end monic

end semiring

section ring

variables {R : Type u} [ring R] {S : Type v} [ring S] (f : R →+* S)

/-- The subring of polynomials that lift. -/
def lifts_ring (f : R →+* S) : subring (polynomial S) := ring_hom.range (ring_hom.of (map f))

/-- If `R` and `S` are rings, `p` is in the subring of polynomials that lift if and only if it is in
the subsemiring of polynomials that lift. -/
lemma lifts_iff_lifts_ring (p : polynomial S) : p ∈ lifts f ↔ p ∈ lifts_ring f :=
by simp only [lifts, lifts_ring, ring_hom.mem_range, ring_hom.mem_srange]

end ring

section algebra

variables {R : Type u} [comm_semiring R] {S : Type v} [semiring S] [algebra R S]

/-- The map `polynomial R → polynomial S` as an algebra homomorphism. -/
def map_alg (R : Type u) [comm_semiring R] (S : Type v) [semiring S] [algebra R S] :
  polynomial R →ₐ[R] polynomial S := @aeval _ (polynomial S) _ _ _ (X : polynomial S)

/-- `map_alg` is the morphism induced by `R → S`. -/
lemma map_alg_eq_map (p : polynomial R) : map_alg R S p = map (algebra_map R S) p :=
by simp only [map_alg, aeval_def, eval₂, map, algebra_map_apply, ring_hom.coe_comp]

/-- A polynomial `p` lifts if and only if it is in the image of `map_alg`. -/
lemma mem_lifts_iff_mem_alg (R : Type u) [comm_semiring R] {S : Type v} [semiring S] [algebra R S]
  (p : polynomial S) :p ∈ lifts (algebra_map R S) ↔ p ∈ (alg_hom.range (@map_alg R _ S _ _)) :=
by simp only [lifts, map_alg_eq_map, alg_hom.mem_range, ring_hom.coe_of, ring_hom.mem_srange]

/-- If `p` lifts and `(r : R)` then `r • p` lifts. -/
lemma smul_mem_lifts {p : polynomial S} (r : R) (hp : p ∈ lifts (algebra_map R S)) :
  r • p ∈ lifts (algebra_map R S) :=
by { rw mem_lifts_iff_mem_alg at hp ⊢, exact subalgebra.smul_mem (map_alg R S).range hp r }

end algebra

end polynomial
