/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import ring_theory.int.basic
import ring_theory.localization

/-!
# Gauss's Lemma

Gauss's Lemma is one of a few results pertaining to irreducibility of primitive polynomials.

## Main Results
 - `polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map`:
  A primitive polynomial is irreducible iff it is irreducible in a fraction field.
 - `polynomial.is_primitive.int.irreducible_iff_irreducible_map_cast`:
  A primitive polynomial over `ℤ` is irreducible iff it is irreducible over `ℚ`.
 - `polynomial.is_primitive.dvd_iff_fraction_map_dvd_fraction_map`:
  Two primitive polynomials divide each other iff they do in a fraction field.
 - `polynomial.is_primitive.int.dvd_iff_map_cast_dvd_map_cast`:
  Two primitive polynomials over `ℤ` divide each other if they do in `ℚ`.

-/

local notation R`⁰`:9000 := non_zero_divisors R

variables {R : Type*} [integral_domain R]

namespace polynomial
section gcd_monoid
variable [gcd_monoid R]

section
variables {S : Type*} [integral_domain S] {φ : R →+* S} (hinj : function.injective φ)
variables {f : polynomial R} (hf : f.is_primitive)
include hinj hf

lemma is_primitive.is_unit_iff_is_unit_map_of_injective :
  is_unit f ↔ is_unit (map φ f) :=
begin
  refine ⟨(ring_hom.of (map φ)).is_unit_map, λ h, _⟩,
  rcases is_unit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩,
  have hdeg := degree_C u.ne_zero,
  rw [hu, degree_map' hinj] at hdeg,
  rw [eq_C_of_degree_eq_zero hdeg, is_primitive_iff_content_eq_one,
      content_C, normalize_eq_one] at hf,
  rwa [eq_C_of_degree_eq_zero hdeg, is_unit_C],
end

lemma is_primitive.irreducible_of_irreducible_map_of_injective (h_irr : irreducible (map φ f)) :
  irreducible f :=
begin
  refine ⟨λ h, h_irr.not_unit (is_unit.map (monoid_hom.of (map φ)) h), _⟩,
  intros a b h,
  rcases h_irr.is_unit_or_is_unit (by rw [h, map_mul]) with hu | hu,
  { left,
    rwa (hf.is_primitive_of_dvd (dvd.intro _ h.symm)).is_unit_iff_is_unit_map_of_injective hinj },
  right,
  rwa (hf.is_primitive_of_dvd (dvd.intro_left _ h.symm)).is_unit_iff_is_unit_map_of_injective hinj
end

end

section fraction_map
variables {K : Type*} [field K] [algebra R K] [is_fraction_ring R K]

lemma is_primitive.is_unit_iff_is_unit_map {p : polynomial R} (hp : p.is_primitive) :
  is_unit p ↔ is_unit (p.map (algebra_map R K)) :=
hp.is_unit_iff_is_unit_map_of_injective (is_fraction_ring.injective _ _)

open is_localization

lemma is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part
  {p : polynomial K} (h0 : p ≠ 0) (h : is_unit (integer_normalization R⁰ p).prim_part) :
  is_unit p :=
begin
  rcases is_unit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩,
  obtain ⟨⟨c, c0⟩, hc⟩ := integer_normalization_map_to_map R⁰ p,
  rw [subtype.coe_mk, algebra.smul_def, algebra_map_apply] at hc,
  apply is_unit_of_mul_is_unit_right,
  rw [← hc, (integer_normalization R⁰ p).eq_C_content_mul_prim_part, ← hu,
    ← ring_hom.map_mul, is_unit_iff],
  refine ⟨algebra_map R K ((integer_normalization R⁰ p).content * ↑u),
    is_unit_iff_ne_zero.2 (λ con, _), by simp⟩,
  replace con := (algebra_map R K).injective_iff.1 (is_fraction_ring.injective _ _) _ con,
  rw [mul_eq_zero, content_eq_zero_iff, is_fraction_ring.integer_normalization_eq_zero_iff] at con,
  rcases con with con | con,
  { apply h0 con },
  { apply units.ne_zero _ con },
end

/-- **Gauss's Lemma** states that a primitive polynomial is irreducible iff it is irreducible in the
  fraction field. -/
theorem is_primitive.irreducible_iff_irreducible_map_fraction_map
  {p : polynomial R} (hp : p.is_primitive) :
  irreducible p ↔ irreducible (p.map (algebra_map R K)) :=
begin
  refine ⟨λ hi, ⟨λ h, hi.not_unit (hp.is_unit_iff_is_unit_map.2 h), λ a b hab, _⟩,
    hp.irreducible_of_irreducible_map_of_injective (is_fraction_ring.injective _ _)⟩,
  obtain ⟨⟨c, c0⟩, hc⟩ := integer_normalization_map_to_map R⁰ a,
  obtain ⟨⟨d, d0⟩, hd⟩ := integer_normalization_map_to_map R⁰ b,
  rw [algebra.smul_def, algebra_map_apply, subtype.coe_mk] at hc hd,
  rw mem_non_zero_divisors_iff_ne_zero at c0 d0,
  have hcd0 : c * d ≠ 0 := mul_ne_zero c0 d0,
  rw [ne.def, ← C_eq_zero] at hcd0,
  have h1 : C c * C d * p = integer_normalization R⁰ a * integer_normalization R⁰ b,
  { apply map_injective (algebra_map R K) (is_fraction_ring.injective _ _) _,
    rw [map_mul, map_mul, map_mul, hc, hd, map_C, map_C, hab],
    ring },
  obtain ⟨u, hu⟩ : associated (c * d) (content (integer_normalization R⁰ a) *
            content (integer_normalization R⁰ b)),
  { rw [← dvd_dvd_iff_associated, ← normalize_eq_normalize_iff, normalize.map_mul,
        normalize.map_mul, normalize_content, normalize_content,
        ← mul_one (normalize c * normalize d), ← hp.content_eq_one, ← content_C, ← content_C,
        ← content_mul, ← content_mul, ← content_mul, h1] },
  rw [← ring_hom.map_mul, eq_comm,
    (integer_normalization R⁰ a).eq_C_content_mul_prim_part,
    (integer_normalization R⁰ b).eq_C_content_mul_prim_part, mul_assoc,
    mul_comm _ (C _ * _), ← mul_assoc, ← mul_assoc, ← ring_hom.map_mul, ← hu, ring_hom.map_mul,
    mul_assoc, mul_assoc, ← mul_assoc (C ↑u)] at h1,
  have h0 : (a ≠ 0) ∧ (b ≠ 0),
  { classical,
    rw [ne.def, ne.def, ← decidable.not_or_iff_and_not, ← mul_eq_zero, ← hab],
    intro con,
    apply hp.ne_zero (map_injective (algebra_map R K) (is_fraction_ring.injective _ _) _),
    simp [con] },
  rcases hi.is_unit_or_is_unit (mul_left_cancel' hcd0 h1).symm with h | h,
  { right,
    apply is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part h0.2
      (is_unit_of_mul_is_unit_right h) },
  { left,
    apply is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part h0.1 h },
end

lemma is_primitive.dvd_of_fraction_map_dvd_fraction_map {p q : polynomial R}
  (hp : p.is_primitive) (hq : q.is_primitive)
  (h_dvd : p.map (algebra_map R K) ∣ q.map (algebra_map R K)) : p ∣ q :=
begin
  rcases h_dvd with ⟨r, hr⟩,
  obtain ⟨⟨s, s0⟩, hs⟩ := integer_normalization_map_to_map R⁰ r,
  rw [subtype.coe_mk, algebra.smul_def, algebra_map_apply] at hs,
  have h : p ∣ q * C s,
  { use (integer_normalization R⁰ r),
    apply map_injective (algebra_map R K) (is_fraction_ring.injective _ _),
    rw [map_mul, map_mul, hs, hr, mul_assoc, mul_comm r],
    simp },
  rw [← hp.dvd_prim_part_iff_dvd, prim_part_mul, hq.prim_part_eq, dvd_iff_dvd_of_rel_right] at h,
  { exact h },
  { symmetry,
    rcases is_unit_prim_part_C s with ⟨u, hu⟩,
    use u,
    simp [hu], },
  iterate 2 { apply mul_ne_zero hq.ne_zero,
    rw [ne.def, C_eq_zero],
    contrapose! s0,
    simp [s0, mem_non_zero_divisors_iff_ne_zero] }
end

variables (K)

lemma is_primitive.dvd_iff_fraction_map_dvd_fraction_map {p q : polynomial R}
  (hp : p.is_primitive) (hq : q.is_primitive) :
  (p ∣ q) ↔ (p.map (algebra_map R K) ∣ q.map (algebra_map R K)) :=
⟨λ ⟨a,b⟩, ⟨a.map (algebra_map R K), b.symm ▸ map_mul (algebra_map R K)⟩,
  λ h, hp.dvd_of_fraction_map_dvd_fraction_map hq h⟩

end fraction_map

/-- **Gauss's Lemma** for `ℤ` states that a primitive integer polynomial is irreducible iff it is
  irreducible over `ℚ`. -/
theorem is_primitive.int.irreducible_iff_irreducible_map_cast
  {p : polynomial ℤ} (hp : p.is_primitive) :
  irreducible p ↔ irreducible (p.map (int.cast_ring_hom ℚ)) :=
hp.irreducible_iff_irreducible_map_fraction_map

lemma is_primitive.int.dvd_iff_map_cast_dvd_map_cast (p q : polynomial ℤ)
  (hp : p.is_primitive) (hq : q.is_primitive) :
  (p ∣ q) ↔ (p.map (int.cast_ring_hom ℚ) ∣ q.map (int.cast_ring_hom ℚ)) :=
hp.dvd_iff_fraction_map_dvd_fraction_map ℚ hq

end gcd_monoid
end polynomial
