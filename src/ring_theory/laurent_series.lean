/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import ring_theory.hahn_series
import ring_theory.localization

/-!
# Laurent Series

## Main Definitions
* Defines `laurent_series` as an abbreviation for `hahn_series ℤ`.
* Provides a coercion `power_series R` into `laurent_series R` given by
  `hahn_series.of_power_series`.
* Defines `laurent_series.power_series_part`
* Defines the localization map `laurent_series.of_power_series_localization` which evaluates to
  `hahn_series.of_power_series`.

-/

open hahn_series
open_locale big_operators classical
noncomputable theory

/-- A `laurent_series` is implemented as a `hahn_series` with value group `ℤ`. -/
abbreviation laurent_series (R : Type*) [has_zero R] := hahn_series ℤ R

variables {R : Type*}

namespace laurent_series

section semiring
variable [semiring R]

instance : has_coe (power_series R) (laurent_series R) :=
⟨hahn_series.of_power_series ℤ R⟩

lemma coe_power_series (x : power_series R) : (x : laurent_series R) =
  hahn_series.of_power_series ℤ R x := rfl

@[simp] lemma coeff_coe_power_series (x : power_series R) (n : ℕ) :
  hahn_series.coeff (x : laurent_series R) n = power_series.coeff R n x :=
by rw [← int.nat_cast_eq_coe_nat, coe_power_series, of_power_series_apply_coeff]

/-- This is a power series that can be multiplied by an integer power of `X` to give our
  Laurent series. If the Laurent series is nonzero, `power_series_part` has a nonzero
  constant term.  -/
def power_series_part (x : laurent_series R) : power_series R :=
power_series.mk (λ n, x.coeff (x.order + n))

@[simp] lemma power_series_part_coeff (x : laurent_series R) (n : ℕ) :
  power_series.coeff R n x.power_series_part = x.coeff (x.order + n) :=
power_series.coeff_mk _ _

@[simp] lemma power_series_part_zero : power_series_part (0 : laurent_series R) = 0 :=
by { ext, simp }

@[simp] lemma power_series_part_eq_zero (x : laurent_series R) :
  x.power_series_part = 0 ↔ x = 0 :=
begin
  split,
  { contrapose!,
    intro h,
    rw [power_series.ext_iff, not_forall],
    refine ⟨0, _⟩,
    simp [coeff_order_ne_zero h] },
  { rintro rfl,
    simp }
end

@[simp] lemma single_order_mul_power_series_part (x : laurent_series R) :
  (single x.order 1 : laurent_series R) * x.power_series_part = x :=
begin
  ext n,
  rw [← sub_add_cancel n x.order, single_mul_coeff_add, sub_add_cancel, one_mul],
  by_cases h : x.order ≤ n,
  { rw [int.eq_nat_abs_of_zero_le (sub_nonneg_of_le h), coeff_coe_power_series,
      power_series_part_coeff, ← int.eq_nat_abs_of_zero_le (sub_nonneg_of_le h),
      add_sub_cancel'_right] },
  { rw [coe_power_series, of_power_series_apply, emb_domain_notin_range],
    { contrapose! h,
      exact order_le_of_coeff_ne_zero h.symm },
    { contrapose! h,
      simp only [set.mem_range, rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk,
        int.nat_cast_eq_coe_nat] at h,
      obtain ⟨m, hm⟩ := h,
      rw [← sub_nonneg, ← hm],
      exact int.zero_le_of_nat _ } }
end

lemma of_power_series_power_series_part (x : laurent_series R) :
  of_power_series ℤ R x.power_series_part = single (-x.order) 1 * x :=
begin
  refine eq.trans _ (congr rfl x.single_order_mul_power_series_part),
  rw [← mul_assoc, single_mul_single, neg_add_self, mul_one, ← C_apply, C_one, one_mul,
    coe_power_series],
end

@[simp] lemma of_power_series_X :
  of_power_series ℤ R power_series.X = single 1 1 :=
begin
  ext n,
  cases n,
  { rw [int.of_nat_eq_coe, ← int.nat_cast_eq_coe_nat, of_power_series_apply_coeff],
    by_cases h1 : n = 1,
    { simp [h1] },
    { rw [power_series.coeff_X, single_coeff, if_neg h1, if_neg],
      contrapose! h1,
      rw [← nat.cast_one] at h1,
      exact nat.cast_injective h1 } },
  { rw [of_power_series_apply, emb_domain_notin_range, single_coeff_of_ne],
    { dec_trivial },
    rw [set.mem_range, not_exists],
    intro m,
    simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk, int.nat_cast_eq_coe_nat],
    dec_trivial }
end

end semiring

@[simp] lemma of_power_series_X_pow [comm_semiring R] (n : ℕ) :
  of_power_series ℤ R (power_series.X ^ n) = single (n : ℤ) 1 :=
begin
  rw ring_hom.map_pow,
  induction n with n ih,
  { refl },
  rw [pow_succ, int.coe_nat_succ, ih, of_power_series_X, mul_comm, single_mul_single, one_mul],
end

instance [comm_semiring R] : algebra (power_series R) (laurent_series R) :=
(hahn_series.of_power_series ℤ R).to_algebra

@[simp] lemma coe_algebra_map [comm_semiring R] :
  ⇑(algebra_map (power_series R) (laurent_series R)) = hahn_series.of_power_series ℤ R :=
rfl

/-- The localization map from power series to Laurent series. -/
@[simps] instance of_power_series_localization [comm_ring R] :
  is_localization (submonoid.powers (power_series.X : power_series R)) (laurent_series R) :=
{ map_units := (begin rintro ⟨_, n, rfl⟩,
    refine ⟨⟨single (n : ℤ) 1, single (-n : ℤ) 1, _, _⟩, _⟩,
    { simp only [single_mul_single, mul_one, add_right_neg],
      refl },
    { simp only [single_mul_single, mul_one, add_left_neg],
      refl },
    { simp } end),
 surj := (begin intro z,
    by_cases h : 0 ≤ z.order,
    { refine ⟨⟨power_series.X ^ (int.nat_abs z.order) * power_series_part z, 1⟩, _⟩,
      simp only [ring_hom.map_one, mul_one, ring_hom.map_mul, coe_algebra_map,
        of_power_series_X_pow, submonoid.coe_one],
      rw [int.nat_abs_of_nonneg h, ← coe_power_series, single_order_mul_power_series_part] },
    { refine ⟨⟨power_series_part z, power_series.X ^ (int.nat_abs z.order), ⟨_, rfl⟩⟩, _⟩,
      simp only [coe_algebra_map, of_power_series_power_series_part],
      rw [mul_comm _ z],
      refine congr rfl _,
      rw [subtype.coe_mk, of_power_series_X_pow, int.of_nat_nat_abs_of_nonpos],
      exact le_of_not_ge h } end),
  eq_iff_exists := (begin intros x y,
    rw [coe_algebra_map, of_power_series_injective.eq_iff],
    split,
    { rintro rfl,
      exact ⟨1, rfl⟩ },
    { rintro ⟨⟨_, n, rfl⟩, hc⟩,
      rw [← sub_eq_zero, ← sub_mul, power_series.ext_iff] at hc,
      rw [← sub_eq_zero, power_series.ext_iff],
      intro m,
      have h := hc (m + n),
      rw [linear_map.map_zero, subtype.coe_mk, power_series.X_pow_eq, power_series.monomial,
        power_series.coeff, finsupp.single_add, mv_power_series.coeff_add_mul_monomial,
        mul_one] at h,
      exact h } end) }

end laurent_series
