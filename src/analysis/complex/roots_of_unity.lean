/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.roots_of_unity
import analysis.special_functions.pow

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `e ^ (2 * real.pi * complex.I * (i / n))` for `i ∈ finset.range n`.

## Main declarations

* `complex.mem_roots_of_unity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`.
* `complex.card_roots_of_unity`: the number of `n`-th roots of unity is exactly `n`.

-/

namespace complex

open polynomial real
open_locale nat

lemma is_primitive_root_exp_of_coprime (i n : ℕ) (h0 : n ≠ 0) (hi : i.coprime n) :
  is_primitive_root (exp (2 * pi * I * (i / n))) n :=
begin
  rw is_primitive_root.iff_def,
  simp only [← exp_nat_mul, exp_eq_one_iff],
  have hn0 : (n : ℂ) ≠ 0, by exact_mod_cast h0,
  split,
  { use i,
    field_simp [hn0, mul_comm (i : ℂ), mul_comm (n : ℂ)] },
  { simp only [hn0, mul_right_comm _ _ ↑n, mul_left_inj' two_pi_I_ne_zero, ne.def, not_false_iff,
      mul_comm _ (i : ℂ), ← mul_assoc _ (i : ℂ), exists_imp_distrib] with field_simps,
    norm_cast,
    rintro l k hk,
    have : n ∣ i * l,
    { rw [← int.coe_nat_dvd, hk], apply dvd_mul_left },
    exact hi.symm.dvd_of_dvd_mul_left this }
end

lemma is_primitive_root_exp (n : ℕ) (h0 : n ≠ 0) : is_primitive_root (exp (2 * pi * I / n)) n :=
by simpa only [nat.cast_one, one_div]
  using is_primitive_root_exp_of_coprime 1 n h0 n.coprime_one_left

lemma is_primitive_root_iff (ζ : ℂ) (n : ℕ) (hn : n ≠ 0) :
  is_primitive_root ζ n ↔ (∃ (i < (n : ℕ)) (hi : i.coprime n), exp (2 * pi * I * (i / n)) = ζ) :=
begin
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn,
  split, swap,
  { rintro ⟨i, -, hi, rfl⟩, exact is_primitive_root_exp_of_coprime i n hn hi },
  intro h,
  obtain ⟨i, hi, rfl⟩ :=
    (is_primitive_root_exp n hn).eq_pow_of_pow_eq_one h.pow_eq_one (nat.pos_of_ne_zero hn),
  refine ⟨i, hi, ((is_primitive_root_exp n hn).pow_iff_coprime (nat.pos_of_ne_zero hn) i).mp h, _⟩,
  rw [← exp_nat_mul],
  congr' 1,
  field_simp [hn0, mul_comm (i : ℂ)]
end

/-- The complex `n`-th roots of unity are exactly the
complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`. -/
lemma mem_roots_of_unity (n : ℕ+) (x : units ℂ) :
  x ∈ roots_of_unity n ℂ ↔ (∃ i < (n : ℕ), exp (2 * pi * I * (i / n)) = x) :=
begin
  rw [mem_roots_of_unity, units.ext_iff, units.coe_pow, units.coe_one],
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (n.ne_zero),
  split,
  { intro h,
    obtain ⟨i, hi, H⟩ : ∃ i < (n : ℕ), exp (2 * pi * I / n) ^ i = x,
    { simpa only using (is_primitive_root_exp n n.ne_zero).eq_pow_of_pow_eq_one h n.pos },
    refine ⟨i, hi, _⟩,
    rw [← H, ← exp_nat_mul],
    congr' 1,
    field_simp [hn0, mul_comm (i : ℂ)] },
  { rintro ⟨i, hi, H⟩,
    rw [← H, ← exp_nat_mul, exp_eq_one_iff],
    use i,
    field_simp [hn0, mul_comm ((n : ℕ) : ℂ), mul_comm (i : ℂ)] }
end

lemma card_roots_of_unity (n : ℕ+) : fintype.card (roots_of_unity n ℂ) = n :=
(is_primitive_root_exp n n.ne_zero).card_roots_of_unity

lemma card_primitive_roots (k : ℕ) (h : k ≠ 0) : (primitive_roots k ℂ).card = φ k :=
(is_primitive_root_exp k h).card_primitive_roots (nat.pos_of_ne_zero h)

end complex
