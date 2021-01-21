/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes
-/
import data.zsqrtd.basic
import data.complex.basic
import number_theory.quadratic_reciprocity
/-!
# Gaussian integers

The Gaussian integers are complex integer, complex numbers whose real and imaginary parts are both
integers.

## Main definitions

The Euclidean domain structure on `ℤ[i]` is defined in this file.

The homomorphism `to_complex` into the complex numbers is also defined in this file.

## Main statements

`prime_iff_mod_four_eq_three_of_nat_prime`
A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

## Notations

This file uses the local notation `ℤ[i]` for `gaussian_int`

## Implementation notes

Gaussian integers are implemented using the more general definition `zsqrtd`, the type of integers
adjoined a square root of `d`, in this case `-1`. The definition is reducible, so that properties
and definitions about `zsqrtd` can easily be used.
-/

open zsqrtd complex

@[reducible] def gaussian_int : Type := zsqrtd (-1)

local notation `ℤ[i]` := gaussian_int

namespace gaussian_int

instance : has_repr ℤ[i] := ⟨λ x, "⟨" ++ repr x.re ++ ", " ++ repr x.im ++ "⟩"⟩

instance : comm_ring ℤ[i] := zsqrtd.comm_ring

section
local attribute [-instance] complex.field -- Avoid making things noncomputable unnecessarily.

/-- The embedding of the Gaussian integers into the complex numbers, as a ring homomorphism. -/
def to_complex : ℤ[i] →+* ℂ :=
begin
  refine_struct { to_fun := λ x : ℤ[i], (x.re + x.im * I : ℂ), .. };
  intros; apply complex.ext; dsimp; norm_cast; simp; abel
end
end

instance : has_coe (ℤ[i]) ℂ := ⟨to_complex⟩

lemma to_complex_def (x : ℤ[i]) : (x : ℂ) = x.re + x.im * I := rfl

lemma to_complex_def' (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ) = x + y * I := by simp [to_complex_def]

lemma to_complex_def₂ (x : ℤ[i]) : (x : ℂ) = ⟨x.re, x.im⟩ :=
by apply complex.ext; simp [to_complex_def]

@[simp] lemma to_real_re (x : ℤ[i]) : ((x.re : ℤ) : ℝ) = (x : ℂ).re := by simp [to_complex_def]
@[simp] lemma to_real_im (x : ℤ[i]) : ((x.im : ℤ) : ℝ) = (x : ℂ).im := by simp [to_complex_def]
@[simp] lemma to_complex_re (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).re = x := by simp [to_complex_def]
@[simp] lemma to_complex_im (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).im = y := by simp [to_complex_def]
@[simp] lemma to_complex_add (x y : ℤ[i]) : ((x + y : ℤ[i]) : ℂ) = x + y := to_complex.map_add _ _
@[simp] lemma to_complex_mul (x y : ℤ[i]) : ((x * y : ℤ[i]) : ℂ) = x * y := to_complex.map_mul _ _
@[simp] lemma to_complex_one : ((1 : ℤ[i]) : ℂ) = 1 := to_complex.map_one
@[simp] lemma to_complex_zero : ((0 : ℤ[i]) : ℂ) = 0 := to_complex.map_zero
@[simp] lemma to_complex_neg (x : ℤ[i]) : ((-x : ℤ[i]) : ℂ) = -x := to_complex.map_neg _
@[simp] lemma to_complex_sub (x y : ℤ[i]) : ((x - y : ℤ[i]) : ℂ) = x - y := to_complex.map_sub _ _

@[simp] lemma to_complex_inj {x y : ℤ[i]} : (x : ℂ) = y ↔ x = y :=
by cases x; cases y; simp [to_complex_def₂]

@[simp] lemma to_complex_eq_zero {x : ℤ[i]} : (x : ℂ) = 0 ↔ x = 0 :=
by rw [← to_complex_zero, to_complex_inj]

@[simp] lemma nat_cast_real_norm (x : ℤ[i]) : (x.norm : ℝ) = (x : ℂ).norm_sq :=
by rw [norm, norm_sq]; simp

@[simp] lemma nat_cast_complex_norm (x : ℤ[i]) : (x.norm : ℂ) = (x : ℂ).norm_sq :=
by cases x; rw [norm, norm_sq]; simp

lemma norm_nonneg (x : ℤ[i]) : 0 ≤ norm x := norm_nonneg (by norm_num) _

@[simp] lemma norm_eq_zero {x : ℤ[i]} : norm x = 0 ↔ x = 0 :=
by rw [← @int.cast_inj ℝ _ _ _]; simp

lemma norm_pos {x : ℤ[i]} : 0 < norm x ↔ x ≠ 0 :=
by rw [lt_iff_le_and_ne, ne.def, eq_comm, norm_eq_zero]; simp [norm_nonneg]

@[simp] lemma coe_nat_abs_norm (x : ℤ[i]) : (x.norm.nat_abs : ℤ) = x.norm :=
int.nat_abs_of_nonneg (norm_nonneg _)

@[simp] lemma nat_cast_nat_abs_norm {α : Type*} [ring α]
  (x : ℤ[i]) : (x.norm.nat_abs : α) = x.norm :=
by rw [← int.cast_coe_nat, coe_nat_abs_norm]

lemma nat_abs_norm_eq (x : ℤ[i]) : x.norm.nat_abs =
  x.re.nat_abs * x.re.nat_abs + x.im.nat_abs * x.im.nat_abs :=
int.coe_nat_inj $ begin simp, simp [norm] end

protected def div (x y : ℤ[i]) : ℤ[i] :=
let n := (rat.of_int (norm y))⁻¹ in let c := y.conj in
⟨round (rat.of_int (x * c).re * n : ℚ),
 round (rat.of_int (x * c).im * n : ℚ)⟩

instance : has_div ℤ[i] := ⟨gaussian_int.div⟩

lemma div_def (x y : ℤ[i]) : x / y = ⟨round ((x * conj y).re / norm y : ℚ),
  round ((x * conj y).im / norm y : ℚ)⟩ :=
show zsqrtd.mk _ _ = _, by simp [rat.of_int_eq_mk, rat.mk_eq_div, div_eq_mul_inv]

lemma to_complex_div_re (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).re = round ((x / y : ℂ).re) :=
by rw [div_def, ← @rat.cast_round ℝ _ _];
  simp [-rat.cast_round, mul_assoc, div_eq_mul_inv, mul_add, add_mul]

lemma to_complex_div_im (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).im = round ((x / y : ℂ).im) :=
by rw [div_def, ← @rat.cast_round ℝ _ _, ← @rat.cast_round ℝ _ _];
  simp [-rat.cast_round, mul_assoc, div_eq_mul_inv, mul_add, add_mul]

local notation `abs'` := _root_.abs

lemma norm_sq_le_norm_sq_of_re_le_of_im_le {x y : ℂ} (hre : abs' x.re ≤ abs' y.re)
  (him : abs' x.im ≤ abs' y.im) : x.norm_sq ≤ y.norm_sq :=
by rw [norm_sq_apply, norm_sq_apply, ← _root_.abs_mul_self, _root_.abs_mul,
  ← _root_.abs_mul_self y.re, _root_.abs_mul y.re,
  ← _root_.abs_mul_self x.im, _root_.abs_mul x.im,
  ← _root_.abs_mul_self y.im, _root_.abs_mul y.im]; exact
(add_le_add (mul_self_le_mul_self (abs_nonneg _) hre)
  (mul_self_le_mul_self (abs_nonneg _) him))

lemma norm_sq_div_sub_div_lt_one (x y : ℤ[i]) :
  ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)).norm_sq < 1 :=
calc ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)).norm_sq =
    ((x / y : ℂ).re - ((x / y : ℤ[i]) : ℂ).re +
    ((x / y : ℂ).im - ((x / y : ℤ[i]) : ℂ).im) * I : ℂ).norm_sq :
      congr_arg _ $ by apply complex.ext; simp
  ... ≤ (1 / 2 + 1 / 2 * I).norm_sq :
  have abs' (2⁻¹ : ℝ) = 2⁻¹, from _root_.abs_of_nonneg (by norm_num),
  norm_sq_le_norm_sq_of_re_le_of_im_le
    (by rw [to_complex_div_re]; simp [norm_sq, this];
      simpa using abs_sub_round (x / y : ℂ).re)
    (by rw [to_complex_div_im]; simp [norm_sq, this];
      simpa using abs_sub_round (x / y : ℂ).im)
  ... < 1 : by simp [norm_sq]; norm_num

protected def mod (x y : ℤ[i]) : ℤ[i] := x - y * (x / y)

instance : has_mod ℤ[i] := ⟨gaussian_int.mod⟩

lemma mod_def (x y : ℤ[i]) : x % y = x - y * (x / y) := rfl

lemma norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (x % y).norm < y.norm :=
have (y : ℂ) ≠ 0, by rwa [ne.def, ← to_complex_zero, to_complex_inj],
(@int.cast_lt ℝ _ _ _ _).1 $
  calc ↑(norm (x % y)) = (x - y * (x / y : ℤ[i]) : ℂ).norm_sq : by simp [mod_def]
  ... = (y : ℂ).norm_sq * (((x / y) - (x / y : ℤ[i])) : ℂ).norm_sq :
    by rw [← norm_sq_mul, mul_sub, mul_div_cancel' _ this]
  ... < (y : ℂ).norm_sq * 1 : mul_lt_mul_of_pos_left (norm_sq_div_sub_div_lt_one _ _)
    (norm_sq_pos.2 this)
  ... = norm y : by simp

lemma nat_abs_norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) :
  (x % y).norm.nat_abs < y.norm.nat_abs :=
int.coe_nat_lt.1 (by simp [-int.coe_nat_lt, norm_mod_lt x hy])

lemma norm_le_norm_mul_left (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) :
  (norm x).nat_abs ≤ (norm (x * y)).nat_abs :=
by rw [norm_mul, int.nat_abs_mul];
  exact le_mul_of_one_le_right (nat.zero_le _)
    (int.coe_nat_le.1 (by rw [coe_nat_abs_norm]; exact int.add_one_le_of_lt (norm_pos.2 hy)))

instance : nontrivial ℤ[i] :=
⟨⟨0, 1, dec_trivial⟩⟩

instance : euclidean_domain ℤ[i] :=
{ quotient := (/),
  remainder := (%),
  quotient_zero := λ _, by simp [div_def]; refl,
  quotient_mul_add_remainder_eq := λ _ _, by simp [mod_def],
  r := _,
  r_well_founded := measure_wf (int.nat_abs ∘ norm),
  remainder_lt := nat_abs_norm_mod_lt,
  mul_left_not_lt := λ a b hb0, not_lt_of_ge $ norm_le_norm_mul_left a hb0,
  .. gaussian_int.comm_ring,
  .. gaussian_int.nontrivial }

open principal_ideal_ring

lemma mod_four_eq_three_of_nat_prime_of_prime (p : ℕ) [hp : fact p.prime] (hpi : prime (p : ℤ[i])) :
  p % 4 = 3 :=
hp.eq_two_or_odd.elim
  (λ hp2, absurd hpi (mt irreducible_iff_prime.2 $
    λ ⟨hu, h⟩, begin
      have := h ⟨1, 1⟩ ⟨1, -1⟩ (hp2.symm ▸ rfl),
      rw [← norm_eq_one_iff, ← norm_eq_one_iff] at this,
      exact absurd this dec_trivial
    end))
  (λ hp1, by_contradiction $ λ hp3 : p % 4 ≠ 3,
    have hp41 : p % 4 = 1,
      begin
        rw [← nat.mod_mul_left_mod p 2 2, show 2 * 2 = 4, from rfl] at hp1,
        have := nat.mod_lt p (show 0 < 4, from dec_trivial),
        revert this hp3 hp1,
        generalize : p % 4 = m, dec_trivial!,
      end,
    let ⟨k, hk⟩ := (zmod.exists_pow_two_eq_neg_one_iff_mod_four_ne_three p).2 $
      by rw hp41; exact dec_trivial in
    begin
      obtain ⟨k, k_lt_p, rfl⟩ : ∃ (k' : ℕ) (h : k' < p), (k' : zmod p) = k,
      { refine ⟨k.val, k.val_lt, zmod.cast_val k⟩ },
      have hpk : p ∣ k ^ 2 + 1,
        by rw [← char_p.cast_eq_zero_iff (zmod p) p]; simp *,
      have hkmul : (k ^ 2 + 1 : ℤ[i]) = ⟨k, 1⟩ * ⟨k, -1⟩ :=
        by simp [pow_two, zsqrtd.ext],
      have hpne1 : p ≠ 1, from (ne_of_lt (hp.one_lt)).symm,
      have hkltp : 1 + k * k < p * p,
        from calc 1 + k * k ≤ k + k * k :
          add_le_add_right (nat.pos_of_ne_zero
            (λ hk0, by clear_aux_decl; simp [*, pow_succ'] at *)) _
        ... = k * (k + 1) : by simp [add_comm, mul_add]
        ... < p * p : mul_lt_mul k_lt_p k_lt_p (nat.succ_pos _) (nat.zero_le _),
      have hpk₁ : ¬ (p : ℤ[i]) ∣ ⟨k, -1⟩ :=
        λ ⟨x, hx⟩, lt_irrefl (p * x : ℤ[i]).norm.nat_abs $
          calc (norm (p * x : ℤ[i])).nat_abs = (norm ⟨k, -1⟩).nat_abs : by rw hx
          ... < (norm (p : ℤ[i])).nat_abs : by simpa [add_comm, norm] using hkltp
          ... ≤ (norm (p * x : ℤ[i])).nat_abs : norm_le_norm_mul_left _
            (λ hx0, (show (-1 : ℤ) ≠ 0, from dec_trivial) $
              by simpa [hx0] using congr_arg zsqrtd.im hx),
      have hpk₂ : ¬ (p : ℤ[i]) ∣ ⟨k, 1⟩ :=
        λ ⟨x, hx⟩, lt_irrefl (p * x : ℤ[i]).norm.nat_abs $
          calc (norm (p * x : ℤ[i])).nat_abs = (norm ⟨k, 1⟩).nat_abs : by rw hx
          ... < (norm (p : ℤ[i])).nat_abs : by simpa [add_comm, norm] using hkltp
          ... ≤ (norm (p * x : ℤ[i])).nat_abs : norm_le_norm_mul_left _
            (λ hx0, (show (1 : ℤ) ≠ 0, from dec_trivial) $
                by simpa [hx0] using congr_arg zsqrtd.im hx),
      have hpu : ¬ is_unit (p : ℤ[i]), from mt norm_eq_one_iff.2
        (by rw [norm_nat_cast, int.nat_abs_mul, nat.mul_eq_one_iff];
        exact λ h, (ne_of_lt hp.one_lt).symm h.1),
      obtain ⟨y, hy⟩ := hpk,
      have := hpi.2.2 ⟨k, 1⟩ ⟨k, -1⟩ ⟨y, by rw [← hkmul, ← nat.cast_mul p, ← hy]; simp⟩,
      clear_aux_decl, tauto
    end)

lemma sum_two_squares_of_nat_prime_of_not_irreducible (p : ℕ) [hp : fact p.prime]
  (hpi : ¬irreducible (p : ℤ[i])) : ∃ a b, a^2 + b^2 = p :=
have hpu : ¬ is_unit (p : ℤ[i]), from mt norm_eq_one_iff.2 $
  by rw [norm_nat_cast, int.nat_abs_mul, nat.mul_eq_one_iff];
    exact λ h, (ne_of_lt hp.one_lt).symm h.1,
have hab : ∃ a b, (p : ℤ[i]) = a * b ∧ ¬ is_unit a ∧ ¬ is_unit b,
  by simpa [irreducible, hpu, not_forall, not_or_distrib] using hpi,
let ⟨a, b, hpab, hau, hbu⟩ := hab in
have hnap : (norm a).nat_abs = p, from ((hp.mul_eq_prime_pow_two_iff
    (mt norm_eq_one_iff.1 hau) (mt norm_eq_one_iff.1 hbu)).1 $
  by rw [← int.coe_nat_inj', int.coe_nat_pow, pow_two,
    ← @norm_nat_cast (-1), hpab];
    simp).1,
⟨a.re.nat_abs, a.im.nat_abs, by simpa [nat_abs_norm_eq, pow_two] using hnap⟩

lemma prime_of_nat_prime_of_mod_four_eq_three (p : ℕ) [hp : fact p.prime] (hp3 : p % 4 = 3) :
  prime (p : ℤ[i]) :=
irreducible_iff_prime.1 $ classical.by_contradiction $ λ hpi,
  let ⟨a, b, hab⟩ := sum_two_squares_of_nat_prime_of_not_irreducible p hpi in
have ∀ a b : zmod 4, a^2 + b^2 ≠ p, by erw [← zmod.cast_mod_nat 4 p, hp3]; exact dec_trivial,
this a b (hab ▸ by simp)

/-- A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4` -/
lemma prime_iff_mod_four_eq_three_of_nat_prime (p : ℕ) [hp : fact p.prime] :
  prime (p : ℤ[i]) ↔ p % 4 = 3 :=
⟨mod_four_eq_three_of_nat_prime_of_prime p, prime_of_nat_prime_of_mod_four_eq_three p⟩

end gaussian_int
