/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import algebra.big_operators.ring
import number_theory.divisors

/-!
# Arithmetic Functions and Dirichlet Convolution

This file defines arithmetic functions, which are functions from `ℕ` to a specified type that map 0
to 0. In the literature, they are often instead defined as functions from `ℕ+`. These arithmetic
functions are endowed with a multiplication, given by Dirichlet convolution, and pointwise addition,
to form the Dirichlet ring.

## Main Definitions
 * `arithmetic_function R` consists of functions `f : ℕ → R` such that `f 0 = 0`.
 * An arithmetic function `f` `is_multiplicative` when `x.coprime y → f (x * y) = f x * f y`.
 * The pointwise operations `pmul` and `ppow` differ from the multiplication
  and power instances on `arithmetic_function R`, which use Dirichlet multiplication.
 * `ζ` is the arithmetic function such that `ζ x = 1` for `0 < x`.
 * `σ k` is the arithmetic function such that `σ k x = ∑ y in divisors x, y ^ k` for `0 < x`.
 * `pow k` is the arithmetic function such that `pow k x = x ^ k` for `0 < x`.
 * `id` is the identity arithmetic function on `ℕ`.

## Notation
The arithmetic functions `ζ` and `σ` have Greek letter names, which are localized notation in
the namespace `arithmetic_function`.

## Tags
arithmetic functions, dirichlet convolution, divisors

-/

open finset
open_locale big_operators

namespace nat
variable (R : Type*)

/-- An arithmetic function is a function from `ℕ` that maps 0 to 0. In the literature, they are
  often instead defined as functions from `ℕ+`. Multiplication on `arithmetic_functions` is by
  Dirichlet convolution. -/
@[derive [has_coe_to_fun, has_zero, inhabited]]
def arithmetic_function [has_zero R] := zero_hom ℕ R

variable {R}

namespace arithmetic_function

section has_zero
variable [has_zero R]

@[simp] lemma to_fun_eq (f : arithmetic_function R) : f.to_fun = f := rfl

@[simp]
lemma map_zero {f : arithmetic_function R} : f 0 = 0 :=
zero_hom.map_zero' f

theorem coe_inj {f g : arithmetic_function R} : (f : ℕ → R) = g ↔ f = g :=
⟨λ h, zero_hom.coe_inj h, λ h, h ▸ rfl⟩

@[simp]
lemma zero_apply {x : ℕ} : (0 : arithmetic_function R) x = 0 :=
zero_hom.zero_apply x

@[ext] theorem ext ⦃f g : arithmetic_function R⦄ (h : ∀ x, f x = g x) : f = g :=
zero_hom.ext h

theorem ext_iff {f g : arithmetic_function R} : f = g ↔ ∀ x, f x = g x :=
zero_hom.ext_iff

section has_one
variable [has_one R]

instance : has_one (arithmetic_function R) := ⟨⟨λ x, ite (x = 1) 1 0, rfl⟩⟩

@[simp]
lemma one_one : (1 : arithmetic_function R) 1 = 1 := rfl

@[simp]
lemma one_apply_ne {x : ℕ} (h : x ≠ 1) : (1 : arithmetic_function R) x = 0 := if_neg h

end has_one
end has_zero

instance nat_coe [semiring R] : has_coe (arithmetic_function ℕ) (arithmetic_function R) :=
⟨λ f, ⟨↑(f : ℕ → ℕ), by { transitivity ↑(f 0), refl, simp }⟩⟩

@[simp]
lemma nat_coe_apply [semiring R] {f : arithmetic_function ℕ} {x : ℕ} :
  (f : arithmetic_function R) x = f x := rfl

instance int_coe [ring R] : has_coe (arithmetic_function ℤ) (arithmetic_function R) :=
⟨λ f, ⟨↑(f : ℕ → ℤ), by { transitivity ↑(f 0), refl, simp }⟩⟩

@[simp]
lemma int_coe_apply [ring R] {f : arithmetic_function ℤ} {x : ℕ} :
  (f : arithmetic_function R) x = f x := rfl

@[simp]
lemma coe_coe [ring R] {f : arithmetic_function ℕ} :
  ((f : arithmetic_function ℤ) : arithmetic_function R) = f :=
by { ext, simp, }

section add_monoid

variable [add_monoid R]

instance : has_add (arithmetic_function R) := ⟨λ f g, ⟨λ n, f n + g n, by simp⟩⟩

@[simp]
lemma add_apply {f g : arithmetic_function R} {n : ℕ} : (f + g) n = f n + g n := rfl

instance : add_monoid (arithmetic_function R) :=
{ add_assoc := λ _ _ _, ext (λ _, add_assoc _ _ _),
  zero_add := λ _, ext (λ _, zero_add _),
  add_zero := λ _, ext (λ _, add_zero _),
  .. arithmetic_function.has_zero R,
  .. arithmetic_function.has_add }

end add_monoid

instance [add_comm_monoid R] : add_comm_monoid (arithmetic_function R) :=
{ add_comm := λ _ _, ext (λ _, add_comm _ _),
  .. arithmetic_function.add_monoid }

instance [add_group R] : add_group (arithmetic_function R) :=
{ neg := λ f, ⟨λ n, - f n, by simp⟩,
  add_left_neg := λ _, ext (λ _, add_left_neg _),
  .. arithmetic_function.add_monoid }

instance [add_comm_group R] : add_comm_group (arithmetic_function R) :=
{ .. arithmetic_function.add_comm_monoid,
  .. arithmetic_function.add_group }

section dirichlet_ring
variable [semiring R]

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
instance : has_mul (arithmetic_function R) :=
⟨λ f g, ⟨λ n, ∑ x in divisors_antidiagonal n, f x.fst * g x.snd, by simp⟩⟩

@[simp]
lemma mul_apply {f g : arithmetic_function R} {n : ℕ} :
  (f * g) n = ∑ x in divisors_antidiagonal n, f x.fst * g x.snd := rfl

instance : monoid (arithmetic_function R) :=
{ one_mul := λ f,
  begin
    ext,
    rw mul_apply,
    by_cases x0 : x = 0, {simp [x0]},
    have h : {(1,x)} ⊆ divisors_antidiagonal x := by simp [x0],
    rw ← sum_subset h, {simp},
    intros y ymem ynmem,
    have y1ne : y.fst ≠ 1,
    { intro con,
      simp only [con, mem_divisors_antidiagonal, one_mul, ne.def] at ymem,
      simp only [mem_singleton, prod.ext_iff] at ynmem,
      tauto },
    simp [y1ne],
  end,
  mul_one := λ f,
  begin
    ext,
    rw mul_apply,
    by_cases x0 : x = 0, {simp [x0]},
    have h : {(x,1)} ⊆ divisors_antidiagonal x := by simp [x0],
    rw ← sum_subset h, {simp},
    intros y ymem ynmem,
    have y2ne : y.snd ≠ 1,
    { intro con,
      simp only [con, mem_divisors_antidiagonal, mul_one, ne.def] at ymem,
      simp only [mem_singleton, prod.ext_iff] at ynmem,
      tauto },
    simp [y2ne],
  end,
  mul_assoc := λ f g h,
  begin
    ext n,
    simp only [mul_apply],
    have := @finset.sum_sigma (ℕ × ℕ) R _ _ (divisors_antidiagonal n)
      (λ p, (divisors_antidiagonal p.1)) (λ x, f x.2.1 * g x.2.2 * h x.1.2),
    convert this.symm using 1; clear this,
    { apply finset.sum_congr rfl,
      intros p hp, exact finset.sum_mul },
    have := @finset.sum_sigma (ℕ × ℕ) R _ _ (divisors_antidiagonal n)
      (λ p, (divisors_antidiagonal p.2)) (λ x, f x.1.1 * (g x.2.1 * h x.2.2)),
    convert this.symm using 1; clear this,
    { apply finset.sum_congr rfl, intros p hp, rw finset.mul_sum },
    apply finset.sum_bij,
    swap 5,
    { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, exact ⟨(k, l*j), (l, j)⟩ },
    { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H,
      simp only [finset.mem_sigma, mem_divisors_antidiagonal] at H ⊢, finish },
    { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, simp only [mul_assoc] },
    { rintros ⟨⟨a,b⟩, ⟨c,d⟩⟩ ⟨⟨i,j⟩, ⟨k,l⟩⟩ H₁ H₂,
      simp only [finset.mem_sigma, mem_divisors_antidiagonal,
        and_imp, prod.mk.inj_iff, add_comm, heq_iff_eq] at H₁ H₂ ⊢,
      finish },
    { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, refine ⟨⟨(i*k, l), (i, k)⟩, _, _⟩;
      { simp only [finset.mem_sigma, mem_divisors_antidiagonal] at H ⊢, finish } }
  end,
  .. arithmetic_function.has_one,
  .. arithmetic_function.has_mul }

instance : semiring (arithmetic_function R) :=
{ zero_mul := λ f, by { ext, simp, },
  mul_zero := λ f, by { ext, simp, },
  left_distrib := λ a b c, by { ext, simp [← sum_add_distrib, mul_add] },
  right_distrib := λ a b c, by { ext, simp [← sum_add_distrib, add_mul] },
  .. arithmetic_function.has_zero R,
  .. arithmetic_function.has_mul,
  .. arithmetic_function.has_add,
  .. arithmetic_function.add_comm_monoid,
  .. arithmetic_function.monoid }

end dirichlet_ring

instance [comm_semiring R] : comm_semiring (arithmetic_function R) :=
{ mul_comm := λ f g, by { ext,
    rw [mul_apply, ← map_swap_divisors_antidiagonal, sum_map],
    simp [mul_comm] },
  .. arithmetic_function.semiring }

instance [comm_ring R] : comm_ring (arithmetic_function R) :=
{ .. arithmetic_function.add_comm_group,
  .. arithmetic_function.comm_semiring }

section zeta

/-- `ζ 0 = 0`, otherwise `ζ x = 1`. The Dirichlet Series is the Riemann ζ.  -/
def zeta [has_zero R] [has_one R] : arithmetic_function R :=
⟨λ x, ite (x = 0) 0 1, rfl⟩

localized "notation `ζ` := zeta" in arithmetic_function

@[simp]
lemma zeta_apply [has_zero R] [has_one R] {x : ℕ} : (ζ x : R) = if (x = 0) then 0 else 1 := rfl

lemma zeta_apply_ne [has_zero R] [has_one R] {x : ℕ} (h : x ≠ 0) : ζ x = (1 : R) := if_neg h

theorem zeta_mul_apply [semiring R] {f : arithmetic_function R} {x : ℕ} :
  (ζ * f) x = ∑ i in divisors x, f i :=
begin
  rw mul_apply,
  transitivity ∑ i in divisors_antidiagonal x, f i.snd,
  { apply sum_congr rfl,
    intros i hi,
    rcases mem_divisors_antidiagonal.1 hi with ⟨rfl, h⟩,
    rw [zeta_apply_ne (left_ne_zero_of_mul h), one_mul] },
  { apply sum_bij (λ i h, prod.snd i),
    { rintros ⟨a, b⟩ h, simp [snd_mem_divisors_of_mem_antidiagonal h] },
    { rintros ⟨a, b⟩ h, refl },
    { rintros ⟨a1, b1⟩ ⟨a2, b2⟩ h1 h2 h,
      dsimp at h,
      rw h at *,
      rw mem_divisors_antidiagonal at *,
      ext, swap, {refl},
      simp only [prod.fst, prod.snd] at *,
      apply nat.eq_of_mul_eq_mul_right _ (eq.trans h1.1 h2.1.symm),
      rcases h1 with ⟨rfl, h⟩,
      apply nat.pos_of_ne_zero (right_ne_zero_of_mul h) },
    { intros a ha,
      rcases mem_divisors.1 ha with ⟨⟨b, rfl⟩, ne0⟩,
      use (b, a),
      simp [ne0, mul_comm] } }
end

theorem mul_zeta_apply [semiring R] {f : arithmetic_function R} {x : ℕ} :
  (f * ζ) x = ∑ i in divisors x, f i :=
begin
  apply opposite.op_injective,
  rw [← opposite.coe_op_add_hom, add_monoid_hom.map_sum],
  convert @zeta_mul_apply Rᵒᵖ _ { to_fun := opposite.op_add_hom ∘ f, map_zero' := by simp} x,
  rw [mul_apply, mul_apply, add_monoid_hom.map_sum],
  conv_lhs { rw ← map_swap_divisors_antidiagonal, },
  rw sum_map,
  apply sum_congr rfl,
  intros y hy,
  by_cases h1 : y.fst = 0,
  { simp [function.comp_apply, h1] },
  { simp only [h1, mul_one, one_mul, prod.fst_swap, function.embedding.coe_fn_mk, prod.snd_swap,
    if_false, zeta_apply, opposite.coe_op_add_hom],
    refl },
  refl
end

end zeta

open_locale arithmetic_function

section pmul

/-- This is the pointwise product of `arithmetic_function`s. -/
def pmul [mul_zero_class R] (f g : arithmetic_function R) :
  arithmetic_function R :=
⟨λ x, f x * g x, by simp⟩

@[simp]
lemma pmul_apply [mul_zero_class R] {f g : arithmetic_function R} {x : ℕ} :
  f.pmul g x = f x * g x := rfl

lemma pmul_comm [comm_monoid_with_zero R] (f g : arithmetic_function R) :
  f.pmul g = g.pmul f :=
by { ext, simp [mul_comm] }

variable [monoid_with_zero R]

@[simp]
lemma pmul_zeta (f : arithmetic_function R) : f.pmul ζ = f :=
begin
  ext x,
  cases x;
  simp [nat.succ_ne_zero],
end

@[simp]
lemma zeta_pmul (f : arithmetic_function R) : (ζ).pmul f = f :=
begin
  ext x,
  cases x;
  simp [nat.succ_ne_zero],
end

/-- This is the pointwise power of `arithmetic_function`s. -/
def ppow (f : arithmetic_function R) (k : ℕ) :
  arithmetic_function R :=
if h0 : k = 0 then ζ else ⟨λ x, (f x) ^ k,
  by { rw [map_zero], exact zero_pow (nat.pos_of_ne_zero h0) }⟩

@[simp]
lemma ppow_zero {f : arithmetic_function R} : f.ppow 0 = ζ :=
by rw [ppow, dif_pos rfl]

@[simp]
lemma ppow_apply {f : arithmetic_function R} {k x : ℕ} (kpos : 0 < k) :
  f.ppow k x = (f x) ^ k :=
by { rw [ppow, dif_neg (ne_of_gt kpos)], refl }

lemma ppow_succ {f : arithmetic_function R} {k : ℕ} :
  f.ppow (k + 1) = f.pmul (f.ppow k) :=
begin
  ext x,
  rw [ppow_apply (nat.succ_pos k), pow_succ],
  induction k; simp,
end

lemma ppow_succ' {f : arithmetic_function R} {k : ℕ} {kpos : 0 < k} :
  f.ppow (k + 1) = (f.ppow k).pmul f :=
begin
  ext x,
  rw [ppow_apply (nat.succ_pos k), pow_succ'],
  induction k; simp,
end

end pmul

/-- Multiplicative functions -/
def is_multiplicative [monoid_with_zero R] (f : arithmetic_function R) : Prop :=
f 1 = 1 ∧ (∀ {m n : ℕ}, m.coprime n → f (m * n) = f m * f n)

namespace is_multiplicative

section monoid_with_zero
variable [monoid_with_zero R]

@[simp]
lemma map_one {f : arithmetic_function R} (h : f.is_multiplicative) : f 1 = 1 :=
h.1

@[simp]
lemma map_mul_of_coprime {f : arithmetic_function R} (hf : f.is_multiplicative)
  {m n : ℕ} (h : m.coprime n) : f (m * n) = f m * f n :=
hf.2 h

end monoid_with_zero

lemma nat_cast {f : arithmetic_function ℕ} [semiring R] (h : f.is_multiplicative) :
  is_multiplicative (f : arithmetic_function R) :=
⟨by simp [h], λ m n cop, by simp [cop, h]⟩

lemma int_cast {f : arithmetic_function ℤ} [ring R] (h : f.is_multiplicative) :
  is_multiplicative (f : arithmetic_function R) :=
⟨by simp [h], λ m n cop, by simp [cop, h]⟩

lemma mul [comm_semiring R] {f g : arithmetic_function R}
  (hf : f.is_multiplicative) (hg : g.is_multiplicative) :
  is_multiplicative (f * g) :=
⟨by { simp [hf, hg], }, begin
  simp only [mul_apply],
  intros m n cop,
  rw sum_mul_sum,
  symmetry,
  apply sum_bij (λ (x : (ℕ × ℕ) × ℕ × ℕ) h, (x.1.1 * x.2.1, x.1.2 * x.2.2)),
  { rintros ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at h,
    rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩,
    simp only [mem_divisors_antidiagonal, nat.mul_eq_zero, ne.def],
    split, {ring},
    rw nat.mul_eq_zero at *,
    apply not_or ha hb },
  { rintros ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at h,
    rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩,
    dsimp only,
    rw [hf.map_mul_of_coprime cop.coprime_mul_right.coprime_mul_right_right,
        hg.map_mul_of_coprime cop.coprime_mul_left.coprime_mul_left_right],
    ring, },
  { rintros ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ hab hcd h,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at hab,
    rcases hab with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at hcd,
    simp only [prod.mk.inj_iff] at h,
    ext; dsimp only,
    { transitivity nat.gcd (a1 * a2) (a1 * b1),
      { rw [nat.gcd_mul_left, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one] },
      { rw [← hcd.1.1, ← hcd.2.1] at cop,
        rw [← hcd.1.1, h.1, nat.gcd_mul_left,
            cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one] } },
    { transitivity nat.gcd (a1 * a2) (a2 * b2),
      { rw [mul_comm, nat.gcd_mul_left, cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one,
            mul_one] },
      { rw [← hcd.1.1, ← hcd.2.1] at cop,
        rw [← hcd.1.1, h.2, mul_comm, nat.gcd_mul_left,
            cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one, mul_one] } },
    { transitivity nat.gcd (b1 * b2) (a1 * b1),
      { rw [mul_comm, nat.gcd_mul_right,
           cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, one_mul] },
      { rw [← hcd.1.1, ← hcd.2.1] at cop,
        rw [← hcd.2.1, h.1, mul_comm c1 d1, nat.gcd_mul_left,
            cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, mul_one] } },
    { transitivity nat.gcd (b1 * b2) (a2 * b2),
      { rw [nat.gcd_mul_right,
           cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul] },
      { rw [← hcd.1.1, ← hcd.2.1] at cop,
        rw [← hcd.2.1, h.2, nat.gcd_mul_right,
            cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul] } } },
  { rintros ⟨b1, b2⟩ h,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at h,
    use ((b1.gcd m, b2.gcd m), (b1.gcd n, b2.gcd n)),
    simp only [exists_prop, prod.mk.inj_iff, ne.def, mem_product, mem_divisors_antidiagonal],
    rw [← cop.gcd_mul _, ← cop.gcd_mul _, ← h.1, nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul cop h.1,
        nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul cop.symm _],
    { rw [nat.mul_eq_zero, decidable.not_or_iff_and_not] at h, simp [h.2.1, h.2.2] },
    rw [mul_comm n m, h.1] }
end⟩

lemma pmul [comm_semiring R] {f g : arithmetic_function R}
  (hf : f.is_multiplicative) (hg : g.is_multiplicative) :
  is_multiplicative (f.pmul g) :=
⟨by { simp [hf, hg], }, λ m n cop, begin
  simp only [pmul_apply, hf.map_mul_of_coprime cop, hg.map_mul_of_coprime cop],
  ring,
end⟩

end is_multiplicative

section special_functions

/-- The identity on `ℕ` as an `arithmetic_function`.  -/
def id : arithmetic_function ℕ := ⟨id, rfl⟩

@[simp]
lemma id_apply {x : ℕ} : id x = x := rfl

/-- `pow k n = n ^ k`, except `pow 0 0 = 0`. -/
def pow (k : ℕ) : arithmetic_function ℕ := id.ppow k

@[simp]
lemma pow_apply {k n : ℕ} : pow k n = if (k = 0 ∧ n = 0) then 0 else n ^ k :=
begin
  cases k,
  { simp [pow] },
  simp [pow, (ne_of_lt (nat.succ_pos k)).symm],
end

/-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
def sigma (k : ℕ) : arithmetic_function ℕ :=
⟨λ n, ∑ d in divisors n, d ^ k, by simp⟩

localized "notation `σ` := sigma" in arithmetic_function

@[simp]
lemma sigma_apply {k n : ℕ} : σ k n = ∑ d in divisors n, d ^ k := rfl

lemma sigma_one_apply {n : ℕ} : σ 1 n = ∑ d in divisors n, d := by simp

lemma zeta_mul_pow_eq_sigma {k : ℕ} : ζ * pow k = σ k :=
begin
  ext,
  rw [sigma, zeta_mul_apply],
  apply sum_congr rfl,
  intros x hx,
  rw [pow_apply, if_neg (not_and_of_not_right _ _)],
  contrapose! hx,
  simp [hx],
end

lemma is_multiplicative_zeta [semiring R] : is_multiplicative (ζ : arithmetic_function R) :=
⟨by simp, λ m n cop, begin
  cases m, {simp},
  cases n, {simp},
  rw [zeta_apply_ne (mul_ne_zero _ _), zeta_apply_ne,
      zeta_apply_ne, mul_one],
  repeat { apply nat.succ_ne_zero },
end⟩

lemma is_multiplicative_id : is_multiplicative arithmetic_function.id :=
⟨rfl, λ _ _ _, rfl⟩

lemma is_multiplicative.ppow [comm_semiring R] {f : arithmetic_function R}
  (hf : f.is_multiplicative) {k : ℕ} :
  is_multiplicative (f.ppow k) :=
begin
  induction k with k hi,
  { exact is_multiplicative_zeta },
  { rw ppow_succ,
    apply hf.pmul hi },
end

lemma is_multiplicative_pow {k : ℕ} : is_multiplicative (pow k) :=
is_multiplicative_id.ppow

lemma is_multiplicative_sigma {k : ℕ} :
  is_multiplicative (sigma k) :=
begin
  rw [← zeta_mul_pow_eq_sigma],
  apply ((is_multiplicative_zeta).mul is_multiplicative_pow)
end

end special_functions
end arithmetic_function
end nat
