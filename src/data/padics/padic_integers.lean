/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro, Johan Commelin
-/
import data.zmod.basic
import linear_algebra.adic_completion
import data.padics.padic_numbers
import ring_theory.discrete_valuation_ring
import topology.metric_space.cau_seq_filter

/-!
# p-adic integers

This file defines the p-adic integers `ℤ_p` as the subtype of `ℚ_p` with norm `≤ 1`.
We show that `ℤ_p`
* is complete
* is nonarchimedean
* is a normed ring
* is a local ring
* is a discrete valuation ring

The relation between `ℤ_[p]` and `zmod p` is established in another file.

## Important definitions

* `padic_int` : the type of p-adic numbers

## Notation

We introduce the notation `ℤ_[p]` for the p-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact (nat.prime p)] as a type class argument.

Coercions into `ℤ_p` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouêva, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/

open nat padic metric local_ring
noncomputable theory
open_locale classical

/-- The p-adic integers ℤ_p are the p-adic numbers with norm ≤ 1. -/
def padic_int (p : ℕ) [fact p.prime] := {x : ℚ_[p] // ∥x∥ ≤ 1}
notation `ℤ_[`p`]` := padic_int p

namespace padic_int
/-! ### Ring structure and coercion to `ℚ_[p]` -/
variables {p : ℕ} [fact p.prime]

instance : has_coe ℤ_[p] ℚ_[p] := ⟨subtype.val⟩

lemma ext {x y : ℤ_[p]} : (x : ℚ_[p]) = y → x = y := subtype.ext_iff_val.2

/-- Addition on ℤ_p is inherited from ℚ_p. -/
instance : has_add ℤ_[p] :=
⟨λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x+y,
    le_trans (padic_norm_e.nonarchimedean _ _) (max_le_iff.2 ⟨hx,hy⟩)⟩⟩

/-- Multiplication on ℤ_p is inherited from ℚ_p. -/
instance : has_mul ℤ_[p] :=
⟨λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x*y,
    begin rw padic_norm_e.mul, apply mul_le_one; {assumption <|> apply norm_nonneg} end⟩⟩

/-- Negation on ℤ_p is inherited from ℚ_p. -/
instance : has_neg ℤ_[p] :=
⟨λ ⟨x, hx⟩, ⟨-x, by simpa⟩⟩

/-- Subtraction on ℤ_p is inherited from ℚ_p. -/
instance : has_sub ℤ_[p] :=
⟨λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x - y,
  by { rw sub_eq_add_neg, rw ← norm_neg at hy,
       exact le_trans (padic_norm_e.nonarchimedean _ _) (max_le_iff.2 ⟨hx, hy⟩) }⟩⟩

/-- Zero on ℤ_p is inherited from ℚ_p. -/
instance : has_zero ℤ_[p] :=
⟨⟨0, by norm_num⟩⟩

instance : inhabited ℤ_[p] := ⟨0⟩

/-- One on ℤ_p is inherited from ℚ_p. -/
instance : has_one ℤ_[p] :=
⟨⟨1, by norm_num⟩⟩

@[simp] lemma mk_zero {h} : (⟨0, h⟩ : ℤ_[p]) = (0 : ℤ_[p]) := rfl

@[simp] lemma val_eq_coe (z : ℤ_[p]) : z.val = z := rfl

@[simp, norm_cast] lemma coe_add : ∀ (z1 z2 : ℤ_[p]), ((z1 + z2 : ℤ_[p]) : ℚ_[p]) = z1 + z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp, norm_cast] lemma coe_mul : ∀ (z1 z2 : ℤ_[p]), ((z1 * z2 : ℤ_[p]) : ℚ_[p]) = z1 * z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp, norm_cast] lemma coe_neg : ∀ (z1 : ℤ_[p]), ((-z1 : ℤ_[p]) : ℚ_[p]) = -z1
| ⟨_, _⟩ := rfl

@[simp, norm_cast] lemma coe_sub : ∀ (z1 z2 : ℤ_[p]), ((z1 - z2 : ℤ_[p]) : ℚ_[p]) = z1 - z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp, norm_cast] lemma coe_one : ((1 : ℤ_[p]) : ℚ_[p]) = 1 := rfl

@[simp, norm_cast] lemma coe_coe : ∀ n : ℕ, ((n : ℤ_[p]) : ℚ_[p]) = n
| 0 := rfl
| (k+1) := by simp [coe_coe]


@[simp, norm_cast] lemma coe_coe_int : ∀ (z : ℤ), ((z : ℤ_[p]) : ℚ_[p]) = z
| (int.of_nat n) := by simp
| -[1+n] := by simp

@[simp, norm_cast] lemma coe_zero : ((0 : ℤ_[p]) : ℚ_[p]) = 0 := rfl

instance : ring ℤ_[p] :=
begin
  refine { add := (+),
           mul := (*),
           neg := has_neg.neg,
           zero := 0,
           one := 1,
           sub := has_sub.sub,
           sub_eq_add_neg := _,
           .. };
  intros; ext; simp; ring
end

/-- The coercion from ℤ[p] to ℚ[p] as a ring homomorphism. -/
def coe.ring_hom : ℤ_[p] →+* ℚ_[p]  :=
{ to_fun := (coe : ℤ_[p] → ℚ_[p]),
  map_zero' := rfl,
  map_one' := rfl,
  map_mul' := coe_mul,
  map_add' := coe_add }

@[simp, norm_cast] lemma coe_pow (x : ℤ_[p]) (n : ℕ) : (↑(x^n) : ℚ_[p]) = (↑x : ℚ_[p])^n :=
coe.ring_hom.map_pow x n

@[simp] lemma mk_coe : ∀ (k : ℤ_[p]), (⟨k, k.2⟩ : ℤ_[p]) = k
| ⟨_, _⟩ := rfl

/-- The inverse of a p-adic integer with norm equal to 1 is also a p-adic integer. Otherwise, the
inverse is defined to be 0. -/
def inv : ℤ_[p] → ℤ_[p]
| ⟨k, _⟩ := if h : ∥k∥ = 1 then ⟨1/k, by simp [h]⟩ else 0

instance : char_zero ℤ_[p] :=
{ cast_injective :=
  λ m n h, cast_injective $
  show (m:ℚ_[p]) = n, by { rw subtype.ext_iff at h, norm_cast at h, exact h } }

@[simp, norm_cast] lemma coe_int_eq (z1 z2 : ℤ) : (z1 : ℤ_[p]) = z2 ↔ z1 = z2 :=
suffices (z1 : ℚ_[p]) = z2 ↔ z1 = z2, from iff.trans (by norm_cast) this,
by norm_cast

/--
A sequence of integers that is Cauchy with respect to the `p`-adic norm
converges to a `p`-adic integer.
-/
def of_int_seq (seq : ℕ → ℤ) (h : is_cau_seq (padic_norm p) (λ n, seq n)) : ℤ_[p] :=
⟨⟦⟨_, h⟩⟧,
 show ↑(padic_seq.norm _) ≤ (1 : ℝ), begin
   rw padic_seq.norm,
   split_ifs with hne; norm_cast,
   { exact zero_le_one },
   { apply padic_norm.of_int }
 end ⟩

end padic_int

namespace padic_int
/-!
### Instances

We now show that `ℤ_[p]` is a
* complete metric space
* normed ring
* integral domain
-/

variables (p : ℕ) [fact p.prime]

instance : metric_space ℤ_[p] := subtype.metric_space

instance complete_space : complete_space ℤ_[p] :=
begin
  delta padic_int,
  rw [complete_space_iff_is_complete_range uniform_embedding_subtype_coe,
    subtype.range_coe_subtype],
  have : is_complete (closed_ball (0 : ℚ_[p]) 1) := is_closed_ball.is_complete,
  simpa [closed_ball],
end

instance : has_norm ℤ_[p] := ⟨λ z, ∥(z : ℚ_[p])∥⟩

variables {p}

protected lemma mul_comm : ∀ z1 z2 : ℤ_[p], z1*z2 = z2*z1
| ⟨q1, h1⟩ ⟨q2, h2⟩ := show (⟨q1*q2, _⟩ : ℤ_[p]) = ⟨q2*q1, _⟩, by simp [_root_.mul_comm]

protected lemma zero_ne_one : (0 : ℤ_[p]) ≠ 1 :=
show (⟨(0 : ℚ_[p]), _⟩ : ℤ_[p]) ≠ ⟨(1 : ℚ_[p]), _⟩, from mt subtype.ext_iff_val.1 zero_ne_one

protected lemma eq_zero_or_eq_zero_of_mul_eq_zero :
          ∀ (a b : ℤ_[p]), a * b = 0 → a = 0 ∨ b = 0
| ⟨a, ha⟩ ⟨b, hb⟩ := λ h : (⟨a * b, _⟩ : ℤ_[p]) = ⟨0, _⟩,
have a * b = 0, from subtype.ext_iff_val.1 h,
(mul_eq_zero.1 this).elim
  (λ h1, or.inl (by simp [h1]; refl))
  (λ h2, or.inr (by simp [h2]; refl))

lemma norm_def {z : ℤ_[p]} : ∥z∥ = ∥(z : ℚ_[p])∥ := rfl

variables (p)

instance : normed_comm_ring ℤ_[p] :=
{ dist_eq := λ ⟨_, _⟩ ⟨_, _⟩, rfl,
  norm_mul := λ ⟨_, _⟩ ⟨_, _⟩, norm_mul_le _ _,
  mul_comm := padic_int.mul_comm }

instance : norm_one_class ℤ_[p] := ⟨norm_def.trans norm_one⟩

instance is_absolute_value : is_absolute_value (λ z : ℤ_[p], ∥z∥) :=
{ abv_nonneg := norm_nonneg,
  abv_eq_zero := λ ⟨_, _⟩, by simp [norm_eq_zero],
  abv_add := λ ⟨_,_⟩ ⟨_, _⟩, norm_add_le _ _,
  abv_mul := λ _ _, by simp only [norm_def, padic_norm_e.mul, padic_int.coe_mul]}

variables {p}

instance : integral_domain ℤ_[p] :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y, padic_int.eq_zero_or_eq_zero_of_mul_eq_zero x y,
  exists_pair_ne := ⟨0, 1, padic_int.zero_ne_one⟩,
  .. padic_int.normed_comm_ring p }

end padic_int

namespace padic_int
/-! ### Norm -/
variables {p : ℕ} [fact p.prime]

lemma norm_le_one : ∀ z : ℤ_[p], ∥z∥ ≤ 1
| ⟨_, h⟩ := h

@[simp] lemma norm_mul (z1 z2 : ℤ_[p]) : ∥z1 * z2∥ = ∥z1∥ * ∥z2∥ :=
by simp [norm_def]

@[simp] lemma norm_pow (z : ℤ_[p]) : ∀ n : ℕ, ∥z^n∥ = ∥z∥^n
| 0 := by simp
| (k+1) := show ∥z*z^k∥ = ∥z∥*∥z∥^k, by {rw norm_mul, congr, apply norm_pow}

theorem nonarchimedean : ∀ (q r : ℤ_[p]), ∥q + r∥ ≤ max (∥q∥) (∥r∥)
| ⟨_, _⟩ ⟨_, _⟩ := padic_norm_e.nonarchimedean _ _

theorem norm_add_eq_max_of_ne : ∀ {q r : ℤ_[p]}, ∥q∥ ≠ ∥r∥ → ∥q+r∥ = max (∥q∥) (∥r∥)
| ⟨_, _⟩ ⟨_, _⟩ := padic_norm_e.add_eq_max_of_ne

lemma norm_eq_of_norm_add_lt_right {z1 z2 : ℤ_[p]}
  (h : ∥z1 + z2∥ < ∥z2∥) : ∥z1∥ = ∥z2∥ :=
by_contradiction $ λ hne,
  not_lt_of_ge (by rw norm_add_eq_max_of_ne hne; apply le_max_right) h

lemma norm_eq_of_norm_add_lt_left {z1 z2 : ℤ_[p]}
  (h : ∥z1 + z2∥ < ∥z1∥) : ∥z1∥ = ∥z2∥ :=
by_contradiction $ λ hne,
  not_lt_of_ge (by rw norm_add_eq_max_of_ne hne; apply le_max_left) h

@[simp] lemma padic_norm_e_of_padic_int (z : ℤ_[p]) : ∥(↑z : ℚ_[p])∥ = ∥z∥ :=
by simp [norm_def]

lemma norm_int_cast_eq_padic_norm (z : ℤ) : ∥(z : ℤ_[p])∥ = ∥(z : ℚ_[p])∥ :=
by simp [norm_def]

@[simp] lemma norm_eq_padic_norm {q : ℚ_[p]} (hq : ∥q∥ ≤ 1) :
  @norm ℤ_[p] _ ⟨q, hq⟩ = ∥q∥ := rfl

@[simp] lemma norm_p : ∥(p : ℤ_[p])∥ = p⁻¹ :=
show ∥((p : ℤ_[p]) : ℚ_[p])∥ = p⁻¹, by exact_mod_cast padic_norm_e.norm_p

@[simp] lemma norm_p_pow (n : ℕ) : ∥(p : ℤ_[p])^n∥ = p^(-n:ℤ) :=
show ∥((p^n : ℤ_[p]) : ℚ_[p])∥ = p^(-n:ℤ),
by { convert padic_norm_e.norm_p_pow n, simp, }

private def cau_seq_to_rat_cau_seq (f : cau_seq ℤ_[p] norm) :
  cau_seq ℚ_[p] (λ a, ∥a∥) :=
⟨ λ n, f n,
  λ _ hε, by simpa [norm, norm_def] using f.cauchy hε ⟩

variables (p)

instance complete : cau_seq.is_complete ℤ_[p] norm :=
⟨ λ f,
  have hqn : ∥cau_seq.lim (cau_seq_to_rat_cau_seq f)∥ ≤ 1,
    from padic_norm_e_lim_le zero_lt_one (λ _, norm_le_one _),
  ⟨ ⟨_, hqn⟩,
    λ ε, by simpa [norm, norm_def] using cau_seq.equiv_lim (cau_seq_to_rat_cau_seq f) ε⟩⟩

end padic_int

namespace padic_int

variables (p : ℕ) [hp_prime : fact p.prime]
include hp_prime

lemma exists_pow_neg_lt {ε : ℝ} (hε : 0 < ε) :
  ∃ (k : ℕ), ↑p ^ -((k : ℕ) : ℤ) < ε :=
begin
  obtain ⟨k, hk⟩ := exists_nat_gt ε⁻¹,
  use k,
  rw ← inv_lt_inv hε (_root_.fpow_pos_of_pos _ _),
  { rw [fpow_neg, inv_inv', fpow_coe_nat],
    apply lt_of_lt_of_le hk,
    norm_cast,
    apply le_of_lt,
    convert nat.lt_pow_self _ _ using 1,
    exact hp_prime.one_lt },
  { exact_mod_cast hp_prime.pos }
end

lemma exists_pow_neg_lt_rat {ε : ℚ} (hε : 0 < ε) :
  ∃ (k : ℕ), ↑p ^ -((k : ℕ) : ℤ) < ε :=
begin
  obtain ⟨k, hk⟩ := @exists_pow_neg_lt p _ ε (by exact_mod_cast hε),
  use k,
  rw (show (p : ℝ) = (p : ℚ), by simp) at hk,
  exact_mod_cast hk
end

variable {p}

lemma norm_int_lt_one_iff_dvd (k : ℤ) : ∥(k : ℤ_[p])∥ < 1 ↔ ↑p ∣ k :=
suffices ∥(k : ℚ_[p])∥ < 1 ↔ ↑p ∣ k, by rwa norm_int_cast_eq_padic_norm,
padic_norm_e.norm_int_lt_one_iff_dvd k

lemma norm_int_le_pow_iff_dvd {k : ℤ} {n : ℕ} : ∥(k : ℤ_[p])∥ ≤ ((↑p)^(-n : ℤ)) ↔ ↑p^n ∣ k :=
suffices ∥(k : ℚ_[p])∥ ≤ ((↑p)^(-n : ℤ)) ↔ ↑(p^n) ∣ k, by simpa [norm_int_cast_eq_padic_norm],
padic_norm_e.norm_int_le_pow_iff_dvd _ _

/-! ### Valuation on `ℤ_[p]` -/

/-- `padic_int.valuation` lifts the p-adic valuation on `ℚ` to `ℤ_[p]`.  -/
def valuation (x : ℤ_[p]) := padic.valuation (x : ℚ_[p])

lemma norm_eq_pow_val {x : ℤ_[p]} (hx : x ≠ 0) :
  ∥x∥ = p^(-x.valuation) :=
begin
  convert padic.norm_eq_pow_val _,
  contrapose! hx,
  exact subtype.val_injective hx
end

@[simp] lemma valuation_zero : valuation (0 : ℤ_[p]) = 0 :=
padic.valuation_zero

@[simp] lemma valuation_one : valuation (1 : ℤ_[p]) = 0 :=
padic.valuation_one

@[simp] lemma valuation_p : valuation (p : ℤ_[p]) = 1 :=
by simp [valuation, -cast_eq_of_rat_of_nat]

lemma valuation_nonneg (x : ℤ_[p]) : 0 ≤ x.valuation :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  have h : (1 : ℝ) < p := by exact_mod_cast hp_prime.one_lt,
  rw [← neg_nonpos, ← (fpow_strict_mono h).le_iff_le],
  show (p : ℝ) ^ -valuation x ≤ p ^ 0,
  rw [← norm_eq_pow_val hx],
  simpa using x.property,
end

@[simp] lemma valuation_p_pow_mul (n : ℕ) (c : ℤ_[p]) (hc : c ≠ 0) :
  (↑p ^ n * c).valuation = n + c.valuation :=
begin
  have : ∥↑p ^ n * c∥ = ∥(p ^ n : ℤ_[p])∥ * ∥c∥,
  { exact norm_mul _ _ },
  have aux : ↑p ^ n * c ≠ 0,
  { contrapose! hc, rw mul_eq_zero at hc, cases hc,
    { refine (hp_prime.ne_zero _).elim,
      exact_mod_cast (pow_eq_zero hc) },
    { exact hc } },
  rwa [norm_eq_pow_val aux, norm_p_pow, norm_eq_pow_val hc,
      ← fpow_add, ← neg_add, fpow_inj, neg_inj] at this,
  { exact_mod_cast hp_prime.pos },
  { exact_mod_cast hp_prime.ne_one },
  { exact_mod_cast hp_prime.ne_zero },
end

section units
/-! ### Units of `ℤ_[p]` -/

local attribute [reducible] padic_int

lemma mul_inv : ∀ {z : ℤ_[p]}, ∥z∥ = 1 → z * z.inv = 1
| ⟨k, _⟩ h :=
  begin
    have hk : k ≠ 0, from λ h', @zero_ne_one ℚ_[p] _ _ (by simpa [h'] using h),
    unfold padic_int.inv, split_ifs,
    { change (⟨k * (1/k), _⟩ : ℤ_[p]) = 1,
      simp [hk], refl },
    { apply subtype.ext_iff_val.2, simp [mul_inv_cancel hk] }
  end

lemma inv_mul {z : ℤ_[p]} (hz : ∥z∥ = 1) : z.inv * z = 1 :=
by rw [mul_comm, mul_inv hz]

lemma is_unit_iff {z : ℤ_[p]} : is_unit z ↔ ∥z∥ = 1 :=
⟨λ h, begin
  rcases is_unit_iff_dvd_one.1 h with ⟨w, eq⟩,
  refine le_antisymm (norm_le_one _) _,
  have := mul_le_mul_of_nonneg_left (norm_le_one w) (norm_nonneg z),
  rwa [mul_one, ← norm_mul, ← eq, norm_one] at this
end, λ h, ⟨⟨z, z.inv, mul_inv h, inv_mul h⟩, rfl⟩⟩

lemma norm_lt_one_add {z1 z2 : ℤ_[p]} (hz1 : ∥z1∥ < 1) (hz2 : ∥z2∥ < 1) : ∥z1 + z2∥ < 1 :=
lt_of_le_of_lt (nonarchimedean _ _) (max_lt hz1 hz2)

lemma norm_lt_one_mul {z1 z2 : ℤ_[p]} (hz2 : ∥z2∥ < 1) : ∥z1 * z2∥ < 1 :=
calc  ∥z1 * z2∥ = ∥z1∥ * ∥z2∥ : by simp
           ... < 1 : mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one _) (norm_nonneg _) hz2

@[simp] lemma mem_nonunits {z : ℤ_[p]} : z ∈ nonunits ℤ_[p] ↔ ∥z∥ < 1 :=
by rw lt_iff_le_and_ne; simp [norm_le_one z, nonunits, is_unit_iff]

/-- A `p`-adic number `u` with `∥u∥ = 1` is a unit of `ℤ_[p]`. -/
def mk_units {u : ℚ_[p]} (h : ∥u∥ = 1) : units ℤ_[p] :=
let z : ℤ_[p] := ⟨u, le_of_eq h⟩ in ⟨z, z.inv, mul_inv h, inv_mul h⟩

@[simp]
lemma mk_units_eq {u : ℚ_[p]} (h : ∥u∥ = 1) : ((mk_units h : ℤ_[p]) : ℚ_[p]) = u :=
rfl

@[simp] lemma norm_units (u : units ℤ_[p]) : ∥(u : ℤ_[p])∥ = 1 :=
is_unit_iff.mp $ by simp

/-- `unit_coeff hx` is the unit `u` in the unique representation `x = u * p ^ n`.
See `unit_coeff_spec`. -/
def unit_coeff {x : ℤ_[p]} (hx : x ≠ 0) : units ℤ_[p] :=
let u : ℚ_[p] := x*p^(-x.valuation) in
have hu : ∥u∥ = 1,
by simp [hx, nat.fpow_ne_zero_of_pos (by exact_mod_cast hp_prime.pos) x.valuation,
         norm_eq_pow_val, fpow_neg, inv_mul_cancel, -cast_eq_of_rat_of_nat],
mk_units hu

@[simp] lemma unit_coeff_coe {x : ℤ_[p]} (hx : x ≠ 0) :
  (unit_coeff hx : ℚ_[p]) = x * p ^ (-x.valuation) := rfl

lemma unit_coeff_spec {x : ℤ_[p]} (hx : x ≠ 0) :
  x = (unit_coeff hx : ℤ_[p]) * p ^ int.nat_abs (valuation x) :=
begin
  apply subtype.coe_injective,
  push_cast,
  have repr : (x : ℚ_[p]) = (unit_coeff hx) * p ^ x.valuation,
  { rw [unit_coeff_coe, mul_assoc, ← fpow_add],
    { simp },
    { exact_mod_cast hp_prime.ne_zero } },
  convert repr using 2,
  rw [← fpow_coe_nat, int.nat_abs_of_nonneg (valuation_nonneg x)],
end

end units

section norm_le_iff
/-! ### Various characterizations of open unit balls -/

lemma norm_le_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
  ∥x∥ ≤ p ^ (-n : ℤ) ↔ ↑n ≤ x.valuation :=
begin
  rw norm_eq_pow_val hx,
  lift x.valuation to ℕ using x.valuation_nonneg with k hk,
  simp only [int.coe_nat_le, fpow_neg, fpow_coe_nat],
  have aux : ∀ n : ℕ, 0 < (p ^ n : ℝ),
  { apply pow_pos, exact_mod_cast nat.prime.pos ‹_› },
  rw [inv_le_inv (aux _) (aux _)],
  have : p ^ n ≤ p ^ k ↔ n ≤ k := (pow_right_strict_mono (nat.prime.two_le ‹_›)).le_iff_le,
  rw [← this],
  norm_cast,
end

lemma mem_span_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
  x ∈ (ideal.span {p ^ n} : ideal ℤ_[p]) ↔ ↑n ≤ x.valuation :=
begin
  rw [ideal.mem_span_singleton],
  split,
  { rintro ⟨c, rfl⟩,
    suffices : c ≠ 0,
    { rw [valuation_p_pow_mul _ _ this, le_add_iff_nonneg_right], apply valuation_nonneg, },
    contrapose! hx, rw [hx, mul_zero], },
  { rw [unit_coeff_spec hx] { occs := occurrences.pos [2] },
    lift x.valuation to ℕ using x.valuation_nonneg with k hk,
    simp only [int.nat_abs_of_nat, is_unit_unit, is_unit.dvd_mul_left, int.coe_nat_le],
    intro H,
    obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le H,
    simp only [pow_add, dvd_mul_right], }
end

lemma norm_le_pow_iff_mem_span_pow (x : ℤ_[p]) (n : ℕ) :
  ∥x∥ ≤ p ^ (-n : ℤ) ↔ x ∈ (ideal.span {p ^ n} : ideal ℤ_[p]) :=
begin
  by_cases hx : x = 0,
  { subst hx,
    simp only [norm_zero, fpow_neg, fpow_coe_nat, inv_nonneg, iff_true, submodule.zero_mem],
    exact_mod_cast nat.zero_le _ },
  rw [norm_le_pow_iff_le_valuation x hx, mem_span_pow_iff_le_valuation x hx],
end

lemma norm_le_pow_iff_norm_lt_pow_add_one (x : ℤ_[p]) (n : ℤ) :
  ∥x∥ ≤ p ^ n ↔ ∥x∥ < p ^ (n + 1) :=
begin
  have aux : ∀ n : ℤ, 0 < (p ^ n : ℝ),
  { apply nat.fpow_pos_of_pos, exact nat.prime.pos ‹_› },
  by_cases hx0 : x = 0, { simp [hx0, norm_zero, aux, le_of_lt (aux _)], },
  rw norm_eq_pow_val hx0,
  have h1p : 1 < (p : ℝ), { exact_mod_cast nat.prime.one_lt ‹_› },
  have H := fpow_strict_mono h1p,
  rw [H.le_iff_le, H.lt_iff_lt, int.lt_add_one_iff],
end

lemma norm_lt_pow_iff_norm_le_pow_sub_one (x : ℤ_[p]) (n : ℤ) :
  ∥x∥ < p ^ n ↔ ∥x∥ ≤ p ^ (n - 1) :=
by rw [norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel]

lemma norm_lt_one_iff_dvd (x : ℤ_[p]) : ∥x∥ < 1 ↔ ↑p ∣ x :=
begin
  have := norm_le_pow_iff_mem_span_pow x 1,
  rw [ideal.mem_span_singleton, pow_one] at this,
  rw [← this, norm_le_pow_iff_norm_lt_pow_add_one],
  simp only [fpow_zero, int.coe_nat_zero, int.coe_nat_succ, add_left_neg, zero_add],
end

@[simp] lemma pow_p_dvd_int_iff (n : ℕ) (a : ℤ) : (p ^ n : ℤ_[p]) ∣ a ↔ ↑p ^ n ∣ a :=
by rw [← norm_int_le_pow_iff_dvd, norm_le_pow_iff_mem_span_pow, ideal.mem_span_singleton]

end norm_le_iff

section dvr
/-! ### Discrete valuation ring -/

instance : local_ring ℤ_[p] :=
local_of_nonunits_ideal zero_ne_one $ λ x y, by simp; exact norm_lt_one_add

lemma p_nonnunit : (p : ℤ_[p]) ∈ nonunits ℤ_[p] :=
have (p : ℝ)⁻¹ < 1, from inv_lt_one $ by exact_mod_cast hp_prime.one_lt,
by simp [this]

lemma maximal_ideal_eq_span_p : maximal_ideal ℤ_[p] = ideal.span {p} :=
begin
  apply le_antisymm,
  { intros x hx,
    rw ideal.mem_span_singleton,
    simp only [local_ring.mem_maximal_ideal, mem_nonunits] at hx,
    rwa ← norm_lt_one_iff_dvd, },
  { rw [ideal.span_le, set.singleton_subset_iff], exact p_nonnunit }
end

lemma prime_p : prime (p : ℤ_[p]) :=
begin
  rw [← ideal.span_singleton_prime, ← maximal_ideal_eq_span_p],
  { apply_instance },
  { exact_mod_cast hp_prime.ne_zero }
end

lemma irreducible_p : irreducible (p : ℤ_[p]) :=
irreducible_of_prime prime_p

instance : discrete_valuation_ring ℤ_[p] :=
discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization
⟨p, irreducible_p, λ x hx, ⟨x.valuation.nat_abs, unit_coeff hx,
  by rw [mul_comm, ← unit_coeff_spec hx]⟩⟩

lemma ideal_eq_span_pow_p {s : ideal ℤ_[p]} (hs : s ≠ ⊥) :
  ∃ n : ℕ, s = ideal.span {p ^ n} :=
discrete_valuation_ring.ideal_eq_span_pow_irreducible hs irreducible_p

end dvr

end padic_int
