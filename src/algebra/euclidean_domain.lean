/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/

import data.int.basic
import algebra.field

/-!
# Euclidean domains

This file introduces Euclidean domains and provides the extended Euclidean algorithm. To be precise,
a slightly more general version is provided which is sometimes called a transfinite Euclidean domain
and differs in the fact that the degree function need not take values in `ℕ` but can take values in
any well-ordered set. Transfinite Euclidean domains were introduced by Motzkin and examples which
don't satisfy the classical notion were provided independently by Hiblot and Nagata.

## Main definitions

* `euclidean_domain`: Defines Euclidean domain with functions `quotient` and `remainder`. Instances
  of `has_div` and `has_mod` are provided, so that one can write `a = b * (a / b) + a % b`.
* `gcd`: defines the greatest common divisors of two elements of a Euclidean domain.
* `xgcd`: given two elements `a b : R`, `xgcd a b` defines the pair `(x, y)` such that
  `x * a + y * b = gcd a b`.
* `lcm`: defines the lowest common multiple of two elements `a` and `b` of a Euclidean domain as
  `a * b / (gcd a b)`

## Main statements

* `gcd_eq_gcd_ab`: states Bézout's lemma for Euclidean domains.
* `int.euclidean_domain`: shows that `ℤ` is a Euclidean domain.
* `field.to_euclidean_domain`: shows that any field is a Euclidean domain.

## Notation

`≺` denotes the well founded relation on the Euclidean domain, e.g. in the example of the polynomial
ring over a field, `p ≺ q` for polynomials `p` and `q` if and only if the degree of `p` is less than
the degree of `q`.

## Implementation details

Instead of working with a valuation, `euclidean_domain` is implemented with the existence of a well
founded relation `r` on the integral domain `R`, which in the example of `ℤ` would correspond to
setting `i ≺ j` for integers `i` and `j` if the absolute value of `i` is smaller than the absolute
value of `j`.

## References

* [Th. Motzkin, *The Euclidean algorithm*][MR32592]
* [J.-J. Hiblot, *Des anneaux euclidiens dont le plus petit algorithme n'est pas à valeurs finies*]
  [MR399081]
* [M. Nagata, *On Euclid algorithm*][MR541021]


## Tags

Euclidean domain, transfinite Euclidean domain, Bézout's lemma
-/

universe u

section old_structure_cmd
set_option old_structure_cmd true

/-- A `euclidean_domain` is an `integral_domain` with a division and a remainder, satisfying
  `b * (a / b) + a % b = a`. The definition of a euclidean domain usually includes a valuation
  function `R → ℕ`. This definition is slightly generalised to include a well founded relation
  `r` with the property that `r (a % b) b`, instead of a valuation.  -/
@[protect_proj without mul_left_not_lt r_well_founded]
class euclidean_domain (R : Type u) extends comm_ring R, nontrivial R :=
(quotient : R → R → R)
(quotient_zero : ∀ a, quotient a 0 = 0)
(remainder : R → R → R)
(quotient_mul_add_remainder_eq : ∀ a b, b * quotient a b + remainder a b = a)
(r : R → R → Prop)
(r_well_founded : well_founded r)
(remainder_lt : ∀ a {b}, b ≠ 0 → r (remainder a b) b)
(mul_left_not_lt : ∀ a {b}, b ≠ 0 → ¬r (a * b) a)
end old_structure_cmd

namespace euclidean_domain
variable {R : Type u}
variables [euclidean_domain R]

local infix ` ≺ `:50 := euclidean_domain.r

@[priority 70] -- see Note [lower instance priority]
instance : has_div R := ⟨euclidean_domain.quotient⟩

@[priority 70] -- see Note [lower instance priority]
instance : has_mod R := ⟨euclidean_domain.remainder⟩

theorem div_add_mod (a b : R) : b * (a / b) + a % b = a :=
euclidean_domain.quotient_mul_add_remainder_eq _ _

lemma mod_add_div (a b : R) : a % b + b * (a / b) = a :=
(add_comm _ _).trans (div_add_mod _ _)

lemma mod_add_div' (m k : R) : m % k + (m / k) * k = m :=
by { rw mul_comm, exact mod_add_div _ _ }

lemma div_add_mod' (m k : R) : (m / k) * k + m % k = m :=
by { rw mul_comm, exact div_add_mod _ _ }

lemma mod_eq_sub_mul_div {R : Type*} [euclidean_domain R] (a b : R) :
  a % b = a - b * (a / b) :=
calc a % b = b * (a / b) + a % b - b * (a / b) : (add_sub_cancel' _ _).symm
... = a - b * (a / b) : by rw div_add_mod

theorem mod_lt : ∀ a {b : R}, b ≠ 0 → (a % b) ≺ b :=
euclidean_domain.remainder_lt

theorem mul_right_not_lt {a : R} (b) (h : a ≠ 0) : ¬(a * b) ≺ b :=
by rw mul_comm; exact mul_left_not_lt b h

lemma mul_div_cancel_left {a : R} (b) (a0 : a ≠ 0) : a * b / a = b :=
eq.symm $ eq_of_sub_eq_zero $ classical.by_contradiction $ λ h,
begin
  have := mul_left_not_lt a h,
  rw [mul_sub, sub_eq_iff_eq_add'.2 (div_add_mod (a*b) a).symm] at this,
  exact this (mod_lt _ a0)
end

lemma mul_div_cancel (a) {b : R} (b0 : b ≠ 0) : a * b / b = a :=
by rw mul_comm; exact mul_div_cancel_left a b0

@[simp] lemma mod_zero (a : R) : a % 0 = a :=
by simpa only [zero_mul, zero_add] using div_add_mod a 0

@[simp] lemma mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a :=
⟨λ h, by rw [← div_add_mod a b, h, add_zero]; exact dvd_mul_right _ _,
 λ ⟨c, e⟩, begin
  rw [e, ← add_left_cancel_iff, div_add_mod, add_zero],
  haveI := classical.dec,
  by_cases b0 : b = 0,
  { simp only [b0, zero_mul] },
  { rw [mul_div_cancel_left _ b0] }
 end⟩

@[simp] lemma mod_self (a : R) : a % a = 0 :=
mod_eq_zero.2 (dvd_refl _)

lemma dvd_mod_iff {a b c : R} (h : c ∣ b) : c ∣ a % b ↔ c ∣ a :=
by rw [dvd_add_iff_right (dvd_mul_of_dvd_left h _), div_add_mod]

lemma lt_one (a : R) : a ≺ (1:R) → a = 0 :=
by haveI := classical.dec; exact
not_imp_not.1 (λ h, by simpa only [one_mul] using mul_left_not_lt 1 h)

lemma val_dvd_le : ∀ a b : R, b ∣ a → a ≠ 0 → ¬a ≺ b
| _ b ⟨d, rfl⟩ ha := mul_left_not_lt b (mt (by rintro rfl; exact mul_zero _) ha)

@[simp] lemma mod_one (a : R) : a % 1 = 0 :=
mod_eq_zero.2 (one_dvd _)

@[simp] lemma zero_mod (b : R) : 0 % b = 0 :=
mod_eq_zero.2 (dvd_zero _)

@[simp, priority 900] lemma div_zero (a : R) : a / 0 = 0 :=
euclidean_domain.quotient_zero a

@[simp, priority 900] lemma zero_div {a : R} : 0 / a = 0 :=
classical.by_cases
  (λ a0 : a = 0, a0.symm ▸ div_zero 0)
  (λ a0, by simpa only [zero_mul] using mul_div_cancel 0 a0)

@[simp, priority 900] lemma div_self {a : R} (a0 : a ≠ 0) : a / a = 1 :=
by simpa only [one_mul] using mul_div_cancel 1 a0

lemma eq_div_of_mul_eq_left {a b c : R} (hb : b ≠ 0) (h : a * b = c) : a = c / b :=
by rw [← h, mul_div_cancel _ hb]

lemma eq_div_of_mul_eq_right {a b c : R} (ha : a ≠ 0) (h : a * b = c) : b = c / a :=
by rw [← h, mul_div_cancel_left _ ha]

theorem mul_div_assoc (x : R) {y z : R} (h : z ∣ y) : x * y / z = x * (y / z) :=
begin
  classical, by_cases hz : z = 0,
  { subst hz, rw [div_zero, div_zero, mul_zero] },
  rcases h with ⟨p, rfl⟩,
  rw [mul_div_cancel_left _ hz, mul_left_comm, mul_div_cancel_left _ hz]
end

section
open_locale classical

@[elab_as_eliminator]
theorem gcd.induction {P : R → R → Prop} : ∀ a b : R,
  (∀ x, P 0 x) →
  (∀ a b, a ≠ 0 → P (b % a) a → P a b) →
  P a b
| a := λ b H0 H1, if a0 : a = 0 then by rw [a0]; apply H0 else
  have h:_ := mod_lt b a0,
  H1 _ _ a0 (gcd.induction (b%a) a H0 H1)
using_well_founded {dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨_, r_well_founded⟩]}

end

section gcd
variable [decidable_eq R]

/-- `gcd a b` is a (non-unique) element such that `gcd a b ∣ a` `gcd a b ∣ b`, and for
  any element `c` such that `c ∣ a` and `c ∣ b`, then `c ∣ gcd a b` -/
def gcd : R → R → R
| a := λ b, if a0 : a = 0 then b else
  have h:_ := mod_lt b a0,
  gcd (b%a) a
using_well_founded {dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨_, r_well_founded⟩]}

@[simp] theorem gcd_zero_left (a : R) : gcd 0 a = a :=
by rw gcd; exact if_pos rfl

@[simp] theorem gcd_zero_right (a : R) : gcd a 0 = a :=
by rw gcd; split_ifs; simp only [h, zero_mod, gcd_zero_left]

theorem gcd_val (a b : R) : gcd a b = gcd (b % a) a :=
by rw gcd; split_ifs; [simp only [h, mod_zero, gcd_zero_right], refl]

theorem gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b :=
gcd.induction a b
  (λ b, by rw [gcd_zero_left]; exact ⟨dvd_zero _, dvd_refl _⟩)
  (λ a b aneq ⟨IH₁, IH₂⟩, by rw gcd_val;
    exact ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩)

theorem gcd_dvd_left (a b : R) : gcd a b ∣ a := (gcd_dvd a b).left

theorem gcd_dvd_right (a b : R) : gcd a b ∣ b := (gcd_dvd a b).right

protected theorem gcd_eq_zero_iff {a b : R} :
  gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
⟨λ h, by simpa [h] using gcd_dvd a b,
 by rintro ⟨rfl, rfl⟩; simp⟩

theorem dvd_gcd {a b c : R} : c ∣ a → c ∣ b → c ∣ gcd a b :=
gcd.induction a b
  (λ _ _ H, by simpa only [gcd_zero_left] using H)
  (λ a b a0 IH ca cb, by rw gcd_val;
    exact IH ((dvd_mod_iff ca).2 cb) ca)

theorem gcd_eq_left {a b : R} : gcd a b = a ↔ a ∣ b :=
⟨λ h, by rw ← h; apply gcd_dvd_right,
 λ h, by rw [gcd_val, mod_eq_zero.2 h, gcd_zero_left]⟩

@[simp] theorem gcd_one_left (a : R) : gcd 1 a = 1 :=
gcd_eq_left.2 (one_dvd _)

@[simp] theorem gcd_self (a : R) : gcd a a = a :=
gcd_eq_left.2 (dvd_refl _)

/--
An implementation of the extended GCD algorithm.
At each step we are computing a triple `(r, s, t)`, where `r` is the next value of the GCD
algorithm, to compute the greatest common divisor of the input (say `x` and `y`), and `s` and `t`
are the coefficients in front of `x` and `y` to obtain `r` (i.e. `r = s * x + t * y`).
The function `xgcd_aux` takes in two triples, and from these recursively computes the next triple:
```
xgcd_aux (r, s, t) (r', s', t') = xgcd_aux (r' % r, s' - (r' / r) * s, t' - (r' / r) * t) (r, s, t)
```
-/
def xgcd_aux : R → R → R → R → R → R → R × R × R
| r := λ s t r' s' t',
if hr : r = 0 then (r', s', t')
  else
  have r' % r ≺ r, from mod_lt _ hr,
  let q := r' / r in xgcd_aux (r' % r) (s' - q * s) (t' - q * t) r s t
using_well_founded {dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨_, r_well_founded⟩]}

@[simp] theorem xgcd_zero_left {s t r' s' t' : R} : xgcd_aux 0 s t r' s' t' = (r', s', t') :=
by unfold xgcd_aux; exact if_pos rfl

theorem xgcd_aux_rec {r s t r' s' t' : R} (h : r ≠ 0) :
  xgcd_aux r s t r' s' t' = xgcd_aux (r' % r) (s' - (r' / r) * s) (t' - (r' / r) * t) r s t :=
by conv {to_lhs, rw [xgcd_aux]}; exact if_neg h

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x y : R) : R × R := (xgcd_aux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_a (x y : R) : R := (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_b (x y : R) : R := (xgcd x y).2

@[simp] theorem gcd_a_zero_left {s : R} : gcd_a 0 s = 0 :=
by { unfold gcd_a, rw [xgcd, xgcd_zero_left] }

@[simp] theorem gcd_b_zero_left {s : R} : gcd_b 0 s = 1 :=
by { unfold gcd_b, rw [xgcd, xgcd_zero_left] }

@[simp] theorem xgcd_aux_fst (x y : R) : ∀ s t s' t',
  (xgcd_aux x s t y s' t').1 = gcd x y :=
gcd.induction x y (by intros; rw [xgcd_zero_left, gcd_zero_left])
(λ x y h IH s t s' t', by simp only [xgcd_aux_rec h, if_neg h, IH]; rw ← gcd_val)

theorem xgcd_aux_val (x y : R) : xgcd_aux x 1 0 y 0 1 = (gcd x y, xgcd x y) :=
by rw [xgcd, ← xgcd_aux_fst x y 1 0 0 1, prod.mk.eta]

theorem xgcd_val (x y : R) : xgcd x y = (gcd_a x y, gcd_b x y) :=
prod.mk.eta.symm

private def P (a b : R) : R × R × R → Prop | (r, s, t) := (r : R) = a * s + b * t

theorem xgcd_aux_P (a b : R) {r r' : R} : ∀ {s t s' t'}, P a b (r, s, t) →
  P a b (r', s', t') → P a b (xgcd_aux r s t r' s' t') :=
gcd.induction r r' (by intros; simpa only [xgcd_zero_left]) $ λ x y h IH s t s' t' p p', begin
  rw [xgcd_aux_rec h], refine IH _ p, unfold P at p p' ⊢,
  rw [mul_sub, mul_sub, add_sub, sub_add_eq_add_sub, ← p', sub_sub,
    mul_comm _ s, ← mul_assoc, mul_comm _ t, ← mul_assoc, ← add_mul, ← p,
    mod_eq_sub_mul_div]
end

/-- An explicit version of **Bézout's lemma** for Euclidean domains. -/
theorem gcd_eq_gcd_ab (a b : R) : (gcd a b : R) = a * gcd_a a b + b * gcd_b a b :=
by have := @xgcd_aux_P _ _ _ a b a b 1 0 0 1
  (by rw [P, mul_one, mul_zero, add_zero]) (by rw [P, mul_one, mul_zero, zero_add]);
rwa [xgcd_aux_val, xgcd_val] at this

@[priority 70] -- see Note [lower instance priority]
instance (R : Type*) [e : euclidean_domain R] : integral_domain R :=
by haveI := classical.dec_eq R; exact
{ eq_zero_or_eq_zero_of_mul_eq_zero :=
    λ a b h, (or_iff_not_and_not.2 $ λ h0,
      h0.1 $ by rw [← mul_div_cancel a h0.2, h, zero_div]),
  zero := 0, add := (+), mul := (*), ..e }

end gcd

section lcm
variables [decidable_eq R]

/-- `lcm a b` is a (non-unique) element such that `a ∣ lcm a b` `b ∣ lcm a b`, and for
  any element `c` such that `a ∣ c` and `b ∣ c`, then `lcm a b ∣ c` -/
def lcm (x y : R) : R :=
x * y / gcd x y

theorem dvd_lcm_left (x y : R) : x ∣ lcm x y :=
classical.by_cases
  (assume hxy : gcd x y = 0, by rw [lcm, hxy, div_zero]; exact dvd_zero _)
  (λ hxy, let ⟨z, hz⟩ := (gcd_dvd x y).2 in ⟨z, eq.symm $ eq_div_of_mul_eq_left hxy $
    by rw [mul_right_comm, mul_assoc, ← hz]⟩)

theorem dvd_lcm_right (x y : R) : y ∣ lcm x y :=
classical.by_cases
  (assume hxy : gcd x y = 0, by rw [lcm, hxy, div_zero]; exact dvd_zero _)
  (λ hxy, let ⟨z, hz⟩ := (gcd_dvd x y).1 in ⟨z, eq.symm $ eq_div_of_mul_eq_right hxy $
    by rw [← mul_assoc, mul_right_comm, ← hz]⟩)

theorem lcm_dvd {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z) : lcm x y ∣ z :=
begin
  rw lcm, by_cases hxy : gcd x y = 0,
  { rw [hxy, div_zero], rw euclidean_domain.gcd_eq_zero_iff at hxy, rwa hxy.1 at hxz },
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩,
  suffices : x * y ∣ z * gcd x y,
  { cases this with p hp, use p,
    generalize_hyp : gcd x y = g at hxy hs hp ⊢, subst hs,
    rw [mul_left_comm, mul_div_cancel_left _ hxy, ← mul_left_inj' hxy, hp],
    rw [← mul_assoc], simp only [mul_right_comm] },
  rw [gcd_eq_gcd_ab, mul_add], apply dvd_add,
  { rw mul_left_comm, exact mul_dvd_mul_left _ (dvd_mul_of_dvd_left hyz _) },
  { rw [mul_left_comm, mul_comm], exact mul_dvd_mul_left _ (dvd_mul_of_dvd_left hxz _) }
end

@[simp] lemma lcm_dvd_iff {x y z : R} : lcm x y ∣ z ↔ x ∣ z ∧ y ∣ z :=
⟨λ hz, ⟨dvd_trans (dvd_lcm_left _ _) hz, dvd_trans (dvd_lcm_right _ _) hz⟩,
λ ⟨hxz, hyz⟩, lcm_dvd hxz hyz⟩

@[simp] lemma lcm_zero_left (x : R) : lcm 0 x = 0 :=
by rw [lcm, zero_mul, zero_div]

@[simp] lemma lcm_zero_right (x : R) : lcm x 0 = 0 :=
by rw [lcm, mul_zero, zero_div]

@[simp] lemma lcm_eq_zero_iff {x y : R} : lcm x y = 0 ↔ x = 0 ∨ y = 0 :=
begin
  split,
  { intro hxy, rw [lcm, mul_div_assoc _ (gcd_dvd_right _ _), mul_eq_zero] at hxy,
    apply or_of_or_of_imp_right hxy, intro hy,
    by_cases hgxy : gcd x y = 0,
    { rw euclidean_domain.gcd_eq_zero_iff at hgxy, exact hgxy.2 },
    { rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩,
      generalize_hyp : gcd x y = g at hr hs hy hgxy ⊢, subst hs,
      rw [mul_div_cancel_left _ hgxy] at hy, rw [hy, mul_zero] } },
  rintro (hx | hy),
  { rw [hx, lcm_zero_left] },
  { rw [hy, lcm_zero_right] }
end

@[simp] lemma gcd_mul_lcm (x y : R) : gcd x y * lcm x y = x * y :=
begin
  rw lcm, by_cases h : gcd x y = 0,
  { rw [h, zero_mul], rw euclidean_domain.gcd_eq_zero_iff at h, rw [h.1, zero_mul] },
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩,
  generalize_hyp : gcd x y = g at h hr ⊢, subst hr,
  rw [mul_assoc, mul_div_cancel_left _ h]
end

end lcm

end euclidean_domain

instance int.euclidean_domain : euclidean_domain ℤ :=
{ add := (+),
  mul := (*),
  one := 1,
  zero := 0,
  neg := has_neg.neg,
  quotient := (/),
  quotient_zero := int.div_zero,
  remainder := (%),
  quotient_mul_add_remainder_eq := λ a b, int.div_add_mod _ _,
  r := λ a b, a.nat_abs < b.nat_abs,
  r_well_founded := measure_wf (λ a, int.nat_abs a),
  remainder_lt := λ a b b0, int.coe_nat_lt.1 $
    by rw [int.nat_abs_of_nonneg (int.mod_nonneg _ b0), ← int.abs_eq_nat_abs];
    exact int.mod_lt _ b0,
  mul_left_not_lt := λ a b b0, not_lt_of_ge $
    by rw [← mul_one a.nat_abs, int.nat_abs_mul];
    exact mul_le_mul_of_nonneg_left (int.nat_abs_pos_of_ne_zero b0) (nat.zero_le _),
  .. int.comm_ring,
  .. int.nontrivial }

@[priority 100] -- see Note [lower instance priority]
instance field.to_euclidean_domain {K : Type u} [field K] : euclidean_domain K :=
{ add := (+),
  mul := (*),
  one := 1,
  zero := 0,
  neg := has_neg.neg,
  quotient := (/),
  remainder := λ a b, a - a * b / b,
  quotient_zero := div_zero,
  quotient_mul_add_remainder_eq := λ a b,
    by classical; by_cases b = 0; simp [h, mul_div_cancel'],
  r := λ a b, a = 0 ∧ b ≠ 0,
  r_well_founded := well_founded.intro $ λ a, acc.intro _ $ λ b ⟨hb, hna⟩,
    acc.intro _ $ λ c ⟨hc, hnb⟩, false.elim $ hnb hb,
  remainder_lt := λ a b hnb, by simp [hnb],
  mul_left_not_lt := λ a b hnb ⟨hab, hna⟩, or.cases_on (mul_eq_zero.1 hab) hna hnb,
  .. ‹field K› }
