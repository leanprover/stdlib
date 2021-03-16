/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import algebra.ordered_ring
import tactic.monotonicity.basic
import deprecated.group

/-!
# Power operations on monoids and groups

The power operation on monoids and groups.
We separate this from group, because it depends on `ℕ`,
which in turn depends on other parts of algebra.

This module contains the definitions of `monoid.pow` and `group.pow`
and their additive counterparts `nsmul` and `gsmul`, along with a few lemmas.
Further lemmas can be found in `algebra.group_power.lemmas`.

## Notation

The class `has_pow α β` provides the notation `a^b` for powers.
We define instances of `has_pow M ℕ`, for monoids `M`, and `has_pow G ℤ` for groups `G`.

We also define infix operators `•ℕ` and `•ℤ` for scalar multiplication by a natural and an integer
numbers, respectively.

## Implementation details

We adopt the convention that `0^0 = 1`.

This module provides the instance `has_pow ℕ ℕ` (via `monoid.has_pow`)
and is imported by `data.nat.basic`, so it has to live low in the import hierarchy.
Not all of its imports are needed yet; the intent is to move more lemmas here from `.lemmas`
so that they are available in `data.nat.basic`, and the imports will be required then.
-/

universes u v w x y z u₁ u₂

variables {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z}
  {R : Type u₁} {S : Type u₂}

open multiplicative additive

/-- The power operation in a monoid. `a^n = a*a*...*a` n times. -/
def monoid.pow [has_mul M] [has_one M] (a : M) : ℕ → M
| 0     := 1
| (n+1) := a * monoid.pow n

/-- The scalar multiplication in an additive monoid.
`n •ℕ a = a+a+...+a` n times. -/
def nsmul [has_add A] [has_zero A] (n : ℕ) (a : A) : A :=
(monoid.pow (of_add a) n).to_add

infix ` •ℕ `:70 := nsmul

instance monoid.has_pow [monoid M] : has_pow M ℕ := ⟨monoid.pow⟩

@[simp] lemma monoid.pow_eq_has_pow [monoid M] (a : M) (n : ℕ) : monoid.pow a n = a^n := rfl

lemma to_add_pow_nsmul [add_monoid A] (a : multiplicative A) (n : ℕ) :
  to_add (a ^ n) = n •ℕ to_add a :=
by simp [nsmul]

/-!
### Commutativity

First we prove some facts about `semiconj_by` and `commute`. They do not require any theory about
`pow` and/or `nsmul` and will be useful later in this file.
-/

namespace semiconj_by

variables [monoid M]

@[simp] lemma pow_right {a x y : M} (h : semiconj_by a x y) (n : ℕ) : semiconj_by a (x^n) (y^n) :=
nat.rec_on n (one_right a) $ λ n ihn, h.mul_right ihn

end semiconj_by

namespace commute

variables [monoid M] {a b : M}

@[simp] theorem pow_right (h : commute a b) (n : ℕ) : commute a (b ^ n) := h.pow_right n
@[simp] theorem pow_left (h : commute a b) (n : ℕ) : commute (a ^ n) b := (h.symm.pow_right n).symm
@[simp] theorem pow_pow (h : commute a b) (m n : ℕ) : commute (a ^ m) (b ^ n) :=
(h.pow_left m).pow_right n

@[simp] theorem self_pow (a : M) (n : ℕ) : commute a (a ^ n) := (commute.refl a).pow_right n
@[simp] theorem pow_self (a : M) (n : ℕ) : commute (a ^ n) a := (commute.refl a).pow_left n
@[simp] theorem pow_pow_self (a : M) (m n : ℕ) : commute (a ^ m) (a ^ n) :=
(commute.refl a).pow_pow m n

end commute

section monoid
variables [monoid M] [monoid N] [add_monoid A] [add_monoid B]

@[simp] theorem pow_zero (a : M) : a^0 = 1 := rfl
@[simp] theorem zero_nsmul (a : A) : 0 •ℕ a = 0 := rfl

theorem pow_succ (a : M) (n : ℕ) : a^(n+1) = a * a^n := rfl
theorem succ_nsmul (a : A) (n : ℕ) : (n+1) •ℕ a = a + n •ℕ a := rfl

theorem pow_two (a : M) : a^2 = a * a :=
show a*(a*1)=a*a, by rw mul_one
theorem two_nsmul (a : A) : 2 •ℕ a = a + a :=
by simpa [nsmul] using congr_arg to_add (pow_two (of_add a))

theorem pow_mul_comm' (a : M) (n : ℕ) : a^n * a = a * a^n := commute.pow_self a n
theorem nsmul_add_comm' (a : A) (n : ℕ) : n •ℕ a + a = a + n •ℕ a :=
by simpa [nsmul] using congr_arg to_add (pow_mul_comm' (of_add a) n)

theorem pow_succ' (a : M) (n : ℕ) : a^(n+1) = a^n * a :=
by rw [pow_succ, pow_mul_comm']
theorem succ_nsmul' (a : A) (n : ℕ) : (n+1) •ℕ a = n •ℕ a + a :=
by simpa [nsmul] using congr_arg to_add (pow_succ' (of_add a) n)

theorem pow_add (a : M) (m n : ℕ) : a^(m + n) = a^m * a^n :=
by induction n with n ih; [rw [nat.add_zero, pow_zero, mul_one],
  rw [pow_succ', ← mul_assoc, ← ih, ← pow_succ', nat.add_assoc]]
theorem add_nsmul (a : A) (m n : ℕ) : (m + n) •ℕ a = m •ℕ a + n •ℕ a :=
by simpa [nsmul] using congr_arg to_add (pow_add (of_add a) m n)

@[simp] theorem pow_one (a : M) : a^1 = a := mul_one _

@[simp] theorem one_nsmul (a : A) : 1 •ℕ a = a := add_zero _

@[simp] lemma pow_ite (P : Prop) [decidable P] (a : M) (b c : ℕ) :
  a ^ (if P then b else c) = if P then a ^ b else a ^ c :=
by split_ifs; refl

@[simp] lemma ite_pow (P : Prop) [decidable P] (a b : M) (c : ℕ) :
  (if P then a else b) ^ c = if P then a ^ c else b ^ c :=
by split_ifs; refl

@[simp] lemma pow_boole (P : Prop) [decidable P] (a : M) :
  a ^ (if P then 1 else 0) = if P then a else 1 :=
by simp

@[simp] theorem one_pow (n : ℕ) : (1 : M)^n = 1 :=
by induction n with n ih; [refl, rw [pow_succ, ih, one_mul]]

@[simp] theorem nsmul_zero (n : ℕ) : n •ℕ (0 : A) = 0 :=
by induction n with n ih; [refl, rw [succ_nsmul, ih, zero_add]]

theorem pow_mul (a : M) (m n : ℕ) : a^(m * n) = (a^m)^n :=
by induction n with n ih; [rw nat.mul_zero, rw [nat.mul_succ, pow_add, pow_succ', ih]]; refl

theorem mul_nsmul' (a : A) (m n : ℕ) : m * n •ℕ a = n •ℕ (m •ℕ a) :=
by simpa [nsmul] using congr_arg to_add (pow_mul (of_add a) m n)

theorem pow_mul' (a : M) (m n : ℕ) : a^(m * n) = (a^n)^m :=
by rw [nat.mul_comm, pow_mul]

theorem mul_nsmul (a : A) (m n : ℕ) : m * n •ℕ a = m •ℕ (n •ℕ a) :=
by simpa [nsmul] using congr_arg to_add (pow_mul' (of_add a) m n)

theorem pow_mul_pow_sub (a : M) {m n : ℕ} (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n :=
by rw [←pow_add, nat.add_comm, nat.sub_add_cancel h]

theorem nsmul_add_sub_nsmul (a : A) {m n : ℕ} (h : m ≤ n) : (m •ℕ a) + ((n - m) •ℕ a) = n •ℕ a :=
by simpa [nsmul] using congr_arg to_add (pow_mul_pow_sub (of_add a) h)

theorem pow_sub_mul_pow (a : M) {m n : ℕ} (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n :=
by rw [←pow_add, nat.sub_add_cancel h]

theorem sub_nsmul_nsmul_add (a : A) {m n : ℕ} (h : m ≤ n) : ((n - m) •ℕ a) + (m •ℕ a) = n •ℕ a :=
by simpa [nsmul] using congr_arg to_add (pow_sub_mul_pow (of_add a) h)

theorem pow_bit0 (a : M) (n : ℕ) : a ^ bit0 n = a^n * a^n := pow_add _ _ _

theorem bit0_nsmul (a : A) (n : ℕ) : bit0 n •ℕ a = n •ℕ a + n •ℕ a := add_nsmul _ _ _

theorem pow_bit1 (a : M) (n : ℕ) : a ^ bit1 n = a^n * a^n * a :=
by rw [bit1, pow_succ', pow_bit0]

theorem bit1_nsmul (a : A) (n : ℕ) : bit1 n •ℕ a = n •ℕ a + n •ℕ a + a :=
by simpa [nsmul] using congr_arg to_add (pow_bit1 (of_add a) n)

theorem pow_mul_comm (a : M) (m n : ℕ) : a^m * a^n = a^n * a^m :=
commute.pow_pow_self a m n

theorem nsmul_add_comm (a : A) (m n : ℕ) : m •ℕ a + n •ℕ a = n •ℕ a + m •ℕ a :=
by simpa [nsmul] using congr_arg to_add (pow_mul_comm (of_add a) m n)

@[simp] theorem monoid_hom.map_pow (f : M →* N) (a : M) : ∀(n : ℕ), f (a ^ n) = (f a) ^ n
| 0     := f.map_one
| (n+1) := by rw [pow_succ, pow_succ, f.map_mul, monoid_hom.map_pow]

@[simp] theorem add_monoid_hom.map_nsmul (f : A →+ B) (a : A) (n : ℕ) : f (n •ℕ a) = n •ℕ f a :=
by simpa [nsmul, -monoid_hom.map_pow] using congr_arg to_add (f.to_multiplicative.map_pow _ n)

lemma to_mul_nsmul (a : additive M) (n : ℕ) :
  to_mul (n •ℕ a) = to_mul a ^ n :=
have ∀ a (n : ℕ), to_mul (to_add (a ^ n)) = to_mul (to_add a) ^ n,
from (@to_add_to_mul M _).to_monoid_hom.map_pow,
by simp [nsmul, this]

theorem is_monoid_hom.map_pow (f : M → N) [is_monoid_hom f] (a : M) :
  ∀(n : ℕ), f (a ^ n) = (f a) ^ n :=
(monoid_hom.of f).map_pow a

theorem is_add_monoid_hom.map_nsmul (f : A → B) [is_add_monoid_hom f] (a : A) (n : ℕ) :
  f (n •ℕ a) = n •ℕ f a :=
(add_monoid_hom.of f).map_nsmul a n

lemma commute.mul_pow {a b : M} (h : commute a b) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
nat.rec_on n (by simp) $ λ n ihn,
by simp only [pow_succ, ihn, ← mul_assoc, (h.pow_left n).right_comm]

theorem neg_pow [ring R] (a : R) (n : ℕ) : (- a) ^ n = (-1) ^ n * a ^ n :=
(neg_one_mul a) ▸ (commute.neg_one_left a).mul_pow n

theorem pow_bit0' (a : M) (n : ℕ) : a ^ bit0 n = (a * a) ^ n :=
by rw [pow_bit0, (commute.refl a).mul_pow]

theorem bit0_nsmul' (a : A) (n : ℕ) : bit0 n •ℕ a = n •ℕ (a + a) :=
by simpa [nsmul] using congr_arg to_add (pow_bit0' (of_add a) n)

theorem pow_bit1' (a : M) (n : ℕ) : a ^ bit1 n = (a * a) ^ n * a :=
by rw [bit1, pow_succ', pow_bit0']

theorem bit1_nsmul' (a : A) (n : ℕ) : bit1 n •ℕ a = n •ℕ (a + a) + a :=
by simpa [nsmul] using congr_arg to_add (pow_bit1' (of_add a) n)

@[simp] theorem neg_pow_bit0 [ring R] (a : R) (n : ℕ) : (- a) ^ (bit0 n) = a ^ (bit0 n) :=
by rw [pow_bit0', neg_mul_neg, pow_bit0']

@[simp] theorem neg_pow_bit1 [ring R] (a : R) (n : ℕ) : (- a) ^ (bit1 n) = - a ^ (bit1 n) :=
by simp only [bit1, pow_succ, neg_pow_bit0, neg_mul_eq_neg_mul]

end monoid

/-!
### Commutative (additive) monoid
-/

section comm_monoid
variables [comm_monoid M] [add_comm_monoid A]

theorem mul_pow (a b : M) (n : ℕ) : (a * b)^n = a^n * b^n :=
(commute.all a b).mul_pow n

theorem nsmul_add (a b : A) (n : ℕ) : n •ℕ (a + b) = n •ℕ a + n •ℕ b :=
by simpa [nsmul] using congr_arg to_add (mul_pow (of_add a) (of_add b) n)

instance pow.is_monoid_hom (n : ℕ) : is_monoid_hom ((^ n) : M → M) :=
{ map_mul := λ _ _, mul_pow _ _ _, map_one := one_pow _ }

instance nsmul.is_add_monoid_hom (n : ℕ) : is_add_monoid_hom (nsmul n : A → A) :=
{ map_add := λ _ _, nsmul_add _ _ _, map_zero := nsmul_zero _ }

lemma dvd_pow {x y : M} :
  ∀ {n : ℕ} (hxy : x ∣ y) (hn : n ≠ 0), x ∣ y^n
| 0     hxy hn := (hn rfl).elim
| (n+1) hxy hn := by { rw [pow_succ], exact dvd_mul_of_dvd_left hxy _ }

end comm_monoid

section group
variables [group G] [group H] [add_group A] [add_group B]

open int

/--
The power operation in a group. This extends `monoid.pow` to negative integers
with the definition `a^(-n) = (a^n)⁻¹`.
-/
def gpow (a : G) : ℤ → G
| (of_nat n) := a^n
| -[1+n]     := (a^(nat.succ n))⁻¹

/--
The scalar multiplication by integers on an additive group.
This extends `nsmul` to negative integers
with the definition `(-n) •ℤ a = -(n •ℕ a)`.
-/
def gsmul (n : ℤ) (a : A) : A :=
(gpow (of_add a) n).to_add

instance group.has_pow : has_pow G ℤ := ⟨gpow⟩

infix ` •ℤ `:70 := gsmul

@[simp] lemma group.gpow_eq_has_pow (a : G) (n : ℤ) : gpow a n = a ^ n := rfl

lemma to_add_pow_gsmul (a : multiplicative A) (n : ℤ) :
  to_add (a ^ n) = n •ℤ to_add a :=
by simp [gsmul]

section nat

@[simp] theorem inv_pow (a : G) (n : ℕ) : (a⁻¹)^n = (a^n)⁻¹ :=
by induction n with n ih; [exact one_inv.symm,
  rw [pow_succ', pow_succ, ih, mul_inv_rev]]

@[simp] theorem neg_nsmul : ∀ (a : A) (n : ℕ), n •ℕ (-a) = -(n •ℕ a) :=
by simp [nsmul]

theorem pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a^(m - n) = a^m * (a^n)⁻¹ :=
have h1 : m - n + n = m, from nat.sub_add_cancel h,
have h2 : a^(m - n) * a^n = a^m, by rw [←pow_add, h1],
eq_mul_inv_of_mul_eq h2

theorem nsmul_sub (a : A) {m n : ℕ} (h : n ≤ m) : (m - n) •ℕ a = m •ℕ a - n •ℕ a :=
by simpa [nsmul, sub_eq_add_neg] using congr_arg to_add (pow_sub (of_add a) h)

theorem pow_inv_comm (a : G) (m n : ℕ) : (a⁻¹)^m * a^n = a^n * (a⁻¹)^m :=
(commute.refl a).inv_left.pow_pow m n

theorem nsmul_neg_comm (a : A) (m n : ℕ) : m •ℕ (-a) + n •ℕ a = n •ℕ a + m •ℕ (-a) :=
by simpa [nsmul, sub_eq_add_neg] using congr_arg to_add (pow_inv_comm (of_add a) m n)

end nat

@[simp] theorem gpow_coe_nat (a : G) (n : ℕ) : a ^ (n:ℤ) = a ^ n := rfl

@[simp] theorem gsmul_coe_nat (a : A) (n : ℕ) : n •ℤ a = n •ℕ a := rfl

theorem gpow_of_nat (a : G) (n : ℕ) : a ^ of_nat n = a ^ n := rfl

theorem gsmul_of_nat (a : A) (n : ℕ) : of_nat n •ℤ a = n •ℕ a := rfl

@[simp] theorem gpow_neg_succ_of_nat (a : G) (n : ℕ) : a ^ -[1+n] = (a ^ n.succ)⁻¹ := rfl

@[simp] theorem gsmul_neg_succ_of_nat (a : A) (n : ℕ) : -[1+n] •ℤ a = - (n.succ •ℕ a) := rfl

@[simp] theorem gpow_zero (a : G) : a ^ (0:ℤ) = 1 := rfl

@[simp] theorem zero_gsmul (a : A) : (0:ℤ) •ℤ a = 0 := rfl

@[simp] theorem gpow_one (a : G) : a ^ (1:ℤ) = a := pow_one a

@[simp] theorem one_gsmul (a : A) : (1:ℤ) •ℤ a = a := add_zero _

@[simp] theorem one_gpow : ∀ (n : ℤ), (1 : G) ^ n = 1
| (n : ℕ) := one_pow _
| -[1+ n] := show _⁻¹=(1:G), by rw [one_pow, one_inv]

@[simp] theorem gsmul_zero : ∀ (n : ℤ), n •ℤ (0 : A) = 0 :=
by simp [gsmul]

@[simp] theorem gpow_neg (a : G) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹
| (n+1:ℕ) := rfl
| 0       := one_inv.symm
| -[1+ n] := (inv_inv _).symm

lemma mul_gpow_neg_one (a b : G) : (a*b)^(-(1:ℤ)) = b^(-(1:ℤ))*a^(-(1:ℤ)) :=
by simp only [mul_inv_rev, gpow_one, gpow_neg]

@[simp] theorem neg_gsmul : ∀ (a : A) (n : ℤ), -n •ℤ a = -(n •ℤ a) :=
by simp [gsmul]

theorem gpow_neg_one (x : G) : x ^ (-1:ℤ) = x⁻¹ := congr_arg has_inv.inv $ pow_one x

theorem neg_one_gsmul (x : A) : (-1:ℤ) •ℤ x = -x := congr_arg has_neg.neg $ one_nsmul x

theorem inv_gpow (a : G) : ∀n:ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
| (n : ℕ) := inv_pow a n
| -[1+ n] := congr_arg has_inv.inv $ inv_pow a (n+1)

theorem gsmul_neg (a : A) (n : ℤ) : gsmul n (- a) = - gsmul n a :=
by simp [gsmul, inv_gpow]

theorem commute.mul_gpow {a b : G} (h : commute a b) : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n
| (n : ℕ) := h.mul_pow n
| -[1+n] := by simp [h.mul_pow, (h.pow_pow n.succ n.succ).inv_inv.symm.eq]

end group

section comm_group
variables [comm_group G] [add_comm_group A]

theorem mul_gpow (a b : G) (n : ℤ) : (a * b)^n = a^n * b^n := (commute.all a b).mul_gpow n

theorem gsmul_add (a b : A) (n : ℤ) : n •ℤ (a + b) = n •ℤ a + n •ℤ b :=
by simp [gsmul, mul_gpow]

theorem gsmul_sub (a b : A) (n : ℤ) : gsmul n (a - b) = gsmul n a - gsmul n b :=
by simp only [gsmul_add, gsmul_neg, sub_eq_add_neg]

instance gpow.is_group_hom (n : ℤ) : is_group_hom ((^ n) : G → G) :=
{ map_mul := λ _ _, mul_gpow _ _ n }

instance gsmul.is_add_group_hom (n : ℤ) : is_add_group_hom (gsmul n : A → A) :=
{ map_add := λ _ _, gsmul_add _ _ n }

end comm_group

lemma zero_pow [monoid_with_zero R] : ∀ {n : ℕ}, 0 < n → (0 : R) ^ n = 0
| (n+1) _ := zero_mul _

lemma zero_pow_eq [monoid_with_zero R] (n : ℕ) : (0 : R)^n = if n = 0 then 1 else 0 :=
begin
  split_ifs with h,
  { rw [h, pow_zero], },
  { rw [zero_pow (nat.pos_of_ne_zero h)] },
end

namespace ring_hom

variables [semiring R] [semiring S]

@[simp] lemma map_pow (f : R →+* S) (a) :
  ∀ n : ℕ, f (a ^ n) = (f a) ^ n :=
f.to_monoid_hom.map_pow a

end ring_hom

theorem neg_one_pow_eq_or [ring R] : ∀ n : ℕ, (-1 : R)^n = 1 ∨ (-1 : R)^n = -1
| 0     := or.inl rfl
| (n+1) := (neg_one_pow_eq_or n).swap.imp
  (λ h, by rw [pow_succ, h, neg_one_mul, neg_neg])
  (λ h, by rw [pow_succ, h, mul_one])

lemma pow_dvd_pow [monoid R] (a : R) {m n : ℕ} (h : m ≤ n) :
  a ^ m ∣ a ^ n := ⟨a ^ (n - m), by rw [← pow_add, nat.add_comm, nat.sub_add_cancel h]⟩

theorem pow_dvd_pow_of_dvd [comm_monoid R] {a b : R} (h : a ∣ b) : ∀ n : ℕ, a ^ n ∣ b ^ n
| 0     := dvd_refl _
| (n+1) := mul_dvd_mul h (pow_dvd_pow_of_dvd n)

lemma pow_two_sub_pow_two {R : Type*} [comm_ring R] (a b : R) :
  a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
by simp only [pow_two, mul_sub, add_mul, sub_sub, add_sub, mul_comm, sub_add_cancel]

lemma eq_or_eq_neg_of_pow_two_eq_pow_two [integral_domain R] (a b : R) (h : a ^ 2 = b ^ 2) :
  a = b ∨ a = -b :=
by rwa [← add_eq_zero_iff_eq_neg, ← sub_eq_zero, or_comm, ← mul_eq_zero,
        ← pow_two_sub_pow_two a b, sub_eq_zero]

theorem sq_sub_sq [comm_ring R] (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
by rw [pow_two, pow_two, mul_self_sub_mul_self]

theorem pow_eq_zero [monoid_with_zero R] [no_zero_divisors R] {x : R} {n : ℕ} (H : x^n = 0) :
  x = 0 :=
begin
  induction n with n ih,
  { rw pow_zero at H,
    rw [← mul_one x, H, mul_zero] },
  exact or.cases_on (mul_eq_zero.1 H) id ih
end

@[simp] lemma pow_eq_zero_iff [monoid_with_zero R] [no_zero_divisors R]
  {a : R} {n : ℕ} (hn : 0 < n) :
  a ^ n = 0 ↔ a = 0 :=
begin
  refine ⟨pow_eq_zero, _⟩,
  rintros rfl,
  exact zero_pow hn,
end

@[field_simps] theorem pow_ne_zero [monoid_with_zero R] [no_zero_divisors R]
  {a : R} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
mt pow_eq_zero h

lemma pow_abs [linear_ordered_comm_ring R] (a : R) (n : ℕ) : (abs a)^n = abs (a^n) :=
(abs_hom.to_monoid_hom.map_pow a n).symm

lemma abs_neg_one_pow [linear_ordered_comm_ring R] (n : ℕ) : abs ((-1 : R)^n) = 1 :=
by rw [←pow_abs, abs_neg, abs_one, one_pow]

section add_monoid
variable [ordered_add_comm_monoid A]

theorem nsmul_nonneg {a : A} (H : 0 ≤ a) : ∀ n : ℕ, 0 ≤ n •ℕ a
| 0     := le_refl _
| (n+1) := add_nonneg H (nsmul_nonneg n)

lemma nsmul_pos {a : A} (ha : 0 < a) {k : ℕ} (hk : 0 < k) : 0 < k •ℕ a :=
begin
  rcases nat.exists_eq_succ_of_ne_zero (ne_of_gt hk) with ⟨l, rfl⟩,
  clear hk,
  induction l with l IH,
  { simpa using ha },
  { exact add_pos ha IH }
end

theorem nsmul_le_nsmul {a : A} {n m : ℕ} (ha : 0 ≤ a) (h : n ≤ m) : n •ℕ a ≤ m •ℕ a :=
let ⟨k, hk⟩ := nat.le.dest h in
calc n •ℕ a = n •ℕ a + 0 : (add_zero _).symm
  ... ≤ n •ℕ a + k •ℕ a : add_le_add_left (nsmul_nonneg ha _) _
  ... = m •ℕ a : by rw [← hk, add_nsmul]

lemma nsmul_le_nsmul_of_le_right {a b : A} (hab : a ≤ b) : ∀ i : ℕ, i •ℕ a ≤ i •ℕ b
| 0 := by simp
| (k+1) := add_le_add hab (nsmul_le_nsmul_of_le_right _)

end add_monoid

section add_group
variable [ordered_add_comm_group A]

theorem gsmul_nonneg {a : A} (H : 0 ≤ a) {n : ℤ} (hn : 0 ≤ n) :
  0 ≤ n •ℤ a :=
begin
  lift n to ℕ using hn,
  apply nsmul_nonneg H
end

end add_group

section cancel_add_monoid
variable [ordered_cancel_add_comm_monoid A]

theorem nsmul_lt_nsmul {a : A} {n m : ℕ} (ha : 0 < a) (h : n < m) :
  n •ℕ a < m •ℕ a :=
let ⟨k, hk⟩ := nat.le.dest h in
begin
  have succ_swap : n.succ + k = n + k.succ := nat.succ_add n k,
  calc n •ℕ a = (n •ℕ a : A) + (0 : A) : (add_zero _).symm
    ... < n •ℕ a + (k.succ •ℕ a : A) : add_lt_add_left (nsmul_pos ha (nat.succ_pos k)) _
    ... = m •ℕ a : by rw [← hk, succ_swap, add_nsmul]
end

end cancel_add_monoid

section semiring

variables [semiring R]

lemma min_pow_dvd_add {n m : ℕ} {a b c : R} (ha : c ^ n ∣ a) (hb : c ^ m ∣ b) :
  c ^ (min n m) ∣ a + b :=
begin
  replace ha := dvd.trans (pow_dvd_pow c (min_le_left n m)) ha,
  replace hb := dvd.trans (pow_dvd_pow c (min_le_right n m)) hb,
  exact dvd_add ha hb
end

end semiring

section comm_semiring

variables [comm_semiring R]

lemma add_pow_two (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by simp only [pow_two, add_mul_self_eq]

end comm_semiring

namespace canonically_ordered_semiring
variable [canonically_ordered_comm_semiring R]

theorem pow_pos {a : R} (H : 0 < a) : ∀ n : ℕ, 0 < a ^ n
| 0     := by { nontriviality, exact canonically_ordered_semiring.zero_lt_one }
| (n+1) := canonically_ordered_semiring.mul_pos.2 ⟨H, pow_pos n⟩

@[mono] lemma pow_le_pow_of_le_left {a b : R} (hab : a ≤ b) : ∀ i : ℕ, a^i ≤ b^i
| 0     := by simp
| (k+1) := canonically_ordered_semiring.mul_le_mul hab (pow_le_pow_of_le_left k)

theorem one_le_pow_of_one_le {a : R} (H : 1 ≤ a) (n : ℕ) : 1 ≤ a ^ n :=
by simpa only [one_pow] using pow_le_pow_of_le_left H n

theorem pow_le_one {a : R} (H : a ≤ 1) (n : ℕ) : a ^ n ≤ 1:=
by simpa only [one_pow] using pow_le_pow_of_le_left H n

end canonically_ordered_semiring

section ordered_semiring
variable [ordered_semiring R]

@[simp] theorem pow_pos {a : R} (H : 0 < a) : ∀ (n : ℕ), 0 < a ^ n
| 0     := by { nontriviality, exact zero_lt_one }
| (n+1) := mul_pos H (pow_pos _)

@[simp] theorem pow_nonneg {a : R} (H : 0 ≤ a) : ∀ (n : ℕ), 0 ≤ a ^ n
| 0     := zero_le_one
| (n+1) := mul_nonneg H (pow_nonneg _)

theorem pow_add_pow_le {x y : R} {n : ℕ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hn : n ≠ 0) :
  x ^ n + y ^ n ≤ (x + y) ^ n :=
begin
  rcases nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩,
  induction k with k ih, { simp only [pow_one] },
  let n := k.succ,
  have h1 := add_nonneg (mul_nonneg hx (pow_nonneg hy n)) (mul_nonneg hy (pow_nonneg hx n)),
  have h2 := add_nonneg hx hy,
  calc x^n.succ + y^n.succ ≤ x*x^n + y*y^n + (x*y^n + y*x^n) : le_add_of_nonneg_right h1
                       ... = (x+y) * (x^n + y^n) : by rw [add_mul, mul_add, mul_add,
                                                          add_comm (y*x^n), ← add_assoc,
                                                          ← add_assoc, add_assoc (x*x^n) (x*y^n),
                                                          add_comm (x*y^n) (y*y^n), ← add_assoc]
                       ... ≤ (x+y)^n.succ : mul_le_mul_of_nonneg_left (ih (nat.succ_ne_zero k)) h2,
end

theorem pow_lt_pow_of_lt_left {x y : R} {n : ℕ} (Hxy : x < y) (Hxpos : 0 ≤ x) (Hnpos : 0 < n) :
  x ^ n < y ^ n :=
begin
  cases lt_or_eq_of_le Hxpos,
  { rw ←nat.sub_add_cancel Hnpos,
    induction (n - 1), { simpa only [pow_one] },
    rw [pow_add, pow_add, nat.succ_eq_add_one, pow_one, pow_one],
    apply mul_lt_mul ih (le_of_lt Hxy) h (le_of_lt (pow_pos (lt_trans h Hxy) _)) },
  { rw [←h, zero_pow Hnpos], apply pow_pos (by rwa ←h at Hxy : 0 < y),}
end

theorem strict_mono_incr_on_pow {n : ℕ} (hn : 0 < n) :
  strict_mono_incr_on (λ x : R, x ^ n) (set.Ici 0) :=
λ x hx y hy h, pow_lt_pow_of_lt_left h hx hn

theorem one_le_pow_of_one_le {a : R} (H : 1 ≤ a) : ∀ (n : ℕ), 1 ≤ a ^ n
| 0     := le_refl _
| (n+1) := by simpa only [mul_one] using mul_le_mul H (one_le_pow_of_one_le n)
    zero_le_one (le_trans zero_le_one H)

lemma pow_mono {a : R} (h : 1 ≤ a) : monotone (λ n : ℕ, a ^ n) :=
monotone_of_monotone_nat $ λ n, le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans h) _) h

theorem pow_le_pow {a : R} {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
pow_mono ha h

lemma strict_mono_pow {a : R} (h : 1 < a) : strict_mono (λ n : ℕ, a ^ n) :=
have 0 < a := zero_le_one.trans_lt h,
strict_mono.nat $ λ n, by simpa only [one_mul, pow_succ]
  using mul_lt_mul h (le_refl (a ^ n)) (pow_pos this _) this.le

lemma pow_lt_pow {a : R} {n m : ℕ} (h : 1 < a) (h2 : n < m) : a ^ n < a ^ m :=
strict_mono_pow h h2

lemma pow_lt_pow_iff {a : R} {n m : ℕ} (h : 1 < a) : a ^ n < a ^ m ↔ n < m :=
(strict_mono_pow h).lt_iff_lt

@[mono] lemma pow_le_pow_of_le_left {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ i : ℕ, a^i ≤ b^i
| 0     := by simp
| (k+1) := mul_le_mul hab (pow_le_pow_of_le_left _) (pow_nonneg ha _) (le_trans ha hab)

end ordered_semiring

section linear_ordered_semiring
variable [linear_ordered_semiring R]

theorem pow_left_inj {x y : R} {n : ℕ} (Hxpos : 0 ≤ x) (Hypos : 0 ≤ y) (Hnpos : 0 < n)
  (Hxyn : x ^ n = y ^ n) : x = y :=
(@strict_mono_incr_on_pow R _ _ Hnpos).inj_on Hxpos Hypos Hxyn

lemma lt_of_pow_lt_pow {a b : R} (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
lt_of_not_ge $ λ hn, not_lt_of_ge (pow_le_pow_of_le_left hb hn _) h

lemma le_of_pow_le_pow {a b : R} (n : ℕ) (hb : 0 ≤ b) (hn : 0 < n) (h : a ^ n ≤ b ^ n) : a ≤ b :=
le_of_not_lt $ λ h1, not_le_of_lt (pow_lt_pow_of_lt_left h1 hb hn) h

end linear_ordered_semiring

section linear_ordered_ring

variable [linear_ordered_ring R]

theorem pow_bit0_nonneg (a : R) (n : ℕ) : 0 ≤ a ^ bit0 n :=
by { rw pow_bit0, exact mul_self_nonneg _ }

theorem pow_two_nonneg (a : R) : 0 ≤ a ^ 2 :=
pow_bit0_nonneg a 1

theorem pow_bit0_pos {a : R} (h : a ≠ 0) (n : ℕ) : 0 < a ^ bit0 n :=
(pow_bit0_nonneg a n).lt_of_ne (pow_ne_zero _ h).symm

theorem pow_two_pos_of_ne_zero (a : R) (h : a ≠ 0) : 0 < a ^ 2 :=
pow_bit0_pos h 1

variables {x y : R}

@[simp] theorem sqr_abs (x : R) : abs x ^ 2 = x ^ 2 :=
by simpa only [pow_two] using abs_mul_abs_self x

theorem abs_sqr (x : R) : abs (x ^ 2) = x ^ 2 :=
by simpa only [pow_two] using abs_mul_self x

theorem sqr_lt_sqr (h : abs x < y) : x ^ 2 < y ^ 2 :=
by simpa only [sqr_abs] using pow_lt_pow_of_lt_left h (abs_nonneg x) (1:ℕ).succ_pos

theorem sqr_lt_sqr' (h1 : -y < x) (h2 : x < y) : x ^ 2 < y ^ 2 :=
sqr_lt_sqr (abs_lt.mpr ⟨h1, h2⟩)

theorem sqr_le_sqr (h : abs x ≤ y) : x ^ 2 ≤ y ^ 2 :=
by simpa only [sqr_abs] using pow_le_pow_of_le_left (abs_nonneg x) h 2

theorem sqr_le_sqr' (h1 : -y ≤ x) (h2 : x ≤ y) : x ^ 2 ≤ y ^ 2 :=
sqr_le_sqr (abs_le.mpr ⟨h1, h2⟩)

theorem abs_lt_abs_of_sqr_lt_sqr (h : x^2 < y^2) : abs x < abs y :=
lt_of_pow_lt_pow 2 (abs_nonneg y) $ by rwa [← sqr_abs x, ← sqr_abs y] at h

theorem abs_lt_of_sqr_lt_sqr (h : x^2 < y^2) (hy : 0 ≤ y) : abs x < y :=
begin
  rw [← abs_of_nonneg hy],
  exact abs_lt_abs_of_sqr_lt_sqr h,
end

theorem abs_lt_of_sqr_lt_sqr' (h : x^2 < y^2) (hy : 0 ≤ y) : -y < x ∧ x < y :=
abs_lt.mp $ abs_lt_of_sqr_lt_sqr h hy

theorem abs_le_abs_of_sqr_le_sqr (h : x^2 ≤ y^2) : abs x ≤ abs y :=
le_of_pow_le_pow 2 (abs_nonneg y) (1:ℕ).succ_pos $ by rwa [← sqr_abs x, ← sqr_abs y] at h

theorem abs_le_of_sqr_le_sqr (h : x^2 ≤ y^2) (hy : 0 ≤ y) : abs x ≤ y :=
begin
  rw [← abs_of_nonneg hy],
  exact abs_le_abs_of_sqr_le_sqr h,
end

theorem abs_le_of_sqr_le_sqr' (h : x^2 ≤ y^2) (hy : 0 ≤ y) : -y ≤ x ∧ x ≤ y :=
abs_le.mp $ abs_le_of_sqr_le_sqr h hy

end linear_ordered_ring

@[simp] lemma eq_of_pow_two_eq_pow_two [linear_ordered_comm_ring R]
  {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) :
  a ^ 2 = b ^ 2 ↔ a = b :=
begin
  refine ⟨_, congr_arg _⟩,
  intros h,
  refine (eq_or_eq_neg_of_pow_two_eq_pow_two _ _ h).elim id _,
  rintros rfl,
  rw le_antisymm (neg_nonneg.mp ha) hb,
  exact neg_zero
end

@[simp] lemma neg_square {α} [ring α] (z : α) : (-z)^2 = z^2 :=
by simp [pow, monoid.pow]

lemma of_add_nsmul [add_monoid A] (x : A) (n : ℕ) :
  of_add (n •ℕ x) = (of_add x)^n :=
by simp [nsmul]

lemma of_add_gsmul [add_group A] (x : A) (n : ℤ) :
  of_add (n •ℤ x) = (of_add x)^n :=
by simp [gsmul]

@[simp] lemma semiconj_by.gpow_right [group G] {a x y : G} (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (x^m) (y^m)
| (n : ℕ) := h.pow_right n
| -[1+n] := (h.pow_right n.succ).inv_right

namespace commute

variables [group G] {a b : G}

@[simp] lemma gpow_right (h : commute a b) (m : ℤ) : commute a (b^m) :=
h.gpow_right m

@[simp] lemma gpow_left (h : commute a b) (m : ℤ) : commute (a^m) b :=
(h.symm.gpow_right m).symm

lemma gpow_gpow (h : commute a b) (m n : ℤ) : commute (a^m) (b^n) := (h.gpow_left m).gpow_right n

variables (a) (m n : ℕ)

@[simp] theorem self_gpow : commute a (a ^ n) := (commute.refl a).gpow_right n
@[simp] theorem gpow_self : commute (a ^ n) a := (commute.refl a).gpow_left n
@[simp] theorem gpow_gpow_self : commute (a ^ m) (a ^ n) := (commute.refl a).gpow_gpow m n

end commute
