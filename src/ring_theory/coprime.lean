/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
import tactic.ring
import algebra.big_operators.basic
import data.int.gcd
import data.set.disjointed

/-!
# Coprime elements of a ring

## Main definitions

* `is_coprime x y`: that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime.

-/

open_locale classical big_operators

universes u v

section comm_semiring

variables {R : Type u} [comm_semiring R] (x y z : R)

/-- The proposition that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime. -/
@[simp] def is_coprime : Prop :=
∃ a b, a * x + b * y = 1

theorem nat.is_coprime_iff_coprime {m n : ℕ} : is_coprime (m : ℤ) n ↔ nat.coprime m n :=
⟨λ ⟨a, b, H⟩, nat.eq_one_of_dvd_one $ int.coe_nat_dvd.1 $ by { rw [int.coe_nat_one, ← H],
  exact dvd_add (dvd_mul_of_dvd_right (int.coe_nat_dvd.2 $ nat.gcd_dvd_left m n) _)
    (dvd_mul_of_dvd_right (int.coe_nat_dvd.2 $ nat.gcd_dvd_right m n) _) },
λ H, ⟨nat.gcd_a m n, nat.gcd_b m n, by rw [mul_comm _ (m : ℤ), mul_comm _ (n : ℤ),
    ← nat.gcd_eq_gcd_ab, show _ = _, from H, int.coe_nat_one]⟩⟩

variables {x y z}

theorem is_coprime.symm (H : is_coprime x y) : is_coprime y x :=
let ⟨a, b, H⟩ := H in ⟨b, a, by rw [add_comm, H]⟩

theorem is_coprime_comm : is_coprime x y ↔ is_coprime y x :=
⟨is_coprime.symm, is_coprime.symm⟩

theorem is_coprime_self : is_coprime x x ↔ is_unit x :=
⟨λ ⟨a, b, h⟩, is_unit_of_mul_eq_one x (a + b) $ by rwa [mul_comm, add_mul],
λ h, let ⟨b, hb⟩ := is_unit_iff_exists_inv'.1 h in ⟨b, 0, by rwa [zero_mul, add_zero]⟩⟩

theorem is_coprime_zero_left : is_coprime 0 x ↔ is_unit x :=
⟨λ ⟨a, b, H⟩, is_unit_of_mul_eq_one x b $ by rwa [mul_zero, zero_add, mul_comm] at H,
λ H, let ⟨b, hb⟩ := is_unit_iff_exists_inv'.1 H in ⟨1, b, by rwa [one_mul, zero_add]⟩⟩

theorem is_coprime_zero_right : is_coprime x 0 ↔ is_unit x :=
is_coprime_comm.trans is_coprime_zero_left

theorem is_coprime_one_left : is_coprime 1 x :=
⟨1, 0, by rw [one_mul, zero_mul, add_zero]⟩

theorem is_coprime_one_right : is_coprime x 1 :=
⟨0, 1, by rw [one_mul, zero_mul, zero_add]⟩

theorem is_coprime.dvd_of_dvd_mul_right (H1 : is_coprime x z) (H2 : x ∣ y * z) : x ∣ y :=
let ⟨a, b, H⟩ := H1 in by { rw [← mul_one y, ← H, mul_add, ← mul_assoc, mul_left_comm],
exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_right H2 _) }

theorem is_coprime.dvd_of_dvd_mul_left (H1 : is_coprime x y) (H2 : x ∣ y * z) : x ∣ z :=
let ⟨a, b, H⟩ := H1 in by { rw [← one_mul z, ← H, add_mul, mul_right_comm, mul_assoc b],
exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_right H2 _) }

theorem is_coprime.mul_left (H1 : is_coprime x z) (H2 : is_coprime y z) : is_coprime (x * y) z :=
let ⟨a, b, h1⟩ := H1, ⟨c, d, h2⟩ := H2 in
⟨a * c, a * x * d + b * c * y + b * d * z,
calc  a * c * (x * y) + (a * x * d + b * c * y + b * d * z) * z
    = (a * x + b * z) * (c * y + d * z) : by ring
... = 1 : by rw [h1, h2, mul_one]⟩

theorem is_coprime.mul_right (H1 : is_coprime x y) (H2 : is_coprime x z) : is_coprime x (y * z) :=
by { rw is_coprime_comm at H1 H2 ⊢, exact H1.mul_left H2 }

variables {I : Type v} {s : I → R} {t : finset I}

theorem is_coprime.prod_left : (∀ i ∈ t, is_coprime (s i) x) → is_coprime (∏ i in t, s i) x :=
finset.induction_on t (λ _, is_coprime_one_left) $ λ b t hbt ih H,
by { rw finset.prod_insert hbt, rw finset.forall_mem_insert at H, exact H.1.mul_left (ih H.2) }

theorem is_coprime.prod_right : (∀ i ∈ t, is_coprime x (s i)) → is_coprime x (∏ i in t, s i) :=
by simpa only [is_coprime_comm] using is_coprime.prod_left

theorem is_coprime.mul_dvd (H : is_coprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z :=
begin
  obtain ⟨a, b, h⟩ := H,
  rw [← mul_one z, ← h, mul_add],
  apply dvd_add,
  { rw [mul_comm z, mul_assoc],
    exact dvd_mul_of_dvd_right (mul_dvd_mul_left _ H2) _ },
  { rw [mul_comm b, ← mul_assoc],
    exact dvd_mul_of_dvd_left (mul_dvd_mul_right H1 _) _ }
end

theorem finset.prod_dvd_of_coprime :
  ∀ (Hs : set.pairwise_on (↑t : set I) (is_coprime on s)) (Hs1 : ∀ i ∈ t, s i ∣ z),
  ∏ x in t, s x ∣ z :=
finset.induction_on t (λ _ _, one_dvd z)
begin
  intros a r har ih Hs Hs1,
  rw finset.prod_insert har,
  have aux1 : a ∈ (↑(insert a r) : set I) := finset.mem_insert_self a r,
  refine (is_coprime.prod_right $ λ i hir, Hs a aux1 i _ (by { rintro rfl, exact har hir })).mul_dvd
    (Hs1 a aux1) (ih (Hs.mono _) $ λ i hi, Hs1 i (finset.mem_insert_of_mem hi)),
  { exact finset.mem_insert_of_mem hir },
  { simp only [finset.coe_insert, set.subset_insert] }
end

theorem fintype.prod_dvd_of_coprime [fintype I] (Hs : pairwise (is_coprime on s))
  (Hs1 : ∀ i, s i ∣ z) : ∏ x, s x ∣ z :=
finset.prod_dvd_of_coprime (Hs.pairwise_on _) (λ i _, Hs1 i)

theorem is_coprime.of_mul_left_left (H : is_coprime (x * y) z) : is_coprime x z :=
let ⟨a, b, h⟩ := H in ⟨a * y, b, by rwa [mul_right_comm, mul_assoc]⟩

theorem is_coprime.of_mul_left_right (H : is_coprime (x * y) z) : is_coprime y z :=
by { rw mul_comm at H, exact H.of_mul_left_left }

theorem is_coprime.of_mul_right_left (H : is_coprime x (y * z)) : is_coprime x y :=
by { rw is_coprime_comm at H ⊢, exact H.of_mul_left_left }

theorem is_coprime.of_mul_right_right (H : is_coprime x (y * z)) : is_coprime x z :=
by { rw mul_comm at H, exact H.of_mul_right_left }

theorem is_coprime.mul_left_iff : is_coprime (x * y) z ↔ is_coprime x z ∧ is_coprime y z :=
⟨λ H, ⟨H.of_mul_left_left, H.of_mul_left_right⟩, λ ⟨H1, H2⟩, H1.mul_left H2⟩

theorem is_coprime.mul_right_iff : is_coprime x (y * z) ↔ is_coprime x y ∧ is_coprime x z :=
by rw [is_coprime_comm, is_coprime.mul_left_iff, is_coprime_comm, @is_coprime_comm _ _ z]

theorem is_coprime.prod_left_iff : is_coprime (∏ i in t, s i) x ↔ ∀ i ∈ t, is_coprime (s i) x :=
finset.induction_on t (iff_of_true is_coprime_one_left $ λ _, false.elim) $ λ b t hbt ih,
by rw [finset.prod_insert hbt, is_coprime.mul_left_iff, ih, finset.forall_mem_insert]

theorem is_coprime.prod_right_iff : is_coprime x (∏ i in t, s i) ↔ ∀ i ∈ t, is_coprime x (s i) :=
by simpa only [is_coprime_comm] using is_coprime.prod_left_iff

theorem is_coprime.of_prod_left (H1 : is_coprime (∏ i in t, s i) x) (i : I) (hit : i ∈ t) :
  is_coprime (s i) x :=
is_coprime.prod_left_iff.1 H1 i hit

theorem is_coprime.of_prod_right (H1 : is_coprime x (∏ i in t, s i)) (i : I) (hit : i ∈ t) :
  is_coprime x (s i) :=
is_coprime.prod_right_iff.1 H1 i hit

variables {m n : ℕ}

theorem is_coprime.pow_left (H : is_coprime x y) : is_coprime (x ^ m) y :=
by { rw [← finset.card_range m, ← finset.prod_const], exact is_coprime.prod_left (λ _ _, H) }

theorem is_coprime.pow_right (H : is_coprime x y) : is_coprime x (y ^ n) :=
by { rw [← finset.card_range n, ← finset.prod_const], exact is_coprime.prod_right (λ _ _, H) }

theorem is_coprime.pow (H : is_coprime x y) : is_coprime (x ^ m) (y ^ n) :=
H.pow_left.pow_right

theorem is_coprime.is_unit_of_dvd (H : is_coprime x y) (d : x ∣ y) : is_unit x :=
let ⟨k, hk⟩ := d in is_coprime_self.1 $ is_coprime.of_mul_right_left $
show is_coprime x (x * k), from hk ▸ H

theorem is_coprime.map (H : is_coprime x y) {S : Type v} [comm_semiring S] (f : R →+* S) :
  is_coprime (f x) (f y) :=
let ⟨a, b, h⟩ := H in ⟨f a, f b, by rw [← f.map_mul, ← f.map_mul, ← f.map_add, h, f.map_one]⟩

variables {x y z}

lemma is_coprime.of_add_mul_left_left (h : is_coprime (x + y * z) y) : is_coprime x y :=
let ⟨a, b, H⟩ := h in ⟨a, a * z + b, by simpa only [add_mul, mul_add,
    add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using H⟩

lemma is_coprime.of_add_mul_right_left (h : is_coprime (x + z * y) y) : is_coprime x y :=
by { rw mul_comm at h, exact h.of_add_mul_left_left }

lemma is_coprime.of_add_mul_left_right (h : is_coprime x (y + x * z)) : is_coprime x y :=
by { rw is_coprime_comm at h ⊢, exact h.of_add_mul_left_left }

lemma is_coprime.of_add_mul_right_right (h : is_coprime x (y + z * x)) : is_coprime x y :=
by { rw mul_comm at h, exact h.of_add_mul_left_right }

lemma is_coprime.of_mul_add_left_left (h : is_coprime (y * z + x) y) : is_coprime x y :=
by { rw add_comm at h, exact h.of_add_mul_left_left }

lemma is_coprime.of_mul_add_right_left (h : is_coprime (z * y + x) y) : is_coprime x y :=
by { rw add_comm at h, exact h.of_add_mul_right_left }

lemma is_coprime.of_mul_add_left_right (h : is_coprime x (x * z + y)) : is_coprime x y :=
by { rw add_comm at h, exact h.of_add_mul_left_right }

lemma is_coprime.of_mul_add_right_right (h : is_coprime x (z * x + y)) : is_coprime x y :=
by { rw add_comm at h, exact h.of_add_mul_right_right }

end comm_semiring

namespace is_coprime

section comm_ring

variables {R : Type u} [comm_ring R]

lemma add_mul_left_left {x y : R} (h : is_coprime x y) (z : R) : is_coprime (x + y * z) y :=
@of_add_mul_left_left R _ _ _ (-z) $
by simpa only [mul_neg_eq_neg_mul_symm, add_neg_cancel_right] using h

lemma add_mul_right_left {x y : R} (h : is_coprime x y) (z : R) : is_coprime (x + z * y) y :=
by { rw mul_comm, exact h.add_mul_left_left z }

lemma add_mul_left_right {x y : R} (h : is_coprime x y) (z : R) : is_coprime x (y + x * z) :=
by { rw is_coprime_comm, exact h.symm.add_mul_left_left z }

lemma add_mul_right_right {x y : R} (h : is_coprime x y) (z : R) : is_coprime x (y + z * x) :=
by { rw is_coprime_comm, exact h.symm.add_mul_right_left z }

lemma mul_add_left_left {x y : R} (h : is_coprime x y) (z : R) : is_coprime (y * z + x) y :=
by { rw add_comm, exact h.add_mul_left_left z }

lemma mul_add_right_left {x y : R} (h : is_coprime x y) (z : R) : is_coprime (z * y + x) y :=
by { rw add_comm, exact h.add_mul_right_left z }

lemma mul_add_left_right {x y : R} (h : is_coprime x y) (z : R) : is_coprime x (x * z + y) :=
by { rw add_comm, exact h.add_mul_left_right z }

lemma mul_add_right_right {x y : R} (h : is_coprime x y) (z : R) : is_coprime x (z * x + y) :=
by { rw add_comm, exact h.add_mul_right_right z }

lemma add_mul_left_left_iff {x y z : R} : is_coprime (x + y * z) y ↔ is_coprime x y :=
⟨of_add_mul_left_left, λ h, h.add_mul_left_left z⟩

lemma add_mul_right_left_iff {x y z : R} : is_coprime (x + z * y) y ↔ is_coprime x y :=
⟨of_add_mul_right_left, λ h, h.add_mul_right_left z⟩

lemma add_mul_left_right_iff {x y z : R} : is_coprime x (y + x * z) ↔ is_coprime x y :=
⟨of_add_mul_left_right, λ h, h.add_mul_left_right z⟩

lemma add_mul_right_right_iff {x y z : R} : is_coprime x (y + z * x) ↔ is_coprime x y :=
⟨of_add_mul_right_right, λ h, h.add_mul_right_right z⟩

lemma mul_add_left_left_iff {x y z : R} : is_coprime (y * z + x) y ↔ is_coprime x y :=
⟨of_mul_add_left_left, λ h, h.mul_add_left_left z⟩

lemma mul_add_right_left_iff {x y z : R} : is_coprime (z * y + x) y ↔ is_coprime x y :=
⟨of_mul_add_right_left, λ h, h.mul_add_right_left z⟩

lemma mul_add_left_right_iff {x y z : R} : is_coprime x (x * z + y) ↔ is_coprime x y :=
⟨of_mul_add_left_right, λ h, h.mul_add_left_right z⟩

lemma mul_add_right_right_iff {x y z : R} : is_coprime x (z * x + y) ↔ is_coprime x y :=
⟨of_mul_add_right_right, λ h, h.mul_add_right_right z⟩

end comm_ring

end is_coprime
