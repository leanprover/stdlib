/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import data.nat.choose.sum
import algebra.algebra.basic

/-!
# Nilpotent elements

## Main definitions

  * `is_nilpotent`
  * `is_nilpotent_neg_iff`
  * `commute.is_nilpotent_add`
  * `commute.is_nilpotent_mul_left`
  * `commute.is_nilpotent_mul_right`
  * `commute.is_nilpotent_sub`

-/

universes u v

variables {R : Type u} {x y : R}

/-- An element is said to be nilpotent if some natural-number-power of it equals zero.

Note that we require only the bare minimum assumptions for the definition to make sense. Even
`monoid_with_zero` is too strong since nilpotency is important in the study of rings that are only
power-associative. -/
def is_nilpotent [has_zero R] [has_pow R ℕ] (x : R) : Prop := ∃ (n : ℕ), x^n = 0

lemma is_nilpotent.zero [monoid_with_zero R] : is_nilpotent (0 : R) := ⟨1, pow_one 0⟩

lemma is_nilpotent.neg [ring R] (h : is_nilpotent x) : is_nilpotent (-x) :=
begin
  obtain ⟨n, hn⟩ := h,
  use n,
  rw [neg_pow, hn, mul_zero],
end

@[simp] lemma is_nilpotent_neg_iff [ring R] : is_nilpotent (-x) ↔ is_nilpotent x :=
⟨λ h, neg_neg x ▸ h.neg, λ h, h.neg⟩

lemma is_nilpotent.eq_zero [monoid_with_zero R] [no_zero_divisors R]
  (h : is_nilpotent x) : x = 0 :=
by { obtain ⟨n, hn⟩ := h, exact pow_eq_zero hn, }

@[simp] lemma is_nilpotent_iff_eq_zero [monoid_with_zero R] [no_zero_divisors R] :
  is_nilpotent x ↔ x = 0 :=
⟨λ h, h.eq_zero, λ h, h.symm ▸ is_nilpotent.zero⟩

namespace commute

section semiring

variables [semiring R] (h_comm : commute x y)

include h_comm

lemma is_nilpotent_add (hx : is_nilpotent x) (hy : is_nilpotent y) : is_nilpotent (x + y) :=
begin
  obtain ⟨n, hn⟩ := hx,
  obtain ⟨m, hm⟩ := hy,
  use n + m - 1,
  rw h_comm.add_pow',
  apply finset.sum_eq_zero,
  rintros ⟨i, j⟩ hij,
  suffices : x^i * y^j = 0, { simp only [this, nsmul_eq_mul, mul_zero], },
  cases nat.le_or_le_of_add_eq_add_pred (finset.nat.mem_antidiagonal.mp hij) with hi hj,
  { rw [pow_eq_zero_of_le hi hn, zero_mul], },
  { rw [pow_eq_zero_of_le hj hm, mul_zero], },
end

lemma is_nilpotent_mul_left (h : is_nilpotent x) : is_nilpotent (x * y) :=
begin
  obtain ⟨n, hn⟩ := h,
  use n,
  rw [h_comm.mul_pow, hn, zero_mul],
end

lemma is_nilpotent_mul_right (h : is_nilpotent y) : is_nilpotent (x * y) :=
by { rw h_comm.eq, exact h_comm.symm.is_nilpotent_mul_left h, }

end semiring

section ring

variables [ring R] (h_comm : commute x y)

include h_comm

lemma is_nilpotent_sub (hx : is_nilpotent x) (hy : is_nilpotent y) : is_nilpotent (x - y) :=
begin
  rw ← neg_right_iff at h_comm,
  rw ← is_nilpotent_neg_iff at hy,
  rw sub_eq_add_neg,
  exact h_comm.is_nilpotent_add hx hy,
end

end ring

end commute

namespace algebra

variables (R) {A : Type v} [comm_semiring R] [semiring A] [algebra R A]

@[simp] lemma is_nilpotent_lmul_left_iff (a : A) :
  is_nilpotent (lmul_left R a) ↔ is_nilpotent a :=
begin
  split; rintros ⟨n, hn⟩; use n;
  simp only [lmul_left_eq_zero_iff, pow_lmul_left] at ⊢ hn;
  exact hn,
end

@[simp] lemma is_nilpotent_lmul_right_iff (a : A) :
  is_nilpotent (lmul_right R a) ↔ is_nilpotent a :=
begin
  split; rintros ⟨n, hn⟩; use n;
  simp only [lmul_right_eq_zero_iff, pow_lmul_right] at ⊢ hn;
  exact hn,
end

end algebra
