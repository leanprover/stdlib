/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Robert Y. Lewis
-/
import data.real.cau_seq

/-!
# Cauchy completion

This file generalizes the Cauchy completion of `(ℚ, abs)` to the completion of a commutative ring
with absolute value.
-/

namespace cau_seq.completion
open cau_seq

section
parameters {α : Type*} [linear_ordered_field α]
parameters {β : Type*} [comm_ring β] {abv : β → α} [is_absolute_value abv]

def Cauchy := @quotient (cau_seq _ abv) cau_seq.equiv

def mk : cau_seq _ abv → Cauchy := quotient.mk

@[simp] theorem mk_eq_mk (f) : @eq Cauchy ⟦f⟧ (mk f) := rfl

theorem mk_eq {f g} : mk f = mk g ↔ f ≈ g := quotient.eq

def of_rat (x : β) : Cauchy := mk (const abv x)

instance : has_zero Cauchy := ⟨of_rat 0⟩
instance : has_one Cauchy := ⟨of_rat 1⟩
instance : inhabited Cauchy := ⟨0⟩

theorem of_rat_zero : of_rat 0 = 0 := rfl
theorem of_rat_one : of_rat 1 = 1 := rfl

@[simp] theorem mk_eq_zero {f} : mk f = 0 ↔ lim_zero f :=
by have : mk f = 0 ↔ lim_zero (f - 0) := quotient.eq;
   rwa sub_zero at this

instance : has_add Cauchy :=
⟨λ x y, quotient.lift_on₂ x y (λ f g, mk (f + g)) $
  λ f₁ g₁ f₂ g₂ hf hg, quotient.sound $
  by simpa [(≈), setoid.r, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using add_lim_zero hf hg⟩

@[simp] theorem mk_add (f g : cau_seq β abv) : mk f + mk g = mk (f + g) := rfl

instance : has_neg Cauchy :=
⟨λ x, quotient.lift_on x (λ f, mk (-f)) $
  λ f₁ f₂ hf, quotient.sound $
  by simpa [(≈), setoid.r] using neg_lim_zero hf⟩

@[simp] theorem mk_neg (f : cau_seq β abv) : -mk f = mk (-f) := rfl

instance : has_mul Cauchy :=
⟨λ x y, quotient.lift_on₂ x y (λ f g, mk (f * g)) $
  λ f₁ g₁ f₂ g₂ hf hg, quotient.sound $
  by simpa [(≈), setoid.r, mul_add, mul_comm, add_assoc, sub_eq_add_neg] using
    add_lim_zero (mul_lim_zero_right g₁ hf) (mul_lim_zero_right f₂ hg)⟩

@[simp] theorem mk_mul (f g : cau_seq β abv) : mk f * mk g = mk (f * g) := rfl

instance : has_sub Cauchy :=
⟨λ x y, quotient.lift_on₂ x y (λ f g, mk (f - g)) $
  λ f₁ g₁ f₂ g₂ hf hg, quotient.sound $ show ((f₁ - g₁) - (f₂ - g₂)).lim_zero,
    by simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using sub_lim_zero hf hg⟩

@[simp] theorem mk_sub (f g : cau_seq β abv) : mk f - mk g = mk (f - g) := rfl

theorem of_rat_add (x y : β) : of_rat (x + y) = of_rat x + of_rat y :=
congr_arg mk (const_add _ _)

theorem of_rat_neg (x : β) : of_rat (-x) = -of_rat x :=
congr_arg mk (const_neg _)

theorem of_rat_mul (x y : β) : of_rat (x * y) = of_rat x * of_rat y :=
congr_arg mk (const_mul _ _)

private lemma zero_def : 0 = mk 0 := rfl

private lemma one_def : 1 = mk 1 := rfl

instance : comm_ring Cauchy :=
by refine { neg := has_neg.neg, sub := has_sub.sub, sub_eq_add_neg := _,
    add := (+), zero := (0 : Cauchy), mul := (*), one := 1, nsmul := nsmul_rec, npow := npow_rec,
    gsmul := gsmul_rec, .. }; try { intros; refl };
{ repeat {refine λ a, quotient.induction_on a (λ _, _)},
  simp [zero_def, one_def, mul_left_comm, mul_comm, mul_add, add_comm, add_left_comm,
          sub_eq_add_neg] }

theorem of_rat_sub (x y : β) : of_rat (x - y) = of_rat x - of_rat y :=
congr_arg mk (const_sub _ _)

end

open_locale classical
section

parameters {α : Type*} [linear_ordered_field α]
parameters {β : Type*} [field β] {abv : β → α} [is_absolute_value abv]
local notation `Cauchy` := @Cauchy _ _ _ _ abv _

noncomputable instance : has_inv Cauchy :=
⟨λ x, quotient.lift_on x
  (λ f, mk $ if h : lim_zero f then 0 else inv f h) $
λ f g fg, begin
  have := lim_zero_congr fg,
  by_cases hf : lim_zero f,
  { simp [hf, this.1 hf, setoid.refl] },
  { have hg := mt this.2 hf, simp [hf, hg],
    have If : mk (inv f hf) * mk f = 1 := mk_eq.2 (inv_mul_cancel hf),
    have Ig : mk (inv g hg) * mk g = 1 := mk_eq.2 (inv_mul_cancel hg),
    rw [mk_eq.2 fg, ← Ig] at If,
    rw mul_comm at Ig,
    rw [← mul_one (mk (inv f hf)), ← Ig, ← mul_assoc, If,
        mul_assoc, Ig, mul_one] }
end⟩

@[simp] theorem inv_zero : (0 : Cauchy)⁻¹ = 0 :=
congr_arg mk $ by rw dif_pos; [refl, exact zero_lim_zero]

@[simp] theorem inv_mk {f} (hf) : (@mk α _ β _ abv _ f)⁻¹ = mk (inv f hf) :=
congr_arg mk $ by rw dif_neg

lemma cau_seq_zero_ne_one : ¬ (0 : cau_seq _ abv) ≈ 1 := λ h,
have lim_zero (1 - 0), from setoid.symm h,
have lim_zero 1, by simpa,
one_ne_zero $ const_lim_zero.1 this

lemma zero_ne_one : (0 : Cauchy) ≠ 1 :=
λ h, cau_seq_zero_ne_one $ mk_eq.1 h

protected theorem inv_mul_cancel {x : Cauchy} : x ≠ 0 → x⁻¹ * x = 1 :=
quotient.induction_on x $ λ f hf, begin
  simp at hf, simp [hf],
  exact quotient.sound (cau_seq.inv_mul_cancel hf)
end

noncomputable def field : field Cauchy :=
{ inv              := has_inv.inv,
  mul_inv_cancel   := λ x x0, by rw [mul_comm, cau_seq.completion.inv_mul_cancel x0],
  exists_pair_ne   := ⟨0, 1, zero_ne_one⟩,
  inv_zero         := inv_zero,
  .. Cauchy.comm_ring }

local attribute [instance] field

theorem of_rat_inv (x : β) : of_rat (x⁻¹) = ((of_rat x)⁻¹ : Cauchy) :=
congr_arg mk $ by split_ifs with h; [simp [const_lim_zero.1 h], refl]

theorem of_rat_div (x y : β) : of_rat (x / y) = (of_rat x / of_rat y : Cauchy) :=
by simp only [div_eq_inv_mul, of_rat_inv, of_rat_mul]

end
end cau_seq.completion

variables {α : Type*} [linear_ordered_field α]
namespace cau_seq
section

variables (β : Type*) [ring β] (abv : β → α) [is_absolute_value abv]

class is_complete :=
(is_complete : ∀ s : cau_seq β abv, ∃ b : β, s ≈ const abv b)
end

section

variables {β : Type*} [ring β] {abv : β → α} [is_absolute_value abv]
variable [is_complete β abv]

lemma complete : ∀ s : cau_seq β abv, ∃ b : β, s ≈ const abv b :=
is_complete.is_complete

noncomputable def lim (s : cau_seq β abv) := classical.some (complete s)

lemma equiv_lim (s : cau_seq β abv) : s ≈ const abv (lim s) :=
classical.some_spec (complete s)

lemma eq_lim_of_const_equiv {f : cau_seq β abv} {x : β} (h : cau_seq.const abv x ≈ f) : x = lim f :=
const_equiv.mp $ setoid.trans h $ equiv_lim f

lemma lim_eq_of_equiv_const {f : cau_seq β abv} {x : β} (h : f ≈ cau_seq.const abv x) : lim f = x :=
(eq_lim_of_const_equiv $ setoid.symm h).symm

lemma lim_eq_lim_of_equiv {f g : cau_seq β abv} (h : f ≈ g) : lim f = lim g :=
lim_eq_of_equiv_const $ setoid.trans h $ equiv_lim g

@[simp] lemma lim_const (x : β) : lim (const abv x) = x :=
lim_eq_of_equiv_const $ setoid.refl _

lemma lim_add (f g : cau_seq β abv) : lim f + lim g = lim (f + g) :=
eq_lim_of_const_equiv $ show lim_zero (const abv (lim f + lim g) - (f + g)),
  by rw [const_add, add_sub_comm];
  exact add_lim_zero (setoid.symm (equiv_lim f)) (setoid.symm (equiv_lim g))

lemma lim_mul_lim (f g : cau_seq β abv) : lim f * lim g = lim (f * g) :=
eq_lim_of_const_equiv $ show lim_zero (const abv (lim f * lim g) - f * g),
  from have h : const abv (lim f * lim g) - f * g = (const abv (lim f) - f) * g
      + const abv (lim f) * (const abv (lim g) - g) :=
    by simp [const_mul (lim f), mul_add, add_mul, sub_eq_add_neg, add_comm, add_left_comm],
  by rw h; exact add_lim_zero (mul_lim_zero_left _ (setoid.symm (equiv_lim _)))
    (mul_lim_zero_right _ (setoid.symm (equiv_lim _)))

lemma lim_mul (f : cau_seq β abv) (x : β) : lim f * x = lim (f * const abv x) :=
by rw [← lim_mul_lim, lim_const]

lemma lim_neg (f : cau_seq β abv) : lim (-f) = -lim f :=
lim_eq_of_equiv_const (show lim_zero (-f - const abv (-lim f)),
  by rw [const_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg];
  exact setoid.symm (equiv_lim f))

lemma lim_eq_zero_iff (f : cau_seq β abv) : lim f = 0 ↔ lim_zero f :=
⟨assume h,
  by have hf := equiv_lim f;
  rw h at hf;
  exact (lim_zero_congr hf).mpr (const_lim_zero.mpr rfl),
assume h,
  have h₁ : f = (f - const abv 0) := ext (λ n, by simp [sub_apply, const_apply]),
  by rw h₁ at h; exact lim_eq_of_equiv_const h ⟩

end

section
variables {β : Type*} [field β] {abv : β → α} [is_absolute_value abv] [is_complete β abv]

lemma lim_inv {f : cau_seq β abv} (hf : ¬ lim_zero f) : lim (inv f hf) = (lim f)⁻¹ :=
have hl : lim f ≠ 0 := by rwa ← lim_eq_zero_iff at hf,
lim_eq_of_equiv_const $ show lim_zero (inv f hf - const abv (lim f)⁻¹),
  from have h₁ : ∀ (g f : cau_seq β abv) (hf : ¬ lim_zero f), lim_zero (g - f * inv f hf * g) :=
    λ g f hf, by rw [← one_mul g, ← mul_assoc, ← sub_mul, mul_one, mul_comm, mul_comm f];
    exact mul_lim_zero_right _ (setoid.symm (cau_seq.inv_mul_cancel _)),
  have h₂ : lim_zero ((inv f hf - const abv (lim f)⁻¹) - (const abv (lim f) - f) *
      (inv f hf * const abv (lim f)⁻¹)) :=
    by rw [sub_mul, ← sub_add, sub_sub, sub_add_eq_sub_sub, sub_right_comm, sub_add];
    exact show lim_zero (inv f hf - const abv (lim f) * (inv f hf * const abv (lim f)⁻¹)
      - (const abv (lim f)⁻¹ - f * (inv f hf * const abv (lim f)⁻¹))),
    from sub_lim_zero
      (by rw [← mul_assoc, mul_right_comm, const_inv hl]; exact h₁ _ _ _)
      (by rw [← mul_assoc]; exact h₁ _ _ _),
  (lim_zero_congr h₂).mpr $ mul_lim_zero_left _ (setoid.symm (equiv_lim f))

end

section
variables [is_complete α abs]

lemma lim_le {f : cau_seq α abs} {x : α}
  (h : f ≤ cau_seq.const abs x) : lim f ≤ x :=
cau_seq.const_le.1 $ cau_seq.le_of_eq_of_le (setoid.symm (equiv_lim f)) h

lemma le_lim {f : cau_seq α abs} {x : α}
  (h : cau_seq.const abs x ≤ f) : x ≤ lim f :=
cau_seq.const_le.1 $ cau_seq.le_of_le_of_eq h (equiv_lim f)

lemma lt_lim {f : cau_seq α abs} {x : α}
  (h : cau_seq.const abs x < f) : x < lim f :=
cau_seq.const_lt.1 $ cau_seq.lt_of_lt_of_eq h (equiv_lim f)

lemma lim_lt {f : cau_seq α abs} {x : α}
  (h : f < cau_seq.const abs x) : lim f < x :=
cau_seq.const_lt.1 $ cau_seq.lt_of_eq_of_lt (setoid.symm (equiv_lim f)) h

end
end cau_seq
