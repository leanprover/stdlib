/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import data.int.parity
import algebra.module.opposites
import algebra.archimedean

/-!
# Periodicity

In this file we define and then prove facts about periodic and antiperiodic functions.

## Main definitions

* `function.periodic`: A function `f` is *periodic* if `∀ x, f (x + c) = f x`.
  `f` is referred to as periodic with period `c` or `c`-periodic.

* `function.antiperiodic`: A function `f` is *antiperiodic* if `∀ x, f (x + c) = -f x`.
  `f` is referred to as antiperiodic with antiperiod `c` or `c`-antiperiodic.

Note that any `c`-antiperiodic function will necessarily also be `2*c`-periodic.

## Tags

period, periodic, periodicity, antiperiodic
-/

variables {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

namespace function

/-! ### Periodicity -/

/-- A function `f` is said to be `periodic` with period `c` if for all `x`, `f (x + c) = f x`. -/
@[simp] def periodic [has_add α] (f : α → β) (c : α) : Prop :=
∀ x : α, f (x + c) = f x

lemma periodic.funext [has_add α]
  (h : periodic f c) :
  (λ x, f (x + c)) = f :=
funext h

lemma periodic.comp [has_add α]
  (h : periodic f c) (g : β → γ) :
  periodic (g ∘ f) c :=
by simp * at *

lemma periodic.comp_add_hom [has_add α] [has_add γ]
  (h : periodic f c) (g : add_hom γ α) (g_inv : α → γ) (hg : right_inverse g_inv g) :
  periodic (f ∘ g) (g_inv c) :=
λ x, by simp only [hg c, h (g x), add_hom.map_add, comp_app]

@[to_additive]
lemma periodic.mul [has_add α] [has_mul β]
  (hf : periodic f c) (hg : periodic g c) :
  periodic (f * g) c :=
by simp * at *

@[to_additive]
lemma periodic.div [has_add α] [has_div β]
  (hf : periodic f c) (hg : periodic g c) :
  periodic (f / g) c :=
by simp * at *

lemma periodic.const_smul [add_monoid α] [group γ] [distrib_mul_action γ α]
  (h : periodic f c) (a : γ) :
  periodic (λ x, f (a • x)) (a⁻¹ • c) :=
λ x, by simpa only [smul_add, smul_inv_smul] using h (a • x)

lemma periodic.const_smul' [add_comm_monoid α] [division_ring γ] [module γ α]
  (h : periodic f c) (a : γ) :
  periodic (λ x, f (a • x)) (a⁻¹ • c) :=
begin
  intro x,
  by_cases ha : a = 0, { simp only [ha, zero_smul] },
  simpa only [smul_add, smul_inv_smul' ha] using h (a • x),
end

lemma periodic.const_mul [division_ring α]
  (h : periodic f c) (a : α) :
  periodic (λ x, f (a * x)) (a⁻¹ * c) :=
h.const_smul' a

lemma periodic.const_inv_smul [add_monoid α] [group γ] [distrib_mul_action γ α]
  (h : periodic f c) (a : γ) :
  periodic (λ x, f (a⁻¹ • x)) (a • c) :=
by simpa only [inv_inv] using h.const_smul a⁻¹

lemma periodic.const_inv_smul' [add_comm_monoid α] [division_ring γ] [module γ α]
  (h : periodic f c) (a : γ) :
  periodic (λ x, f (a⁻¹ • x)) (a • c) :=
by simpa only [inv_inv'] using h.const_smul' a⁻¹

lemma periodic.const_inv_mul [division_ring α]
  (h : periodic f c) (a : α) :
  periodic (λ x, f (a⁻¹ * x)) (a * c) :=
h.const_inv_smul' a

lemma periodic.mul_const [division_ring α]
  (h : periodic f c) (a : α) :
  periodic (λ x, f (x * a)) (c * a⁻¹) :=
h.const_smul' $ opposite.op a

lemma periodic.mul_const' [division_ring α]
  (h : periodic f c) (a : α) :
  periodic (λ x, f (x * a)) (c / a) :=
by simpa only [div_eq_mul_inv] using h.mul_const a

lemma periodic.mul_const_inv [division_ring α]
  (h : periodic f c) (a : α) :
  periodic (λ x, f (x * a⁻¹)) (c * a) :=
h.const_inv_smul' $ opposite.op a

lemma periodic.div_const [division_ring α]
  (h : periodic f c) (a : α) :
  periodic (λ x, f (x / a)) (c * a) :=
by simpa only [div_eq_mul_inv] using h.mul_const_inv a

lemma periodic.add_period [add_semigroup α]
  (h1 : periodic f c₁) (h2 : periodic f c₂) :
  periodic f (c₁ + c₂) :=
by simp [*, ← add_assoc] at *

lemma periodic.sub_eq [add_group α]
  (h : periodic f c) (x : α) :
  f (x - c) = f x :=
by simpa only [sub_add_cancel] using (h (x - c)).symm

lemma periodic.sub_eq' [add_comm_group α]
  (h : periodic f c) :
  f (c - x) = f (-x) :=
by simpa only [sub_eq_neg_add] using h (-x)

lemma periodic.neg [add_group α]
  (h : periodic f c) :
  periodic f (-c) :=
by simpa only [sub_eq_add_neg, periodic] using h.sub_eq

lemma periodic.sub_period [add_comm_group α]
  (h1 : periodic f c₁) (h2 : periodic f c₂) :
  periodic f (c₁ - c₂) :=
let h := h2.neg in by simp [*, sub_eq_add_neg, add_comm c₁, ← add_assoc] at *

lemma periodic.nsmul [add_monoid α]
  (h : periodic f c) (n : ℕ) :
  periodic f (n • c) :=
by induction n; simp [nat.succ_eq_add_one, add_nsmul, ← add_assoc, zero_nsmul, *] at *

lemma periodic.nat_mul [semiring α]
  (h : periodic f c) (n : ℕ) :
  periodic f (n * c) :=
by simpa only [nsmul_eq_mul] using h.nsmul n

lemma periodic.neg_nsmul [add_group α]
  (h : periodic f c) (n : ℕ) :
  periodic f (-(n • c)) :=
(h.nsmul n).neg

lemma periodic.neg_nat_mul [ring α]
  (h : periodic f c) (n : ℕ) :
  periodic f (-(n * c)) :=
(h.nat_mul n).neg

lemma periodic.sub_nsmul_eq [add_group α]
  (h : periodic f c) (n : ℕ) :
  f (x - n • c) = f x :=
by simpa only [sub_eq_add_neg] using h.neg_nsmul n x

lemma periodic.sub_nat_mul_eq [ring α]
  (h : periodic f c) (n : ℕ) :
  f (x - n * c) = f x :=
by simpa only [nsmul_eq_mul] using h.sub_nsmul_eq n

lemma periodic.nsmul_sub_eq [add_comm_group α]
  (h : periodic f c) (n : ℕ) :
  f (n • c - x) = f (-x) :=
by simpa only [sub_eq_neg_add] using h.nsmul n (-x)

lemma periodic.nat_mul_sub_eq [ring α]
  (h : periodic f c) (n : ℕ) :
  f (n * c - x) = f (-x) :=
by simpa only [sub_eq_neg_add] using h.nat_mul n (-x)

lemma periodic.gsmul [add_group α]
  (h : periodic f c) (n : ℤ) :
  periodic f (n • c) :=
begin
  cases n,
  { simpa only [int.of_nat_eq_coe, gsmul_coe_nat] using h.nsmul n },
  { simpa only [gsmul_neg_succ_of_nat] using (h.nsmul n.succ).neg },
end

lemma periodic.int_mul [ring α]
  (h : periodic f c) (n : ℤ) :
  periodic f (n * c) :=
by simpa only [gsmul_eq_mul] using h.gsmul n

lemma periodic.sub_gsmul_eq [add_group α]
  (h : periodic f c) (n : ℤ) :
  f (x - n • c) = f x :=
(h.gsmul n).sub_eq x

lemma periodic.sub_int_mul_eq [ring α]
  (h : periodic f c) (n : ℤ) :
  f (x - n * c) = f x :=
(h.int_mul n).sub_eq x

lemma periodic.gsmul_sub_eq [add_comm_group α]
  (h : periodic f c) (n : ℤ) :
  f (n • c - x) = f (-x) :=
by simpa only [sub_eq_neg_add] using h.gsmul n (-x)

lemma periodic.int_mul_sub_eq [ring α]
  (h : periodic f c) (n : ℤ) :
  f (n * c - x) = f (-x) :=
by simpa only [sub_eq_neg_add] using h.int_mul n (-x)

lemma periodic.eq [add_zero_class α]
  (h : periodic f c) :
  f c = f 0 :=
by simpa only [zero_add] using h 0

lemma periodic.neg_eq [add_group α]
  (h : periodic f c) :
  f (-c) = f 0 :=
h.neg.eq

lemma periodic.nsmul_eq [add_monoid α]
  (h : periodic f c) (n : ℕ) :
  f (n • c) = f 0 :=
(h.nsmul n).eq

lemma periodic.nat_mul_eq [semiring α]
  (h : periodic f c) (n : ℕ) :
  f (n * c) = f 0 :=
(h.nat_mul n).eq

lemma periodic.gsmul_eq [add_group α]
  (h : periodic f c) (n : ℤ) :
  f (n • c) = f 0 :=
(h.gsmul n).eq

lemma periodic.int_mul_eq [ring α]
  (h : periodic f c) (n : ℤ) :
  f (n * c) = f 0 :=
(h.int_mul n).eq

/-- If a function `f` is `periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico 0 c` such that `f x = f y`. -/
lemma periodic.exists_mem_Ico [linear_ordered_add_comm_group α] [archimedean α]
  (h : periodic f c) (hc : 0 < c) (x) :
  ∃ y ∈ set.Ico 0 c, f x = f y :=
let ⟨n, H⟩ := linear_ordered_add_comm_group.exists_int_smul_near_of_pos' hc x in
⟨x - n • c, H, (h.sub_gsmul_eq n).symm⟩

lemma periodic_with_period_zero [add_zero_class α]
  (f : α → β) :
  periodic f 0 :=
λ x, by rw add_zero

/-! ### Antiperiodicity -/

/-- A function `f` is said to be `antiperiodic` with antiperiod `c` if for all `x`,
  `f (x + c) = -f x`. -/
@[simp] def antiperiodic [has_add α] [has_neg β] (f : α → β) (c : α) : Prop :=
∀ x : α, f (x + c) = -f x

lemma antiperiodic.funext [has_add α] [has_neg β]
  (h : antiperiodic f c) :
  (λ x, f (x + c)) = -f :=
funext h

lemma antiperiodic.funext' [has_add α] [add_group β]
  (h : antiperiodic f c) :
  (λ x, -f (x + c)) = f :=
(eq_neg_iff_eq_neg.mp h.funext).symm

/-- If a function is `antiperiodic` with antiperiod `c`, then it is also `periodic` with period
  `2 * c`. -/
lemma antiperiodic.periodic [semiring α] [add_group β]
  (h : antiperiodic f c) :
  periodic f (2 * c) :=
by simp [two_mul, ← add_assoc, h _]

lemma antiperiodic.eq [add_zero_class α] [has_neg β]
  (h : antiperiodic f c) : f c = -f 0 :=
by simpa only [zero_add] using h 0

lemma antiperiodic.nat_even_mul_periodic [semiring α] [add_group β]
  (h : antiperiodic f c) (n : ℕ) :
  periodic f (n * (2 * c)) :=
h.periodic.nat_mul n

lemma antiperiodic.nat_odd_mul_antiperiodic [semiring α] [add_group β]
  (h : antiperiodic f c) (n : ℕ) :
  antiperiodic f (n * (2 * c) + c) :=
λ x, by rw [← add_assoc, h, h.periodic.nat_mul]

lemma antiperiodic.int_even_mul_periodic [ring α] [add_group β]
  (h : antiperiodic f c) (n : ℤ) :
  periodic f (n * (2 * c)) :=
h.periodic.int_mul n

lemma antiperiodic.int_odd_mul_antiperiodic [ring α] [add_group β]
  (h : antiperiodic f c) (n : ℤ) :
  antiperiodic f (n * (2 * c) + c) :=
λ x, by rw [← add_assoc, h, h.periodic.int_mul]

lemma antiperiodic.nat_mul_eq_of_eq_zero [comm_semiring α] [add_group β]
  (h : antiperiodic f c) (hi : f 0 = 0) (n : ℕ) :
  f (n * c) = 0 :=
begin
  rcases nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩;
  have hk : (k : α) * (2 * c) = 2 * k * c := by rw [mul_left_comm, ← mul_assoc],
  { simpa [hk, hi] using (h.nat_even_mul_periodic k).eq },
  { simpa [add_mul, hk, hi] using (h.nat_odd_mul_antiperiodic k).eq },
end

lemma antiperiodic.int_mul_eq_of_eq_zero [comm_ring α] [add_group β]
  (h : antiperiodic f c) (hi : f 0 = 0) (n : ℤ) :
  f (n * c) = 0 :=
begin
  rcases int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩;
  have hk : (k : α) * (2 * c) = 2 * k * c := by rw [mul_left_comm, ← mul_assoc],
  { simpa [hk, hi] using (h.int_even_mul_periodic k).eq },
  { simpa [add_mul, hk, hi] using (h.int_odd_mul_antiperiodic k).eq },
end

lemma antiperiodic.sub_eq [add_group α] [add_group β]
  (h : antiperiodic f c) (x : α) :
  f (x - c) = -f x :=
by simp only [eq_neg_iff_eq_neg.mp (h (x - c)), sub_add_cancel]

lemma antiperiodic.sub_eq' [add_comm_group α] [add_group β]
  (h : antiperiodic f c) :
  f (c - x) = -f (-x) :=
by simpa only [sub_eq_neg_add] using h (-x)

lemma antiperiodic.neg [add_group α] [add_group β]
  (h : antiperiodic f c) :
  antiperiodic f (-c) :=
by simpa only [sub_eq_add_neg, antiperiodic] using h.sub_eq

lemma antiperiodic.neg_eq [add_group α] [add_group β]
  (h : antiperiodic f c) :
  f (-c) = -f 0 :=
by simpa only [zero_add] using h.neg 0

lemma antiperiodic.const_smul [add_monoid α] [has_neg β] [group γ] [distrib_mul_action γ α]
  (h : antiperiodic f c) (a : γ) :
  antiperiodic (λ x, f (a • x)) (a⁻¹ • c) :=
λ x, by simpa only [smul_add, smul_inv_smul] using h (a • x)

lemma antiperiodic.const_smul' [add_comm_monoid α] [has_neg β] [division_ring γ] [module γ α]
  (h : antiperiodic f c) {a : γ} (ha : a ≠ 0) :
  antiperiodic (λ x, f (a • x)) (a⁻¹ • c) :=
λ x, by simpa only [smul_add, smul_inv_smul' ha] using h (a • x)

lemma antiperiodic.const_mul [division_ring α] [has_neg β]
  (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
  antiperiodic (λ x, f (a * x)) (a⁻¹ * c) :=
h.const_smul' ha

lemma antiperiodic.const_inv_smul [add_monoid α] [has_neg β] [group γ] [distrib_mul_action γ α]
  (h : antiperiodic f c) (a : γ) :
  antiperiodic (λ x, f (a⁻¹ • x)) (a • c) :=
by simpa only [inv_inv] using h.const_smul a⁻¹

lemma antiperiodic.const_inv_smul' [add_comm_monoid α] [has_neg β] [division_ring γ] [module γ α]
  (h : antiperiodic f c) {a : γ} (ha : a ≠ 0) :
  antiperiodic (λ x, f (a⁻¹ • x)) (a • c) :=
by simpa only [inv_inv'] using h.const_smul' (inv_ne_zero ha)

lemma antiperiodic.const_inv_mul [division_ring α] [has_neg β]
  (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
  antiperiodic (λ x, f (a⁻¹ * x)) (a * c) :=
h.const_inv_smul' ha

lemma antiperiodic.mul_const [division_ring α] [has_neg β]
  (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
  antiperiodic (λ x, f (x * a)) (c * a⁻¹) :=
h.const_smul' $ (opposite.op_ne_zero_iff a).mpr ha

lemma antiperiodic.mul_const' [division_ring α] [has_neg β]
  (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
  antiperiodic (λ x, f (x * a)) (c / a) :=
by simpa only [div_eq_mul_inv] using h.mul_const ha

lemma antiperiodic.mul_const_inv [division_ring α] [has_neg β]
  (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
  antiperiodic (λ x, f (x * a⁻¹)) (c * a) :=
h.const_inv_smul' $ (opposite.op_ne_zero_iff a).mpr ha

lemma antiperiodic.div_inv [division_ring α] [has_neg β]
  (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
  antiperiodic (λ x, f (x / a)) (c * a) :=
by simpa only [div_eq_mul_inv] using h.mul_const_inv ha

lemma antiperiodic.add [add_group α] [add_group β]
  (h1 : antiperiodic f c₁) (h2 : antiperiodic f c₂) :
  periodic f (c₁ + c₂) :=
by simp [*, ← add_assoc] at *

lemma antiperiodic.sub [add_comm_group α] [add_group β]
  (h1 : antiperiodic f c₁) (h2 : antiperiodic f c₂) :
  periodic f (c₁ - c₂) :=
let h := h2.neg in by simp [*, sub_eq_add_neg, add_comm c₁, ← add_assoc] at *

lemma periodic.add_antiperiod [add_group α] [add_group β]
  (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
  antiperiodic f (c₁ + c₂) :=
by simp [*, ← add_assoc] at *

lemma periodic.sub_antiperiod [add_comm_group α] [add_group β]
  (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
  antiperiodic f (c₁ - c₂) :=
let h := h2.neg in by simp [*, sub_eq_add_neg, add_comm c₁, ← add_assoc] at *

lemma periodic.add_antiperiod_eq [add_group α] [add_group β]
  (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
  f (c₁ + c₂) = -f 0 :=
(h1.add_antiperiod h2).eq

lemma periodic.sub_antiperiod_eq [add_comm_group α] [add_group β]
  (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
  f (c₁ - c₂) = -f 0 :=
(h1.sub_antiperiod h2).eq

lemma antiperiodic.mul [has_add α] [ring β]
  (hf : antiperiodic f c) (hg : antiperiodic g c) :
  periodic (f * g) c :=
by simp * at *

lemma antiperiodic.div [has_add α] [division_ring β]
  (hf : antiperiodic f c) (hg : antiperiodic g c) :
  periodic (f / g) c :=
by simp [*, neg_div_neg_eq] at *

end function
