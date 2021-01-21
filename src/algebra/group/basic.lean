/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import algebra.group.defs

universe u

section associative
variables {α : Type u} (f : α → α → α) [is_associative α f] (x y : α)

/--
Composing two associative operations of `f : α → α → α` on the left
is equal to an associative operation on the left.
-/
lemma comp_assoc_left : (f x) ∘ (f y) = (f (f x y)) :=
by { ext z, rw [function.comp_apply, @is_associative.assoc _ f] }

/--
Composing two associative operations of `f : α → α → α` on the right
is equal to an associative operation on the right.
-/
lemma comp_assoc_right : (λ z, f z x) ∘ (λ z, f z y) = (λ z, f z (f y x)) :=
by { ext z, rw [function.comp_apply, @is_associative.assoc _ f] }

end associative

section semigroup
variables {α : Type*}

/--
Composing two multiplications on the left by `y` then `x`
is equal to a multiplication on the left by `x * y`.
-/
@[simp, to_additive
"Composing two additions on the left by `y` then `x`
is equal to a addition on the left by `x + y`."]
lemma comp_mul_left [semigroup α] (x y : α) :
  ((*) x) ∘ ((*) y) = ((*) (x * y)) :=
comp_assoc_left _ _ _

/--
Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
@[simp, to_additive
"Composing two additions on the right by `y` and `x`
is equal to a addition on the right by `y + x`."]
lemma comp_mul_right [semigroup α] (x y : α) :
  (* x) ∘ (* y) = (* (y * x)) :=
comp_assoc_right _ _ _

end semigroup

section monoid
variables {M : Type u} [monoid M]

@[to_additive]
lemma ite_mul_one {P : Prop} [decidable P] {a b : M} :
  ite P (a * b) 1 = ite P a 1 * ite P b 1 :=
by { by_cases h : P; simp [h], }

@[to_additive]
lemma eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 :=
by split; { rintro rfl, simpa using h }

end monoid

section comm_semigroup
variables {G : Type u} [comm_semigroup G]

@[no_rsimp, to_additive]
lemma mul_left_comm : ∀ a b c : G, a * (b * c) = b * (a * c) :=
left_comm has_mul.mul mul_comm mul_assoc
attribute [no_rsimp] add_left_comm

@[to_additive]
lemma mul_right_comm : ∀ a b c : G, a * b * c = a * c * b :=
right_comm has_mul.mul mul_comm mul_assoc

@[to_additive]
theorem mul_mul_mul_comm (a b c d : G) : (a * b) * (c * d) = (a * c) * (b * d) :=
by simp only [mul_left_comm, mul_assoc]

end comm_semigroup

local attribute [simp] mul_assoc sub_eq_add_neg

section add_monoid
variables {M : Type u} [add_monoid M] {a b c : M}

@[simp] lemma bit0_zero : bit0 (0 : M) = 0 := add_zero _
@[simp] lemma bit1_zero [has_one M] : bit1 (0 : M) = 1 :=
by rw [bit1, bit0_zero, zero_add]

end add_monoid

section comm_monoid
variables {M : Type u} [comm_monoid M] {x y z : M}

@[to_additive] lemma inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z :=
left_inv_eq_right_inv (trans (mul_comm _ _) hy) hz

end comm_monoid

section left_cancel_monoid

variables {M : Type u} [left_cancel_monoid M] {a b : M}

@[simp, to_additive] lemma mul_eq_left_iff : a * b = a ↔ b = 1 :=
calc a * b = a ↔ a * b = a * 1 : by rw mul_one
           ... ↔ b = 1         : mul_left_cancel_iff

@[simp, to_additive] lemma left_eq_mul_iff : a = a * b ↔ b = 1 :=
eq_comm.trans mul_eq_left_iff

end left_cancel_monoid

section right_cancel_monoid

variables {M : Type u} [right_cancel_monoid M] {a b : M}

@[simp, to_additive] lemma mul_eq_right_iff : a * b = b ↔ a = 1 :=
calc a * b = b ↔ a * b = 1 * b : by rw one_mul
           ... ↔ a = 1         : mul_right_cancel_iff

@[simp, to_additive] lemma right_eq_mul_iff : b = a * b ↔ a = 1 :=
eq_comm.trans mul_eq_right_iff

end right_cancel_monoid

section div_inv_monoid

variables {G : Type u} [div_inv_monoid G]

@[to_additive]
lemma inv_eq_one_div (x : G) :
  x⁻¹ = 1 / x :=
by rw [div_eq_mul_inv, one_mul]

@[to_additive]
lemma mul_one_div (x y : G) :
  x * (1 / y) = x / y :=
by rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]

lemma mul_div_assoc {a b c : G} : a * b / c = a * (b / c) :=
by rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]

lemma mul_div_assoc' (a b c : G) : a * (b / c) = (a * b) / c :=
mul_div_assoc.symm

@[simp, to_additive] lemma one_div (a : G) : 1 / a = a⁻¹ :=
(inv_eq_one_div a).symm

end div_inv_monoid

section group
variables {G : Type u} [group G] {a b c : G}

@[simp, to_additive]
lemma inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a :=
by simp [mul_assoc]

@[simp, to_additive neg_zero]
lemma one_inv : 1⁻¹ = (1 : G) :=
inv_eq_of_mul_eq_one (one_mul 1)

@[to_additive]
theorem left_inverse_inv (G) [group G] :
  function.left_inverse (λ a : G, a⁻¹) (λ a, a⁻¹) :=
inv_inv

@[simp, to_additive]
lemma inv_involutive : function.involutive (has_inv.inv : G → G) := inv_inv

@[to_additive]
lemma inv_injective : function.injective (has_inv.inv : G → G) :=
inv_involutive.injective

@[simp, to_additive] theorem inv_inj : a⁻¹ = b⁻¹ ↔ a = b := inv_injective.eq_iff

@[simp, to_additive]
lemma mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b :=
by rw [← mul_assoc, mul_right_inv, one_mul]

@[to_additive]
theorem mul_left_surjective (a : G) : function.surjective ((*) a) :=
λ x, ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

@[to_additive]
theorem mul_right_surjective (a : G) : function.surjective (λ x, x * a) :=
λ x, ⟨x * a⁻¹, inv_mul_cancel_right x a⟩

@[simp, to_additive neg_add_rev]
lemma mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
inv_eq_of_mul_eq_one $ by simp

@[to_additive]
lemma eq_inv_of_eq_inv (h : a = b⁻¹) : b = a⁻¹ :=
by simp [h]

@[to_additive]
lemma eq_inv_of_mul_eq_one (h : a * b = 1) : a = b⁻¹ :=
have a⁻¹ = b, from inv_eq_of_mul_eq_one h,
by simp [this.symm]

@[to_additive]
lemma eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹ :=
by simp [h.symm]

@[to_additive]
lemma eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c :=
by simp [h.symm]

@[to_additive]
lemma inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c :=
by simp [h]

@[to_additive]
lemma mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c :=
by simp [h]

@[to_additive]
lemma eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c :=
by simp [h.symm]

@[to_additive]
lemma eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c :=
by simp [h.symm, mul_inv_cancel_left]

@[to_additive]
lemma mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c :=
by rw [h, mul_inv_cancel_left]

@[to_additive]
lemma mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c :=
by simp [h]

@[to_additive]
theorem mul_self_iff_eq_one : a * a = a ↔ a = 1 :=
by have := @mul_right_inj _ _ a a 1; rwa mul_one at this

@[simp, to_additive]
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
by rw [← @inv_inj _ _ a 1, one_inv]

@[simp, to_additive]
theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
by rw [eq_comm, inv_eq_one]

@[to_additive]
theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
not_congr inv_eq_one

@[to_additive]
theorem eq_inv_iff_eq_inv : a = b⁻¹ ↔ b = a⁻¹ :=
⟨eq_inv_of_eq_inv, eq_inv_of_eq_inv⟩

@[to_additive]
theorem inv_eq_iff_inv_eq : a⁻¹ = b ↔ b⁻¹ = a :=
eq_comm.trans $ eq_inv_iff_eq_inv.trans eq_comm

@[to_additive]
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
by simpa [mul_left_inv, -mul_left_inj] using @mul_left_inj _ _ b a (b⁻¹)

@[to_additive]
theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b :=
by rw [mul_eq_one_iff_eq_inv, eq_inv_iff_eq_inv, eq_comm]

@[to_additive]
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
mul_eq_one_iff_eq_inv.symm

@[to_additive]
theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
mul_eq_one_iff_inv_eq.symm

@[to_additive]
theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
⟨λ h, by rw [h, inv_mul_cancel_right], λ h, by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]
theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
⟨λ h, by rw [h, mul_inv_cancel_left], λ h, by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]
theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
⟨λ h, by rw [← h, mul_inv_cancel_left], λ h, by rw [h, inv_mul_cancel_left]⟩

@[to_additive]
theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
⟨λ h, by rw [← h, inv_mul_cancel_right], λ h, by rw [h, mul_inv_cancel_right]⟩

@[to_additive]
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b :=
by rw [mul_eq_one_iff_eq_inv, inv_inv]

@[to_additive]
theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b :=
by rw [mul_eq_one_iff_eq_inv, inv_inj]

@[simp, to_additive]
lemma mul_left_eq_self : a * b = b ↔ a = 1 :=
⟨λ h, @mul_right_cancel _ _ a b 1 (by simp [h]), λ h, by simp [h]⟩

@[simp, to_additive]
lemma mul_right_eq_self : a * b = a ↔ b = 1 :=
⟨λ h, @mul_left_cancel _ _ a b 1 (by simp [h]), λ h, by simp [h]⟩

@[to_additive]
lemma div_left_injective : function.injective (λ a, a / b) :=
by simpa only [div_eq_mul_inv] using λ a a' h, mul_left_injective (b⁻¹) h

@[to_additive]
lemma div_right_injective : function.injective (λ a, b / a) :=
by simpa only [div_eq_mul_inv] using λ a a' h, inv_injective (mul_right_injective b h)

end group

section add_group
variables {G : Type u} [add_group G] {a b c d : G}

@[simp] lemma sub_self (a : G) : a - a = 0 :=
by rw [sub_eq_add_neg, add_right_neg a]

@[simp] lemma sub_add_cancel (a b : G) : a - b + b = a :=
by rw [sub_eq_add_neg, neg_add_cancel_right a b]

@[simp] lemma add_sub_cancel (a b : G) : a + b - b = a :=
by rw [sub_eq_add_neg, add_neg_cancel_right a b]

lemma add_sub_assoc (a b c : G) : a + b - c = a + (b - c) :=
by rw [sub_eq_add_neg, add_assoc, ←sub_eq_add_neg]

lemma eq_of_sub_eq_zero (h : a - b = 0) : a = b :=
have 0 + b = b, by rw zero_add,
have (a - b) + b = b, by rwa h,
by rwa [sub_eq_add_neg, neg_add_cancel_right] at this

lemma sub_eq_zero_of_eq (h : a = b) : a - b = 0 :=
by rw [h, sub_self]

lemma sub_eq_zero_iff_eq : a - b = 0 ↔ a = b :=
⟨eq_of_sub_eq_zero, sub_eq_zero_of_eq⟩

@[simp] lemma sub_zero (a : G) : a - 0 = a :=
by rw [sub_eq_add_neg, neg_zero, add_zero]

lemma sub_ne_zero_of_ne (h : a ≠ b) : a - b ≠ 0 :=
begin
  intro hab,
  apply h,
  apply eq_of_sub_eq_zero hab
end

@[simp] lemma sub_neg_eq_add (a b : G) : a - (-b) = a + b :=
by rw [sub_eq_add_neg, neg_neg]

@[simp] lemma neg_sub (a b : G) : -(a - b) = b - a :=
neg_eq_of_add_eq_zero (by rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, neg_add_cancel_left,
  add_right_neg])

local attribute [simp] add_assoc

lemma add_sub (a b c : G) : a + (b - c) = a + b - c :=
by simp

lemma sub_add_eq_sub_sub_swap (a b c : G) : a - (b + c) = a - c - b :=
by simp

@[simp] lemma add_sub_add_right_eq_sub (a b c : G) : (a + c) - (b + c) = a - b :=
by rw [sub_add_eq_sub_sub_swap]; simp

lemma eq_sub_of_add_eq (h : a + c = b) : a = b - c :=
by simp [h.symm]

lemma sub_eq_of_eq_add (h : a = c + b) : a - b = c :=
by simp [h]

lemma eq_add_of_sub_eq (h : a - c = b) : a = b + c :=
by simp [h.symm]

lemma add_eq_of_eq_sub (h : a = c - b) : a + b = c :=
by simp [h]

@[simp] lemma sub_right_inj : a - b = a - c ↔ b = c :=
sub_right_injective.eq_iff

@[simp] lemma sub_left_inj : b - a = c - a ↔ b = c :=
by { rw [sub_eq_add_neg, sub_eq_add_neg], exact add_left_inj _ }

lemma sub_add_sub_cancel (a b c : G) : (a - b) + (b - c) = a - c :=
by rw [← add_sub_assoc, sub_add_cancel]

lemma sub_sub_sub_cancel_right (a b c : G) : (a - c) - (b - c) = a - b :=
by rw [← neg_sub c b, sub_neg_eq_add, sub_add_sub_cancel]

theorem sub_sub_assoc_swap : a - (b - c) = a + c - b :=
by simp

theorem sub_eq_zero : a - b = 0 ↔ a = b :=
⟨eq_of_sub_eq_zero, λ h, by rw [h, sub_self]⟩

theorem sub_ne_zero : a - b ≠ 0 ↔ a ≠ b :=
not_congr sub_eq_zero

theorem eq_sub_iff_add_eq : a = b - c ↔ a + c = b :=
by rw [sub_eq_add_neg, eq_add_neg_iff_add_eq]

theorem sub_eq_iff_eq_add : a - b = c ↔ a = c + b :=
by rw [sub_eq_add_neg, add_neg_eq_iff_eq_add]

theorem eq_iff_eq_of_sub_eq_sub (H : a - b = c - d) : a = b ↔ c = d :=
by rw [← sub_eq_zero, H, sub_eq_zero]

theorem left_inverse_sub_add_left (c : G) : function.left_inverse (λ x, x - c) (λ x, x + c) :=
assume x, add_sub_cancel x c

theorem left_inverse_add_left_sub (c : G) : function.left_inverse (λ x, x + c) (λ x, x - c) :=
assume x, sub_add_cancel x c

theorem left_inverse_add_right_neg_add (c : G) :
  function.left_inverse (λ x, c + x) (λ x, - c + x) :=
assume x, add_neg_cancel_left c x

theorem left_inverse_neg_add_add_right (c : G) :
  function.left_inverse (λ x, - c + x) (λ x, c + x) :=
assume x, neg_add_cancel_left c x

end add_group

section comm_group
variables {G : Type u} [comm_group G]

@[to_additive neg_add]
lemma mul_inv (a b : G) : (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
by rw [mul_inv_rev, mul_comm]

end comm_group

section add_comm_group
variables {G : Type u} [add_comm_group G] {a b c d : G}

local attribute [simp] add_assoc add_comm add_left_comm sub_eq_add_neg

lemma sub_add_eq_sub_sub (a b c : G) : a - (b + c) = a - b - c :=
by simp

lemma neg_add_eq_sub (a b : G) : -a + b = b - a :=
by simp

lemma sub_add_eq_add_sub (a b c : G) : a - b + c = a + c - b :=
by simp

lemma sub_sub (a b c : G) : a - b - c = a - (b + c) :=
by simp

lemma sub_add (a b c : G) : a - b + c = a - (b - c) :=
by simp

@[simp] lemma add_sub_add_left_eq_sub (a b c : G) : (c + a) - (c + b) = a - b :=
by simp

lemma eq_sub_of_add_eq' (h : c + a = b) : a = b - c :=
by simp [h.symm]

lemma sub_eq_of_eq_add' (h : a = b + c) : a - b = c :=
begin simp [h], rw [add_left_comm], simp end

lemma eq_add_of_sub_eq' (h : a - b = c) : a = b + c :=
by simp [h.symm]

lemma add_eq_of_eq_sub' (h : b = c - a) : a + b = c :=
begin simp [h], rw [add_comm c, add_neg_cancel_left] end

lemma sub_sub_self (a b : G) : a - (a - b) = b :=
begin simp, rw [add_comm b, add_neg_cancel_left] end

lemma add_sub_comm (a b c d : G) : a + b - (c + d) = (a - c) + (b - d) :=
by simp

lemma sub_eq_sub_add_sub (a b c : G) : a - b = c - b + (a - c) :=
begin simp, rw [add_left_comm c], simp end

lemma neg_neg_sub_neg (a b : G) : - (-a - -b) = a - b :=
by simp

@[simp] lemma sub_sub_cancel (a b : G) : a - (a - b) = b := sub_sub_self a b

lemma sub_eq_neg_add (a b : G) : a - b = -b + a :=
by rw [sub_eq_add_neg, add_comm _ _]

theorem neg_add' (a b : G) : -(a + b) = -a - b :=
by rw [sub_eq_add_neg, neg_add a b]

@[simp]
lemma neg_sub_neg (a b : G) : -a - -b = b - a :=
by simp [sub_eq_neg_add, add_comm]

lemma eq_sub_iff_add_eq' : a = b - c ↔ c + a = b :=
by rw [eq_sub_iff_add_eq, add_comm]

lemma sub_eq_iff_eq_add' : a - b = c ↔ a = b + c :=
by rw [sub_eq_iff_eq_add, add_comm]

@[simp]
lemma add_sub_cancel' (a b : G) : a + b - a = b :=
by rw [sub_eq_neg_add, neg_add_cancel_left]

@[simp]
lemma add_sub_cancel'_right (a b : G) : a + (b - a) = b :=
by rw [← add_sub_assoc, add_sub_cancel']

-- This lemma is in the `simp` set under the name `add_neg_cancel_comm_assoc`,
-- defined  in `algebra/group/commute`
lemma add_add_neg_cancel'_right (a b : G) : a + (b + -a) = b :=
by rw [← sub_eq_add_neg, add_sub_cancel'_right a b]

lemma sub_right_comm (a b c : G) : a - b - c = a - c - b :=
by { repeat { rw sub_eq_add_neg }, exact add_right_comm _ _ _ }

@[simp] lemma add_add_sub_cancel (a b c : G) : (a + c) + (b - c) = a + b :=
by rw [add_assoc, add_sub_cancel'_right]

@[simp] lemma sub_add_add_cancel (a b c : G) : (a - c) + (b + c) = a + b :=
by rw [add_left_comm, sub_add_cancel, add_comm]

@[simp] lemma sub_add_sub_cancel' (a b c : G) : (a - b) + (c - a) = c - b :=
by rw add_comm; apply sub_add_sub_cancel

@[simp] lemma add_sub_sub_cancel (a b c : G) : (a + b) - (a - c) = b + c :=
by rw [← sub_add, add_sub_cancel']

@[simp] lemma sub_sub_sub_cancel_left (a b c : G) : (c - a) - (c - b) = b - a :=
by rw [← neg_sub b c, sub_neg_eq_add, add_comm, sub_add_sub_cancel]

lemma sub_eq_sub_iff_add_eq_add : a - b = c - d ↔ a + d = c + b :=
begin
  rw [sub_eq_iff_eq_add, sub_add_eq_add_sub, eq_comm, sub_eq_iff_eq_add'],
  simp only [add_comm, eq_comm]
end

lemma sub_eq_sub_iff_sub_eq_sub : a - b = c - d ↔ a - c = b - d :=
by simp [-sub_eq_add_neg, sub_eq_sub_iff_add_eq_add, add_comm]

end add_comm_group
