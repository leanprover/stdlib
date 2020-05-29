/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import algebra.group.to_additive
import tactic.simpa
import logic.function.basic

set_option default_priority 100
set_option old_structure_cmd true

universe u

/- Additive "sister" structures.
   Example, add_semigroup mirrors semigroup.
   These structures exist just to help automation.
   In an alternative design, we could have the binary operation as an
   extra argument for semigroup, monoid, group, etc. However, the lemmas
   would be hard to index since they would not contain any constant.
   For example, mul_assoc would be

   lemma mul_assoc {α : Type u} {op : α → α → α} [semigroup α op] :
                   ∀ a b c : α, op (op a b) c = op a (op b c) :=
    semigroup.mul_assoc

   The simplifier cannot effectively use this lemma since the pattern for
   the left-hand-side would be

        ?op (?op ?a ?b) ?c

   Remark: we use a tactic for transporting theorems from the multiplicative fragment
   to the additive one.
-/

@[ancestor has_mul] class semigroup (α : Type u) extends has_mul α :=
(mul_assoc : ∀ a b c : α, a * b * c = a * (b * c))
@[ancestor has_add] class add_semigroup (α : Type u) extends has_add α :=
(add_assoc : ∀ a b c : α, a + b + c = a + (b + c))
attribute [to_additive add_semigroup] semigroup

section semigroup
variables {α : Type u} [semigroup α]

@[no_rsimp, to_additive]
lemma mul_assoc : ∀ a b c : α, a * b * c = a * (b * c) :=
semigroup.mul_assoc

attribute [no_rsimp] add_assoc -- TODO(Mario): find out why this isn't copying

@[to_additive add_semigroup_to_is_eq_associative]
instance semigroup_to_is_associative : is_associative α (*) :=
⟨mul_assoc⟩

end semigroup

@[ancestor semigroup] class comm_semigroup (α : Type u) extends semigroup α :=
(mul_comm : ∀ a b : α, a * b = b * a)
@[ancestor add_semigroup] class add_comm_semigroup (α : Type u) extends add_semigroup α :=
(add_comm : ∀ a b : α, a + b = b + a)
attribute [to_additive add_comm_semigroup] comm_semigroup

section comm_semigroup
variables {G : Type u} [comm_semigroup G]

@[no_rsimp, to_additive]
lemma mul_comm : ∀ a b : G, a * b = b * a :=
comm_semigroup.mul_comm
attribute [no_rsimp] add_comm

@[to_additive add_comm_semigroup_to_is_eq_commutative]
instance comm_semigroup_to_is_commutative : is_commutative G (*) :=
⟨mul_comm⟩

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

local attribute [simp] mul_assoc

@[ancestor semigroup] class left_cancel_semigroup (α : Type u) extends semigroup α :=
(mul_left_cancel : ∀ a b c : α, a * b = a * c → b = c)
@[ancestor add_semigroup] class add_left_cancel_semigroup (α : Type u) extends add_semigroup α :=
(add_left_cancel : ∀ a b c : α, a + b = a + c → b = c)
attribute [to_additive add_left_cancel_semigroup] left_cancel_semigroup

section left_cancel_semigroup
variables {α : Type u} [left_cancel_semigroup α] {a b c : α}

@[to_additive]
lemma mul_left_cancel : a * b = a * c → b = c :=
left_cancel_semigroup.mul_left_cancel a b c

def eq_of_add_eq_add_left := @add_left_cancel

@[to_additive]
lemma mul_left_cancel_iff : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congr_arg _⟩

@[to_additive]
theorem mul_right_injective (a : α) : function.injective ((*) a) :=
λ b c, mul_left_cancel

@[simp, to_additive]
theorem mul_right_inj (a : α) {b c : α} : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congr_arg _⟩

end left_cancel_semigroup

@[ancestor semigroup] class right_cancel_semigroup (α : Type u) extends semigroup α :=
(mul_right_cancel : ∀ a b c : α, a * b = c * b → a = c)
@[ancestor add_semigroup] class add_right_cancel_semigroup (α : Type u) extends add_semigroup α :=
(add_right_cancel : ∀ a b c : α, a + b = c + b → a = c)
attribute [to_additive add_right_cancel_semigroup] right_cancel_semigroup

section right_cancel_semigroup
variables {α : Type u} [right_cancel_semigroup α] {a b c : α}

@[to_additive]
lemma mul_right_cancel : a * b = c * b → a = c :=
right_cancel_semigroup.mul_right_cancel a b c

def eq_of_add_eq_add_right := @add_right_cancel

@[to_additive]
lemma mul_right_cancel_iff : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, congr_arg _⟩

@[to_additive]
theorem mul_left_injective (a : α) : function.injective (λ x, x * a) :=
λ b c, mul_right_cancel

@[simp, to_additive]
theorem mul_left_inj (a : α) {b c : α} : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, congr_arg _⟩

end right_cancel_semigroup

@[ancestor semigroup has_one]
class monoid (M : Type u) extends semigroup M, has_one M :=
(one_mul : ∀ a : M, 1 * a = a) (mul_one : ∀ a : M, a * 1 = a)
@[ancestor add_semigroup has_zero]
class add_monoid (M : Type u) extends add_semigroup M, has_zero M :=
(zero_add : ∀ a : M, 0 + a = a) (add_zero : ∀ a : M, a + 0 = a)
attribute [to_additive add_monoid] monoid

section monoid
variables {M : Type u} [monoid M]

@[ematch, simp, to_additive]
lemma one_mul : ∀ a : M, 1 * a = a :=
monoid.one_mul

@[ematch, simp, to_additive]
lemma mul_one : ∀ a : M, a * 1 = a :=
monoid.mul_one

attribute [ematch] add_zero zero_add -- TODO(Mario): Make to_additive transfer this

@[to_additive add_monoid_to_is_left_id]
instance monoid_to_is_left_id : is_left_id M (*) 1 :=
⟨ monoid.one_mul ⟩

@[to_additive add_monoid_to_is_right_id]
instance monoid_to_is_right_id : is_right_id M (*) 1 :=
⟨ monoid.mul_one ⟩

@[to_additive]
lemma left_inv_eq_right_inv {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c :=
by rw [←one_mul c, ←hba, mul_assoc, hac, mul_one b]

end monoid

section add_monoid
variables {M : Type u} [add_monoid M] {a b c : M}

@[simp] lemma bit0_zero : bit0 (0 : M) = 0 := add_zero _
@[simp] lemma bit1_zero [has_one M] : bit1 (0 : M) = 1 :=
by rw [bit1, bit0_zero, zero_add]

end add_monoid

@[ancestor comm_semigroup has_one]
structure comm_monoid (M : Type u) extends comm_semigroup M, has_one M :=
(one_mul : ∀ a : M, 1 * a = a)
@[ancestor add_comm_semigroup has_zero]
structure add_comm_monoid (M : Type u) extends add_comm_semigroup M, has_zero M :=
(zero_add : ∀ a : M, 0 + a = a)
attribute [class] comm_monoid add_comm_monoid
attribute [to_additive add_comm_monoid] comm_monoid

section comm_monoid
variables {M : Type u} [comm_monoid M] {x y z : M}

@[to_additive add_comm_monoid.to_add_comm_semigroup']
instance comm_monoid.to_comm_semigroup' : comm_semigroup M :=
@comm_monoid.to_comm_semigroup _ (by apply_instance)

@[to_additive add_comm_monoid.to_add_monoid]
instance comm_monoid.to_monoid : monoid M :=
{ mul_one := λ a, by rw [comm_monoid.mul_comm, comm_monoid.one_mul]
  ..show comm_monoid M, by apply_instance }

@[to_additive] lemma inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z :=
left_inv_eq_right_inv (trans (mul_comm _ _) hy) hz

end comm_monoid

/-- An algebraic class missing in core: an additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_left_cancel_semigroup` is not enough. -/
class add_left_cancel_monoid (M : Type u) extends add_left_cancel_semigroup M, add_monoid M

section add_left_cancel_monoid
variables {M : Type u} [add_left_cancel_monoid M]

end add_left_cancel_monoid

@[ancestor semigroup has_one has_inv]
structure group (α : Type u) extends semigroup α, has_one α, has_inv α :=
(one_mul : ∀ a : α, 1 * a = a)
(mul_left_inv : ∀ a : α, a⁻¹ * a = 1)
@[ancestor add_semigroup has_zero has_neg]
structure add_group (α : Type u) extends add_semigroup α, has_zero α, has_neg α :=
(zero_add : ∀ a : α, 0 + a = a)
(add_left_neg : ∀ a : α, -a + a = 0)
attribute [class] group add_group
attribute [to_additive add_group] group

section group
variables {G : Type u} [group G] {a b c : G}

@[to_additive add_group.to_has_neg']
instance group.to_has_inv' : has_inv G :=
@group.to_has_inv _ (by apply_instance)

@[to_additive add_group.to_has_zero']
def group.to_has_one' : has_one G :=
@group.to_has_one _ (by apply_instance)

@[to_additive add_group.to_add_semigroup']
def group.to_semigroup' : Π {α : Type u} [group α], semigroup α :=
@group.to_semigroup

section

local attribute [instance] group.to_semigroup' group.to_has_one'

@[simp, to_additive]
lemma mul_left_inv : ∀ a : G, a⁻¹ * a = 1 :=
group.mul_left_inv (by apply_instance)

@[to_additive] def inv_mul_self := @mul_left_inv

@[simp, to_additive] lemma mul_right_inv (a : G) : a * a⁻¹ = 1 :=
calc a * a⁻¹ = (a * a⁻¹)⁻¹ * (a * a⁻¹) * (a * a⁻¹) :
  by rw [mul_left_inv, group.one_mul]
... = (a * a⁻¹)⁻¹ * (a * a⁻¹) :
  by rw [mul_assoc, mul_assoc, ← mul_assoc (a⁻¹), mul_left_inv, group.one_mul]
... = 1 : by rw mul_left_inv

@[to_additive add_group.to_add_monoid]
instance group.to_monoid : monoid G :=
{ mul_one := λ a,
    by rw [← group.mul_left_inv _ a, ← mul_assoc, mul_right_inv, group.one_mul],
  .. show group G, by apply_instance }

end

@[simp, to_additive]
lemma inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b :=
by rw [← mul_assoc, mul_left_inv, one_mul]

@[simp, to_additive]
lemma inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a :=
by simp

@[simp, to_additive]
lemma inv_eq_of_mul_eq_one (h : a * b = 1) : a⁻¹ = b :=
by rw [← mul_one a⁻¹, ←h, ←mul_assoc, mul_left_inv, one_mul]

@[simp, to_additive neg_zero]
lemma one_inv : 1⁻¹ = (1 : G) :=
inv_eq_of_mul_eq_one (one_mul 1)

@[simp, to_additive]
lemma inv_inv (a : G) : (a⁻¹)⁻¹ = a :=
inv_eq_of_mul_eq_one (mul_left_inv a)

@[to_additive]
theorem left_inverse_inv (G) [group G] :
  function.left_inverse (λ a : G, a⁻¹) (λ a, a⁻¹) :=
inv_inv

@[to_additive] def mul_inv_self := @mul_right_inv

@[to_additive]
lemma inv_inj (h : a⁻¹ = b⁻¹) : a = b :=
have a = a⁻¹⁻¹, by simp,
begin rw this, simp [h] end

@[simp, to_additive]
theorem inv_inj' : a⁻¹ = b⁻¹ ↔ a = b :=
⟨λ h, by rw [← inv_inv a, h, inv_inv], congr_arg _⟩

@[to_additive]
theorem eq_of_inv_eq_inv : a⁻¹ = b⁻¹ → a = b :=
inv_inj'.1

@[to_additive add_group.add_left_cancel]
lemma group.mul_left_cancel (h : a * b = a * c) : b = c :=
have a⁻¹ * (a * b) = b, by simp,
begin simp [h] at this, rw this end

@[to_additive add_group.add_right_cancel]
lemma group.mul_right_cancel (h : a * b = c * b) : a = c :=
have a * b * b⁻¹ = a, by simp,
begin simp [h] at this, rw this end

@[to_additive add_group.to_left_cancel_add_semigroup]
instance group.to_left_cancel_semigroup : left_cancel_semigroup G :=
{ mul_left_cancel := @group.mul_left_cancel G _, ..‹group G› }

@[to_additive add_group.to_right_cancel_add_semigroup]
instance group.to_right_cancel_semigroup : right_cancel_semigroup G :=
{ mul_right_cancel := @group.mul_right_cancel G _, ..‹group G› }

@[simp, to_additive]
lemma mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b :=
by rw [← mul_assoc, mul_right_inv, one_mul]

@[simp, to_additive]
lemma mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a :=
by rw [mul_assoc, mul_right_inv, mul_one]

@[to_additive]
theorem mul_left_surjective (a : G) : function.surjective ((*) a) :=
λ x, ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

@[to_additive]
theorem mul_right_surjective (a : G) : function.surjective (λ x, x * a) :=
λ x, ⟨x * a⁻¹, inv_mul_cancel_right x a⟩

@[simp, to_additive neg_add_rev]
lemma mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
inv_eq_of_mul_eq_one begin rw [mul_assoc, ← mul_assoc b, mul_right_inv, one_mul, mul_right_inv] end

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
by rw [← @inv_inj' _ _ a 1, one_inv]

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
by rw [mul_eq_one_iff_eq_inv, inv_inj']

@[to_additive]
theorem inv_comm_of_comm (H : a * b = b * a) : a⁻¹ * b = b * a⁻¹ :=
begin
  have : a⁻¹ * (b * a) * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ :=
    congr_arg (λ x:G, a⁻¹ * x * a⁻¹) H.symm,
  rwa [inv_mul_cancel_left, mul_assoc, mul_inv_cancel_right] at this
end

@[simp, to_additive]
lemma mul_left_eq_self : a * b = b ↔ a = 1 :=
⟨λ h, @mul_right_cancel _ _ a b 1 (by simp [h]), λ h, by simp [h]⟩

@[simp, to_additive]
lemma mul_right_eq_self : a * b = a ↔ b = 1 :=
⟨λ h, @mul_left_cancel _ _ a b 1 (by simp [h]), λ h, by simp [h]⟩

@[to_additive]
lemma inv_involutive : function.involutive (has_inv.inv : G → G) := inv_inv

end group

section add_group
variables {G : Type u} [add_group G] {a b c d : G}

@[reducible] protected def algebra.sub (a b : G) : G :=
a + -b

instance add_group_has_sub : has_sub G :=
⟨algebra.sub⟩

local attribute [simp]
lemma sub_eq_add_neg (a b : G) : a - b = a + -b :=
rfl

@[simp] lemma sub_self (a : G) : a - a = 0 :=
add_right_neg a

@[simp] lemma sub_add_cancel (a b : G) : a - b + b = a :=
neg_add_cancel_right a b

@[simp] lemma add_sub_cancel (a b : G) : a + b - b = a :=
add_neg_cancel_right a b

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

@[simp] lemma zero_sub (a : G) : 0 - a = -a :=
zero_add (-a)

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
neg_eq_of_add_eq_zero (by rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, neg_add_cancel_left, add_right_neg])

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

instance add_group.to_add_left_cancel_monoid : add_left_cancel_monoid G :=
{ ..‹add_group G›, .. add_group.to_left_cancel_add_semigroup, ..add_group.to_add_monoid }

@[simp] lemma sub_right_inj : a - b = a - c ↔ b = c :=
(add_right_inj _).trans neg_inj'

@[simp] lemma sub_left_inj : b - a = c - a ↔ b = c :=
add_left_inj _

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
eq_add_neg_iff_add_eq

theorem sub_eq_iff_eq_add : a - b = c ↔ a = c + b :=
add_neg_eq_iff_eq_add

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

@[ancestor group comm_monoid]
class comm_group (G : Type u) extends group G, comm_monoid G
@[ancestor add_group add_comm_monoid]
class add_comm_group (G : Type u) extends add_group G, add_comm_monoid G
attribute [to_additive add_comm_group] comm_group

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

lemma sub_sub_cancel (a b : G) : a - (a - b) = b := sub_sub_self a b

lemma sub_eq_neg_add (a b : G) : a - b = -b + a :=
add_comm _ _

theorem neg_add' (a b : G) : -(a + b) = -a - b := neg_add a b

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

@[simp] lemma add_add_neg_cancel'_right (a b : G) : a + (b + -a) = b :=
add_sub_cancel'_right a b

lemma sub_right_comm (a b c : G) : a - b - c = a - c - b :=
add_right_comm _ _ _

lemma add_add_sub_cancel (a b c : G) : (a + c) + (b - c) = a + b :=
by rw [add_assoc, add_sub_cancel'_right]

lemma sub_add_add_cancel (a b c : G) : (a - c) + (b + c) = a + b :=
by rw [add_left_comm, sub_add_cancel, add_comm]

lemma sub_add_sub_cancel' (a b c : G) : (a - b) + (c - a) = c - b :=
by rw add_comm; apply sub_add_sub_cancel

lemma add_sub_sub_cancel (a b c : G) : (a + b) - (a - c) = b + c :=
by rw [← sub_add, add_sub_cancel']

lemma sub_sub_sub_cancel_left (a b c : G) : (c - a) - (c - b) = b - a :=
by rw [← neg_sub b c, sub_neg_eq_add, add_comm, sub_add_sub_cancel]

lemma sub_eq_sub_iff_add_eq_add : a - b = c - d ↔ a + d = c + b :=
begin
  rw [sub_eq_iff_eq_add, sub_add_eq_add_sub, eq_comm, sub_eq_iff_eq_add'],
  simp only [add_comm, eq_comm]
end

lemma sub_eq_sub_iff_sub_eq_sub : a - b = c - d ↔ a - c = b - d :=
by simp [-sub_eq_add_neg, sub_eq_sub_iff_add_eq_add, add_comm]

end add_comm_group
