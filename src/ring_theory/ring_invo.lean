/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kenny Lau
-/
import data.equiv.ring

/-!
# Ring involutions

This file defines a ring involution as a structure extending `R ≃+* Rᵒᵖ`,
with the additional fact `f.involution : (f (f x).unop).unop = x`.

## Notations

We provide a coercion to a function `R → Rᵒᵖ`.

## References

* <https://en.wikipedia.org/wiki/Involution_(mathematics)#Ring_theory>

## Tags

Ring involution
-/

variables (R : Type*)

/-- A ring involution -/
structure ring_invo [semiring R] extends R ≃+* Rᵒᵖ :=
(involution' : ∀ x, (to_fun (to_fun x).unop).unop = x)

namespace ring_invo
variables {R} [semiring R]

/-- Construct a ring involution from a ring homomorphism. -/
def mk' (f : R →+* Rᵒᵖ) (involution : ∀ r, (f (f r).unop).unop = r) :
  ring_invo R :=
{ inv_fun := λ r, (f r.unop).unop,
  left_inv := λ r, involution r,
  right_inv := λ r, congr_arg opposite.op (involution (r.unop)),
  involution' := involution,
  ..f }

instance : has_coe_to_fun (ring_invo R) := ⟨_, λ f, f.to_ring_equiv.to_fun⟩

@[simp]
lemma to_fun_eq_coe (f : ring_invo R) : f.to_fun = f := rfl

@[simp]
lemma involution (f : ring_invo R) (x : R) : (f (f x).unop).unop = x :=
f.involution' x

instance has_coe_to_ring_equiv : has_coe (ring_invo R) (R ≃+* Rᵒᵖ) :=
⟨ring_invo.to_ring_equiv⟩

@[norm_cast] lemma coe_ring_equiv (f : ring_invo R) (a : R) :
  (f : R ≃+* Rᵒᵖ) a = f a := rfl

@[simp] lemma map_eq_zero_iff (f : ring_invo R) {x : R} : f x = 0 ↔ x = 0 :=
f.to_ring_equiv.map_eq_zero_iff

end ring_invo

open ring_invo

section comm_ring
variables [comm_ring R]

/-- The identity function of a `comm_ring` is a ring involution. -/
protected def ring_invo.id : ring_invo R :=
{ involution' := λ r, rfl,
  ..(ring_equiv.to_opposite R) }

instance : inhabited (ring_invo R) := ⟨ring_invo.id _⟩

end comm_ring
