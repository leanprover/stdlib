/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison.
-/
import tactic.apply_fun
import algebra.big_operators.basic
import data.equiv.ring

/-!
# Star monoids and star rings

We introduce the basic algebraic notions of star monoids, and star rings.
Star algebras are introduced in `algebra.algebra.star`.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type) [ring R] [star_ring R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.
-/


universes u v

/--
Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
class has_star (R : Type u) :=
(star : R → R)

variables {R : Type u}

/--
A star operation (e.g. complex conjugate).
-/
def star [has_star R] (r : R) : R := has_star.star r

/--
Typeclass for a star operation with is involutive.
-/
class has_involutive_star (R : Type u) extends has_star R :=
(star_involutive : function.involutive star)

@[simp] lemma star_star [has_involutive_star R] (r : R) : star (star r) = r :=
has_involutive_star.star_involutive _

lemma star_injective [has_involutive_star R] : function.injective (star : R → R) :=
has_involutive_star.star_involutive.injective

/--
A *-monoid is a monoid `R` with an involutive operations `star`
so `star (r * s) = star s * star r`.
-/
class star_monoid (R : Type u) [monoid R] extends has_involutive_star R :=
(star_mul : ∀ r s : R, star (r * s) = star s * star r)

@[simp] lemma star_mul [monoid R] [star_monoid R] (r s : R) : star (r * s) = star s * star r :=
star_monoid.star_mul r s

/-- `star` as an `mul_equiv` from `R` to `Rᵒᵖ` -/
@[simps apply]
def star_mul_equiv [monoid R] [star_monoid R] : R ≃* Rᵒᵖ :=
{ to_fun := λ x, opposite.op (star x),
  map_mul' := λ x y, (star_mul x y).symm ▸ (opposite.op_mul _ _),
  ..(has_involutive_star.star_involutive.to_equiv star).trans opposite.equiv_to_opposite}

variables (R)

@[simp] lemma star_one [monoid R] [star_monoid R] : star (1 : R) = 1 :=
begin
  have := congr_arg opposite.unop (star_mul_equiv : R ≃* Rᵒᵖ).map_one,
  rwa [star_mul_equiv_apply, opposite.unop_op, opposite.unop_one] at this,
end

variables {R}

/--
A *-ring `R` is a (semi)ring with an involutive `star` operation which is additive
which makes `R` with its multiplicative structure into a *-monoid
(i.e. `star (r * s) = star s * star r`).
-/
class star_ring (R : Type u) [semiring R] extends star_monoid R :=
(star_add : ∀ r s : R, star (r + s) = star r + star s)

@[simp] lemma star_add [semiring R] [star_ring R] (r s : R) : star (r + s) = star r + star s :=
star_ring.star_add r s

/-- `star` as an `add_equiv` -/
@[simps apply]
def star_add_equiv [semiring R] [star_ring R] : R ≃+ R :=
{ to_fun := star,
  map_add' := star_add,
  ..(has_involutive_star.star_involutive.to_equiv star)}

variables (R)

@[simp] lemma star_zero [semiring R] [star_ring R] : star (0 : R) = 0 :=
(star_add_equiv : R ≃+ R).map_zero

variables {R}

/-- `star` as an `ring_equiv` from `R` to `Rᵒᵖ` -/
@[simps apply]
def star_ring_equiv [semiring R] [star_ring R] : R ≃+* Rᵒᵖ :=
{ to_fun := λ x, opposite.op (star x),
  ..star_add_equiv.trans (opposite.op_add_equiv : R ≃+ Rᵒᵖ),
  ..star_mul_equiv}

section
open_locale big_operators

@[simp] lemma star_sum [semiring R] [star_ring R] {α : Type*}
  (s : finset α) (f : α → R):
  star (∑ x in s, f x) = ∑ x in s, star (f x) :=
(star_add_equiv : R ≃+ R).map_sum _ _

end

@[simp] lemma star_neg [ring R] [star_ring R] (r : R) : star (-r) = - star r :=
(star_add_equiv : R ≃+ R).map_neg _

@[simp] lemma star_sub [ring R] [star_ring R] (r s : R) : star (r - s) = star r - star s :=
(star_add_equiv : R ≃+ R).map_sub _ _

@[simp] lemma star_bit0 [ring R] [star_ring R] (r : R) : star (bit0 r) = bit0 (star r) :=
by simp [bit0]

@[simp] lemma star_bit1 [ring R] [star_ring R] (r : R) : star (bit1 r) = bit1 (star r) :=
by simp [bit1]

/--
Any commutative semiring admits the trivial *-structure.
-/
def star_ring_of_comm {R : Type*} [comm_semiring R] : star_ring R :=
{ star := id,
  star_involutive := λ x, by simp,
  star_mul := by simp [mul_comm],
  star_add := by simp, }

section
local attribute [instance] star_ring_of_comm

@[simp] lemma star_id_of_comm {R : Type*} [comm_semiring R] {x : R} : star x = x := rfl

end
