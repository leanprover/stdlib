/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import order.rel_iso
import algebra.ordered_ring

/-!
# Ordered ring homomorphisms

Homomorphisms between ordered rings that respect the ordering.

## Main definitions

* `ordered_ring_hom` : A homomorphism `f` between two `ordered_semiring`s that has the property that
  `x ≤ y → f x ≤ f y`.

## Main results

* `ordered_ring_equiv_eq_cut_ordered_ring_equiv` : Uniqueness of the `ordered_ring_equiv`

## Notation

* `→+*o`: equivalence of ordered rings.

## Tags
ordered ring, equivalence, order homomorphism
-/

/-- Homomorphism commuting with multiplicative, additive and order structure. -/
@[nolint has_inhabited_instance]
structure ordered_ring_hom (R S : Type*) [ordered_semiring R] [ordered_semiring S]
  extends R →+* S :=
(map_rel' : ∀ {a b}, a ≤ b → to_fun a ≤ to_fun b)

/-- Reinterpret an ordered ring homomorphism as a ring homomorphism. -/
add_decl_doc ordered_ring_hom.to_ring_hom

namespace ordered_ring_hom

infix ` →+*o `:25 := ordered_ring_hom

variables {R S : Type*} [ordered_semiring R] [ordered_semiring S]

/-- Reinterpret an ordered ring homomorphism as an order homomorphism. -/
def to_rel_hom (f : R →+*o S) : ((≤) : R → R → Prop) →r ((≤) : S → S → Prop) := { ..f }

instance has_coe_to_ring_hom : has_coe (R →+*o S) (R →+* S) := ⟨to_ring_hom⟩
instance has_coe_to_hom : has_coe (R →+*o S) (R → S) := ⟨ring_hom.to_fun ∘ to_ring_hom⟩
instance has_coe_to_rel_hom : has_coe (R →+*o S) (((≤) : R → R → Prop) →r ((≤) : S → S → Prop)) :=
⟨to_rel_hom⟩

instance : has_coe_to_fun (R →+*o S) := ⟨_, λ f, f.to_fun⟩

@[simp] lemma to_ring_hom_eq_coe {f : R →+*o S} : f.to_ring_hom = f := rfl
@[simp] lemma to_order_iso_eq_coe {f : R →+*o S} : f.to_rel_hom = f := rfl
@[simp] lemma coe_ring_hom_to_fun_eq_coe_fun {f : R →+*o S} : (f : R →+* S).to_fun = f := rfl
@[simp] lemma coe_ring_hom_coe_fun_eq_coe_fun {f : R →+*o S} : ((f : R →+* S) : R → S) = f := rfl
@[simp] lemma coe_rel_hom_to_fun_eq_to_equiv {f : R →+*o S} :
  (f : ((≤) : R → R → Prop) →r ((≤) : S → S → Prop)).to_fun = f := rfl
@[simp] lemma coe_rel_hom_coe_fun_eq_to_equiv {f : R →+*o S} :
  ((f : ((≤) : R → R → Prop) →r ((≤) : S → S → Prop)) : R → S) = f := rfl
@[simp]
lemma coe_mul_equiv_to_fun_eq_coe_fun {f : R →+*o S} : ((f : R →+* S) : R →* S).to_fun = f := rfl
@[simp]
lemma coe_mul_equiv_coe_fun_eq_coe_fun {f : R →+*o S} : (((f : R →+* S) : R →* S) : R → S) = f :=
rfl
@[simp]
lemma coe_add_equiv_to_fun_eq_coe_fun {f : R →+*o S} : ((f : R →+* S) : R →+ S).to_fun = f := rfl
@[simp]
lemma coe_add_equiv_coe_fun_eq_coe_fun {f : R →+*o S} : (((f : R →+* S) : R →+ S) : R → S) = f :=
rfl

/-- An ordered ring homomorphism preserves multiplication. -/
@[simp] lemma map_mul (e : R →+*o S) (x y : R) : e (x * y) = e x * e y := e.map_mul' x y

/-- An ordered ring homomorphism preserves addition. -/
@[simp] lemma map_add (e : R →+*o S) (x y : R) : e (x + y) = e x + e y := e.map_add' x y

/-- An ordered ring homomorphism preserves ordering. -/
@[simp] lemma map_le (e : R →+*o S) {x y : R} (h : x ≤ y) : e x ≤ e y := e.map_rel' h

protected lemma congr_arg {f : R →+*o S} : Π {x x' : R}, x = x' → f x = f x'
| _ _ rfl := rfl

protected lemma congr_fun {f g : R →+*o S} (h : f = g) (x : R) : f x = g x := h ▸ rfl

/-- Two ordered ring homomorphisms agree if they are defined by the
  same underlying function. -/
@[ext] lemma ext {f g : R →+*o S} (h : ∀ x, f x = g x) : f = g :=
begin
  cases f, cases g, congr,
  apply ring_hom.ext,
  intro x,
  convert h x,
end

lemma ext_iff {f g : R →+*o S} : f = g ↔ ∀ x, f x = g x := ⟨λ h x, h ▸ rfl, ext⟩

@[norm_cast] lemma coe_ring_equiv (f : R →+*o S) (a : R) : (f : R →+* S) a = f a := rfl

@[norm_cast] lemma coe_mul_equiv (f : R →+*o S) (a : R) : (f : R →* S) a = f a := rfl

@[norm_cast] lemma coe_add_equiv (f : R →+*o S) (a : R) : (f : R →+ S) a = f a := rfl

variable (R)

/-- Identity map is an ordered ring isomorphism. -/
protected def id : R →+*o R :=
{ ..ring_hom.id _,
  ..rel_hom.id _, }

variable {R}
@[simp] lemma id_apply (x : R) : ordered_ring_hom.id R x = x := rfl

@[simp] lemma coe_add_hom_id : (ordered_ring_hom.id R : R →+ R) = add_monoid_hom.id R := rfl
@[simp] lemma coe_mul_hom_id : (ordered_ring_hom.id R : R →* R) = monoid_hom.id R := rfl
@[simp] lemma coe_ring_hom_id : (ordered_ring_hom.id R : R →+* R) = ring_hom.id R := rfl
@[simp] lemma coe_rel_hom_id :
  (ordered_ring_hom.id R : ((≤) : R → R → Prop) →r ((≤) : R → R → Prop)) =
  rel_hom.id ((≤) : R → R → Prop) := rfl

instance : inhabited (R →+*o R) := ⟨ordered_ring_hom.id R⟩

/-- Composition of two ordered ring homomorphisms is an ordered ring homomorphism. -/
protected def comp {T : Type*} [ordered_semiring T]
  (f₂ : S →+*o T) (f₁ : R →+*o S) : R →+*o T :=
{ ..f₂.to_ring_hom.comp f₁.to_ring_hom,
  ..f₂.to_rel_hom.comp f₁.to_rel_hom, }

-- @[simp] lemma comp_apply {T : Type*} [ordered_semiring T]
--     (f₁ : R →+*o S) (f₂ : S →+*o T) (a : R) : f₂.comp f₁ a = f₂ (f₁ a) := rfl

lemma comp_assoc {T U : Type*} [ordered_semiring T] [ordered_semiring U] (f₁ : R →+*o S)
  (f₂ : S →+*o T) (f₃ : T →+*o U) : (f₃.comp f₂).comp f₁ = f₃.comp (f₂.comp f₁) := rfl

@[simp]
lemma coe_comp {T : Type*} [ordered_semiring T] (f₁ : R →+*o S) (f₂ : S →+*o T) :
  (f₂.comp f₁ : R → T) = f₂ ∘ f₁ := rfl

@[simp] lemma comp_id (f : R →+*o S) : f.comp (ordered_ring_hom.id R) = f := ext $ λ x, rfl

@[simp] lemma id_comp (f : R →+*o S) : (ordered_ring_hom.id S).comp f = f := ext $ λ x, rfl

end ordered_ring_hom
