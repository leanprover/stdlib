/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import data.equiv.ring
import algebra.ordered_ring_hom

/-!
# Ordered ring equivalences

archimedean, and define equivalences between these fields. We also construct the natural map from a
`linear_ordered_field` to such a field.

## Main definitions

* `conditionally_complete_linear_ordered_field` : A field satisfying the standard axiomatization of
  the real numbers

## Main results

* `ordered_ring_equiv_eq_cut_ordered_ring_equiv` : Uniqueness of the `ordered_ring_equiv`

## Notation

* `≃+*o`: equivalence of ordered rings.

## Tags
ordered ring, equivalence, order isomorphism
-/

/-- Equivalence commuting with multiplicative, additive and order structure. -/
@[nolint has_inhabited_instance]
structure ordered_ring_equiv (R S : Type*) [has_mul R] [has_add R] [has_mul S] [has_add S]
  [has_le R] [has_le S] extends R ≃+* S :=
(map_rel_iff' : ∀ {x y : R}, to_fun x ≤ to_fun y ↔ x ≤ y)

/-- Reinterpret an ordered ring equivalence as a ring equivalence. -/
add_decl_doc ordered_ring_equiv.to_ring_equiv

namespace ordered_ring_equiv

infix ` ≃+*o `:25 := ordered_ring_equiv

section general
variables {R S : Type*} [has_mul R] [has_add R] [has_le R] [has_mul S] [has_add S] [has_le S]

/-- Reinterpret an ordered ring equivalence as an order isomorphism. -/
def to_order_iso (f : R ≃+*o S) : R ≃o S := { ..f }

instance has_coe_to_ring_equiv : has_coe (R ≃+*o S) (R ≃+* S) := ⟨to_ring_equiv⟩
instance has_coe_to_equiv : has_coe (R ≃+*o S) (R ≃ S) := ⟨ring_equiv.to_equiv ∘ to_ring_equiv⟩
instance has_coe_to_order_iso : has_coe (R ≃+*o S) (R ≃o S) := ⟨to_order_iso⟩

instance : has_coe_to_fun (R ≃+*o S) := ⟨_, λ f, f.to_fun⟩

@[simp] lemma to_ring_equiv_eq_coe {f : R ≃+*o S} : f.to_ring_equiv = f := rfl
@[simp] lemma to_order_iso_eq_coe {f : R ≃+*o S} : f.to_order_iso = f := rfl
@[simp] lemma coe_ring_equiv_to_fun_eq_coe_fun {f : R ≃+*o S} : (f : R ≃+* S).to_fun = f := rfl
@[simp] lemma coe_ring_equiv_coe_fun_eq_coe_fun {f : R ≃+*o S} : ((f : R ≃+* S) : R → S) = f := rfl
@[simp] lemma to_order_iso_to_fun_eq_to_equiv {f : R ≃+*o S} : (f : R ≃o S).to_fun = f := rfl
@[simp] lemma to_order_iso_coe_fun_eq_to_equiv {f : R ≃+*o S} : ((f : R ≃o S) : R → S) = f := rfl
@[simp]
lemma coe_mul_equiv_to_fun_eq_coe_fun {f : R ≃+*o S} : ((f : R ≃+* S) : R ≃* S).to_fun = f := rfl
@[simp]
lemma coe_mul_equiv_coe_fun_eq_coe_fun {f : R ≃+*o S} : (((f : R ≃+* S) : R ≃* S) : R → S) = f :=
rfl
@[simp]
lemma coe_add_equiv_to_fun_eq_coe_fun {f : R ≃+*o S} : ((f : R ≃+* S) : R ≃+ S).to_fun = f := rfl
@[simp]
lemma coe_add_equiv_coe_fun_eq_coe_fun {f : R ≃+*o S} : (((f : R ≃+* S) : R ≃+ S) : R → S) = f :=
rfl

/-- An ordered ring isomorphism preserves multiplication. -/
@[simp] lemma map_mul (e : R ≃+*o S) (x y : R) : e (x * y) = e x * e y := e.map_mul' x y

/-- An ordered ring isomorphism preserves addition. -/
@[simp] lemma map_add (e : R ≃+*o S) (x y : R) : e (x + y) = e x + e y := e.map_add' x y

/-- An ordered ring isomorphism preserves ordering. -/
@[simp] lemma map_le (e : R ≃+*o S) (x y : R) : e x ≤ e y ↔ x ≤ y :=
begin
  have := e.map_rel_iff',
  convert @this x y
end

protected lemma congr_arg {f : R ≃+*o S} : Π {x x' : R}, x = x' → f x = f x'
| _ _ rfl := rfl

protected lemma congr_fun {f g : R ≃+*o S} (h : f = g) (x : R) : f x = g x := h ▸ rfl

/-- Two ordered ring isomorphisms agree if they are defined by the
  same underlying function. -/
@[ext] lemma ext {f g : R ≃+*o S} (h : ∀ x, f x = g x) : f = g :=
begin
  cases f, cases g, congr,
  apply ring_equiv.ext,
  intro x,
  convert h x,
end

lemma ext_iff {f g : R ≃+*o S} : f = g ↔ ∀ x, f x = g x := ⟨λ h x, h ▸ rfl, ext⟩

@[norm_cast] lemma coe_ring_equiv (f : R ≃+*o S) (a : R) : (f : R ≃+* S) a = f a := rfl

@[norm_cast] lemma coe_mul_equiv (f : R ≃+*o S) (a : R) : (f : R ≃* S) a = f a := rfl

@[norm_cast] lemma coe_add_equiv (f : R ≃+*o S) (a : R) : (f : R ≃+ S) a = f a := rfl

variable (R)

/-- Identity map is an ordered ring isomorphism. -/
@[refl] protected def refl : R ≃+*o R :=
{ ..ring_equiv.refl _,
  ..rel_iso.refl _, }

variable {R}
@[simp] lemma refl_apply (x : R) : ordered_ring_equiv.refl R x = x := rfl

@[simp] lemma coe_add_equiv_refl : (ordered_ring_equiv.refl R : R ≃+ R) = add_equiv.refl R := rfl
@[simp] lemma coe_mul_equiv_refl : (ordered_ring_equiv.refl R : R ≃* R) = mul_equiv.refl R := rfl
@[simp] lemma coe_ring_equiv_refl : (ordered_ring_equiv.refl R : R ≃+* R) = ring_equiv.refl R := rfl
@[simp] lemma coe_order_iso_refl : (ordered_ring_equiv.refl R : R ≃o R) = rel_iso.refl _ := rfl

instance : inhabited (R ≃+*o R) := ⟨ordered_ring_equiv.refl R⟩

/-- Inverse map of an ordered ring isomorphism is an order isomorphism. -/
@[symm] protected def symm (f : R ≃+*o S) : S ≃+*o R :=
{ ..f.to_order_iso.symm,
  ..f.to_ring_equiv.symm, }

@[simp] lemma symm_symm (e : R ≃+*o S) : e.symm.symm = e := ext $ λ x, rfl

/-- Composition of two ordered ring isomorphisms is an ordered ring isomorphism. -/
@[trans] protected def trans {R S T : Type*} [has_mul R] [has_add R] [has_le R]
  [has_mul S] [has_add S] [has_le S]
  [has_mul T] [has_add T] [has_le T]
    (f₁ : R ≃+*o S) (f₂ : S ≃+*o T) : R ≃+*o T :=
{ ..f₁.to_ring_equiv.trans f₂.to_ring_equiv,
  ..f₁.to_order_iso.trans f₂.to_order_iso, }

@[simp] lemma trans_apply {R S T : Type*} [has_mul R] [has_add R] [has_le R]
  [has_mul S] [has_add S] [has_le S]
  [has_mul T] [has_add T] [has_le T]
    (f₁ : R ≃+*o S) (f₂ : S ≃+*o T) (a : R) : f₁.trans f₂ a = f₂ (f₁ a) := rfl

@[simp]
lemma trans_symm (e : R ≃+*o S) : e.trans e.symm = ordered_ring_equiv.refl R := ext (e : R ≃ S).3
@[simp]
lemma symm_trans (e : R ≃+*o S) : e.symm.trans e = ordered_ring_equiv.refl S := ext (e : R ≃ S).4


-- TODO check these for ring equivs
@[simp] lemma trans_refl (e : R ≃+*o S) : e.trans (ordered_ring_equiv.refl S) = e := ext $ λ x, rfl

@[simp] lemma refl_symm : (ordered_ring_equiv.refl R).symm = ordered_ring_equiv.refl R := rfl

@[simp] lemma refl_trans (e : R ≃+*o S) : (ordered_ring_equiv.refl R).trans e = e := ext $ λ x, rfl
end general

variables {R S : Type*} [ordered_semiring R] [ordered_semiring S]

/-- Reinterpret an ordered ring isomorphism as an ordered ring homomorphism. -/
def to_ordered_ring_hom (f : R ≃+*o S) : R →+*o S := { ..f.to_ring_equiv.to_ring_hom,
  ..f.to_order_iso.to_rel_embedding.to_rel_hom }
instance has_coe_to_ordered_ring_hom : has_coe (R ≃+*o S) (R →+*o S) := ⟨to_ordered_ring_hom⟩
@[norm_cast] lemma coe_ordered_ring_hom (f : R ≃+*o S) (a : R) : (f : R →+*o S) a = f a := rfl

end ordered_ring_equiv
