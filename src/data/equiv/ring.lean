/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import algebra.opposites

/-!
# (Semi)ring equivs

In this file we define extension of `equiv` called `ring_equiv`, which is a datatype representing an
isomorphism of `semiring`s, `ring`s, `division_ring`s, or `field`s. We also introduce the
corresponding group of automorphisms `ring_aut`.

## Notations

The extended equiv have coercions to functions, and the coercion is the canonical notation when
treating the isomorphism as maps.

## Implementation notes

The fields for `ring_equiv` now avoid the unbundled `is_mul_hom` and `is_add_hom`, as these are
deprecated.

Definition of multiplication in the groups of automorphisms agrees with function composition,
multiplication in `equiv.perm`, and multiplication in `category_theory.End`, not with
`category_theory.comp`.

## Tags

equiv, mul_equiv, add_equiv, ring_equiv, mul_aut, add_aut, ring_aut
-/

variables {R : Type*} {S : Type*} {S' : Type*}

set_option old_structure_cmd true

/-- An equivalence between two (semi)rings that preserves the algebraic structure. -/
structure ring_equiv (R S : Type*) [has_mul R] [has_add R] [has_mul S] [has_add S]
  extends R ≃ S, R ≃* S, R ≃+ S

infix ` ≃+* `:25 := ring_equiv

/-- The "plain" equivalence of types underlying an equivalence of (semi)rings. -/
add_decl_doc ring_equiv.to_equiv

/-- The equivalence of additive monoids underlying an equivalence of (semi)rings. -/
add_decl_doc ring_equiv.to_add_equiv

/-- The equivalence of multiplicative monoids underlying an equivalence of (semi)rings. -/
add_decl_doc ring_equiv.to_mul_equiv

namespace ring_equiv

section basic

variables [has_mul R] [has_add R] [has_mul S] [has_add S] [has_mul S'] [has_add S']

instance : has_coe_to_fun (R ≃+* S) := ⟨_, ring_equiv.to_fun⟩

@[simp] lemma to_fun_eq_coe_fun (f : R ≃+* S) : f.to_fun = f := rfl

/-- A ring isomorphism preserves multiplication. -/
@[simp] lemma map_mul (e : R ≃+* S) (x y : R) : e (x * y) = e x * e y := e.map_mul' x y

/-- A ring isomorphism preserves addition. -/
@[simp] lemma map_add (e : R ≃+* S) (x y : R) : e (x + y) = e x + e y := e.map_add' x y

/-- Two ring isomorphisms agree if they are defined by the
    same underlying function. -/
@[ext] lemma ext {f g : R ≃+* S} (h : ∀ x, f x = g x) : f = g :=
begin
  have h₁ : f.to_equiv = g.to_equiv := equiv.ext h,
  cases f, cases g, congr,
  { exact (funext h) },
  { exact congr_arg equiv.inv_fun h₁ }
end

protected lemma congr_arg {f : R ≃+* S} : Π {x x' : R}, x = x' → f x = f x'
| _ _ rfl := rfl

protected lemma congr_fun {f g : R ≃+* S} (h : f = g) (x : R) : f x = g x := h ▸ rfl

lemma ext_iff {f g : R ≃+* S} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, ext⟩

instance has_coe_to_mul_equiv : has_coe (R ≃+* S) (R ≃* S) := ⟨ring_equiv.to_mul_equiv⟩

instance has_coe_to_add_equiv : has_coe (R ≃+* S) (R ≃+ S) := ⟨ring_equiv.to_add_equiv⟩

@[norm_cast] lemma coe_mul_equiv (f : R ≃+* S) (a : R) :
  (f : R ≃* S) a = f a := rfl

@[norm_cast] lemma coe_add_equiv (f : R ≃+* S) (a : R) :
  (f : R ≃+ S) a = f a := rfl

variable (R)

/-- The identity map is a ring isomorphism. -/
@[refl] protected def refl : R ≃+* R := { .. mul_equiv.refl R, .. add_equiv.refl R }

@[simp] lemma refl_apply (x : R) : ring_equiv.refl R x = x := rfl

@[simp] lemma coe_add_equiv_refl : (ring_equiv.refl R : R ≃+ R) = add_equiv.refl R := rfl

@[simp] lemma coe_mul_equiv_refl : (ring_equiv.refl R : R ≃* R) = mul_equiv.refl R := rfl

instance : inhabited (R ≃+* R) := ⟨ring_equiv.refl R⟩

variables {R}

/-- The inverse of a ring isomorphism is a ring isomorphism. -/
@[symm] protected def symm (e : R ≃+* S) : S ≃+* R :=
{ .. e.to_mul_equiv.symm, .. e.to_add_equiv.symm }

/-- See Note [custom simps projection] -/
def simps.inv_fun (e : R ≃+* S) : S → R := e.symm

initialize_simps_projections ring_equiv (to_fun → apply, inv_fun → symm_apply)

@[simp] lemma symm_symm (e : R ≃+* S) : e.symm.symm = e := ext $ λ x, rfl

@[simp] lemma coe_symm_mk (f : R → S) (g h₁ h₂ h₃ h₄) : ⇑(mk f g h₁ h₂ h₃ h₄).symm = g := rfl

/-- Transitivity of `ring_equiv`. -/
@[trans] protected def trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : R ≃+* S' :=
{ .. (e₁.to_mul_equiv.trans e₂.to_mul_equiv), .. (e₁.to_add_equiv.trans e₂.to_add_equiv) }

@[simp] lemma trans_apply {A B C : Type*}
  [semiring A] [semiring B] [semiring C] (e : A ≃+* B) (f : B ≃+* C) (a : A) :
  e.trans f a = f (e a) := rfl

protected lemma bijective (e : R ≃+* S) : function.bijective e := e.to_equiv.bijective
protected lemma injective (e : R ≃+* S) : function.injective e := e.to_equiv.injective
protected lemma surjective (e : R ≃+* S) : function.surjective e := e.to_equiv.surjective

@[simp] lemma apply_symm_apply (e : R ≃+* S) : ∀ x, e (e.symm x) = x := e.to_equiv.apply_symm_apply
@[simp] lemma symm_apply_apply (e : R ≃+* S) : ∀ x, e.symm (e x) = x := e.to_equiv.symm_apply_apply

lemma image_eq_preimage (e : R ≃+* S) (s : set R) : e '' s = e.symm ⁻¹' s :=
e.to_equiv.image_eq_preimage s

end basic

section comm_semiring
open opposite

variables (R) [comm_semiring R]

/-- A commutative ring is isomorphic to its opposite. -/
def to_opposite : R ≃+* Rᵒᵖ :=
{ map_add' := λ x y, rfl,
  map_mul' := λ x y, mul_comm (op y) (op x),
  ..equiv_to_opposite }

@[simp]
lemma to_opposite_apply (r : R) : to_opposite R r = op r := rfl

@[simp]
lemma to_opposite_symm_apply (r : Rᵒᵖ) : (to_opposite R).symm r = unop r := rfl

end comm_semiring

section semiring

variables [semiring R] [semiring S] (f : R ≃+* S) (x y : R)

/-- A ring isomorphism sends one to one. -/
@[simp] lemma map_one : f 1 = 1 := (f : R ≃* S).map_one

/-- A ring isomorphism sends zero to zero. -/
@[simp] lemma map_zero : f 0 = 0 := (f : R ≃+ S).map_zero

variable {x}

@[simp] lemma map_eq_one_iff : f x = 1 ↔ x = 1 := (f : R ≃* S).map_eq_one_iff
@[simp] lemma map_eq_zero_iff : f x = 0 ↔ x = 0 := (f : R ≃+ S).map_eq_zero_iff

lemma map_ne_one_iff : f x ≠ 1 ↔ x ≠ 1 := (f : R ≃* S).map_ne_one_iff
lemma map_ne_zero_iff : f x ≠ 0 ↔ x ≠ 0 := (f : R ≃+ S).map_ne_zero_iff

/-- Produce a ring isomorphism from a bijective ring homomorphism. -/
noncomputable def of_bijective (f : R →+* S) (hf : function.bijective f) : R ≃+* S :=
{ .. equiv.of_bijective f hf, .. f }

end semiring

section

variables [ring R] [ring S] (f : R ≃+* S) (x y : R)

@[simp] lemma map_neg : f (-x) = -f x := (f : R ≃+ S).map_neg x

@[simp] lemma map_sub : f (x - y) = f x - f y := (f : R ≃+ S).map_sub x y

@[simp] lemma map_neg_one : f (-1) = -1 := f.map_one ▸ f.map_neg 1

end

section semiring_hom

variables [semiring R] [semiring S] [semiring S']

/-- Reinterpret a ring equivalence as a ring homomorphism. -/
def to_ring_hom (e : R ≃+* S) : R →+* S :=
{ .. e.to_mul_equiv.to_monoid_hom, .. e.to_add_equiv.to_add_monoid_hom }

lemma to_ring_hom_injective : function.injective (to_ring_hom : (R ≃+* S) → R →+* S) :=
λ f g h, ring_equiv.ext (ring_hom.ext_iff.1 h)

instance has_coe_to_ring_hom : has_coe (R ≃+* S) (R →+* S) := ⟨ring_equiv.to_ring_hom⟩

@[norm_cast] lemma coe_ring_hom (f : R ≃+* S) (a : R) :
  (f : R →+* S) a = f a := rfl

lemma coe_ring_hom_inj_iff {R S : Type*} [semiring R] [semiring S] (f g : R ≃+* S) :
  f = g ↔ (f : R →+* S) = g :=
⟨congr_arg _, λ h, ext $ ring_hom.ext_iff.mp h⟩

/-- Reinterpret a ring equivalence as a monoid homomorphism. -/
abbreviation to_monoid_hom (e : R ≃+* S) : R →* S := e.to_ring_hom.to_monoid_hom

/-- Reinterpret a ring equivalence as an `add_monoid` homomorphism. -/
abbreviation to_add_monoid_hom (e : R ≃+* S) : R →+ S := e.to_ring_hom.to_add_monoid_hom

@[simp]
lemma to_ring_hom_refl : (ring_equiv.refl R).to_ring_hom = ring_hom.id R := rfl

@[simp]
lemma to_monoid_hom_refl : (ring_equiv.refl R).to_monoid_hom = monoid_hom.id R := rfl

@[simp]
lemma to_add_monoid_hom_refl : (ring_equiv.refl R).to_add_monoid_hom = add_monoid_hom.id R := rfl

@[simp]
lemma to_ring_hom_apply_symm_to_ring_hom_apply (e : R ≃+* S) :
  ∀ (y : S), e.to_ring_hom (e.symm.to_ring_hom y) = y :=
e.to_equiv.apply_symm_apply

@[simp]
lemma symm_to_ring_hom_apply_to_ring_hom_apply (e : R ≃+* S) :
  ∀ (x : R), e.symm.to_ring_hom (e.to_ring_hom x) = x :=
equiv.symm_apply_apply (e.to_equiv)

@[simp]
lemma to_ring_hom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
  (e₁.trans e₂).to_ring_hom = e₂.to_ring_hom.comp e₁.to_ring_hom := rfl

@[simp]
lemma to_ring_hom_comp_symm_to_ring_hom (e : R ≃+* S) :
  e.to_ring_hom.comp e.symm.to_ring_hom = ring_hom.id _ :=
by { ext, simp }

@[simp]
lemma symm_to_ring_hom_comp_to_ring_hom (e : R ≃+* S) :
  e.symm.to_ring_hom.comp e.to_ring_hom = ring_hom.id _ :=
by { ext, simp }

/--
Construct an equivalence of rings from homomorphisms in both directions, which are inverses.
-/
def of_hom_inv (hom : R →+* S) (inv : S →+* R)
  (hom_inv_id : inv.comp hom = ring_hom.id R) (inv_hom_id : hom.comp inv = ring_hom.id S) :
  R ≃+* S :=
{ inv_fun := inv,
  left_inv := λ x, ring_hom.congr_fun hom_inv_id x,
  right_inv := λ x, ring_hom.congr_fun inv_hom_id x,
  ..hom }

@[simp]
lemma of_hom_inv_apply (hom : R →+* S) (inv : S →+* R) (hom_inv_id inv_hom_id) (r : R) :
  (of_hom_inv hom inv hom_inv_id inv_hom_id) r = hom r := rfl

@[simp]
lemma of_hom_inv_symm_apply (hom : R →+* S) (inv : S →+* R) (hom_inv_id inv_hom_id) (s : S) :
  (of_hom_inv hom inv hom_inv_id inv_hom_id).symm s = inv s := rfl

end semiring_hom

end ring_equiv

namespace mul_equiv

/-- Gives a `ring_equiv` from a `mul_equiv` preserving addition.-/
def to_ring_equiv {R : Type*} {S : Type*} [has_add R] [has_add S] [has_mul R] [has_mul S]
  (h : R ≃* S) (H : ∀ x y : R, h (x + y) = h x + h y) : R ≃+* S :=
{..h.to_equiv, ..h, ..add_equiv.mk' h.to_equiv H }

end mul_equiv

namespace ring_equiv

variables [has_add R] [has_add S] [has_mul R] [has_mul S]

@[simp] theorem trans_symm (e : R ≃+* S) : e.trans e.symm = ring_equiv.refl R := ext e.3
@[simp] theorem symm_trans (e : R ≃+* S) : e.symm.trans e = ring_equiv.refl S := ext e.4

/-- If two rings are isomorphic, and the second is an integral domain, then so is the first. -/
protected lemma is_integral_domain {A : Type*} (B : Type*) [ring A] [ring B]
  (hB : is_integral_domain B) (e : A ≃+* B) : is_integral_domain A :=
{ mul_comm := λ x y, have e.symm (e x * e y) = e.symm (e y * e x), by rw hB.mul_comm, by simpa,
  eq_zero_or_eq_zero_of_mul_eq_zero := λ x y hxy,
    have e x * e y = 0, by rw [← e.map_mul, hxy, e.map_zero],
    (hB.eq_zero_or_eq_zero_of_mul_eq_zero _ _ this).imp (λ hx, by simpa using congr_arg e.symm hx)
      (λ hy, by simpa using congr_arg e.symm hy),
  exists_pair_ne := ⟨e.symm 0, e.symm 1,
    by { haveI : nontrivial B := hB.to_nontrivial, exact e.symm.injective.ne zero_ne_one }⟩ }

/-- If two rings are isomorphic, and the second is an integral domain, then so is the first. -/
protected def integral_domain {A : Type*} (B : Type*) [ring A] [integral_domain B]
  (e : A ≃+* B) : integral_domain A :=
{ .. (‹_› : ring A), .. e.is_integral_domain B (integral_domain.to_is_integral_domain B) }

end ring_equiv

namespace equiv

variables (K : Type*) [division_ring K]

/-- In a division ring `K`, the unit group `units K`
is equivalent to the subtype of nonzero elements. -/
-- TODO: this might already exist elsewhere for `group_with_zero`
-- deduplicate or generalize
def units_equiv_ne_zero : units K ≃ {a : K | a ≠ 0} :=
⟨λ a, ⟨a.1, a.ne_zero⟩, λ a, units.mk0 _ a.2, λ ⟨_, _, _, _⟩, units.ext rfl, λ ⟨_, _⟩, rfl⟩

variable {K}

@[simp]
lemma coe_units_equiv_ne_zero (a : units K) :
  ((units_equiv_ne_zero K a) : K) = a := rfl

end equiv
