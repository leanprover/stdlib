/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Yury Kudryashov
-/

import algebra.category.Mon.basic
import category_theory.fully_faithful
import algebra.ring
import data.int.basic

/-!
# Category instances for semiring, ring, comm_semiring, and comm_ring.

We introduce the bundled categories:
* `SemiRing`
* `Ring`
* `CommSemiRing`
* `CommRing`
along with the relevant forgetful functors between them.
-/

universes u v

open category_theory

/-- The category of semirings. -/
def SemiRing : Type (u+1) := bundled semiring

namespace SemiRing
local attribute [reducible] SemiRing

/-- Construct a bundled SemiRing from the underlying type and typeclass. -/
def of (R : Type u) [semiring R] : SemiRing := bundled.of R

instance bundled_hom : bundled_hom @ring_hom :=
⟨@ring_hom.to_fun, @ring_hom.id, @ring_hom.comp, @ring_hom.ext⟩

instance (R : SemiRing) : semiring R := R.str

-- Setup instances while `SemiRing` is reducible:
instance : concrete_category SemiRing.{u} := infer_instance
instance : has_coe_to_sort SemiRing.{u} := infer_instance

instance has_forget_to_Mon : has_forget₂ SemiRing.{u} Mon.{u} :=
bundled_hom.mk_has_forget₂ @semiring.to_monoid (λ R₁ R₂ f, f.to_monoid_hom) (λ _ _ _, rfl)

end SemiRing

/-- The category of rings. -/
def Ring : Type (u+1) := induced_category SemiRing (bundled.map @ring.to_semiring.{u})

namespace Ring
local attribute [reducible] Ring

/-- Construct a bundled Ring from the underlying type and typeclass. -/
def of (R : Type u) [ring R] : Ring := bundled.of R

instance (R : Ring) : ring R := R.str

-- Setup instances while `Ring` is reducible:
instance : concrete_category Ring.{u} := infer_instance
instance : has_coe_to_sort Ring.{u} := infer_instance
instance : has_forget₂ Ring.{u} SemiRing.{u} := infer_instance

end Ring

/-- The category of commutative semirings. -/
def CommSemiRing : Type (u+1) := induced_category SemiRing (bundled.map comm_semiring.to_semiring.{u})

namespace CommSemiRing
local attribute [reducible] CommSemiRing

/-- Construct a bundled CommSemiRing from the underlying type and typeclass. -/
def of (R : Type u) [comm_semiring R] : CommSemiRing := bundled.of R

instance (R : CommSemiRing) : comm_semiring R := R.str

-- Setup instances while `CommSemiRing` is reducible:
instance : concrete_category CommSemiRing.{u} := infer_instance
instance : has_coe_to_sort CommSemiRing.{u} := infer_instance
instance : has_forget₂ CommSemiRing.{u} SemiRing.{u} := infer_instance

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance has_forget_to_CommMon : has_forget₂ CommSemiRing.{u} CommMon.{u} :=
has_forget₂.mk'
  (λ R : CommSemiRing.{u}, CommMon.of R) (λ R, rfl)
  (λ R₁ R₂ f, f.to_monoid_hom) (by tidy)

end CommSemiRing

/-- The category of commutative rings. -/
def CommRing : Type (u+1) := induced_category Ring (bundled.map comm_ring.to_ring.{u})

namespace CommRing
local attribute [reducible] CommRing

/-- Construct a bundled CommRing from the underlying type and typeclass. -/
def of (R : Type u) [comm_ring R] : CommRing := bundled.of R

instance (R : CommRing) : comm_ring R := R.str

-- Setup instances while `CommRing` is reducible:
instance : concrete_category CommRing.{u} := infer_instance
instance : has_coe_to_sort CommRing.{u} := infer_instance
instance : has_forget₂ CommRing.{u} Ring.{u} := infer_instance

/-- The forgetful functor from commutative rings to commutative semirings. -/
instance has_forget_to_CommSemiRing : has_forget₂ CommRing.{u} CommSemiRing.{u} :=
has_forget₂.mk' (λ R : CommRing.{u}, CommSemiRing.of R) (λ R, rfl) (λ R₁ R₂ f, f) (by tidy)

end CommRing

namespace ring_equiv

variables {X Y : Type u}

section
variables [ring X] [ring Y]

/-- Build an isomorphism in the category `Ring` from a `ring_equiv` between `ring`s. -/
def to_Ring_iso (e : X ≃r Y) : Ring.of X ≅ Ring.of Y :=
{ hom := e.to_ring_hom,
  inv := e.symm.to_ring_hom }

@[simp] lemma to_Ring_iso_hom {e : X ≃r Y} : e.to_Ring_iso.hom = e.to_ring_hom := rfl
@[simp] lemma to_Ring_iso_inv {e : X ≃r Y} : e.to_Ring_iso.inv = e.symm.to_ring_hom := rfl
end

section
variables [comm_ring X] [comm_ring Y]

/-- Build an isomorphism in the category `CommRing` from a `ring_equiv` between `comm_ring`s. -/
def to_CommRing_iso (e : X ≃r Y) : CommRing.of X ≅ CommRing.of Y :=
{ hom := e.to_ring_hom,
  inv := e.symm.to_ring_hom }

@[simp] lemma to_CommRing_iso_hom {e : X ≃r Y} : e.to_CommRing_iso.hom = e.to_ring_hom := rfl
@[simp] lemma to_CommRing_iso_inv {e : X ≃r Y} : e.to_CommRing_iso.inv = e.symm.to_ring_hom := rfl
end

end ring_equiv

namespace category_theory.iso

/-- Build a `ring_equiv` from an isomorphism in the category `Ring`. -/
def Ring_iso_to_ring_equiv {X Y : Ring.{u}} (i : X ≅ Y) : X ≃r Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  hom       := by apply_instance }.

/-- Build a `ring_equiv` from an isomorphism in the category `CommRing`. -/
def CommRing_iso_to_ring_equiv {X Y : CommRing.{u}} (i : X ≅ Y) : X ≃r Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  hom       := by apply_instance  }.

end category_theory.iso

/-- ring equivalences between `ring`s are the same as (isomorphic to) isomorphisms in `Ring`. -/
def ring_equiv_iso_Ring_iso {X Y : Type u} [ring X] [ring Y] :
  (X ≃r Y) ≅ (Ring.of X ≅ Ring.of Y) :=
{ hom := λ e, e.to_Ring_iso,
  inv := λ i, i.Ring_iso_to_ring_equiv, }

/-- ring equivalences between `comm_ring`s are the same as (isomorphic to) isomorphisms in `CommRing`. -/
def ring_equiv_iso_CommRing_iso {X Y : Type u} [comm_ring X] [comm_ring Y] :
  (X ≃r Y) ≅ (CommRing.of X ≅ CommRing.of Y) :=
{ hom := λ e, e.to_CommRing_iso,
  inv := λ i, i.CommRing_iso_to_ring_equiv, }
