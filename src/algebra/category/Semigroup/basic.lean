/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import category_theory.concrete_category.bundled_hom
import category_theory.concrete_category.reflects_isomorphisms
import algebra.pempty_instances

/-!
# Category instances for has_mul, has_add, semigroup and add_semigroup

We introduce the bundled categories:
* `Magma`
* `AddMagma`
* `Semigroup`
* `AddSemigroup`
along with the relevant forgetful functors between them.

This closely follows `algebra.category.Mon.basic`.

## TODO

* Limits in these categories
* free/forgetful adjunctions
-/

universes u v

open category_theory

/-- The category of magmas and magma morphisms. -/
@[to_additive AddMagma]
def Magma : Type (u+1) := bundled has_mul

/-- The category of additive magmas and additive magma morphisms. -/
add_decl_doc AddMagma

namespace Magma

@[to_additive]
instance bundled_hom : bundled_hom @mul_hom :=
⟨@mul_hom.to_fun, @mul_hom.id, @mul_hom.comp, @mul_hom.coe_inj⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] Magma
attribute [to_additive] Magma.has_coe_to_sort Magma.large_category Magma.concrete_category

/-- Construct a bundled `Magma` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [has_mul M] : Magma := bundled.of M

/-- Construct a bundled `Magma` from the underlying type and typeclass. -/
add_decl_doc AddMagma.of

@[to_additive]
instance : inhabited Magma := ⟨Magma.of pempty⟩

@[to_additive]
instance (M : Magma) : has_mul M := M.str

@[simp, to_additive] lemma coe_of (R : Type u) [has_mul R] : (Magma.of R : Type u) = R := rfl

end Magma

/-- The category of semigroups and semigroup morphisms. -/
@[to_additive AddSemigroup]
def Semigroup : Type (u+1) := bundled semigroup

/-- The category of additive semigroups and semigroup morphisms. -/
add_decl_doc AddSemigroup

namespace Semigroup

@[to_additive]
instance : bundled_hom.parent_projection semigroup.to_has_mul := ⟨⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] Semigroup
attribute [to_additive] Semigroup.has_coe_to_sort Semigroup.large_category
  Semigroup.concrete_category

/-- Construct a bundled `Semigroup` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [semigroup M] : Semigroup := bundled.of M

/-- Construct a bundled `AddSemigroup` from the underlying type and typeclass. -/
add_decl_doc AddSemigroup.of

@[to_additive]
instance : inhabited Semigroup := ⟨Semigroup.of pempty⟩

@[to_additive]
instance (M : Semigroup) : semigroup M := M.str

@[simp, to_additive] lemma coe_of (R : Type u) [semigroup R] : (Semigroup.of R : Type u) = R := rfl

@[to_additive has_forget_to_AddMagma]
instance has_forget_to_Magma : has_forget₂ Semigroup Magma := bundled_hom.forget₂ _ _

end Semigroup

variables {X Y : Type u}

section
variables [has_mul X] [has_mul Y]

/-- Build an isomorphism in the category `Magma` from a `mul_equiv` between `has_mul`s. -/
@[to_additive add_equiv.to_AddMagma_iso "Build an isomorphism in the category `AddMagma` from
an `add_equiv` between `has_add`s.", simps]
def mul_equiv.to_Magma_iso (e : X ≃* Y) : Magma.of X ≅ Magma.of Y :=
{ hom := e.to_mul_hom,
  inv := e.symm.to_mul_hom }

end

section
variables [semigroup X] [semigroup Y]

/-- Build an isomorphism in the category `Semigroup` from a `mul_equiv` between `semigroup`s. -/
@[to_additive add_equiv.to_AddSemigroup_iso "Build an isomorphism in the category
`AddSemigroup` from an `add_equiv` between `add_semigroup`s.", simps]
def mul_equiv.to_Semigroup_iso (e : X ≃* Y) : Semigroup.of X ≅ Semigroup.of Y :=
{ hom := e.to_mul_hom,
  inv := e.symm.to_mul_hom }

end

namespace category_theory.iso

/-- Build a `mul_equiv` from an isomorphism in the category `Magma`. -/
@[to_additive AddMagma_iso_to_add_equiv "Build an `add_equiv` from an isomorphism in the category
`AddMagma`."]
def Magma_iso_to_mul_equiv {X Y : Magma} (i : X ≅ Y) : X ≃* Y :=
{ to_fun := i.hom,
  inv_fun := i.inv,
  left_inv := begin rw function.left_inverse, simp end,
  right_inv := begin rw function.right_inverse, rw function.left_inverse, simp end,
  map_mul' := by simp }

/-- Build a `mul_equiv` from an isomorphism in the category `Semigroup`. -/
@[to_additive "Build an `add_equiv` from an isomorphism in the category
`AddSemigroup`."]
def Semigroup_iso_to_mul_equiv {X Y : Semigroup} (i : X ≅ Y) : X ≃* Y :=
{ to_fun := i.hom,
  inv_fun := i.inv,
  left_inv := begin rw function.left_inverse, simp end,
  right_inv := begin rw function.right_inverse, rw function.left_inverse, simp end,
  map_mul' := by simp }

end category_theory.iso

/-- multiplicative equivalences between `has_mul`s are the same as (isomorphic to) isomorphisms
in `Magma` -/
@[to_additive add_equiv_iso_AddMagma_iso "additive equivalences between `has_add`s are the same
as (isomorphic to) isomorphisms in `AddMagma`"]
def mul_equiv_iso_Magma_iso {X Y : Type u} [has_mul X] [has_mul Y] :
  (X ≃* Y) ≅ (Magma.of X ≅ Magma.of Y) :=
{ hom := λ e, e.to_Magma_iso,
  inv := λ i, i.Magma_iso_to_mul_equiv }

/-- multiplicative equivalences between `semigroup`s are the same as (isomorphic to) isomorphisms
in `Semigroup` -/
@[to_additive add_equiv_iso_AddSemigroup_iso "additive equivalences between `add_semigroup`s are
the same as (isomorphic to) isomorphisms in `AddSemigroup`"]
def mul_equiv_iso_Semigroup_iso {X Y : Type u} [semigroup X] [semigroup Y] :
  (X ≃* Y) ≅ (Semigroup.of X ≅ Semigroup.of Y) :=
{ hom := λ e, e.to_Semigroup_iso,
  inv := λ i, i.Semigroup_iso_to_mul_equiv }

@[to_additive]
instance Magma.forget_reflects_isos : reflects_isomorphisms (forget Magma.{u}) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget Magma).map f),
    let e : X ≃* Y := { ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_Magma_iso).1⟩,
  end }

@[to_additive]
instance Semigroup.forget_reflects_isos : reflects_isomorphisms (forget Semigroup.{u}) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget Semigroup).map f),
    let e : X ≃* Y := { ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_Semigroup_iso).1⟩,
  end }

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/
example : reflects_isomorphisms (forget₂ Semigroup Magma) := by apply_instance
