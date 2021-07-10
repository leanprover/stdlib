/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.category.Mon.basic
import category_theory.endomorphism

/-!
# Category instances for group, add_group, comm_group, and add_comm_group.

We introduce the bundled categories:
* `Group`
* `AddGroup`
* `CommGroup`
* `AddCommGroup`
along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/

universes u v

open category_theory

/-- The category of groups and group morphisms. -/
@[to_additive AddGroup]
def Group : Type (u+1) := bundled group

/-- The category of additive groups and group morphisms -/
add_decl_doc AddGroup

namespace Group

@[to_additive]
instance : bundled_hom.parent_projection group.to_monoid := ⟨⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] Group
attribute [to_additive] Group.has_coe_to_sort Group.large_category Group.concrete_category

/-- Construct a bundled `Group` from the underlying type and typeclass. -/
@[to_additive] def of (X : Type u) [group X] : Group := bundled.of X

/-- Construct a bundled `AddGroup` from the underlying type and typeclass. -/
add_decl_doc AddGroup.of

@[to_additive]
instance (G : Group) : group G := G.str

@[simp, to_additive] lemma coe_of (R : Type u) [group R] : (Group.of R : Type u) = R := rfl

@[to_additive]
instance : has_one Group := ⟨Group.of punit⟩

@[to_additive]
instance : inhabited Group := ⟨1⟩

@[to_additive]
instance one.unique : unique (1 : Group) :=
{ default := 1,
  uniq := λ a, begin cases a, refl, end }

@[simp, to_additive]
lemma one_apply (G H : Group) (g : G) : (1 : G ⟶ H) g = 1 := rfl

@[ext, to_additive]
lemma ext (G H : Group) (f₁ f₂ : G ⟶ H) (w : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
by { ext1, apply w }

-- should to_additive do this automatically?
attribute [ext] AddGroup.ext

@[to_additive has_forget_to_AddMon]
instance has_forget_to_Mon : has_forget₂ Group Mon := bundled_hom.forget₂ _ _

end Group

/-- The category of commutative groups and group morphisms. -/
@[to_additive AddCommGroup]
def CommGroup : Type (u+1) := bundled comm_group

/-- The category of additive commutative groups and group morphisms. -/
add_decl_doc AddCommGroup

/-- `Ab` is an abbreviation for `AddCommGroup`, for the sake of mathematicians' sanity. -/
abbreviation Ab := AddCommGroup

namespace CommGroup

@[to_additive]
instance : bundled_hom.parent_projection comm_group.to_group := ⟨⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] CommGroup
attribute [to_additive] CommGroup.has_coe_to_sort CommGroup.large_category
  CommGroup.concrete_category

/-- Construct a bundled `CommGroup` from the underlying type and typeclass. -/
@[to_additive] def of (G : Type u) [comm_group G] : CommGroup := bundled.of G

/-- Construct a bundled `AddCommGroup` from the underlying type and typeclass. -/
add_decl_doc AddCommGroup.of

@[to_additive]
instance comm_group_instance (G : CommGroup) : comm_group G := G.str

@[simp, to_additive] lemma coe_of (R : Type u) [comm_group R] : (CommGroup.of R : Type u) = R := rfl

@[to_additive] instance : has_one CommGroup := ⟨CommGroup.of punit⟩

@[to_additive] instance : inhabited CommGroup := ⟨1⟩

@[to_additive]
instance one.unique : unique (1 : CommGroup) :=
{ default := 1,
  uniq := λ a, begin cases a, refl, end }

@[simp, to_additive]
lemma one_apply (G H : CommGroup) (g : G) : (1 : G ⟶ H) g = 1 := rfl

@[to_additive,ext]
lemma ext (G H : CommGroup) (f₁ f₂ : G ⟶ H) (w : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
by { ext1, apply w }

attribute [ext] AddCommGroup.ext

@[to_additive has_forget_to_AddGroup]
instance has_forget_to_Group : has_forget₂ CommGroup Group := bundled_hom.forget₂ _ _

@[to_additive has_forget_to_AddCommMon]
instance has_forget_to_CommMon : has_forget₂ CommGroup CommMon :=
induced_category.has_forget₂ (λ G : CommGroup, CommMon.of G)

end CommGroup

-- This example verifies an improvement possible in Lean 3.8.
-- Before that, to have `monoid_hom.map_map` usable by `simp` here,
-- we had to mark all the concrete category `has_coe_to_sort` instances reducible.
-- Now, it just works.
@[to_additive]
example {R S : CommGroup} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 :=
by simp [h]

namespace AddCommGroup

/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
-- Note that because `ℤ : Type 0`, this forces `G : AddCommGroup.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ulift_instances.lean` file
def as_hom {G : AddCommGroup.{0}} (g : G) : (AddCommGroup.of ℤ) ⟶ G :=
gmultiples_hom G g

@[simp]
lemma as_hom_apply {G : AddCommGroup.{0}} (g : G) (i : ℤ) : (as_hom g) i = i • g := rfl

lemma as_hom_injective {G : AddCommGroup.{0}} : function.injective (@as_hom G) :=
λ h k w, by convert congr_arg (λ k : (AddCommGroup.of ℤ) ⟶ G, (k : ℤ → G) (1 : ℤ)) w; simp

@[ext]
lemma int_hom_ext
  {G : AddCommGroup.{0}} (f g : (AddCommGroup.of ℤ) ⟶ G) (w : f (1 : ℤ) = g (1 : ℤ)) : f = g :=
add_monoid_hom.ext_int w

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
lemma injective_of_mono {G H : AddCommGroup.{0}} (f : G ⟶ H) [mono f] : function.injective f :=
λ g₁ g₂ h,
begin
  have t0 : as_hom g₁ ≫ f = as_hom g₂ ≫ f :=
  begin
    ext,
    simpa [as_hom_apply] using h,
  end,
  have t1 : as_hom g₁ = as_hom g₂ := (cancel_mono _).1 t0,
  apply as_hom_injective t1,
end

end AddCommGroup

variables {X Y : Type u}

/-- Build an isomorphism in the category `Group` from a `mul_equiv` between `group`s. -/
@[to_additive add_equiv.to_AddGroup_iso, simps]
def mul_equiv.to_Group_iso [group X] [group Y] (e : X ≃* Y) : Group.of X ≅ Group.of Y :=
{ hom := e.to_monoid_hom,
  inv := e.symm.to_monoid_hom }

/-- Build an isomorphism in the category `AddGroup` from an `add_equiv` between `add_group`s. -/
add_decl_doc add_equiv.to_AddGroup_iso

/-- Build an isomorphism in the category `CommGroup` from a `mul_equiv` between `comm_group`s. -/
@[to_additive add_equiv.to_AddCommGroup_iso, simps]
def mul_equiv.to_CommGroup_iso [comm_group X] [comm_group Y] (e : X ≃* Y) :
  CommGroup.of X ≅ CommGroup.of Y :=
{ hom := e.to_monoid_hom,
  inv := e.symm.to_monoid_hom }

/-- Build an isomorphism in the category `AddCommGroup` from a `add_equiv` between
`add_comm_group`s. -/
add_decl_doc add_equiv.to_AddCommGroup_iso

namespace category_theory.iso

/-- Build a `mul_equiv` from an isomorphism in the category `Group`. -/
@[to_additive AddGroup_iso_to_add_equiv "Build an `add_equiv` from an isomorphism in the category
`AddGroup`.", simps]
def Group_iso_to_mul_equiv {X Y : Group} (i : X ≅ Y) : X ≃* Y :=
i.hom.to_mul_equiv i.inv i.hom_inv_id i.inv_hom_id

/-- Build a `mul_equiv` from an isomorphism in the category `CommGroup`. -/
@[to_additive AddCommGroup_iso_to_add_equiv "Build an `add_equiv` from an isomorphism
in the category `AddCommGroup`.", simps]
def CommGroup_iso_to_mul_equiv {X Y : CommGroup} (i : X ≅ Y) : X ≃* Y :=
i.hom.to_mul_equiv i.inv i.hom_inv_id i.inv_hom_id

end category_theory.iso

/-- multiplicative equivalences between `group`s are the same as (isomorphic to) isomorphisms
in `Group` -/
@[to_additive add_equiv_iso_AddGroup_iso "additive equivalences between `add_group`s are the same
as (isomorphic to) isomorphisms in `AddGroup`"]
def mul_equiv_iso_Group_iso {X Y : Type u} [group X] [group Y] :
  (X ≃* Y) ≅ (Group.of X ≅ Group.of Y) :=
{ hom := λ e, e.to_Group_iso,
  inv := λ i, i.Group_iso_to_mul_equiv, }

/-- multiplicative equivalences between `comm_group`s are the same as (isomorphic to) isomorphisms
in `CommGroup` -/
@[to_additive add_equiv_iso_AddCommGroup_iso "additive equivalences between `add_comm_group`s are
the same as (isomorphic to) isomorphisms in `AddCommGroup`"]
def mul_equiv_iso_CommGroup_iso {X Y : Type u} [comm_group X] [comm_group Y] :
  (X ≃* Y) ≅ (CommGroup.of X ≅ CommGroup.of Y) :=
{ hom := λ e, e.to_CommGroup_iso,
  inv := λ i, i.CommGroup_iso_to_mul_equiv, }

namespace category_theory.Aut

/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group
of permutations. -/
def iso_perm {α : Type u} : Group.of (Aut α) ≅ Group.of (equiv.perm α) :=
{ hom := ⟨λ g, g.to_equiv, (by tidy), (by tidy)⟩,
  inv := ⟨λ g, g.to_iso, (by tidy), (by tidy)⟩ }

/-- The (unbundled) group of automorphisms of a type is `mul_equiv` to the (unbundled) group
of permutations. -/
def mul_equiv_perm {α : Type u} : Aut α ≃* equiv.perm α :=
iso_perm.Group_iso_to_mul_equiv

end category_theory.Aut

@[to_additive]
instance Group.forget_reflects_isos : reflects_isomorphisms (forget Group.{u}) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget Group).map f),
    let e : X ≃* Y := { ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_Group_iso).1⟩,
  end }

@[to_additive]
instance CommGroup.forget_reflects_isos : reflects_isomorphisms (forget CommGroup.{u}) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget CommGroup).map f),
    let e : X ≃* Y := { ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_CommGroup_iso).1⟩,
  end }
