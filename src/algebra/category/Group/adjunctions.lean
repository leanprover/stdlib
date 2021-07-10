/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import algebra.category.Group.basic
import group_theory.free_abelian_group

/-!
# Adjunctions regarding the category of (abelian) groups

This file contains construction of basic adjunctions concerning the category of groups and the
category of abelian groups.

## Main definitions

* `AddCommGroup.free`: constructs the functor associating to a type `X` the free abelian group with
  generators `x : X`.
* `Group.free`: constructs the functor associating to a type `X` the free group with
  generators `x : X`.
* `abelianize`: constructs the functor which associates to a group `G` its abelianization `Gᵃᵇ`.

## Main statements

* `AddCommGroup.adj`: proves that `AddCommGroup.free` is the left adjoint of the forgetful functor
  from abelian groups to types.
* `Group.adj`: proves that `Group.free` is the left adjoint of the forgetful functor from groups to
  types.
* `abelianize_adj`: proves that `abelianize` is left adjoint to the forgetful functor from
  abelian groups to groups.
-/

noncomputable theory

universe u

open category_theory

namespace AddCommGroup

open_locale classical

/--
The free functor `Type u ⥤ AddCommGroup` sending a type `X` to the
free abelian group with generators `x : X`.
-/
def free : Type u ⥤ AddCommGroup :=
{ obj := λ α, of (free_abelian_group α),
  map := λ X Y, free_abelian_group.map,
  map_id' := λ X, add_monoid_hom.ext free_abelian_group.map_id_apply,
  map_comp' := λ X Y Z f g, add_monoid_hom.ext free_abelian_group.map_comp_apply, }

@[simp] lemma free_obj_coe {α : Type u} :
  (free.obj α : Type u) = (free_abelian_group α) := rfl

@[simp] lemma free_map_coe {α β : Type u} {f : α → β} (x : free_abelian_group α) :
  (free.map f) x = f <$> x := rfl

/--
The free-forgetful adjunction for abelian groups.
-/
def adj : free ⊣ forget AddCommGroup.{u} :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X G, free_abelian_group.lift.symm,
  hom_equiv_naturality_left_symm' :=
  by { intros, ext, refl} }

/--
As an example, we now give a high-powered proof that
the monomorphisms in `AddCommGroup` are just the injective functions.

(This proof works in all universes.)
-/
example {G H : AddCommGroup.{u}} (f : G ⟶ H) [mono f] : function.injective f :=
(mono_iff_injective f).1 (right_adjoint_preserves_mono adj (by apply_instance : mono f))

instance : is_right_adjoint (forget AddCommGroup.{u}) := ⟨_, adj⟩

end AddCommGroup

namespace Group

/-- The free functor `Type u ⥤ Group` sending a type `X` to the free group with generators `x : X`.
-/
def free : Type u ⥤ Group :=
{ obj := λ α, of (free_group α),
  map := λ X Y, free_group.map,
  map_id' := by { intros, ext1, refl },
  map_comp' := by { intros, ext1, refl } }

/-- The free-forgetful adjunction for groups.
-/
def adj : free ⊣ forget Group.{u} :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X G, free_group.lift.symm,
  hom_equiv_naturality_left_symm' := λ X Y G f g, begin ext1, refl end  }

instance : is_right_adjoint (forget Group.{u}) := ⟨_, adj⟩

end Group

section abelianization

/-- The abelianization functor `Group ⥤ CommGroup` sending a group `G` to its abelianization `Gᵃᵇ`.
 -/
def abelianize : Group.{u} ⥤ CommGroup.{u} :=
{ obj := λ G, { α := abelianization G, str := by apply_instance },
  map := λ G H f, abelianization.lift ( { to_fun := λ x, abelianization.of (f x),
  map_one' := by simp,
  map_mul' := by simp } ),
  map_id' := by { intros, simp only [monoid_hom.mk_coe, coe_id], ext1, refl },
  map_comp' := by { intros, simp only [coe_comp], ext1, refl } }

/-- The abelianization-forgetful adjuction from `Group` to `CommGroup`.-/
def abelianize_adj : abelianize ⊣ forget₂ CommGroup.{u} Group.{u} :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ G A, abelianization.lift.symm,
  hom_equiv_naturality_left_symm' := λ G H A f g, by { ext1, refl } }

end abelianization
