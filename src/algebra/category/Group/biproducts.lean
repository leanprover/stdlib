/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.limits
import category_theory.limits.shapes.biproducts
import category_theory.limits.shapes.types

/-!
# The category of abelian groups has finite biproducts
-/

open category_theory
open category_theory.limits

open_locale big_operators

universe u

namespace AddCommGroup

/--
Construct limit data for a binary product in `AddCommGroup`, using `AddCommGroup.of (G × H)`.
-/
def binary_product_limit_cone (G H : AddCommGroup.{u}) : limits.limit_cone (pair G H) :=
{ cone :=
  { X := AddCommGroup.of (G × H),
    π := { app := λ j, walking_pair.cases_on j (add_monoid_hom.fst G H) (add_monoid_hom.snd G H) }},
  is_limit :=
  { lift := λ s, add_monoid_hom.prod (s.π.app walking_pair.left) (s.π.app walking_pair.right),
    fac' := begin rintros s (⟨⟩|⟨⟩); { ext x, simp, }, end,
    uniq' := λ s m w,
    begin
      ext; [rw ← w walking_pair.left, rw ← w walking_pair.right]; refl,
    end, } }


instance has_binary_product (G H : AddCommGroup.{u}) : has_binary_product G H :=
has_limit.mk (binary_product_limit_cone G H)

instance (G H : AddCommGroup.{u}) : has_binary_biproduct G H :=
has_binary_biproduct.of_has_binary_product _ _

/--
We verify that the biproduct in AddCommGroup is isomorphic to
the cartesian product of the underlying types:
-/
noncomputable
def biprod_iso_prod (G H : AddCommGroup.{u}) : (G ⊞ H : AddCommGroup) ≅ AddCommGroup.of (G × H) :=
is_limit.cone_point_unique_up_to_iso
  (binary_biproduct.is_limit G H)
  (binary_product_limit_cone G H).is_limit

-- Furthermore, our biproduct will automatically function as a coproduct.
example (G H : AddCommGroup.{u}) : has_colimit (pair G H) := by apply_instance

variables {J : Type u} (F : (discrete J) ⥤ AddCommGroup.{u})

namespace has_limit

/--
The map from an arbitrary cone over a indexed family of abelian groups
to the cartesian product of those groups.
-/
def lift (s : cone F) :
  s.X ⟶ AddCommGroup.of (Π j, F.obj j) :=
{ to_fun := λ x j, s.π.app j x,
  map_zero' := by { ext, simp },
  map_add' := λ x y, by { ext, simp }, }

@[simp] lemma lift_apply (s : cone F) (x : s.X) (j : J) : (lift F s) x j = s.π.app j x := rfl

/--
Construct limit data for a product in `AddCommGroup`, using `AddCommGroup.of (Π j, F.obj j)`.
-/
def product_limit_cone : limits.limit_cone F :=
{ cone :=
  { X := AddCommGroup.of (Π j, F.obj j),
    π := discrete.nat_trans (λ j, add_monoid_hom.apply (λ j, F.obj j) j), },
  is_limit :=
  { lift := lift F,
    fac' := λ s j, by { ext, simp, },
    uniq' := λ s m w,
    begin
      ext x j,
      dsimp only [has_limit.lift],
      simp only [add_monoid_hom.coe_mk],
      exact congr_arg (λ f : s.X ⟶ F.obj j, (f : s.X → F.obj j) x) (w j),
    end, }, }

end has_limit

section

open has_limit

variables [decidable_eq J] [fintype J]

instance (f : J → AddCommGroup.{u}) : has_biproduct f :=
has_biproduct.of_has_product _

/--
We verify that the biproduct we've just defined is isomorphic to the AddCommGroup structure
on the dependent function type
-/
noncomputable
def biproduct_iso_pi (f : J → AddCommGroup.{u}) :
  (⨁ f : AddCommGroup) ≅ AddCommGroup.of (Π j, f j) :=
is_limit.cone_point_unique_up_to_iso
  (biproduct.is_limit f)
  (product_limit_cone (discrete.functor f)).is_limit

end

instance : has_finite_biproducts AddCommGroup :=
⟨λ J _ _, by exactI { has_biproduct := λ f, by apply_instance }⟩

end AddCommGroup
