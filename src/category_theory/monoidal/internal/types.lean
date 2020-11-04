/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Mon.basic
import category_theory.monoidal.CommMon_
import category_theory.monoidal.types

/-!
# `Mon_ (Type u) ≌ Mon.{u}`

The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/

universes v u

open category_theory
open category_theory.monoidal

namespace Mon_Type_equivalence_Mon

instance Mon_monoid (A : Mon_ (Type u)) : monoid (A.X) :=
{ one := A.one punit.star,
  mul := λ x y, A.mul (x, y),
  one_mul := λ x, by simpa [-Mon_.one_mul_hom] using congr_fun A.one_mul (punit.star, x),
  mul_one := λ x, by simpa [-Mon_.mul_one_hom] using congr_fun A.mul_one (x, punit.star),
  mul_assoc := λ x y z, by simpa [-Mon_.mul_assoc] using congr_fun A.mul_assoc ((x, y), z) }

/--
Converting a monoid object in `Type` to a bundled monoid.
-/
def functor : Mon_ (Type u) ⥤ Mon.{u} :=
{ obj := λ A, ⟨A.X⟩,
  map := λ A B f,
  { to_fun := f.hom,
    map_one' := congr_fun f.one_hom punit.star,
    map_mul' := λ x y, congr_fun f.mul_hom (x, y), }, }

/--
Converting a bundled monoid to a monoid object in `Type`.
-/
def inverse : Mon.{u} ⥤ Mon_ (Type u) :=
{ obj := λ A,
  { X := A,
    one := λ _, 1,
    mul := λ p, p.1 * p.2,
    mul_assoc' := by { ext ⟨⟨x, y⟩, z⟩, simp [mul_assoc], }, },
  map := λ A B f,
  { hom := f, }, }

end Mon_Type_equivalence_Mon

open Mon_Type_equivalence_Mon

/--
The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.
-/
def Mon_Type_equivalence_Mon : Mon_ (Type u) ≌ Mon.{u} :=
{ functor := functor,
  inverse := inverse,
  unit_iso := nat_iso.of_components
    (λ A, { hom := { hom := 𝟙 _, }, inv := { hom := 𝟙 _, }, })
    (by tidy),
  counit_iso := nat_iso.of_components (λ A,
  { hom := { to_fun := id, map_one' := rfl, map_mul' := λ x y, rfl, },
    inv := { to_fun := id, map_one' := rfl, map_mul' := λ x y, rfl, }, }) (by tidy), }

/--
The equivalence `Mon_ (Type u) ≌ Mon.{u}`
is naturally compatible with the forgetful functors to `Type u`.
-/
def Mon_Type_equivalence_Mon_forget :
  Mon_Type_equivalence_Mon.functor ⋙ forget Mon ≅ Mon_.forget (Type u) :=
nat_iso.of_components (λ A, iso.refl _) (by tidy)

instance Mon_Type_inhabited : inhabited (Mon_ (Type u)) :=
⟨Mon_Type_equivalence_Mon.inverse.obj (Mon.of punit)⟩


namespace CommMon_Type_equivalence_CommMon

instance CommMon_comm_monoid (A : CommMon_ (Type u)) : comm_monoid (A.X) :=
{ mul_comm := λ x y, by simpa [-CommMon_.mul_comm] using congr_fun A.mul_comm (y, x),
  ..Mon_Type_equivalence_Mon.Mon_monoid A.to_Mon_ }

/--
Converting a commutative monoid object in `Type` to a bundled commutative monoid.
-/
def functor : CommMon_ (Type u) ⥤ CommMon.{u} :=
{ obj := λ A, ⟨A.X⟩,
  map := λ A B f, Mon_Type_equivalence_Mon.functor.map f, }

/--
Converting a bundled commutative monoid to a commutative monoid object in `Type`.
-/
def inverse : CommMon.{u} ⥤ CommMon_ (Type u) :=
{ obj := λ A,
  { mul_comm' := by { ext ⟨x, y⟩, exact comm_monoid.mul_comm y x, },
    ..Mon_Type_equivalence_Mon.inverse.obj ((forget₂ CommMon Mon).obj A), },
  map := λ A B f, Mon_Type_equivalence_Mon.inverse.map f, }

end CommMon_Type_equivalence_CommMon

open CommMon_Type_equivalence_CommMon

/--
The category of internal commutative monoid objects in `Type`
is equivalent to the category of "native" bundled commutative monoids.
-/
def CommMon_Type_equivalence_CommMon : CommMon_ (Type u) ≌ CommMon.{u} :=
{ functor := functor,
  inverse := inverse,
  unit_iso := nat_iso.of_components
    (λ A, { hom := { hom := 𝟙 _, }, inv := { hom := 𝟙 _, }, })
    (by tidy),
  counit_iso := nat_iso.of_components (λ A,
  { hom := { to_fun := id, map_one' := rfl, map_mul' := λ x y, rfl, },
    inv := { to_fun := id, map_one' := rfl, map_mul' := λ x y, rfl, }, }) (by tidy), }

/--
The equivalences `Mon_ (Type u) ≌ Mon.{u}` and `CommMon_ (Type u) ≌ CommMon.{u}`
are naturally compatible with the forgetful functors to `Mon` and `Mon_ (Type u)`.
-/
def CommMon_Type_equivalence_CommMon_forget :
  CommMon_Type_equivalence_CommMon.functor ⋙ forget₂ CommMon Mon ≅
  CommMon_.forget₂_Mon_ (Type u) ⋙ Mon_Type_equivalence_Mon.functor :=
nat_iso.of_components (λ A, iso.refl _) (by tidy)

instance CommMon_Type_inhabited : inhabited (CommMon_ (Type u)) :=
⟨CommMon_Type_equivalence_CommMon.inverse.obj (CommMon.of punit)⟩
