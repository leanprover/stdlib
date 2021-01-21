/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Mon.basic
import group_theory.submonoid
import category_theory.limits.types
import category_theory.limits.creates

/-!
# The category of (commutative) (additive) monoids has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/

noncomputable theory

open category_theory
open category_theory.limits

universe u

namespace Mon

variables {J : Type u} [small_category J]

@[to_additive]
instance monoid_obj (F : J ⥤ Mon) (j) :
  monoid ((F ⋙ forget Mon).obj j) :=
by { change monoid (F.obj j), apply_instance }

/--
The flat sections of a functor into `Mon` form a submonoid of all sections.
-/
@[to_additive
  "The flat sections of a functor into `AddMon` form an additive submonoid of all sections."]
def sections_submonoid (F : J ⥤ Mon) :
  submonoid (Π j, F.obj j) :=
{ carrier := (F ⋙ forget Mon).sections,
  one_mem' := λ j j' f, by simp,
  mul_mem' := λ a b ah bh j j' f,
  begin
    simp only [forget_map_eq_coe, functor.comp_map, monoid_hom.map_mul, pi.mul_apply],
    dsimp [functor.sections] at ah bh,
    rw [ah f, bh f],
  end }

@[to_additive]
instance limit_monoid (F : J ⥤ Mon) :
  monoid (types.limit_cone (F ⋙ forget Mon.{u})).X :=
(sections_submonoid F).to_monoid

/-- `limit.π (F ⋙ forget Mon) j` as a `monoid_hom`. -/
@[to_additive "`limit.π (F ⋙ forget AddMon) j` as an `add_monoid_hom`."]
def limit_π_monoid_hom (F : J ⥤ Mon.{u}) (j) :
  (types.limit_cone (F ⋙ forget Mon)).X →* (F ⋙ forget Mon).obj j :=
{ to_fun := (types.limit_cone (F ⋙ forget Mon)).π.app j,
  map_one' := rfl,
  map_mul' := λ x y, rfl }

namespace has_limits
-- The next two definitions are used in the construction of `has_limits Mon`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `Mon`.
(Internal use only; use the limits API.)
-/
@[to_additive "(Internal use only; use the limits API.)"]
def limit_cone (F : J ⥤ Mon) : cone F :=
{ X := Mon.of (types.limit_cone (F ⋙ forget _)).X,
  π :=
  { app := limit_π_monoid_hom F,
    naturality' := λ j j' f,
      monoid_hom.coe_inj ((types.limit_cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `Mon` is a limit cone.
(Internal use only; use the limits API.)
-/
@[to_additive "(Internal use only; use the limits API.)"]
def limit_cone_is_limit (F : J ⥤ Mon) : is_limit (limit_cone F) :=
begin
  refine is_limit.of_faithful
    (forget Mon) (types.limit_cone_is_limit _)
    (λ s, ⟨_, _, _⟩) (λ s, rfl); tidy,
end

end has_limits

open has_limits

/-- The category of monoids has all limits. -/
@[to_additive]
instance has_limits : has_limits Mon :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk
    { cone     := limit_cone F,
      is_limit := limit_cone_is_limit F } } }

/--
The forgetful functor from monoids to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
@[to_additive]
instance forget_preserves_limits : preserves_limits (forget Mon) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
    (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget _)) } }

end Mon

namespace CommMon

variables {J : Type u} [small_category J]

@[to_additive]
instance comm_monoid_obj (F : J ⥤ CommMon) (j) :
  comm_monoid ((F ⋙ forget CommMon).obj j) :=
by { change comm_monoid (F.obj j), apply_instance }

@[to_additive]
instance limit_comm_monoid (F : J ⥤ CommMon) :
  comm_monoid (types.limit_cone (F ⋙ forget CommMon.{u})).X :=
@submonoid.to_comm_monoid (Π j, F.obj j) _
  (Mon.sections_submonoid (F ⋙ forget₂ CommMon Mon.{u}))

/--
We show that the forgetful functor `CommMon ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `comm_monoid` instance available,
and then reuse the existing limit.
-/
@[to_additive]
instance (F : J ⥤ CommMon) : creates_limit F (forget₂ CommMon Mon.{u}) :=
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone :=
  { X := CommMon.of (types.limit_cone (F ⋙ forget CommMon)).X,
    π :=
    { app := Mon.limit_π_monoid_hom (F ⋙ forget₂ CommMon Mon),
      naturality' := (Mon.has_limits.limit_cone (F ⋙ forget₂ _ _)).π.naturality, } },
  valid_lift := is_limit.unique_up_to_iso (Mon.has_limits.limit_cone_is_limit _) t,
  makes_limit := is_limit.of_faithful (forget₂ CommMon Mon.{u})
    (Mon.has_limits.limit_cone_is_limit _) (λ s, _) (λ s, rfl) })

/--
A choice of limit cone for a functor into `CommMon`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive "A choice of limit cone for a functor into `CommMon`. (Generally, you'll just want
to use `limit F`.)"]
def limit_cone (F : J ⥤ CommMon) : cone F :=
lift_limit (limit.is_limit (F ⋙ (forget₂ CommMon Mon.{u})))

/--
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive "The chosen cone is a limit cone. (Generally, you'll just want to use
`limit.cone F`.)"]
def limit_cone_is_limit (F : J ⥤ CommMon) : is_limit (limit_cone F) :=
lifted_limit_is_limit _

/-- The category of commutative monoids has all limits. -/
@[to_additive]
instance has_limits : has_limits CommMon :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ CommMon Mon) } }

/--
The forgetful functor from commutative monoids to monoids preserves all limits.
(That is, the underlying monoid could have been computed instead as limits in the category
of monoids.)
-/
@[to_additive AddCommMon.forget₂_AddMon_preserves_limits]
instance forget₂_Mon_preserves_limits : preserves_limits (forget₂ CommMon Mon) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by apply_instance } }

/--
The forgetful functor from commutative monoids to types preserves all limits. (That is, the
underlying types could have been computed instead as limits in the category of types.)
-/
@[to_additive]
instance forget_preserves_limits : preserves_limits (forget CommMon) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, limits.comp_preserves_limit (forget₂ CommMon Mon) (forget Mon) } }

end CommMon
