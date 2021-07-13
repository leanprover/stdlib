/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.basic
import algebra.category.Group.limits
import algebra.direct_limit

/-!
# The category of R-modules has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

open category_theory
open category_theory.limits

universes u v

noncomputable theory

namespace Module

variables {R : Type u} [ring R]
variables {J : Type v} [small_category J]

instance add_comm_group_obj (F : J ⥤ Module.{v} R) (j) :
  add_comm_group ((F ⋙ forget (Module R)).obj j) :=
by { change add_comm_group (F.obj j), apply_instance }

instance module_obj (F : J ⥤ Module.{v} R) (j) :
  module R ((F ⋙ forget (Module R)).obj j) :=
by { change module R (F.obj j), apply_instance }

/--
The flat sections of a functor into `Module R` form a submodule of all sections.
-/
def sections_submodule (F : J ⥤ Module R) :
  submodule R (Π j, F.obj j) :=
{ carrier := (F ⋙ forget (Module R)).sections,
  smul_mem' := λ r s sh j j' f,
  begin
    simp only [forget_map_eq_coe, functor.comp_map, pi.smul_apply, linear_map.map_smul],
    dsimp [functor.sections] at sh,
    rw sh f,
  end,
  ..(AddGroup.sections_add_subgroup
          (F ⋙ forget₂ (Module R) AddCommGroup.{v} ⋙ forget₂ AddCommGroup AddGroup.{v})) }

-- Adding the following instance speeds up `limit_module` noticeably,
-- by preventing a bad unfold of `limit_add_comm_group`.
instance limit_add_comm_monoid (F : J ⥤ Module R) :
  add_comm_monoid (types.limit_cone (F ⋙ forget (Module.{v} R))).X :=
show add_comm_monoid (sections_submodule F), by apply_instance

instance limit_add_comm_group (F : J ⥤ Module R) :
  add_comm_group (types.limit_cone (F ⋙ forget (Module.{v} R))).X :=
show add_comm_group (sections_submodule F), by apply_instance

instance limit_module (F : J ⥤ Module R) :
  module R (types.limit_cone (F ⋙ forget (Module.{v} R))).X :=
show module R (sections_submodule F), by apply_instance

/-- `limit.π (F ⋙ forget Ring) j` as a `ring_hom`. -/
def limit_π_linear_map (F : J ⥤ Module R) (j) :
  (types.limit_cone (F ⋙ forget (Module.{v} R))).X →ₗ[R] (F ⋙ forget (Module R)).obj j :=
{ to_fun := (types.limit_cone (F ⋙ forget (Module R))).π.app j,
  map_smul' := λ x y, rfl,
  map_add' := λ x y, rfl }

namespace has_limits
-- The next two definitions are used in the construction of `has_limits (Module R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `Module R`.
(Internal use only; use the limits API.)
-/
def limit_cone (F : J ⥤ Module R) : cone F :=
{ X := Module.of R (types.limit_cone (F ⋙ forget _)).X,
  π :=
  { app := limit_π_linear_map F,
    naturality' := λ j j' f,
      linear_map.coe_injective ((types.limit_cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `Module R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_cone_is_limit (F : J ⥤ Module R) : is_limit (limit_cone F) :=
begin
  refine is_limit.of_faithful
    (forget (Module R)) (types.limit_cone_is_limit _)
    (λ s, { map_zero' := _, .. }) (λ s, rfl); tidy
end

end has_limits

open has_limits

/-- The category of R-modules has all limits. -/
@[irreducible]
instance has_limits : has_limits (Module.{v} R) :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk
    { cone     := limit_cone F,
      is_limit := limit_cone_is_limit F } } }

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_AddCommGroup_preserves_limits_aux (F : J ⥤ Module R) :
  is_limit ((forget₂ (Module R) AddCommGroup).map_cone (limit_cone F)) :=
AddCommGroup.limit_cone_is_limit (F ⋙ forget₂ (Module R) AddCommGroup)

/--
The forgetful functor from R-modules to abelian groups preserves all limits.
-/
instance forget₂_AddCommGroup_preserves_limits :
  preserves_limits (forget₂ (Module R) AddCommGroup.{v}) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
      (limit_cone_is_limit F) (forget₂_AddCommGroup_preserves_limits_aux F) } }

/--
The forgetful functor from R-modules to types preserves all limits.
-/
instance forget_preserves_limits : preserves_limits (forget (Module R)) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
    (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget _)) } }

section direct_limit
open module

variables {ι : Type v}
variables [dec_ι : decidable_eq ι] [directed_order ι]
variables (G : ι → Type v)
variables [Π i, add_comm_group (G i)] [Π i, module R (G i)]
variables (f : Π i j, i ≤ j → G i →ₗ[R] G j) [module.directed_system G f]

/-- The diagram (in the sense of `category_theory`)
 of an unbundled `direct_limit` of modules. -/
@[simps]
def direct_limit_diagram : ι ⥤ Module R :=
{ obj := λ i, Module.of R (G i),
  map := λ i j hij, f i j hij.le,
  map_id' := λ i, by { ext x, apply module.directed_system.map_self },
  map_comp' := λ i j k hij hjk,
  begin
    ext x,
    symmetry,
    apply module.directed_system.map_map
  end }

variables [decidable_eq ι]

/-- The `cocone` on `direct_limit_diagram` corresponding to
the unbundled `direct_limit` of modules.

In `direct_limit_is_colimit` we show that it is a colimit cocone. -/
@[simps]
def direct_limit_cocone : cocone (direct_limit_diagram G f) :=
{ X := Module.of R $ direct_limit G f,
  ι := { app := module.direct_limit.of R ι G f,
         naturality' := λ i j hij, by { ext x, exact direct_limit.of_f } } }

/-- The unbundled `direct_limit` of modules is a colimit
in the sense of `category_theory`. -/
@[simps]
def direct_limit_is_colimit [nonempty ι] : is_colimit (direct_limit_cocone G f) :=
{ desc := λ s, direct_limit.lift R ι G f s.ι.app $ λ i j h x, by { rw [←s.w (hom_of_le h)], refl },
  fac' := λ s i,
  begin
    ext x,
    dsimp,
    exact direct_limit.lift_of s.ι.app _ x,
  end,
  uniq' := λ s m h,
  begin
    have : s.ι.app = λ i, linear_map.comp m (direct_limit.of R ι (λ i, G i) (λ i j H, f i j H) i),
    { funext i, rw ← h, refl },
    ext x,
    simp only [this],
    apply module.direct_limit.lift_unique
  end }

end direct_limit

end Module
