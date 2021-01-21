/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import category_theory.over
import category_theory.limits.creates

/-!
# Limits and colimits in the over and under categories

Show that the forgetful functor `forget X : over X ⥤ C` creates colimits, and hence `over X` has
any colimits that `C` has (as well as the dual that `forget X : under X ⟶ C` creates limits).

Note that the folder `category_theory.limits.shapes.constructions.over` further shows that
`forget X : over X ⥤ C` creates connected limits (so `over X` has connected limits), and that
`over X` has `J`-indexed products if `C` has `J`-indexed wide pullbacks.

TODO: If `C` has binary products, then `forget X : over X ⥤ C` has a right adjoint.
-/
noncomputable theory

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

open category_theory category_theory.limits

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C]
variable {X : C}

namespace category_theory.functor

/-- We can interpret a functor `F` into the category of arrows with codomain `X` as a cocone over
    the diagram given by the domains of the arrows in the image of `F` such that the apex of the
    cocone is `X`. -/
@[simps] def to_cocone (F : J ⥤ over X) : cocone (F ⋙ over.forget X) :=
{ X := X,
  ι := { app := λ j, (F.obj j).hom } }

/-- We can interpret a functor `F` into the category of arrows with domain `X` as a cone over the
    diagram given by the codomains of the arrows in the image of `F` such that the apex of the cone
    is `X`. -/
@[simps] def to_cone (F : J ⥤ under X) : cone (F ⋙ under.forget X) :=
{ X := X,
  π := { app := λ j, (F.obj j).hom } }

end category_theory.functor

namespace category_theory.over

instance : reflects_colimits (forget X) :=
{ reflects_colimits_of_shape := λ J 𝒥₁,
  { reflects_colimit := λ F,
    { reflects := λ c t, by exactI
      { desc := λ s, hom_mk (t.desc ((forget X).map_cocone s)) $ t.hom_ext $
                         λ j, by { rw t.fac_assoc, exact ((s.ι.app j).w).trans (c.ι.app j).w.symm },
        fac' := λ s j, over_morphism.ext (t.fac _ j),
        uniq' :=
          λ s m w, over_morphism.ext $
          t.uniq ((forget X).map_cocone s) m.left (λ j, congr_arg comma_morphism.left (w j)) } } } }

instance : creates_colimits (forget X) :=
{ creates_colimits_of_shape := λ J 𝒥₁, by exactI
  { creates_colimit := λ K,
    { lifts := λ c t,
      { lifted_cocone :=
        { X := mk (t.desc K.to_cocone),
          ι :=
          { app := λ j, hom_mk (c.ι.app j),
            naturality' := λ j j' f, over_morphism.ext (c.ι.naturality f) } },
        valid_lift := cocones.ext (iso.refl _) (λ j, category.comp_id _) } } } }

instance has_colimit {F : J ⥤ over X} [has_colimit (F ⋙ forget X)] : has_colimit F :=
has_colimit_of_created _ (forget X)

instance has_colimits_of_shape [has_colimits_of_shape J C] :
  has_colimits_of_shape J (over X) :=
{ has_colimit := λ F, by apply_instance }

instance has_colimits [has_colimits C] : has_colimits (over X) :=
{ has_colimits_of_shape := λ J 𝒥, by apply_instance }

-- We can automatically infer that the forgetful functor preserves colimits
example [has_colimits C] : preserves_colimits (forget X) := infer_instance

end category_theory.over

namespace category_theory.under

instance : reflects_limits (forget X) :=
{ reflects_limits_of_shape := λ J 𝒥₁,
  { reflects_limit := λ F,
    { reflects := λ c t, by exactI
      { lift := λ s, hom_mk (t.lift ((forget X).map_cone s)) $ t.hom_ext $ λ j,
                    by { rw [category.assoc, t.fac], exact (s.π.app j).w.symm.trans (c.π.app j).w },
        fac' := λ s j, under_morphism.ext (t.fac _ j),
        uniq' :=
          λ s m w, under_morphism.ext $
          t.uniq ((forget X).map_cone s) m.right (λ j, congr_arg comma_morphism.right (w j)) } } } }

instance : creates_limits (forget X) :=
{ creates_limits_of_shape := λ J 𝒥₁, by exactI
  { creates_limit := λ K,
    { lifts := λ c t,
      { lifted_cone :=
        { X := mk (t.lift K.to_cone),
          π :=
          { app := λ j, hom_mk (c.π.app j),
            naturality' := λ j j' f, under_morphism.ext (c.π.naturality f) } },
        valid_lift := cones.ext (iso.refl _) (λ j, (category.id_comp _).symm) } } } }

instance has_limit {F : J ⥤ under X} [has_limit (F ⋙ forget X)] : has_limit F :=
has_limit_of_created F (forget X)

instance has_limits_of_shape [has_limits_of_shape J C] :
  has_limits_of_shape J (under X) :=
{ has_limit := λ F, by apply_instance }

instance has_limits [has_limits C] : has_limits (under X) :=
{ has_limits_of_shape := λ J 𝒥, by resetI; apply_instance }

-- We can automatically infer that the forgetful functor preserves limits
example [has_limits C] : preserves_limits (forget X) := infer_instance

end category_theory.under
