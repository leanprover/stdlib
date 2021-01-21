/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import category_theory.over
import category_theory.limits.shapes.finite_products

/-!
# Products in the over category

Shows that products in the over category can be derived from wide pullbacks in the base category.
The main result is `over_product_of_wide_pullback`, which says that if `C` has `J`-indexed wide
pullbacks, then `over B` has `J`-indexed products.
-/
universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

open category_theory category_theory.limits

variables {J : Type v}
variables {C : Type u} [category.{v} C]
variable {X : C}

namespace category_theory.over

namespace construct_products

/--
(Implementation)
Given a product diagram in `C/B`, construct the corresponding wide pullback diagram
in `C`.
-/
@[reducible]
def wide_pullback_diagram_of_diagram_over (B : C) {J : Type v} (F : discrete J ⥤ over B) :
  wide_pullback_shape J ⥤ C :=
wide_pullback_shape.wide_cospan B (λ j, (F.obj j).left) (λ j, (F.obj j).hom)

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def cones_equiv_inverse_obj (B : C) {J : Type v} (F : discrete J ⥤ over B) (c : cone F) :
  cone (wide_pullback_diagram_of_diagram_over B F) :=
{ X := c.X.left,
  π :=
  { app := λ X, option.cases_on X c.X.hom (λ (j : J), (c.π.app j).left),
  -- `tidy` can do this using `case_bash`, but let's try to be a good `-T50000` citizen:
    naturality' := λ X Y f,
    begin
      dsimp, cases X; cases Y; cases f,
      { rw [category.id_comp, category.comp_id], },
      { rw [over.w, category.id_comp], },
      { rw [category.id_comp, category.comp_id], },
    end } }

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def cones_equiv_inverse (B : C) {J : Type v} (F : discrete J ⥤ over B) :
  cone F ⥤ cone (wide_pullback_diagram_of_diagram_over B F) :=
{ obj := cones_equiv_inverse_obj B F,
  map := λ c₁ c₂ f,
  { hom := f.hom.left,
    w' := λ j,
    begin
      cases j,
      { simp },
      { dsimp,
        rw ← f.w j,
        refl }
    end } }

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def cones_equiv_functor (B : C) {J : Type v} (F : discrete J ⥤ over B) :
  cone (wide_pullback_diagram_of_diagram_over B F) ⥤ cone F :=
{ obj := λ c,
  { X := over.mk (c.π.app none),
    π :=
    { app := λ j, over.hom_mk (c.π.app (some j))
                    (by apply c.w (wide_pullback_shape.hom.term j)) } },
  map := λ c₁ c₂ f,
  { hom := over.hom_mk f.hom } }

local attribute [tidy] tactic.case_bash

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp]
def cones_equiv_unit_iso (B : C) (F : discrete J ⥤ over B) :
  𝟭 (cone (wide_pullback_diagram_of_diagram_over B F)) ≅
    cones_equiv_functor B F ⋙ cones_equiv_inverse B F :=
nat_iso.of_components (λ _, cones.ext {hom := 𝟙 _, inv := 𝟙 _} (by tidy)) (by tidy)

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp]
def cones_equiv_counit_iso (B : C) (F : discrete J ⥤ over B) :
  cones_equiv_inverse B F ⋙ cones_equiv_functor B F ≅ 𝟭 (cone F) :=
nat_iso.of_components
  (λ _, cones.ext {hom := over.hom_mk (𝟙 _), inv := over.hom_mk (𝟙 _)} (by tidy)) (by tidy)

-- TODO: Can we add `. obviously` to the second arguments of `nat_iso.of_components` and
--       `cones.ext`?
/--
(Impl) Establish an equivalence between the category of cones for `F` and for the "grown" `F`.
-/
@[simps]
def cones_equiv (B : C) (F : discrete J ⥤ over B) :
  cone (wide_pullback_diagram_of_diagram_over B F) ≌ cone F :=
{ functor := cones_equiv_functor B F,
  inverse := cones_equiv_inverse B F,
  unit_iso := cones_equiv_unit_iso B F,
  counit_iso := cones_equiv_counit_iso B F, }

/-- Use the above equivalence to prove we have a limit. -/
lemma has_over_limit_discrete_of_wide_pullback_limit {B : C} (F : discrete J ⥤ over B)
  [has_limit (wide_pullback_diagram_of_diagram_over B F)] :
  has_limit F :=
has_limit.mk
{ cone := _,
  is_limit := is_limit.of_right_adjoint
    (cones_equiv B F).functor (limit.is_limit (wide_pullback_diagram_of_diagram_over B F)) }

/-- Given a wide pullback in `C`, construct a product in `C/B`. -/
lemma over_product_of_wide_pullback [has_limits_of_shape (wide_pullback_shape J) C] {B : C} :
  has_limits_of_shape (discrete J) (over B) :=
{ has_limit := λ F, has_over_limit_discrete_of_wide_pullback_limit F }

/-- Given a pullback in `C`, construct a binary product in `C/B`. -/
lemma over_binary_product_of_pullback [has_pullbacks C] {B : C} :
  has_binary_products (over B) :=
over_product_of_wide_pullback

/-- Given all wide pullbacks in `C`, construct products in `C/B`. -/
lemma over_products_of_wide_pullbacks [has_wide_pullbacks C] {B : C} :
  has_products (over B) :=
λ J, over_product_of_wide_pullback

/-- Given all finite wide pullbacks in `C`, construct finite products in `C/B`. -/
lemma over_finite_products_of_finite_wide_pullbacks [has_finite_wide_pullbacks C] {B : C} :
  has_finite_products (over B) :=
λ J 𝒥₁ 𝒥₂, by exactI over_product_of_wide_pullback

end construct_products

/--
Construct terminal object in the over category. This isn't an instance as it's not typically the
way we want to define terminal objects.
(For instance, this gives a terminal object which is different from the generic one given by
`over_product_of_wide_pullback` above.)
-/
lemma over_has_terminal (B : C) : has_terminal (over B) :=
{ has_limit := λ F, has_limit.mk
  { cone :=
    { X := over.mk (𝟙 _),
      π := { app := λ p, pempty.elim p } },
    is_limit :=
      { lift := λ s, over.hom_mk _,
        fac' := λ _ j, j.elim,
        uniq' := λ s m _,
          begin
            ext,
            rw over.hom_mk_left,
            have := m.w,
            dsimp at this,
            rwa [category.comp_id, category.comp_id] at this
          end } } }

end category_theory.over
