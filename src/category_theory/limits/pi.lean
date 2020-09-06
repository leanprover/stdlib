/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.pi.basic
import category_theory.limits.limits

/-!
# Limits in the category of indexed families of objects.

Given a functor `F : J ⥤ Π i, C i` into a category of indexed families,
1. we can assemble a collection of cones over `F ⋙ pi.eval C i` into a cone over `F`
2. if all those cones are limit cones, the assembled cone is a limit cone, and
3. if we have chosen limits for each of `F ⋙ pi.eval C i`, we can produce a
   `has_limit F` instance
-/

open category_theory
open category_theory.limits

namespace category_theory.pi

universes v₁ v₂ u₁ u₂

variables {I : Type v₁} {C : I → Type u₁} [Π i, category.{v₁} (C i)]
variables {J : Type v₁} [small_category J]
variables {F : J ⥤ Π i, C i}

/--
A cone over `F : J ⥤ Π i, C i` has as its components cones over each of the `F ⋙ pi.eval C i`.
-/
def cone_comp_eval (c : cone F) (i : I) : cone (F ⋙ pi.eval C i) :=
{ X := c.X i,
  π :=
  { app := λ j, c.π.app j i,
    naturality' := λ j j' f, congr_fun (c.π.naturality f) i, } }

/--
A cocone over `F : J ⥤ Π i, C i` has as its components cocones over each of the `F ⋙ pi.eval C i`.
-/
def cocone_comp_eval (c : cocone F) (i : I) : cocone (F ⋙ pi.eval C i) :=
{ X := c.X i,
  ι :=
  { app := λ j, c.ι.app j i,
    naturality' := λ j j' f, congr_fun (c.ι.naturality f) i, } }

/--
Given a family of cones over the `F ⋙ pi.eval C i`, we can assemble these together as a `cone F`.
-/
def cone_of_cone_comp_eval (c : Π i, cone (F ⋙ pi.eval C i)) : cone F :=
{ X := λ i, (c i).X,
  π :=
  { app := λ j i, (c i).π.app j,
    naturality' := λ j j' f, by { ext i, exact (c i).π.naturality f, } } }

/--
Given a family of cocones over the `F ⋙ pi.eval C i`, we can assemble these together as a `cocone F`.
-/
def cocone_of_cocone_comp_eval (c : Π i, cocone (F ⋙ pi.eval C i)) : cocone F :=
{ X := λ i, (c i).X,
  ι :=
  { app := λ j i, (c i).ι.app j,
    naturality' := λ j j' f, by { ext i, exact (c i).ι.naturality f, } } }

/--
Given a family of limit cones over the `F ⋙ pi.eval C i`,
assembling them together as a `cone F` produces a limit cone.
-/
def cone_of_cone_eval_is_limit {c : Π i, cone (F ⋙ pi.eval C i)} (P : Π i, is_limit (c i)) :
  is_limit (cone_of_cone_comp_eval c) :=
{ lift := λ s i, (P i).lift (cone_comp_eval s i),
  fac' := λ s j,
  begin
    ext i,
    exact (P i).fac (cone_comp_eval s i) j,
  end,
  uniq' := λ s m w,
  begin
    ext i,
    exact (P i).uniq (cone_comp_eval s i) (m i) (λ j, congr_fun (w j) i)
  end }

/--
Given a family of colimit cocones over the `F ⋙ pi.eval C i`,
assembling them together as a `cocone F` produces a colimit cocone.
-/
def cocone_of_cocone_eval_is_colimit {c : Π i, cocone (F ⋙ pi.eval C i)} (P : Π i, is_colimit (c i)) :
  is_colimit (cocone_of_cocone_comp_eval c) :=
{ desc := λ s i, (P i).desc (cocone_comp_eval s i),
  fac' := λ s j,
  begin
    ext i,
    exact (P i).fac (cocone_comp_eval s i) j,
  end,
  uniq' := λ s m w,
  begin
    ext i,
    exact (P i).uniq (cocone_comp_eval s i) (m i) (λ j, congr_fun (w j) i)
  end }

section

variables [∀ i, has_limit (F ⋙ pi.eval C i)]

/--
If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and we have chosen limits for each of the `F ⋙ pi.eval C i`,
there is a canonical choice of chosen limit for `F`.
-/
def has_limit_of_has_limit_comp_eval : has_limit F :=
{ cone := cone_of_cone_comp_eval (λ i, limit.cone _),
  is_limit := cone_of_cone_eval_is_limit (λ i, limit.is_limit _), }

end

section

variables [∀ i, has_colimit (F ⋙ pi.eval C i)]

/--
If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and we have chosen colimits for each of the `F ⋙ pi.eval C i`,
there is a canonical choice of chosen colimit for `F`.
-/
def has_colimit_of_has_colimit_comp_eval : has_colimit F :=
{ cocone := cocone_of_cocone_comp_eval (λ i, colimit.cocone _),
  is_colimit := cocone_of_cocone_eval_is_colimit (λ i, colimit.is_colimit _), }

end

/-!
As an example, we can use this to construct particular shapes of limits
in a category of indexed families.

With the addition of
`import category_theory.limits.shapes.types`
we can use:
```
local attribute [instance] has_limit_of_has_limit_comp_eval
example : has_binary_products (I → Type v₁) := ⟨by apply_instance⟩
```
-/

end category_theory.pi
