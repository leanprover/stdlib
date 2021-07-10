/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.basic
import category_theory.linear
import category_theory.preadditive.additive_functor
import category_theory.preadditive.opposite

/-!
# The Yoneda embedding for `R`-linear categories

The Yoneda embedding for `R`-linear categories `C`,
sends an object `X : C` to the `Module R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `Module.of R (unop Y ⟶ X)`.

TODO: `linear_yoneda R C` is `R`-linear.
TODO: In fact, `linear_yoneda` itself is additive and `R`-linear.
-/

namespace category_theory

open opposite

variables (R : Type*) [ring R] (C : Type*) [category C] [preadditive C] [linear R C]

/-- The Yoneda embedding for `R`-linear categories `C`,
sending an object `X : C` to the `Module R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `Module.of R (unop Y ⟶ X)`. -/
@[simps]
def linear_yoneda : C ⥤ Cᵒᵖ ⥤ Module R :=
{ obj := λ X,
  { obj := λ Y, Module.of R (unop Y ⟶ X),
    map := λ Y Y' f, linear.left_comp R _ f.unop,
    map_comp' := λ _ _ _ f g, begin ext, dsimp, erw [category.assoc] end,
    map_id' := λ Y, begin ext, dsimp, erw [category.id_comp] end },
  map := λ X X' f, { app := λ Y, linear.right_comp R _ f } }.

instance linear_yoneda_obj_additive (X : C) : ((linear_yoneda R C).obj X).additive := {}

end category_theory
