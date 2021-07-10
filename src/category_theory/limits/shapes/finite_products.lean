/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.terminal

universes v u

open category_theory
namespace category_theory.limits

variables (C : Type u) [category.{v} C]

/--
A category has finite products if there is a chosen limit for every diagram
with shape `discrete J`, where we have `[decidable_eq J]` and `[fintype J]`.
-/
-- We can't simply make this an abbreviation, as we do with other `has_Xs` limits typeclasses,
-- because of https://github.com/leanprover-community/lean/issues/429
class has_finite_products : Prop :=
(out (J : Type v) [decidable_eq J] [fintype J] : has_limits_of_shape (discrete J) C)

instance has_limits_of_shape_discrete
  (J : Type v) [fintype J] [has_finite_products C] :
  has_limits_of_shape (discrete J) C :=
by { haveI := @has_finite_products.out C _ _ J (classical.dec_eq _), apply_instance }

/-- If `C` has finite limits then it has finite products. -/
@[priority 10]
instance has_finite_products_of_has_finite_limits [has_finite_limits C] : has_finite_products C :=
⟨λ J 𝒥₁ 𝒥₂, by { resetI, apply_instance }⟩

/--
If a category has all products then in particular it has finite products.
-/
lemma has_finite_products_of_has_products [has_products C] : has_finite_products C :=
⟨by apply_instance⟩

/--
A category has finite coproducts if there is a chosen colimit for every diagram
with shape `discrete J`, where we have `[decidable_eq J]` and `[fintype J]`.
-/
class has_finite_coproducts : Prop :=
(out (J : Type v) [decidable_eq J] [fintype J] : has_colimits_of_shape (discrete J) C)

attribute [class] has_finite_coproducts

instance has_colimits_of_shape_discrete
  (J : Type v) [fintype J] [has_finite_coproducts C] :
  has_colimits_of_shape (discrete J) C :=
by { haveI := @has_finite_coproducts.out C _ _ J (classical.dec_eq _), apply_instance }

/-- If `C` has finite colimits then it has finite coproducts. -/
@[priority 10]
instance has_finite_coproducts_of_has_finite_colimits [has_finite_colimits C] :
  has_finite_coproducts C :=
⟨λ J 𝒥₁ 𝒥₂, by { resetI, apply_instance }⟩

/--
If a category has all coproducts then in particular it has finite coproducts.
-/
lemma has_finite_coproducts_of_has_coproducts [has_coproducts C] : has_finite_coproducts C :=
⟨by apply_instance⟩

end category_theory.limits
