/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.pullbacks

/-!
# Constructing equalizers from pullbacks and binary products.

If a category has pullbacks and binary products, then it has equalizers.

TODO: provide the dual result.
-/

noncomputable theory

universes v u

open category_theory category_theory.category

namespace category_theory.limits

variables {C : Type u} [category.{v} C] [has_binary_products C] [has_pullbacks C]

-- We hide the "implementation details" inside a namespace
namespace has_equalizers_of_pullbacks_and_binary_products

/-- Define the equalizing object -/
@[reducible]
def construct_equalizer (F : walking_parallel_pair ⥤ C) : C :=
pullback (prod.lift (𝟙 _) (F.map walking_parallel_pair_hom.left))
         (prod.lift (𝟙 _) (F.map walking_parallel_pair_hom.right))

/-- Define the equalizing morphism -/
abbreviation pullback_fst (F : walking_parallel_pair ⥤ C) :
  construct_equalizer F ⟶ F.obj walking_parallel_pair.zero :=
pullback.fst

lemma pullback_fst_eq_pullback_snd (F : walking_parallel_pair ⥤ C) :
  pullback_fst F = pullback.snd :=
by convert pullback.condition =≫ limits.prod.fst; simp

/-- Define the equalizing cone -/
@[reducible]
def equalizer_cone (F : walking_parallel_pair ⥤ C) : cone F :=
cone.of_fork
  (fork.of_ι (pullback_fst F)
    (begin
      conv_rhs { rw pullback_fst_eq_pullback_snd, },
      convert pullback.condition =≫ limits.prod.snd using 1; simp
     end))

/-- Show the equalizing cone is a limit -/
def equalizer_cone_is_limit (F : walking_parallel_pair ⥤ C) : is_limit (equalizer_cone F) :=
{ lift :=
  begin
    intro c, apply pullback.lift (c.π.app _) (c.π.app _),
    apply limit.hom_ext,
    rintro (_ | _); simp
  end,
  fac' := by rintros c (_ | _); simp,
  uniq' :=
  begin
    intros c _ J,
    have J0 := J walking_parallel_pair.zero, simp at J0,
    apply pullback.hom_ext,
    { rwa limit.lift_π },
    { erw [limit.lift_π, ← J0, pullback_fst_eq_pullback_snd] }
  end }

end has_equalizers_of_pullbacks_and_binary_products

open has_equalizers_of_pullbacks_and_binary_products
/-- Any category with pullbacks and binary products, has equalizers. -/
-- This is not an instance, as it is not always how one wants to construct equalizers!
lemma has_equalizers_of_pullbacks_and_binary_products :
  has_equalizers C :=
{ has_limit := λ F, has_limit.mk
  { cone := equalizer_cone F,
    is_limit := equalizer_cone_is_limit F } }

end category_theory.limits
