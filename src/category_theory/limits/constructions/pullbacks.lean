/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.pullbacks

/-!
# Constructing pullbacks from binary products and equalizers

If a category as binary products and equalizers, then it has pullbacks.
Also, if a category has binary coproducts and coequalizers, then it has pushouts
-/

universes v u

open category_theory

namespace category_theory.limits

/-- If the product `X ⨯ Y` and the equalizer of `π₁ ≫ f` and `π₂ ≫ g` exist, then the
    pullback of `f` and `g` exists: It is given by composing the equalizer with the projections. -/
lemma has_limit_cospan_of_has_limit_pair_of_has_limit_parallel_pair
  {C : Type u} [𝒞 : category.{v} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_limit (pair X Y)]
  [has_limit (parallel_pair (prod.fst ≫ f) (prod.snd ≫ g))] : has_limit (cospan f g) :=
let π₁ : X ⨯ Y ⟶ X := prod.fst, π₂ : X ⨯ Y ⟶ Y := prod.snd, e := equalizer.ι (π₁ ≫ f) (π₂ ≫ g) in
has_limit.mk
{ cone := pullback_cone.mk (e ≫ π₁) (e ≫ π₂) $ by simp only [category.assoc, equalizer.condition],
  is_limit := pullback_cone.is_limit.mk _
    (λ s, equalizer.lift (prod.lift (s.π.app walking_cospan.left)
      (s.π.app walking_cospan.right)) $ by
        rw [←category.assoc, limit.lift_π, ←category.assoc, limit.lift_π];
        exact pullback_cone.condition _)
    (by simp) (by simp) $ λ s m h₁ h₂, by { ext,
      { simpa using h₁ },
      { simpa using h₂ } } }

section

local attribute [instance] has_limit_cospan_of_has_limit_pair_of_has_limit_parallel_pair

/-- If a category has all binary products and all equalizers, then it also has all pullbacks.
    As usual, this is not an instance, since there may be a more direct way to construct
    pullbacks. -/
lemma has_pullbacks_of_has_binary_products_of_has_equalizers
  (C : Type u) [𝒞 : category.{v} C] [has_binary_products C] [has_equalizers C] :
  has_pullbacks C :=
{ has_limit := λ F, has_limit_of_iso (diagram_iso_cospan F).symm }

end

/-- If the coproduct `Y ⨿ Z` and the coequalizer of `f ≫ ι₁` and `g ≫ ι₂` exist, then the
    pushout of `f` and `g` exists: It is given by composing the inclusions with the coequalizer. -/
lemma has_colimit_span_of_has_colimit_pair_of_has_colimit_parallel_pair
  {C : Type u} [𝒞 : category.{v} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [has_colimit (pair Y Z)]
  [has_colimit (parallel_pair (f ≫ coprod.inl) (g ≫ coprod.inr))] : has_colimit (span f g) :=
let ι₁ : Y ⟶ Y ⨿ Z := coprod.inl, ι₂ : Z ⟶ Y ⨿ Z := coprod.inr,
  c := coequalizer.π (f ≫ ι₁) (g ≫ ι₂) in
has_colimit.mk
{ cocone := pushout_cocone.mk (ι₁ ≫ c) (ι₂ ≫ c) $
    by rw [←category.assoc, ←category.assoc, coequalizer.condition],
  is_colimit := pushout_cocone.is_colimit.mk _
    (λ s, coequalizer.desc (coprod.desc (s.ι.app walking_span.left)
      (s.ι.app walking_span.right)) $ by
        rw [category.assoc, colimit.ι_desc, category.assoc, colimit.ι_desc];
        exact pushout_cocone.condition _)
    (by simp) (by simp) $ λ s m h₁ h₂, by { ext,
      { simpa using h₁ },
      { simpa using h₂ } } }

section

local attribute [instance] has_colimit_span_of_has_colimit_pair_of_has_colimit_parallel_pair

/-- If a category has all binary coproducts and all coequalizers, then it also has all pushouts.
    As usual, this is not an instance, since there may be a more direct way to construct
    pushouts. -/
lemma has_pushouts_of_has_binary_coproducts_of_has_coequalizers
  (C : Type u) [𝒞 : category.{v} C] [has_binary_coproducts C] [has_coequalizers C] :
  has_pushouts C :=
has_pushouts_of_has_colimit_span C

end

end category_theory.limits
