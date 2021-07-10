/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz
-/
import category_theory.limits.preserves.basic
import category_theory.limits.types
import category_theory.limits.shapes.wide_pullbacks
import tactic.elementwise

/-!
# Facts about (co)limits of functors into concrete categories
-/

universes w v u

open category_theory

namespace category_theory.limits

attribute [elementwise] cone.w limit.lift_π limit.w cocone.w colimit.ι_desc colimit.w

local attribute [instance] concrete_category.has_coe_to_fun concrete_category.has_coe_to_sort

section limits

variables {C : Type u} [category.{v} C] [concrete_category.{v} C]
  {J : Type v} [small_category J] (F : J ⥤ C) [preserves_limit F (forget C)]

lemma concrete.to_product_injective_of_is_limit {D : cone F} (hD : is_limit D) :
  function.injective (λ (x : D.X) (j : J), D.π.app j x) :=
begin
  let E := (forget C).map_cone D,
  let hE : is_limit E := is_limit_of_preserves _ hD,
  let G := types.limit_cone (F ⋙ forget C),
  let hG := types.limit_cone_is_limit (F ⋙ forget C),
  let T : E.X ≅ G.X := hE.cone_point_unique_up_to_iso hG,
  change function.injective (T.hom ≫ (λ x j, G.π.app j x)),
  have h : function.injective T.hom,
  { intros a b h,
    suffices : T.inv (T.hom a) = T.inv (T.hom b), by simpa,
    rw h },
  suffices : function.injective (λ (x : G.X) j, G.π.app j x),
    by exact this.comp h,
  apply subtype.ext,
end

lemma concrete.is_limit_ext {D : cone F} (hD : is_limit D) (x y : D.X) :
  (∀ j, D.π.app j x = D.π.app j y) → x = y :=
λ h, concrete.to_product_injective_of_is_limit _ hD (funext h)

lemma concrete.limit_ext [has_limit F] (x y : limit F) :
  (∀ j, limit.π F j x = limit.π F j y) → x = y :=
concrete.is_limit_ext F (limit.is_limit _) _ _

section wide_pullback

open wide_pullback
open wide_pullback_shape

lemma concrete.wide_pullback_ext {B : C} {ι : Type*} {X : ι → C} (f : Π j : ι, X j ⟶ B)
  [has_wide_pullback B X f] [preserves_limit (wide_cospan B X f) (forget C)]
  (x y : wide_pullback B X f) (h₀ : base f x = base f y)
  (h : ∀ j, π f j x = π f j y) : x = y :=
begin
  apply concrete.limit_ext,
  rintro (_|j),
  { exact h₀ },
  { apply h }
end

lemma concrete.wide_pullback_ext' {B : C} {ι : Type*} [nonempty ι]
  {X : ι → C} (f : Π j : ι, X j ⟶ B) [has_wide_pullback B X f]
  [preserves_limit (wide_cospan B X f) (forget C)]
  (x y : wide_pullback B X f) (h : ∀ j, π f j x = π f j y) : x = y :=
begin
  apply concrete.wide_pullback_ext _ _ _ _ h,
  inhabit ι,
  simp only [← π_arrow f (arbitrary _), comp_apply, h],
end

end wide_pullback

-- TODO: Add analogous lemmas about products and equalizers.

end limits

section colimits

variables {C : Type u} [category.{v} C] [concrete_category.{v} C]
  {J : Type v} [small_category J] (F : J ⥤ C) [preserves_colimit F (forget C)]

lemma concrete.from_union_surjective_of_is_colimit {D : cocone F} (hD : is_colimit D) :
  let ff : (Σ (j : J), F.obj j) → D.X := λ a, D.ι.app a.1 a.2 in function.surjective ff :=
begin
  intro ff,
  let E := (forget C).map_cocone D,
  let hE : is_colimit E := is_colimit_of_preserves _ hD,
  let G := types.colimit_cocone (F ⋙ forget C),
  let hG := types.colimit_cocone_is_colimit (F ⋙ forget C),
  let T : E ≅ G := hE.unique_up_to_iso hG,
  let TX : E.X ≅ G.X := (cocones.forget _).map_iso T,
  suffices : function.surjective (TX.hom ∘ ff),
  { intro a,
    obtain ⟨b, hb⟩ := this (TX.hom a),
    refine ⟨b, _⟩,
    apply_fun TX.inv at hb,
    change (TX.hom ≫ TX.inv) (ff b) = (TX.hom ≫ TX.inv) _ at hb,
    simpa only [TX.hom_inv_id] using hb },
  have : TX.hom ∘ ff = λ a, G.ι.app a.1 a.2,
  { ext a,
    change (E.ι.app a.1 ≫ hE.desc G) a.2 = _,
    rw hE.fac },
  rw this,
  rintro ⟨⟨j,a⟩⟩,
  exact ⟨⟨j,a⟩,rfl⟩,
end

lemma concrete.is_colimit_exists_rep {D : cocone F} (hD : is_colimit D) (x : D.X) :
  ∃ (j : J) (y : F.obj j), D.ι.app j y = x :=
begin
  obtain ⟨a, rfl⟩ := concrete.from_union_surjective_of_is_colimit F hD x,
  exact ⟨a.1, a.2, rfl⟩,
end

lemma concrete.colimit_exists_rep [has_colimit F] (x : colimit F) :
  ∃ (j : J) (y : F.obj j), colimit.ι F j y = x :=
concrete.is_colimit_exists_rep F (colimit.is_colimit _) x

section wide_pushout

open wide_pushout
open wide_pushout_shape

lemma concrete.wide_pushout_exists_rep {B : C} {α : Type*} {X : α → C} (f : Π j : α, B ⟶ X j)
  [has_wide_pushout B X f] [preserves_colimit (wide_span B X f) (forget C)]
  (x : wide_pushout B X f) : (∃ y : B, head f y = x) ∨ (∃ (i : α) (y : X i), ι f i y = x) :=
begin
  obtain ⟨_ | j, y, rfl⟩ := concrete.colimit_exists_rep _ x,
  { use y },
  { right,
    use [j,y] }
end

lemma concrete.wide_pushout_exists_rep' {B : C} {α : Type*} [nonempty α] {X : α → C}
  (f : Π j : α, B ⟶ X j) [has_wide_pushout B X f]
  [preserves_colimit (wide_span B X f) (forget C)] (x : wide_pushout B X f) :
  ∃ (i : α) (y : X i), ι f i y = x :=
begin
  rcases concrete.wide_pushout_exists_rep f x with ⟨y, rfl⟩ | ⟨i, y, rfl⟩,
  { inhabit α,
    use [arbitrary _, f _ y],
    simp only [← arrow_ι _ (arbitrary α), comp_apply] },
  { use [i,y] }
end

end wide_pushout

-- TODO: Add analogous lemmas about coproducts and coequalizers.

end colimits

end category_theory.limits
