/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.preserves.limits

open category_theory category_theory.category

cache_file?

namespace category_theory.limits

universes v v₂ u -- morphism levels before object levels. See note [category_theory universes].

variables {C : Type u} [category.{v} C]

variables {J K : Type v} [small_category J] [category.{v₂} K]

@[simp, reassoc]
lemma limit.lift_π_app (H : J ⥤ K ⥤ C) [has_limit H] (c : cone H) (j : J) (k : K) :
  (limit.lift H c).app k ≫ (limit.π H j).app k = (c.π.app j).app k :=
congr_app (limit.lift_π c j) k

@[simp, reassoc]
lemma colimit.ι_desc_app (H : J ⥤ K ⥤ C) [has_colimit H] (c : cocone H) (j : J) (k : K) :
  (colimit.ι H j).app k ≫ (colimit.desc H c).app k = (c.ι.app j).app k :=
congr_app (colimit.ι_desc c j) k

/--
The evaluation functors jointly reflect limits: that is, to show a cone is a limit of `F`
it suffices to show that each evaluation cone is a limit. In other words, to prove a cone is
limiting you can show it's pointwise limiting.
-/
def evaluation_jointly_reflects_limits {F : J ⥤ K ⥤ C} (c : cone F)
  (t : Π (k : K), is_limit (((evaluation K C).obj k).map_cone c)) : is_limit c :=
{ lift := λ s,
  { app := λ k, (t k).lift ⟨s.X.obj k, whisker_right s.π ((evaluation K C).obj k)⟩,
    naturality' := λ X Y f, (t Y).hom_ext $ λ j,
    begin
      rw [assoc, (t Y).fac _ j],
      simpa using
        ((t X).fac_assoc ⟨s.X.obj X, whisker_right s.π ((evaluation K C).obj X)⟩ j _).symm,
    end },
  fac' := λ s j, nat_trans.ext _ _ $ funext $ λ k, (t k).fac _ j,
  uniq' := λ s m w, nat_trans.ext _ _ $ funext $ λ x, (t x).hom_ext $ λ j,
      (congr_app (w j) x).trans
        ((t x).fac ⟨s.X.obj _, whisker_right s.π ((evaluation K C).obj _)⟩ j).symm }

/--
Given a functor `F` and a collection of limit cones for each diagram `X ↦ F X k`, we can stitch
them together to give a cone for the diagram `F`.
`combined_is_limit` shows that the new cone is limiting, and `eval_combined` shows it is
(essentially) made up of the original cones.
-/
@[simps] def combine_cones (F : J ⥤ K ⥤ C) (c : Π (k : K), limit_cone (F.flip.obj k)) :
  cone F :=
{ X :=
  { obj := λ k, (c k).cone.X,
    map := λ k₁ k₂ f, (c k₂).is_limit.lift ⟨_, (c k₁).cone.π ≫ F.flip.map f⟩,
    map_id' := λ k, (c k).is_limit.hom_ext (λ j, by { dsimp, simp }),
    map_comp' := λ k₁ k₂ k₃ f₁ f₂, (c k₃).is_limit.hom_ext (λ j, by simp) },
  π :=
  { app := λ j, { app := λ k, (c k).cone.π.app j },
    naturality' := λ j₁ j₂ g, nat_trans.ext _ _ $ funext $ λ k, (c k).cone.π.naturality g } }

/-- The stitched together cones each project down to the original given cones (up to iso). -/
def evaluate_combined_cones (F : J ⥤ K ⥤ C) (c : Π (k : K), limit_cone (F.flip.obj k)) (k : K) :
  ((evaluation K C).obj k).map_cone (combine_cones F c) ≅ (c k).cone :=
cones.ext (iso.refl _) (by tidy)

/-- Stitching together limiting cones gives a limiting cone. -/
def combined_is_limit (F : J ⥤ K ⥤ C) (c : Π (k : K), limit_cone (F.flip.obj k)) :
  is_limit (combine_cones F c) :=
evaluation_jointly_reflects_limits _
  (λ k, (c k).is_limit.of_iso_limit (evaluate_combined_cones F c k).symm)

/--
The evaluation functors jointly reflect colimits: that is, to show a cocone is a colimit of `F`
it suffices to show that each evaluation cocone is a colimit. In other words, to prove a cocone is
colimiting you can show it's pointwise colimiting.
-/
def evaluation_jointly_reflects_colimits {F : J ⥤ K ⥤ C} (c : cocone F)
  (t : Π (k : K), is_colimit (((evaluation K C).obj k).map_cocone c)) : is_colimit c :=
{ desc := λ s,
  { app := λ k, (t k).desc ⟨s.X.obj k, whisker_right s.ι ((evaluation K C).obj k)⟩,
    naturality' := λ X Y f, (t X).hom_ext $ λ j,
    begin
      rw [(t X).fac_assoc _ j],
      erw ← (c.ι.app j).naturality_assoc f,
      erw (t Y).fac ⟨s.X.obj _, whisker_right s.ι _⟩ j,
      dsimp,
      simp,
    end },
  fac' := λ s j, nat_trans.ext _ _ $ funext $ λ k, (t k).fac _ j,
  uniq' := λ s m w, nat_trans.ext _ _ $ funext $ λ x, (t x).hom_ext $ λ j,
      (congr_app (w j) x).trans
        ((t x).fac ⟨s.X.obj _, whisker_right s.ι ((evaluation K C).obj _)⟩ j).symm }

/--
Given a functor `F` and a collection of colimit cocones for each diagram `X ↦ F X k`, we can stitch
them together to give a cocone for the diagram `F`.
`combined_is_colimit` shows that the new cocone is colimiting, and `eval_combined` shows it is
(essentially) made up of the original cocones.
-/
@[simps] def combine_cocones (F : J ⥤ K ⥤ C) (c : Π (k : K), colimit_cocone (F.flip.obj k)) :
  cocone F :=
{ X :=
  { obj := λ k, (c k).cocone.X,
    map := λ k₁ k₂ f, (c k₁).is_colimit.desc ⟨_, F.flip.map f ≫ (c k₂).cocone.ι⟩,
    map_id' := λ k, (c k).is_colimit.hom_ext (λ j, by { dsimp, simp }),
    map_comp' := λ k₁ k₂ k₃ f₁ f₂, (c k₁).is_colimit.hom_ext (λ j, by simp) },
  ι :=
  { app := λ j, { app := λ k, (c k).cocone.ι.app j },
    naturality' := λ j₁ j₂ g, nat_trans.ext _ _ $ funext $ λ k, (c k).cocone.ι.naturality g } }

/-- The stitched together cocones each project down to the original given cocones (up to iso). -/
def evaluate_combined_cocones
  (F : J ⥤ K ⥤ C) (c : Π (k : K), colimit_cocone (F.flip.obj k)) (k : K) :
  ((evaluation K C).obj k).map_cocone (combine_cocones F c) ≅ (c k).cocone :=
cocones.ext (iso.refl _) (by tidy)

/-- Stitching together colimiting cocones gives a colimiting cocone. -/
def combined_is_colimit (F : J ⥤ K ⥤ C) (c : Π (k : K), colimit_cocone (F.flip.obj k)) :
  is_colimit (combine_cocones F c) :=
evaluation_jointly_reflects_colimits _
  (λ k, (c k).is_colimit.of_iso_colimit (evaluate_combined_cocones F c k).symm)

noncomputable theory

instance functor_category_has_limits_of_shape
  [has_limits_of_shape J C] : has_limits_of_shape J (K ⥤ C) :=
{ has_limit := λ F, has_limit.mk
  { cone := combine_cones F (λ k, get_limit_cone _),
    is_limit := combined_is_limit _ _ } }

instance functor_category_has_colimits_of_shape
  [has_colimits_of_shape J C] : has_colimits_of_shape J (K ⥤ C) :=
{ has_colimit := λ F, has_colimit.mk
  { cocone := combine_cocones _ (λ k, get_colimit_cocone _),
    is_colimit := combined_is_colimit _ _ } }

instance functor_category_has_limits [has_limits C] : has_limits (K ⥤ C) := {}

instance functor_category_has_colimits [has_colimits C] : has_colimits (K ⥤ C) := {}

instance evaluation_preserves_limits_of_shape [has_limits_of_shape J C] (k : K) :
  preserves_limits_of_shape J ((evaluation K C).obj k) :=
{ preserves_limit :=
  λ F, preserves_limit_of_preserves_limit_cone (combined_is_limit _ _) $
    is_limit.of_iso_limit (limit.is_limit _)
      (evaluate_combined_cones F _ k).symm }

/--
If `F : J ⥤ K ⥤ C` is a functor into a functor category which has a limit,
then the evaluation of that limit at `k` is the limit of the evaluations of `F.obj j` at `k`.
-/
def limit_obj_iso_limit_comp_evaluation [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) (k : K) :
  (limit F).obj k ≅ limit (F ⋙ ((evaluation K C).obj k)) :=
preserves_limit_iso ((evaluation K C).obj k) F

@[simp, reassoc]
lemma limit_obj_iso_limit_comp_evaluation_hom_π
  [has_limits_of_shape J C] (F : J ⥤ (K ⥤ C)) (j : J) (k : K) :
  (limit_obj_iso_limit_comp_evaluation F k).hom ≫ limit.π (F ⋙ ((evaluation K C).obj k)) j =
    (limit.π F j).app k :=
begin
  dsimp [limit_obj_iso_limit_comp_evaluation],
  simp,
end

@[simp, reassoc]
lemma limit_obj_iso_limit_comp_evaluation_inv_π_app
  [has_limits_of_shape J C] (F : J ⥤ (K ⥤ C)) (j : J) (k : K):
  (limit_obj_iso_limit_comp_evaluation F k).inv ≫ (limit.π F j).app k =
    limit.π (F ⋙ ((evaluation K C).obj k)) j :=
begin
  dsimp [limit_obj_iso_limit_comp_evaluation],
  rw iso.inv_comp_eq,
  simp,
end

@[ext]
lemma limit_obj_ext {H : J ⥤ K ⥤ C} [has_limits_of_shape J C]
  {k : K} {W : C} {f g : W ⟶ (limit H).obj k}
  (w : ∀ j, f ≫ (limits.limit.π H j).app k = g ≫ (limits.limit.π H j).app k) : f = g :=
begin
  apply (cancel_mono (limit_obj_iso_limit_comp_evaluation H k).hom).1,
  ext,
  simpa using w j,
end

instance evaluation_preserves_colimits_of_shape [has_colimits_of_shape J C] (k : K) :
  preserves_colimits_of_shape J ((evaluation K C).obj k) :=
{ preserves_colimit :=
  λ F, preserves_colimit_of_preserves_colimit_cocone (combined_is_colimit _ _) $
    is_colimit.of_iso_colimit (colimit.is_colimit _)
      (evaluate_combined_cocones F _ k).symm }

/--
If `F : J ⥤ K ⥤ C` is a functor into a functor category which has a colimit,
then the evaluation of that colimit at `k` is the colimit of the evaluations of `F.obj j` at `k`.
-/
def colimit_obj_iso_colimit_comp_evaluation [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) (k : K) :
  (colimit F).obj k ≅ colimit (F ⋙ ((evaluation K C).obj k)) :=
preserves_colimit_iso ((evaluation K C).obj k) F

@[simp, reassoc]
lemma colimit_obj_iso_colimit_comp_evaluation_ι_inv
  [has_colimits_of_shape J C] (F : J ⥤ (K ⥤ C)) (j : J) (k : K) :
  colimit.ι (F ⋙ ((evaluation K C).obj k)) j ≫ (colimit_obj_iso_colimit_comp_evaluation F k).inv =
    (colimit.ι F j).app k :=
begin
  dsimp [colimit_obj_iso_colimit_comp_evaluation],
  simp,
end

@[simp, reassoc]
lemma colimit_obj_iso_colimit_comp_evaluation_ι_app_hom
  [has_colimits_of_shape J C] (F : J ⥤ (K ⥤ C)) (j : J) (k : K) :
  (colimit.ι F j).app k ≫ (colimit_obj_iso_colimit_comp_evaluation F k).hom =
     colimit.ι (F ⋙ ((evaluation K C).obj k)) j :=
begin
  dsimp [colimit_obj_iso_colimit_comp_evaluation],
  rw ←iso.eq_comp_inv,
  simp,
end

@[ext]
lemma colimit_obj_ext {H : J ⥤ K ⥤ C} [has_colimits_of_shape J C]
  {k : K} {W : C} {f g : (colimit H).obj k ⟶ W}
  (w : ∀ j, (colimit.ι H j).app k ≫ f = (colimit.ι H j).app k ≫ g) : f = g :=
begin
  apply (cancel_epi (colimit_obj_iso_colimit_comp_evaluation H k).inv).1,
  ext,
  simpa using w j,
end

instance evaluation_preserves_limits [has_limits C] (k : K) :
  preserves_limits ((evaluation K C).obj k) :=
{ preserves_limits_of_shape := λ J 𝒥, by resetI; apply_instance }

instance evaluation_preserves_colimits [has_colimits C] (k : K) :
  preserves_colimits ((evaluation K C).obj k) :=
{ preserves_colimits_of_shape := λ J 𝒥, by resetI; apply_instance }

end category_theory.limits
