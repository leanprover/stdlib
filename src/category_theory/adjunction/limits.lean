/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin
-/
import category_theory.limits.creates

open opposite

namespace category_theory.adjunction
open category_theory
open category_theory.functor
open category_theory.limits

universes u₁ u₂ v

variables {C : Type u₁} [category.{v} C] {D : Type u₂} [category.{v} D]

variables {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
include adj

section preservation_colimits
variables {J : Type v} [small_category J] (K : J ⥤ C)

/--
The right adjoint of `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
def functoriality_right_adjoint : cocone (K ⋙ F) ⥤ cocone K :=
(cocones.functoriality _ G) ⋙
  (cocones.precompose (K.right_unitor.inv ≫ (whisker_left K adj.unit) ≫ (associator _ _ _).inv))

local attribute [reducible] functoriality_right_adjoint

/--
The unit for the adjunction for `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
@[simps] def functoriality_unit : 𝟭 (cocone K) ⟶ cocones.functoriality _ F ⋙ functoriality_right_adjoint adj K :=
{ app := λ c, { hom := adj.unit.app c.X } }

/--
The counit for the adjunction for `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
@[simps] def functoriality_counit : functoriality_right_adjoint adj K ⋙ cocones.functoriality _ F ⟶ 𝟭 (cocone (K ⋙ F)) :=
{ app := λ c, { hom := adj.counit.app c.X } }

/-- The functor `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)` is a left adjoint. -/
def functoriality_is_left_adjoint :
  is_left_adjoint (cocones.functoriality K F) :=
{ right := functoriality_right_adjoint adj K,
  adj := mk_of_unit_counit
  { unit := functoriality_unit adj K,
    counit := functoriality_counit adj K } }

/--
A left adjoint preserves colimits.

See https://stacks.math.columbia.edu/tag/0038.
-/
def left_adjoint_preserves_colimits : preserves_colimits F :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ F,
    by exactI
    { preserves := λ c hc, is_colimit.iso_unique_cocone_morphism.inv
        (λ s, @equiv.unique _ _ (is_colimit.iso_unique_cocone_morphism.hom hc _)
          (((adj.functoriality_is_left_adjoint _).adj).hom_equiv _ _)) } } }.

omit adj

@[priority 100] -- see Note [lower instance priority]
instance is_equivalence_preserves_colimits (E : C ⥤ D) [is_equivalence E] : preserves_colimits E :=
left_adjoint_preserves_colimits E.adjunction

@[priority 100] -- see Note [lower instance priority]
instance is_equivalence_reflects_colimits (E : D ⥤ C) [is_equivalence E] : reflects_colimits E :=
{ reflects_colimits_of_shape := λ J 𝒥, by exactI
  { reflects_colimit := λ K,
    { reflects := λ c t,
      begin
        have l := (is_colimit_of_preserves E.inv t).map_cocone_equiv E.fun_inv_id,
        refine (((is_colimit.precompose_inv_equiv K.right_unitor _).symm) l).of_iso_colimit _,
        tidy,
      end } } }

@[priority 100] -- see Note [lower instance priority]
instance is_equivalence_creates_colimits (H : D ⥤ C) [is_equivalence H] : creates_colimits H :=
{ creates_colimits_of_shape := λ J 𝒥, by exactI
  { creates_colimit := λ F,
    { lifts := λ c t,
      { lifted_cocone := H.map_cocone_inv c,
        valid_lift := H.map_cocone_map_cocone_inv c } } } }

-- verify the preserve_colimits instance works as expected:
example (E : C ⥤ D) [is_equivalence E]
  (c : cocone K) (h : is_colimit c) : is_colimit (E.map_cocone c) :=
preserves_colimit.preserves h

instance has_colimit_comp_equivalence (E : C ⥤ D) [is_equivalence E] [has_colimit K] :
  has_colimit (K ⋙ E) :=
has_colimit.mk
{ cocone := E.map_cocone (colimit.cocone K),
  is_colimit := preserves_colimit.preserves (colimit.is_colimit K) }

lemma has_colimit_of_comp_equivalence (E : C ⥤ D) [is_equivalence E] [has_colimit (K ⋙ E)] :
  has_colimit K :=
@has_colimit_of_iso _ _ _ _ (K ⋙ E ⋙ inv E) K
(@adjunction.has_colimit_comp_equivalence _ _ _ _ _ _ (K ⋙ E) (inv E) _ _)
((functor.right_unitor _).symm ≪≫ (iso_whisker_left K (fun_inv_id E)).symm)

end preservation_colimits

section preservation_limits
variables {J : Type v} [small_category J] (K : J ⥤ D)

/--
The left adjoint of `cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
def functoriality_left_adjoint : cone (K ⋙ G) ⥤ cone K :=
(cones.functoriality _ F) ⋙ (cones.postcompose
    ((associator _ _ _).hom ≫ (whisker_left K adj.counit) ≫ K.right_unitor.hom))

local attribute [reducible] functoriality_left_adjoint

/--
The unit for the adjunction for`cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
@[simps] def functoriality_unit' : 𝟭 (cone (K ⋙ G)) ⟶ functoriality_left_adjoint adj K ⋙ cones.functoriality _ G :=
{ app := λ c, { hom := adj.unit.app c.X, } }

/--
The counit for the adjunction for`cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
@[simps] def functoriality_counit' : cones.functoriality _ G ⋙ functoriality_left_adjoint adj K ⟶ 𝟭 (cone K) :=
{ app := λ c, { hom := adj.counit.app c.X, } }

/-- The functor `cones.functoriality K G : cone K ⥤ cone (K ⋙ G)` is a right adjoint. -/
def functoriality_is_right_adjoint :
  is_right_adjoint (cones.functoriality K G) :=
{ left := functoriality_left_adjoint adj K,
  adj := mk_of_unit_counit
  { unit := functoriality_unit' adj K,
    counit := functoriality_counit' adj K } }

/--
A right adjoint preserves limits.

See https://stacks.math.columbia.edu/tag/0038.
-/
def right_adjoint_preserves_limits : preserves_limits G :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ K,
    by exactI
    { preserves := λ c hc, is_limit.iso_unique_cone_morphism.inv
        (λ s, @equiv.unique _ _ (is_limit.iso_unique_cone_morphism.hom hc _)
          (((adj.functoriality_is_right_adjoint _).adj).hom_equiv _ _).symm) } } }.

omit adj

@[priority 100] -- see Note [lower instance priority]
instance is_equivalence_preserves_limits (E : D ⥤ C) [is_equivalence E] : preserves_limits E :=
right_adjoint_preserves_limits E.inv.adjunction

@[priority 100] -- see Note [lower instance priority]
instance is_equivalence_reflects_limits (E : D ⥤ C) [is_equivalence E] : reflects_limits E :=
{ reflects_limits_of_shape := λ J 𝒥, by exactI
  { reflects_limit := λ K,
    { reflects := λ c t,
      begin
        have := (is_limit_of_preserves E.inv t).map_cone_equiv E.fun_inv_id,
        refine (((is_limit.postcompose_hom_equiv K.left_unitor _).symm) this).of_iso_limit _,
        tidy,
      end } } }

@[priority 100] -- see Note [lower instance priority]
instance is_equivalence_creates_limits (H : D ⥤ C) [is_equivalence H] : creates_limits H :=
{ creates_limits_of_shape := λ J 𝒥, by exactI
  { creates_limit := λ F,
    { lifts := λ c t,
      { lifted_cone := H.map_cone_inv c,
        valid_lift := H.map_cone_map_cone_inv c } } } }

-- verify the preserve_limits instance works as expected:
example (E : D ⥤ C) [is_equivalence E]
  (c : cone K) [h : is_limit c] : is_limit (E.map_cone c) :=
preserves_limit.preserves h

instance has_limit_comp_equivalence (E : D ⥤ C) [is_equivalence E] [has_limit K] :
  has_limit (K ⋙ E) :=
has_limit.mk
{ cone := E.map_cone (limit.cone K),
  is_limit := preserves_limit.preserves (limit.is_limit K) }

lemma has_limit_of_comp_equivalence (E : D ⥤ C) [is_equivalence E] [has_limit (K ⋙ E)] :
  has_limit K :=
@has_limit_of_iso _ _ _ _ (K ⋙ E ⋙ inv E) K
(@adjunction.has_limit_comp_equivalence _ _ _ _ _ _ (K ⋙ E) (inv E) _ _)
((iso_whisker_left K (fun_inv_id E)) ≪≫ (functor.right_unitor _))

end preservation_limits

/-- auxiliary construction for `cocones_iso` -/
@[simps]
def cocones_iso_component_hom {J : Type v} [small_category J] {K : J ⥤ C}
  (Y : D) (t : ((cocones J D).obj (op (K ⋙ F))).obj Y) :
  (G ⋙ (cocones J C).obj (op K)).obj Y :=
{ app := λ j, (adj.hom_equiv (K.obj j) Y) (t.app j),
  naturality' := λ j j' f, by { erw [← adj.hom_equiv_naturality_left, t.naturality], dsimp, simp } }

/-- auxiliary construction for `cocones_iso` -/
@[simps]
def cocones_iso_component_inv {J : Type v} [small_category J] {K : J ⥤ C}
  (Y : D) (t : (G ⋙ (cocones J C).obj (op K)).obj Y) :
  ((cocones J D).obj (op (K ⋙ F))).obj Y :=
{ app := λ j, (adj.hom_equiv (K.obj j) Y).symm (t.app j),
  naturality' := λ j j' f,
  begin
    erw [← adj.hom_equiv_naturality_left_symm, ← adj.hom_equiv_naturality_right_symm, t.naturality],
    dsimp, simp
  end }

/--
When `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/
-- Note: this is natural in K, but we do not yet have the tools to formulate that.
def cocones_iso {J : Type v} [small_category J] {K : J ⥤ C} :
  (cocones J D).obj (op (K ⋙ F)) ≅ G ⋙ ((cocones J C).obj (op K)) :=
nat_iso.of_components (λ Y,
{ hom := cocones_iso_component_hom adj Y,
  inv := cocones_iso_component_inv adj Y, })
(by tidy)

/-- auxiliary construction for `cones_iso` -/
@[simps]
def cones_iso_component_hom {J : Type v} [small_category J] {K : J ⥤ D}
  (X : Cᵒᵖ) (t : (functor.op F ⋙ (cones J D).obj K).obj X) :
  ((cones J C).obj (K ⋙ G)).obj X :=
{ app := λ j, (adj.hom_equiv (unop X) (K.obj j)) (t.app j),
  naturality' := λ j j' f,
  begin
    erw [← adj.hom_equiv_naturality_right, ← t.naturality, category.id_comp, category.id_comp],
    refl
  end }

/-- auxiliary construction for `cones_iso` -/
@[simps]
def cones_iso_component_inv {J : Type v} [small_category J] {K : J ⥤ D}
  (X : Cᵒᵖ) (t : ((cones J C).obj (K ⋙ G)).obj X) :
  (functor.op F ⋙ (cones J D).obj K).obj X :=
{ app := λ j, (adj.hom_equiv (unop X) (K.obj j)).symm (t.app j),
  naturality' := λ j j' f,
  begin
    erw [← adj.hom_equiv_naturality_right_symm, ← t.naturality, category.id_comp, category.id_comp]
  end }

-- Note: this is natural in K, but we do not yet have the tools to formulate that.
/--
When `F ⊣ G`,
the functor associating to each `X` the cones over `K` with cone point `F.op.obj X`
is naturally isomorphic to
the functor associating to each `X` the cones over `K ⋙ G` with cone point `X`.
-/
def cones_iso {J : Type v} [small_category J] {K : J ⥤ D} :
  F.op ⋙ ((cones J D).obj K) ≅ (cones J C).obj (K ⋙ G) :=
nat_iso.of_components (λ X,
{ hom := cones_iso_component_hom adj X,
  inv := cones_iso_component_inv adj X, } )
(by tidy)

end category_theory.adjunction
