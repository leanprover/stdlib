/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.limits.functor_category

/-!
# Limit properties relating to the (co)yoneda embedding.

We calculate the colimit of `Y ↦ (X ⟶ Y)`, which is just `punit`.
(This is used in characterising cofinal functors.)

We also show the (co)yoneda embeddings preserve limits and jointly reflect them.
-/

open opposite
open category_theory
open category_theory.limits

universes v u

namespace category_theory

namespace coyoneda
variables {C : Type v} [small_category C]

/--
The colimit cocone over `coyoneda.obj X`, with cocone point `punit`.
-/
@[simps]
def colimit_cocone (X : Cᵒᵖ) : cocone (coyoneda.obj X) :=
{ X := punit,
  ι := { app := by tidy, } }

/--
The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
@[simps]
def colimit_cocone_is_colimit (X : Cᵒᵖ) : is_colimit (colimit_cocone X) :=
{ desc := λ s x, s.ι.app (unop X) (𝟙 _),
  fac' := λ s Y, by { ext f, convert congr_fun (s.w f).symm (𝟙 (unop X)), simp, },
  uniq' := λ s m w, by { ext ⟨⟩, rw ← w, simp, } }

instance (X : Cᵒᵖ) : has_colimit (coyoneda.obj X) :=
has_colimit.mk { cocone := _, is_colimit := colimit_cocone_is_colimit X }

/--
The colimit of `coyoneda.obj X` is isomorphic to `punit`.
-/
noncomputable
def colimit_coyoneda_iso (X : Cᵒᵖ) : colimit (coyoneda.obj X) ≅ punit :=
colimit.iso_colimit_cocone { cocone := _, is_colimit := colimit_cocone_is_colimit X }

end coyoneda

variables {C : Type u} [category.{v} C]

open limits

/-- The yoneda embedding `yoneda.obj X : Cᵒᵖ ⥤ Type v` for `X : C` preserves limits. -/
instance yoneda_preserves_limits (X : C) : preserves_limits (yoneda.obj X) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ K,
    { preserves := λ c t,
      { lift := λ s x, has_hom.hom.unop (t.lift ⟨op X, λ j, (s.π.app j x).op, λ j₁ j₂ α, _⟩),
        fac' := λ s j, funext $ λ x, has_hom.hom.op_inj (t.fac _ _),
        uniq' := λ s m w, funext $ λ x,
        begin
          refine has_hom.hom.op_inj (t.uniq ⟨op X, _, _⟩ _ (λ j, _)),
          { dsimp, simp [← s.w α] }, -- See library note [dsimp, simp]
          { exact has_hom.hom.unop_inj (congr_fun (w j) x) },
        end } } } }

/-- The coyoneda embedding `coyoneda.obj X : C ⥤ Type v` for `X : Cᵒᵖ` preserves limits. -/
instance coyoneda_preserves_limits (X : Cᵒᵖ) : preserves_limits (coyoneda.obj X) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ K,
    { preserves := λ c t,
      { lift := λ s x, t.lift ⟨unop X, λ j, s.π.app j x, λ j₁ j₂ α, by { dsimp, simp [← s.w α]}⟩,
          -- See library note [dsimp, simp]
        fac' := λ s j, funext $ λ x, t.fac _ _,
        uniq' := λ s m w, funext $ λ x,
        begin
          refine (t.uniq ⟨unop X, _⟩ _ (λ j, _)),
          exact congr_fun (w j) x,
        end } } } }

/-- The yoneda embeddings jointly reflect limits. -/
def yoneda_jointly_reflects_limits (J : Type v) [small_category J] (K : J ⥤ Cᵒᵖ) (c : cone K)
  (t : Π (X : C), is_limit ((yoneda.obj X).map_cone c)) : is_limit c :=
let s' : Π (s : cone K), cone (K ⋙ yoneda.obj s.X.unop) :=
  λ s, ⟨punit, λ j _, (s.π.app j).unop, λ j₁ j₂ α, funext $ λ _, has_hom.hom.op_inj (s.w α).symm⟩
in
{ lift := λ s, ((t s.X.unop).lift (s' s) punit.star).op,
  fac' := λ s j, has_hom.hom.unop_inj (congr_fun ((t s.X.unop).fac (s' s) j) punit.star),
  uniq' := λ s m w,
  begin
    apply has_hom.hom.unop_inj,
    suffices : (λ (x : punit), m.unop) = (t s.X.unop).lift (s' s),
    { apply congr_fun this punit.star },
    apply (t _).uniq (s' s) _ (λ j, _),
    ext,
    exact has_hom.hom.op_inj (w j),
  end }

/-- The coyoneda embeddings jointly reflect limits. -/
def coyoneda_jointly_reflects_limits (J : Type v) [small_category J] (K : J ⥤ C) (c : cone K)
  (t : Π (X : Cᵒᵖ), is_limit ((coyoneda.obj X).map_cone c)) : is_limit c :=
let s' : Π (s : cone K), cone (K ⋙ coyoneda.obj (op s.X)) :=
  λ s, ⟨punit, λ j _, s.π.app j, λ j₁ j₂ α, funext $ λ _, (s.w α).symm⟩
in
{ lift := λ s, (t (op s.X)).lift (s' s) punit.star,
  fac' := λ s j, congr_fun ((t _).fac (s' s) j) punit.star,
  uniq' := λ s m w,
  begin
    suffices : (λ (x : punit), m) = (t _).lift (s' s),
    { apply congr_fun this punit.star },
    apply (t _).uniq (s' s) _ (λ j, _),
    ext,
    exact (w j),
  end }

end category_theory
