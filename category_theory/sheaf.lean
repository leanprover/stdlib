import category_theory.examples.topological_spaces

import category_theory.opposites
import category_theory.yoneda
import category_theory.limits
import category_theory.limits.types
import category_theory.limits.functor_category

open category_theory
open category_theory.limits

universes u u₁ u₂ v v₁ v₂ w w₁ w₂

section square
variables {C : Type u} [𝒞 : category.{u v} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
include 𝒞

@[simp] lemma cospan_left {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  cospan f g walking_cospan.left = X := rfl

@[simp] lemma cospan_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  cospan f g walking_cospan.right = Y := rfl

@[simp] lemma cospan_one {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  cospan f g walking_cospan.one = Z := rfl

@[simp] lemma cospan_map_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).map walking_cospan_hom.inl = f := rfl

@[simp] lemma cospan_map_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).map walking_cospan_hom.inr = g := rfl

@[simp] lemma cospan_map_id {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : walking_cospan):
  (cospan f g).map (walking_cospan_hom.id w) = 𝟙 _ := rfl

def square.mk {X Y Z W : C} {f : X ⟶ Z} {g : Y ⟶ Z} (f' : W ⟶ X) (g' : W ⟶ Y)
  (eq : f' ≫ f = g' ≫ g) :
  square f g :=
{ X := W,
  π :=
  { app := λX, walking_cospan.cases_on X f' g' (f' ≫ f),
    naturality' := assume X Y f, by cases f; obviously } }

def pullback.lift [has_pullbacks.{u v} C] {X Y Z W : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  (f' : W ⟶ X) (g' : W ⟶ Y) (eq : f' ≫ f = g' ≫ g) : W ⟶ pullback f g :=
(pullback.universal_property f g).lift (square.mk f' g' eq)

@[simp] lemma pullback.lift_π₁ [has_pullbacks.{u v} C] {X Y Z W : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  (f' : W ⟶ X) (g' : W ⟶ Y) (eq : f' ≫ f = g' ≫ g) :
  pullback.lift f' g' eq ≫ pullback.π₁ f g = f' :=
(pullback.universal_property f g).fac (square.mk f' g' eq) _

@[simp] lemma pullback.lift_π₂ [has_pullbacks.{u v} C] {X Y Z W : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  (f' : W ⟶ X) (g' : W ⟶ Y) (eq : f' ≫ f = g' ≫ g) :
  pullback.lift f' g' eq ≫ pullback.π₂ f g = g' :=
(pullback.universal_property f g).fac (square.mk f' g' eq) _

end square

section presheaf
variables (X : Type v) [𝒳 : small_category X] (C : Type u) [𝒞 : category.{u v} C]
include 𝒳 𝒞

def presheaf := Xᵒᵖ ⥤ C

variables {X} {C}

instance : category.{(max u v) v} (presheaf X C) := by unfold presheaf; apply_instance

set_option pp.universes true
instance presheaf.has_coequalizers [has_coequalizers.{u v} C] :
  has_coequalizers.{(max u v) v} (presheaf X C) := limits.functor_category_has_coequalizers
instance presheaf.has_coproducts [has_coproducts.{u v} C] :
  has_coproducts.{(max u v) v} (presheaf X C) := limits.functor_category_has_coproducts
instance presheaf.has_limits [has_limits.{u v} C] :
  has_limits.{(max u v) v} (presheaf X C) := limits.functor_category_has_limits
instance presheaf.has_pullbacks [has_pullbacks.{u v} C] :
  has_pullbacks.{(max u v) v} (presheaf X C) := limits.functor_category_has_pullbacks

omit 𝒞

-- TODO these can be removed; just checking they work
instance presheaf_of_types.has_coequalizers : has_coequalizers.{v+1 v} (presheaf X (Type v)) := by apply_instance
instance presheaf_of_types.has_coproducts : has_coproducts.{v+1 v} (presheaf X (Type v)) := by apply_instance
instance presheaf_of_types.has_limits : has_limits.{v+1 v} (presheaf X (Type v)) := by apply_instance
instance presheaf_of_types.has_pullbacks : has_pullbacks.{v+1 v} (presheaf X (Type v)) := by apply_instance

end presheaf

section over_under -- move somewhere else
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def over (X : C) := comma (functor.id C) (category_theory.limits.functor.of_obj X)

def under (X : C) := comma (category_theory.limits.functor.of_obj X) (functor.id C)

end over_under

namespace over
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

instance {X : C} : category (over X) := by unfold over; apply_instance

def forget (X : C) : (over X) ⥤ C :=
{ obj  := λ Y, Y.left,
  map' := λ _ _ f, f.left }

def mk {X Y : C} (f : Y ⟶ X) : over X :=
{ left := Y, hom := f }

@[simp] lemma mk_left {X Y : C} (f : Y ⟶ X) : (mk f).left = Y := rfl
@[simp] lemma mk_hom {X Y : C} (f : Y ⟶ X) : (mk f).hom = f := rfl
@[simp] lemma mk_right {X Y : C} (f : Y ⟶ X) : (mk f).right = ⟨⟩ := rfl

def map {X Y : C} (f : X ⟶ Y) : over X ⥤ over Y :=
{ obj := λ U, mk (U.hom ≫ f),
  map' := λ U V g,
  { left := g.left,
    w' :=
    begin
      dsimp only [mk],
      rw [← category.assoc, g.w],
      dsimp [limits.functor.of_obj],
      simp
    end } }

def comap [has_pullbacks.{u v} C] {X Y : C} (f : X ⟶ Y) : over Y ⥤ over X :=
{ obj  := λ V, mk $ pullback.π₁ f V.hom,
  map' := λ V₁ V₂ g,
  { left := pullback.lift (pullback.π₁ f V₁.hom) (pullback.π₂ f V₁.hom ≫ g.left)
      begin
        have := g.w,
        dsimp [functor.of_obj] at this,
        simp at this,
        rw [pullback.w, category.assoc, this],
      end,
    w' := by dsimp [mk, functor.of_obj]; simp },
  map_id' :=
  begin
    obviously,
  end }

end over

@[reducible]
def covering_family {X : Type v} [small_category X] (U : X) : Type v := set (over.{v v} U)

namespace covering_family
open category_theory.limits
variables {X : Type v} [𝒳 : small_category X]
include 𝒳

variables {U : X} (c : covering_family U)

def sieve : presheaf X (Type v) :=
let
  y (Ui : c) := (yoneda X).map Ui.val.hom,
  pb (Ujk : c × c) : presheaf X (Type v) := limits.pullback (y Ujk.1) (y Ujk.2),
  re (Ui : c) : presheaf X (Type v) := (yoneda X).obj Ui.val.left,
  left  : limits.sigma pb ⟶ limits.sigma re :=
    sigma.desc $ λUjk:c×c, pullback.π₁ (y Ujk.1) (y Ujk.2) ≫ sigma.ι re Ujk.1,
  right : limits.sigma pb ⟶ limits.sigma re :=
    sigma.desc $ λUjk:c×c, pullback.π₂ (y Ujk.1) (y Ujk.2) ≫ sigma.ι re Ujk.2
in coequalizer left right

def π : c.sieve ⟶ yoneda X U :=
coequalizer.desc _ _ (sigma.desc $ λUi, (yoneda X).map Ui.val.hom)
begin
  ext1, dsimp at *,
  erw ←category.assoc,
  erw ←category.assoc,
  simp,
end

def sheaf_condition (F : presheaf X (Type v)) :=
is_iso $ ((yoneda (presheaf X (Type v))).obj F).map c.π

end covering_family

def coverage_on (X : Type u) [small_category.{u} X]
  (covers : Π (U : X), set (covering_family U)) : Prop :=
∀ {U V : X} (g : V ⟶ U),
∀f ∈ covers U, ∃h ∈ covers V,
∀ Vj : (h : set _), ∃ (Ui : f),
∃ k : Vj.val.left ⟶ Ui.val.left, Vj.val.hom ≫ g = k ≫ Ui.val.hom

structure coverage (X : Type u) [small_category.{u} X] :=
(covers   : Π (U : X), set (covering_family U))
(property : coverage_on X covers)

class site (X : Type u) extends category.{u u} X :=
(coverage : coverage X)

namespace site
variables {X : Type u₁} [𝒳 : site.{u₁} X]

definition covers := coverage.covers 𝒳.coverage

end site

structure sheaf (X : Type u) [𝒳 : site.{u} X] :=
(presheaf : presheaf X (Type u))
(sheaf_condition : ∀ {U : X}, ∀c ∈ site.covers U, (c : covering_family U).sheaf_condition presheaf)

namespace topological_space

variables {X : Type u} [topological_space X]

-- The following should be generalised to categories coming from a complete(?) lattice
instance : has_pullbacks.{u u} (opens X) :=
{ square := _ }

instance : site (opens X) :=
{ coverage :=
  { covers := λ U Us, U = ⨆u∈Us, (u:over _).left,
    property :=
    begin
      refine λU V i Us (hUs : _ = _), ⟨_, _, _⟩,
      exact (over.comap i '' Us),
    end } }

end topological_space
