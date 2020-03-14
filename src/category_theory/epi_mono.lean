/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

Facts about epimorphisms and monomorphisms.

The definitions of `epi` and `mono` are in `category_theory.category`,
since they are used by some lemmas for `iso`, which is used everywhere.
-/

import category_theory.adjunction.basic
import category_theory.fully_faithful

universes v₁ v₂ u₁ u₂

namespace category_theory

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

section
variables {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒟

lemma left_adjoint_preserves_epi {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  {X Y : C} {f : X ⟶ Y} (hf : epi f) : epi (F.map f) :=
begin
  constructor,
  intros Z g h H,
  replace H := congr_arg (adj.hom_equiv X Z) H,
  rwa [adj.hom_equiv_naturality_left, adj.hom_equiv_naturality_left,
    cancel_epi, equiv.apply_eq_iff_eq] at H
end

lemma right_adjoint_preserves_mono {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  {X Y : D} {f : X ⟶ Y} (hf : mono f) : mono (G.map f) :=
begin
  constructor,
  intros Z g h H,
  replace H := congr_arg (adj.hom_equiv Z Y).symm H,
  rwa [adj.hom_equiv_naturality_right_symm, adj.hom_equiv_naturality_right_symm,
    cancel_mono, equiv.apply_eq_iff_eq] at H
end

lemma faithful_reflects_epi (F : C ⥤ D) [faithful F] {X Y : C} {f : X ⟶ Y}
  (hf : epi (F.map f)) : epi f :=
⟨λ Z g h H, F.injectivity $
  by rw [←cancel_epi (F.map f), ←F.map_comp, ←F.map_comp, H]⟩

lemma faithful_reflects_mono (F : C ⥤ D) [faithful F] {X Y : C} {f : X ⟶ Y}
  (hf : mono (F.map f)) : mono f :=
⟨λ Z g h H, F.injectivity $
  by rw [←cancel_mono (F.map f), ←F.map_comp, ←F.map_comp, H]⟩
end

class split_mono {X Y : C} (f : X ⟶ Y) :=
(retraction : Y ⟶ X)
(id' : f ≫ retraction = 𝟙 X . obviously)

class split_epi {X Y : C} (f : X ⟶ Y) :=
(section_ : Y ⟶ X)
(id' : section_ ≫ f = 𝟙 Y . obviously)

/-- The chosen retraction of a split monomorphism. -/
def retraction {X Y : C} (f : X ⟶ Y) [split_mono f] : Y ⟶ X := split_mono.retraction.{v₁} f
@[simp, reassoc]
lemma split_mono.id {X Y : C} (f : X ⟶ Y) [split_mono f] : f ≫ retraction f = 𝟙 X :=
split_mono.id' f

/-- The chosen retraction of a split monomorphism. -/
def section_ {X Y : C} (f : X ⟶ Y) [split_epi f] : Y ⟶ X := split_epi.section_.{v₁} f
@[simp, reassoc]
lemma split_epi.id {X Y : C} (f : X ⟶ Y) [split_epi f] : section_ f ≫ f = 𝟙 Y :=
split_epi.id' f

instance mono_of_split_mono {X Y : C} (f : X ⟶ Y) [split_mono f] : mono f :=
{ right_cancellation := λ Z g h w, begin replace w := w =≫ retraction f, simpa using w, end }

instance epi_of_split_epi {X Y : C} (f : X ⟶ Y) [split_epi f] : epi f :=
{ left_cancellation := λ Z g h w, begin replace w := section_ f ≫= w, simpa using w, end }

section
variables {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒟

/-- Split monomorphisms are also absolute monomorphisms. -/
instance {X Y : C} (f : X ⟶ Y) [split_mono f] (F : C ⥤ D) : split_mono (F.map f) :=
{ retraction := F.map (retraction f),
  id' := by { rw [←functor.map_comp, split_mono.id, functor.map_id], } }

/-- Split epimorphisms are also absolute epimorphisms. -/
instance {X Y : C} (f : X ⟶ Y) [split_epi f] (F : C ⥤ D) : split_epi (F.map f) :=
{ section_ := F.map (section_ f),
  id' := by { rw [←functor.map_comp, split_epi.id, functor.map_id], } }
end

end category_theory
