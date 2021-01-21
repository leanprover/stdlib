/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.category.Top.open_nhds
import topology.sheaves.presheaf
import category_theory.limits.types

noncomputable theory

universes v u v' u'

open category_theory
open Top
open category_theory.limits
open topological_space
open opposite

variables {C : Type u} [category.{v} C]

variables [has_colimits.{v} C]

variables {X Y Z : Top.{v}}

namespace Top.presheaf

variables (C)
/-- Stalks are functorial with respect to morphisms of presheaves over a fixed `X`. -/
def stalk_functor (x : X) : X.presheaf C ⥤ C :=
((whiskering_left _ _ C).obj (open_nhds.inclusion x).op) ⋙ colim

variables {C}

/--
The stalk of a presheaf `F` at a point `x` is calculated as the colimit of the functor
nbhds x ⥤ opens F.X ⥤ C
-/
def stalk (ℱ : X.presheaf C) (x : X) : C :=
(stalk_functor C x).obj ℱ -- -- colimit ((open_nhds.inclusion x).op ⋙ ℱ)

@[simp] lemma stalk_functor_obj (ℱ : X.presheaf C) (x : X) :
  (stalk_functor C x).obj ℱ = ℱ.stalk x := rfl

/--
The germ of a section of a presheaf over an open at a point of that open.
-/
def germ (F : X.presheaf C) {U : opens X} (x : U) : F.obj (op U) ⟶ stalk F x :=
colimit.ι ((open_nhds.inclusion x.1).op ⋙ F) (op ⟨U, x.2⟩)

/-- For a `Type` valued presheaf, every point in a stalk is a germ. -/
lemma germ_exist (F : X.presheaf (Type v)) (x : X) (t : stalk F x) :
  ∃ (U : opens X) (m : x ∈ U) (s : F.obj (op U)), F.germ ⟨x, m⟩ s = t :=
begin
  obtain ⟨U, s, e⟩ := types.jointly_surjective _ (colimit.is_colimit _) t,
  revert s e,
  rw [(show U = op (unop U), from rfl)],
  generalize : unop U = V, clear U,
  cases V with V m,
  intros s e,
  exact ⟨V, m, s, e⟩,
end

lemma germ_eq (F : X.presheaf (Type v)) {U V : opens X} (x : X) (mU : x ∈ U) (mV : x ∈ V)
  (s : F.obj (op U)) (t : F.obj (op V))
  (h : germ F ⟨x, mU⟩ s = germ F ⟨x, mV⟩ t) :
  ∃ (W : opens X) (m : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V), F.map iU.op s = F.map iV.op t :=
begin
  erw types.filtered_colimit.colimit_eq_iff at h,
  rcases h with ⟨W, iU, iV, e⟩,
  exact ⟨(unop W).1, (unop W).2, iU.unop, iV.unop, e⟩,
end

@[simp] lemma germ_res (F : X.presheaf C) {U V : opens X} (i : U ⟶ V) (x : U) :
  F.map i.op ≫ germ F x = germ F (i x : V) :=
let i' : (⟨U, x.2⟩ : open_nhds x.1) ⟶ ⟨V, (i x : V).2⟩ := i in
colimit.w ((open_nhds.inclusion x.1).op ⋙ F) i'.op

@[simp] lemma germ_res_apply (F : X.presheaf (Type v)) {U V : opens X} (i : U ⟶ V)
  (x : U) (f : F.obj (op V)) :
  germ F x (F.map i.op f) = germ F (i x : V) f :=
let i' : (⟨U, x.2⟩ : open_nhds x.1) ⟶ ⟨V, (i x : V).2⟩ := i in
congr_fun (colimit.w ((open_nhds.inclusion x.1).op ⋙ F) i'.op) f

/-- A variant when the open sets are written in `(opens X)ᵒᵖ`. -/
@[simp] lemma germ_res_apply' (F : X.presheaf (Type v)) {U V : (opens X)ᵒᵖ} (i : V ⟶ U)
  (x : unop U) (f : F.obj V) :
  germ F x (F.map i f) = germ F (i.unop x : unop V) f :=
let i' : (⟨unop U, x.2⟩ : open_nhds x.1) ⟶ ⟨unop V, (i.unop x : unop V).2⟩ := i.unop in
congr_fun (colimit.w ((open_nhds.inclusion x.1).op ⋙ F) i'.op) f

section
local attribute [instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

@[ext]
lemma germ_ext {D : Type u} [category.{v} D] [concrete_category D] [has_colimits D]
  (F : X.presheaf D)
  {U V : opens X} {x : X} {hxU : x ∈ U} {hxV : x ∈ V}
  (W : opens X) (hxW : x ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V)
  {sU : F.obj (op U)} {sV : F.obj (op V)}
  (ih : F.map iWU.op sU = F.map iWV.op sV) :
  F.germ ⟨x, hxU⟩ sU = F.germ ⟨x, hxV⟩ sV :=
by erw [← F.germ_res iWU ⟨x, hxW⟩,
    ← F.germ_res iWV ⟨x, hxW⟩, coe_comp, coe_comp, ih]

end

lemma stalk_hom_ext (F : X.presheaf C) {x} {Y : C} {f₁ f₂ : F.stalk x ⟶ Y}
  (ih : ∀ (U : opens X) (hxU : x ∈ U), F.germ ⟨x, hxU⟩ ≫ f₁ = F.germ ⟨x, hxU⟩ ≫ f₂) : f₁ = f₂ :=
colimit.hom_ext $ λ U, by { op_induction U, cases U with U hxU, exact ih U hxU }

variables (C)

def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) : (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
begin
  -- This is a hack; Lean doesn't like to elaborate the term written directly.
  transitivity,
  swap,
  exact colimit.pre _ (open_nhds.map f x).op,
  exact colim.map (whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ),
end

-- Here are two other potential solutions, suggested by @fpvandoorn at
-- <https://github.com/leanprover-community/mathlib/pull/1018#discussion_r283978240>
-- However, I can't get the subsequent two proofs to work with either one.

-- def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) : (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- colim.map ((functor.associator _ _ _).inv ≫
--   whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ) ≫
-- colimit.pre ((open_nhds.inclusion x).op ⋙ ℱ) (open_nhds.map f x).op

-- def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) : (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- (colim.map (whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ) :
--   colim.obj ((open_nhds.inclusion (f x) ⋙ opens.map f).op ⋙ ℱ) ⟶ _) ≫
-- colimit.pre ((open_nhds.inclusion x).op ⋙ ℱ) (open_nhds.map f x).op

namespace stalk_pushforward
local attribute [tidy] tactic.op_induction'

@[simp] lemma id (ℱ : X.presheaf C) (x : X) :
  ℱ.stalk_pushforward C (𝟙 X) x = (stalk_functor C x).map ((pushforward.id ℱ).hom) :=
begin
  dsimp [stalk_pushforward, stalk_functor],
  ext1,
  tactic.op_induction',
  cases j, cases j_val,
  rw [colimit.ι_map_assoc, colimit.ι_map, colimit.ι_pre, whisker_left_app, whisker_right_app,
       pushforward.id_hom_app, eq_to_hom_map, eq_to_hom_refl],
  dsimp,
  -- FIXME A simp lemma which unfortunately doesn't fire:
  erw [category_theory.functor.map_id],
end

-- This proof is sadly not at all robust:
-- having to use `erw` at all is a bad sign.
@[simp] lemma comp (ℱ : X.presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  ℱ.stalk_pushforward C (f ≫ g) x =
  ((f _* ℱ).stalk_pushforward C g (f x)) ≫ (ℱ.stalk_pushforward C f x) :=
begin
  dsimp [stalk_pushforward, stalk_functor],
  ext U,
  op_induction U,
  cases U,
  cases U_val,
  simp only [colimit.ι_map_assoc, colimit.ι_pre_assoc,
             whisker_right_app, category.assoc],
  dsimp,
  -- FIXME: Some of these are simp lemmas, but don't fire successfully:
  erw [category_theory.functor.map_id, category.id_comp, category.id_comp, category.id_comp,
       colimit.ι_pre, colimit.ι_pre],
  refl,
end

end stalk_pushforward
end Top.presheaf
