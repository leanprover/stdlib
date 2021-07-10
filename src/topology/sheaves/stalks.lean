/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer
-/
import topology.category.Top.open_nhds
import topology.sheaves.presheaf
import topology.sheaves.sheaf_condition.unique_gluing
import category_theory.limits.types
import tactic.elementwise

/-!
# Stalks

For a presheaf `F` on a topological space `X`, valued in some category `C`, the *stalk* of `F`
at the point `x : X` is defined as the colimit of the following functor

(nhds x)ᵒᵖ ⥤ (opens X)ᵒᵖ ⥤ C

where the functor on the left is the inclusion of categories and the functor on the right is `F`.
For an open neighborhood `U` of `x`, we define the map `F.germ x : F.obj (op U) ⟶ F.stalk x` as the
canonical morphism into this colimit.

Taking stalks is functorial: For every point `x : X` we define a functor `stalk_functor C x`,
sending presheaves on `X` to objects of `C`. In `is_iso_iff_stalk_functor_map_iso`, we prove that a
map `f : F ⟶ G` between `Type`-valued sheaves is an isomorphism if and only if all the maps
`F.stalk x ⟶ G.stalk x` (given by the stalk functor on `f`) are isomorphisms.

For a map `f : X ⟶ Y` between topological spaces, we define `stalk_pushforward` as the induced map
on the stalks `(f _* ℱ).stalk (f x) ⟶ ℱ.stalk x`.

-/

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
    ← F.germ_res iWV ⟨x, hxW⟩, comp_apply, comp_apply, ih]

end

lemma stalk_hom_ext (F : X.presheaf C) {x} {Y : C} {f₁ f₂ : F.stalk x ⟶ Y}
  (ih : ∀ (U : opens X) (hxU : x ∈ U), F.germ ⟨x, hxU⟩ ≫ f₁ = F.germ ⟨x, hxU⟩ ≫ f₂) : f₁ = f₂ :=
colimit.hom_ext $ λ U, by { op_induction U, cases U with U hxU, exact ih U hxU }

/-- If two sections agree on all stalks, they must be equal -/
lemma section_ext (F : sheaf (Type v) X) (U : opens X) (s t : F.presheaf.obj (op U))
  (h : ∀ x : U, F.presheaf.germ x s = F.presheaf.germ x t) :
  s = t :=
begin
  -- We use `germ_eq` and the axiom of choice, to pick for every point `x` a neighbourhood
  -- `V x`, such that the restrictions of `s` and `t` to `V x` coincide.
  choose V m i₁ i₂ heq using λ x : U, F.presheaf.germ_eq x.1 x.2 x.2 s t (h x),
  -- Since `F` is a sheaf, we can prove the equality locally, if we can show that these
  -- neighborhoods form a cover of `U`.
  apply F.eq_of_locally_eq' V U i₁,
  { intros x hxU,
    rw [subtype.val_eq_coe, opens.mem_coe, opens.mem_supr],
    exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩ },
  { intro x,
    rw [heq, subsingleton.elim (i₁ x) (i₂ x)] }
end

@[simp, reassoc] lemma stalk_functor_map_germ {F G : X.presheaf C} (U : opens X) (x : U)
  (f : F ⟶ G) : germ F x ≫ (stalk_functor C x.1).map f = f.app (op U) ≫ germ G x :=
colimit.ι_map (whisker_left ((open_nhds.inclusion x.1).op) f) (op ⟨U, x.2⟩)

@[simp] lemma stalk_functor_map_germ_apply (U : opens X) (x : U) {F G : X.presheaf (Type v)}
  (f : F ⟶ G) (s : F.obj (op U)) :
  (stalk_functor (Type v) x.1).map f (germ F x s) = germ G x (f.app (op U) s) :=
congr_fun (stalk_functor_map_germ U x f) s

open function

lemma stalk_functor_map_injective_of_app_injective {F G : presheaf (Type v) X} (f : F ⟶ G)
  (h : ∀ U : opens X, injective (f.app (op U))) (x : X) :
  injective ((stalk_functor (Type v) x).map f) := λ s t hst,
begin
  rcases germ_exist F x s with ⟨U₁, hxU₁, s, rfl⟩,
  rcases germ_exist F x t with ⟨U₂, hxU₂, t, rfl⟩,
  simp only [stalk_functor_map_germ_apply _ ⟨x,_⟩] at hst,
  obtain ⟨W, hxW, iWU₁, iWU₂, heq⟩ := G.germ_eq x hxU₁ hxU₂ _ _ hst,
  rw [← functor_to_types.naturality, ← functor_to_types.naturality] at heq,
  replace heq := h W heq,
  convert congr_arg (F.germ ⟨x,hxW⟩) heq,
  exacts [(F.germ_res_apply iWU₁ ⟨x,hxW⟩ s).symm,
          (F.germ_res_apply iWU₂ ⟨x,hxW⟩ t).symm],
end

/-
Note that the analogous statement for surjectivity is false: Surjectivity on stalks does not
imply surjectivity of the components of a sheaf morphism. However it does imply that the morphism
is an epi, but this fact is not yet formalized.
-/
lemma app_injective_of_stalk_functor_map_injective {F : sheaf (Type v) X} {G : presheaf (Type v) X}
  (f : F.presheaf ⟶ G) (h : ∀ x : X, injective ((stalk_functor (Type v) x).map f)) (U : opens X) :
  injective (f.app (op U)) :=
λ s t hst, section_ext F _ _ _ $ λ x, h x.1 $ by
  rw [stalk_functor_map_germ_apply, stalk_functor_map_germ_apply, hst]

lemma app_injective_iff_stalk_functor_map_injective {F : sheaf (Type v) X}
  {G : presheaf (Type v) X} (f : F.presheaf ⟶ G) :
  (∀ x : X, injective ((stalk_functor (Type v) x).map f)) ↔
  (∀ U : opens X, injective (f.app (op U))) :=
⟨app_injective_of_stalk_functor_map_injective f, stalk_functor_map_injective_of_app_injective f⟩

lemma app_surjective_of_stalk_functor_map_bijective {F G : sheaf (Type v) X} (f : F ⟶ G)
  (h : ∀ x : X, bijective ((stalk_functor (Type v) x).map f)) (U : opens X) :
  surjective (f.app (op U)) :=
begin
  intro t,
  -- For surjectivity, we are given an arbitrary section `t` and need to find a preimage for it.
  -- We claim that it suffices to find preimages *locally*. That is, for each `x : U` we construct
  -- a neighborhood `V ≤ U` and a section `s : F.obj (op V))` such that `f.app (op V) s` and `t`
  -- agree on `V`.
  suffices : ∀ x : U, ∃ (V : opens X) (m : x.1 ∈ V) (iVU : V ⟶ U) (s : F.presheaf.obj (op V)),
    f.app (op V) s = G.presheaf.map iVU.op t,
  { -- We use the axiom of choice to pick around each point `x` an open neighborhood `V` and a
    -- preimage under `f` on `V`.
    choose V mV iVU sf heq using this,
    -- These neighborhoods clearly cover all of `U`.
    have V_cover : U ≤ supr V,
    { intros x hxU,
      rw [subtype.val_eq_coe, opens.mem_coe, opens.mem_supr],
      exact ⟨⟨x, hxU⟩, mV ⟨x, hxU⟩⟩ },
    -- Since `F` is a sheaf, we can glue all the local preimages together to get a global preimage.
    obtain ⟨s, s_spec, -⟩ := F.exists_unique_gluing' V U iVU V_cover sf _,
    { use s,
      apply G.eq_of_locally_eq' V U iVU V_cover,
      intro x,
      rw [← functor_to_types.naturality, s_spec, heq] },
    { intros x y,
      -- What's left to show here is that the secions `sf` are compatible, i.e. they agree on
      -- the intersections `V x ⊓ V y`. We prove this by showing that all germs are equal.
      apply section_ext,
      intro z,
      -- Here, we need to use injectivity of the stalk maps.
      apply (h z).1,
      erw [stalk_functor_map_germ_apply, stalk_functor_map_germ_apply],
      rw [functor_to_types.naturality, functor_to_types.naturality, heq, heq,
        ← functor_to_types.map_comp_apply, ← functor_to_types.map_comp_apply],
      refl } },

  intro x,
  -- Now we need to prove our initial claim: That we can find preimages of `t` locally.
  -- Since `f` is surjective on stalks, we can find a preimage `s₀` of the germ of `t` at `x`
  obtain ⟨s₀,hs₀⟩ := (h x).2 (G.presheaf.germ x t),
  -- ... and this preimage must come from some section `s₁` defined on some open neighborhood `V₁`
  obtain ⟨V₁,hxV₁,s₁,hs₁⟩ := F.presheaf.germ_exist x.1 s₀,
  subst hs₁, rename hs₀ hs₁,
  erw stalk_functor_map_germ_apply V₁ ⟨x.1,hxV₁⟩ f s₁ at hs₁,
  -- Now, the germ of `f.app (op V₁) s₁` equals the germ of `t`, hence they must coincide on
  -- some open neighborhood `V₂`.
  obtain ⟨V₂, hxV₂, iV₂V₁, iV₂U, heq⟩ := G.presheaf.germ_eq x.1 hxV₁ x.2 _ _ hs₁,
  -- The restriction of `s₁` to that neighborhood is our desired local preimage.
  use [V₂, hxV₂, iV₂U, F.presheaf.map iV₂V₁.op s₁],
  rw [functor_to_types.naturality, heq],
end

lemma app_bijective_of_stalk_functor_map_bijective {F G : sheaf (Type v) X} (f : F ⟶ G)
  (h : ∀ x : X, bijective ((stalk_functor (Type v) x).map f)) (U : opens X) :
  bijective (f.app (op U)) :=
⟨app_injective_of_stalk_functor_map_injective f (λ x, (h x).1) U,
  app_surjective_of_stalk_functor_map_bijective f h U⟩

/--
If all the stalk maps of map `f : F ⟶ G` of `Type`-valued sheaves are isomorphisms, then `f` is
an isomorphism.
-/
-- Making this an instance would cause a loop in typeclass resolution with `functor.map_is_iso`
lemma is_iso_of_stalk_functor_map_iso {F G : sheaf (Type v) X} (f : F ⟶ G)
  [∀ x : X, is_iso ((stalk_functor (Type v) x).map f)] : is_iso f :=
begin
  -- Rather annoyingly, an isomorphism of presheaves isn't quite the same as an isomorphism of
  -- sheaves. We have to use that the induced functor from sheaves to presheaves is fully faithful
  haveI : is_iso ((induced_functor sheaf.presheaf).map f) :=
  @nat_iso.is_iso_of_is_iso_app _ _ _ _ F.presheaf G.presheaf f (by {
    intro U, op_induction U,
    rw is_iso_iff_bijective,
    exact app_bijective_of_stalk_functor_map_bijective f
      (λ x, (is_iso_iff_bijective _).mp (_inst_3 x)) U,
  }),
  exact is_iso_of_fully_faithful (induced_functor sheaf.presheaf) f,
end

/--
A morphism of `Type`-valued sheaves `f : F ⟶ G` is an isomorphism if and only if all the stalk
maps are isomorphisms
-/
lemma is_iso_iff_stalk_functor_map_iso {F G : sheaf (Type v) X} (f : F ⟶ G) :
  is_iso f ↔ ∀ x : X, is_iso ((stalk_functor (Type v) x).map f) :=
begin
  split,
  { intros h x, resetI,
    exact @functor.map_is_iso _ _ _ _ _ _ (stalk_functor (Type v) x) f
      ((induced_functor sheaf.presheaf).map_is_iso f) },
  { intro h, resetI,
    exact is_iso_of_stalk_functor_map_iso f }
end

variables (C)

def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) : (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
begin
  -- This is a hack; Lean doesn't like to elaborate the term written directly.
  transitivity,
  swap,
  exact colimit.pre _ (open_nhds.map f x).op,
  exact colim.map (whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ),
end

@[simp, elementwise, reassoc]
lemma stalk_pushforward_germ (f : X ⟶ Y) (F : X.presheaf C) (U : opens Y)
  (x : (opens.map f).obj U) :
  (f _* F).germ ⟨f x, x.2⟩ ≫ F.stalk_pushforward C f x = F.germ x :=
begin
  rw [stalk_pushforward, germ, colimit.ι_map_assoc, colimit.ι_pre, whisker_right_app],
  erw [category_theory.functor.map_id, category.id_comp],
  refl,
end

-- Here are two other potential solutions, suggested by @fpvandoorn at
-- <https://github.com/leanprover-community/mathlib/pull/1018#discussion_r283978240>
-- However, I can't get the subsequent two proofs to work with either one.

-- def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) :
--   (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- colim.map ((functor.associator _ _ _).inv ≫
--   whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ) ≫
-- colimit.pre ((open_nhds.inclusion x).op ⋙ ℱ) (open_nhds.map f x).op

-- def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) :
--   (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
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
