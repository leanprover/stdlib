/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro
-/
import topology.category.Top.basic
import category_theory.limits.types
import category_theory.limits.preserves.basic
import category_theory.category.ulift

/-!
# The category of topological spaces has all limits and colimits

Further, these limits and colimits are preserved by the forgetful functor --- that is, the
underlying types are just the limits in the category of types.
-/

open topological_space
open category_theory
open category_theory.limits
open opposite

universes u v w

noncomputable theory

namespace Top

variables {J : Type u} [small_category J]

local notation `forget` := forget Top

/--
A choice of limit cone for a functor `F : J ⥤ Top`.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limit_cone (F : J ⥤ Top.{u}) : cone F :=
{ X := Top.of {u : Π j : J, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j},
  π :=
  { app := λ j,
    { to_fun := λ u, u.val j,
      continuous_to_fun := show continuous ((λ u : Π j : J, F.obj j, u j) ∘ subtype.val),
        by continuity } } }

/--
A choice of limit cone for a functor `F : J ⥤ Top` whose topology is defined as an
infimum of topologies infimum.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limit_cone_infi (F : J ⥤ Top.{u}) : cone F :=
{ X := ⟨(types.limit_cone (F ⋙ forget)).X, ⨅j,
        (F.obj j).str.induced ((types.limit_cone (F ⋙ forget)).π.app j)⟩,
  π :=
  { app := λ j, ⟨(types.limit_cone (F ⋙ forget)).π.app j,
                 continuous_iff_le_induced.mpr (infi_le _ _)⟩,
    naturality' := λ j j' f,
                   continuous_map.coe_inj ((types.limit_cone (F ⋙ forget)).π.naturality f) } }

/--
The chosen cone `Top.limit_cone F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limit_cone_is_limit (F : J ⥤ Top.{u}) : is_limit (limit_cone F) :=
{ lift := λ S, { to_fun := λ x, ⟨λ j, S.π.app _ x, λ i j f, by { dsimp, erw ← S.w f, refl }⟩ },
  uniq' := λ S m h, by { ext : 3, simpa [← h] } }

/--
The chosen cone `Top.limit_cone_infi F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limit_cone_infi_is_limit (F : J ⥤ Top.{u}) : is_limit (limit_cone_infi F) :=
by { refine is_limit.of_faithful forget (types.limit_cone_is_limit _) (λ s, ⟨_, _⟩) (λ s, rfl),
     exact continuous_iff_coinduced_le.mpr (le_infi $ λ j,
       coinduced_le_iff_le_induced.mp $ (continuous_iff_coinduced_le.mp (s.π.app j).continuous :
         _) ) }

instance Top_has_limits : has_limits.{u} Top.{u} :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk { cone := limit_cone F, is_limit := limit_cone_is_limit F } } }

instance forget_preserves_limits : preserves_limits (forget : Top.{u} ⥤ Type u) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget)) } }

/--
A choice of colimit cocone for a functor `F : J ⥤ Top`.
Generally you should just use `colimit.coone F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone`).
-/
def colimit_cocone (F : J ⥤ Top.{u}) : cocone F :=
{ X := ⟨(types.colimit_cocone (F ⋙ forget)).X, ⨆ j,
        (F.obj j).str.coinduced ((types.colimit_cocone (F ⋙ forget)).ι.app j)⟩,
  ι :=
  { app := λ j, ⟨(types.colimit_cocone (F ⋙ forget)).ι.app j,
                 continuous_iff_coinduced_le.mpr (le_supr _ j)⟩,
    naturality' := λ j j' f,
                   continuous_map.coe_inj ((types.colimit_cocone (F ⋙ forget)).ι.naturality f) } }

/--
The chosen cocone `Top.colimit_cocone F` for a functor `F : J ⥤ Top` is a colimit cocone.
Generally you should just use `colimit.is_colimit F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone_is_colimit`).
-/
def colimit_cocone_is_colimit (F : J ⥤ Top.{u}) : is_colimit (colimit_cocone F) :=
by { refine is_colimit.of_faithful forget (types.colimit_cocone_is_colimit _) (λ s, ⟨_, _⟩)
       (λ s, rfl),
     exact continuous_iff_le_induced.mpr (supr_le $ λ j,
       coinduced_le_iff_le_induced.mp $ (continuous_iff_coinduced_le.mp (s.ι.app j).continuous :
         _) ) }

instance Top_has_colimits : has_colimits.{u} Top.{u} :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk { cocone := colimit_cocone F, is_colimit :=
    colimit_cocone_is_colimit F } } }

instance forget_preserves_colimits : preserves_colimits (forget : Top.{u} ⥤ Type u) :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ F,
    by exactI preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F) (types.colimit_cocone_is_colimit (F ⋙ forget)) } }

end Top

namespace Top

section cofiltered_limit

variables {J : Type u} [small_category J] [is_cofiltered J] (F : J ⥤ Top.{u})
  (C : cone F) (hC : is_limit C)

include hC

/--
Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/
theorem is_topological_basis_cofiltered_limit
  (T : Π j, set (set (F.obj j))) (hT : ∀ j, is_topological_basis (T j))
  (univ : ∀ (i : J), set.univ ∈ T i)
  (inter : ∀ i (U1 U2 : set (F.obj i)), U1 ∈ T i → U2 ∈ T i → U1 ∩ U2 ∈ T i)
  (compat : ∀ (i j : J) (f : i ⟶ j) (V : set (F.obj j)) (hV : V ∈ T j), (F.map f) ⁻¹' V ∈ T i) :
  is_topological_basis { U : set C.X | ∃ j (V : set (F.obj j)), V ∈ T j ∧ U = C.π.app j ⁻¹' V } :=
begin
  classical,
  -- The limit cone for `F` whose topology is defined as an infimum.
  let D := limit_cone_infi F,
  -- The isomorphism between the cone point of `C` and the cone point of `D`.
  let E : C.X ≅ D.X := hC.cone_point_unique_up_to_iso (limit_cone_infi_is_limit _),
  have hE : inducing E.hom := (Top.homeo_of_iso E).inducing,
  -- Reduce to the assertion of the theorem with `D` instead of `C`.
  suffices : is_topological_basis
    { U : set D.X | ∃ j (V : set (F.obj j)), V ∈ T j ∧ U = D.π.app j ⁻¹' V },
  { convert this.inducing hE,
    ext U0,
    split,
    { rintro ⟨j, V, hV, rfl⟩,
      refine ⟨D.π.app j ⁻¹' V, ⟨j, V, hV, rfl⟩, rfl⟩ },
    { rintro ⟨W, ⟨j, V, hV, rfl⟩, rfl⟩,
      refine ⟨j, V, hV, rfl⟩ } },
  -- Using `D`, we can apply the characterization of the topological basis of a
  -- topology defined as an infimum...
  convert is_topological_basis_infi hT (λ j (x : D.X), D.π.app j x),
  ext U0,
  split,
  { rintros  ⟨j, V, hV, rfl⟩,
    let U : Π i, set (F.obj i) := λ i, if h : i = j then (by {rw h, exact V}) else set.univ,
    refine ⟨U,{j},_,_⟩,
    { rintro i h,
      rw finset.mem_singleton at h,
      dsimp [U],
      rw dif_pos h,
      subst h,
      exact hV },
    { dsimp [U],
      simp } },
  { rintros ⟨U, G, h1, h2⟩,
    obtain ⟨j, hj⟩ := is_cofiltered.inf_objs_exists G,
    let g : ∀ e (he : e ∈ G), j ⟶ e := λ _ he, (hj he).some,
    let Vs : J → set (F.obj j) := λ e, if h : e ∈ G then F.map (g e h) ⁻¹' (U e) else set.univ,
    let V : set (F.obj j) := ⋂ (e : J) (he : e ∈ G), Vs e,
    refine ⟨j, V, _, _⟩,
    { -- An intermediate claim used to apply induction along `G : finset J` later on.
      have : ∀ (S : set (set (F.obj j))) (E : finset J) (P : J → set (F.obj j))
        (univ : set.univ ∈ S)
        (inter : ∀ A B : set (F.obj j), A ∈ S → B ∈ S → A ∩ B ∈ S)
        (cond : ∀ (e : J) (he : e ∈ E), P e ∈ S), (⋂ e (he : e ∈ E), P e) ∈ S,
      { intros S E,
        apply E.induction_on,
        { intros P he hh,
          simpa },
        { intros a E ha hh1 hh2 hh3 hh4 hh5,
          rw finset.set_bInter_insert,
          refine hh4 _ _ (hh5 _ (finset.mem_insert_self _ _)) (hh1 _ hh3 hh4 _),
          intros e he,
          exact hh5 e (finset.mem_insert_of_mem he) } },
      -- use the intermediate claim to finish off the goal using `univ` and `inter`.
      refine this _ _ _ (univ _) (inter _) _,
      intros e he,
      dsimp [Vs],
      rw dif_pos he,
      exact compat j e (g e he) (U e) (h1 e he), },
    { -- conclude...
      rw h2,
      dsimp [V],
      rw set.preimage_Inter,
      congr' 1,
      ext1 e,
      rw set.preimage_Inter,
      congr' 1,
      ext1 he,
      dsimp [Vs],
      rw [dif_pos he, ← set.preimage_comp],
      congr' 1,
      change _ = ⇑(D.π.app j ≫ F.map (g e he)),
      rw D.w } }
end

end cofiltered_limit

section topological_konig

/-!
## Topological Kőnig's lemma

A topological version of Kőnig's lemma is that the inverse limit of nonempty compact Hausdorff
spaces is nonempty.  (Note: this can be generalized further to inverse limits of nonempty compact
T0 spaces, where all the maps are closed maps; see [Stone1979] --- however there is an erratum
for Theorem 4 that the element in the inverse limit can have cofinally many components that are
not closed points.)

We give this in a more general form, which is that cofiltered limits
of nonempty compact Hausdorff spaces are nonempty
(`nonempty_limit_cone_of_compact_t2_cofiltered_system`).

This also applies to inverse limits, where `{J : Type u} [directed_order J]` and `F : Jᵒᵖ ⥤ Top`.

The theorem is specialized to nonempty finite types (which are compact Hausdorff with the
discrete topology) in `nonempty_sections_of_fintype_cofiltered_system` and
`nonempty_sections_of_fintype_inverse_system`.

(See https://stacks.math.columbia.edu/tag/086J for the Set version.)
-/

variables {J : Type u} [small_category J]
variables (F : J ⥤ Top.{u})

private abbreviation finite_diagram_arrow {J : Type u} [small_category J] (G : finset J) :=
Σ' (X Y : J) (mX : X ∈ G) (mY : Y ∈ G), X ⟶ Y
private abbreviation finite_diagram (J : Type u) [small_category J] :=
Σ (G : finset J), finset (finite_diagram_arrow G)

/--
Partial sections of a cofiltered limit are sections when restricted to
a finite subset of objects and morphisms of `J`.
-/
def partial_sections {J : Type u} [small_category J] (F : J ⥤ Top.{u})
  {G : finset J} (H : finset (finite_diagram_arrow G)) : set (Π j, F.obj j) :=
{ u | ∀ {f : finite_diagram_arrow G} (hf : f ∈ H), F.map f.2.2.2.2 (u f.1) = u f.2.1 }

lemma partial_sections.nonempty [is_cofiltered J] [h : Π (j : J), nonempty (F.obj j)]
  {G : finset J} (H : finset (finite_diagram_arrow G)) :
  (partial_sections F H).nonempty :=
begin
  classical,
  use λ (j : J), if hj : j ∈ G
                 then F.map (is_cofiltered.inf_to G H hj) (h (is_cofiltered.inf G H)).some
                 else (h _).some,
  rintros ⟨X, Y, hX, hY, f⟩ hf,
  dsimp only,
  rwa [dif_pos hX, dif_pos hY, ←comp_app, ←F.map_comp,
       @is_cofiltered.inf_to_commutes _ _ _ G H],
end

lemma partial_sections.directed :
  directed superset (λ (G : finite_diagram J), partial_sections F G.2) :=
begin
  classical,
  intros A B,
  let ιA : finite_diagram_arrow A.1 → finite_diagram_arrow (A.1 ⊔ B.1) :=
    λ f, ⟨f.1, f.2.1, finset.mem_union_left _ f.2.2.1, finset.mem_union_left _ f.2.2.2.1,
          f.2.2.2.2⟩,
  let ιB : finite_diagram_arrow B.1 → finite_diagram_arrow (A.1 ⊔ B.1) :=
    λ f, ⟨f.1, f.2.1, finset.mem_union_right _ f.2.2.1, finset.mem_union_right _ f.2.2.2.1,
          f.2.2.2.2⟩,
  refine ⟨⟨A.1 ⊔ B.1, A.2.image ιA ⊔ B.2.image ιB⟩, _, _⟩,
  { rintro u hu f hf,
    have : ιA f ∈ A.2.image ιA ⊔ B.2.image ιB,
    { apply finset.mem_union_left,
      rw finset.mem_image,
      refine ⟨f, hf, rfl⟩ },
    exact hu this },
  { rintro u hu f hf,
    have : ιB f ∈ A.2.image ιA ⊔ B.2.image ιB,
    { apply finset.mem_union_right,
      rw finset.mem_image,
      refine ⟨f, hf, rfl⟩ },
    exact hu this }
end

lemma partial_sections.closed [Π (j : J), t2_space (F.obj j)]
  {G : finset J} (H : finset (finite_diagram_arrow G)) :
  is_closed (partial_sections F H) :=
begin
  have : partial_sections F H =
    ⋂ {f : finite_diagram_arrow G} (hf : f ∈ H), { u | F.map f.2.2.2.2 (u f.1) = u f.2.1 },
  { ext1,
    simp only [set.mem_Inter, set.mem_set_of_eq],
    refl, },
  rw this,
  apply is_closed_bInter,
  intros f hf,
  apply is_closed_eq,
  continuity,
end

/--
Cofiltered limits of nonempty compact Hausdorff spaces are nonempty topological spaces.
--/
lemma nonempty_limit_cone_of_compact_t2_cofiltered_system
  [is_cofiltered J]
  [Π (j : J), nonempty (F.obj j)]
  [Π (j : J), compact_space (F.obj j)]
  [Π (j : J), t2_space (F.obj j)] :
  nonempty (Top.limit_cone F).X :=
begin
  classical,
  obtain ⟨u, hu⟩ := is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
    (λ G, partial_sections F _)
    (partial_sections.directed F)
    (λ G, partial_sections.nonempty F _)
    (λ G, is_closed.is_compact (partial_sections.closed F _))
    (λ G, partial_sections.closed F _),
  use u,
  intros X Y f,
  let G : finite_diagram J :=
    ⟨{X, Y},
     {⟨X, Y,
      by simp only [true_or, eq_self_iff_true, finset.mem_insert],
      by simp only [eq_self_iff_true, or_true, finset.mem_insert, finset.mem_singleton],
      f⟩}⟩,
  exact hu _ ⟨G, rfl⟩ (finset.mem_singleton_self _),
end

end topological_konig

end Top

section fintype_konig

/-- This bootstraps `nonempty_sections_of_fintype_inverse_system`. In this version,
the `F` functor is between categories of the same universe, and it is an easy
corollary to `Top.nonempty_limit_cone_of_compact_t2_inverse_system`. -/
lemma nonempty_sections_of_fintype_cofiltered_system.init
  {J : Type u} [small_category J] [is_cofiltered J] (F : J ⥤ Type u)
  [hf : Π (j : J), fintype (F.obj j)] [hne : Π (j : J), nonempty (F.obj j)] :
  F.sections.nonempty :=
begin
  let F' : J ⥤ Top := F ⋙ Top.discrete,
  haveI : Π (j : J), fintype (F'.obj j) := hf,
  haveI : Π (j : J), nonempty (F'.obj j) := hne,
  obtain ⟨⟨u, hu⟩⟩ := Top.nonempty_limit_cone_of_compact_t2_cofiltered_system F',
  exact ⟨u, λ _ _ f, hu f⟩,
end

/-- The cofiltered limit of nonempty finite types is nonempty.

See `nonempty_sections_of_fintype_inverse_system` for a specialization to inverse limits. -/
theorem nonempty_sections_of_fintype_cofiltered_system
  {J : Type u} [category.{w} J] [is_cofiltered J] (F : J ⥤ Type v)
  [Π (j : J), fintype (F.obj j)] [Π (j : J), nonempty (F.obj j)] :
  F.sections.nonempty :=
begin
  -- Step 1: lift everything to the `max u v w` universe.
  let J' : Type (max w v u) := as_small.{max w v} J,
  let down : J' ⥤ J := as_small.down,
  let F' : J' ⥤ Type (max u v w) := down ⋙ F ⋙ ulift_functor.{(max u w) v},
  haveI : ∀ i, nonempty (F'.obj i) := λ i, ⟨⟨classical.arbitrary (F.obj (down.obj i))⟩⟩,
  haveI : ∀ i, fintype (F'.obj i) := λ i, fintype.of_equiv (F.obj (down.obj i)) equiv.ulift.symm,
  -- Step 2: apply the bootstrap theorem
  obtain ⟨u, hu⟩ := nonempty_sections_of_fintype_cofiltered_system.init F',
  -- Step 3: interpret the results
  use λ j, (u ⟨j⟩).down,
  intros j j' f,
  have h := @hu (⟨j⟩ : J') (⟨j'⟩ : J') (ulift.up f),
  simp only [as_small.down, functor.comp_map, ulift_functor_map, functor.op_map] at h,
  simp_rw [←h],
  refl,
end

/-- The inverse limit of nonempty finite types is nonempty.

See `nonempty_sections_of_fintype_cofiltered_system` for a generalization to cofiltered limits.
That version applies in almost all cases, and the only difference is that this version
allows `J` to be empty.

This may be regarded as a generalization of Kőnig's lemma.
To specialize: given a locally finite connected graph, take `Jᵒᵖ` to be `ℕ` and
`F j` to be length-`j` paths that start from an arbitrary fixed vertex.
Elements of `F.sections` can be read off as infinite rays in the graph. -/
theorem nonempty_sections_of_fintype_inverse_system
  {J : Type u} [directed_order J] (F : Jᵒᵖ ⥤ Type v)
  [Π (j : Jᵒᵖ), fintype (F.obj j)] [Π (j : Jᵒᵖ), nonempty (F.obj j)] :
  F.sections.nonempty :=
begin
  tactic.unfreeze_local_instances,
  by_cases h : nonempty J,
  { apply nonempty_sections_of_fintype_cofiltered_system, },
  { rw not_nonempty_iff_imp_false at h,
    exact ⟨λ j, false.elim (h j.unop), λ j, false.elim (h j.unop)⟩, },
end

end fintype_konig
