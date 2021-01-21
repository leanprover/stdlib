/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.monad.limits
import category_theory.monad.coequalizer

/-!
# Monadicity theorems

We prove monadicity theorems which can establish a given functor is monadic. In particular, we
show three versions of Beck's monadicity theorem, and the reflexive (crude) monadicity theorem:

`G` is a monadic right adjoint if it has a right adjoint, and:

* `D` has, `G` preserves and reflects `G`-split coequalizers, see
  `category_theory.monad.monadic_of_has_preserves_reflects_G_split_coequalizers`
* `G` creates `G`-split coequalizers, see
  `category_theory.monad.monadic_of_creates_G_split_coequalizers`
  (The converse of this is also shown, see
   `category_theory.monad.creates_G_split_coequalizers_of_monadic`)
* `D` has and `G` preserves `G`-split coequalizers, and `G` reflects isomorphisms, see
  `category_theory.monad.monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms`
* `D` has and `G` preserves reflexive coequalizers, and `G` reflects isomorphisms, see
  `category_theory.monad.monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms`

## Tags

Beck, monadicity, descent

## TODO

Dualise to show comonadicity theorems.
-/
universes v₁ v₂ u₁ u₂

namespace category_theory
namespace monad
open limits

noncomputable theory
-- Hide the implementation details in this namespace.
namespace monadicity_internal

section

-- We use these parameters and notations to simplify the statements of internal constructions
-- here.
parameters {C : Type u₁} {D : Type u₂}
parameters [category.{v₁} C] [category.{v₁} D]
parameters {G : D ⥤ C} [is_right_adjoint G]

local notation `F` := left_adjoint G
local notation `adj` := adjunction.of_right_adjoint G

/--
The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
reflexive pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_reflexive (A : algebra (F ⋙ G)) :
  is_reflexive_pair (F .map A.a) (adj .counit.app (F .obj A.A)) :=
begin
  apply is_reflexive_pair.mk' (F .map (adj .unit.app _)) _ _,
  { rw [← F .map_comp, ← F .map_id],
    exact congr_arg (λ _, F .map _) A.unit },
  { rw adj .left_triangle_components,
    refl },
end

/--
The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
`G`-split pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_G_split (A : algebra (F ⋙ G)) :
  G.is_split_pair (F .map A.a) (adj .counit.app (F .obj A.A)) :=
{ splittable := ⟨_, _, ⟨beck_split_coequalizer A⟩⟩ }

/-- The object function for the left adjoint to the comparison functor. -/
def comparison_left_adjoint_obj
  (A : algebra (F ⋙ G)) [has_coequalizer (F .map A.a) (adj .counit.app _)] : D :=
coequalizer (F .map A.a) (adj .counit.app _)

/--
We have a bijection of homsets which will be used to construct the left adjoint to the comparison
functor.
-/
@[simps]
def comparison_left_adjoint_hom_equiv (A : algebra (F ⋙ G)) (B : D)
  [has_coequalizer (F .map A.a) (adj .counit.app (F .obj A.A))] :
  (comparison_left_adjoint_obj A ⟶ B) ≃ (A ⟶ (comparison G).obj B) :=
calc (comparison_left_adjoint_obj A ⟶ B) ≃ {f : F .obj A.A ⟶ B // _} :
        cofork.is_colimit.hom_iso (colimit.is_colimit _) B
     ... ≃ {g : A.A ⟶ G.obj B // G.map (F .map g) ≫ G.map (adj .counit.app B) = A.a ≫ g} :
      begin
        refine (adj .hom_equiv _ _).subtype_congr _,
        intro f,
        rw [← (adj .hom_equiv _ _).injective.eq_iff, adjunction.hom_equiv_naturality_left,
            adj .hom_equiv_unit, adj .hom_equiv_unit, G.map_comp],
        dsimp,
        rw [adj .right_triangle_components_assoc, ← G.map_comp, F .map_comp, category.assoc,
            adj .counit_naturality, adj .left_triangle_components_assoc],
        apply eq_comm,
      end
     ... ≃ (A ⟶ (comparison G).obj B) :
     { to_fun := λ g, { f := _, h' := g.prop },
       inv_fun := λ f, ⟨f.f, f.h⟩,
       left_inv := λ g, begin ext, refl end,
       right_inv := λ f, begin ext, refl end }

/--
Construct the adjunction to the comparison functor.
-/
def left_adjoint_comparison
  [∀ (A : algebra (F ⋙ G)), has_coequalizer (F .map A.a) (adj .counit.app (F .obj A.A))] :
  algebra (F ⋙ G) ⥤ D :=
begin
  refine @adjunction.left_adjoint_of_equiv _ _ _ _
              (comparison G) (λ A, comparison_left_adjoint_obj A) (λ A B, _) _,
  { apply comparison_left_adjoint_hom_equiv },
  { intros A B B' g h,
    ext1,
    dsimp [comparison_left_adjoint_hom_equiv],
    rw [← adj .hom_equiv_naturality_right, category.assoc] },
end

/--
Provided we have the appropriate coequalizers, we have an adjunction to the comparison functor.
-/
@[simps counit]
def comparison_adjunction
  [∀ (A : algebra (F ⋙ G)), has_coequalizer (F .map A.a) (adj .counit.app (F .obj A.A))] :
  left_adjoint_comparison ⊣ comparison G :=
adjunction.adjunction_of_equiv_left _ _

lemma comparison_adjunction_unit_f_aux
  [∀ (A : algebra (F ⋙ G)), has_coequalizer (F .map A.a) (adj .counit.app (F .obj A.A))]
  (A : algebra (F ⋙ G)) :
  (comparison_adjunction.unit.app A).f =
    adj .hom_equiv A.A _ (coequalizer.π (F .map A.a) (adj .counit.app (F .obj A.A))) :=
congr_arg (adj .hom_equiv _ _) (category.comp_id _)

/--
This is a cofork which is helpful for establishing monadicity: the morphism from the Beck
coequalizer to this cofork is the unit for the adjunction on the comparison functor.
-/
@[simps]
def unit_cofork (A : algebra (F ⋙ G))
  [has_coequalizer (F .map A.a) (adj .counit.app (F .obj A.A))] :
  cofork (G.map (F .map A.a)) (G.map (adj .counit.app (F .obj A.A))) :=
cofork.of_π (G.map (coequalizer.π (F .map A.a) (adj .counit.app (F .obj A.A))))
begin
  change _ = G.map _ ≫ _,
  rw [← G.map_comp, coequalizer.condition, G.map_comp],
end

lemma comparison_adjunction_unit_f
  [∀ (A : algebra (F ⋙ G)), has_coequalizer (F .map A.a) (adj .counit.app (F .obj A.A))]
  (A : algebra (F ⋙ G)) :
  (comparison_adjunction.unit.app A).f =
    (beck_coequalizer A).desc (unit_cofork A) :=
begin
  apply limits.cofork.is_colimit.hom_ext (beck_coequalizer A),
  rw is_colimit.fac,
  dsimp only [cofork.π_eq_app_one, beck_cofork_ι_app, unit_cofork_ι_app],
  rw [comparison_adjunction_unit_f_aux, ← adj .hom_equiv_naturality_left A.a, coequalizer.condition,
      adj .hom_equiv_naturality_right, adj .hom_equiv_unit, category.assoc],
  apply adj .right_triangle_components_assoc,
end

/--
The cofork which describes the counit of the adjunction: the morphism from the coequalizer of
this pair to this morphism is the counit.
-/
@[simps]
def counit_cofork (B : D) :
  cofork (F .map (G.map (adj .counit.app B))) (adj .counit.app (F .obj (G.obj B))) :=
cofork.of_π (adj .counit.app B) (adj .counit_naturality _)

/-- The unit cofork is a colimit provided `G` preserves it.  -/
def unit_colimit_of_preserves_coequalizer
  (A : algebra (F ⋙ G)) [has_coequalizer (F .map A.a) (adj .counit.app (F .obj A.A))]
  [preserves_colimit (parallel_pair (F .map A.a) (adj .counit.app (F .obj A.A))) G] :
  is_colimit (unit_cofork A) :=
is_colimit_of_has_coequalizer_of_preserves_colimit G _ _

/-- The counit cofork is a colimit provided `G` reflects it. -/
def counit_coequalizer_of_reflects_coequalizer (B : D)
  [reflects_colimit (parallel_pair
                          (F .map (G.map (adj .counit.app B)))
                          (adj .counit.app (F .obj (G.obj B)))) G] :
  is_colimit (counit_cofork B) :=
is_colimit_of_is_colimit_cofork_map G _ (beck_coequalizer ((comparison G).obj B))

lemma comparison_adjunction_counit_app
  [∀ (A : algebra (F ⋙ G)), has_coequalizer (F .map A.a) (adj .counit.app (F .obj A.A))] (B : D) :
  comparison_adjunction.counit.app B = colimit.desc _ (counit_cofork B) :=
begin
  apply coequalizer.hom_ext,
  change coequalizer.π _ _ ≫ coequalizer.desc ((adj .hom_equiv _ B).symm (𝟙 _)) _ =
         coequalizer.π _ _ ≫ coequalizer.desc _ _,
  simp,
end

end
end monadicity_internal

open monadicity_internal
variables {C : Type u₁} {D : Type u₂}
variables [category.{v₁} C] [category.{v₁} D]
variables (G : D ⥤ C)

/--
If `G` is monadic, it creates colimits of `G`-split pairs. This is the "boring" direction of Beck's
monadicity theorem, the converse is given in `monadic_of_creates_G_split_coequalizers`.
-/
def creates_G_split_coequalizers_of_monadic [monadic_right_adjoint G] ⦃A B⦄ (f g : A ⟶ B)
  [G.is_split_pair f g] :
  creates_colimit (parallel_pair f g) G :=
begin
  apply monadic_creates_colimit_of_preserves_colimit _ _,
  apply_instance,
  { apply preserves_colimit_of_iso_diagram _ (diagram_iso_parallel_pair _).symm,
    dsimp,
    apply_instance },
  { apply preserves_colimit_of_iso_diagram _ (diagram_iso_parallel_pair _).symm,
    dsimp,
    apply_instance }
end

variables [is_right_adjoint G]

section beck_monadicity

/--
To show `G` is a monadic right adjoint, we can show it preserves and reflects `G`-split
coequalizers, and `C` has them.
-/
def monadic_of_has_preserves_reflects_G_split_coequalizers
  [∀ ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g], has_coequalizer f g]
  [∀ ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g], preserves_colimit (parallel_pair f g) G]
  [∀ ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g], reflects_colimit (parallel_pair f g) G] :
  monadic_right_adjoint G :=
begin
  let L : algebra (left_adjoint G ⋙ G) ⥤ D := left_adjoint_comparison,
  letI i : is_right_adjoint (comparison G) := ⟨_, comparison_adjunction⟩,
  constructor,
  let : Π (X : algebra (left_adjoint G ⋙ G)),
    is_iso ((adjunction.of_right_adjoint (comparison G)).unit.app X),
  { intro X,
    apply is_iso_of_reflects_iso _ (monad.forget (left_adjoint G ⋙ G)),
    { change is_iso (comparison_adjunction.unit.app X).f,
      rw comparison_adjunction_unit_f,
      change
        is_iso
          (is_colimit.cocone_point_unique_up_to_iso
            (beck_coequalizer X)
            (unit_colimit_of_preserves_coequalizer X)).hom,
      refine is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso _ _) } },
  let : Π (Y : D),
    is_iso ((adjunction.of_right_adjoint (comparison G)).counit.app Y),
  { intro Y,
    change is_iso (comparison_adjunction.counit.app Y),
    rw comparison_adjunction_counit_app,
    change is_iso (is_colimit.cocone_point_unique_up_to_iso _ _).hom,
    apply_instance,
    apply counit_coequalizer_of_reflects_coequalizer _,
    letI : G.is_split_pair
            ((left_adjoint G).map (G.map ((adjunction.of_right_adjoint G).counit.app Y)))
            ((adjunction.of_right_adjoint G).counit.app ((left_adjoint G).obj (G.obj Y))) :=
      monadicity_internal.main_pair_G_split ((comparison G).obj Y),
    apply_instance },
  exactI adjunction.is_right_adjoint_to_is_equivalence,
end

/--
Beck's monadicity theorem. If `G` has a right adjoint and creates coequalizers of `G`-split pairs,
then it is monadic.
This is the converse of `creates_G_split_of_monadic`.
-/
def monadic_of_creates_G_split_coequalizers
  [∀ ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g], creates_colimit (parallel_pair f g) G] :
  monadic_right_adjoint G :=
begin
  letI : ∀ ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g], has_colimit (parallel_pair f g ⋙ G),
  { introsI A B f g i,
    apply has_colimit_of_iso (diagram_iso_parallel_pair _),
    change has_coequalizer (G.map f) (G.map g),
    apply_instance },
  apply monadic_of_has_preserves_reflects_G_split_coequalizers _,
  { apply_instance },
  { introsI A B f g i,
    apply has_colimit_of_created (parallel_pair f g) G },
  { introsI A B f g i,
    apply_instance },
  { introsI A B f g i,
    apply_instance }
end

/--
An alternate version of Beck's monadicity theorem. If `G` reflects isomorphisms, preserves
coequalizers of `G`-split pairs and `C` has coequalizers of `G`-split pairs, then it is monadic.
-/
def monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms
  [reflects_isomorphisms G]
  [∀ ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g], has_coequalizer f g]
  [∀ ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g], preserves_colimit (parallel_pair f g) G] :
  monadic_right_adjoint G :=
begin
  apply monadic_of_has_preserves_reflects_G_split_coequalizers _,
  { apply_instance },
  { assumption },
  { assumption },
  { introsI A B f g i,
    apply reflects_colimit_of_reflects_isomorphisms },
end

end beck_monadicity

section reflexive_monadicity

variables [has_reflexive_coequalizers D] [reflects_isomorphisms G]
variables [∀ ⦃A B⦄ (f g : A ⟶ B) [is_reflexive_pair f g], preserves_colimit (parallel_pair f g) G]

/--
Reflexive (crude) monadicity theorem. If `G` has a right adjoint, `D` has and `G` preserves
reflexive coequalizers and `G` reflects isomorphisms, then `G` is monadic.
-/
def monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms :
  monadic_right_adjoint G :=
begin
  let L : algebra (left_adjoint G ⋙ G) ⥤ D := left_adjoint_comparison,
  letI i : is_right_adjoint (comparison G) := ⟨_, comparison_adjunction⟩,
  constructor,
  let : Π (X : algebra (left_adjoint G ⋙ G)),
    is_iso ((adjunction.of_right_adjoint (comparison G)).unit.app X),
  { intro X,
    apply is_iso_of_reflects_iso _ (monad.forget (left_adjoint G ⋙ G)),
    { change is_iso (comparison_adjunction.unit.app X).f,
      rw comparison_adjunction_unit_f,
      change
        is_iso
          (is_colimit.cocone_point_unique_up_to_iso
            (beck_coequalizer X)
            (unit_colimit_of_preserves_coequalizer X)).hom,
      apply is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso _ _) } },
  let : Π (Y : D),
    is_iso ((adjunction.of_right_adjoint (comparison G)).counit.app Y),
  { intro Y,
    change is_iso (comparison_adjunction.counit.app Y),
    rw comparison_adjunction_counit_app,
    change is_iso (is_colimit.cocone_point_unique_up_to_iso _ _).hom,
    apply_instance,
    apply counit_coequalizer_of_reflects_coequalizer _,
    apply reflects_colimit_of_reflects_isomorphisms },
  exactI adjunction.is_right_adjoint_to_is_equivalence,
end

end reflexive_monadicity

end monad

end category_theory
