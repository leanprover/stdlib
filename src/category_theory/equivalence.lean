/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import category_theory.fully_faithful
import category_theory.full_subcategory
import category_theory.whiskering
import category_theory.essential_image
import tactic.slice

/-!
# Equivalence of categories

An equivalence of categories `C` and `D` is a pair of functors `F : C ⥤ D` and `G : D ⥤ C` such
that `η : 𝟭 C ≅ F ⋙ G` and `ε : G ⋙ F ≅ 𝟭 D`. In many situations, equivalences are a better
notion of "sameness" of categories than the stricter isomorphims of categories.

Recall that one way to express that two functors `F : C ⥤ D` and `G : D ⥤ C` are adjoint is using
two natural transformations `η : 𝟭 C ⟶ F ⋙ G` and `ε : G ⋙ F ⟶ 𝟭 D`, called the unit and the
counit, such that the compositions `F ⟶ FGF ⟶ F` and `G ⟶ GFG ⟶ G` are the identity. Unfortunately,
it is not the case that the natural isomorphisms `η` and `ε` in the definition of an equivalence
automatically give an adjunction. However, it is true that
* if one of the two compositions is the identity, then so is the other, and
* given an equivalence of categories, it is always possible to refine `η` in such a way that the
  identities are satisfied.

For this reason, in mathlib we define an equivalence to be a "half-adjoint equivalence", which is
a tuple `(F, G, η, ε)` as in the first paragraph such that the composite `F ⟶ FGF ⟶ F` is the
identity. By the remark above, this already implies that the tuple is an "adjoint equivalence",
i.e., that the composite `G ⟶ GFG ⟶ G` is also the identity.

We also define essentially surjective functors and show that a functor is an equivalence if and only
if it is full, faithful and essentially surjective.

## Main definitions

* `equivalence`: bundled (half-)adjoint equivalences of categories
* `is_equivalence`: type class on a functor `F` containing the data of the inverse `G` as well as
  the natural isomorphisms `η` and `ε`.
* `ess_surj`: type class on a functor `F` containing the data of the preimages and the isomorphisms
  `F.obj (preimage d) ≅ d`.

## Main results

* `equivalence.mk`: upgrade an equivalence to a (half-)adjoint equivalence
* `equivalence.of_fully_faithfully_ess_surj`: a fully faithful essentially surjective functor is an
  equivalence.

## Notations

We write `C ≌ D` (`\backcong`, not to be confused with `≅`/`\cong`) for a bundled equivalence.

-/

namespace category_theory
open category_theory.functor nat_iso category
-- declare the `v`'s first; see `category_theory.category` for an explanation
universes v₁ v₂ v₃ u₁ u₂ u₃

/-- We define an equivalence as a (half)-adjoint equivalence, a pair of functors with
  a unit and counit which are natural isomorphisms and the triangle law `Fη ≫ εF = 1`, or in other
  words the composite `F ⟶ FGF ⟶ F` is the identity.

  In `unit_inverse_comp`, we show that this is actually an adjoint equivalence, i.e., that the
  composite `G ⟶ GFG ⟶ G` is also the identity.

  The triangle equation is written as a family of equalities between morphisms, it is more
  complicated if we write it as an equality of natural transformations, because then we would have
  to insert natural transformations like `F ⟶ F1`.

See https://stacks.math.columbia.edu/tag/001J
-/
structure equivalence (C : Type u₁) [category.{v₁} C] (D : Type u₂) [category.{v₂} D] :=
mk' ::
(functor : C ⥤ D)
(inverse : D ⥤ C)
(unit_iso   : 𝟭 C ≅ functor ⋙ inverse)
(counit_iso : inverse ⋙ functor ≅ 𝟭 D)
(functor_unit_iso_comp' : ∀(X : C), functor.map ((unit_iso.hom : 𝟭 C ⟶ functor ⋙ inverse).app X) ≫
  counit_iso.hom.app (functor.obj X) = 𝟙 (functor.obj X) . obviously)

restate_axiom equivalence.functor_unit_iso_comp'

infixr ` ≌ `:10  := equivalence

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

namespace equivalence

/-- The unit of an equivalence of categories. -/
abbreviation unit (e : C ≌ D) : 𝟭 C ⟶ e.functor ⋙ e.inverse := e.unit_iso.hom
/-- The counit of an equivalence of categories. -/
abbreviation counit (e : C ≌ D) : e.inverse ⋙ e.functor ⟶ 𝟭 D := e.counit_iso.hom
/-- The inverse of the unit of an equivalence of categories. -/
abbreviation unit_inv (e : C ≌ D) : e.functor ⋙ e.inverse ⟶ 𝟭 C := e.unit_iso.inv
/-- The inverse of the counit of an equivalence of categories. -/
abbreviation counit_inv (e : C ≌ D) : 𝟭 D ⟶ e.inverse ⋙ e.functor := e.counit_iso.inv

/- While these abbreviations are convenient, they also cause some trouble,
preventing structure projections from unfolding. -/
@[simp] lemma equivalence_mk'_unit (functor inverse unit_iso counit_iso f) :
  (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unit = unit_iso.hom := rfl
@[simp] lemma equivalence_mk'_counit (functor inverse unit_iso counit_iso f) :
  (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counit = counit_iso.hom := rfl
@[simp] lemma equivalence_mk'_unit_inv (functor inverse unit_iso counit_iso f) :
  (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unit_inv = unit_iso.inv := rfl
@[simp] lemma equivalence_mk'_counit_inv (functor inverse unit_iso counit_iso f) :
  (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counit_inv = counit_iso.inv := rfl

@[simp] lemma functor_unit_comp (e : C ≌ D) (X : C) :
  e.functor.map (e.unit.app X) ≫ e.counit.app (e.functor.obj X) = 𝟙 (e.functor.obj X) :=
e.functor_unit_iso_comp X

@[simp] lemma counit_inv_functor_comp (e : C ≌ D) (X : C) :
  e.counit_inv.app (e.functor.obj X) ≫ e.functor.map (e.unit_inv.app X) = 𝟙 (e.functor.obj X) :=
begin
  erw [iso.inv_eq_inv
    (e.functor.map_iso (e.unit_iso.app X) ≪≫ e.counit_iso.app (e.functor.obj X)) (iso.refl _)],
  exact e.functor_unit_comp X
end

lemma counit_inv_app_functor (e : C ≌ D) (X : C) :
  e.counit_inv.app (e.functor.obj X) = e.functor.map (e.unit.app X) :=
by { symmetry, erw [←iso.comp_hom_eq_id (e.counit_iso.app _), functor_unit_comp], refl }

lemma counit_app_functor (e : C ≌ D) (X : C) :
  e.counit.app (e.functor.obj X) = e.functor.map (e.unit_inv.app X) :=
by { erw [←iso.hom_comp_eq_id (e.functor.map_iso (e.unit_iso.app X)), functor_unit_comp], refl }

/-- The other triangle equality. The proof follows the following proof in Globular:
  http://globular.science/1905.001 -/
@[simp] lemma unit_inverse_comp (e : C ≌ D) (Y : D) :
  e.unit.app (e.inverse.obj Y) ≫ e.inverse.map (e.counit.app Y) = 𝟙 (e.inverse.obj Y) :=
begin
  rw [←id_comp (e.inverse.map _), ←map_id e.inverse, ←counit_inv_functor_comp, map_comp,
      ←iso.hom_inv_id_assoc (e.unit_iso.app _) (e.inverse.map (e.functor.map _)),
      app_hom, app_inv],
  slice_lhs 2 3 { erw [e.unit.naturality] },
  slice_lhs 1 2 { erw [e.unit.naturality] },
  slice_lhs 4 4
  { rw [←iso.hom_inv_id_assoc (e.inverse.map_iso (e.counit_iso.app _)) (e.unit_inv.app _)] },
  slice_lhs 3 4 { erw [←map_comp e.inverse, e.counit.naturality],
    erw [(e.counit_iso.app _).hom_inv_id, map_id] }, erw [id_comp],
  slice_lhs 2 3 { erw [←map_comp e.inverse, e.counit_iso.inv.naturality, map_comp] },
  slice_lhs 3 4 { erw [e.unit_inv.naturality] },
  slice_lhs 4 5 { erw [←map_comp (e.functor ⋙ e.inverse), (e.unit_iso.app _).hom_inv_id, map_id] },
  erw [id_comp],
  slice_lhs 3 4 { erw [←e.unit_inv.naturality] },
  slice_lhs 2 3 { erw [←map_comp e.inverse, ←e.counit_iso.inv.naturality,
    (e.counit_iso.app _).hom_inv_id, map_id] }, erw [id_comp, (e.unit_iso.app _).hom_inv_id], refl
end

@[simp] lemma inverse_counit_inv_comp (e : C ≌ D) (Y : D) :
  e.inverse.map (e.counit_inv.app Y) ≫ e.unit_inv.app (e.inverse.obj Y) = 𝟙 (e.inverse.obj Y) :=
begin
  erw [iso.inv_eq_inv
    (e.unit_iso.app (e.inverse.obj Y) ≪≫ e.inverse.map_iso (e.counit_iso.app Y)) (iso.refl _)],
  exact e.unit_inverse_comp Y
end

lemma unit_app_inverse (e : C ≌ D) (Y : D) :
  e.unit.app (e.inverse.obj Y) = e.inverse.map (e.counit_inv.app Y) :=
by { erw [←iso.comp_hom_eq_id (e.inverse.map_iso (e.counit_iso.app Y)), unit_inverse_comp], refl }

lemma unit_inv_app_inverse (e : C ≌ D) (Y : D) :
  e.unit_inv.app (e.inverse.obj Y) = e.inverse.map (e.counit.app Y) :=
by { symmetry, erw [←iso.hom_comp_eq_id (e.unit_iso.app _), unit_inverse_comp], refl }

@[simp] lemma fun_inv_map (e : C ≌ D) (X Y : D) (f : X ⟶ Y) :
  e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counit_inv.app Y :=
(nat_iso.naturality_2 (e.counit_iso) f).symm

@[simp] lemma inv_fun_map (e : C ≌ D) (X Y : C) (f : X ⟶ Y) :
  e.inverse.map (e.functor.map f) = e.unit_inv.app X ≫ f ≫ e.unit.app Y :=
(nat_iso.naturality_1 (e.unit_iso) f).symm

section
-- In this section we convert an arbitrary equivalence to a half-adjoint equivalence.
variables {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)

/-- If `η : 𝟭 C ≅ F ⋙ G` is part of a (not necessarily half-adjoint) equivalence, we can upgrade it
to a refined natural isomorphism `adjointify_η η : 𝟭 C ≅ F ⋙ G` which exhibits the properties
required for a half-adjoint equivalence. See `equivalence.mk`. -/
def adjointify_η : 𝟭 C ≅ F ⋙ G :=
calc
  𝟭 C ≅ F ⋙ G               : η
  ... ≅ F ⋙ (𝟭 D ⋙ G)      : iso_whisker_left F (left_unitor G).symm
  ... ≅ F ⋙ ((G ⋙ F) ⋙ G) : iso_whisker_left F (iso_whisker_right ε.symm G)
  ... ≅ F ⋙ (G ⋙ (F ⋙ G)) : iso_whisker_left F (associator G F G)
  ... ≅ (F ⋙ G) ⋙ (F ⋙ G) : (associator F G (F ⋙ G)).symm
  ... ≅ 𝟭 C ⋙ (F ⋙ G)      : iso_whisker_right η.symm (F ⋙ G)
  ... ≅ F ⋙ G               : left_unitor (F ⋙ G)

lemma adjointify_η_ε (X : C) :
  F.map ((adjointify_η η ε).hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 (F.obj X) :=
begin
  dsimp [adjointify_η], simp,
  have := ε.hom.naturality (F.map (η.inv.app X)), dsimp at this, rw [this], clear this,
  rw [←assoc _ _ (F.map _)],
  have := ε.hom.naturality (ε.inv.app $ F.obj X), dsimp at this, rw [this], clear this,
  have := (ε.app $ F.obj X).hom_inv_id, dsimp at this, rw [this], clear this,
  rw [id_comp], have := (F.map_iso $ η.app X).hom_inv_id, dsimp at this, rw [this]
end

end

/-- Every equivalence of categories consisting of functors `F` and `G` such that `F ⋙ G` and
    `G ⋙ F` are naturally isomorphic to identity functors can be transformed into a half-adjoint
    equivalence without changing `F` or `G`. -/
protected definition mk (F : C ⥤ D) (G : D ⥤ C)
  (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : C ≌ D :=
⟨F, G, adjointify_η η ε, ε, adjointify_η_ε η ε⟩

/-- Equivalence of categories is reflexive. -/
@[refl, simps] def refl : C ≌ C :=
⟨𝟭 C, 𝟭 C, iso.refl _, iso.refl _, λ X, category.id_comp _⟩

instance : inhabited (C ≌ C) :=
⟨refl⟩

/-- Equivalence of categories is symmetric. -/
@[symm, simps] def symm (e : C ≌ D) : D ≌ C :=
⟨e.inverse, e.functor, e.counit_iso.symm, e.unit_iso.symm, e.inverse_counit_inv_comp⟩

variables {E : Type u₃} [category.{v₃} E]

/-- Equivalence of categories is transitive. -/
@[trans, simps] def trans (e : C ≌ D) (f : D ≌ E) : C ≌ E :=
{ functor := e.functor ⋙ f.functor,
  inverse := f.inverse ⋙ e.inverse,
  unit_iso :=
  begin
    refine iso.trans e.unit_iso _,
    exact iso_whisker_left e.functor (iso_whisker_right f.unit_iso e.inverse) ,
  end,
  counit_iso :=
  begin
    refine iso.trans _ f.counit_iso,
    exact iso_whisker_left f.inverse (iso_whisker_right e.counit_iso f.functor)
  end,
  -- We wouldn't have needed to give this proof if we'd used `equivalence.mk`,
  -- but we choose to avoid using that here, for the sake of good structure projection `simp`
  -- lemmas.
  functor_unit_iso_comp' := λ X,
  begin
    dsimp,
    rw [← f.functor.map_comp_assoc, e.functor.map_comp, ←counit_inv_app_functor, fun_inv_map,
        iso.inv_hom_id_app_assoc, assoc, iso.inv_hom_id_app, counit_app_functor,
        ← functor.map_comp],
    erw [comp_id, iso.hom_inv_id_app, functor.map_id],
  end }

/-- Composing a functor with both functors of an equivalence yields a naturally isomorphic
functor. -/
def fun_inv_id_assoc (e : C ≌ D) (F : C ⥤ E) : e.functor ⋙ e.inverse ⋙ F ≅ F :=
(functor.associator _ _ _).symm ≪≫ iso_whisker_right e.unit_iso.symm F ≪≫ F.left_unitor

@[simp] lemma fun_inv_id_assoc_hom_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
  (fun_inv_id_assoc e F).hom.app X = F.map (e.unit_inv.app X) :=
by { dsimp [fun_inv_id_assoc], tidy }

@[simp] lemma fun_inv_id_assoc_inv_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
  (fun_inv_id_assoc e F).inv.app X = F.map (e.unit.app X) :=
by { dsimp [fun_inv_id_assoc], tidy }

/-- Composing a functor with both functors of an equivalence yields a naturally isomorphic
functor. -/
def inv_fun_id_assoc (e : C ≌ D) (F : D ⥤ E) : e.inverse ⋙ e.functor ⋙ F ≅ F :=
(functor.associator _ _ _).symm ≪≫ iso_whisker_right e.counit_iso F ≪≫ F.left_unitor

@[simp] lemma inv_fun_id_assoc_hom_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
  (inv_fun_id_assoc e F).hom.app X = F.map (e.counit.app X) :=
by { dsimp [inv_fun_id_assoc], tidy }

@[simp] lemma inv_fun_id_assoc_inv_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
  (inv_fun_id_assoc e F).inv.app X = F.map (e.counit_inv.app X) :=
by { dsimp [inv_fun_id_assoc], tidy }

/-- If `C` is equivalent to `D`, then `C ⥤ E` is equivalent to `D ⥤ E`. -/
@[simps functor inverse unit_iso counit_iso]
def congr_left (e : C ≌ D) : (C ⥤ E) ≌ (D ⥤ E) :=
equivalence.mk
  ((whiskering_left _ _ _).obj e.inverse)
  ((whiskering_left _ _ _).obj e.functor)
  (nat_iso.of_components (λ F, (e.fun_inv_id_assoc F).symm) (by tidy))
  (nat_iso.of_components (λ F, e.inv_fun_id_assoc F) (by tidy))

/-- If `C` is equivalent to `D`, then `E ⥤ C` is equivalent to `E ⥤ D`. -/
@[simps functor inverse unit_iso counit_iso]
def congr_right (e : C ≌ D) : (E ⥤ C) ≌ (E ⥤ D) :=
equivalence.mk
  ((whiskering_right _ _ _).obj e.functor)
  ((whiskering_right _ _ _).obj e.inverse)
  (nat_iso.of_components
    (λ F, F.right_unitor.symm ≪≫ iso_whisker_left F e.unit_iso ≪≫ functor.associator _ _ _)
    (by tidy))
  (nat_iso.of_components
    (λ F, functor.associator _ _ _ ≪≫ iso_whisker_left F e.counit_iso ≪≫ F.right_unitor)
    (by tidy))

section cancellation_lemmas
variables (e : C ≌ D)

/- We need special forms of `cancel_nat_iso_hom_right(_assoc)` and
`cancel_nat_iso_inv_right(_assoc)` for units and counits, because neither `simp` or `rw` will apply
those lemmas in this setting without providing `e.unit_iso` (or similar) as an explicit argument.
We also provide the lemmas for length four compositions, since they're occasionally useful.
(e.g. in proving that equivalences take monos to monos) -/

@[simp] lemma cancel_unit_right {X Y : C}
  (f f' : X ⟶ Y) :
  f ≫ e.unit.app Y = f' ≫ e.unit.app Y ↔ f = f' :=
by simp only [cancel_mono]

@[simp] lemma cancel_unit_inv_right {X Y : C}
  (f f' : X ⟶ e.inverse.obj (e.functor.obj Y))   :
  f ≫ e.unit_inv.app Y = f' ≫ e.unit_inv.app Y ↔ f = f' :=
by simp only [cancel_mono]

@[simp] lemma cancel_counit_right {X Y : D}
  (f f' : X ⟶ e.functor.obj (e.inverse.obj Y))   :
  f ≫ e.counit.app Y = f' ≫ e.counit.app Y ↔ f = f' :=
by simp only [cancel_mono]

@[simp] lemma cancel_counit_inv_right {X Y : D}
  (f f' : X ⟶ Y) :
  f ≫ e.counit_inv.app Y = f' ≫ e.counit_inv.app Y ↔ f = f' :=
by simp only [cancel_mono]

@[simp] lemma cancel_unit_right_assoc {W X X' Y : C}
  (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) :
  f ≫ g ≫ e.unit.app Y = f' ≫ g' ≫ e.unit.app Y ↔ f ≫ g = f' ≫ g' :=
by simp only [←category.assoc, cancel_mono]

@[simp] lemma cancel_counit_inv_right_assoc {W X X' Y : D}
  (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) :
  f ≫ g ≫ e.counit_inv.app Y = f' ≫ g' ≫ e.counit_inv.app Y ↔ f ≫ g = f' ≫ g' :=
by simp only [←category.assoc, cancel_mono]

@[simp] lemma cancel_unit_right_assoc' {W X X' Y Y' Z : C}
  (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
  f ≫ g ≫ h ≫ e.unit.app Z = f' ≫ g' ≫ h' ≫ e.unit.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' :=
by simp only [←category.assoc, cancel_mono]

@[simp] lemma cancel_counit_inv_right_assoc' {W X X' Y Y' Z : D}
  (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
  f ≫ g ≫ h ≫ e.counit_inv.app Z = f' ≫ g' ≫ h' ≫ e.counit_inv.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' :=
by simp only [←category.assoc, cancel_mono]

end cancellation_lemmas

section

-- There's of course a monoid structure on `C ≌ C`,
-- but let's not encourage using it.
-- The power structure is nevertheless useful.

/-- Natural number powers of an auto-equivalence.  Use `(^)` instead. -/
def pow_nat (e : C ≌ C) : ℕ → (C ≌ C)
| 0 := equivalence.refl
| 1 := e
| (n+2) := e.trans (pow_nat (n+1))

/-- Powers of an auto-equivalence.  Use `(^)` instead. -/
def pow (e : C ≌ C) : ℤ → (C ≌ C)
| (int.of_nat n) := e.pow_nat n
| (int.neg_succ_of_nat n) := e.symm.pow_nat (n+1)

instance : has_pow (C ≌ C) ℤ := ⟨pow⟩

@[simp] lemma pow_zero (e : C ≌ C) : e^(0 : ℤ) = equivalence.refl := rfl
@[simp] lemma pow_one (e : C ≌ C) : e^(1 : ℤ) = e := rfl
@[simp] lemma pow_neg_one (e : C ≌ C) : e^(-1 : ℤ) = e.symm := rfl

-- TODO as necessary, add the natural isomorphisms `(e^a).trans e^b ≅ e^(a+b)`.
-- At this point, we haven't even defined the category of equivalences.

end

end equivalence


/-- A functor that is part of a (half) adjoint equivalence -/
class is_equivalence (F : C ⥤ D) :=
mk' ::
(inverse    : D ⥤ C)
(unit_iso   : 𝟭 C ≅ F ⋙ inverse)
(counit_iso : inverse ⋙ F ≅ 𝟭 D)
(functor_unit_iso_comp' : ∀ (X : C), F.map ((unit_iso.hom : 𝟭 C ⟶ F ⋙ inverse).app X) ≫
  counit_iso.hom.app (F.obj X) = 𝟙 (F.obj X) . obviously)

restate_axiom is_equivalence.functor_unit_iso_comp'

namespace is_equivalence

instance of_equivalence (F : C ≌ D) : is_equivalence F.functor :=
{ ..F }

instance of_equivalence_inverse (F : C ≌ D) : is_equivalence F.inverse :=
is_equivalence.of_equivalence F.symm

open equivalence
/-- To see that a functor is an equivalence, it suffices to provide an inverse functor `G` such that
    `F ⋙ G` and `G ⋙ F` are naturally isomorphic to identity functors. -/
protected definition mk {F : C ⥤ D} (G : D ⥤ C)
  (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : is_equivalence F :=
⟨G, adjointify_η η ε, ε, adjointify_η_ε η ε⟩

end is_equivalence


namespace functor

/-- Interpret a functor that is an equivalence as an equivalence. -/
def as_equivalence (F : C ⥤ D) [is_equivalence F] : C ≌ D :=
⟨F, is_equivalence.inverse F, is_equivalence.unit_iso, is_equivalence.counit_iso,
  is_equivalence.functor_unit_iso_comp⟩

instance is_equivalence_refl : is_equivalence (𝟭 C) :=
is_equivalence.of_equivalence equivalence.refl

/-- The inverse functor of a functor that is an equivalence. -/
def inv (F : C ⥤ D) [is_equivalence F] : D ⥤ C :=
is_equivalence.inverse F

instance is_equivalence_inv (F : C ⥤ D) [is_equivalence F] : is_equivalence F.inv :=
is_equivalence.of_equivalence F.as_equivalence.symm

@[simp] lemma as_equivalence_functor (F : C ⥤ D) [is_equivalence F] :
  F.as_equivalence.functor = F := rfl

@[simp] lemma as_equivalence_inverse (F : C ⥤ D) [is_equivalence F] :
  F.as_equivalence.inverse = inv F := rfl

@[simp] lemma inv_inv (F : C ⥤ D) [is_equivalence F] :
  inv (inv F) = F := rfl

variables {E : Type u₃} [category.{v₃} E]

instance is_equivalence_trans (F : C ⥤ D) (G : D ⥤ E) [is_equivalence F] [is_equivalence G] :
  is_equivalence (F ⋙ G) :=
is_equivalence.of_equivalence (equivalence.trans (as_equivalence F) (as_equivalence G))

end functor

namespace equivalence

@[simp]
lemma functor_inv (E : C ≌ D) : E.functor.inv = E.inverse := rfl

@[simp]
lemma inverse_inv (E : C ≌ D) : E.inverse.inv = E.functor := rfl

@[simp]
lemma functor_as_equivalence (E : C ≌ D) : E.functor.as_equivalence = E :=
by { cases E, congr, }

@[simp]
lemma inverse_as_equivalence (E : C ≌ D) : E.inverse.as_equivalence = E.symm :=
by { cases E, congr, }

end equivalence

namespace is_equivalence

@[simp] lemma fun_inv_map (F : C ⥤ D) [is_equivalence F] (X Y : D) (f : X ⟶ Y) :
  F.map (F.inv.map f) = F.as_equivalence.counit.app X ≫ f ≫ F.as_equivalence.counit_inv.app Y :=
begin
  erw [nat_iso.naturality_2],
  refl
end
@[simp] lemma inv_fun_map (F : C ⥤ D) [is_equivalence F] (X Y : C) (f : X ⟶ Y) :
  F.inv.map (F.map f) = F.as_equivalence.unit_inv.app X ≫ f ≫ F.as_equivalence.unit.app Y :=
begin
  erw [nat_iso.naturality_1],
  refl
end

end is_equivalence

namespace equivalence

/--
An equivalence is essentially surjective.

See https://stacks.math.columbia.edu/tag/02C3.
-/
lemma ess_surj_of_equivalence (F : C ⥤ D) [is_equivalence F] : ess_surj F :=
⟨λ Y, ⟨F.inv.obj Y, ⟨F.as_equivalence.counit_iso.app Y⟩⟩⟩

/--
An equivalence is faithful.

See https://stacks.math.columbia.edu/tag/02C3.
-/
@[priority 100] -- see Note [lower instance priority]
instance faithful_of_equivalence (F : C ⥤ D) [is_equivalence F] : faithful F :=
{ map_injective' := λ X Y f g w,
  begin
    have p := congr_arg (@category_theory.functor.map _ _ _ _ F.inv _ _) w,
    simpa only [cancel_epi, cancel_mono, is_equivalence.inv_fun_map] using p
  end }.

/--
An equivalence is full.

See https://stacks.math.columbia.edu/tag/02C3.
-/
@[priority 100] -- see Note [lower instance priority]
instance full_of_equivalence (F : C ⥤ D) [is_equivalence F] : full F :=
{ preimage := λ X Y f, F.as_equivalence.unit.app X ≫ F.inv.map f ≫ F.as_equivalence.unit_inv.app Y,
  witness' := λ X Y f, F.inv.map_injective $
  by simpa only [is_equivalence.inv_fun_map, assoc, iso.inv_hom_id_app_assoc, iso.inv_hom_id_app]
    using comp_id _ }

@[simps] private noncomputable def equivalence_inverse (F : C ⥤ D) [full F] [faithful F]
  [ess_surj F] : D ⥤ C :=
{ obj  := λ X, F.obj_preimage X,
  map := λ X Y f, F.preimage ((F.obj_obj_preimage_iso X).hom ≫ f ≫ (F.obj_obj_preimage_iso Y).inv),
  map_id' := λ X, begin apply F.map_injective, tidy end,
  map_comp' := λ X Y Z f g, by apply F.map_injective; simp }

/--
A functor which is full, faithful, and essentially surjective is an equivalence.

See https://stacks.math.columbia.edu/tag/02C3.
-/
noncomputable def of_fully_faithfully_ess_surj
  (F : C ⥤ D) [full F] [faithful F] [ess_surj F] : is_equivalence F :=
is_equivalence.mk (equivalence_inverse F)
  (nat_iso.of_components
    (λ X, (preimage_iso $ F.obj_obj_preimage_iso $ F.obj X).symm)
    (λ X Y f, by { apply F.map_injective, obviously }))
  (nat_iso.of_components F.obj_obj_preimage_iso (by tidy))

@[simp] lemma functor_map_inj_iff (e : C ≌ D) {X Y : C} (f g : X ⟶ Y) :
  e.functor.map f = e.functor.map g ↔ f = g :=
⟨λ h, e.functor.map_injective h, λ h, h ▸ rfl⟩

@[simp] lemma inverse_map_inj_iff (e : C ≌ D) {X Y : D} (f g : X ⟶ Y) :
  e.inverse.map f = e.inverse.map g ↔ f = g :=
functor_map_inj_iff e.symm f g

instance ess_surj_induced_functor {C' : Type*} (e : C' ≃ D) : ess_surj (induced_functor e) :=
{ mem_ess_image := λ Y, ⟨e.symm Y, by simp⟩, }

noncomputable
instance induced_functor_of_equiv {C' : Type*} (e : C' ≃ D) : is_equivalence (induced_functor e) :=
equivalence.of_fully_faithfully_ess_surj _

end equivalence

section partial_order
variables {α β : Type*} [partial_order α] [partial_order β]

/--
A categorical equivalence between partial orders is just an order isomorphism.
-/
def equivalence.to_order_iso (e : α ≌ β) : α ≃o β :=
{ to_fun := e.functor.obj,
  inv_fun := e.inverse.obj,
  left_inv := λ a, (e.unit_iso.app a).to_eq.symm,
  right_inv := λ b, (e.counit_iso.app b).to_eq,
  map_rel_iff' := λ a a',
    ⟨λ h, ((equivalence.unit e).app a ≫ e.inverse.map h.hom ≫ (equivalence.unit_inv e).app a').le,
     λ (h : a ≤ a'), (e.functor.map h.hom).le⟩, }

-- `@[simps]` on `equivalence.to_order_iso` produces lemmas that fail the `simp_nf` linter,
-- so we provide them by hand:
@[simp]
lemma equivalence.to_order_iso_apply (e : α ≌ β) (a : α) :
  e.to_order_iso a = e.functor.obj a := rfl

@[simp]
lemma equivalence.to_order_iso_symm_apply (e : α ≌ β) (b : β) :
  e.to_order_iso.symm b = e.inverse.obj b := rfl

end partial_order

end category_theory
