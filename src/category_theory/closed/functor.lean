/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.closed.cartesian
import category_theory.limits.preserves.shapes.binary_products
import category_theory.adjunction.fully_faithful

/-!
# Cartesian closed functors

Define the exponential comparison morphisms for a functor which preserves binary products, and use
them to define a cartesian closed functor: one which (naturally) preserves exponentials.

Define the Frobenius morphism, and show it is an isomorphism iff the exponential comparison is an
isomorphism.

## TODO
Some of the results here are true more generally for closed objects and for closed monoidal
categories, and these could be generalised.

## References
https://ncatlab.org/nlab/show/cartesian+closed+functor
https://ncatlab.org/nlab/show/Frobenius+reciprocity

## Tags
Frobenius reciprocity, cartesian closed functor

-/

namespace category_theory

open category limits cartesian_closed

universes v u u'
variables {C : Type u} [category.{v} C]
variables {D : Type u'} [category.{v} D]

variables [has_finite_products C] [has_finite_products D]

variables (F : C ⥤ D) {L : D ⥤ C}

noncomputable theory

/--
The Frobenius morphism for an adjunction `L ⊣ F` at `A` is given by the morphism

    L(FA ⨯ B) ⟶ LFA ⨯ LB ⟶ A ⨯ LB

natural in `B`, where the first morphism is the product comparison and the latter uses the counit
of the adjunction.

We will show that if `C` and `D` are cartesian closed, then this morphism is an isomorphism for all
`A` iff `F` is a cartesian closed functor, i.e. it preserves exponentials.
-/
def frobenius_morphism (h : L ⊣ F) (A : C) :
  prod.functor.obj (F.obj A) ⋙ L ⟶ L ⋙ prod.functor.obj A :=
prod_comparison_nat_trans L (F.obj A) ≫ whisker_left _ (prod.functor.map (h.counit.app _))

/--
If `F` is full and faithful and has a left adjoint `L` which preserves binary products, then the
Frobenius morphism is an isomorphism.
-/
instance frobenius_morphism_iso_of_preserves_binary_products (h : L ⊣ F) (A : C)
  [preserves_limits_of_shape (discrete walking_pair) L] [full F] [faithful F] :
is_iso (frobenius_morphism F h A) :=
begin
  apply nat_iso.is_iso_of_is_iso_app _,
  intro B,
  dsimp [frobenius_morphism],
  apply_instance,
end

variables [cartesian_closed C] [cartesian_closed D]
variables [preserves_limits_of_shape (discrete walking_pair) F]

/--
The exponential comparison map.
`F` is a cartesian closed functor if this is an iso for all `A`.
-/
def exp_comparison (A : C) :
  exp A ⋙ F ⟶ F ⋙ exp (F.obj A) :=
transfer_nat_trans (exp.adjunction A) (exp.adjunction (F.obj A)) (prod_comparison_nat_iso F A).inv

lemma exp_comparison_ev (A B : C) :
  limits.prod.map (𝟙 (F.obj A)) ((exp_comparison F A).app B) ≫ (ev (F.obj A)).app (F.obj B) =
    inv (prod_comparison F _ _) ≫ F.map ((ev _).app _) :=
begin
  convert transfer_nat_trans_counit _ _ (prod_comparison_nat_iso F A).inv B,
  ext,
  simp,
end

lemma coev_exp_comparison (A B : C) :
  F.map ((coev A).app B) ≫ (exp_comparison F A).app (A ⨯ B) =
      (coev _).app (F.obj B) ≫ (exp (F.obj A)).map (inv (prod_comparison F A B)) :=
begin
  convert unit_transfer_nat_trans _ _ (prod_comparison_nat_iso F A).inv B,
  ext,
  dsimp,
  simp,
end

lemma uncurry_exp_comparison (A B : C) :
  uncurry ((exp_comparison F A).app B) = inv (prod_comparison F _ _) ≫ F.map ((ev _).app _) :=
by rw [uncurry_eq, exp_comparison_ev]

/-- The exponential comparison map is natural in `A`. -/
lemma exp_comparison_whisker_left {A A' : C} (f : A' ⟶ A) :
  exp_comparison F A ≫ whisker_left _ (pre (F.map f)) =
  whisker_right (pre f) _ ≫ exp_comparison F A' :=
begin
  ext B,
  dsimp,
  apply uncurry_injective,
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_exp_comparison, uncurry_pre,
    prod.map_swap_assoc, ←F.map_id, exp_comparison_ev, ←F.map_id,
    ←prod_comparison_inv_natural_assoc, ←prod_comparison_inv_natural_assoc, ←F.map_comp,
    ←F.map_comp, prod_map_pre_app_comp_ev],
end

/--
The functor `F` is cartesian closed (ie preserves exponentials) if each natural transformation
`exp_comparison F A` is an isomorphism
-/
class cartesian_closed_functor :=
(comparison_iso : ∀ A, is_iso (exp_comparison F A))

attribute [instance] cartesian_closed_functor.comparison_iso

lemma frobenius_morphism_mate (h : L ⊣ F) (A : C) :
  transfer_nat_trans_self
    (h.comp _ _ (exp.adjunction A))
    ((exp.adjunction (F.obj A)).comp _ _ h)
    (frobenius_morphism F h A) = exp_comparison F A :=
  begin
    rw ←equiv.eq_symm_apply,
    ext B : 2,
    dsimp [frobenius_morphism, transfer_nat_trans_self, transfer_nat_trans, adjunction.comp],
    simp only [id_comp, comp_id, adjunction.hom_equiv_counit, adjunction.hom_equiv_unit],
    rw [←L.map_comp_assoc, prod.map_id_comp, assoc, uncurry_id_eq_ev, exp_comparison_ev,
      prod.map_id_comp, ← F.map_id, assoc, ←prod_comparison_inv_natural_assoc, ← F.map_comp,
      curry_id_eq_coev, ev_coev, F.map_id (A ⨯ L.obj B), comp_id],
    apply prod.hom_ext,
    { rw [assoc, assoc, ←h.counit_naturality, ←L.map_comp_assoc, assoc,
        inv_prod_comparison_map_fst],
      simp },
    { rw [assoc, assoc, ←h.counit_naturality, ←L.map_comp_assoc, assoc,
        inv_prod_comparison_map_snd],
      simp },
  end

/--
If the exponential comparison transformation (at `A`) is an isomorphism, then the Frobenius morphism
at `A` is an isomorphism.
-/
lemma frobenius_morphism_iso_of_exp_comparison_iso (h : L ⊣ F) (A : C)
  [i : is_iso (exp_comparison F A)] :
  is_iso (frobenius_morphism F h A) :=
begin
  rw ←frobenius_morphism_mate F h at i,
  exact @@transfer_nat_trans_self_of_iso _ _ _ _ _ i,
end

/--
If the Frobenius morphism at `A` is an isomorphism, then the exponential comparison transformation
(at `A`) is an isomorphism.
-/
lemma exp_comparison_iso_of_frobenius_morphism_iso (h : L ⊣ F) (A : C)
  [i : is_iso (frobenius_morphism F h A)] :
  is_iso (exp_comparison F A) :=
by { rw ← frobenius_morphism_mate F h, apply_instance }

/--
If `F` is full and faithful, and has a left adjoint which preserves binary products, then it is
cartesian closed.

TODO: Show the converse, that if `F` is cartesian closed and its left adjoint preserves binary
products, then it is full and faithful.
-/
def cartesian_closed_functor_of_left_adjoint_preserves_binary_products (h : L ⊣ F)
  [full F] [faithful F] [preserves_limits_of_shape (discrete walking_pair) L] :
  cartesian_closed_functor F :=
{ comparison_iso := λ A, exp_comparison_iso_of_frobenius_morphism_iso F h _ }

end category_theory
