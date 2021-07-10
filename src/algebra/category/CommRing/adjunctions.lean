/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import algebra.category.CommRing.basic
import data.mv_polynomial

/-!
Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/

noncomputable theory

universe u

open mv_polynomial
open category_theory

namespace CommRing

open_locale classical

/--
The free functor `Type u ⥤ CommRing` sending a type `X` to the multivariable (commutative)
polynomials with variables `x : X`.
-/
def free : Type u ⥤ CommRing.{u} :=
{ obj := λ α, of (mv_polynomial α ℤ),
  map := λ X Y f,
    (↑(rename f : _ →ₐ[ℤ] _) : (mv_polynomial X ℤ →+* mv_polynomial Y ℤ)),
  -- TODO these next two fields can be done by `tidy`, but the calls in `dsimp` and `simp` it
  -- generates are too slow.
  map_id' := λ X, ring_hom.ext $ rename_id,
  map_comp' := λ X Y Z f g, ring_hom.ext $ λ p, (rename_rename f g p).symm }

@[simp] lemma free_obj_coe {α : Type u} :
  (free.obj α : Type u) = mv_polynomial α ℤ := rfl

@[simp] lemma free_map_coe {α β : Type u} {f : α → β} :
  ⇑(free.map f) = rename f := rfl

/--
The free-forgetful adjunction for commutative rings.
-/
def adj : free ⊣ forget CommRing.{u} :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X R, hom_equiv,
  hom_equiv_naturality_left_symm' :=
    λ _ _ Y f g, ring_hom.ext $ λ x, eval₂_cast_comp f (int.cast_ring_hom Y) g x }

instance : is_right_adjoint (forget CommRing.{u}) := ⟨_, adj⟩

end CommRing
