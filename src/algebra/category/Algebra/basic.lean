/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.algebra.basic
import algebra.algebra.subalgebra
import algebra.free_algebra
import algebra.category.CommRing.basic
import algebra.category.Module.basic

/-!
# Category instance for algebras over a commutative ring

We introduce the bundled category `Algebra` of algebras over a fixed commutative ring `R ` along
with the forgetful functors to `Ring` and `Module`. We furthermore show that the functor associating
to a type the free `R`-algebra on that type is left adjoint to the forgetful functor.
-/

open category_theory
open category_theory.limits

universes v u

variables (R : Type u) [comm_ring R]

/-- The category of R-algebras and their morphisms. -/
structure Algebra :=
(carrier : Type v)
[is_ring : ring carrier]
[is_algebra : algebra R carrier]

attribute [instance] Algebra.is_ring Algebra.is_algebra

namespace Algebra

instance : has_coe_to_sort (Algebra R) :=
{ S := Type v, coe := Algebra.carrier }

instance : category (Algebra.{v} R) :=
{ hom   := λ A B, A →ₐ[R] B,
  id    := λ A, alg_hom.id R A,
  comp  := λ A B C f g, g.comp f }

instance : concrete_category.{v} (Algebra.{v} R) :=
{ forget := { obj := λ R, R, map := λ R S f, (f : R → S) },
  forget_faithful := { } }

instance has_forget_to_Ring : has_forget₂ (Algebra.{v} R) Ring.{v} :=
{ forget₂ :=
  { obj := λ A, Ring.of A,
    map := λ A₁ A₂ f, alg_hom.to_ring_hom f, } }

instance has_forget_to_Module : has_forget₂ (Algebra.{v} R) (Module.{v} R) :=
{ forget₂ :=
  { obj := λ M, Module.of R M,
    map := λ M₁ M₂ f, alg_hom.to_linear_map f, } }

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (X : Type v) [ring X] [algebra R X] : Algebra.{v} R := ⟨X⟩

instance : inhabited (Algebra R) := ⟨of R R⟩

@[simp]
lemma coe_of (X : Type u) [ring X] [algebra R X] : (of R X : Type u) = X := rfl

variables {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def of_self_iso (M : Algebra.{v} R) : Algebra.of R M ≅ M :=
{ hom := 𝟙 M, inv := 𝟙 M }

variables {R} {M N U : Module.{v} R}

@[simp] lemma id_apply (m : M) : (𝟙 M : M → M) m = m := rfl

@[simp] lemma coe_comp (f : M ⟶ N) (g : N ⟶ U) :
  ((f ≫ g) : M → U) = g ∘ f := rfl

variables (R)
/-- The "free algebra" functor, sending a type `S` to the free algebra on `S`. -/
@[simps]
def free : Type u ⥤ Algebra.{u} R :=
{ obj := λ S,
  { carrier := free_algebra R S,
    is_ring := algebra.semiring_to_ring R },
  map := λ S T f, free_algebra.lift _ $ (free_algebra.ι _) ∘ f,
  -- obviously can fill the next two goals, but it is slow
  map_id' := by { intros X, ext1, simp only [free_algebra.ι_comp_lift], refl },
  map_comp' := by { intros, ext1, simp only [free_algebra.ι_comp_lift], ext1,
    simp only [free_algebra.lift_ι_apply, category_theory.coe_comp, function.comp_app,
      types_comp_apply] } }

/-- The free/forget adjunction for `R`-algebras. -/
def adj : free.{u} R ⊣ forget (Algebra.{u} R) :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X A, (free_algebra.lift _).symm,
  -- Relying on `obviously` to fill out these proofs is very slow :(
  hom_equiv_naturality_left_symm' := by { intros, ext,
    simp only [free_map, equiv.symm_symm, free_algebra.lift_ι_apply, category_theory.coe_comp,
      function.comp_app, types_comp_apply] },
  hom_equiv_naturality_right' := by { intros, ext,
    simp only [forget_map_eq_coe, category_theory.coe_comp, function.comp_app,
      free_algebra.lift_symm_apply, types_comp_apply] } }

instance : is_right_adjoint (forget (Algebra.{u} R)) := ⟨_, adj R⟩

end Algebra

variables {R}
variables {X₁ X₂ : Type u}

/-- Build an isomorphism in the category `Algebra R` from a `alg_equiv` between `algebra`s. -/
@[simps]
def alg_equiv.to_Algebra_iso
  {g₁ : ring X₁} {g₂ : ring X₂} {m₁ : algebra R X₁} {m₂ : algebra R X₂} (e : X₁ ≃ₐ[R] X₂) :
  Algebra.of R X₁ ≅ Algebra.of R X₂ :=
{ hom := (e : X₁ →ₐ[R] X₂),
  inv := (e.symm : X₂ →ₐ[R] X₁),
  hom_inv_id' := begin ext, exact e.left_inv x, end,
  inv_hom_id' := begin ext, exact e.right_inv x, end, }

namespace category_theory.iso

/-- Build a `alg_equiv` from an isomorphism in the category `Algebra R`. -/
@[simps]
def to_alg_equiv {X Y : Algebra R} (i : X ≅ Y) : X ≃ₐ[R] Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_add'  := by tidy,
  map_mul'  := by tidy,
  commutes' := by tidy, }.

end category_theory.iso

/-- Algebra equivalences between `algebras`s are the same as (isomorphic to) isomorphisms in
`Algebra`. -/
@[simps]
def alg_equiv_iso_Algebra_iso {X Y : Type u}
  [ring X] [ring Y] [algebra R X] [algebra R Y] :
  (X ≃ₐ[R] Y) ≅ (Algebra.of R X ≅ Algebra.of R Y) :=
{ hom := λ e, e.to_Algebra_iso,
  inv := λ i, i.to_alg_equiv, }

instance (X : Type u) [ring X] [algebra R X] : has_coe (subalgebra R X) (Algebra R) :=
⟨ λ N, Algebra.of R N ⟩

instance Algebra.forget_reflects_isos : reflects_isomorphisms (forget (Algebra.{u} R)) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget (Algebra.{u} R)).map f),
    let e : X ≃ₐ[R] Y := { ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_Algebra_iso).1⟩,
  end }
