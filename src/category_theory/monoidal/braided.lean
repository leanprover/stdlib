/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.discrete

/-!
# Braided and symmetric monoidal categories

The basic definitions of braided monoidal categories, and symmetric monoidal categories,
as well as braided functors.

## Implementation note

We make `braided_monoidal_category` another typeclass, but then have `symmetric_monoidal_category`
extend this. The rationale is that we are not carrying any additional data,
just requiring a property.

## Future work

* Construct the Drinfeld center of a monoidal category as a braided monoidal category.
* Say something about pseudo-natural transformations.

-/

open category_theory

universes v v₁ v₂ v₃ u u₁ u₂ u₃

namespace category_theory

/--
A braided monoidal category is a monoidal category equipped with a braiding isomorphism
`β_ X Y : X ⊗ Y ≅ Y ⊗ X`
which is natural in both arguments,
and also satisfies the two hexagon identities.
-/
class braided_category (C : Type u) [category.{v} C] [monoidal_category.{v} C] :=
-- braiding natural iso:
(braiding             : Π X Y : C, X ⊗ Y ≅ Y ⊗ X)
(braiding_naturality' : ∀ {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
  (f ⊗ g) ≫ (braiding Y Y').hom = (braiding X X').hom ≫ (g ⊗ f) . obviously)
-- hexagon identities:
(hexagon_forward'     : Π X Y Z : C,
    (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom
  = ((braiding X Y).hom ⊗ (𝟙 Z)) ≫ (α_ Y X Z).hom ≫ ((𝟙 Y) ⊗ (braiding X Z).hom)
  . obviously)
(hexagon_reverse'     : Π X Y Z : C,
    (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv
  = ((𝟙 X) ⊗ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ⊗ (𝟙 Y))
  . obviously)

restate_axiom braided_category.braiding_naturality'
attribute [simp,reassoc] braided_category.braiding_naturality
restate_axiom braided_category.hexagon_forward'
restate_axiom braided_category.hexagon_reverse'

open category
open monoidal_category
open braided_category

notation `β_` := braiding

section
/-!
We now establish how the braiding interacts with the unitors.

I couldn't find a detailed proof in print, but this is discussed in:

* Proposition 1 of André Joyal and Ross Street,
  "Braided monoidal categories", Macquarie Math Reports 860081 (1986).
* Proposition 2.1 of André Joyal and Ross Street,
  "Braided tensor categories" , Adv. Math. 102 (1993), 20–78.
* Exercise 8.1.6 of Etingof, Gelaki, Nikshych, Ostrik,
  "Tensor categories", vol 25, Mathematical Surveys and Monographs (2015), AMS.
-/

variables (C : Type u₁) [category.{v₁} C] [monoidal_category C] [braided_category C]

lemma braiding_left_unitor_aux₁ (X : C) :
  (α_ (𝟙_ C) (𝟙_ C) X).hom ≫ (𝟙 _ ⊗ (β_ X (𝟙_ C)).inv) ≫ (α_ _ X _).inv ≫ ((λ_ X).hom ⊗ 𝟙 _) =
  ((λ_ _).hom ⊗ 𝟙 X) ≫ (β_ X _).inv :=
by { rw [←left_unitor_tensor, left_unitor_naturality], simp, }

lemma braiding_left_unitor_aux₂ (X : C) :
  ((β_ X (𝟙_ C)).hom ⊗ (𝟙 (𝟙_ C))) ≫ ((λ_ X).hom ⊗ (𝟙 (𝟙_ C))) = (ρ_ X).hom ⊗ (𝟙 (𝟙_ C)) :=
calc ((β_ X (𝟙_ C)).hom ⊗ (𝟙 (𝟙_ C))) ≫ ((λ_ X).hom ⊗ (𝟙 (𝟙_ C)))
    = ((β_ X (𝟙_ C)).hom ⊗ (𝟙 (𝟙_ C))) ≫ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫ ((λ_ X).hom ⊗ (𝟙 (𝟙_ C)))
         : by simp
... = ((β_ X (𝟙_ C)).hom ⊗ (𝟙 (𝟙_ C))) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (β_ X _).hom) ≫
        (𝟙 _ ⊗ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫ ((λ_ X).hom ⊗ (𝟙 (𝟙_ C)))
         : by { slice_rhs 3 4 { rw [←id_tensor_comp, iso.hom_inv_id, tensor_id], }, rw [id_comp], }
... = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫
        (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫ ((λ_ X).hom ⊗ (𝟙 (𝟙_ C)))
         : by { slice_lhs 1 3 { rw ←hexagon_forward }, simp only [assoc], }
... = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ ((λ_ _).hom ⊗ 𝟙 X) ≫ (β_ X _).inv
         : by rw braiding_left_unitor_aux₁
... = (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (λ_ _).hom) ≫ (β_ _ _).hom ≫ (β_ X _).inv
         : by { slice_lhs 2 3 { rw [←braiding_naturality] }, simp only [assoc], }
... = (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (λ_ _).hom)
         : by rw [iso.hom_inv_id, comp_id]
... = (ρ_ X).hom ⊗ (𝟙 (𝟙_ C))
         : by rw triangle

@[simp]
lemma braiding_left_unitor (X : C) : (β_ X (𝟙_ C)).hom ≫ (λ_ X).hom = (ρ_ X).hom :=
by rw [←tensor_right_iff, comp_tensor_id, braiding_left_unitor_aux₂]

lemma braiding_right_unitor_aux₁ (X : C) :
  (α_ X (𝟙_ C) (𝟙_ C)).inv ≫ ((β_ (𝟙_ C) X).inv ⊗ 𝟙 _) ≫ (α_ _ X _).hom ≫ (𝟙 _ ⊗ (ρ_ X).hom) =
  (𝟙 X ⊗ (ρ_ _).hom) ≫ (β_ _ X).inv :=
by { rw [←right_unitor_tensor, right_unitor_naturality], simp, }

lemma braiding_right_unitor_aux₂ (X : C) :
  ((𝟙 (𝟙_ C)) ⊗ (β_ (𝟙_ C) X).hom) ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ X).hom) = (𝟙 (𝟙_ C)) ⊗ (λ_ X).hom :=
calc ((𝟙 (𝟙_ C)) ⊗ (β_ (𝟙_ C) X).hom) ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ X).hom)
    = ((𝟙 (𝟙_ C)) ⊗ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ X).hom)
         : by simp
... = ((𝟙 (𝟙_ C)) ⊗ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ ((β_ _ X).hom ⊗ 𝟙 _) ≫
        ((β_ _ X).inv ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ X).hom)
         : by { slice_rhs 3 4 { rw [←comp_tensor_id, iso.hom_inv_id, tensor_id], }, rw [id_comp], }
... = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫
        (α_ _ _ _).inv ≫ ((β_ _ X).inv ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ X).hom)
         : by { slice_lhs 1 3 { rw ←hexagon_reverse }, simp only [assoc], }
... = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (𝟙 X ⊗ (ρ_ _).hom) ≫ (β_ _ X).inv
         : by rw braiding_right_unitor_aux₁
... = (α_ _ _ _).inv ≫ ((ρ_ _).hom ⊗ 𝟙 _) ≫ (β_ _ X).hom ≫ (β_ _ _).inv
         : by { slice_lhs 2 3 { rw [←braiding_naturality] }, simp only [assoc], }
... = (α_ _ _ _).inv ≫ ((ρ_ _).hom ⊗ 𝟙 _)
         : by rw [iso.hom_inv_id, comp_id]
... = (𝟙 (𝟙_ C)) ⊗ (λ_ X).hom
         : by rw [triangle_assoc_comp_right]

@[simp]
lemma braiding_right_unitor (X : C) : (β_ (𝟙_ C) X).hom ≫ (ρ_ X).hom = (λ_ X).hom :=
by rw [←tensor_left_iff, id_tensor_comp, braiding_right_unitor_aux₂]

end

/--
A symmetric monoidal category is a braided monoidal category for which the braiding is symmetric.

See https://stacks.math.columbia.edu/tag/0FFW.
-/
class symmetric_category (C : Type u) [category.{v} C] [monoidal_category.{v} C]
   extends braided_category.{v} C :=
-- braiding symmetric:
(symmetry' : ∀ X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) . obviously)

restate_axiom symmetric_category.symmetry'
attribute [simp,reassoc] symmetric_category.symmetry

variables (C : Type u₁) [category.{v₁} C] [monoidal_category C] [braided_category C]
variables (D : Type u₂) [category.{v₂} D] [monoidal_category D] [braided_category D]
variables (E : Type u₃) [category.{v₃} E] [monoidal_category E] [braided_category E]

/--
A lax braided functor between braided monoidal categories is a lax monoidal functor
which preserves the braiding.
-/
structure lax_braided_functor extends lax_monoidal_functor C D :=
(braided' : ∀ X Y : C, μ X Y ≫ map (β_ X Y).hom = (β_ (obj X) (obj Y)).hom ≫ μ Y X . obviously)

restate_axiom lax_braided_functor.braided'

namespace lax_braided_functor

/-- The identity lax braided monoidal functor. -/
@[simps] def id : lax_braided_functor C C :=
{ .. monoidal_functor.id C }

instance : inhabited (lax_braided_functor C C) := ⟨id C⟩

variables {C D E}

/-- The composition of lax braided monoidal functors. -/
@[simps]
def comp (F : lax_braided_functor C D) (G : lax_braided_functor D E) : lax_braided_functor C E :=
{ braided' := λ X Y,
  begin
    dsimp,
    slice_lhs 2 3 { rw [←category_theory.functor.map_comp, F.braided,
      category_theory.functor.map_comp], },
    slice_lhs 1 2 { rw [G.braided], },
    simp only [category.assoc],
  end,
  ..(lax_monoidal_functor.comp F.to_lax_monoidal_functor G.to_lax_monoidal_functor) }

instance category_lax_braided_functor : category (lax_braided_functor C D) :=
induced_category.category lax_braided_functor.to_lax_monoidal_functor

@[simp] lemma comp_to_nat_trans {F G H : lax_braided_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
  (α ≫ β).to_nat_trans =
    @category_struct.comp (C ⥤ D) _ _ _ _ (α.to_nat_trans) (β.to_nat_trans) := rfl

/--
Interpret a natural isomorphism of the underlyling lax monoidal functors as an
isomorphism of the lax braided monoidal functors.
-/
@[simps]
def mk_iso {F G : lax_braided_functor C D}
  (i : F.to_lax_monoidal_functor ≅ G.to_lax_monoidal_functor) : F ≅ G :=
{ ..i }

end lax_braided_functor

/--
A braided functor between braided monoidal categories is a monoidal functor
which preserves the braiding.
-/
structure braided_functor extends monoidal_functor C D :=
-- Note this is stated different than for `lax_braided_functor`.
-- We move the `μ X Y` to the right hand side,
-- so that this makes a good `@[simp]` lemma.
(braided' : ∀ X Y : C, map (β_ X Y).hom = inv (μ X Y) ≫ (β_ (obj X) (obj Y)).hom ≫ μ Y X . obviously)

restate_axiom braided_functor.braided'
attribute [simp] braided_functor.braided

namespace braided_functor

/-- Turn a braided functor into a lax braided functor. -/
@[simps]
def to_lax_braided_functor (F : braided_functor C D) : lax_braided_functor C D :=
{ braided' := λ X Y, by { rw F.braided, simp, }
  .. F }

/-- The identity braided monoidal functor. -/
@[simps] def id : braided_functor C C :=
{ .. monoidal_functor.id C }

instance : inhabited (braided_functor C C) := ⟨id C⟩

variables {C D E}

/-- The composition of braided monoidal functors. -/
@[simps]
def comp (F : braided_functor C D) (G : braided_functor D E) : braided_functor C E :=
{ ..(monoidal_functor.comp F.to_monoidal_functor G.to_monoidal_functor) }

instance category_braided_functor : category (braided_functor C D) :=
induced_category.category braided_functor.to_monoidal_functor

@[simp] lemma comp_to_nat_trans {F G H : braided_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
  (α ≫ β).to_nat_trans =
    @category_struct.comp (C ⥤ D) _ _ _ _ (α.to_nat_trans) (β.to_nat_trans) := rfl

/--
Interpret a natural isomorphism of the underlyling monoidal functors as an
isomorphism of the braided monoidal functors.
-/
@[simps]
def mk_iso {F G : braided_functor C D}
  (i : F.to_monoidal_functor ≅ G.to_monoidal_functor) : F ≅ G :=
{ ..i }


end braided_functor

section comm_monoid

variables (M : Type u) [comm_monoid M]

instance comm_monoid_discrete : comm_monoid (discrete M) := by { dsimp [discrete], apply_instance }

instance : braided_category (discrete M) :=
{ braiding := λ X Y, eq_to_iso (mul_comm X Y), }

variables {M} {N : Type u} [comm_monoid N]

/--
A multiplicative morphism between commutative monoids gives a braided functor between
the corresponding discrete braided monoidal categories.
-/
@[simps]
def discrete.braided_functor (F : M →* N) : braided_functor (discrete M) (discrete N) :=
{ ..discrete.monoidal_functor F }

end comm_monoid

end category_theory
