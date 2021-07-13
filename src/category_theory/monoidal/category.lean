/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta
-/
import category_theory.products.basic

/-!
# Monoidal categories

A monoidal category is a category equipped with a tensor product, unitors, and an associator.
In the definition, we provide the tensor product as a pair of functions
* `tensor_obj : C → C → C`
* `tensor_hom : (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → ((X₁ ⊗ X₂) ⟶ (Y₁ ⊗ Y₂))`
and allow use of the overloaded notation `⊗` for both.
The unitors and associator are provided componentwise.

The tensor product can be expressed as a functor via `tensor : C × C ⥤ C`.
The unitors and associator are gathered together as natural
isomorphisms in `left_unitor_nat_iso`, `right_unitor_nat_iso` and `associator_nat_iso`.

Some consequences of the definition are proved in other files,
e.g. `(λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom` in `category_theory.monoidal.unitors_equal`.

## Implementation
Dealing with unitors and associators is painful, and at this stage we do not have a useful
implementation of coherence for monoidal categories.

In an effort to lessen the pain, we put some effort into choosing the right `simp` lemmas.
Generally, the rule is that the component index of a natural transformation "weighs more"
in considering the complexity of an expression than does a structural isomorphism (associator, etc).

As an example when we prove Proposition 2.2.4 of
<http://www-math.mit.edu/~etingof/egnobookfinal.pdf>
we state it as a `@[simp]` lemma as
```
(λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ⊗ (𝟙 Y)
```

This is far from completely effective, but seems to prove a useful principle.

## References
* Tensor categories, Etingof, Gelaki, Nikshych, Ostrik,
  http://www-math.mit.edu/~etingof/egnobookfinal.pdf
* https://stacks.math.columbia.edu/tag/0FFK.
-/

open category_theory

universes v u

open category_theory
open category_theory.category
open category_theory.iso

namespace category_theory

/--
In a monoidal category, we can take the tensor product of objects, `X ⊗ Y` and of morphisms `f ⊗ g`.
Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. There is a tensor unit `𝟙_ C`,
with specified left and right unitor isomorphisms `λ_ X : 𝟙_ C ⊗ X ≅ X` and `ρ_ X : X ⊗ 𝟙_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations.

See https://stacks.math.columbia.edu/tag/0FFK.
-/
class monoidal_category (C : Type u) [𝒞 : category.{v} C] :=
-- curried tensor product of objects:
(tensor_obj               : C → C → C)
(infixr ` ⊗ `:70          := tensor_obj) -- This notation is only temporary
-- curried tensor product of morphisms:
(tensor_hom               :
  Π {X₁ Y₁ X₂ Y₂ : C}, (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → ((X₁ ⊗ X₂) ⟶ (Y₁ ⊗ Y₂)))
(infixr ` ⊗' `:69         := tensor_hom) -- This notation is only temporary
-- tensor product laws:
(tensor_id'               :
  ∀ (X₁ X₂ : C), (𝟙 X₁) ⊗' (𝟙 X₂) = 𝟙 (X₁ ⊗ X₂) . obviously)
(tensor_comp'             :
  ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
  (f₁ ≫ g₁) ⊗' (f₂ ≫ g₂) = (f₁ ⊗' f₂) ≫ (g₁ ⊗' g₂) . obviously)
-- tensor unit:
(tensor_unit []           : C)
(notation `𝟙_`            := tensor_unit)
-- associator:
(associator               :
  Π X Y Z : C, (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z))
(notation `α_`            := associator)
(associator_naturality'   :
  ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
  ((f₁ ⊗' f₂) ⊗' f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗' (f₂ ⊗' f₃)) . obviously)
-- left unitor:
(left_unitor              : Π X : C, 𝟙_ ⊗ X ≅ X)
(notation `λ_`            := left_unitor)
(left_unitor_naturality'  :
  ∀ {X Y : C} (f : X ⟶ Y), ((𝟙 𝟙_) ⊗' f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f . obviously)
-- right unitor:
(right_unitor             : Π X : C, X ⊗ 𝟙_ ≅ X)
(notation `ρ_`            := right_unitor)
(right_unitor_naturality' :
  ∀ {X Y : C} (f : X ⟶ Y), (f ⊗' (𝟙 𝟙_)) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f . obviously)
-- pentagon identity:
(pentagon'                : ∀ W X Y Z : C,
  ((α_ W X Y).hom ⊗' (𝟙 Z)) ≫ (α_ W (X ⊗ Y) Z).hom ≫ ((𝟙 W) ⊗' (α_ X Y Z).hom)
  = (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom . obviously)
-- triangle identity:
(triangle'                :
  ∀ X Y : C, (α_ X 𝟙_ Y).hom ≫ ((𝟙 X) ⊗' (λ_ Y).hom) = (ρ_ X).hom ⊗' (𝟙 Y) . obviously)

restate_axiom monoidal_category.tensor_id'
attribute [simp] monoidal_category.tensor_id
restate_axiom monoidal_category.tensor_comp'
attribute [reassoc] monoidal_category.tensor_comp -- This would be redundant in the simp set.
attribute [simp] monoidal_category.tensor_comp
restate_axiom monoidal_category.associator_naturality'
attribute [reassoc] monoidal_category.associator_naturality
restate_axiom monoidal_category.left_unitor_naturality'
attribute [reassoc] monoidal_category.left_unitor_naturality
restate_axiom monoidal_category.right_unitor_naturality'
attribute [reassoc] monoidal_category.right_unitor_naturality
restate_axiom monoidal_category.pentagon'
restate_axiom monoidal_category.triangle'
attribute [reassoc] monoidal_category.pentagon
attribute [simp, reassoc] monoidal_category.triangle

open monoidal_category

infixr ` ⊗ `:70 := tensor_obj
infixr ` ⊗ `:70 := tensor_hom

notation `𝟙_` := tensor_unit
notation `α_` := associator
notation `λ_` := left_unitor
notation `ρ_` := right_unitor

/-- The tensor product of two isomorphisms is an isomorphism. -/
@[simps]
def tensor_iso {C : Type u} {X Y X' Y' : C} [category.{v} C] [monoidal_category.{v} C]
  (f : X ≅ Y) (g : X' ≅ Y') :
    X ⊗ X' ≅ Y ⊗ Y' :=
{ hom := f.hom ⊗ g.hom,
  inv := f.inv ⊗ g.inv,
  hom_inv_id' := by rw [←tensor_comp, iso.hom_inv_id, iso.hom_inv_id, ←tensor_id],
  inv_hom_id' := by rw [←tensor_comp, iso.inv_hom_id, iso.inv_hom_id, ←tensor_id] }

infixr ` ⊗ `:70 := tensor_iso

namespace monoidal_category

section

variables {C : Type u} [category.{v} C] [monoidal_category.{v} C]

instance tensor_is_iso {W X Y Z : C} (f : W ⟶ X) [is_iso f] (g : Y ⟶ Z) [is_iso g] :
  is_iso (f ⊗ g) :=
is_iso.of_iso (as_iso f ⊗ as_iso g)

@[simp] lemma inv_tensor {W X Y Z : C} (f : W ⟶ X) [is_iso f] (g : Y ⟶ Z) [is_iso g] :
  inv (f ⊗ g) = inv f ⊗ inv g :=
by { ext, simp [←tensor_comp], }

variables {U V W X Y Z : C}

-- When `rewrite_search` lands, add @[search] attributes to

-- monoidal_category.tensor_id monoidal_category.tensor_comp monoidal_category.associator_naturality
-- monoidal_category.left_unitor_naturality monoidal_category.right_unitor_naturality
-- monoidal_category.pentagon monoidal_category.triangle

-- tensor_comp_id tensor_id_comp comp_id_tensor_tensor_id
-- triangle_assoc_comp_left triangle_assoc_comp_right
-- triangle_assoc_comp_left_inv triangle_assoc_comp_right_inv
-- left_unitor_tensor left_unitor_tensor_inv
-- right_unitor_tensor right_unitor_tensor_inv
-- pentagon_inv
-- associator_inv_naturality
-- left_unitor_inv_naturality
-- right_unitor_inv_naturality

@[reassoc, simp] lemma comp_tensor_id (f : W ⟶ X) (g : X ⟶ Y) :
  (f ≫ g) ⊗ (𝟙 Z) = (f ⊗ (𝟙 Z)) ≫ (g ⊗ (𝟙 Z)) :=
by { rw ←tensor_comp, simp }

@[reassoc, simp] lemma id_tensor_comp (f : W ⟶ X) (g : X ⟶ Y) :
  (𝟙 Z) ⊗ (f ≫ g) = (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) :=
by { rw ←tensor_comp, simp }

@[simp, reassoc] lemma id_tensor_comp_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) :
  ((𝟙 Y) ⊗ f) ≫ (g ⊗ (𝟙 X)) = g ⊗ f :=
by { rw [←tensor_comp], simp }

@[simp, reassoc] lemma tensor_id_comp_id_tensor (f : W ⟶ X) (g : Y ⟶ Z) :
  (g ⊗ (𝟙 W)) ≫ ((𝟙 Z) ⊗ f) = g ⊗ f :=
by { rw [←tensor_comp], simp }

@[reassoc]
lemma left_unitor_inv_naturality {X X' : C} (f : X ⟶ X') :
  f ≫ (λ_ X').inv = (λ_ X).inv ≫ (𝟙 _ ⊗ f) :=
begin
  apply (cancel_mono (λ_ X').hom).1,
  simp only [assoc, comp_id, iso.inv_hom_id],
  rw [left_unitor_naturality, ←category.assoc, iso.inv_hom_id, category.id_comp]
end

@[reassoc]
lemma right_unitor_inv_naturality {X X' : C} (f : X ⟶ X') :
  f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ (f ⊗ 𝟙 _) :=
begin
  apply (cancel_mono (ρ_ X').hom).1,
  simp only [assoc, comp_id, iso.inv_hom_id],
  rw [right_unitor_naturality, ←category.assoc, iso.inv_hom_id, category.id_comp]
end

@[simp]
lemma right_unitor_conjugation {X Y : C} (f : X ⟶ Y) :
  (ρ_ X).inv ≫ (f ⊗ (𝟙 (𝟙_ C))) ≫ (ρ_ Y).hom = f :=
by rw [right_unitor_naturality, ←category.assoc, iso.inv_hom_id, category.id_comp]

@[simp]
lemma left_unitor_conjugation {X Y : C} (f : X ⟶ Y) :
  (λ_ X).inv ≫ ((𝟙 (𝟙_ C)) ⊗ f) ≫ (λ_ Y).hom = f :=
by rw [left_unitor_naturality, ←category.assoc, iso.inv_hom_id, category.id_comp]

@[simp] lemma tensor_left_iff
  {X Y : C} (f g : X ⟶ Y) :
  ((𝟙 (𝟙_ C)) ⊗ f = (𝟙 (𝟙_ C)) ⊗ g) ↔ (f = g) :=
by { rw [←cancel_mono (λ_ Y).hom, left_unitor_naturality, left_unitor_naturality], simp }

@[simp] lemma tensor_right_iff
  {X Y : C} (f g : X ⟶ Y) :
  (f ⊗ (𝟙 (𝟙_ C)) = g ⊗ (𝟙 (𝟙_ C))) ↔ (f = g) :=
by { rw [←cancel_mono (ρ_ Y).hom, right_unitor_naturality, right_unitor_naturality], simp }

-- See Proposition 2.2.4 of <http://www-math.mit.edu/~etingof/egnobookfinal.pdf>
@[reassoc]
lemma left_unitor_tensor' (X Y : C) :
  ((α_ (𝟙_ C) X Y).hom) ≫ ((λ_ (X ⊗ Y)).hom) = ((λ_ X).hom ⊗ (𝟙 Y)) :=
by
  rw [←tensor_left_iff, id_tensor_comp, ←cancel_epi (α_ (𝟙_ C) (𝟙_ C ⊗ X) Y).hom,
    ←cancel_epi ((α_ (𝟙_ C) (𝟙_ C) X).hom ⊗ 𝟙 Y), pentagon_assoc, triangle, ←associator_naturality,
    ←comp_tensor_id_assoc, triangle, associator_naturality, tensor_id]

@[simp]
lemma left_unitor_tensor (X Y : C) :
  ((λ_ (X ⊗ Y)).hom) = ((α_ (𝟙_ C) X Y).inv) ≫ ((λ_ X).hom ⊗ (𝟙 Y)) :=
by { rw [←left_unitor_tensor'], simp }

lemma left_unitor_tensor_inv' (X Y : C) :
  ((λ_ (X ⊗ Y)).inv) ≫ ((α_ (𝟙_ C) X Y).inv) = ((λ_ X).inv ⊗ (𝟙 Y)) :=
eq_of_inv_eq_inv (by simp)

@[reassoc, simp]
lemma left_unitor_tensor_inv (X Y : C) :
  (λ_ (X ⊗ Y)).inv = ((λ_ X).inv ⊗ (𝟙 Y)) ≫ (α_ (𝟙_ C) X Y).hom :=
by { rw [←left_unitor_tensor_inv'], simp }

@[simp]
lemma right_unitor_tensor (X Y : C) :
  (ρ_ (X ⊗ Y)).hom = (α_ X Y (𝟙_ C)).hom ≫ ((𝟙 X) ⊗ (ρ_ Y).hom) :=
by
  rw [←tensor_right_iff, comp_tensor_id, ←cancel_mono (α_ X Y (𝟙_ C)).hom, assoc,
      associator_naturality, ←triangle_assoc, ←triangle, id_tensor_comp, pentagon_assoc,
      ←associator_naturality, tensor_id]

@[reassoc, simp]
lemma right_unitor_tensor_inv (X Y : C) :
  ((ρ_ (X ⊗ Y)).inv) = ((𝟙 X) ⊗ (ρ_ Y).inv) ≫ ((α_ X Y (𝟙_ C)).inv) :=
eq_of_inv_eq_inv (by simp)

@[reassoc]
lemma associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
  (f ⊗ (g ⊗ h)) ≫ (α_ X' Y' Z').inv = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) :=
by { rw [comp_inv_eq, assoc, associator_naturality], simp }

@[reassoc]
lemma id_tensor_associator_naturality {X Y Z Z' : C} (h : Z ⟶ Z') :
  (𝟙 (X ⊗ Y) ⊗ h) ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ (𝟙 X ⊗ (𝟙 Y ⊗ h)) :=
by { rw [←tensor_id, associator_naturality], }

@[reassoc]
lemma id_tensor_associator_inv_naturality {X Y Z X' : C} (f : X ⟶ X')  :
  (f ⊗ 𝟙 (Y ⊗ Z)) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ ((f ⊗ 𝟙 Y) ⊗ 𝟙 Z) :=
by { rw [←tensor_id, associator_inv_naturality] }

@[reassoc]
lemma pentagon_inv (W X Y Z : C) :
  ((𝟙 W) ⊗ (α_ X Y Z).inv) ≫ (α_ W (X ⊗ Y) Z).inv ≫ ((α_ W X Y).inv ⊗ (𝟙 Z))
    = (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv :=
category_theory.eq_of_inv_eq_inv (by simp [pentagon])

lemma triangle_assoc_comp_left (X Y : C) :
  (α_ X (𝟙_ C) Y).hom ≫ ((𝟙 X) ⊗ (λ_ Y).hom) = (ρ_ X).hom ⊗ 𝟙 Y :=
monoidal_category.triangle X Y

@[simp, reassoc] lemma triangle_assoc_comp_right (X Y : C) :
  (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ⊗ 𝟙 Y) = ((𝟙 X) ⊗ (λ_ Y).hom) :=
by rw [←triangle_assoc_comp_left, iso.inv_hom_id_assoc]

@[simp, reassoc] lemma triangle_assoc_comp_right_inv (X Y : C) :
  ((ρ_ X).inv ⊗ 𝟙 Y) ≫ (α_ X (𝟙_ C) Y).hom = ((𝟙 X) ⊗ (λ_ Y).inv) :=
begin
  apply (cancel_mono (𝟙 X ⊗ (λ_ Y).hom)).1,
  simp only [assoc, triangle_assoc_comp_left],
  rw [←comp_tensor_id, iso.inv_hom_id, ←id_tensor_comp, iso.inv_hom_id]
end

@[simp, reassoc] lemma triangle_assoc_comp_left_inv (X Y : C) :
  ((𝟙 X) ⊗ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = ((ρ_ X).inv ⊗ 𝟙 Y) :=
begin
  apply (cancel_mono ((ρ_ X).hom ⊗ 𝟙 Y)).1,
  simp only [triangle_assoc_comp_right, assoc],
  rw [←id_tensor_comp, iso.inv_hom_id, ←comp_tensor_id, iso.inv_hom_id]
end

lemma unitors_equal : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
by rw [←tensor_left_iff, ←cancel_epi (α_ (𝟙_ C) (𝟙_ _) (𝟙_ _)).hom, ←cancel_mono (ρ_ (𝟙_ C)).hom,
       triangle, ←right_unitor_tensor, right_unitor_naturality]

lemma unitors_inv_equal : (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv :=
by { ext, simp [←unitors_equal], }

@[simp, reassoc]
lemma hom_inv_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
  (f.hom ⊗ g) ≫ (f.inv ⊗ h) = 𝟙 V ⊗ (g ≫ h) :=
by rw [←tensor_comp, f.hom_inv_id]

@[simp, reassoc]
lemma inv_hom_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
  (f.inv ⊗ g) ≫ (f.hom ⊗ h) = 𝟙 W ⊗ (g ≫ h) :=
by rw [←tensor_comp, f.inv_hom_id]

@[simp, reassoc]
lemma tensor_hom_inv_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
  (g ⊗ f.hom) ≫ (h ⊗ f.inv) = (g ≫ h) ⊗ 𝟙 V :=
by rw [←tensor_comp, f.hom_inv_id]

@[simp, reassoc]
lemma tensor_inv_hom_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
  (g ⊗ f.inv) ≫ (h ⊗ f.hom) = (g ≫ h) ⊗ 𝟙 W :=
by rw [←tensor_comp, f.inv_hom_id]

end

section
variables (C : Type u) [category.{v} C] [monoidal_category.{v} C]

/-- The tensor product expressed as a functor. -/
def tensor : (C × C) ⥤ C :=
{ obj := λ X, X.1 ⊗ X.2,
  map := λ {X Y : C × C} (f : X ⟶ Y), f.1 ⊗ f.2 }

/-- The left-associated triple tensor product as a functor. -/
def left_assoc_tensor : (C × C × C) ⥤ C :=
{ obj := λ X, (X.1 ⊗ X.2.1) ⊗ X.2.2,
  map := λ {X Y : C × C × C} (f : X ⟶ Y), (f.1 ⊗ f.2.1) ⊗ f.2.2 }

@[simp] lemma left_assoc_tensor_obj (X) :
  (left_assoc_tensor C).obj X = (X.1 ⊗ X.2.1) ⊗ X.2.2 := rfl
@[simp] lemma left_assoc_tensor_map {X Y} (f : X ⟶ Y) :
  (left_assoc_tensor C).map f = (f.1 ⊗ f.2.1) ⊗ f.2.2 := rfl

/-- The right-associated triple tensor product as a functor. -/
def right_assoc_tensor : (C × C × C) ⥤ C :=
{ obj := λ X, X.1 ⊗ (X.2.1 ⊗ X.2.2),
  map := λ {X Y : C × C × C} (f : X ⟶ Y), f.1 ⊗ (f.2.1 ⊗ f.2.2) }

@[simp] lemma right_assoc_tensor_obj (X) :
  (right_assoc_tensor C).obj X = X.1 ⊗ (X.2.1 ⊗ X.2.2) := rfl
@[simp] lemma right_assoc_tensor_map {X Y} (f : X ⟶ Y) :
  (right_assoc_tensor C).map f = f.1 ⊗ (f.2.1 ⊗ f.2.2) := rfl

/-- The functor `λ X, 𝟙_ C ⊗ X`. -/
def tensor_unit_left : C ⥤ C :=
{ obj := λ X, 𝟙_ C ⊗ X,
  map := λ {X Y : C} (f : X ⟶ Y), (𝟙 (𝟙_ C)) ⊗ f }
/-- The functor `λ X, X ⊗ 𝟙_ C`. -/
def tensor_unit_right : C ⥤ C :=
{ obj := λ X, X ⊗ 𝟙_ C,
  map := λ {X Y : C} (f : X ⟶ Y), f ⊗ (𝟙 (𝟙_ C)) }

-- We can express the associator and the unitors, given componentwise above,
-- as natural isomorphisms.

/-- The associator as a natural isomorphism. -/
@[simps]
def associator_nat_iso :
  left_assoc_tensor C ≅ right_assoc_tensor C :=
nat_iso.of_components
  (by { intros, apply monoidal_category.associator })
  (by { intros, apply monoidal_category.associator_naturality })

/-- The left unitor as a natural isomorphism. -/
@[simps]
def left_unitor_nat_iso :
  tensor_unit_left C ≅ 𝟭 C :=
nat_iso.of_components
  (by { intros, apply monoidal_category.left_unitor })
  (by { intros, apply monoidal_category.left_unitor_naturality })

/-- The right unitor as a natural isomorphism. -/
@[simps]
def right_unitor_nat_iso :
  tensor_unit_right C ≅ 𝟭 C :=
nat_iso.of_components
  (by { intros, apply monoidal_category.right_unitor })
  (by { intros, apply monoidal_category.right_unitor_naturality })



section
variables {C}

/-- Tensoring on the left with a fixed object, as a functor. -/
@[simps]
def tensor_left (X : C) : C ⥤ C :=
{ obj := λ Y, X ⊗ Y,
  map := λ Y Y' f, (𝟙 X) ⊗ f, }

/--
Tensoring on the left with `X ⊗ Y` is naturally isomorphic to
tensoring on the left with `Y`, and then again with `X`.
-/
def tensor_left_tensor (X Y : C) : tensor_left (X ⊗ Y) ≅ tensor_left Y ⋙ tensor_left X :=
nat_iso.of_components
  (associator _ _)
  (λ Z Z' f, by { dsimp, rw[←tensor_id], apply associator_naturality })

@[simp] lemma tensor_left_tensor_hom_app (X Y Z : C) :
  (tensor_left_tensor X Y).hom.app Z = (associator X Y Z).hom :=
rfl
@[simp] lemma tensor_left_tensor_inv_app (X Y Z : C) :
  (tensor_left_tensor X Y).inv.app Z = (associator X Y Z).inv :=
by { simp [tensor_left_tensor], }

/-- Tensoring on the right with a fixed object, as a functor. -/
@[simps]
def tensor_right (X : C) : C ⥤ C :=
{ obj := λ Y, Y ⊗ X,
  map := λ Y Y' f, f ⊗ (𝟙 X), }

variables (C)

/--
Tensoring on the left, as a functor from `C` into endofunctors of `C`.

TODO: show this is a op-monoidal functor.
-/
@[simps]
def tensoring_left : C ⥤ C ⥤ C :=
{ obj := tensor_left,
  map := λ X Y f,
  { app := λ Z, f ⊗ (𝟙 Z) } }

instance : faithful (tensoring_left C) :=
{ map_injective' := λ X Y f g h,
  begin
    injections with h,
    replace h := congr_fun h (𝟙_ C),
    simpa using h,
  end }

/--
Tensoring on the right, as a functor from `C` into endofunctors of `C`.

We later show this is a monoidal functor.
-/
@[simps]
def tensoring_right : C ⥤ C ⥤ C :=
{ obj := tensor_right,
  map := λ X Y f,
  { app := λ Z, (𝟙 Z) ⊗ f } }

instance : faithful (tensoring_right C) :=
{ map_injective' := λ X Y f g h,
  begin
    injections with h,
    replace h := congr_fun h (𝟙_ C),
    simpa using h,
  end }

variables {C}

/--
Tensoring on the right with `X ⊗ Y` is naturally isomorphic to
tensoring on the right with `X`, and then again with `Y`.
-/
def tensor_right_tensor (X Y : C) : tensor_right (X ⊗ Y) ≅ tensor_right X ⋙ tensor_right Y :=
nat_iso.of_components
  (λ Z, (associator Z X Y).symm)
  (λ Z Z' f, by { dsimp, rw[←tensor_id], apply associator_inv_naturality })

@[simp] lemma tensor_right_tensor_hom_app (X Y Z : C) :
  (tensor_right_tensor X Y).hom.app Z = (associator Z X Y).inv :=
rfl
@[simp] lemma tensor_right_tensor_inv_app (X Y Z : C) :
  (tensor_right_tensor X Y).inv.app Z = (associator Z X Y).hom :=
by simp [tensor_right_tensor]

end

end

end monoidal_category

end category_theory
