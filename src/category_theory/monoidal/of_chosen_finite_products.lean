/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Simon Hudon
-/
import category_theory.monoidal.braided
import category_theory.limits.shapes.binary_products

/-!
# The monoidal structure on a category with chosen finite products.

This is a variant of the development in `category_theory.monoidal.of_has_finite_products`,
which uses specified choices of the terminal object and binary product,
enabling the construction of a cartesian category with specific definitions of the tensor unit
and tensor product.

(Because the construction in `category_theory.monoidal.of_has_finite_products` uses `has_limit`
classes, the actual definitions there are opaque behind `classical.choice`.)

We use this in `category_theory.monoidal.types` to construct the monoidal category of types
so that the tensor product is the usual cartesian product of types.

For now we only do the construction from products, and not from coproducts,
which seems less often useful.
-/

universes v u

noncomputable theory

namespace category_theory

variables (C : Type u) [category.{v} C] {X Y : C}

namespace limits

section
variables {C}

/-- Swap the two sides of a `binary_fan`. -/
def binary_fan.swap {P Q : C} (t : binary_fan P Q) : binary_fan Q P :=
binary_fan.mk t.snd t.fst

@[simp] lemma binary_fan.swap_fst {P Q : C} (t : binary_fan P Q) : t.swap.fst = t.snd := rfl
@[simp] lemma binary_fan.swap_snd {P Q : C} (t : binary_fan P Q) : t.swap.snd = t.fst := rfl

/--
If a cone `t` over `P Q` is a limit cone, then `t.swap` is a limit cone over `Q P`.
-/
@[simps]
def is_limit.swap_binary_fan {P Q : C} {t : binary_fan P Q} (I : is_limit t) : is_limit t.swap :=
{ lift := λ s, I.lift (binary_fan.swap s),
  fac' := λ s, by { rintro ⟨⟩; simp, },
  uniq' := λ s m w,
  begin
    have h := I.uniq (binary_fan.swap s) m,
    rw h,
    intro j,
    specialize w j.swap,
    cases j; exact w,
  end }

/--
Construct `has_binary_product Q P` from `has_binary_product P Q`.
This can't be an instance, as it would cause a loop in typeclass search.
-/
lemma has_binary_product.swap (P Q : C) [has_binary_product P Q] : has_binary_product Q P :=
has_limit.mk ⟨binary_fan.swap (limit.cone (pair P Q)), (limit.is_limit (pair P Q)).swap_binary_fan⟩

/--
Given a limit cone over `X` and `Y`, and another limit cone over `Y` and `X`, we can construct
an isomorphism between the cone points. Relative to some fixed choice of limits cones for every pair,
these isomorphisms constitute a braiding.
-/
def binary_fan.braiding {X Y : C}
  {s : binary_fan X Y} (P : is_limit s) {t : binary_fan Y X} (Q : is_limit t) :
  s.X ≅ t.X :=
is_limit.cone_point_unique_up_to_iso P Q.swap_binary_fan

/--
Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `sXY.X Z`,
if `sYZ` is a limit cone we can construct a binary fan over `X sYZ.X`.

This is an ingredient of building the associator for a cartesian category.
-/
def binary_fan.assoc {X Y Z : C}
  {sXY : binary_fan X Y} {sYZ : binary_fan Y Z} (Q : is_limit sYZ) (s : binary_fan sXY.X Z) :
  binary_fan X sYZ.X :=
binary_fan.mk (s.fst ≫ sXY.fst) (Q.lift (binary_fan.mk (s.fst ≫ sXY.snd) s.snd))

@[simp] lemma binary_fan.assoc_fst {X Y Z : C}
  {sXY : binary_fan X Y} {sYZ : binary_fan Y Z} (Q : is_limit sYZ) (s : binary_fan sXY.X Z) :
  (s.assoc Q).fst = s.fst ≫ sXY.fst := rfl
@[simp] lemma binary_fan.assoc_snd {X Y Z : C}
  {sXY : binary_fan X Y} {sYZ : binary_fan Y Z} (Q : is_limit sYZ) (s : binary_fan sXY.X Z) :
  (s.assoc Q).snd = Q.lift (binary_fan.mk (s.fst ≫ sXY.snd) s.snd) := rfl

/--
Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `X sYZ.X`,
if `sYZ` is a limit cone we can construct a binary fan over `sXY.X Z`.

This is an ingredient of building the associator for a cartesian category.
-/
def binary_fan.assoc_inv {X Y Z : C}
  {sXY : binary_fan X Y} (P : is_limit sXY) {sYZ : binary_fan Y Z} (s : binary_fan X sYZ.X) :
  binary_fan sXY.X Z :=
binary_fan.mk (P.lift (binary_fan.mk s.fst (s.snd ≫ sYZ.fst))) (s.snd ≫ sYZ.snd)

@[simp] lemma binary_fan.assoc_inv_fst {X Y Z : C}
  {sXY : binary_fan X Y} (P : is_limit sXY) {sYZ : binary_fan Y Z} (s : binary_fan X sYZ.X) :
  (s.assoc_inv P).fst = P.lift (binary_fan.mk s.fst (s.snd ≫ sYZ.fst)) := rfl
@[simp] lemma binary_fan.assoc_inv_snd {X Y Z : C}
  {sXY : binary_fan X Y} (P : is_limit sXY) {sYZ : binary_fan Y Z} (s : binary_fan X sYZ.X) :
  (s.assoc_inv P).snd = s.snd ≫ sYZ.snd := rfl

/--
If all the binary fans involved a limit cones, `binary_fan.assoc` produces another limit cone.
-/
@[simps]
def is_limit.assoc {X Y Z : C}
  {sXY : binary_fan X Y} (P : is_limit sXY) {sYZ : binary_fan Y Z} (Q : is_limit sYZ)
  {s : binary_fan sXY.X Z} (R : is_limit s) : is_limit (s.assoc Q) :=
{ lift := λ t, R.lift (binary_fan.assoc_inv P t),
  fac' := λ t,
  begin
    rintro ⟨⟩; simp,
    apply Q.hom_ext,
    rintro ⟨⟩; simp,
  end,
  uniq' := λ t m w,
  begin
    have h := R.uniq (binary_fan.assoc_inv P t) m,
    rw h,
    rintro ⟨⟩; simp,
    apply P.hom_ext,
    rintro ⟨⟩; simp,
    { exact w walking_pair.left, },
    { specialize w walking_pair.right,
      simp at w,
      rw [←w], simp, },
    { specialize w walking_pair.right,
      simp at w,
      rw [←w], simp, },
  end, }

/--
Given two pairs of limit cones corresponding to the parenthesisations of `X × Y × Z`,
we obtain an isomorphism between the cone points.
-/
@[reducible]
def binary_fan.associator {X Y Z : C}
  {sXY : binary_fan X Y} (P : is_limit sXY) {sYZ : binary_fan Y Z} (Q : is_limit sYZ)
  {s : binary_fan sXY.X Z} (R : is_limit s) {t : binary_fan X sYZ.X} (S : is_limit t) :
  s.X ≅ t.X :=
is_limit.cone_point_unique_up_to_iso (is_limit.assoc P Q R) S

/--
Given a fixed family of limit data for every pair `X Y`, we obtain an associator.
-/
@[reducible]
def binary_fan.associator_of_limit_cone
  (L : Π X Y : C, limit_cone (pair X Y)) (X Y Z : C) :
  (L (L X Y).cone.X Z).cone.X ≅ (L X (L Y Z).cone.X).cone.X :=
binary_fan.associator
  (L X Y).is_limit (L Y Z).is_limit
  (L (L X Y).cone.X Z).is_limit (L X (L Y Z).cone.X).is_limit

/--
Construct a left unitor from specified limit cones.
-/
@[simps]
def binary_fan.left_unitor
  {X : C} {s : cone (functor.empty C)} (P : is_limit s) {t : binary_fan s.X X} (Q : is_limit t) :
  t.X ≅ X :=
{ hom := t.snd,
  inv := Q.lift (binary_fan.mk (P.lift { X := X, π := { app := pempty.rec _ } }) (𝟙 X) ),
  hom_inv_id' := by { apply Q.hom_ext, rintro ⟨⟩, { apply P.hom_ext, rintro ⟨⟩, }, { simp, }, }, }

/--
Construct a right unitor from specified limit cones.
-/
@[simps]
def binary_fan.right_unitor
  {X : C} {s : cone (functor.empty C)} (P : is_limit s) {t : binary_fan X s.X} (Q : is_limit t) :
  t.X ≅ X :=
{ hom := t.fst,
  inv := Q.lift (binary_fan.mk (𝟙 X) (P.lift { X := X, π := { app := pempty.rec _ } })),
  hom_inv_id' := by { apply Q.hom_ext, rintro ⟨⟩, { simp, }, { apply P.hom_ext, rintro ⟨⟩, }, }, }

end

end limits

open category_theory.limits

section
local attribute [tidy] tactic.case_bash

variables {C}
variables (𝒯 : limit_cone (functor.empty C))
variables (ℬ : Π (X Y : C), limit_cone (pair X Y))

namespace monoidal_of_chosen_finite_products

/-- Implementation of the tensor product for `monoidal_of_chosen_finite_products`. -/
@[reducible]
def tensor_obj (X Y : C) : C := (ℬ X Y).cone.X

/-- Implementation of the tensor product of morphisms for `monoidal_of_chosen_finite_products`. -/
@[reducible]
def tensor_hom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : tensor_obj ℬ W Y ⟶ tensor_obj ℬ X Z :=
  (binary_fan.is_limit.lift' (ℬ X Z).is_limit
    ((ℬ W Y).cone.π.app walking_pair.left ≫ f)
    (((ℬ W Y).cone.π.app walking_pair.right : (ℬ W Y).cone.X ⟶ Y) ≫ g)).val

lemma tensor_id (X₁ X₂ : C) : tensor_hom ℬ (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensor_obj ℬ X₁ X₂) :=
begin
  apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩;
  { dsimp [tensor_hom], simp, },
end

lemma tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
  tensor_hom ℬ (f₁ ≫ g₁) (f₂ ≫ g₂) =
    tensor_hom ℬ f₁ f₂ ≫ tensor_hom ℬ g₁ g₂ :=
begin
  apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩;
  { dsimp [tensor_hom], simp, },
end

lemma pentagon (W X Y Z : C) :
  tensor_hom ℬ (binary_fan.associator_of_limit_cone ℬ W X Y).hom (𝟙 Z) ≫
    (binary_fan.associator_of_limit_cone ℬ W (tensor_obj ℬ X Y) Z).hom ≫
      tensor_hom ℬ (𝟙 W) (binary_fan.associator_of_limit_cone ℬ X Y Z).hom =
  (binary_fan.associator_of_limit_cone ℬ (tensor_obj ℬ W X) Y Z).hom ≫
    (binary_fan.associator_of_limit_cone ℬ W X (tensor_obj ℬ Y Z)).hom :=
begin
  dsimp [tensor_hom],
  apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩,
  { simp, },
  { apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩,
    { simp, },
    apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩,
    { simp, },
    { simp, }, }
end

lemma triangle (X Y : C) :
  (binary_fan.associator_of_limit_cone ℬ X 𝒯.cone.X Y).hom ≫
    tensor_hom ℬ (𝟙 X) (binary_fan.left_unitor 𝒯.is_limit (ℬ 𝒯.cone.X Y).is_limit).hom =
  tensor_hom ℬ (binary_fan.right_unitor 𝒯.is_limit (ℬ X 𝒯.cone.X).is_limit).hom (𝟙 Y) :=
begin
  dsimp [tensor_hom],
  apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩; simp,
end

lemma left_unitor_naturality {X₁ X₂ : C} (f : X₁ ⟶ X₂) :
  tensor_hom ℬ (𝟙 𝒯.cone.X) f ≫ (binary_fan.left_unitor 𝒯.is_limit (ℬ 𝒯.cone.X X₂).is_limit).hom =
    (binary_fan.left_unitor 𝒯.is_limit (ℬ 𝒯.cone.X X₁).is_limit).hom ≫ f :=
begin
  dsimp [tensor_hom],
  simp,
end

lemma right_unitor_naturality {X₁ X₂ : C} (f : X₁ ⟶ X₂) :
  tensor_hom ℬ f (𝟙 𝒯.cone.X) ≫ (binary_fan.right_unitor 𝒯.is_limit (ℬ X₂ 𝒯.cone.X).is_limit).hom =
    (binary_fan.right_unitor 𝒯.is_limit (ℬ X₁ 𝒯.cone.X).is_limit).hom ≫ f :=
begin
  dsimp [tensor_hom],
  simp,
end

lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
  tensor_hom ℬ (tensor_hom ℬ f₁ f₂) f₃ ≫ (binary_fan.associator_of_limit_cone ℬ Y₁ Y₂ Y₃).hom =
    (binary_fan.associator_of_limit_cone ℬ X₁ X₂ X₃).hom ≫ tensor_hom ℬ f₁ (tensor_hom ℬ f₂ f₃) :=
begin
  dsimp [tensor_hom],
  apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩,
  { simp, },
  { apply is_limit.hom_ext (ℬ _ _).is_limit, rintro ⟨⟩,
    { simp, },
    { simp, }, },
end

end monoidal_of_chosen_finite_products

open monoidal_of_chosen_finite_products

/-- A category with a terminal object and binary products has a natural monoidal structure. -/
def monoidal_of_chosen_finite_products :
  monoidal_category C :=
{ tensor_unit  := 𝒯.cone.X,
  tensor_obj   := λ X Y, tensor_obj ℬ X Y,
  tensor_hom   := λ _ _ _ _ f g, tensor_hom ℬ f g,
  tensor_id'   := tensor_id ℬ,
  tensor_comp' := λ _ _ _ _ _ _ f₁ f₂ g₁ g₂, tensor_comp ℬ f₁ f₂ g₁ g₂,
  associator   := λ X Y Z, binary_fan.associator_of_limit_cone ℬ X Y Z,
  left_unitor  := λ X, binary_fan.left_unitor (𝒯.is_limit) (ℬ 𝒯.cone.X X).is_limit,
  right_unitor := λ X, binary_fan.right_unitor (𝒯.is_limit) (ℬ X 𝒯.cone.X).is_limit,
  pentagon'    := pentagon ℬ,
  triangle'    := triangle 𝒯 ℬ,
  left_unitor_naturality' := λ _ _ f, left_unitor_naturality 𝒯 ℬ f,
  right_unitor_naturality' := λ _ _ f, right_unitor_naturality 𝒯 ℬ f,
  associator_naturality' := λ _ _ _ _ _ _ f₁ f₂ f₃, associator_naturality ℬ f₁ f₂ f₃, }

namespace monoidal_of_chosen_finite_products

open monoidal_category

/--
A type synonym for `C` carrying a monoidal category structure corresponding to
a fixed choice of limit data for the empty functor, and for `pair X Y` for every `X Y : C`.

This is an implementation detail for `symmetric_of_chosen_finite_products`.
-/
@[derive category, nolint unused_arguments has_inhabited_instance]
def monoidal_of_chosen_finite_products_synonym
  (𝒯 : limit_cone (functor.empty C)) (ℬ : Π (X Y : C), limit_cone (pair X Y)):= C

instance : monoidal_category (monoidal_of_chosen_finite_products_synonym 𝒯 ℬ) :=
monoidal_of_chosen_finite_products 𝒯 ℬ

lemma braiding_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
  (tensor_hom ℬ f g) ≫ (limits.binary_fan.braiding (ℬ Y Y').is_limit (ℬ Y' Y).is_limit).hom =
    (limits.binary_fan.braiding (ℬ X X').is_limit (ℬ X' X).is_limit).hom ≫ (tensor_hom ℬ g f) :=
begin
  dsimp [tensor_hom, limits.binary_fan.braiding],
  apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟩;
  { dsimp [limits.is_limit.cone_point_unique_up_to_iso], simp, },
end

lemma hexagon_forward (X Y Z : C) :
  (binary_fan.associator_of_limit_cone ℬ X Y Z).hom ≫
    (limits.binary_fan.braiding (ℬ X (tensor_obj ℬ Y Z)).is_limit (ℬ (tensor_obj ℬ Y Z) X).is_limit).hom ≫
        (binary_fan.associator_of_limit_cone ℬ Y Z X).hom =
    (tensor_hom ℬ (limits.binary_fan.braiding (ℬ X Y).is_limit (ℬ Y X).is_limit).hom (𝟙 Z)) ≫
      (binary_fan.associator_of_limit_cone ℬ Y X Z).hom ≫
        (tensor_hom ℬ (𝟙 Y) (limits.binary_fan.braiding (ℬ X Z).is_limit (ℬ Z X).is_limit).hom) :=
begin
  dsimp [tensor_hom, limits.binary_fan.braiding],
  apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟩,
  { dsimp [limits.is_limit.cone_point_unique_up_to_iso], simp, },
  { apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟩;
    { dsimp [limits.is_limit.cone_point_unique_up_to_iso], simp, }, }
end

lemma hexagon_reverse (X Y Z : C) :
  (binary_fan.associator_of_limit_cone ℬ X Y Z).inv ≫
    (limits.binary_fan.braiding (ℬ (tensor_obj ℬ X Y) Z).is_limit (ℬ Z (tensor_obj ℬ X Y)).is_limit).hom ≫
      (binary_fan.associator_of_limit_cone ℬ Z X Y).inv =
    (tensor_hom ℬ (𝟙 X) (limits.binary_fan.braiding (ℬ Y Z).is_limit (ℬ Z Y).is_limit).hom) ≫
      (binary_fan.associator_of_limit_cone ℬ X Z Y).inv ≫
        (tensor_hom ℬ (limits.binary_fan.braiding (ℬ X Z).is_limit (ℬ Z X).is_limit).hom (𝟙 Y)) :=
begin
  dsimp [tensor_hom, limits.binary_fan.braiding],
  apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟩,
  { apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟩;
    { dsimp [binary_fan.associator_of_limit_cone, binary_fan.associator,
        limits.is_limit.cone_point_unique_up_to_iso],
      simp, }, },
  { dsimp [binary_fan.associator_of_limit_cone, binary_fan.associator,
      limits.is_limit.cone_point_unique_up_to_iso],
    simp, },
end

lemma symmetry (X Y : C) :
  (limits.binary_fan.braiding (ℬ X Y).is_limit (ℬ Y X).is_limit).hom ≫
      (limits.binary_fan.braiding (ℬ Y X).is_limit (ℬ X Y).is_limit).hom =
    𝟙 (tensor_obj ℬ X Y) :=
begin
  dsimp [tensor_hom, limits.binary_fan.braiding],
  apply (ℬ _ _).is_limit.hom_ext, rintro ⟨⟩;
  { dsimp [limits.is_limit.cone_point_unique_up_to_iso], simp, },
end

end monoidal_of_chosen_finite_products

open monoidal_of_chosen_finite_products

/--
The monoidal structure coming from finite products is symmetric.
-/
def symmetric_of_chosen_finite_products :
  symmetric_category (monoidal_of_chosen_finite_products_synonym 𝒯 ℬ) :=
{ braiding := λ X Y, limits.binary_fan.braiding (ℬ _ _).is_limit (ℬ _ _).is_limit,
  braiding_naturality' := λ X X' Y Y' f g, braiding_naturality ℬ f g,
  hexagon_forward' := λ X Y Z, hexagon_forward ℬ X Y Z,
  hexagon_reverse' := λ X Y Z, hexagon_reverse ℬ X Y Z,
  symmetry' := λ X Y, symmetry ℬ X Y, }

end

end category_theory
