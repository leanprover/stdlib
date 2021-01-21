/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.biproducts
import category_theory.preadditive

/-!
# Basic facts about morphisms between biproducts in preadditive categories.

* In any category (with zero morphisms), if `biprod.map f g` is an isomorphism,
  then both `f` and `g` are isomorphisms.

The remaining lemmas hold in any preadditive category.

* If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
  so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
  via Gaussian elimination.

* As a corollary of the previous two facts,
  if we have an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  we can construct an isomorphism `X₂ ≅ Y₂`.

* If `f : W ⊞ X ⟶ Y ⊞ Z` is an isomorphism, either `𝟙 W = 0`,
  or at least one of the component maps `W ⟶ Y` and `W ⟶ Z` is nonzero.

* If `f : ⨁ S ⟶ ⨁ T` is an isomorphism,
  then every column (corresponding to a nonzero summand in the domain)
  has some nonzero matrix entry.
-/

open category_theory
open category_theory.preadditive
open category_theory.limits

universes v u

noncomputable theory

namespace category_theory

variables {C : Type u} [category.{v} C]
section
variables [has_zero_morphisms.{v} C] [has_binary_biproducts.{v} C]

/--
If
```
(f 0)
(0 g)
```
is invertible, then `f` is invertible.
-/
def is_iso_left_of_is_iso_biprod_map
  {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [is_iso (biprod.map f g)] : is_iso f :=
{ inv := biprod.inl ≫ inv (biprod.map f g) ≫ biprod.fst,
  hom_inv_id' :=
  begin
    have t := congr_arg (λ p : W ⊞ X ⟶ W ⊞ X, biprod.inl ≫ p ≫ biprod.fst)
      (is_iso.hom_inv_id (biprod.map f g)),
    simp only [category.id_comp, category.assoc, biprod.inl_map_assoc] at t,
    simp [t],
  end,
  inv_hom_id' :=
  begin
    have t := congr_arg (λ p : Y ⊞ Z ⟶ Y ⊞ Z, biprod.inl ≫ p ≫ biprod.fst)
      (is_iso.inv_hom_id (biprod.map f g)),
    simp only [category.id_comp, category.assoc, biprod.map_fst] at t,
    simp only [category.assoc],
    simp [t],
  end }

/--
If
```
(f 0)
(0 g)
```
is invertible, then `g` is invertible.
-/
def is_iso_right_of_is_iso_biprod_map
  {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [is_iso (biprod.map f g)] : is_iso g :=
begin
  letI : is_iso (biprod.map g f) := by
  { rw [←biprod.braiding_map_braiding],
    apply_instance, },
  exact is_iso_left_of_is_iso_biprod_map g f,
end

end

section
variables [preadditive.{v} C] [has_binary_biproducts.{v} C]

variables {X₁ X₂ Y₁ Y₂ : C}
variables (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)

/--
The "matrix" morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` with specified components.
-/
def biprod.of_components : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂ :=
biprod.fst ≫ f₁₁ ≫ biprod.inl +
biprod.fst ≫ f₁₂ ≫ biprod.inr +
biprod.snd ≫ f₂₁ ≫ biprod.inl +
biprod.snd ≫ f₂₂ ≫ biprod.inr

@[simp]
lemma biprod.inl_of_components :
  biprod.inl ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ =
    f₁₁ ≫ biprod.inl + f₁₂ ≫ biprod.inr :=
by simp [biprod.of_components]

@[simp]
lemma biprod.inr_of_components :
  biprod.inr ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ =
    f₂₁ ≫ biprod.inl + f₂₂ ≫ biprod.inr :=
by simp [biprod.of_components]

@[simp]
lemma biprod.of_components_fst :
  biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.fst =
    biprod.fst ≫ f₁₁ + biprod.snd ≫ f₂₁ :=
by simp [biprod.of_components]

@[simp]
lemma biprod.of_components_snd :
  biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.snd =
    biprod.fst ≫ f₁₂ + biprod.snd ≫ f₂₂ :=
by simp [biprod.of_components]

@[simp]
lemma biprod.of_components_eq (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) :
  biprod.of_components (biprod.inl ≫ f ≫ biprod.fst) (biprod.inl ≫ f ≫ biprod.snd)
    (biprod.inr ≫ f ≫ biprod.fst) (biprod.inr ≫ f ≫ biprod.snd) = f :=
begin
  ext; simp,
end

@[simp]
lemma biprod.of_components_comp {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
  (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)
  (g₁₁ : Y₁ ⟶ Z₁) (g₁₂ : Y₁ ⟶ Z₂) (g₂₁ : Y₂ ⟶ Z₁) (g₂₂ : Y₂ ⟶ Z₂) :
  biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.of_components g₁₁ g₁₂ g₂₁ g₂₂ =
    biprod.of_components
      (f₁₁ ≫ g₁₁ + f₁₂ ≫ g₂₁) (f₁₁ ≫ g₁₂ + f₁₂ ≫ g₂₂)
      (f₂₁ ≫ g₁₁ + f₂₂ ≫ g₂₁) (f₂₁ ≫ g₁₂ + f₂₂ ≫ g₂₂) :=
begin
  dsimp [biprod.of_components],
  apply biprod.hom_ext; apply biprod.hom_ext';
  simp only [add_comp, comp_add, add_comp_assoc, add_zero, zero_add,
    biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
    biprod.inl_fst_assoc, biprod.inl_snd_assoc, biprod.inr_fst_assoc, biprod.inr_snd_assoc,
    comp_zero, zero_comp,
    category.comp_id, category.assoc],
end

/--
The unipotent upper triangular matrix
```
(1 r)
(0 1)
```
as an isomorphism.
-/
@[simps]
def biprod.unipotent_upper {X₁ X₂ : C} (r : X₁ ⟶ X₂) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ :=
{ hom := biprod.of_components (𝟙 _) r 0 (𝟙 _),
  inv := biprod.of_components (𝟙 _) (-r) 0 (𝟙 _), }

/--
The unipotent lower triangular matrix
```
(1 0)
(r 1)
```
as an isomorphism.
-/
@[simps]
def biprod.unipotent_lower {X₁ X₂ : C} (r : X₂ ⟶ X₁) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ :=
{ hom := biprod.of_components (𝟙 _) 0 r (𝟙 _),
  inv := biprod.of_components (𝟙 _) 0 (-r) (𝟙 _), }

/--
If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
via Gaussian elimination.

(This is the version of `biprod.gaussian` written in terms of components.)
-/
def biprod.gaussian' [is_iso f₁₁] :
  Σ' (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) (g₂₂ : X₂ ⟶ Y₂),
    L.hom ≫ (biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂) ≫ R.hom = biprod.map f₁₁ g₂₂ :=
⟨biprod.unipotent_lower (-(f₂₁ ≫ inv f₁₁)),
 biprod.unipotent_upper (-(inv f₁₁ ≫ f₁₂)),
 f₂₂ - f₂₁ ≫ (inv f₁₁) ≫ f₁₂,
 by ext; simp; abel⟩

/--
If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
via Gaussian elimination.
-/
def biprod.gaussian (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) [is_iso (biprod.inl ≫ f ≫ biprod.fst)] :
  Σ' (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) (g₂₂ : X₂ ⟶ Y₂),
    L.hom ≫ f ≫ R.hom = biprod.map (biprod.inl ≫ f ≫ biprod.fst) g₂₂ :=
begin
  let := biprod.gaussian'
    (biprod.inl ≫ f ≫ biprod.fst) (biprod.inl ≫ f ≫ biprod.snd)
    (biprod.inr ≫ f ≫ biprod.fst) (biprod.inr ≫ f ≫ biprod.snd),
  simpa [biprod.of_components_eq],
end

/--
If `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` via a two-by-two matrix whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def biprod.iso_elim' [is_iso f₁₁] [is_iso (biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂)] : X₂ ≅ Y₂ :=
begin
  obtain ⟨L, R, g, w⟩ := biprod.gaussian' f₁₁ f₁₂ f₂₁ f₂₂,
  letI : is_iso (biprod.map f₁₁ g) := by { rw ←w, apply_instance, },
  letI : is_iso g := (is_iso_right_of_is_iso_biprod_map f₁₁ g),
  exact as_iso g,
end

/--
If `f` is an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def biprod.iso_elim (f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂) [is_iso (biprod.inl ≫ f.hom ≫ biprod.fst)] : X₂ ≅ Y₂ :=
begin
  letI : is_iso (biprod.of_components
       (biprod.inl ≫ f.hom ≫ biprod.fst)
       (biprod.inl ≫ f.hom ≫ biprod.snd)
       (biprod.inr ≫ f.hom ≫ biprod.fst)
       (biprod.inr ≫ f.hom ≫ biprod.snd)) :=
  by { simp only [biprod.of_components_eq], apply_instance, },
  exact biprod.iso_elim'
    (biprod.inl ≫ f.hom ≫ biprod.fst)
    (biprod.inl ≫ f.hom ≫ biprod.snd)
    (biprod.inr ≫ f.hom ≫ biprod.fst)
    (biprod.inr ≫ f.hom ≫ biprod.snd)
end

lemma biprod.column_nonzero_of_iso {W X Y Z : C}
  (f : W ⊞ X ⟶ Y ⊞ Z) [is_iso f] :
  𝟙 W = 0 ∨ biprod.inl ≫ f ≫ biprod.fst ≠ 0 ∨ biprod.inl ≫ f ≫ biprod.snd ≠ 0 :=
begin
  by_contradiction,
  rw [not_or_distrib, not_or_distrib, not_not, not_not] at h,
  rcases h with ⟨nz, a₁, a₂⟩,
  set x := biprod.inl ≫ f ≫ inv f ≫ biprod.fst,
  have h₁ : x = 𝟙 W, by simp [x],
  have h₀ : x = 0,
  { dsimp [x],
    rw [←category.id_comp (inv f), category.assoc, ←biprod.total],
    conv_lhs { slice 2 3, rw [comp_add], },
    simp only [category.assoc],
    rw [comp_add_assoc, add_comp],
    conv_lhs { congr, skip, slice 1 3, rw a₂, },
    simp only [zero_comp, add_zero],
    conv_lhs { slice 1 3, rw a₁, },
    simp only [zero_comp], },
  exact nz (h₁.symm.trans h₀),
end


end

variables [preadditive.{v} C]

lemma biproduct.column_nonzero_of_iso'
  {σ τ : Type v} [decidable_eq σ] [decidable_eq τ] [fintype τ]
  {S : σ → C} [has_biproduct.{v} S] {T : τ → C} [has_biproduct.{v} T]
  (s : σ) (f : ⨁ S ⟶ ⨁ T) [is_iso f] :
  (∀ t : τ, biproduct.ι S s ≫ f ≫ biproduct.π T t = 0) → 𝟙 (S s) = 0 :=
begin
  intro z,
  set x := biproduct.ι S s ≫ f ≫ inv f ≫ biproduct.π S s,
  have h₁ : x = 𝟙 (S s), by simp [x],
  have h₀ : x = 0,
  { dsimp [x],
    rw [←category.id_comp (inv f), category.assoc, ←biproduct.total],
    simp only [comp_sum_assoc],
    conv_lhs { congr, apply_congr, skip, simp only [reassoc_of z], },
    simp, },
  exact h₁.symm.trans h₀,
end

/--
If `f : ⨁ S ⟶ ⨁ T` is an isomorphism, and `s` is a non-trivial summand of the source,
then there is some `t` in the target so that the `s, t` matrix entry of `f` is nonzero.
-/
def biproduct.column_nonzero_of_iso
  {σ τ : Type v} [decidable_eq σ] [decidable_eq τ] [fintype τ]
  {S : σ → C} [has_biproduct.{v} S] {T : τ → C} [has_biproduct.{v} T]
  (s : σ) (nz : 𝟙 (S s) ≠ 0)
  [∀ t, decidable_eq (S s ⟶ T t)]
  (f : ⨁ S ⟶ ⨁ T) [is_iso f] :
  trunc (Σ' t : τ, biproduct.ι S s ≫ f ≫ biproduct.π T t ≠ 0) :=
begin
  apply trunc_sigma_of_exists,
  -- Do this before we run `classical`, so we get the right `decidable_eq` instances.
  have t := biproduct.column_nonzero_of_iso'.{v} s f,
  by_contradiction h,
  simp only [not_exists_not] at h,
  exact nz (t h)
end

end category_theory
