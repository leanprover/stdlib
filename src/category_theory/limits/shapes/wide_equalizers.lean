/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.epi_mono
import category_theory.limits.has_limits
import category_theory.limits.shapes.equalizers

/-!
# Wide equalizers and wide coequalizers

This file defines wide (co)equalizers as special cases of (co)limits.

A wide equalizer for the family of morphisms `X ⟶ Y` indexed by `J` is the categorical
generalization of the subobject `{a ∈ A | ∀ j₁ j₂, f(j₁, a) = f(j₂, a)}`. Note that if `J` has
fewer than two morphisms this condition is trivial, so some lemmas and definitions assume `J` is
nonempty.

## Main definitions

* `walking_parallel_family` is the indexing category used for wide (co)equalizer diagrams
* `parallel_family` is a functor from `walking_parallel_family` to our category `C`.
* a `trident` is a cone over a parallel family.
  * there is really only one interesting morphism in a trident: the arrow from the vertex of the
    trident to the domain of f and g. It is called `trident.ι`.
* a `wide_equalizer` is now just a `limit (parallel_family f)`

Each of these has a dual.

## Main statements

* `wide_equalizer.ι_mono` states that every wide_equalizer map is a monomorphism
* `is_iso_limit_cone_parallel_family_of_self` states that the identity on the domain of `f` is an
  equalizer of `f` and `f`.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

noncomputable theory

namespace category_theory.limits

open category_theory

universes v u u₂

variables {J : Type v}

/-- The type of objects for the diagram indexing a wide (co)equalizer. -/
inductive walking_parallel_family (J : Type v) : Type v
| zero : walking_parallel_family
| one : walking_parallel_family

open walking_parallel_family

instance : decidable_eq (walking_parallel_family J)
| zero zero := is_true rfl
| zero one := is_false (λ t, walking_parallel_family.no_confusion t)
| one zero := is_false (λ t, walking_parallel_family.no_confusion t)
| one one := is_true rfl

instance : inhabited (walking_parallel_family J) := ⟨zero⟩

/-- The type family of morphisms for the diagram indexing a wide (co)equalizer. -/
@[derive decidable_eq] inductive walking_parallel_family.hom (J : Type v) :
  walking_parallel_family J → walking_parallel_family J → Type v
| id : Π X : walking_parallel_family.{v} J, walking_parallel_family.hom X X
| line : Π (j : J), walking_parallel_family.hom zero one

/-- Satisfying the inhabited linter -/
instance (J : Type v) : inhabited (walking_parallel_family.hom J zero zero) :=
{ default := hom.id _ }

open walking_parallel_family.hom

/-- Composition of morphisms in the indexing diagram for wide (co)equalizers. -/
def walking_parallel_family.hom.comp :
  Π (X Y Z : walking_parallel_family J)
    (f : walking_parallel_family.hom J X Y) (g : walking_parallel_family.hom J Y Z),
    walking_parallel_family.hom J X Z
  | _ _ _ (id _)   h := h
  | _ _ _ (line j) (id one) := line j.

local attribute [tidy] tactic.case_bash

instance walking_parallel_family.category : small_category (walking_parallel_family J) :=
{ hom  := walking_parallel_family.hom J,
  id   := walking_parallel_family.hom.id,
  comp := walking_parallel_family.hom.comp }

@[simp]
lemma walking_parallel_family.hom_id (X : walking_parallel_family J) :
  walking_parallel_family.hom.id X = 𝟙 X :=
rfl

variables {C : Type u} [category.{v} C]
variables {X Y : C} (f : J → (X ⟶ Y))

/--
`parallel_family f` is the diagram in `C` consisting of the given family of morphisms, each with
common domain and codomain.
-/
def parallel_family : walking_parallel_family J ⥤ C :=
{ obj := λ x, walking_parallel_family.cases_on x X Y,
  map := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, (line j) := f j
  end,
  map_comp' :=
  begin
    rintro _ _ _ ⟨⟩ ⟨⟩;
    { unfold_aux, simp; refl },
  end }

@[simp] lemma parallel_family_obj_zero : (parallel_family f).obj zero = X := rfl
@[simp] lemma parallel_family_obj_one : (parallel_family f).obj one = Y := rfl

@[simp] lemma parallel_family_map_left {j : J} : (parallel_family f).map (line j) = f j := rfl

/-- Every functor indexing a wide (co)equalizer is naturally isomorphic (actually, equal) to a
    `parallel_family` -/
@[simps]
def diagram_iso_parallel_family (F : walking_parallel_family J ⥤ C) :
  F ≅ parallel_family (λ j, F.map (line j)) :=
nat_iso.of_components (λ j, eq_to_iso $ by cases j; tidy) $ by tidy

/-- `walking_parallel_pair` as a category is equivalent to a special case of
`walking_parallel_family`.  -/
@[simps]
def walking_parallel_family_equiv_walking_parallel_pair :
  walking_parallel_family.{v} (ulift bool) ≌ walking_parallel_pair.{v} :=
{ functor := parallel_family
      (λ p, cond p.down walking_parallel_pair_hom.left walking_parallel_pair_hom.right),
  inverse := parallel_pair (line (ulift.up tt)) (line (ulift.up ff)),
  unit_iso := nat_iso.of_components (λ X, eq_to_iso (by cases X; refl)) (by tidy),
  counit_iso := nat_iso.of_components (λ X, eq_to_iso (by cases X; refl)) (by tidy) }

/-- A trident on `f` is just a `cone (parallel_family f)`. -/
abbreviation trident := cone (parallel_family f)

/-- A cotrident on `f` and `g` is just a `cocone (parallel_family f)`. -/
abbreviation cotrident := cocone (parallel_family f)

variables {f}

/-- A trident `t` on the parallel family `f : J → (X ⟶ Y)` consists of two morphisms
    `t.π.app zero : t.X ⟶ X` and `t.π.app one : t.X ⟶ Y`. Of these, only the first one is
    interesting, and we give it the shorter name `trident.ι t`. -/
abbreviation trident.ι (t : trident f) := t.π.app zero

/-- A cotrident `t` on the parallel family `f : J → (X ⟶ Y)` consists of two morphisms
    `t.ι.app zero : X ⟶ t.X` and `t.ι.app one : Y ⟶ t.X`. Of these, only the second one is
    interesting, and we give it the shorter name `cotrident.π t`. -/
abbreviation cotrident.π (t : cotrident f) := t.ι.app one

@[simp] lemma trident.ι_eq_app_zero (t : trident f) : t.ι = t.π.app zero := rfl
@[simp] lemma cotrident.π_eq_app_one (t : cotrident f) : t.π = t.ι.app one := rfl

@[simp, reassoc] lemma trident.app_zero (s : trident f) (j : J) :
  s.π.app zero ≫ f j = s.π.app one :=
by rw [←s.w (line j), parallel_family_map_left]

@[simp, reassoc] lemma cotrident.app_one (s : cotrident f) (j : J) :
  f j ≫ s.ι.app one = s.ι.app zero :=
by rw [←s.w (line j), parallel_family_map_left]

/--
A trident on `f : J → (X ⟶ Y)` is determined by the morphism `ι : P ⟶ X` satisfying
`∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂`.
-/
@[simps]
def trident.of_ι [nonempty J] {P : C} (ι : P ⟶ X) (w : ∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂) :
  trident f :=
{ X := P,
  π :=
  { app := λ X, walking_parallel_family.cases_on X ι (ι ≫ f (classical.arbitrary J)),
    naturality' := λ i j f,
      begin
        dsimp,
        cases f with _ k,
        { simp },
        { simp [w (classical.arbitrary J) k] },
      end } }

/--
A cotrident on `f : J → (X ⟶ Y)` is determined by the morphism `π : Y ⟶ P` satisfying
`∀ j₁ j₂, f j₁ ≫ π = f j₂ ≫ π`.
-/
@[simps]
def cotrident.of_π [nonempty J] {P : C} (π : Y ⟶ P) (w : ∀ j₁ j₂, f j₁ ≫ π = f j₂ ≫ π) :
  cotrident f :=
{ X := P,
  ι :=
  { app := λ X, walking_parallel_family.cases_on X (f (classical.arbitrary J) ≫ π) π,
    naturality' := λ i j f,
      begin
        dsimp,
        cases f with _ k,
        { simp },
        { simp [w (classical.arbitrary J) k] }
      end } } -- See note [dsimp, simp]

lemma trident.ι_of_ι [nonempty J] {P : C} (ι : P ⟶ X) (w : ∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂) :
  (trident.of_ι ι w).ι = ι := rfl
lemma cotrident.π_of_π [nonempty J] {P : C} (π : Y ⟶ P) (w : ∀ j₁ j₂, f j₁ ≫ π = f j₂ ≫ π) :
  (cotrident.of_π π w).π = π := rfl

@[reassoc]
lemma trident.condition (j₁ j₂ : J) (t : trident f) : t.ι ≫ f j₁ = t.ι ≫ f j₂ :=
by rw [t.app_zero, t.app_zero]

@[reassoc]
lemma cotrident.condition (j₁ j₂ : J) (t : cotrident f) : f j₁ ≫ t.π = f j₂ ≫ t.π :=
by rw [t.app_one, t.app_one]

/-- To check whether two maps are equalized by both maps of a trident, it suffices to check it for
the first map -/
lemma trident.equalizer_ext [nonempty J] (s : trident f) {W : C} {k l : W ⟶ s.X}
  (h : k ≫ s.ι = l ≫ s.ι) : ∀ (j : walking_parallel_family J),
    k ≫ s.π.app j = l ≫ s.π.app j
| zero := h
| one := by rw [←s.app_zero (classical.arbitrary J), reassoc_of h]

/-- To check whether two maps are coequalized by both maps of a cotrident, it suffices to check it
for the second map -/
lemma cotrident.coequalizer_ext [nonempty J] (s : cotrident f) {W : C} {k l : s.X ⟶ W}
  (h : s.π ≫ k = s.π ≫ l) : ∀ (j : walking_parallel_family J),
    s.ι.app j ≫ k = s.ι.app j ≫ l
| zero := by rw [←s.app_one (classical.arbitrary J), category.assoc, category.assoc, h]
| one := h

lemma trident.is_limit.hom_ext [nonempty J] {s : trident f} (hs : is_limit s)
  {W : C} {k l : W ⟶ s.X} (h : k ≫ s.ι = l ≫ s.ι) :
  k = l :=
hs.hom_ext $ trident.equalizer_ext _ h

lemma cotrident.is_colimit.hom_ext [nonempty J] {s : cotrident f} (hs : is_colimit s)
  {W : C} {k l : s.X ⟶ W} (h : s.π ≫ k = s.π ≫ l) :
  k = l :=
hs.hom_ext $ cotrident.coequalizer_ext _ h

/-- If `s` is a limit trident over `f`, then a morphism `k : W ⟶ X` satisfying
    `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` induces a morphism `l : W ⟶ s.X` such that
    `l ≫ trident.ι s = k`. -/
def trident.is_limit.lift' [nonempty J] {s : trident f} (hs : is_limit s) {W : C} (k : W ⟶ X)
  (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
  {l : W ⟶ s.X // l ≫ trident.ι s = k} :=
⟨hs.lift $ trident.of_ι _ h, hs.fac _ _⟩

/-- If `s` is a colimit cotrident over `f`, then a morphism `k : Y ⟶ W` satisfying
    `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` induces a morphism `l : s.X ⟶ W` such that
    `cotrident.π s ≫ l = k`. -/
def cotrident.is_colimit.desc' [nonempty J] {s : cotrident f} (hs : is_colimit s) {W : C}
  (k : Y ⟶ W) (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
  {l : s.X ⟶ W // cotrident.π s ≫ l = k} :=
⟨hs.desc $ cotrident.of_π _ h, hs.fac _ _⟩

/-- This is a slightly more convenient method to verify that a trident is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def trident.is_limit.mk [nonempty J] (t : trident f)
  (lift : Π (s : trident f), s.X ⟶ t.X)
  (fac : ∀ (s : trident f), lift s ≫ t.ι = s.ι)
  (uniq : ∀ (s : trident f) (m : s.X ⟶ t.X)
  (w : ∀ j : walking_parallel_family J, m ≫ t.π.app j = s.π.app j), m = lift s) :
  is_limit t :=
{ lift := lift,
  fac' := λ s j, walking_parallel_family.cases_on j (fac s)
    (by rw [←t.w (line (classical.arbitrary J)), reassoc_of fac, s.w]),
  uniq' := uniq }

/-- This is another convenient method to verify that a trident is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def trident.is_limit.mk' [nonempty J] (t : trident f)
  (create : Π (s : trident f), {l // l ≫ t.ι = s.ι ∧ ∀ {m}, m ≫ t.ι = s.ι → m = l}) :
is_limit t :=
trident.is_limit.mk t
  (λ s, (create s).1)
  (λ s, (create s).2.1)
  (λ s m w, (create s).2.2 (w zero))

/-- This is a slightly more convenient method to verify that a cotrident is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content -/
def cotrident.is_colimit.mk [nonempty J] (t : cotrident f)
  (desc : Π (s : cotrident f), t.X ⟶ s.X)
  (fac : ∀ (s : cotrident f), t.π ≫ desc s = s.π)
  (uniq : ∀ (s : cotrident f) (m : t.X ⟶ s.X)
  (w : ∀ j : walking_parallel_family J, t.ι.app j ≫ m = s.ι.app j), m = desc s) :
  is_colimit t :=
{ desc := desc,
  fac' := λ s j, walking_parallel_family.cases_on j
    (by rw [←t.w_assoc (line (classical.arbitrary J)), fac, s.w]) (fac s),
  uniq' := uniq }

/-- This is another convenient method to verify that a cotrident is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def cotrident.is_colimit.mk' [nonempty J] (t : cotrident f)
  (create : Π (s : cotrident f), {l : t.X ⟶ s.X // t.π ≫ l = s.π ∧ ∀ {m}, t.π ≫ m = s.π → m = l}) :
  is_colimit t :=
cotrident.is_colimit.mk t
  (λ s, (create s).1)
  (λ s, (create s).2.1)
  (λ s m w, (create s).2.2 (w one))

/--
Given a limit cone for the family `f : J → (X ⟶ Y)`, for any `Z`, morphisms from `Z` to its point
are in bijection with morphisms `h : Z ⟶ X` such that `∀ j₁ j₂, h ≫ f j₁ = h ≫ f j₂`.
Further, this bijection is natural in `Z`: see `trident.is_limit.hom_iso_natural`.
-/
@[simps]
def trident.is_limit.hom_iso [nonempty J] {t : trident f} (ht : is_limit t) (Z : C) :
  (Z ⟶ t.X) ≃ {h : Z ⟶ X // ∀ j₁ j₂, h ≫ f j₁ = h ≫ f j₂} :=
{ to_fun := λ k, ⟨k ≫ t.ι, by simp⟩,
  inv_fun := λ h, (trident.is_limit.lift' ht _ h.prop).1,
  left_inv := λ k, trident.is_limit.hom_ext ht (trident.is_limit.lift' _ _ _).prop,
  right_inv := λ h, subtype.ext (trident.is_limit.lift' ht _ _).prop }

/-- The bijection of `trident.is_limit.hom_iso` is natural in `Z`. -/
lemma trident.is_limit.hom_iso_natural [nonempty J] {t : trident f} (ht : is_limit t)
  {Z Z' : C} (q : Z' ⟶ Z) (k : Z ⟶ t.X) :
  (trident.is_limit.hom_iso ht _ (q ≫ k) : Z' ⟶ X) =
  q ≫ (trident.is_limit.hom_iso ht _ k : Z ⟶ X) :=
category.assoc _ _ _

/--
Given a colimit cocone for the family `f : J → (X ⟶ Y)`, for any `Z`, morphisms from the cocone
point to `Z` are in bijection with morphisms `h : Z ⟶ X` such that
`∀ j₁ j₂, f j₁ ≫ h = f j₂ ≫ h`.  Further, this bijection is natural in `Z`: see
`cotrident.is_colimit.hom_iso_natural`.
-/
@[simps]
def cotrident.is_colimit.hom_iso [nonempty J] {t : cotrident f} (ht : is_colimit t) (Z : C) :
  (t.X ⟶ Z) ≃ {h : Y ⟶ Z // ∀ j₁ j₂, f j₁ ≫ h = f j₂ ≫ h} :=
{ to_fun := λ k, ⟨t.π ≫ k, by simp⟩,
  inv_fun := λ h, (cotrident.is_colimit.desc' ht _ h.prop).1,
  left_inv := λ k, cotrident.is_colimit.hom_ext ht (cotrident.is_colimit.desc' _ _ _).prop,
  right_inv := λ h, subtype.ext (cotrident.is_colimit.desc' ht _ _).prop }

/-- The bijection of `cotrident.is_colimit.hom_iso` is natural in `Z`. -/
lemma cotrident.is_colimit.hom_iso_natural [nonempty J] {t : cotrident f} {Z Z' : C}
  (q : Z ⟶ Z') (ht : is_colimit t) (k : t.X ⟶ Z) :
    (cotrident.is_colimit.hom_iso ht _ (k ≫ q) : Y ⟶ Z') =
    (cotrident.is_colimit.hom_iso ht _ k : Y ⟶ Z) ≫ q :=
(category.assoc _ _ _).symm

/-- This is a helper construction that can be useful when verifying that a category has certain wide
    equalizers. Given `F : walking_parallel_family ⥤ C`, which is really the same as
    `parallel_family (λ j, F.map (line j))`, and a trident on `λ j, F.map (line j)`, we get a cone
    on `F`.

    If you're thinking about using this, have a look at
    `has_wide_equalizers_of_has_limit_parallel_family`, which you may find to be an easier way of
    achieving your goal. -/
def cone.of_trident
  {F : walking_parallel_family J ⥤ C} (t : trident (λ j, F.map (line j))) : cone F :=
{ X := t.X,
  π :=
  { app := λ X, t.π.app X ≫ eq_to_hom (by tidy),
    naturality' := λ j j' g, by { cases g; { dsimp, simp } } } }

/-- This is a helper construction that can be useful when verifying that a category has all
    coequalizers. Given `F : walking_parallel_family ⥤ C`, which is really the same as
    `parallel_family (λ j, F.map (line j))`, and a cotrident on `λ j, F.map (line j)` we get a
    cocone on `F`.

    If you're thinking about using this, have a look at
    `has_wide_coequalizers_of_has_colimit_parallel_family`, which you may find to be an easier way
    of achieving your goal. -/
def cocone.of_cotrident
  {F : walking_parallel_family J ⥤ C} (t : cotrident (λ j, F.map (line j))) : cocone F :=
{ X := t.X,
  ι :=
  { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X,
    naturality' := λ j j' g, by { cases g; dsimp; simp [cotrident.app_one t] } } }

@[simp] lemma cone.of_trident_π
  {F : walking_parallel_family J ⥤ C} (t : trident (λ j, F.map (line j))) (j) :
  (cone.of_trident t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl

@[simp] lemma cocone.of_cotrident_ι
  {F : walking_parallel_family J ⥤ C} (t : cotrident (λ j, F.map (line j))) (j) :
  (cocone.of_cotrident t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

/-- Given `F : walking_parallel_family ⥤ C`, which is really the same as
    `parallel_family (λ j, F.map (line j))` and a cone on `F`, we get a trident on
    `λ j, F.map (line j)`. -/
def trident.of_cone
  {F : walking_parallel_family J ⥤ C} (t : cone F) : trident (λ j, F.map (line j)) :=
{ X := t.X,
  π := { app := λ X, t.π.app X ≫ eq_to_hom (by tidy) } }

/-- Given `F : walking_parallel_family ⥤ C`, which is really the same as
    `parallel_family (F.map left) (F.map right)` and a cocone on `F`, we get a cotrident on
    `λ j, F.map (line j)`. -/
def cotrident.of_cocone
  {F : walking_parallel_family J ⥤ C} (t : cocone F) : cotrident (λ j, F.map (line j)) :=
{ X := t.X,
  ι := { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X } }

@[simp] lemma trident.of_cone_π {F : walking_parallel_family J ⥤ C} (t : cone F) (j) :
  (trident.of_cone t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl
@[simp] lemma cotrident.of_cocone_ι {F : walking_parallel_family J ⥤ C} (t : cocone F) (j) :
  (cotrident.of_cocone t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

/--
Helper function for constructing morphisms between wide equalizer tridents.
-/
@[simps]
def trident.mk_hom [nonempty J] {s t : trident f} (k : s.X ⟶ t.X) (w : k ≫ t.ι = s.ι) : s ⟶ t :=
{ hom := k,
  w' :=
  begin
    rintro ⟨_|_⟩,
    { exact w },
    { simpa using w =≫ f (classical.arbitrary J) },
  end }

/--
To construct an isomorphism between tridents,
it suffices to give an isomorphism between the cone points
and check that it commutes with the `ι` morphisms.
-/
@[simps]
def trident.ext [nonempty J] {s t : trident f} (i : s.X ≅ t.X) (w : i.hom ≫ t.ι = s.ι) : s ≅ t :=
{ hom := trident.mk_hom i.hom w,
  inv := trident.mk_hom i.inv (by rw [← w, iso.inv_hom_id_assoc]) }

/--
Helper function for constructing morphisms between coequalizer cotridents.
-/
@[simps]
def cotrident.mk_hom [nonempty J] {s t : cotrident f} (k : s.X ⟶ t.X) (w : s.π ≫ k = t.π) :
  s ⟶ t :=
{ hom := k,
  w' :=
  begin
    rintro ⟨_|_⟩,
    { simpa using f (classical.arbitrary J) ≫= w },
    { exact w },
  end }

/--
To construct an isomorphism between cotridents,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
def cotrident.ext [nonempty J] {s t : cotrident f} (i : s.X ≅ t.X) (w : s.π ≫ i.hom = t.π) :
  s ≅ t :=
{ hom := cotrident.mk_hom i.hom w,
  inv := cotrident.mk_hom i.inv (by rw [iso.comp_inv_eq, w]) }

variables (f)

section
/--
`has_wide_equalizer f` represents a particular choice of limiting cone for the parallel family of
morphisms `f`.
-/
abbreviation has_wide_equalizer := has_limit (parallel_family f)

variables [has_wide_equalizer f]

/-- If a wide equalizer of `f` exists, we can access an arbitrary choice of such by
    saying `wide_equalizer f`. -/
abbreviation wide_equalizer : C := limit (parallel_family f)

/-- If a wide equalizer of `f` exists, we can access the inclusion `wide_equalizer f ⟶ X` by
    saying `wide_equalizer.ι f`. -/
abbreviation wide_equalizer.ι : wide_equalizer f ⟶ X :=
limit.π (parallel_family f) zero

/--
A wide equalizer cone for a parallel family `f`.
-/
abbreviation wide_equalizer.trident : trident f := limit.cone (parallel_family f)

@[simp] lemma wide_equalizer.trident_ι :
  (wide_equalizer.trident f).ι = wide_equalizer.ι f := rfl

@[simp] lemma wide_equalizer.trident_π_app_zero :
  (wide_equalizer.trident f).π.app zero = wide_equalizer.ι f := rfl

@[reassoc] lemma wide_equalizer.condition (j₁ j₂ : J) :
  wide_equalizer.ι f ≫ f j₁ = wide_equalizer.ι f ≫ f j₂ :=
trident.condition j₁ j₂ $ limit.cone $ parallel_family f

/-- The wide_equalizer built from `wide_equalizer.ι f` is limiting. -/
def wide_equalizer_is_wide_equalizer [nonempty J] :
  is_limit (trident.of_ι (wide_equalizer.ι f) (wide_equalizer.condition f)) :=
is_limit.of_iso_limit (limit.is_limit _) (trident.ext (iso.refl _) (by tidy))

variables {f}

/-- A morphism `k : W ⟶ X` satisfying `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` factors through the
    wide equalizer of `f` via `wide_equalizer.lift : W ⟶ wide_equalizer f`. -/
abbreviation wide_equalizer.lift [nonempty J] {W : C} (k : W ⟶ X)
  (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
  W ⟶ wide_equalizer f :=
limit.lift (parallel_family f) (trident.of_ι k h)

@[simp, reassoc]
lemma wide_equalizer.lift_ι [nonempty J] {W : C} (k : W ⟶ X) (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
  wide_equalizer.lift k h ≫ wide_equalizer.ι f = k :=
limit.lift_π _ _

/-- A morphism `k : W ⟶ X` satisfying `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` induces a morphism
    `l : W ⟶ wide_equalizer f` satisfying `l ≫ wide_equalizer.ι f = k`. -/
def wide_equalizer.lift' [nonempty J] {W : C} (k : W ⟶ X) (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
  {l : W ⟶ wide_equalizer f // l ≫ wide_equalizer.ι f = k} :=
⟨wide_equalizer.lift k h, wide_equalizer.lift_ι _ _⟩

/-- Two maps into a wide equalizer are equal if they are are equal when composed with the wide
    equalizer map. -/
@[ext] lemma wide_equalizer.hom_ext [nonempty J] {W : C} {k l : W ⟶ wide_equalizer f}
  (h : k ≫ wide_equalizer.ι f = l ≫ wide_equalizer.ι f) : k = l :=
trident.is_limit.hom_ext (limit.is_limit _) h

/-- A wide equalizer morphism is a monomorphism -/
instance wide_equalizer.ι_mono [nonempty J] : mono (wide_equalizer.ι f) :=
{ right_cancellation := λ Z h k w, wide_equalizer.hom_ext w }

end

section
variables {f}
/-- The wide equalizer morphism in any limit cone is a monomorphism. -/
lemma mono_of_is_limit_parallel_family [nonempty J] {c : cone (parallel_family f)}
  (i : is_limit c) :
  mono (trident.ι c) :=
{ right_cancellation := λ Z h k w, trident.is_limit.hom_ext i w }

end

section
/--
`has_wide_coequalizer f g` represents a particular choice of colimiting cocone
for the parallel family of morphisms `f`.
-/
abbreviation has_wide_coequalizer := has_colimit (parallel_family f)

variables [has_wide_coequalizer f]

/-- If a wide coequalizer of `f`, we can access an arbitrary choice of such by
    saying `wide_coequalizer f`. -/
abbreviation wide_coequalizer : C := colimit (parallel_family f)

/--  If a wide_coequalizer of `f` exists, we can access the corresponding projection by
    saying `wide_coequalizer.π f`. -/
abbreviation wide_coequalizer.π : Y ⟶ wide_coequalizer f :=
colimit.ι (parallel_family f) one

/--
An arbitrary choice of coequalizer cocone for a parallel family `f`.
-/
abbreviation wide_coequalizer.cotrident : cotrident f := colimit.cocone (parallel_family f)

@[simp] lemma wide_coequalizer.cotrident_π :
  (wide_coequalizer.cotrident f).π = wide_coequalizer.π f := rfl

@[simp] lemma wide_coequalizer.cotrident_ι_app_one :
  (wide_coequalizer.cotrident f).ι.app one = wide_coequalizer.π f := rfl

@[reassoc] lemma wide_coequalizer.condition (j₁ j₂ : J) :
  f j₁ ≫ wide_coequalizer.π f = f j₂ ≫ wide_coequalizer.π f :=
cotrident.condition j₁ j₂ $ colimit.cocone $ parallel_family f

/-- The cotrident built from `wide_coequalizer.π f` is colimiting. -/
def wide_coequalizer_is_wide_coequalizer [nonempty J] :
  is_colimit (cotrident.of_π (wide_coequalizer.π f) (wide_coequalizer.condition f)) :=
is_colimit.of_iso_colimit (colimit.is_colimit _) (cotrident.ext (iso.refl _) (by tidy))

variables {f}

/-- Any morphism `k : Y ⟶ W` satisfying `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` factors through the
    wide coequalizer of `f` via `wide_coequalizer.desc : wide_coequalizer f ⟶ W`. -/
abbreviation wide_coequalizer.desc [nonempty J] {W : C} (k : Y ⟶ W)
  (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
  wide_coequalizer f ⟶ W :=
colimit.desc (parallel_family f) (cotrident.of_π k h)

@[simp, reassoc]
lemma wide_coequalizer.π_desc [nonempty J] {W : C} (k : Y ⟶ W) (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
  wide_coequalizer.π f ≫ wide_coequalizer.desc k h = k :=
colimit.ι_desc _ _

/-- Any morphism `k : Y ⟶ W` satisfying `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` induces a morphism
    `l : wide_coequalizer f ⟶ W` satisfying `wide_coequalizer.π ≫ g = l`. -/
def wide_coequalizer.desc' [nonempty J] {W : C} (k : Y ⟶ W) (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
  {l : wide_coequalizer f ⟶ W // wide_coequalizer.π f ≫ l = k} :=
⟨wide_coequalizer.desc k h, wide_coequalizer.π_desc _ _⟩

/-- Two maps from a wide coequalizer are equal if they are equal when composed with the wide
    coequalizer map -/
@[ext] lemma wide_coequalizer.hom_ext [nonempty J] {W : C} {k l : wide_coequalizer f ⟶ W}
  (h : wide_coequalizer.π f ≫ k = wide_coequalizer.π f ≫ l) : k = l :=
cotrident.is_colimit.hom_ext (colimit.is_colimit _) h

/-- A wide coequalizer morphism is an epimorphism -/
instance wide_coequalizer.π_epi [nonempty J] : epi (wide_coequalizer.π f) :=
{ left_cancellation := λ Z h k w, wide_coequalizer.hom_ext w }

end

section
variables {f}

/-- The wide coequalizer morphism in any colimit cocone is an epimorphism. -/
lemma epi_of_is_colimit_parallel_family [nonempty J] {c : cocone (parallel_family f)}
  (i : is_colimit c) :
  epi (c.ι.app one) :=
{ left_cancellation := λ Z h k w, cotrident.is_colimit.hom_ext i w }

end

variables (C)

/-- `has_wide_equalizers` represents a choice of wide equalizer for every family of morphisms -/
abbreviation has_wide_equalizers := Π J, has_limits_of_shape (walking_parallel_family J) C

/-- `has_wide_coequalizers` represents a choice of wide coequalizer for every family of morphisms -/
abbreviation has_wide_coequalizers := Π J, has_colimits_of_shape (walking_parallel_family J) C

/-- If `C` has all limits of diagrams `parallel_family f`, then it has all wide equalizers -/
lemma has_wide_equalizers_of_has_limit_parallel_family
  [Π {J} {X Y : C} {f : J → (X ⟶ Y)}, has_limit (parallel_family f)] : has_wide_equalizers C :=
λ J, { has_limit := λ F, has_limit_of_iso (diagram_iso_parallel_family F).symm }

/-- If `C` has all colimits of diagrams `parallel_family f`, then it has all wide coequalizers -/
lemma has_wide_coequalizers_of_has_colimit_parallel_family
  [Π {J} {X Y : C} {f : J → (X ⟶ Y)}, has_colimit (parallel_family f)] : has_wide_coequalizers C :=
λ J, { has_colimit := λ F, has_colimit_of_iso (diagram_iso_parallel_family F) }

@[priority 10]
instance has_equalizers_of_has_wide_equalizers [has_wide_equalizers C] : has_equalizers C :=
has_limits_of_shape_of_equivalence walking_parallel_family_equiv_walking_parallel_pair

@[priority 10]
instance has_coequalizers_of_has_wide_coequalizers [has_wide_coequalizers C] : has_coequalizers C :=
has_colimits_of_shape_of_equivalence walking_parallel_family_equiv_walking_parallel_pair

end category_theory.limits
