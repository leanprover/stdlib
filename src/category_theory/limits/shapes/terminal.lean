/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.pempty
import category_theory.limits.has_limits
import category_theory.epi_mono

/-!
# Initial and terminal objects in a category.

## References
* [Stacks: Initial and final objects](https://stacks.math.columbia.edu/tag/002B)
-/

noncomputable theory

universes v u u₂

open category_theory

namespace category_theory.limits

variables {C : Type u} [category.{v} C]

/-- Construct a cone for the empty diagram given an object. -/
@[simps] def as_empty_cone (X : C) : cone (functor.empty C) := { X := X, π := by tidy }
/-- Construct a cocone for the empty diagram given an object. -/
@[simps] def as_empty_cocone (X : C) : cocone (functor.empty C) := { X := X, ι := by tidy }

/-- `X` is terminal if the cone it induces on the empty diagram is limiting. -/
abbreviation is_terminal (X : C) := is_limit (as_empty_cone X)
/-- `X` is initial if the cocone it induces on the empty diagram is colimiting. -/
abbreviation is_initial (X : C) := is_colimit (as_empty_cocone X)

/-- An object `Y` is terminal if for every `X` there is a unique morphism `X ⟶ Y`. -/
def is_terminal.of_unique (Y : C) [h : Π X : C, unique (X ⟶ Y)] : is_terminal Y :=
{ lift := λ s, (h s.X).default }

/-- Transport a term of type `is_terminal` across an isomorphism. -/
def is_terminal.of_iso {Y Z : C} (hY : is_terminal Y) (i : Y ≅ Z) : is_terminal Z :=
is_limit.of_iso_limit hY
{ hom := { hom := i.hom },
  inv := { hom := i.symm.hom } }

/-- An object `X` is initial if for every `Y` there is a unique morphism `X ⟶ Y`. -/
def is_initial.of_unique (X : C) [h : Π Y : C, unique (X ⟶ Y)] : is_initial X :=
{ desc := λ s, (h s.X).default }

/-- Transport a term of type `is_initial` across an isomorphism. -/
def is_initial.of_iso {X Y : C} (hX : is_initial X) (i : X ≅ Y) : is_initial Y :=
is_colimit.of_iso_colimit hX
{ hom := { hom := i.hom },
  inv := { hom := i.symm.hom } }

/-- Give the morphism to a terminal object from any other. -/
def is_terminal.from {X : C} (t : is_terminal X) (Y : C) : Y ⟶ X :=
t.lift (as_empty_cone Y)

/-- Any two morphisms to a terminal object are equal. -/
lemma is_terminal.hom_ext {X Y : C} (t : is_terminal X) (f g : Y ⟶ X) : f = g :=
t.hom_ext (by tidy)

@[simp] lemma is_terminal.comp_from {Z : C} (t : is_terminal Z) {X Y : C} (f : X ⟶ Y) :
  f ≫ t.from Y = t.from X :=
t.hom_ext _ _

@[simp] lemma is_terminal.from_self {X : C} (t : is_terminal X) : t.from X = 𝟙 X :=
t.hom_ext _ _

/-- Give the morphism from an initial object to any other. -/
def is_initial.to {X : C} (t : is_initial X) (Y : C) : X ⟶ Y :=
t.desc (as_empty_cocone Y)

/-- Any two morphisms from an initial object are equal. -/
lemma is_initial.hom_ext {X Y : C} (t : is_initial X) (f g : X ⟶ Y) : f = g :=
t.hom_ext (by tidy)

@[simp] lemma is_initial.to_comp {X : C} (t : is_initial X) {Y Z : C} (f : Y ⟶ Z) :
  t.to Y ≫ f = t.to Z :=
t.hom_ext _ _

@[simp] lemma is_initial.to_self {X : C} (t : is_initial X) : t.to X = 𝟙 X :=
t.hom_ext _ _

/-- Any morphism from a terminal object is split mono. -/
def is_terminal.split_mono_from {X Y : C} (t : is_terminal X) (f : X ⟶ Y) : split_mono f :=
⟨t.from _, t.hom_ext _ _⟩

/-- Any morphism to an initial object is split epi. -/
def is_initial.split_epi_to {X Y : C} (t : is_initial X) (f : Y ⟶ X) : split_epi f :=
⟨t.to _, t.hom_ext _ _⟩

/-- Any morphism from a terminal object is mono. -/
lemma is_terminal.mono_from {X Y : C} (t : is_terminal X) (f : X ⟶ Y) : mono f :=
by haveI := t.split_mono_from f; apply_instance

/-- Any morphism to an initial object is epi. -/
lemma is_initial.epi_to {X Y : C} (t : is_initial X) (f : Y ⟶ X) : epi f :=
by haveI := t.split_epi_to f; apply_instance

variable (C)

/--
A category has a terminal object if it has a limit over the empty diagram.
Use `has_terminal_of_unique` to construct instances.
-/
abbreviation has_terminal := has_limits_of_shape (discrete pempty) C
/--
A category has an initial object if it has a colimit over the empty diagram.
Use `has_initial_of_unique` to construct instances.
-/
abbreviation has_initial := has_colimits_of_shape (discrete pempty) C

/--
An arbitrary choice of terminal object, if one exists.
You can use the notation `⊤_ C`.
This object is characterized by having a unique morphism from any object.
-/
abbreviation terminal [has_terminal C] : C := limit (functor.empty C)
/--
An arbitrary choice of initial object, if one exists.
You can use the notation `⊥_ C`.
This object is characterized by having a unique morphism to any object.
-/
abbreviation initial [has_initial C] : C := colimit (functor.empty C)

notation `⊤_ ` C:20 := terminal C
notation `⊥_ ` C:20 := initial C

section
variables {C}

/-- We can more explicitly show that a category has a terminal object by specifying the object,
and showing there is a unique morphism to it from any other object. -/
lemma has_terminal_of_unique (X : C) [h : Π Y : C, unique (Y ⟶ X)] : has_terminal C :=
{ has_limit := λ F, has_limit.mk
  { cone     := { X := X, π := { app := pempty.rec _ } },
    is_limit := { lift := λ s, (h s.X).default } } }

/-- We can more explicitly show that a category has an initial object by specifying the object,
and showing there is a unique morphism from it to any other object. -/
lemma has_initial_of_unique (X : C) [h : Π Y : C, unique (X ⟶ Y)] : has_initial C :=
{ has_colimit := λ F, has_colimit.mk
  { cocone     := { X := X, ι := { app := pempty.rec _ } },
    is_colimit := { desc := λ s, (h s.X).default } } }

/-- The map from an object to the terminal object. -/
abbreviation terminal.from [has_terminal C] (P : C) : P ⟶ ⊤_ C :=
limit.lift (functor.empty C) (as_empty_cone P)
/-- The map to an object from the initial object. -/
abbreviation initial.to [has_initial C] (P : C) : ⊥_ C ⟶ P :=
colimit.desc (functor.empty C) (as_empty_cocone P)

instance unique_to_terminal [has_terminal C] (P : C) : unique (P ⟶ ⊤_ C) :=
{ default := terminal.from P,
  uniq := λ m, by { apply limit.hom_ext, rintro ⟨⟩ } }

instance unique_from_initial [has_initial C] (P : C) : unique (⊥_ C ⟶ P) :=
{ default := initial.to P,
  uniq := λ m, by { apply colimit.hom_ext, rintro ⟨⟩ } }

@[simp] lemma terminal.comp_from [has_terminal C] {P Q : C} (f : P ⟶ Q) :
  f ≫ terminal.from Q = terminal.from P :=
by tidy
@[simp] lemma initial.to_comp [has_initial C] {P Q : C} (f : P ⟶ Q) :
  initial.to P ≫ f = initial.to Q :=
by tidy

/-- A terminal object is terminal. -/
def terminal_is_terminal [has_terminal C] : is_terminal (⊤_ C) :=
{ lift := λ s, terminal.from _ }

/-- An initial object is initial. -/
def initial_is_initial [has_initial C] : is_initial (⊥_ C) :=
{ desc := λ s, initial.to _ }

/-- Any morphism from a terminal object is split mono. -/
instance terminal.split_mono_from {Y : C} [has_terminal C] (f : ⊤_ C ⟶ Y) : split_mono f :=
is_terminal.split_mono_from terminal_is_terminal _

/-- Any morphism to an initial object is split epi. -/
instance initial.split_epi_to {Y : C} [has_initial C] (f : Y ⟶ ⊥_ C) : split_epi f :=
is_initial.split_epi_to initial_is_initial _

/-- An initial object is terminal in the opposite category. -/
def terminal_op_of_initial {X : C} (t : is_initial X) : is_terminal (opposite.op X) :=
{ lift := λ s, (t.to s.X.unop).op,
  uniq' := λ s m w, quiver.hom.unop_inj (t.hom_ext _ _) }

/-- An initial object in the opposite category is terminal in the original category. -/
def terminal_unop_of_initial {X : Cᵒᵖ} (t : is_initial X) : is_terminal X.unop :=
{ lift := λ s, (t.to (opposite.op s.X)).unop,
  uniq' := λ s m w, quiver.hom.op_inj (t.hom_ext _ _) }

/-- A terminal object is initial in the opposite category. -/
def initial_op_of_terminal {X : C} (t : is_terminal X) : is_initial (opposite.op X) :=
{ desc := λ s, (t.from s.X.unop).op,
  uniq' := λ s m w, quiver.hom.unop_inj (t.hom_ext _ _) }

/-- A terminal object in the opposite category is initial in the original category. -/
def initial_unop_of_terminal {X : Cᵒᵖ} (t : is_terminal X) : is_initial X.unop :=
{ desc := λ s, (t.from (opposite.op s.X)).unop,
  uniq' := λ s m w, quiver.hom.op_inj (t.hom_ext _ _) }

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cone for `J`.
In `limit_of_diagram_initial` we show it is a limit cone. -/
@[simps]
def cone_of_diagram_initial {J : Type v} [small_category J]
  {X : J} (tX : is_initial X) (F : J ⥤ C) : cone F :=
{ X := F.obj X,
  π :=
  { app := λ j, F.map (tX.to j),
    naturality' := λ j j' k,
    begin
      dsimp,
      rw [← F.map_comp, category.id_comp, tX.hom_ext (tX.to j ≫ k) (tX.to j')],
    end } }

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, show the cone
`cone_of_diagram_initial` is a limit. -/
def limit_of_diagram_initial {J : Type v} [small_category J]
  {X : J} (tX : is_initial X) (F : J ⥤ C) :
is_limit (cone_of_diagram_initial tX F) :=
{ lift := λ s, s.π.app X,
  uniq' := λ s m w,
    begin
      rw [← w X, cone_of_diagram_initial_π_app, tX.hom_ext (tX.to X) (𝟙 _)],
      dsimp, simp -- See note [dsimp, simp]
    end}

-- This is reducible to allow usage of lemmas about `cone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has an initial object then the image of it is isomorphic
to the limit of `F`. -/
@[reducible]
def limit_of_initial {J : Type v} [small_category J] (F : J ⥤ C)
  [has_initial J] [has_limit F] :
limit F ≅ F.obj (⊥_ J) :=
is_limit.cone_point_unique_up_to_iso
  (limit.is_limit _)
  (limit_of_diagram_initial initial_is_initial F)

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cocone for `J`.
In `colimit_of_diagram_terminal` we show it is a colimit cocone. -/
@[simps]
def cocone_of_diagram_terminal {J : Type v} [small_category J]
  {X : J} (tX : is_terminal X) (F : J ⥤ C) : cocone F :=
{ X := F.obj X,
  ι :=
  { app := λ j, F.map (tX.from j),
    naturality' := λ j j' k,
    begin
      dsimp,
      rw [← F.map_comp, category.comp_id, tX.hom_ext (k ≫ tX.from j') (tX.from j)],
    end } }

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, show the cocone
`cocone_of_diagram_terminal` is a colimit. -/
def colimit_of_diagram_terminal {J : Type v} [small_category J]
  {X : J} (tX : is_terminal X) (F : J ⥤ C) :
is_colimit (cocone_of_diagram_terminal tX F) :=
{ desc := λ s, s.ι.app X,
  uniq' := λ s m w,
    by { rw [← w X, cocone_of_diagram_terminal_ι_app, tX.hom_ext (tX.from X) (𝟙 _)], simp } }

-- This is reducible to allow usage of lemmas about `cocone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has a terminal object then the image of it is isomorphic
to the colimit of `F`. -/
@[reducible]
def colimit_of_terminal {J : Type v} [small_category J] (F : J ⥤ C)
  [has_terminal J] [has_colimit F] :
colimit F ≅ F.obj (⊤_ J) :=
is_colimit.cocone_point_unique_up_to_iso
  (colimit.is_colimit _)
  (colimit_of_diagram_terminal terminal_is_terminal F)

end

section comparison
variables {C} {D : Type u₂} [category.{v} D] (G : C ⥤ D)

/--
The comparison morphism from the image of a terminal object to the terminal object in the target
category.
-/
-- TODO: Show this is an isomorphism if and only if `G` preserves terminal objects.
def terminal_comparison [has_terminal C] [has_terminal D] :
  G.obj (⊤_ C) ⟶ ⊤_ D :=
terminal.from _

/--
The comparison morphism from the initial object in the target category to the image of the initial
object.
-/
-- TODO: Show this is an isomorphism if and only if `G` preserves initial objects.
def initial_comparison [has_initial C] [has_initial D] :
  ⊥_ D ⟶ G.obj (⊥_ C) :=
initial.to _

end comparison

variables {C} {J : Type v} [small_category J]

/--
If `j` is initial in the index category, then the map `limit.π F j` is an isomorphism.
-/
lemma is_iso_π_of_is_initial {j : J} (I : is_initial j) (F : J ⥤ C) [has_limit F] :
  is_iso (limit.π F j) :=
⟨⟨limit.lift _ (cone_of_diagram_initial I F), ⟨by { ext, simp }, by simp⟩⟩⟩

instance is_iso_π_initial [has_initial J] (F : J ⥤ C) [has_limit F] :
  is_iso (limit.π F (⊥_ J)) :=
is_iso_π_of_is_initial (initial_is_initial) F

/--
If `j` is terminal in the index category, then the map `colimit.ι F j` is an isomorphism.
-/
lemma is_iso_ι_of_is_terminal {j : J} (I : is_terminal j) (F : J ⥤ C) [has_colimit F] :
  is_iso (colimit.ι F j) :=
⟨⟨colimit.desc _ (cocone_of_diagram_terminal I F), ⟨by simp, by { ext, simp }⟩⟩⟩

instance is_iso_ι_terminal [has_terminal J] (F : J ⥤ C) [has_colimit F] :
  is_iso (colimit.ι F (⊤_ J)) :=
is_iso_ι_of_is_terminal (terminal_is_terminal) F

end category_theory.limits
