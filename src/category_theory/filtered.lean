/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison
-/
import category_theory.fin_category
import category_theory.limits.cones
import category_theory.adjunction.basic
import order.bounded_lattice

/-!
# Filtered categories

A category is filtered if every finite diagram admits a cocone.
We give a simple characterisation of this condition as
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.

Filtered colimits are often better behaved than arbitrary colimits.
See `category_theory/limits/types` for some details.

Filtered categories are nice because colimits indexed by filtered categories tend to be
easier to describe than general colimits (and more often preserved by functors).

In this file we show that any functor from a finite category to a filtered category admits a cocone:
* `cocone_nonempty [fin_category J] [is_filtered C] (F : J ⥤ C) : nonempty (cocone F)`
More generally,
for any finite collection of objects and morphisms between them in a filtered category
(even if not closed under composition) there exists some object `Z` receiving maps from all of them,
so that all the triangles (one edge from the finite set, two from morphisms to `Z`) commute.
This formulation is often more useful in practice and is available via `sup_exists`,
which takes a finset of objects, and an indexed family (indexed by source and target)
of finsets of morphisms.

We also provide all of the above API for cofiltered categories.

## See also
In `category_theory.limits.filtered_colimit_commutes_finite_limit` we show that filtered colimits
commute with finite limits.

## Future work
* Forgetful functors for algebraic categories typically preserve filtered colimits.
-/

universes v v₁ u u₁-- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory

variables (C : Type u) [category.{v} C]

/--
A category `is_filtered_or_empty` if
1. for every pair of objects there exists another object "to the right", and
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal.
-/
class is_filtered_or_empty : Prop :=
(cocone_objs : ∀ (X Y : C), ∃ Z (f : X ⟶ Z) (g : Y ⟶ Z), true)
(cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ Z (h : Y ⟶ Z), f ≫ h = g ≫ h)

/--
A category `is_filtered` if
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.

See https://stacks.math.columbia.edu/tag/002V. (They also define a diagram being filtered.)
-/
class is_filtered extends is_filtered_or_empty C : Prop :=
[nonempty : nonempty C]

@[priority 100]
instance is_filtered_or_empty_of_semilattice_sup
  (α : Type u) [semilattice_sup α] : is_filtered_or_empty α :=
{ cocone_objs := λ X Y, ⟨X ⊔ Y, hom_of_le le_sup_left, hom_of_le le_sup_right, trivial⟩,
  cocone_maps := λ X Y f g, ⟨Y, 𝟙 _, (by ext)⟩, }

@[priority 100]
instance is_filtered_of_semilattice_sup_nonempty
  (α : Type u) [semilattice_sup α] [nonempty α] : is_filtered α := {}

-- TODO: Define `codirected_order` and provide the dual to this instance.
@[priority 100]
instance is_filtered_or_empty_of_directed_order
  (α : Type u) [directed_order α] : is_filtered_or_empty α :=
{ cocone_objs := λ X Y, let ⟨Z,h1,h2⟩ := directed_order.directed X Y in
    ⟨Z, hom_of_le h1, hom_of_le h2, trivial⟩,
  cocone_maps := λ X Y f g, ⟨Y, 𝟙 _, by simp⟩ }

-- TODO: Define `codirected_order` and provide the dual to this instance.
@[priority 100]
instance is_filtered_of_directed_order_nonempty
  (α : Type u) [directed_order α] [nonempty α] : is_filtered α := {}

-- Sanity checks
example (α : Type u) [semilattice_sup_bot α] : is_filtered α := by apply_instance
example (α : Type u) [semilattice_sup_top α] : is_filtered α := by apply_instance

namespace is_filtered

variables {C} [is_filtered C]

/--
`max j j'` is an arbitrary choice of object to the right of both `j` and `j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def max (j j' : C) : C :=
(is_filtered_or_empty.cocone_objs j j').some

/--
`left_to_max j j'` is an arbitrarily choice of morphism from `j` to `max j j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def left_to_max (j j' : C) : j ⟶ max j j' :=
(is_filtered_or_empty.cocone_objs j j').some_spec.some

/--
`right_to_max j j'` is an arbitrarily choice of morphism from `j'` to `max j j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def right_to_max (j j' : C) : j' ⟶ max j j' :=
(is_filtered_or_empty.cocone_objs j j').some_spec.some_spec.some

/--
`coeq f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of object
which admits a morphism `coeq_hom f f' : j' ⟶ coeq f f'` such that
`coeq_condition : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
Its existence is ensured by `is_filtered`.
-/
noncomputable def coeq {j j' : C} (f f' : j ⟶ j') : C :=
(is_filtered_or_empty.cocone_maps f f').some

/--
`coeq_hom f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of morphism
`coeq_hom f f' : j' ⟶ coeq f f'` such that
`coeq_condition : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
Its existence is ensured by `is_filtered`.
-/
noncomputable def coeq_hom {j j' : C} (f f' : j ⟶ j') : j' ⟶ coeq f f' :=
(is_filtered_or_empty.cocone_maps f f').some_spec.some

/--
`coeq_condition f f'`, for morphisms `f f' : j ⟶ j'`, is the proof that
`f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
-/
@[simp, reassoc]
lemma coeq_condition {j j' : C} (f f' : j ⟶ j') : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f' :=
(is_filtered_or_empty.cocone_maps f f').some_spec.some_spec

open category_theory.limits

/--
Any finite collection of objects in a filtered category has an object "to the right".
-/
lemma sup_objs_exists (O : finset C) : ∃ (S : C), ∀ {X}, X ∈ O → _root_.nonempty (X ⟶ S) :=
begin
  classical,
  apply finset.induction_on O,
  { exact ⟨is_filtered.nonempty.some, (by rintros - ⟨⟩)⟩, },
  { rintros X O' nm ⟨S', w'⟩,
    use max X S',
    rintros Y mY,
    by_cases h : X = Y,
    { subst h, exact ⟨left_to_max _ _⟩, },
    { exact ⟨(w' (by finish)).some ≫ right_to_max _ _⟩, }, }
end

variables (O : finset C) (H : finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y))

/--
Given any `finset` of objects `{X, ...}` and
indexed collection of `finset`s of morphisms `{f, ...}` in `C`,
there exists an object `S`, with a morphism `T X : X ⟶ S` from each `X`,
such that the triangles commute: `f ≫ T Y = T X`, for `f : X ⟶ Y` in the `finset`.
-/
lemma sup_exists :
  ∃ (S : C) (T : Π {X : C}, X ∈ O → (X ⟶ S)), ∀ {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y},
    (⟨X, Y, mX, mY, f⟩ : (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y)) ∈ H → f ≫ T mY = T mX :=
begin
  classical,
  apply finset.induction_on H,
  { obtain ⟨S, f⟩ := sup_objs_exists O,
    refine ⟨S, λ X mX, (f mX).some, _⟩,
    rintros - - - - - ⟨⟩, },
  { rintros ⟨X, Y, mX, mY, f⟩ H' nmf ⟨S', T', w'⟩,
    refine ⟨coeq (f ≫ T' mY) (T' mX), λ Z mZ, T' mZ ≫ coeq_hom (f ≫ T' mY) (T' mX), _⟩,
    intros X' Y' mX' mY' f' mf',
    rw [←category.assoc],
    by_cases h : X = X' ∧ Y = Y',
    { rcases h with ⟨rfl, rfl⟩,
      by_cases hf : f = f',
      { subst hf,
        apply coeq_condition, },
      { rw @w' _ _ mX mY f' (by simpa [hf ∘ eq.symm] using mf') }, },
    { rw @w' _ _ mX' mY' f' (by finish), }, },
end

/--
An arbitrary choice of object "to the right"
of a finite collection of objects `O` and morphisms `H`,
making all the triangles commute.
-/
noncomputable
def sup : C :=
(sup_exists O H).some

/--
The morphisms to `sup O H`.
-/
noncomputable
def to_sup {X : C} (m : X ∈ O) :
  X ⟶ sup O H :=
(sup_exists O H).some_spec.some m

/--
The triangles of consisting of a morphism in `H` and the maps to `sup O H` commute.
-/
lemma to_sup_commutes
  {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y}
  (mf : (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) ∈ H) :
  f ≫ to_sup O H mY = to_sup O H mX :=
(sup_exists O H).some_spec.some_spec mX mY mf

variables {J : Type v} [small_category J] [fin_category J]

/--
If we have `is_filtered C`, then for any functor `F : J ⥤ C` with `fin_category J`,
there exists a cocone over `F`.
-/
lemma cocone_nonempty (F : J ⥤ C) : _root_.nonempty (cocone F) :=
begin
  classical,
  let O := (finset.univ.image F.obj),
  let H : finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) :=
    finset.univ.bUnion (λ X : J, finset.univ.bUnion (λ Y : J, finset.univ.image (λ f : X ⟶ Y,
      ⟨F.obj X, F.obj Y, by simp, by simp, F.map f⟩))),
  obtain ⟨Z, f, w⟩ := sup_exists O H,
  refine ⟨⟨Z, ⟨λ X, f (by simp), _⟩⟩⟩,
  intros j j' g,
  dsimp,
  simp only [category.comp_id],
  apply w,
  simp only [finset.mem_univ, finset.mem_bUnion, exists_and_distrib_left,
    exists_prop_of_true, finset.mem_image],
  exact ⟨j, rfl, j', g, (by simp)⟩,
end

/--
An arbitrary choice of cocone over `F : J ⥤ C`, for `fin_category J` and `is_filtered C`.
-/
noncomputable def cocone (F : J ⥤ C) : cocone F :=
(cocone_nonempty F).some

variables {D : Type u₁} [category.{v₁} D]

/--
If `C` is filtered, and we have a functor `R : C ⥤ D` with a left adjoint, then `D` is filtered.
-/
lemma of_right_adjoint {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R) : is_filtered D :=
{ cocone_objs := λ X Y,
    ⟨_, h.hom_equiv _ _ (left_to_max _ _), h.hom_equiv _ _ (right_to_max _ _), ⟨⟩⟩,
  cocone_maps := λ X Y f g,
    ⟨_, h.hom_equiv _ _ (coeq_hom _ _),
     by rw [← h.hom_equiv_naturality_left, ← h.hom_equiv_naturality_left, coeq_condition]⟩,
  nonempty := is_filtered.nonempty.map R.obj }

/-- If `C` is filtered, and we have a right adjoint functor `R : C ⥤ D`, then `D` is filtered. -/
lemma of_is_right_adjoint (R : C ⥤ D) [is_right_adjoint R] : is_filtered D :=
of_right_adjoint (adjunction.of_right_adjoint R)

/-- Being filtered is preserved by equivalence of categories. -/
lemma of_equivalence (h : C ≌ D) : is_filtered D :=
of_right_adjoint h.symm.to_adjunction

end is_filtered

/--
A category `is_cofiltered_or_empty` if
1. for every pair of objects there exists another object "to the left", and
2. for every pair of parallel morphisms there exists a morphism to the left so the compositions
   are equal.
-/
class is_cofiltered_or_empty : Prop :=
(cocone_objs : ∀ (X Y : C), ∃ W (f : W ⟶ X) (g : W ⟶ Y), true)
(cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ W (h : W ⟶ X), h ≫ f = h ≫ g)

/--
A category `is_cofiltered` if
1. for every pair of objects there exists another object "to the left",
2. for every pair of parallel morphisms there exists a morphism to the left so the compositions
   are equal, and
3. there exists some object.

See https://stacks.math.columbia.edu/tag/04AZ.
-/
class is_cofiltered extends is_cofiltered_or_empty C : Prop :=
[nonempty : nonempty C]

@[priority 100]
instance is_cofiltered_or_empty_of_semilattice_inf
  (α : Type u) [semilattice_inf α] : is_cofiltered_or_empty α :=
{ cocone_objs := λ X Y, ⟨X ⊓ Y, hom_of_le inf_le_left, hom_of_le inf_le_right, trivial⟩,
  cocone_maps := λ X Y f g, ⟨X, 𝟙 _, (by ext)⟩, }

@[priority 100]
instance is_cofiltered_of_semilattice_inf_nonempty
  (α : Type u) [semilattice_inf α] [nonempty α] : is_cofiltered α := {}

-- Sanity checks
example (α : Type u) [semilattice_inf_bot α] : is_cofiltered α := by apply_instance
example (α : Type u) [semilattice_inf_top α] : is_cofiltered α := by apply_instance

namespace is_cofiltered

variables {C} [is_cofiltered C]

/--
`min j j'` is an arbitrary choice of object to the left of both `j` and `j'`,
whose existence is ensured by `is_cofiltered`.
-/
noncomputable def min (j j' : C) : C :=
(is_cofiltered_or_empty.cocone_objs j j').some

/--
`min_to_left j j'` is an arbitrarily choice of morphism from `min j j'` to `j`,
whose existence is ensured by `is_cofiltered`.
-/
noncomputable def min_to_left (j j' : C) : min j j' ⟶ j :=
(is_cofiltered_or_empty.cocone_objs j j').some_spec.some

/--
`min_to_right j j'` is an arbitrarily choice of morphism from `min j j'` to `j'`,
whose existence is ensured by `is_cofiltered`.
-/
noncomputable def min_to_right (j j' : C) : min j j' ⟶ j' :=
(is_cofiltered_or_empty.cocone_objs j j').some_spec.some_spec.some

/--
`eq f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of object
which admits a morphism `eq_hom f f' : eq f f' ⟶ j` such that
`eq_condition : eq_hom f f' ≫ f = eq_hom f f' ≫ f'`.
Its existence is ensured by `is_cofiltered`.
-/
noncomputable def eq {j j' : C} (f f' : j ⟶ j') : C :=
(is_cofiltered_or_empty.cocone_maps f f').some

/--
`eq_hom f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of morphism
`eq_hom f f' : eq f f' ⟶ j` such that
`eq_condition : eq_hom f f' ≫ f = eq_hom f f' ≫ f'`.
Its existence is ensured by `is_cofiltered`.
-/
noncomputable def eq_hom {j j' : C} (f f' : j ⟶ j') : eq f f' ⟶ j :=
(is_cofiltered_or_empty.cocone_maps f f').some_spec.some

/--
`eq_condition f f'`, for morphisms `f f' : j ⟶ j'`, is the proof that
`eq_hom f f' ≫ f = eq_hom f f' ≫ f'`.
-/
@[simp, reassoc]
lemma eq_condition {j j' : C} (f f' : j ⟶ j') : eq_hom f f' ≫ f = eq_hom f f' ≫ f' :=
(is_cofiltered_or_empty.cocone_maps f f').some_spec.some_spec

open category_theory.limits

/--
Any finite collection of objects in a cofiltered category has an object "to the left".
-/
lemma inf_objs_exists (O : finset C) : ∃ (S : C), ∀ {X}, X ∈ O → _root_.nonempty (S ⟶ X) :=
begin
  classical,
  apply finset.induction_on O,
  { exact ⟨is_cofiltered.nonempty.some, (by rintros - ⟨⟩)⟩, },
  { rintros X O' nm ⟨S', w'⟩,
    use min X S',
    rintros Y mY,
    by_cases h : X = Y,
    { subst h, exact ⟨min_to_left _ _⟩, },
    { exact ⟨min_to_right _ _ ≫ (w' (by finish)).some⟩, }, }
end

variables (O : finset C) (H : finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y))

/--
Given any `finset` of objects `{X, ...}` and
indexed collection of `finset`s of morphisms `{f, ...}` in `C`,
there exists an object `S`, with a morphism `T X : S ⟶ X` from each `X`,
such that the triangles commute: `T X ≫ f = T Y`, for `f : X ⟶ Y` in the `finset`.
-/
lemma inf_exists :
  ∃ (S : C) (T : Π {X : C}, X ∈ O → (S ⟶ X)), ∀ {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y},
    (⟨X, Y, mX, mY, f⟩ : (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y)) ∈ H → T mX ≫ f = T mY :=
begin
  classical,
  apply finset.induction_on H,
  { obtain ⟨S, f⟩ := inf_objs_exists O,
    refine ⟨S, λ X mX, (f mX).some, _⟩,
    rintros - - - - - ⟨⟩, },
  { rintros ⟨X, Y, mX, mY, f⟩ H' nmf ⟨S', T', w'⟩,
    refine ⟨eq (T' mX ≫ f) (T' mY), λ Z mZ, eq_hom (T' mX ≫ f) (T' mY) ≫ T' mZ, _⟩,
    intros X' Y' mX' mY' f' mf',
    rw [category.assoc],
    by_cases h : X = X' ∧ Y = Y',
    { rcases h with ⟨rfl, rfl⟩,
      by_cases hf : f = f',
      { subst hf,
        apply eq_condition, },
      { rw @w' _ _ mX mY f' (by simpa [hf ∘ eq.symm] using mf') }, },
    { rw @w' _ _ mX' mY' f' (by finish), }, },
end

/--
An arbitrary choice of object "to the left"
of a finite collection of objects `O` and morphisms `H`,
making all the triangles commute.
-/
noncomputable
def inf : C :=
(inf_exists O H).some

/--
The morphisms from `inf O H`.
-/
noncomputable
def inf_to {X : C} (m : X ∈ O) :
  inf O H ⟶ X :=
(inf_exists O H).some_spec.some m

/--
The triangles consisting of a morphism in `H` and the maps from `inf O H` commute.
-/
lemma inf_to_commutes
  {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y}
  (mf : (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) ∈ H) :
  inf_to O H mX ≫ f = inf_to O H mY :=
(inf_exists O H).some_spec.some_spec mX mY mf

variables {J : Type v} [small_category J] [fin_category J]

/--
If we have `is_cofiltered C`, then for any functor `F : J ⥤ C` with `fin_category J`,
there exists a cone over `F`.
-/
lemma cone_nonempty (F : J ⥤ C) : _root_.nonempty (cone F) :=
begin
  classical,
  let O := (finset.univ.image F.obj),
  let H : finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) :=
    finset.univ.bUnion (λ X : J, finset.univ.bUnion (λ Y : J, finset.univ.image (λ f : X ⟶ Y,
      ⟨F.obj X, F.obj Y, by simp, by simp, F.map f⟩))),
  obtain ⟨Z, f, w⟩ := inf_exists O H,
  refine ⟨⟨Z, ⟨λ X, f (by simp), _⟩⟩⟩,
  intros j j' g,
  dsimp,
  simp only [category.id_comp],
  symmetry,
  apply w,
  simp only [finset.mem_univ, finset.mem_bUnion, exists_and_distrib_left,
    exists_prop_of_true, finset.mem_image],
  exact ⟨j, rfl, j', g, (by simp)⟩,
end

/--
An arbitrary choice of cone over `F : J ⥤ C`, for `fin_category J` and `is_cofiltered C`.
-/
noncomputable def cone (F : J ⥤ C) : cone F :=
(cone_nonempty F).some

variables {D : Type u₁} [category.{v₁} D]

/--
If `C` is cofiltered, and we have a functor `L : C ⥤ D` with a right adjoint,
then `D` is cofiltered.
-/
lemma of_left_adjoint {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) : is_cofiltered D :=
{ cocone_objs := λ X Y,
    ⟨L.obj (min (R.obj X) (R.obj Y)),
      (h.hom_equiv _ X).symm (min_to_left _ _), (h.hom_equiv _ Y).symm (min_to_right _ _), ⟨⟩⟩,
  cocone_maps := λ X Y f g,
    ⟨L.obj (eq (R.map f) (R.map g)), (h.hom_equiv _ _).symm (eq_hom _ _),
     by rw [← h.hom_equiv_naturality_right_symm, ← h.hom_equiv_naturality_right_symm,
       eq_condition]⟩,
  nonempty := is_cofiltered.nonempty.map L.obj }

/-- If `C` is cofiltered, and we have a left adjoint functor `L : C ⥤ D`, then `D` is cofiltered. -/
lemma of_is_left_adjoint (L : C ⥤ D) [is_left_adjoint L] : is_cofiltered D :=
of_left_adjoint (adjunction.of_left_adjoint L)

/-- Being cofiltered is preserved by equivalence of categories. -/
lemma of_equivalence (h : C ≌ D) : is_cofiltered D :=
of_left_adjoint h.to_adjunction

end is_cofiltered

section opposite
open opposite

instance is_cofiltered_op_of_is_filtered [is_filtered C] : is_cofiltered Cᵒᵖ :=
{ cocone_objs := λ X Y, ⟨op (is_filtered.max X.unop Y.unop),
    (is_filtered.left_to_max _ _).op, (is_filtered.right_to_max _ _).op, trivial⟩,
  cocone_maps := λ X Y f g, ⟨op (is_filtered.coeq f.unop g.unop),
    (is_filtered.coeq_hom _ _).op, begin
      rw [(show f = f.unop.op, by simp), (show g = g.unop.op, by simp),
        ← op_comp, ← op_comp],
      congr' 1,
      exact is_filtered.coeq_condition f.unop g.unop,
    end⟩,
  nonempty := ⟨op is_filtered.nonempty.some⟩ }

instance is_filtered_op_of_is_cofiltered [is_cofiltered C] : is_filtered Cᵒᵖ :=
{ cocone_objs := λ X Y, ⟨op (is_cofiltered.min X.unop Y.unop),
    (is_cofiltered.min_to_left X.unop Y.unop).op,
    (is_cofiltered.min_to_right X.unop Y.unop).op, trivial⟩,
  cocone_maps := λ X Y f g, ⟨op (is_cofiltered.eq f.unop g.unop),
    (is_cofiltered.eq_hom f.unop g.unop).op, begin
      rw [(show f = f.unop.op, by simp), (show g = g.unop.op, by simp),
        ← op_comp, ← op_comp],
      congr' 1,
      exact is_cofiltered.eq_condition f.unop g.unop,
    end⟩,
  nonempty := ⟨op is_cofiltered.nonempty.some⟩ }

end opposite

end category_theory
