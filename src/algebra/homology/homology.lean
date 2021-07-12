/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.image_to_kernel
import algebra.homology.homological_complex
import category_theory.graded_object

/-!
# The homology of a complex

Given `C : homological_complex V c`, we have `C.cycles i` and `C.boundaries i`,
both defined as subobjects of `C.X i`.

We show these are functorial with respect to chain maps,
as `C.cycles_map f i` and `C.boundaries_map f i`.

As a consequence we construct `homology_functor i : homological_complex V c ⥤ V`,
computing the `i`-th homology.
-/

universes v u

open category_theory category_theory.limits

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_morphisms V]
variables {c : complex_shape ι} (C : homological_complex V c)

open_locale classical zero_object
noncomputable theory

namespace homological_complex

variables [has_zero_object V]

section cycles
variables [has_kernels V]

/-- The cycles at index `i`, as a subobject. -/
def cycles (i : ι) : subobject (C.X i) :=
kernel_subobject (C.d_from i)

@[simp, reassoc]
lemma cycles_arrow_d_from (i : ι) : (C.cycles i).arrow ≫ C.d_from i = 0 :=
by { dsimp [cycles], simp, }

lemma cycles_eq_kernel_subobject {i j : ι} (r : c.rel i j) :
  C.cycles i = kernel_subobject (C.d i j) :=
C.kernel_from_eq_kernel r

/--
The underlying object of `C.cycles i` is isomorphic to `kernel (C.d i j)`,
for any `j` such that `rel i j`.
-/
def cycles_iso_kernel {i j : ι} (r : c.rel i j) :
  (C.cycles i : V) ≅ kernel (C.d i j) :=
subobject.iso_of_eq _ _ (C.cycles_eq_kernel_subobject r) ≪≫
  kernel_subobject_iso (C.d i j)

lemma cycles_eq_top {i} (h : c.next i = none) : C.cycles i = ⊤ :=
begin
  rw eq_top_iff,
  apply le_kernel_subobject,
  rw [C.d_from_eq_zero h, comp_zero],
end

end cycles

section boundaries
variables [has_images V]

/-- The boundaries at index `i`, as a subobject. -/
abbreviation boundaries (C : homological_complex V c) (j : ι) : subobject (C.X j) :=
image_subobject (C.d_to j)

lemma boundaries_eq_image_subobject [has_equalizers V] {i j : ι} (r : c.rel i j) :
  C.boundaries j = image_subobject (C.d i j) :=
C.image_to_eq_image r

/--
The underlying object of `C.boundaries j` is isomorphic to `image (C.d i j)`,
for any `i` such that `rel i j`.
-/
def boundaries_iso_image [has_equalizers V] {i j : ι} (r : c.rel i j) :
  (C.boundaries j : V) ≅ image (C.d i j) :=
subobject.iso_of_eq _ _ (C.boundaries_eq_image_subobject r) ≪≫
  image_subobject_iso (C.d i j)

lemma boundaries_eq_bot {j} (h : c.prev j = none) : C.boundaries j = ⊥ :=
begin
  rw eq_bot_iff,
  refine image_subobject_le _ 0 _,
  rw [C.d_to_eq_zero h, zero_comp],
end

end boundaries

section
variables [has_kernels V] [has_images V]

lemma boundaries_le_cycles (C : homological_complex V c) (i : ι) :
  C.boundaries i ≤ C.cycles i :=
image_le_kernel _ _ (C.d_to_comp_d_from i)

/--
The canonical map from `boundaries i` to `cycles i`.
-/
abbreviation boundaries_to_cycles (C : homological_complex V c) (i : ι) :
  (C.boundaries i : V) ⟶ (C.cycles i : V) :=
image_to_kernel _ _ (C.d_to_comp_d_from i)

/-- Prefer `boundaries_to_cycles`. -/
@[simp] lemma image_to_kernel_as_boundaries_to_cycles (C : homological_complex V c) (i : ι) (h) :
  (C.boundaries i).of_le (C.cycles i) h = C.boundaries_to_cycles i :=
rfl

@[simp, reassoc]
lemma boundaries_to_cycles_arrow (C : homological_complex V c) (i : ι) :
  C.boundaries_to_cycles i ≫ (C.cycles i).arrow = (C.boundaries i).arrow :=
by { dsimp [cycles], simp, }

variables [has_cokernels V]

/--
The homology of a complex at index `i`.
-/
abbreviation homology (C : homological_complex V c) (i : ι) : V :=
homology (C.d_to i) (C.d_from i) (C.d_to_comp_d_from i)

end

end homological_complex

open homological_complex

/-! Computing the cycles is functorial. -/
section
variables [has_zero_object V] [has_kernels V]
variables {C₁ C₂ C₃ : homological_complex V c} (f : C₁ ⟶ C₂)

/--
The morphism between cycles induced by a chain map.
-/
abbreviation cycles_map (f : C₁ ⟶ C₂) (i : ι) : (C₁.cycles i : V) ⟶ (C₂.cycles i : V) :=
subobject.factor_thru _ ((C₁.cycles i).arrow ≫ f.f i) (kernel_subobject_factors _ _ (by simp))

@[simp] lemma cycles_map_arrow (f : C₁ ⟶ C₂) (i : ι) :
  (cycles_map f i) ≫ (C₂.cycles i).arrow = (C₁.cycles i).arrow ≫ f.f i :=
by { simp, }

@[simp] lemma cycles_map_id (i : ι) : cycles_map (𝟙 C₁) i = 𝟙 _ :=
by { dunfold cycles_map, simp, }

@[simp] lemma cycles_map_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
  cycles_map (f ≫ g) i = cycles_map f i ≫ cycles_map g i :=
by { dunfold cycles_map, simp [subobject.factor_thru_right], }

variables (V c)

/-- Cycles as a functor. -/
@[simps]
def cycles_functor (i : ι) : homological_complex V c ⥤ V :=
{ obj := λ C, C.cycles i,
  map := λ C₁ C₂ f, cycles_map f i, }

end

/-! Computing the boundaries is functorial. -/
section
variables [has_zero_object V] [has_images V] [has_image_maps V]
variables {C₁ C₂ C₃ : homological_complex V c} (f : C₁ ⟶ C₂)

/--
The morphism between boundaries induced by a chain map.
-/
abbreviation boundaries_map (f : C₁ ⟶ C₂) (i : ι) : (C₁.boundaries i : V) ⟶ (C₂.boundaries i : V) :=
image_subobject_map (f.sq_to i)

variables (V c)

/-- Boundaries as a functor. -/
@[simps]
def boundaries_functor (i : ι) : homological_complex V c ⥤ V :=
{ obj := λ C, C.boundaries i,
  map := λ C₁ C₂ f, image_subobject_map (f.sq_to i), }

end

section

/-! The `boundaries_to_cycles` morphisms are natural. -/
variables [has_zero_object V] [has_equalizers V] [has_images V] [has_image_maps V]
variables {C₁ C₂ : homological_complex V c} (f : C₁ ⟶ C₂)

@[simp, reassoc]
lemma boundaries_to_cycles_naturality (i : ι) :
  boundaries_map f i ≫ C₂.boundaries_to_cycles i = C₁.boundaries_to_cycles i ≫ cycles_map f i :=
by { ext, simp, }

variables (V c)

/-- The natural transformation from the boundaries functor to the cycles functor. -/
@[simps] def boundaries_to_cycles_nat_trans (i : ι) :
  boundaries_functor V c i ⟶ cycles_functor V c i :=
{ app := λ C, C.boundaries_to_cycles i,
  naturality' := λ C₁ C₂ f, boundaries_to_cycles_naturality f i, }

/-- The `i`-th homology, as a functor to `V`. -/
@[simps]
def homology_functor [has_cokernels V] (i : ι) :
  homological_complex V c ⥤ V :=
-- It would be nice if we could just write
-- `cokernel (boundaries_to_cycles_nat_trans V c i)`
-- here, but universe implementation details get in the way...
{ obj := λ C, C.homology i,
  map := λ C₁ C₂ f, _root_.homology.map _ _ (f.sq_to i) (f.sq_from i) rfl,
  map_id' :=
  begin
    intros, ext1,
    simp only [homology.π_map, kernel_subobject_map_id, hom.sq_from_id,
      category.id_comp, category.comp_id]
  end,
  map_comp' :=
  begin
    intros, ext1,
    simp only [hom.sq_from_comp, kernel_subobject_map_comp, homology.π_map_assoc,
      homology.π_map, category.assoc]
  end }

/-- The homology functor from `ι`-indexed complexes to `ι`-graded objects in `V`. -/
@[simps] def graded_homology_functor [has_cokernels V] :
  homological_complex V c ⥤ graded_object ι V :=
{ obj := λ C i, C.homology i,
  map := λ C C' f i, (homology_functor V c i).map f,
  map_id' :=
  begin
    intros, ext,
    simp only [pi.id_apply, homology.π_map, homology_functor_map, kernel_subobject_map_id,
      hom.sq_from_id, category.id_comp, category.comp_id]
  end,
  map_comp' :=
  begin
    intros, ext,
    simp only [hom.sq_from_comp, kernel_subobject_map_comp, homology.π_map_assoc,
      pi.comp_apply, homology.π_map, homology_functor_map, category.assoc]
  end }

end
