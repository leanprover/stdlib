/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.wide_equalizers
import category_theory.limits.shapes.products
import category_theory.limits.shapes.terminal

/-!
# Constructions related to weakly initial objects

This file gives constructions related to weakly initial objects, namely:
* If a category has small products and a small weakly initial set of objects, then it has a weakly
  initial object.
* If a category has wide equalizers and a weakly initial object, then it has an initial object.

These are primarily useful to show the General Adjoint Functor Theorem.
-/
universes v u

namespace category_theory
open limits

variables {C : Type u} [category.{v} C]

/--
If `C` has (small) products and a small weakly initial set of objects, then it has a weakly initial
object.
-/
lemma has_weakly_initial_of_weakly_initial_set_and_has_products [has_products C]
  {ι : Type v} {B : ι → C} (hB : ∀ (A : C), ∃ i, nonempty (B i ⟶ A)) :
  ∃ (T : C), ∀ X, nonempty (T ⟶ X) :=
⟨∏ B, λ X, ⟨pi.π _ _ ≫ (hB X).some_spec.some⟩⟩

/--
If `C` has (small) wide equalizers and a weakly initial object, then it has an initial object.

The initial object is constructed as the wide equalizer of all endomorphisms on the given weakly
initial object.
-/
lemma has_initial_of_weakly_initial_and_has_wide_equalizers [has_wide_equalizers C]
  {T : C} (hT : ∀ X, nonempty (T ⟶ X)) :
  has_initial C :=
begin
  let endos := T ⟶ T,
  let i := wide_equalizer.ι (id : endos → endos),
  haveI : nonempty endos := ⟨𝟙 _⟩,
  have : ∀ (X : C), unique (wide_equalizer (id : endos → endos) ⟶ X),
  { intro X,
    refine ⟨⟨i ≫ classical.choice (hT X)⟩, λ a, _⟩,
    let E := equalizer a (i ≫ classical.choice (hT _)),
    let e : E ⟶ wide_equalizer id := equalizer.ι _ _,
    let h : T ⟶ E := classical.choice (hT E),
    have : ((i ≫ h) ≫ e) ≫ i = i ≫ 𝟙 _,
    { rw [category.assoc, category.assoc],
      apply wide_equalizer.condition (id : endos → endos) (h ≫ e ≫ i) },
    rw [category.comp_id, cancel_mono_id i] at this,
    haveI : split_epi e := ⟨i ≫ h, this⟩,
    rw ←cancel_epi e,
    apply equalizer.condition },
  exactI has_initial_of_unique (wide_equalizer (id : endos → endos)),
end

end category_theory
