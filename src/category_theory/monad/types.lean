/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bhavik Mehta
-/
import category_theory.monad.kleisli
import category_theory.category.Kleisli

/-!

# Convert from `monad` (i.e. Lean's `Type`-based monads) to `category_theory.monad`

This allows us to use these monads in category theory.

-/

namespace category_theory

section
universes u

variables (m : Type u → Type u) [_root_.monad m] [is_lawful_monad m]

instance : monad (of_type_functor m) :=
{ η           := ⟨@pure m _, assume α β f, (is_lawful_applicative.map_comp_pure f).symm ⟩,
  μ           := ⟨@mjoin m _, assume α β (f : α → β), funext $ assume a, mjoin_map_map f a ⟩,
  assoc'      := assume α, funext $ assume a, mjoin_map_mjoin a,
  left_unit'  := assume α, funext $ assume a, mjoin_pure a,
  right_unit' := assume α, funext $ assume a, mjoin_map_pure a }

/--
The `Kleisli` category of a `control.monad` is equivalent to the `kleisli` category of its
category-theoretic version, provided the monad is lawful.
-/
@[simps]
def eq : Kleisli m ≌ kleisli (of_type_functor m) :=
{ functor :=
  { obj := λ X, X,
    map := λ X Y f, f,
    map_id' := λ X, rfl,
    map_comp' := λ X Y Z f g,
    begin
      unfold_projs,
      ext,
      simp [mjoin, seq_bind_eq],
    end },
  inverse :=
  { obj := λ X, X,
    map := λ X Y f, f,
    map_id' := λ X, rfl,
    map_comp' := λ X Y Z f g,
    begin
      unfold_projs,
      ext,
      simp [mjoin, seq_bind_eq],
    end },
  unit_iso :=
  begin
    refine nat_iso.of_components (λ X, iso.refl X) (λ X Y f, _),
    change f >=> pure = pure >=> f,
    simp with functor_norm,
  end,
  counit_iso := nat_iso.of_components (λ X, iso.refl X) (λ X Y f, by tidy) }

end

end category_theory
