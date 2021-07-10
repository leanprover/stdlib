/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

The Kleisli construction on the Type category

TODO: generalise this to work with category_theory.monad
-/
import category_theory.category

/-!
# The Kleisli construction on the Type category

Define the Kleisli category for (control) monads.
`category_theory/monad/kleisli` defines the general version for a monad on `C`, and demonstrates
the equivalence between the two.
-/

universes u v

namespace category_theory

/-- The Kleisli category on the (type-)monad `m`. Note that the monad is not assumed to be lawful
yet. -/
@[nolint unused_arguments]
def Kleisli (m : Type u → Type v) := Type u

/-- Construct an object of the Kleisli category from a type. -/
def Kleisli.mk (m) (α : Type u) : Kleisli m := α

instance Kleisli.category_struct {m} [monad.{u v} m] : category_struct (Kleisli m) :=
{ hom := λ α β, α → m β,
  id := λ α x, pure x,
  comp := λ X Y Z f g, f >=> g }

instance Kleisli.category {m} [monad.{u v} m] [is_lawful_monad m] : category (Kleisli m) :=
by refine { id_comp' := _, comp_id' := _, assoc' := _ };
   intros; ext; unfold_projs; simp only [(>=>)] with functor_norm

@[simp] lemma Kleisli.id_def {m} [monad m] (α : Kleisli m) :
  𝟙 α = @pure m _ α := rfl

lemma Kleisli.comp_def {m} [monad m] (α β γ : Kleisli m)
  (xs : α ⟶ β) (ys : β ⟶ γ) (a : α) :
  (xs ≫ ys) a = xs a >>= ys := rfl

instance : inhabited (Kleisli id) := ⟨punit⟩
instance {α : Type u} [inhabited α] : inhabited (Kleisli.mk id α) := ⟨(default α : _)⟩
end category_theory
