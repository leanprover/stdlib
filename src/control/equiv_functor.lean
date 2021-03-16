/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import category_theory.category
import data.equiv.functor

/-!
# Functions functorial with respect to equivalences

An `equiv_functor` is a function from `Type → Type` equipped with the additional data of
coherently mapping equivalences to equivalences.

In categorical language, it is an endofunctor of the "core" of the category `Type`.
-/

universes u₀ u₁ u₂ v₀ v₁ v₂

open function

/--
An `equiv_functor` is only functorial with respect to equivalences.

To construct an `equiv_functor`, it suffices to supply just the function `f α → f β` from
an equivalence `α ≃ β`, and then prove the functor laws. It's then a consequence that
this function is part of an equivalence, provided by `equiv_functor.map_equiv`.
-/
class equiv_functor (f : Type u₀ → Type u₁) :=
(map : Π {α β}, (α ≃ β) → (f α → f β))
(map_refl' : Π α, map (equiv.refl α) = @id (f α) . obviously)
(map_trans' : Π {α β γ} (k : α ≃ β) (h : β ≃ γ),
  map (k.trans h) = (map h) ∘ (map k) . obviously)

restate_axiom equiv_functor.map_refl'
restate_axiom equiv_functor.map_trans'
attribute [simp] equiv_functor.map_refl

namespace equiv_functor

section
variables (f : Type u₀ → Type u₁) [equiv_functor f] {α β : Type u₀} (e : α ≃ β)

/-- An `equiv_functor` in fact takes every equiv to an equiv. -/
def map_equiv :
  f α ≃ f β :=
{ to_fun := equiv_functor.map e,
  inv_fun := equiv_functor.map e.symm,
  left_inv := λ x, by { convert (congr_fun (equiv_functor.map_trans e e.symm) x).symm, simp, },
  right_inv := λ y, by { convert (congr_fun (equiv_functor.map_trans e.symm e) y).symm, simp, }, }

lemma map_equiv_apply (x : f α) :
  map_equiv f e x = equiv_functor.map e x := rfl

@[simp] lemma map_equiv_apply' : (map_equiv f e : f α → f β) = equiv_functor.map e := rfl

lemma map_equiv_symm_apply (y : f β) :
  (map_equiv f e).symm y = equiv_functor.map e.symm y := rfl

@[simp] lemma map_equiv_refl (α) :
  map_equiv f (equiv.refl α) = equiv.refl (f α) :=
by simpa [equiv_functor.map_equiv]

@[simp] lemma map_equiv_symm :
  (map_equiv f e).symm = map_equiv f e.symm :=
equiv.ext $ map_equiv_symm_apply f e

/--
The composition of `map_equiv`s is carried over the `equiv_functor`.
For plain `functor`s, this lemma is named `map_map` when applied
or `map_comp_map` when not applied.
-/
@[simp] lemma map_equiv_trans {γ : Type u₀} (ab : α ≃ β) (bc : β ≃ γ) :
  (map_equiv f ab).trans (map_equiv f bc) = map_equiv f (ab.trans bc) :=
equiv.ext $ λ x, by simp [map_equiv, map_trans']

end

@[priority 100, simps]
instance of_is_lawful_functor
  (f : Type u₀ → Type u₁) [functor f] [is_lawful_functor f] : equiv_functor f :=
{ map := λ α β e, functor.map e,
  map_refl' := λ α, by { ext, apply is_lawful_functor.id_map, },
  map_trans' := λ α β γ k h, by { ext x, apply (is_lawful_functor.comp_map k h x), } }

lemma map_equiv.injective
  (f : Type u₀ → Type u₁) [applicative f] [is_lawful_applicative f] {α β : Type u₀}
  (h : ∀ γ, function.injective (pure : γ → f γ)) :
  function.injective (@equiv_functor.map_equiv f _ α β) :=
λ e₁ e₂ H, equiv.ext $ λ x, h β (by simpa [equiv_functor.map] using equiv.congr_fun H (pure x))

end equiv_functor
