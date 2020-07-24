/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Mario Carneiro

Tuples of types, and their categorical structure.

Features:

`typevec n`   : n-tuples of types
`α ⟹ β`      : n-tuples of maps
`f ⊚ g`       : composition
`mvfunctor n` : the type class of multivariate functors
`f <$$> x`    : notation for map

Also, support functions for operating with n-tuples of types, such as:

`append1 α β`    : append type `β` to n-tuple `α` to obtain an (n+1)-tuple
`drop α`         : drops the last element of an (n+1)-tuple
`last α`         : returns the last element of an (n+1)-tuple
`append_fun f g` : appends a function g to an n-tuple of functions
`drop_fun f`     : drops the last function from an n+1-tuple
`last_fun f`     : returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.
-/
import control.family

/-
n-tuples of types, as a category
-/

universes u v w

namespace category_theory.functor.fam

variables {I J : Type u} {α β γ : fam I} {F : fam I ⥤ fam J}

open fam

@[simp] theorem drop_fun_split_fun {α α' : fam (I ⊕ J)}
  (f : drop α ⟶ drop α') (g : last α ⟶ last α') :
  drop_fun (split_fun f g) = f := by ext; refl

@[simp] theorem last_fun_split_fun {α α' : fam (I⊕J)}
  (f : drop α ⟶ fam.drop α') (g : last α ⟶ last α') :
  last_fun (split_fun f g) = g := by ext; refl

open fam

theorem split_fun_inj
  {α α' : fam (I ⊕ J)} {f f' : drop α ⟶ drop α'} {g g' : last α ⟶ last α'}
  (H : split_fun f g = split_fun f' g') : f = f' ∧ g = g' :=
by rw [← drop_fun_split_fun f g, H, ← last_fun_split_fun f g, H]; simp

@[reassoc]
theorem append_fun_comp_split_fun
  {α γ : fam I} {β δ : fam J} {ε : fam (I ⊕ J)}
    (f₀ : fam.drop ε ⟶ fam.drop (α.append1 β)) (f₁ : α ⟶ γ)
    (g₀ : fam.last ε ⟶ fam.last (α.append1 β)) (g₁ : β ⟶ δ) :
  fam.split_fun f₀ g₀ ≫ fam.append_fun f₁ g₁ = fam.split_fun (f₀ ≫ f₁) (g₀ ≫ g₁) :=
(fam.split_fun_comp _ _ _ _).symm

/- for lifting predicates and relations -/

/-- `pred_last α p x` predicates `p` of the last element of `x : α.append1 β`. -/
def pred_last (α : fam I) {β : fam J} (p : Pred β) : Pred (α.append1 β)
| (sum.inl i) x := true
| (sum.inr j) x := p _ x

/-- `rel_last α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r` and all the other elements are equal. -/
def rel_last (α : fam I) {β γ : fam J} (r : Pred $ β ⊗ γ) :
  Pred (α.append1 β ⊗ α.append1 γ)
| (sum.inl i) := function.uncurry eq
| (sum.inr i) := r _

end category_theory.functor.fam
