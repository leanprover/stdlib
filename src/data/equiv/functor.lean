/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon, Scott Morrison
-/
import data.equiv.basic
import control.bifunctor

/-!
# Functor and bifunctors can be applied to `equiv`s.

We define
```lean
def functor.map_equiv (f : Type u → Type v) [functor f] [is_lawful_functor f] :
  α ≃ β → f α ≃ f β
```
and
```lean
def bifunctor.map_equiv (F : Type u → Type v → Type w) [bifunctor F] [is_lawful_bifunctor F] :
  α ≃ β → α' ≃ β' → F α α' ≃ F β β'
```
-/

universes u v w

variables {α β : Type u}
open equiv

namespace functor

variables (f : Type u → Type v) [functor f] [is_lawful_functor f]

/-- Apply a functor to an `equiv`. -/
def map_equiv (h : α ≃ β) : f α ≃ f β :=
{ to_fun    := map h,
  inv_fun   := map h.symm,
  left_inv  := λ x, by simp [map_map],
  right_inv := λ x, by simp [map_map] }

@[simp]
lemma map_equiv_apply (h : α ≃ β) (x : f α) :
  (map_equiv f h : f α ≃ f β) x = map h x := rfl

@[simp]
lemma map_equiv_symm_apply (h : α ≃ β) (y : f β) :
  (map_equiv f h : f α ≃ f β).symm y = map h.symm y := rfl

@[simp]
lemma map_equiv_refl : map_equiv f (equiv.refl α) = equiv.refl (f α) :=
begin
  ext x,
  simp only [map_equiv_apply, refl_apply],
  exact is_lawful_functor.id_map x,
end

end functor

namespace bifunctor

variables {α' β' : Type v} (F : Type u → Type v → Type w) [bifunctor F] [is_lawful_bifunctor F]

/-- Apply a bifunctor to a pair of `equiv`s. -/
def map_equiv (h : α ≃ β) (h' : α' ≃ β') : F α α' ≃ F β β' :=
{ to_fun    := bimap h h',
  inv_fun   := bimap h.symm h'.symm,
  left_inv  := λ x, by simp [bimap_bimap, id_bimap],
  right_inv := λ x, by simp [bimap_bimap, id_bimap] }

lemma map_equiv_apply (h : α ≃ β) (h' : α' ≃ β') (x : F α α') :
  (map_equiv F h h' : F α α' ≃ F β β') x = bimap h h' x := rfl

@[simp] lemma map_equiv_apply' (h : α ≃ β) (h' : α' ≃ β') :
  (map_equiv F h h' : F α α' → F β β') = bimap h h' := rfl

lemma map_equiv_symm_apply (h : α ≃ β) (h' : α' ≃ β') (y : F β β') :
  (map_equiv F h h' : F α α' ≃ F β β').symm y = bimap h.symm h'.symm y := rfl

@[simp] lemma map_equiv_symm (h : α ≃ β) (h' : α' ≃ β') :
  (map_equiv F h h').symm = map_equiv F h.symm h'.symm := rfl

@[simp]
lemma map_equiv_refl_refl : map_equiv F (equiv.refl α) (equiv.refl α') = equiv.refl (F α α') :=
begin
  ext x,
  simp [id_bimap]
end

end bifunctor
