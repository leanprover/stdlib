/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Functors with two arguments
-/
import logic.function.basic
import control.functor
import tactic.core

universes u₀ u₁ u₂ v₀ v₁ v₂

open function

class bifunctor (F : Type u₀ → Type u₁ → Type u₂) :=
(bimap : Π {α α' β β'}, (α → α') → (β → β') → F α β → F α' β')
export bifunctor ( bimap )

class is_lawful_bifunctor (F : Type u₀ → Type u₁ → Type u₂) [bifunctor F] :=
(id_bimap : Π {α β} (x : F α β), bimap id id x = x)
(bimap_bimap : Π {α₀ α₁ α₂ β₀ β₁ β₂} (f : α₀ → α₁) (f' : α₁ → α₂)
  (g : β₀ → β₁) (g' : β₁ → β₂) (x : F α₀ β₀),
  bimap f' g' (bimap f g x) = bimap (f' ∘ f) (g' ∘ g) x)

export is_lawful_bifunctor (id_bimap bimap_bimap)

attribute [higher_order bimap_id_id] id_bimap
attribute [higher_order bimap_comp_bimap] bimap_bimap

export is_lawful_bifunctor (bimap_id_id bimap_comp_bimap)
variables {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F]

namespace bifunctor

@[reducible]
def fst {α α' β} (f : α → α') : F α β → F α' β :=
bimap f id

@[reducible]
def snd {α β β'} (f : β → β') : F α β → F α β' :=
bimap id f

variable [is_lawful_bifunctor F]

@[higher_order fst_id]
lemma id_fst : Π {α β} (x : F α β), fst id x = x :=
@id_bimap _ _ _

@[higher_order snd_id]
lemma id_snd : Π {α β} (x : F α β), snd id x = x :=
@id_bimap _ _ _

@[higher_order fst_comp_fst]
lemma comp_fst {α₀ α₁ α₂ β}
  (f : α₀ → α₁) (f' : α₁ → α₂) (x : F α₀ β) :
  fst f' (fst f x) = fst (f' ∘ f)  x :=
by simp [fst,bimap_bimap]

@[higher_order fst_comp_snd]
lemma fst_snd {α₀ α₁ β₀ β₁}
  (f : α₀ → α₁) (f' : β₀ → β₁) (x : F α₀ β₀) :
  fst f (snd f' x) = bimap f f' x :=
by simp [fst,bimap_bimap]

@[higher_order snd_comp_fst]
lemma snd_fst {α₀ α₁ β₀ β₁}
  (f : α₀ → α₁) (f' : β₀ → β₁) (x : F α₀ β₀) :
  snd f' (fst f x) = bimap f f' x :=
by simp [snd,bimap_bimap]

@[higher_order snd_comp_snd]
lemma comp_snd {α β₀ β₁ β₂}
  (g : β₀ → β₁) (g' : β₁ → β₂) (x : F α β₀) :
  snd g' (snd g x) = snd (g' ∘ g) x :=
by simp [snd,bimap_bimap]

attribute [functor_norm] bimap_bimap comp_snd comp_fst
  snd_comp_snd snd_comp_fst fst_comp_snd fst_comp_fst bimap_comp_bimap
  bimap_id_id fst_id snd_id

end bifunctor
open functor
instance : bifunctor prod :=
{ bimap := @prod.map }

@[simp] lemma prod.bifunctor_apply {α α' β β'} (f : α → α') (g : β → β') :
  (bimap f g : α × β → α' × β') = prod.map f g := rfl

instance : is_lawful_bifunctor prod :=
by refine { .. }; intros; cases x; refl

instance bifunctor.const : bifunctor const :=
{ bimap := (λ α α' β β f _, f) }

@[simp] lemma functor.const.bifunctor_apply {α α' β β'} (f : α → α') (g : β → β') :
  (bimap f g : functor.const α β → functor.const α' β') = f := rfl

instance is_lawful_bifunctor.const : is_lawful_bifunctor const  :=
by refine { .. }; intros; refl

instance bifunctor.flip : bifunctor (flip F) :=
{ bimap := (λ α α' β β' f f' x, (bimap f' f x : F β' α')) }

@[simp] lemma flip.bifunctor_apply {α α' β β'} (f : α → α') (g : β → β') :
  (bimap f g : flip F α β → flip F α' β') = (bimap g f : F β α → F β' α') := rfl

instance is_lawful_bifunctor.flip [is_lawful_bifunctor F] : is_lawful_bifunctor (flip F)  :=
by refine { .. }; intros; simp [bimap] with functor_norm

instance : bifunctor sum :=
{ bimap := @sum.map }

instance : is_lawful_bifunctor sum :=
by refine { .. }; intros; cases x; refl

open bifunctor functor

@[priority 10]
instance bifunctor.functor {α} : functor (F α) :=
{ map := λ _ _, snd }

@[priority 10]
instance bifunctor.is_lawful_functor [is_lawful_bifunctor F] {α} : is_lawful_functor (F α) :=
by refine {..}; intros; simp [functor.map] with functor_norm

section bicompl

variables (G : Type* → Type u₀) (H : Type* → Type u₁) [functor G] [functor H]

instance : bifunctor (bicompl F G H) :=
{ bimap := λ α α' β β' f f' x, (bimap (map f) (map f') x : F (G α') (H β')) }

instance [is_lawful_functor G]  [is_lawful_functor H] [is_lawful_bifunctor F] :
  is_lawful_bifunctor (bicompl F G H) :=
by constructor; intros; simp [bimap,map_id,map_comp_map] with functor_norm

end bicompl
section bicompr

variables (G : Type u₂ → Type*) [functor G]

instance : bifunctor (bicompr G F) :=
{ bimap := λ α α' β β' f f' x, (map (bimap f f') x : G (F α' β')) }

instance [is_lawful_functor G] [is_lawful_bifunctor F] :
  is_lawful_bifunctor (bicompr G F) :=
by constructor; intros; simp [bimap] with functor_norm

end bicompr
