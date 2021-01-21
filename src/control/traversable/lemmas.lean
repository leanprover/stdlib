/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Lemmas about traversing collections.

Inspired by:

    The Essence of the Iterator Pattern
    Jeremy Gibbons and Bruno César dos Santos Oliveira
    In Journal of Functional Programming. Vol. 19. No. 3&4. Pages 377−402. 2009.
    <http://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf>
-/
import control.applicative

universe variables u

open is_lawful_traversable
open function (hiding comp)
open functor

attribute [functor_norm] is_lawful_traversable.naturality
attribute [simp] is_lawful_traversable.id_traverse

namespace traversable

variable {t : Type u → Type u}
variables [traversable t] [is_lawful_traversable t]
variables F G : Type u → Type u

variables [applicative F] [is_lawful_applicative F]
variables [applicative G] [is_lawful_applicative G]
variables {α β γ : Type u}
variables g : α → F β
variables h : β → G γ
variables f : β → γ

/-- The natural applicative transformation from the identity functor
to `F`, defined by `pure : Π {α}, α → F α`. -/
def pure_transformation : applicative_transformation id F :=
{ app := @pure F _,
  preserves_pure' := λ α x, rfl,
  preserves_seq' := λ α β f x, by simp; refl }

@[simp] theorem pure_transformation_apply {α} (x : id α) :
  (pure_transformation F) x = pure x := rfl


variables {F G} (x : t β)

lemma map_eq_traverse_id : map f = @traverse t _ _ _ _ _ (id.mk ∘ f) :=
funext $ λ y, (traverse_eq_map_id f y).symm

theorem map_traverse (x : t α) :
  map f <$> traverse g x = traverse (map f ∘ g) x :=
begin
  rw @map_eq_traverse_id t _ _ _ _ f,
  refine (comp_traverse (id.mk ∘ f) g x).symm.trans _,
  congr, apply comp.applicative_comp_id
end

theorem traverse_map (f : β → F γ) (g : α → β) (x : t α) :
  traverse f (g <$> x) = traverse (f ∘ g) x :=
begin
  rw @map_eq_traverse_id t _ _ _ _ g,
  refine (comp_traverse f (id.mk ∘ g) x).symm.trans _,
  congr, apply comp.applicative_id_comp
end

lemma pure_traverse (x : t α) :
  traverse pure x = (pure x : F (t α)) :=
by have : traverse pure x = pure (traverse id.mk x) :=
     (naturality (pure_transformation F) id.mk x).symm;
   rwa id_traverse at this

lemma id_sequence (x : t α) :
  sequence (id.mk <$> x) = id.mk x :=
by simp [sequence, traverse_map, id_traverse]; refl

lemma comp_sequence (x : t (F (G α))) :
  sequence (comp.mk <$> x) = comp.mk (sequence <$> sequence x) :=
by simp [sequence, traverse_map]; rw ← comp_traverse; simp [map_id]

lemma naturality' (η : applicative_transformation F G) (x : t (F α)) :
  η (sequence x) = sequence (@η _ <$> x) :=
by simp [sequence, naturality, traverse_map]

@[functor_norm]
lemma traverse_id :
  traverse id.mk = (id.mk : t α → id (t α)) :=
by ext; simp [id_traverse]; refl

@[functor_norm]
lemma traverse_comp (g : α → F β) (h : β → G γ) :
  traverse (comp.mk ∘ map h ∘ g) =
  (comp.mk ∘ map (traverse h) ∘ traverse g : t α → comp F G (t γ)) :=
by ext; simp [comp_traverse]

lemma traverse_eq_map_id' (f : β → γ) :
  traverse (id.mk ∘ f) =
  id.mk ∘ (map f : t β → t γ) :=
by ext;rw traverse_eq_map_id

-- @[functor_norm]
lemma traverse_map' (g : α → β) (h : β → G γ) :
  traverse (h ∘ g) =
  (traverse h ∘ map g : t α → G (t γ)) :=
by ext; simp [traverse_map]

lemma map_traverse' (g : α → G β) (h : β → γ) :
  traverse (map h ∘ g) =
  (map (map h) ∘ traverse g : t α → G (t γ)) :=
by ext; simp [map_traverse]

lemma naturality_pf (η : applicative_transformation F G) (f : α → F β) :
  traverse (@η _ ∘ f) = @η _ ∘ (traverse f : t α → F (t β)) :=
by ext; simp [naturality]

end traversable
