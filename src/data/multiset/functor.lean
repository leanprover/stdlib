/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Johannes Hölzl, Simon Hudon, Kenny Lau
-/
import data.multiset.basic
import control.traversable.instances

/-!
# Functoriality of `multiset`.
-/

universes u

namespace multiset

open list

instance : functor multiset :=
{ map := @map }

@[simp] lemma fmap_def {α' β'} {s : multiset α'} (f : α' → β') : f <$> s = s.map f := rfl

instance : is_lawful_functor multiset :=
by refine { .. }; intros; simp

open is_lawful_traversable is_comm_applicative

variables {F : Type u → Type u} [applicative F] [is_comm_applicative F]
variables {α' β' : Type u} (f : α' → F β')

def traverse : multiset α' → F (multiset β') :=
quotient.lift (functor.map coe ∘ traversable.traverse f)
begin
  introv p, unfold function.comp,
  induction p,
  case perm.nil { refl },
  case perm.cons {
    have : multiset.cons <$> f p_x <*> (coe <$> traverse f p_l₁) =
      multiset.cons <$> f p_x <*> (coe <$> traverse f p_l₂),
    { rw [p_ih] },
    simpa with functor_norm },
  case perm.swap {
    have : (λa b (l:list β'), (↑(a :: b :: l) : multiset β')) <$> f p_y <*> f p_x =
      (λa b l, ↑(a :: b :: l)) <$> f p_x <*> f p_y,
    { rw [is_comm_applicative.commutative_map],
      congr, funext a b l, simpa [flip] using perm.swap b a l },
    simp [(∘), this] with functor_norm },
  case perm.trans { simp [*] }
end

instance : monad multiset :=
{ pure := λ α x, x ::ₘ 0,
  bind := @bind,
  .. multiset.functor }

@[simp] lemma pure_def {α} : (pure : α → multiset α) = (λ x, x ::ₘ 0) := rfl
@[simp] lemma bind_def {α β} : (>>=) = @bind α β := rfl

instance : is_lawful_monad multiset :=
{ bind_pure_comp_eq_map := λ α β f s, multiset.induction_on s rfl $ λ a s ih, by simp,
  pure_bind := λ α β x f, by simp,
  bind_assoc := @bind_assoc }

open functor
open traversable is_lawful_traversable

@[simp]
lemma lift_beta {α β : Type*} (x : list α) (f : list α → β)
  (h : ∀ a b : list α, a ≈ b → f a = f b) :
  quotient.lift f h (x : multiset α) = f x :=
quotient.lift_beta _ _ _

@[simp]
lemma map_comp_coe {α β} (h : α → β) :
  functor.map h ∘ coe = (coe ∘ functor.map h : list α → multiset β) :=
by funext; simp [functor.map]

lemma id_traverse {α : Type*} (x : multiset α) :
  traverse id.mk x = x :=
quotient.induction_on x begin intro, simp [traverse], refl end

lemma comp_traverse {G H : Type* → Type*}
               [applicative G] [applicative H]
               [is_comm_applicative G] [is_comm_applicative H]
               {α β γ : Type*}
               (g : α → G β) (h : β → H γ) (x : multiset α) :
  traverse (comp.mk ∘ functor.map h ∘ g) x =
  comp.mk (functor.map (traverse h) (traverse g x)) :=
quotient.induction_on x
(by intro;
    simp [traverse,comp_traverse] with functor_norm;
    simp [(<$>),(∘)] with functor_norm)

lemma map_traverse {G : Type* → Type*}
               [applicative G] [is_comm_applicative G]
               {α β γ : Type*}
               (g : α → G β) (h : β → γ)
               (x : multiset α) :
  functor.map (functor.map h) (traverse g x) =
  traverse (functor.map h ∘ g) x :=
quotient.induction_on x
(by intro; simp [traverse] with functor_norm;
    rw [is_lawful_functor.comp_map, map_traverse])

lemma traverse_map {G : Type* → Type*}
               [applicative G] [is_comm_applicative G]
               {α β γ : Type*}
               (g : α → β) (h : β → G γ)
               (x : multiset α) :
  traverse h (map g x) =
  traverse (h ∘ g) x :=
quotient.induction_on x
(by intro; simp [traverse];
    rw [← traversable.traverse_map h g];
    [ refl, apply_instance ])

lemma naturality {G H : Type* → Type*}
                [applicative G] [applicative H]
                [is_comm_applicative G] [is_comm_applicative H]
                (eta : applicative_transformation G H)
                {α β : Type*} (f : α → G β) (x : multiset α) :
  eta (traverse f x) = traverse (@eta _ ∘ f) x :=
quotient.induction_on x
(by intro; simp [traverse,is_lawful_traversable.naturality] with functor_norm)

end multiset
