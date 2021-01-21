/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Instances for identity and composition functors
-/
import algebra.group.basic

universe variables u v w

section lemmas

open function

variables {F : Type u → Type v}
variables [applicative F] [is_lawful_applicative F]
variables {α β γ σ : Type u}

lemma applicative.map_seq_map (f : α → β → γ) (g : σ → β) (x : F α) (y : F σ) :
  (f <$> x) <*> (g <$> y) = (flip (∘) g ∘ f) <$> x <*> y :=
by simp [flip] with functor_norm

lemma applicative.pure_seq_eq_map' (f : α → β) :
  (<*>) (pure f : F (α → β)) = (<$>) f :=
by ext; simp with functor_norm

theorem applicative.ext {F} : ∀ {A1 : applicative F} {A2 : applicative F}
  [@is_lawful_applicative F A1] [@is_lawful_applicative F A2]
  (H1 : ∀ {α : Type u} (x : α),
    @has_pure.pure _ A1.to_has_pure _ x = @has_pure.pure _ A2.to_has_pure _ x)
  (H2 : ∀ {α β : Type u} (f : F (α → β)) (x : F α),
    @has_seq.seq _ A1.to_has_seq _ _ f x = @has_seq.seq _ A2.to_has_seq _ _ f x),
  A1 = A2
| {to_functor := F1, seq := s1, pure := p1, seq_left := sl1, seq_right := sr1}
  {to_functor := F2, seq := s2, pure := p2, seq_left := sl2, seq_right := sr2} L1 L2 H1 H2 :=
begin
  have : @p1 = @p2, {funext α x, apply H1}, subst this,
  have : @s1 = @s2, {funext α β f x, apply H2}, subst this,
  cases L1, cases L2,
  have : F1 = F2,
  { resetI, apply functor.ext, intros,
    exact (L1_pure_seq_eq_map _ _).symm.trans (L2_pure_seq_eq_map _ _) },
  subst this,
  congr; funext α β x y,
  { exact (L1_seq_left_eq _ _).trans (L2_seq_left_eq _ _).symm },
  { exact (L1_seq_right_eq _ _).trans (L2_seq_right_eq _ _).symm }
end

end lemmas

instance : is_comm_applicative id :=
by refine { .. }; intros; refl

namespace functor
namespace comp

open function (hiding comp)
open functor

variables {F : Type u → Type w} {G : Type v → Type u}

variables [applicative F] [applicative G]

variables [is_lawful_applicative F] [is_lawful_applicative G]
variables {α β γ : Type v}

lemma map_pure (f : α → β) (x : α) : (f <$> pure x : comp F G β) = pure (f x) :=
comp.ext $ by simp

lemma seq_pure (f : comp F G (α → β)) (x : α) :
  f <*> pure x = (λ g : α → β, g x) <$> f :=
comp.ext $ by simp [(∘)] with functor_norm

lemma seq_assoc (x : comp F G α) (f : comp F G (α → β)) (g : comp F G (β → γ)) :
   g <*> (f <*> x) = (@function.comp α β γ <$> g) <*> f <*> x :=
comp.ext $ by simp [(∘)] with functor_norm

lemma pure_seq_eq_map (f : α → β) (x : comp F G α) :
  pure f <*> x = f <$> x :=
comp.ext $ by simp [applicative.pure_seq_eq_map'] with functor_norm

instance : is_lawful_applicative (comp F G) :=
{ pure_seq_eq_map := @comp.pure_seq_eq_map F G _ _ _ _,
  map_pure := @comp.map_pure F G _ _ _ _,
  seq_pure := @comp.seq_pure F G _ _ _ _,
  seq_assoc := @comp.seq_assoc F G _ _ _ _ }

theorem applicative_id_comp {F} [AF : applicative F] [LF : is_lawful_applicative F] :
  @comp.applicative id F _ _ = AF :=
@applicative.ext F _ _ (@comp.is_lawful_applicative id F _ _ _ _) _
  (λ α x, rfl) (λ α β f x, rfl)

theorem applicative_comp_id {F} [AF : applicative F] [LF : is_lawful_applicative F] :
  @comp.applicative F id _ _ = AF :=
@applicative.ext F _ _ (@comp.is_lawful_applicative F id _ _ _ _) _
  (λ α x, rfl) (λ α β f x, show id <$> f <*> x = f <*> x, by rw id_map)

open is_comm_applicative

instance {f : Type u → Type w} {g : Type v → Type u}
  [applicative f] [applicative g]
  [is_comm_applicative f] [is_comm_applicative g] :
  is_comm_applicative (comp f g) :=
by { refine { .. @comp.is_lawful_applicative f g _ _ _ _, .. },
     intros, casesm* comp _ _ _, simp! [map,has_seq.seq] with functor_norm,
     rw [commutative_map],
     simp [comp.mk,flip,(∘)] with functor_norm,
     congr, funext, rw [commutative_map], congr }

end comp
end functor

open functor

@[functor_norm]
lemma comp.seq_mk {α β : Type w}
  {f : Type u → Type v} {g : Type w → Type u}
  [applicative f] [applicative g]
  (h : f (g (α → β))) (x : f (g α)) :
  comp.mk h <*> comp.mk x = comp.mk (has_seq.seq <$> h <*> x) := rfl

instance {α} [has_one α] [has_mul α] : applicative (const α) :=
{ pure := λ β x, (1 : α),
  seq := λ β γ f x, (f * x : α) }

instance {α} [monoid α] : is_lawful_applicative (const α) :=
by refine { .. }; intros; simp [mul_assoc, (<$>), (<*>), pure]

instance {α} [has_zero α] [has_add α] : applicative (add_const α) :=
{ pure := λ β x, (0 : α),
  seq := λ β γ f x, (f + x : α) }

instance {α} [add_monoid α] : is_lawful_applicative (add_const α) :=
by refine { .. }; intros; simp [add_assoc, (<$>), (<*>), pure]
