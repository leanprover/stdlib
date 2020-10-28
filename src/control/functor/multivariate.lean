/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
import data.fin2
import data.typevec
import logic.function.basic
import tactic.basic

/-!

Functors between the category of tuples of types, and the category Type

Features:

`mvfunctor n` : the type class of multivariate functors
`f <$$> x`    : notation for map

-/

universes u v w

open_locale mvfunctor

/-- multivariate functors, i.e. functor between the category of type vectors
and the category of Type -/
class mvfunctor {n : ℕ} (F : typevec n → Type*) :=
(map : Π {α β : typevec n}, (α ⟹ β) → (F α → F β))

localized "infixr ` <$$> `:100 := mvfunctor.map" in mvfunctor

variables {n : ℕ}

namespace mvfunctor

variables {α β γ : typevec.{u} n} {F : typevec.{u} n → Type v} [mvfunctor F]

/-- predicate lifting over multivariate functors -/
def liftp {α : typevec n} (p : Π i, α i → Prop) (x : F α) : Prop :=
∃ u : F (λ i, subtype (p i)), (λ i, @subtype.val _ (p i)) <$$> u = x

/-- relational lifting over multivariate functors -/
def liftr {α : typevec n} (r : Π {i}, α i → α i → Prop) (x y : F α) : Prop :=
∃ u : F (λ i, {p : α i × α i // r p.fst p.snd}),
  (λ i (t : {p : α i × α i // r p.fst p.snd}), t.val.fst) <$$> u = x ∧
  (λ i (t : {p : α i × α i // r p.fst p.snd}), t.val.snd) <$$> u = y

/-- given `x : F α` and a projection `i` of type vector `α`, `supp x i` is the set
of `α.i` contained in `x` -/
def supp {α : typevec n} (x : F α) (i : fin2 n) : set (α i) :=
{ y : α i | ∀ ⦃p⦄, liftp p x → p i y }

theorem of_mem_supp {α : typevec n} {x : F α} {p : Π ⦃i⦄, α i → Prop} (h : liftp p x) (i : fin2 n):
  ∀ y ∈ supp x i, p y :=
λ y hy, hy h

end mvfunctor

/-- laws for `mvfunctor` -/
class is_lawful_mvfunctor {n : ℕ} (F : typevec n → Type*) [mvfunctor F] : Prop :=
(id_map       : ∀ {α : typevec n} (x : F α), typevec.id <$$> x = x)
(comp_map     : ∀ {α β γ : typevec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α),
                    (h ⊚ g) <$$> x = h <$$> g <$$> x)

open nat typevec

namespace mvfunctor

export is_lawful_mvfunctor (comp_map)
open is_lawful_mvfunctor

variables {F : typevec.{u} n → Type v} [mvfunctor F]
variables {α β γ : typevec.{u} n}

variables (p : α ⟹ repeat n Prop) (r : α ⊗ α ⟹ repeat n Prop)

/-- adapt `mvfunctor.liftp` to accept predicates as arrows -/
def liftp' : F α → Prop :=
mvfunctor.liftp $ λ i x, of_repeat $ p i x

/-- adapt `mvfunctor.liftp` to accept relations as arrows -/
def liftr' : F α → F α → Prop :=
mvfunctor.liftr $ λ i x y, of_repeat $ r i $ typevec.prod.mk _ x y

variables [is_lawful_mvfunctor F]

@[simp]
lemma id_map (x : F α) :
  typevec.id <$$> x = x :=
id_map x

@[simp]
lemma id_map' (x : F α) :
  (λ i a, a) <$$> x = x :=
id_map x

lemma map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) :
  h <$$> g <$$> x = (h ⊚ g) <$$> x :=
eq.symm $ comp_map _ _ _

section liftp'

variables (F)

lemma exists_iff_exists_of_mono {p : F α → Prop} {q : F β → Prop} (f : α ⟹ β) (g : β ⟹ α)
  (h₀ : f ⊚ g = id)
  (h₁ : ∀ u : F α, p u ↔ q (f <$$> u)) :
  (∃ u : F α, p u) ↔ (∃ u : F β, q u) :=
begin
  split; rintro ⟨u,h₂⟩; [ use f <$$> u, use g <$$> u ],
  { apply (h₁ u).mp h₂ },
  { apply (h₁ _).mpr _,
    simp only [mvfunctor.map_map,h₀,is_lawful_mvfunctor.id_map,h₂] },
end
variables {F}

#check @liftp
#check @liftp'

#print of_subtype

lemma liftp_def (x : F α) : liftp' p x ↔ ∃ u : F (subtype_ p), subtype_val p <$$> u = x :=
begin
  dsimp only [liftp', mvfunctor.liftp],
  apply exists_iff_exists_of_mono F (to_subtype p) (of_subtype p),
  { clear x _inst_2 _inst_1 F, dsimp only [comp],
    ext i x; induction i, { refl },
    -- Lean 3.11.0 problem
    rw [of_subtype,@to_subtype.equations._eqn_2 i_n _ p i_a,i_ih],
    refl, },
  { intro, rw [mvfunctor.map_map,(⊚)], congr',
    clear x u _inst_2 _inst_1 F, ext i ⟨ x,_ ⟩,
    induction i; dsimp only [to_subtype, subtype_val],
    { refl }, { apply i_ih }, }
end

lemma liftr_def (x y : F α) :
  liftr' r x y ↔
  ∃ u : F (subtype_ r), (typevec.prod.fst ⊚ subtype_val r) <$$> u = x ∧
                        (typevec.prod.snd ⊚ subtype_val r) <$$> u = y :=
begin
  dsimp only [liftr', mvfunctor.liftr],
  apply exists_iff_exists_of_mono F (to_subtype' r) (of_subtype' r),
  { clear x y _inst_2 _inst_1 F, dsimp only [comp],
    ext i x; induction i,
    { dsimp only [typevec.id], cases x, refl },
    -- Lean 3.11.0 problem
    { rw [of_subtype',@to_subtype'.equations._eqn_2 i_n _ r i_a, i_ih], refl } },
  { intro, rw [mvfunctor.map_map,(⊚),mvfunctor.map_map,(⊚)], congr';
    clear x y u _inst_2 _inst_1 F,
    { ext i ⟨ x,_ ⟩, induction i; dsimp only [subtype_val],
      { refl },
      apply i_ih, },
    { ext i ⟨x,_⟩,
      { induction i, { refl },
        { rw i_ih (drop_fun r), refl }, } } }
end

end liftp'

end mvfunctor

open nat

namespace mvfunctor

open typevec

section liftp_last_pred_iff
variables  {F : typevec.{u} (n+1) → Type*} [mvfunctor F] [is_lawful_mvfunctor F]
           {α : typevec.{u} n}
variables (p : α ⟹ repeat n Prop)
          (r : α ⊗ α ⟹ repeat n Prop)

open mvfunctor

variables {β : Type u}
variables (pp : β → Prop)

private def f : Π (n α), (λ (i : fin2 (n + 1)), {p_1 // of_repeat (pred_last' α pp i p_1)}) ⟹
    λ (i : fin2 (n + 1)), {p_1 : (α ::: β) i // pred_last α pp p_1}
| _ α (fin2.fs i) x := ⟨ x.val, cast (by simp only [pred_last]; erw const_iff_true) x.property ⟩
| _ α fin2.fz x := ⟨ x.val, x.property ⟩

private def g : Π (n α), (λ (i : fin2 (n + 1)), {p_1 : (α ::: β) i // pred_last α pp p_1}) ⟹
    (λ (i : fin2 (n + 1)), {p_1 // of_repeat (pred_last' α pp i p_1)})
| _ α (fin2.fs i) x := ⟨ x.val, cast (by simp only [pred_last]; erw const_iff_true) x.property ⟩
| _ α fin2.fz x := ⟨ x.val, x.property ⟩

lemma liftp_last_pred_iff {β} (p : β → Prop) (x : F (α ::: β)) :
  liftp' (pred_last' _ p) x ↔ liftp (pred_last _ p) x :=
begin
  dsimp only [liftp,liftp'],
  apply exists_iff_exists_of_mono F (f _ n α) (g _ n α),
  { clear x _inst_2 _inst_1 F, ext i ⟨x,_⟩, cases i; refl },
  { intros, rw [mvfunctor.map_map,(⊚)],
    congr'; ext i ⟨x,_⟩; cases i; refl }
end

open function
variables (rr : β → β → Prop)

private def f : Π (n α), (λ (i : fin2 (n + 1)), {p_1 : _ × _ // of_repeat (rel_last' α rr i (typevec.prod.mk _ p_1.fst p_1.snd))}) ⟹
    λ (i : fin2 (n + 1)), {p_1 : (α ::: β) i × _ // rel_last α rr (p_1.fst) (p_1.snd)}
| _ α (fin2.fs i) x := ⟨ x.val, cast (by simp only [rel_last]; erw repeat_eq_iff_eq) x.property ⟩
| _ α fin2.fz x := ⟨ x.val, x.property ⟩

private def g : Π (n α), (λ (i : fin2 (n + 1)), {p_1 : (α ::: β) i × _ // rel_last α rr (p_1.fst) (p_1.snd)}) ⟹
    (λ (i : fin2 (n + 1)), {p_1 : _ × _ // of_repeat (rel_last' α rr i (typevec.prod.mk _ p_1.fst p_1.snd))})
| _ α (fin2.fs i) x := ⟨ x.val, cast (by simp only [rel_last]; erw repeat_eq_iff_eq) x.property ⟩
| _ α fin2.fz x := ⟨ x.val, x.property ⟩

lemma liftr_last_rel_iff  (x y : F (α ::: β)) :
  liftr' (rel_last' _ rr) x y ↔ liftr (rel_last _ rr) x y :=
begin
  dsimp only [liftr,liftr'],
  apply exists_iff_exists_of_mono F (f rr _ _) (g rr _ _),
  { clear x y _inst_2 _inst_1 F, ext i ⟨x,_⟩ : 2, cases i; refl, },
  { intros, rw [mvfunctor.map_map,mvfunctor.map_map,(⊚),(⊚)],
    congr'; ext i ⟨x,_⟩; cases i; refl }
end

end liftp_last_pred_iff

end mvfunctor
