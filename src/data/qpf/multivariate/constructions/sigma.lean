/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/

import data.qpf.multivariate.basic

/-!
# Dependent product and sum of QPFs are QPFs
-/

universes u

namespace mvqpf
open_locale mvfunctor

variables {n : ℕ} {A : Type u}
variables (F : A → typevec.{u} n → Type u)

/-- Dependent sum of of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
def sigma (v : typevec.{u} n) : Type.{u} :=
Σ α : A, F α v

/-- Dependent product of of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
def pi (v : typevec.{u} n) : Type.{u} :=
Π α : A, F α v

instance sigma.inhabited {α} [inhabited A] [inhabited (F (default A) α)] : inhabited (sigma F α) :=
⟨ ⟨default A, default _⟩ ⟩

instance pi.inhabited {α} [Π a, inhabited (F a α)] : inhabited (pi F α) :=
⟨ λ a, default _ ⟩

variables [Π α, mvfunctor $ F α]

namespace sigma

instance : mvfunctor (sigma F) :=
{ map := λ α β f ⟨a,x⟩, ⟨a,f <$$> x⟩ }

variables [Π α, mvqpf $ F α]

/-- polynomial functor representation of a dependent sum -/
protected def P : mvpfunctor n :=
⟨ Σ a, (P (F a)).A, λ x, (P (F x.1)).B x.2 ⟩

/-- abstraction function for dependent sums -/
protected def abs ⦃α⦄ : (sigma.P F).obj α → sigma F α
| ⟨a,f⟩ := ⟨ a.1, mvqpf.abs ⟨a.2, f⟩ ⟩

/-- representation function for dependent sums -/
protected def repr ⦃α⦄ : sigma F α → (sigma.P F).obj α
| ⟨a,f⟩ :=
  let x := mvqpf.repr f in
  ⟨ ⟨a,x.1⟩, x.2 ⟩

instance : mvqpf (sigma F) :=
{ P := sigma.P F,
  abs := sigma.abs F,
  repr := sigma.repr F,
  abs_repr := by rintros α ⟨x,f⟩; simp [sigma.repr,sigma.abs,abs_repr],
  abs_map := by rintros α β f ⟨x,g⟩; simp [sigma.abs,mvpfunctor.map_eq];
                simp [(<$$>),mvfunctor._match_1,← abs_map,← mvpfunctor.map_eq]
 }

end sigma

namespace pi

instance : mvfunctor (pi F) :=
{ map := λ α β f x a, f <$$> x a }

variables [Π α, mvqpf $ F α]

/-- polynomial functor representation of a dependent product -/
protected def P : mvpfunctor n :=
⟨ Π a, (P (F a)).A, λ x i, Σ a : A, (P (F a)).B (x a) i ⟩

/-- abstraction function for dependent products -/
protected def abs ⦃α⦄ : (pi.P F).obj α → pi F α
| ⟨a,f⟩ := λ x, mvqpf.abs ⟨a x, λ i y, f i ⟨_,y⟩⟩

/-- representation function for dependent products -/
protected def repr ⦃α⦄ : pi F α → (pi.P F).obj α
| f :=
  ⟨ λ a, (mvqpf.repr (f a)).1, λ i a, (@mvqpf.repr _ _ _ (_inst_2 _) _ (f _)).2 _ a.2 ⟩

instance : mvqpf (pi F) :=
{ P := pi.P F,
  abs := pi.abs F,
  repr := pi.repr F,
  abs_repr := by rintros α f; ext; simp [pi.repr,pi.abs,abs_repr],
  abs_map := by rintros α β f ⟨x,g⟩; simp only [pi.abs, mvpfunctor.map_eq]; ext;
                simp only [(<$$>)];
                simp only [←abs_map, mvpfunctor.map_eq]; refl
 }

end pi

end mvqpf
