/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/

import data.pfunctor.indexed.basic
import data.qpf.indexed.basic

/-!
# Dependent product and sum of QPFs are QPFs
-/

universes u

namespace iqpf

variables {I J A : Type u}
  (F : A → fam I ⥤ fam J)

/-- Dependent sum of of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
def sigma_obj (v : fam I) : fam J :=
λ j, Σ α : A, (F α).obj v j

/-- Dependent product of of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
def pi_obj (v : fam I) : fam J :=
λ j, Π α : A, (F α).obj v j

/-- Dependent sum as a functor -/
@[simps]
def sigma : fam I ⥤ fam J :=
{ obj := sigma_obj F,
  map := λ α β f i ⟨a,x⟩, ⟨a,(F a).map f x⟩ }

namespace sigma

variables [Π α, iqpf $ F α]

/-- polynomial functor representation of a dependent sum -/
protected def P : ipfunctor I J :=
⟨ λ j, Σ a, (P (F a)).A j, λ j, λ x, (P (F x.1)).B j x.2 ⟩

/-- abstraction function for dependent sums -/
protected def abs ⦃α⦄ : (sigma.P F).obj α ⟶ (sigma F).obj α :=
λ (j : J) (x : (sigma.P F).obj α j),
show (sigma F).obj α j, from
match x with
| sigma.mk ⟨a,a'⟩ f :=
  ⟨ a, iqpf.abs (F _) α ⟨a', f⟩ ⟩
end

/-- representation function for dependent sums -/
protected def repr ⦃α⦄ : (sigma F).obj α ⟶ (sigma.P F).obj α :=
λ (j : J) (x : (sigma F).obj α j),
show (sigma.P F).obj α j, from
match x with
| ⟨a, y⟩ :=
  let x := iqpf.repr (F a) α y in
  ⟨ ⟨a, x.1⟩, x.2 ⟩
end

instance : iqpf (sigma F) :=
{ P := sigma.P F,
  abs := sigma.abs F,
  repr := sigma.repr F,
  abs_repr := by rintros α; ext i ⟨x,f⟩ : 2; simp [sigma.repr,sigma.abs,abs_repr']; refl,
  abs_map := by rintros α β f; ext i ⟨⟨x,y⟩,g⟩ : 2;
                simp [sigma.abs,ipfunctor.map_eq];
                simp [ipfunctor.map_eq',abs._match_1,sigma._match_1];
                simp [← ipfunctor.map_eq',abs_map']
 }

end sigma

/-- Dependent product as a functor -/
@[simps]
def pi : fam I ⥤ fam J :=
{ obj := pi_obj F,
  map := λ α β f i x a, (F a).map f (x a) }

namespace pi

variables [Π α, iqpf $ F α]

/-- polynomial functor representation of a dependent products -/
protected def P : ipfunctor I J :=
⟨ λ j, Π a, (P (F a)).A j, λ j x i, Σ a : A, (P (F a)).B j (x a) i ⟩

/-- abstraction function for dependent products -/
protected def abs ⦃α⦄ : (pi.P F).obj α ⟶ (pi F).obj α :=
λ (j : J) (x : (pi.P F).obj α j),
show (pi F).obj α j, from
match x with
| sigma.mk a f :=
  λ y, abs (F y) α ⟨a y, λ i z, f ⟨_,z⟩⟩
end

/-- representation function for dependent products -/
protected def repr ⦃α⦄ : (pi F).obj α ⟶ (pi.P F).obj α :=
λ (j : J) (x : (pi F).obj α j),
show (pi.P F).obj α j, from
let y := λ a, iqpf.repr (F a) α (x a) in
⟨ λ a, (y a).1, λ i a, (y a.1).2 a.2 ⟩

instance : iqpf (pi F) :=
{ P := pi.P F,
  abs := pi.abs F,
  repr := pi.repr F,
  abs_repr := by rintros α; ext; simp [pi.repr,pi.abs,abs_repr']; refl,
  abs_map := by
  { rintros α β f; ext i ⟨x,g⟩ : 3,
    dsimp,
    simp only [ipfunctor.map_eq', pi.abs, ←abs_map'],
    refl,
  }
 }

end pi

end iqpf
