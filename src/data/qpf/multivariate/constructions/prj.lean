/-
Copyright (c) 2020 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/

import data.qpf.multivariate.basic

/-!
Projection functors are QPFs. The `n`-ary projection functors on `i` is an `n`-ary
functor `F` such that `F (α₀..αᵢ₋₁, αᵢ, αᵢ₊₁..αₙ₋₁) = αᵢ`
-/

universes u v
namespace mvqpf
open_locale mvfunctor

variables {n : ℕ} (i : fin2 n)

/-- The projection `i` functor -/
def prj (v : typevec.{u} n) : Type u := v i

instance prj.inhabited {v : typevec.{u} n} [inhabited (v i)] : inhabited (prj i v) :=
⟨ (default _ : v i) ⟩

/-- `map` on functor `prj i` -/
def prj.map ⦃α β : typevec n⦄ (f : α ⟹ β) : prj i α → prj i β :=
f _

instance prj.mvfunctor : mvfunctor (prj i) :=
{ map := prj.map i }

/-- Polynomial representation of the projection functor -/
def prj.P : mvpfunctor.{u} n :=
{ A := punit, B := λ _ j, ulift $ plift $ i = j }

/-- Abstraction function of the `qpf` instance -/
def prj.abs ⦃α : typevec n⦄ : (prj.P i).obj α → prj i α
| ⟨x, f⟩ := f _ ⟨⟨rfl⟩⟩

/-- Representation function of the `qpf` instance -/
def prj.repr ⦃α : typevec n⦄ : prj i α → (prj.P i).obj α :=
λ x : α i, ⟨ ⟨ ⟩, λ j ⟨⟨h⟩⟩, (h.rec x : α j) ⟩

instance prj.mvqpf : mvqpf (prj i) :=
{ P := prj.P i,
  abs := prj.abs i,
  repr := prj.repr i,
  abs_repr := by intros; refl,
  abs_map := by intros; cases p; refl }

end mvqpf
