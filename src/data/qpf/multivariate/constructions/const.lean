/-
Copyright (c) 2020 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/

import data.qpf.multivariate.basic

/-!
# Constant functors are QPFs

Constant functors map every type vectors to the same target type. This
is a useful device for constructing data types from more basic types
that are not actually functorial. For instance `const n nat` makes
`nat` into a functor that can be used in a functor-based data type
specification.
-/

universes u

namespace mvqpf
open_locale mvfunctor

variables (n : ℕ)

/-- Constant multivariate functor -/
@[nolint unused_arguments]
def const (A : Type*) (v : typevec.{u} n) : Type* :=
A

instance const.inhabited {A α} [inhabited A] : inhabited (const n A α) :=
⟨ (default A : A) ⟩

namespace const
open mvfunctor mvpfunctor
variables {n} {A : Type u} {α β : typevec.{u} n} (f : α ⟹ β)

/-- Constructor for constant functor -/
protected def mk (x : A) : (const n A) α := x

/-- Destructor for constant functor -/
protected def get (x : (const n A) α) : A := x

@[simp] protected lemma mk_get (x : (const n A) α) : const.mk (const.get x) = x := rfl

@[simp] protected lemma get_mk (x : A) : const.get (const.mk x : const n A α) = x := rfl

/-- `map` for constant functor -/
protected def map : (const n A) α → (const n A) β :=
λ x, x

instance : mvfunctor (const n A) :=
{ map := λ α β f, const.map }

lemma map_mk (x : A) :
  f <$$> const.mk x = const.mk x := rfl

lemma get_map (x : (const n A) α) :
  const.get (f <$$> x) = const.get x := rfl

instance mvqpf : @mvqpf _ (const n A) (mvqpf.const.mvfunctor) :=
{ P         := mvpfunctor.const n A,
  abs       := λ α x, mvpfunctor.const.get x,
  repr      := λ α x, mvpfunctor.const.mk n x,
  abs_repr  := by intros; simp,
  abs_map   := by intros; simp; refl,
}

end const

end mvqpf
