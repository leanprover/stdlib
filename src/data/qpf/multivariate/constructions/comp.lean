/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Simon Hudon
-/

import data.qpf.multivariate.basic

/-!
# The composition of QPFs is itself a QPF

We define composition between one `n`-ary functor and `n` `m`-ary functors
and show that it preserves the QPF structure
-/

universes u

namespace mvqpf
open_locale mvfunctor

variables {n m : ℕ}
  (F : typevec.{u} n → Type*) [fF : mvfunctor F] [q : mvqpf F]
  (G : fin2 n → typevec.{u} m → Type u) [fG : ∀ i, mvfunctor $ G i] [q' : ∀ i, mvqpf $ G i]

/-- Composition of an `n`-ary functor with `n` `m`-ary
functors gives us one `m`-ary functor -/
def comp (v : typevec.{u} m) : Type* :=
F $ λ i : fin2 n, G i v

namespace comp
open mvfunctor mvpfunctor
variables {F G} {α β : typevec.{u} m} (f : α ⟹ β)

instance [I : inhabited (F $ λ i : fin2 n, G i α)] : inhabited (comp F G α) := I

/-- Constructor for functor composition -/
protected def mk (x : F $ λ i, G i α) : (comp F G) α := x

/-- Destructor for functor composition -/
protected def get (x : (comp F G) α) : F $ λ i, G i α := x

@[simp] protected lemma mk_get (x : (comp F G) α) : comp.mk (comp.get x) = x := rfl

@[simp] protected lemma get_mk (x : F $ λ i, G i α) : comp.get (comp.mk x) = x := rfl

include fG

/-- map operation defined on a vector of functors -/
protected def map' : (λ (i : fin2 n), G i α) ⟹ λ (i : fin2 n), G i β :=
λ i, map f

include fF

/-- The composition of functors is itself functorial -/
protected def map : (comp F G) α → (comp F G) β :=
(map (λ i, map f) : F (λ i, G i α) → F (λ i, G i β))

instance : mvfunctor (comp F G) :=
{ map := λ α β, comp.map }

lemma map_mk (x : F $ λ i, G i α) :
  f <$$> comp.mk x = comp.mk ((λ i (x : G i α), f <$$> x) <$$> x) := rfl

lemma get_map (x : comp F G α) :
  comp.get (f <$$> x) = (λ i (x : G i α), f <$$> x) <$$> comp.get x := rfl

include q q'

instance : mvqpf (comp F G) :=
{ P         := mvpfunctor.comp (P F) (λ i, P $ G i),
  abs       := λ α, comp.mk ∘ map (λ i, abs) ∘ abs ∘ mvpfunctor.comp.get,
  repr      := λ α,  mvpfunctor.comp.mk ∘ repr ∘
                 map (λ i, (repr : G i α → (λ (i : fin2 n), obj (P (G i)) α) i)) ∘ comp.get,
  abs_repr  := by { intros, simp [(∘), mvfunctor.map_map, (⊚), abs_repr] },
  abs_map   := by { intros, simp [(∘)], rw [← abs_map],
                    simp [mvfunctor.id_map, (⊚), map_mk, mvpfunctor.comp.get_map, abs_map,
                      mvfunctor.map_map, abs_repr] } }

end comp

end mvqpf
