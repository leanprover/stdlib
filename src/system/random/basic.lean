/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/

import algebra.group_power
import control.uliftable

import data.bitvec.basic
import data.stream.basic


import system.io
import system.random

/-!
# Rand Monad and Random Class

This module provides tools for formulating computations guided by randomness and for
defining objects that can be created randomly.

## Main definitions
  * `rand` monad for computations guided by randomness;
  * `random` class for objects that can be generated randomly;
    * `random` to generate one object;
    * `random_r` to generate one object inside a range;
    * `random_series` to generate an infinite series of objects;
    * `random_series_r` to generate an infinite series of objects inside a range;
  * `io.mk_generator` to create a new random number generator;
  * `io.run_rand` to run a randomized computation inside the `io` monad;
  * `tactic.run_rand` to run a randomized computation inside the `tactic` monad

## Local notation

 * `i .. j` : `Icc i j`, the set of values between `i` and `j` inclusively;

## Tags

random monad io

## References

  * Similar library in Haskell: https://hackage.haskell.org/package/MonadRandom

-/

open list io applicative

universes u v w

/-- A monad to generate random objects using the generator type `g` -/
@[reducible]
def rand_g (g : Type) (α : Type u) : Type u := state (ulift.{u} g) α

/-- A monad to generate random objects using the generator type `std_gen` -/
@[reducible]
def rand := rand_g std_gen

instance (g : Type) : uliftable (rand_g.{u} g) (rand_g.{v} g) :=
@state_t.uliftable' _ _ _ _ _ (equiv.ulift.trans.{u u u u u} equiv.ulift.symm)

open ulift (hiding inhabited)

/-- Generate one more `ℕ` -/
def rand_g.next {g : Type} [random_gen g] : rand_g g ℕ :=
⟨ prod.map id up ∘ random_gen.next ∘ down ⟩

local infix ` .. `:41 := set.Icc

open stream

/-- `bounded_random α` gives us machinery to generate values of type `α` between certain bounds -/
class bounded_random (α : Type u) [preorder α] :=
(random_r : Π g [random_gen g] (x y : α),
              (x ≤ y) → rand_g g (x .. y))

/-- `random α` gives us machinery to generate values of type `α` -/
class random (α : Type u) :=
(random [] : Π (g : Type) [random_gen g], rand_g g α)

/-- shift_31_left = 2^31; multiplying by it shifts the binary
representation of a number left by 31 bits, dividing by it shifts it
right by 31 bits -/
def shift_31_left : ℕ :=
by apply_normed 2^31

namespace rand

open stream

variables (α : Type u)
variables (g : Type) [random_gen g]

/-- create a new random number generator distinct from the one stored in the state -/
def split : rand_g g g := ⟨ prod.map id up ∘ random_gen.split ∘ down ⟩

variables {g}

section random
variables [random α]

export random (random)

/-- Generate a random value of type `α`. -/
def random : rand_g g α :=
random.random α g

/-- generate an infinite series of random values of type `α` -/
def random_series : rand_g g (stream α) :=
do gen ← uliftable.up (split g),
   pure $ stream.corec_state (random.random α g) gen

end random

variables {α}

/-- Generate a random value between `x` and `y` inclusive. -/
def random_r [preorder α] [bounded_random α] (x y : α) (h : x ≤ y) : rand_g g (x .. y) :=
bounded_random.random_r g x y h

/-- generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/
def random_series_r [preorder α] [bounded_random α] (x y : α) (h : x ≤ y) : rand_g g (stream (x .. y)) :=
do gen ← uliftable.up (split g),
   pure $ corec_state (bounded_random.random_r g x y h) gen

end rand

namespace io

private def accum_char (w : ℕ) (c : char) : ℕ :=
c.to_nat + 256 * w

/-- create and a seed a random number generator -/
def mk_generator : io std_gen := do
seed ← io.rand 0 shift_31_left,
return $ mk_std_gen seed

variables {α : Type}

/-- Run `cmd` using a randomly seeded random number generator -/
def run_rand (cmd : _root_.rand α) : io α :=
do g ← io.mk_generator,
   return $ (cmd.run ⟨g⟩).1

/-- Run `cmd` using the provided seed. -/
def run_rand_with (seed : ℕ) (cmd : _root_.rand α) : io α :=
return $ (cmd.run ⟨mk_std_gen seed⟩).1

section random
variables [random α]

/-- randomly generate a value of type α -/
def random : io α :=
io.run_rand (rand.random α)

/-- randomly generate an infinite series of value of type α -/
def random_series : io (stream α) :=
io.run_rand (rand.random_series α)

end random

section bounded_random
variables [preorder α] [bounded_random α]

/-- randomly generate a value of type α between `x` and `y` -/
def random_r (x y : α) (p : x ≤ y) : io (x .. y) :=
io.run_rand (bounded_random.random_r _ x y p)

/-- randomly generate an infinite series of value of type α between `x` and `y` -/
def random_series_r (x y : α) (h : x ≤ y) : io (stream $ x .. y) :=
io.run_rand (rand.random_series_r x y h)

end bounded_random

end io

namespace tactic

/-- create a seeded random number generator in the `tactic` monad -/
meta def mk_generator : tactic std_gen := do
tactic.unsafe_run_io @io.mk_generator

/-- run `cmd` using the a randomly seeded random number generator
in the tactic monad -/
meta def run_rand {α : Type u} (cmd : rand α) : tactic α := do
⟨g⟩ ← tactic.up mk_generator,
return (cmd.run ⟨g⟩).1

variables {α : Type u}

section bounded_random
variables [preorder α] [bounded_random α]

/-- Generate a random value between `x` and `y` inclusive. -/
meta def random_r (x y : α) (h : x ≤ y) : tactic (x .. y) :=
run_rand (rand.random_r x y h)

/-- Generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/
meta def random_series_r (x y : α) (h : x ≤ y) : tactic (stream $ x .. y) :=
run_rand (rand.random_series_r x y h)

end bounded_random

section random

variables [random α]

/-- randomly generate a value of type α -/
meta def random : tactic α :=
run_rand (rand.random α)

 /-- randomly generate an infinite series of value of type α -/
meta def random_series : tactic (stream α) :=
run_rand (rand.random_series α)

end random

end tactic

open nat (succ one_add mod_eq_of_lt zero_lt_succ add_one succ_le_succ)

variables {g : Type} [random_gen g]

open nat

namespace fin
variables {n : ℕ} [fact (0 < n)]

/-- generate a `fin` randomly -/
protected def random : rand_g g (fin n) :=
⟨ λ ⟨g⟩, prod.map of_nat' up $ rand_nat g 0 n ⟩

end fin

open nat

instance nat_bounded_random : bounded_random ℕ :=
{ random_r := λ g inst x y hxy,
  do z ← @fin.random g inst (succ $ y - x) _,
     pure ⟨z.val + x, nat.le_add_left _ _,
       by rw ← nat.le_sub_right_iff_add_le hxy; apply le_of_succ_le_succ z.is_lt⟩ }

/-- This `bounded_random` interval generates integers between `x` and
`y` by first generating a natural number between `0` and `y - x` and
shifting the result appropriately. -/
instance int_bounded_random : bounded_random ℤ :=
{ random_r := λ g inst x y hxy,
  do ⟨z,h₀,h₁⟩ ← @bounded_random.random_r ℕ _ _ g inst 0 (int.nat_abs $ y - x) dec_trivial,
     pure ⟨z + x,
       int.le_add_of_nonneg_left (int.coe_nat_nonneg _),
       int.add_le_of_le_sub_right $ le_trans
         (int.coe_nat_le_coe_nat_of_le h₁)
         (le_of_eq $ int.of_nat_nat_abs_eq_of_nonneg (int.sub_nonneg_of_le hxy)) ⟩ }

instance fin_random (n : ℕ) [fact (0 < n)] : random (fin n) :=
{ random := λ g inst, @fin.random g inst _ _ }

instance fin_bounded_random (n : ℕ) : bounded_random (fin n) :=
{ random_r := λ g inst (x y : fin n) p,
    do ⟨r, h, h'⟩ ← @rand.random_r ℕ g inst _ _ x.val y.val p,
       pure ⟨⟨r,lt_of_le_of_lt h' y.is_lt⟩, h, h'⟩ }

/-- A shortcut for creating a `random (fin n)` instance from
a proof that `0 < n` rather than on matching on `fin (succ n)`  -/
def random_fin_of_pos : ∀ {n : ℕ} (h : 0 < n), random (fin n)
| (succ n) _ := fin_random _
| 0 h := false.elim (not_lt_zero _ h)

lemma bool_of_nat_mem_Icc_of_mem_Icc_to_nat (x y : bool) (n : ℕ) :
  n ∈ (x.to_nat .. y.to_nat) → bool.of_nat n ∈ (x .. y) :=
begin
  simp only [and_imp, set.mem_Icc], intros h₀ h₁,
  split;
    [ have h₂ := bool.of_nat_le_of_nat h₀, have h₂ := bool.of_nat_le_of_nat h₁ ];
    rw bool.of_nat_to_nat at h₂; exact h₂,
end

instance : random bool :=
{ random   := λ g inst, (bool.of_nat ∘ subtype.val) <$> @bounded_random.random_r ℕ _ _ g inst 0 1 (nat.zero_le _) }

instance : bounded_random bool :=
{ random_r := λ g _inst x y p, subtype.map bool.of_nat (bool_of_nat_mem_Icc_of_mem_Icc_to_nat x y) <$> @bounded_random.random_r ℕ _ _ g _inst x.to_nat y.to_nat (bool.to_nat_le_to_nat p) }

open_locale fin_fact

/-- generate a random bit vector of length `n` -/
def bitvec.random (n : ℕ) : rand_g g (bitvec n) :=
bitvec.of_fin <$> rand.random (fin $ 2^n)

/-- generate a random bit vector of length `n` -/
def bitvec.random_r {n : ℕ} (x y : bitvec n) (h : x ≤ y) : rand_g g (x .. y) :=
have h' : ∀ (a : fin (2 ^ n)), a ∈ (x.to_fin .. y.to_fin) → bitvec.of_fin a ∈ (x .. y),
begin
  simp only [and_imp, set.mem_Icc], intros z h₀ h₁,
  replace h₀ := bitvec.of_fin_le_of_fin_of_le h₀,
  replace h₁ := bitvec.of_fin_le_of_fin_of_le h₁,
  rw bitvec.of_fin_to_fin at h₀ h₁, split; assumption,
end,
subtype.map bitvec.of_fin h' <$> rand.random_r x.to_fin y.to_fin (bitvec.to_fin_le_to_fin_of_le h)

open nat

instance random_bitvec (n : ℕ) : random (bitvec n) :=
{ random := λ _ inst, @bitvec.random _ inst n }

instance bounded_random_bitvec (n : ℕ) : bounded_random (bitvec n) :=
{ random_r := λ _ inst x y p, @bitvec.random_r _ inst _ _ _ p }
