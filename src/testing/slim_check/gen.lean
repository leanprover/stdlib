/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/

import system.random
import system.random.basic

/-!
# `gen` Monad

This monad is used to formulate randomized computations with a parameter
to specify the desired size of the result.

This is a port of the Haskell QuickCheck library.

## Main definitions
  * `gen` monad

## Local notation

 * `i .. j` : `Icc i j`, the set of values between `i` and `j` inclusively;

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/

universes u v

namespace slim_check

/-- Monad to generate random examples to test properties with.
It has a `nat` parameter so that the caller can decide on the
size of the examples. -/
@[reducible, derive [monad, is_lawful_monad]]
def gen (α : Type u) := reader_t (ulift ℕ) rand α

variable (α : Type u)

local infix ` .. `:41 := set.Icc

/-- Execute a `gen` inside the `io` monad using `i` as the example
size and with a fresh random number generator. -/
def io.run_gen {α} (x : gen α) (i : ℕ) : io α :=
io.run_rand (x.run ⟨i⟩)

namespace gen

section rand

/-- Lift `random.random` to the `gen` monad. -/
def choose_any [random α] : gen α :=
⟨ λ _, rand.random α ⟩

variables {α} [preorder α]

/-- Lift `random.random_r` to the `gen` monad. -/
def choose [bounded_random α] (x y : α) (p : x ≤ y) : gen (x .. y) :=
⟨ λ _, rand.random_r x y p ⟩

end rand

open nat (hiding choose)

/-- Generate a `nat` example between `x` and `y`. -/
def choose_nat (x y : ℕ) (p : x ≤ y) : gen (x .. y) :=
choose x y p

/-- Generate a `nat` example between `x` and `y`. -/
def choose_nat' (x y : ℕ) (p : x < y) : gen (set.Ico x y) :=
have ∀ i, x < i → i ≤ y → i.pred < y,
  from λ i h₀ h₁,
     show i.pred.succ ≤ y,
     by rwa succ_pred_eq_of_pos; apply lt_of_le_of_lt (nat.zero_le _) h₀,
subtype.map pred (λ i (h : x+1 ≤ i ∧ i ≤ y), ⟨le_pred_of_lt h.1, this _ h.1 h.2⟩) <$> choose (x+1) y p

open nat

instance : uliftable gen.{u} gen.{v} :=
reader_t.uliftable' (equiv.ulift.trans equiv.ulift.symm)

instance : has_orelse gen.{u} :=
⟨ λ α x y, do
  b ← uliftable.up $ choose_any bool,
  if b.down then x else y ⟩

variable {α}

/-- Get access to the size parameter of the `gen` monad. For
reasons of universe polymorphism, it is specified in
continuation passing style. -/
def sized (cmd : ℕ → gen α) : gen α :=
⟨ λ ⟨sz⟩, reader_t.run (cmd sz) ⟨sz⟩ ⟩

/-- Apply a function to the size parameter. -/
def resize (f : ℕ → ℕ) (cmd : gen α) : gen α :=
⟨ λ ⟨sz⟩, reader_t.run cmd ⟨f sz⟩ ⟩

/-- Create `n` examples using `cmd`. -/
def vector_of : ∀ (n : ℕ) (cmd : gen α), gen (vector α n)
| 0 _ := return vector.nil
| (succ n) cmd := vector.cons <$> cmd <*> vector_of n cmd

/-- Create a list of examples using `cmd`. The size is controlled
by the size parameter of `gen`. -/
def list_of (cmd : gen α) : gen (list α) :=
sized $ λ sz, do
do ⟨ n ⟩ ← uliftable.up $ choose_nat 0 (sz + 1) dec_trivial,
   v ← vector_of n.val cmd,
   return v.to_list

open ulift

/-- Given a list of example generators, choose one to create an example. -/
def one_of (xs : list (gen α)) (pos : 0 < xs.length) : gen α := do
⟨⟨n, h, h'⟩⟩ ← uliftable.up $ choose_nat' 0 xs.length pos,
list.nth_le xs n h'

/-- Given a list of example generators, choose one to create an example. -/
def elements (xs : list α) (pos : 0 < xs.length) : gen α := do
⟨⟨n,h₀,h₁⟩⟩ ← uliftable.up $ choose_nat' 0 xs.length pos,
pure $ list.nth_le xs n h₁

/--
`freq_aux xs i _` takes a weighted list of generator and a number meant to select one of the generators.

If we consider `freq_aux [(1, gena), (3, genb), (5, genc)] 4 _`, we choose a generator by splitting
the interval 1-9 into 1-1, 2-4, 5-9 so that the width of each interval corresponds to one of the
number in the list of generators. Then, we check which interval 4 falls into: it selects `genb`.
-/
def freq_aux : Π (xs : list (ℕ+ × gen α)) i, i < (xs.map (subtype.val ∘ prod.fst)).sum → gen α
| [] i h := false.elim (not_lt_zero _ h)
| ((i, x) :: xs) j h :=
  if h' : j < i then x
  else freq_aux xs (j - i)
    (by rw nat.sub_lt_right_iff_lt_add; [simpa [list.sum_cons, add_comm] using h, exact le_of_not_gt h'])

/--
`freq [(1, gena), (3, genb), (5, genc)] _` will choose one of `gena`, `genb`, `genc` with
probabiities proportional to the number accompanying them. In this example, the sum of
those numbers is 9, `gena` will be chosen with probability ~1/9, `genb` with ~3/9 (i.e. 1/3)
and `genc` with probability 5/9.
-/
def freq (xs : list (ℕ+ × gen α)) (pos : 0 < xs.length) : gen α :=
let s := (xs.map (subtype.val ∘ prod.fst)).sum in
have ha : 1 ≤ s, from
  (le_trans pos $
    list.length_map (subtype.val ∘ prod.fst) xs ▸ (list.length_le_sum_of_one_le _ (λ i, by simp; intros h _; exact h))),
have 0 ≤ s - 1, from nat.le_sub_right_of_add_le ha,
uliftable.adapt_up gen.{0} gen.{u} (choose_nat 0 (s-1) this) $ λ i,
freq_aux xs i.1 (by rcases i with ⟨i,h₀,h₁⟩; rwa nat.le_sub_right_iff_add_le at h₁; exact ha)

/-- Generate a random permutation of a given list. -/
def permutation_of {α : Type u} : Π xs : list α, gen (subtype $ list.perm xs)
| [] := pure ⟨[], list.perm.nil ⟩
| (x :: xs) := do
⟨xs',h⟩ ← permutation_of xs,
⟨⟨n,_,h'⟩⟩ ← uliftable.up $ choose_nat 0 xs'.length dec_trivial,
pure ⟨list.insert_nth n x xs',
  list.perm.trans (list.perm.cons _ h)
    (list.perm_insert_nth _ _ h').symm ⟩

end gen

end slim_check
