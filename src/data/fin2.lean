/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

/-!
# Inductive type variant of `fin`

`fin` is defined as a subtype of `ℕ`. This file defines an equivalent type, `fin2`, which is
defined inductively. This is useful for its induction principle and different definitional
equalities.

## Main declarations

* `fin2 n`: Inductive type variant of `fin n`. `fz` corresponds to `0` and `fs n` corresponds to
  `n`.
* `to_nat`, `opt_of_nat`, `of_nat'`: Conversions to and from `ℕ`. `of_nat' m` takes a proof that
  `m < n` through the class `is_lt`.
* `add k`: Takes `i : fin2 n` to `i + k : fin2 (n + k)`.
* `left`: Embeds `fin2 n` into `fin2 (n + k)`.
* `insert_perm a`: Permutation of `fin2 n` which cycles `0, ..., a - 1` and leaves `a, ..., n - 1`
  unchanged.
* `remap_left f`: Function `fin2 (m + k) → fin2 (n + k)` by applying `f : fin m → fin n` to
  `0, ..., m - 1` and sending `m + i` to `n + i`.
-/

open nat
universes u

/-- An alternate definition of `fin n` defined as an inductive type instead of a subtype of `ℕ`. -/
inductive fin2 : ℕ → Type
/-- `0` as a member of `fin (succ n)` (`fin 0` is empty) -/
| fz {n} : fin2 (succ n)
/-- `n` as a member of `fin (succ n)` -/
| fs {n} : fin2 n → fin2 (succ n)

namespace fin2

/-- Define a dependent function on `fin2 (succ n)` by giving its value at
zero (`H1`) and by giving a dependent function on the rest (`H2`). -/
@[elab_as_eliminator]
protected def cases' {n} {C : fin2 (succ n) → Sort u} (H1 : C fz) (H2 : Π n, C (fs n)) :
  Π (i : fin2 (succ n)), C i
| fz     := H1
| (fs n) := H2 n

/-- Ex falso. The dependent eliminator for the empty `fin2 0` type. -/
def elim0 {C : fin2 0 → Sort u} : Π (i : fin2 0), C i.

/-- Converts a `fin2` into a natural. -/
def to_nat : Π {n}, fin2 n → ℕ
| ._ (@fz n)   := 0
| ._ (@fs n i) := succ (to_nat i)

/-- Converts a natural into a `fin2` if it is in range -/
def opt_of_nat : Π {n} (k : ℕ), option (fin2 n)
| 0 _ := none
| (succ n) 0 := some fz
| (succ n) (succ k) := fs <$> @opt_of_nat n k

/-- `i + k : fin2 (n + k)` when `i : fin2 n` and `k : ℕ` -/
def add {n} (i : fin2 n) : Π k, fin2 (n + k)
| 0        := i
| (succ k) := fs (add k)

/-- `left k` is the embedding `fin2 n → fin2 (k + n)` -/
def left (k) : Π {n}, fin2 n → fin2 (k + n)
| ._ (@fz n)   := fz
| ._ (@fs n i) := fs (left i)

/-- `insert_perm a` is a permutation of `fin2 n` with the following properties:
  * `insert_perm a i = i+1` if `i < a`
  * `insert_perm a a = 0`
  * `insert_perm a i = i` if `i > a` -/
def insert_perm : Π {n}, fin2 n → fin2 n → fin2 n
| ._ (@fz n)          (@fz ._)   := fz
| ._ (@fz n)          (@fs ._ j) := fs j
| ._ (@fs (succ n) i) (@fz ._)   := fs fz
| ._ (@fs (succ n) i) (@fs ._ j) := match insert_perm i j with fz := fz | fs k := fs (fs k) end

/-- `remap_left f k : fin2 (m + k) → fin2 (n + k)` applies the function
  `f : fin2 m → fin2 n` to inputs less than `m`, and leaves the right part
  on the right (that is, `remap_left f k (m + i) = n + i`). -/
def remap_left {m n} (f : fin2 m → fin2 n) : Π k, fin2 (m + k) → fin2 (n + k)
| 0        i          := f i
| (succ k) (@fz ._)   := fz
| (succ k) (@fs ._ i) := fs (remap_left _ i)

/-- This is a simple type class inference prover for proof obligations
  of the form `m < n` where `m n : ℕ`. -/
class is_lt (m n : ℕ) := (h : m < n)
instance is_lt.zero (n) : is_lt 0 (succ n) := ⟨succ_pos _⟩
instance is_lt.succ (m n) [l : is_lt m n] : is_lt (succ m) (succ n) := ⟨succ_lt_succ l.h⟩

/-- Use type class inference to infer the boundedness proof, so that we can directly convert a
`nat` into a `fin2 n`. This supports notation like `&1 : fin 3`. -/
def of_nat' : Π {n} m [is_lt m n], fin2 n
| 0        m        ⟨h⟩ := absurd h (not_lt_zero _)
| (succ n) 0        ⟨h⟩ := fz
| (succ n) (succ m) ⟨h⟩ := fs (@of_nat' n m ⟨lt_of_succ_lt_succ h⟩)

local prefix `&`:max := of_nat'

instance : inhabited (fin2 1) := ⟨fz⟩

end fin2
