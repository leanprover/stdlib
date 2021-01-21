/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich
-/

import data.vector2

/-!
# Basic operations on bitvectors

This is a work-in-progress, and contains additions to other theories.

This file was moved to mathlib from core Lean in the switch to Lean 3.20.0c. It is not fully in compliance with mathlib style standards.
-/

/-- `bitvec n` is a `vector` of `bool` with length `n`. -/
@[reducible] def bitvec (n : ℕ) := vector bool n

namespace bitvec
open nat
open vector

local infix `++ₜ`:65 := vector.append

/-- Create a zero bitvector -/
@[reducible] protected def zero (n : ℕ) : bitvec n := repeat ff n

/-- Create a bitvector of length `n` whose `n-1`st entry is 1 and other entries are 0. -/
@[reducible] protected def one : Π (n : ℕ), bitvec n
| 0        := nil
| (succ n) := repeat ff n ++ₜ tt::ᵥnil

/-- Create a bitvector from another with a provably equal length. -/
protected def cong {a b : ℕ} (h : a = b) : bitvec a → bitvec b
| ⟨x, p⟩ := ⟨x, h ▸ p⟩

/-- `bitvec` specific version of `vector.append` -/
def append {m n} : bitvec m → bitvec n → bitvec (m + n) := vector.append


/-! ### Shift operations -/
section shift
variable {n : ℕ}

/-- `shl x i` is the bitvector obtained by left-shifting `x` `i` times and padding with `ff`.
If `x.length < i` then this will return the all-`ff`s bitvector. -/
def shl (x : bitvec n) (i : ℕ) : bitvec n :=
bitvec.cong (by simp) $
  drop i x ++ₜ repeat ff (min n i)

/-- `fill_shr x i fill` is the bitvector obtained by right-shifting `x` `i` times and then
padding with `fill : bool`. If `x.length < i` then this will return the constant `fill`
bitvector. -/
def fill_shr (x : bitvec n) (i : ℕ) (fill : bool) : bitvec n :=
bitvec.cong
  begin
    by_cases (i ≤ n),
    { have h₁ := sub_le n i,
      rw [min_eq_right h], rw [min_eq_left h₁, ← nat.add_sub_assoc h, nat.add_comm, nat.add_sub_cancel] },
    { have h₁ := le_of_not_ge h,
      rw [min_eq_left h₁, sub_eq_zero_of_le h₁, zero_min, nat.add_zero] }
  end $
  repeat fill (min n i) ++ₜ take (n-i) x

/-- unsigned shift right -/
def ushr (x : bitvec n) (i : ℕ) : bitvec n :=
fill_shr x i ff

/-- signed shift right -/
def sshr : Π {m : ℕ}, bitvec m → ℕ → bitvec m
| 0        _ _ := nil
| (succ m) x i := head x ::ᵥ fill_shr (tail x) i (head x)

end shift

/-! ### Bitwise operations -/
section bitwise
variable {n : ℕ}

/-- bitwise not -/
def not : bitvec n → bitvec n := map bnot
/-- bitwise and -/
def and : bitvec n → bitvec n → bitvec n := map₂ band
/-- bitwise or -/
def or  : bitvec n → bitvec n → bitvec n := map₂ bor
/-- bitwise xor -/
def xor : bitvec n → bitvec n → bitvec n := map₂ bxor

end bitwise

/-! ### Arithmetic operators -/
section arith
variable {n : ℕ}

/-- `xor3 x y c` is `((x XOR y) XOR c)`. -/
protected def xor3 (x y c : bool) := bxor (bxor x y) c
/-- `carry x y c` is `x && y || x && c || y && c`. -/
protected def carry (x y c : bool) :=
x && y || x && c || y && c

/-- `neg x` is the two's complement of `x`. -/
protected def neg (x : bitvec n) : bitvec n :=
let f := λ y c, (y || c, bxor y c) in
prod.snd (map_accumr f x ff)

/-- Add with carry (no overflow) -/
def adc (x y : bitvec n) (c : bool) : bitvec (n+1) :=
let f := λ x y c, (bitvec.carry x y c, bitvec.xor3 x y c) in
let ⟨c, z⟩ := vector.map_accumr₂ f x y c in
c ::ᵥ z

/-- The sum of two bitvectors -/
protected def add (x y : bitvec n) : bitvec n := tail (adc x y ff)

/-- Subtract with borrow -/
def sbb (x y : bitvec n) (b : bool) : bool × bitvec n :=
let f := λ x y c, (bitvec.carry (bnot x) y c, bitvec.xor3 x y c) in
vector.map_accumr₂ f x y b

/-- The difference of two bitvectors -/
protected def sub (x y : bitvec n) : bitvec n := prod.snd (sbb x y ff)

instance : has_zero (bitvec n) := ⟨bitvec.zero n⟩
instance : has_one (bitvec n)  := ⟨bitvec.one n⟩
instance : has_add (bitvec n)  := ⟨bitvec.add⟩
instance : has_sub (bitvec n)  := ⟨bitvec.sub⟩
instance : has_neg (bitvec n)  := ⟨bitvec.neg⟩

/-- The product of two bitvectors -/
protected def mul (x y : bitvec n) : bitvec n :=
let f := λ r b, cond b (r + r + y) (r + r) in
(to_list x).foldl f 0

instance : has_mul (bitvec n)  := ⟨bitvec.mul⟩
end arith

/-! ### Comparison operators -/
section comparison
variable {n : ℕ}

/-- `uborrow x y` returns `tt` iff the "subtract with borrow" operation on `x`, `y` and `ff`
required a borrow. -/
def uborrow (x y : bitvec n) : bool := prod.fst (sbb x y ff)

/-- unsigned less-than proposition -/
def ult (x y : bitvec n) : Prop := uborrow x y
/-- unsigned greater-than proposition -/
def ugt (x y : bitvec n) : Prop := ult y x

/-- unsigned less-than-or-equal-to proposition -/
def ule (x y : bitvec n) : Prop := ¬ (ult y x)
/-- unsigned greater-than-or-equal-to proposition -/
def uge (x y : bitvec n) : Prop := ule y x

/-- `sborrow x y` returns `tt` iff `x < y` as two's complement integers -/
def sborrow : Π {n : ℕ}, bitvec n → bitvec n → bool
| 0        _ _ := ff
| (succ n) x y :=
  match (head x, head y) with
  | (tt, ff) := tt
  | (ff, tt) := ff
  | _        := uborrow (tail x) (tail y)
  end

/-- signed less-than proposition -/
def slt (x y : bitvec n) : Prop := sborrow x y
/-- signed greater-than proposition -/
def sgt (x y : bitvec n) : Prop := slt y x
/-- signed less-than-or-equal-to proposition -/
def sle (x y : bitvec n) : Prop := ¬ (slt y x)
/-- signed greater-than-or-equal-to proposition -/
def sge (x y : bitvec n) : Prop := sle y x

end comparison

/-! ### Conversion to `nat` and `int` -/
section conversion
variable {α : Type}

/-- Create a bitvector from a `nat` -/
protected def of_nat : Π (n : ℕ), nat → bitvec n
| 0        x := nil
| (succ n) x := of_nat n (x / 2) ++ₜ to_bool (x % 2 = 1) ::ᵥ nil

/-- Create a bitvector in the two's complement representation from an `int` -/
protected def of_int : Π (n : ℕ), int → bitvec (succ n)
| n (int.of_nat m)          := ff ::ᵥ bitvec.of_nat n m
| n (int.neg_succ_of_nat m) := tt ::ᵥ not (bitvec.of_nat n m)

/-- `add_lsb r b` is `r + r + 1` if `b` is `tt` and `r + r` otherwise. -/
def add_lsb (r : ℕ) (b : bool) := r + r + cond b 1 0

/-- Given a `list` of `bool`s, return the `nat` they represent as a list of binary digits. -/
def bits_to_nat (v : list bool) : nat :=
v.foldl add_lsb 0

/-- Return the natural number encoded by the input bitvector -/
protected def to_nat {n : nat} (v : bitvec n) : nat :=
bits_to_nat (to_list v)

theorem bits_to_nat_to_list {n : ℕ} (x : bitvec n) :
bitvec.to_nat x = bits_to_nat (vector.to_list x)  := rfl

local attribute [simp] nat.add_comm nat.add_assoc nat.add_left_comm nat.mul_comm nat.mul_assoc
local attribute [simp] nat.zero_add nat.add_zero nat.one_mul nat.mul_one nat.zero_mul nat.mul_zero
-- mul_left_comm

theorem to_nat_append {m : ℕ} (xs : bitvec m) (b : bool) :
bitvec.to_nat (xs ++ₜ b::ᵥnil) = bitvec.to_nat xs * 2 + bitvec.to_nat (b::ᵥnil) :=
begin
  cases xs with xs P,
  simp [bits_to_nat_to_list], clear P,
  unfold bits_to_nat list.foldl,
  -- generalize the accumulator of foldl
  generalize h : 0 = x, conv in (add_lsb x b) { rw ←h }, clear h,
  simp,
  induction xs with x xs generalizing x,
  { simp, unfold list.foldl add_lsb, simp [nat.mul_succ] },
  { simp, apply xs_ih }
end

theorem bits_to_nat_to_bool (n : ℕ)
: bitvec.to_nat (to_bool (n % 2 = 1) ::ᵥ nil) = n % 2 :=
begin
  simp [bits_to_nat_to_list],
  unfold bits_to_nat add_lsb list.foldl cond,
  simp [cond_to_bool_mod_two],
end

theorem of_nat_succ {k n : ℕ}
:  bitvec.of_nat (succ k) n = bitvec.of_nat k (n / 2) ++ₜ to_bool (n % 2 = 1) ::ᵥ nil :=
rfl

theorem to_nat_of_nat {k n : ℕ}
: bitvec.to_nat (bitvec.of_nat k n) = n % 2 ^ k :=
begin
  induction k with k ih generalizing n,
  { simp [nat.mod_one], refl },
  { have h : 0 < 2, { apply le_succ },
    rw [of_nat_succ, to_nat_append, ih, bits_to_nat_to_bool, mod_pow_succ h, nat.mul_comm] }
end

/-- Return the integer encoded by the input bitvector -/
protected def to_int : Π {n : nat}, bitvec n → int
| 0        _ := 0
| (succ n) v :=
  cond (head v)
    (int.neg_succ_of_nat $ bitvec.to_nat $ not $ tail v)
    (int.of_nat $ bitvec.to_nat $ tail v)

end conversion

/-! ### Miscellaneous instances -/
private def repr {n : nat} : bitvec n → string
| ⟨bs, p⟩ :=
  "0b" ++ (bs.map (λ b : bool, if b then '1' else '0')).as_string

instance (n : nat) : has_repr (bitvec n) :=
⟨repr⟩
end bitvec

instance {n} {x y : bitvec n} : decidable (bitvec.ult x y) := bool.decidable_eq _ _
instance {n} {x y : bitvec n} : decidable (bitvec.ugt x y) := bool.decidable_eq _ _
