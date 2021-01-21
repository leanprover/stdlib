/-
Copyright (c) 2019 Robert Y. Lewis . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/
import data.rat.basic

/-!
# Meta operations on ℚ

This file defines functions for dealing with rational numbers as expressions.

They are not defined earlier in the hierarchy, in the `tactic` or `meta` folders, since we do not
want to import `data.rat.basic` there.

## Main definitions

* `rat.mk_numeral` embeds a rational `q` as a numeral expression into a type supporting the needed
  operations. It does not need a tactic state.
* `rat.reflect` specializes `rat.mk_numeral` to `ℚ`.
* `expr.of_rat` behaves like `rat.mk_numeral`, but uses the tactic state to infer the needed
  structure on the target type.

* `expr.to_rat` evaluates a normal numeral expression as a rat.
* `expr.eval_rat` evaluates a numeral expression with arithmetic operations as a rat.

-/

/--
`rat.mk_numeral q` embeds `q` as a numeral expression inside a type with 0, 1, +, -, and /

`type`: an expression representing the target type. This must live in Type 0.
`has_zero`, `has_one`, `has_add`: expressions of the type `has_zero %%type`, etc.

This function is similar to `expr.of_rat` but takes more hypotheses and is not tactic valued.
 -/
meta def rat.mk_numeral (type has_zero has_one has_add has_neg has_div : expr) : ℚ → expr
| ⟨num, denom, _, _⟩ :=
  let nume := num.mk_numeral type has_zero has_one has_add has_neg in
  if denom = 1 then nume else
    let dene := denom.mk_numeral type has_zero has_one has_add in
    `(@has_div.div.{0} %%type %%has_div %%nume %%dene)

/-- `rat.reflect q` represents the rational number `q` as a numeral expression of type `ℚ`. -/
protected meta def rat.reflect : ℚ → expr :=
rat.mk_numeral `(ℚ) `((by apply_instance : has_zero ℚ))
         `((by apply_instance : has_one ℚ))`((by apply_instance : has_add ℚ))
         `((by apply_instance : has_neg ℚ)) `(by apply_instance : has_div ℚ)

section
local attribute [semireducible] reflected
meta instance : has_reflect ℚ := rat.reflect
end

/-- Evaluates an expression as a rational number,
if that expression represents a numeral or the quotient of two numerals. -/
protected meta def expr.to_nonneg_rat : expr → option ℚ
| `(%%e₁ / %%e₂) := do
  m ← e₁.to_nat,
  n ← e₂.to_nat,
  if c : m.coprime n then if h : 1 < n then
    return ⟨m, n, lt_trans zero_lt_one h, c⟩
  else none else none
| e := do n ← e.to_nat, return (rat.of_int n)

/-- Evaluates an expression as a rational number,
if that expression represents a numeral, the quotient of two numerals,
the negation of a numeral, or the negation of the quotient of two numerals. -/
protected meta def expr.to_rat : expr → option ℚ
| `(has_neg.neg %%e) := do q ← e.to_nonneg_rat, some (-q)
| e                  := e.to_nonneg_rat

/-- Evaluates an expression into a rational number, if that expression is built up from
  numerals, +, -, *, /, ⁻¹  -/
protected meta def expr.eval_rat : expr → option ℚ
| `(has_zero.zero) := some 0
| `(has_one.one) := some 1
| `(bit0 %%q) := (*) 2 <$> q.eval_rat
| `(bit1 %%q) := (+) 1 <$> (*) 2 <$> q.eval_rat
| `(%%a + %%b) := (+) <$> a.eval_rat <*> b.eval_rat
| `(%%a - %%b) := has_sub.sub <$> a.eval_rat <*> b.eval_rat
| `(%%a * %%b) := (*) <$> a.eval_rat <*> b.eval_rat
| `(%%a / %%b) := (/) <$> a.eval_rat <*> b.eval_rat
| `(-(%%a)) := has_neg.neg <$> a.eval_rat
| `((%%a)⁻¹) := has_inv.inv <$> a.eval_rat
| _ := none

/-- `expr.of_rat α q` embeds `q` as a numeral expression inside the type `α`.
Lean will try to infer the correct type classes on `α`, and the tactic will fail if it cannot.
This function is similar to `rat.mk_numeral` but it takes fewer hypotheses and is tactic valued.
-/
protected meta def expr.of_rat (α : expr) : ℚ → tactic expr
| ⟨(n:ℕ), d, h, c⟩   := do
  e₁ ← expr.of_nat α n,
  if d = 1 then return e₁ else
  do e₂ ← expr.of_nat α d,
  tactic.mk_app ``has_div.div [e₁, e₂]
| ⟨-[1+n], d, h, c⟩ := do
  e₁ ← expr.of_nat α (n+1),
  e ← (if d = 1 then return e₁ else do
    e₂ ← expr.of_nat α d,
    tactic.mk_app ``has_div.div [e₁, e₂]),
  tactic.mk_app ``has_neg.neg [e]

namespace tactic
namespace instance_cache

/-- `c.of_rat q` embeds `q` as a numeral expression inside the type `α`.
Lean will try to infer the correct type classes on `c.α`, and the tactic will fail if it cannot.
This function is similar to `rat.mk_numeral` but it takes fewer hypotheses and is tactic valued.
-/
protected meta def of_rat (c : instance_cache) : ℚ → tactic (instance_cache × expr)
| ⟨(n:ℕ), d, _, _⟩   :=
  if d = 1 then c.of_nat n else do
    (c, e₁) ← c.of_nat n,
    (c, e₂) ← c.of_nat d,
    c.mk_app ``has_div.div [e₁, e₂]
| ⟨-[1+n], d, _, _⟩ := do
  (c, e) ← (if d = 1 then c.of_nat (n+1) else do
    (c, e₁) ← c.of_nat (n+1),
    (c, e₂) ← c.of_nat d,
    c.mk_app ``has_div.div [e₁, e₂]),
  c.mk_app ``has_neg.neg [e]

end instance_cache
end tactic
