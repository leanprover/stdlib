/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

Case bashing on variables in finite intervals.

In particular, `interval_cases n`
1) inspects hypotheses looking for lower and upper bounds of the form `a ≤ n` and `n < b`
   (although in `ℕ`, `ℤ`, and `ℕ+` bounds of the form `a < n` and `n ≤ b` are also allowed),
   and also makes use of lower and upper bounds found via `le_top` and `bot_le`
   (so for example if `n : ℕ`, then the bound `0 ≤ n` is found automatically), then
2) calls `fin_cases` on the synthesised hypothesis `n ∈ set.Ico a b`,
   assuming an appropriate `fintype` instance can be found for the type of `n`.

The variable `n` can belong to any type `α`, with the following restrictions:
* only bounds on which `expr.to_rat` succeeds will be considered "explicit" (TODO: generalise this?)
* an instance of `decidable_eq α` is available,
* an explicit lower bound can be found amongst the hypotheses, or from `bot_le n`,
* an explicit upper bound can be found amongst the hypotheses, or from `le_top n`,
* if multiple bounds are located, an instance of `linear_order α` is available, and
* an instance of `fintype set.Ico l u` is available for the relevant bounds.

You can also explicitly specify a lower and upper bound to use, as `interval_cases using hl hu`.
The hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,
in which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ set.Ico a b`.

-/
import tactic.fin_cases
import data.fintype.intervals

open set

namespace tactic

namespace interval_cases

/--
If `e` easily implies `(%%n < %%b)`
for some explicit `b`,
return that proof.
-/
-- We use `expr.to_rat` merely to decide if an `expr` is an explicit number.
-- It would be more natural to use `expr.to_int`, but that hasn't been implemented.
meta def gives_upper_bound (n e : expr) : tactic expr :=
do t ← infer_type e,
   match t with
   | `(%%n' < %%b) := do guard (n = n'), b ← b.to_rat, return e
   | `(%%b > %%n') := do guard (n = n'), b ← b.to_rat, return e
   | `(%%n' ≤ %%b) := do
      guard (n = n'),
      b ← b.to_rat,
      tn ← infer_type n,
      match tn with
      | `(ℕ) := to_expr ``(nat.lt_add_one_iff.mpr %%e)
      | `(ℕ+) := to_expr ``(pnat.lt_add_one_iff.mpr %%e)
      | `(ℤ) := to_expr ``(int.lt_add_one_iff.mpr %%e)
      | _ := failed
      end
   | `(%%b ≥ %%n') := do
      guard (n = n'),
      b ← b.to_rat,
      tn ← infer_type n,
      match tn with
      | `(ℕ) := to_expr ``(nat.add_one_le_iff.mpr %%e)
      | `(ℕ+) := to_expr ``(pnat.add_one_le_iff.mpr %%e)
      | `(ℤ) := to_expr ``(int.add_one_le_iff.mpr %%e)
      | _ := failed
      end
   | _ := failed
   end

/--
If `e` easily implies `(%%n ≥ %%b)`
for some explicit `b`,
return that proof.
-/
meta def gives_lower_bound (n e : expr) : tactic expr :=
do t ← infer_type e,
   match t with
   | `(%%n' ≥ %%b) := do guard (n = n'), b ← b.to_rat, return e
   | `(%%b ≤ %%n') := do guard (n = n'), b ← b.to_rat, return e
   | `(%%n' > %%b) := do
      guard (n = n'),
      b ← b.to_rat,
      tn ← infer_type n,
      match tn with
      | `(ℕ) := to_expr ``(nat.add_one_le_iff.mpr %%e)
      | `(ℕ+) := to_expr ``(pnat.add_one_le_iff.mpr %%e)
      | `(ℤ) := to_expr ``(int.add_one_le_iff.mpr %%e)
      | _ := failed
      end
   | `(%%b < %%n') := do
      guard (n = n'),
      b ← b.to_rat,
      tn ← infer_type n,
      match tn with
      | `(ℕ) := to_expr ``(nat.add_one_le_iff.mpr %%e)
      | `(ℕ+) := to_expr ``(pnat.add_one_le_iff.mpr %%e)
      | `(ℤ) := to_expr ``(int.add_one_le_iff.mpr %%e)
      | _ := failed
      end
   | _ := failed
   end

/-- Combine two upper bounds. -/
meta def combine_upper_bounds : option expr → option expr → tactic (option expr)
| none none := return none
| (some prf) none := return $ some prf
| none (some prf) := return $ some prf
| (some prf₁) (some prf₂) :=
  do option.some <$> to_expr ``(lt_min %%prf₁ %%prf₂)

/-- Combine two lower bounds. -/
meta def combine_lower_bounds : option expr → option expr → tactic (option expr)
| none none := return $ none
| (some prf) none := return $ some prf
| none (some prf) := return $ some prf
| (some prf₁) (some prf₂) :=
  do option.some <$> to_expr ``(max_le %%prf₂ %%prf₁)

/-- Inspect a given expression, using it to update a set of upper and lower bounds on `n`. -/
meta def update_bounds (n : expr) (bounds : option expr × option expr) (e : expr) :
  tactic (option expr × option expr) :=
do nlb ← try_core $ gives_lower_bound n e,
   nub ← try_core $ gives_upper_bound n e,
   clb ← combine_lower_bounds bounds.1 nlb,
   cub ← combine_upper_bounds bounds.2 nub,
   return (clb, cub)

/--
Attempt to find a lower bound for the variable `n`, by evaluating `bot_le n`.
-/
meta def initial_lower_bound (n : expr) : tactic expr :=
do e ← to_expr ``(@bot_le _ _ %%n),
   t ← infer_type e,
   match t with
   | `(%%b ≤ %%n) := do return e
   | _ := failed
   end

/--
Attempt to find an upper bound for the variable `n`, by evaluating `le_top n`.
-/
meta def initial_upper_bound (n : expr) : tactic expr :=
do e ← to_expr ``(@le_top _ _ %%n),
   match e with
   | `(%%n ≤ %%b) := do
     tn ← infer_type n,
     e ← match tn with
     | `(ℕ) := to_expr ``(nat.add_one_le_iff.mpr %%e)
     | `(ℕ+) := to_expr ``(pnat.add_one_le_iff.mpr %%e)
     | `(ℤ) := to_expr ``(int.add_one_le_iff.mpr %%e)
     | _ := failed
     end,
     return e
   | _ := failed
   end

/-- Inspect the local hypotheses for upper and lower bounds on a variable `n`. -/
meta def get_bounds (n : expr) : tactic (expr × expr) :=
do
  hl ← try_core (initial_lower_bound n),
  hu ← try_core (initial_upper_bound n),
  lc ← local_context,
  r ← lc.mfoldl (update_bounds n) (hl, hu),
  match r with
  | (_, none) := fail "No upper bound located."
  | (none, _) := fail "No lower bound located."
  | (some lb_prf, some ub_prf) := return (lb_prf, ub_prf)
  end

/-- The finset of elements of a set `s` for which we have `fintype s`. -/
def set_elems {α} [decidable_eq α] (s : set α) [fintype s] : finset α :=
(fintype.elems s).image subtype.val

/-- Each element of `s` is a member of `set_elems s`. -/
lemma mem_set_elems {α} [decidable_eq α] (s : set α) [fintype s] {a : α} (h : a ∈ s) :
  a ∈ set_elems s :=
finset.mem_image.2 ⟨⟨a, h⟩, fintype.complete _, rfl⟩

end interval_cases

open interval_cases

/-- Call `fin_cases` on membership of the finset built from
an `Ico` interval corresponding to a lower and an upper bound.

Here `hl` should be an expression of the form `a ≤ n`, for some explicit `a`, and
`hu` should be of the form `n < b`, for some explicit `b`.

By default `interval_cases_using` automatically generates a name for the new hypothesis. The name
can be specified via the optional argument `n`.
-/
meta def interval_cases_using (hl hu : expr) (n : option name) : tactic unit :=
to_expr ``(mem_set_elems (Ico _ _) ⟨%%hl, %%hu⟩) >>=
(if hn : n.is_some then
  note (option.get hn)
else
  note_anon none) >>= fin_cases_at none

setup_tactic_parser

namespace interactive

local postfix `?`:9001 := optional

/--
`interval_cases n` searches for upper and lower bounds on a variable `n`,
and if bounds are found,
splits into separate cases for each possible value of `n`.

As an example, in
```
example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
begin
  interval_cases n,
  all_goals {simp}
end
```
after `interval_cases n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.

You can also explicitly specify a lower and upper bound to use,
as `interval_cases using hl hu`.
The hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,
in which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ set.Ico a b`.

You can specify a name `h` for the new hypothesis,
as `interval_cases n with h` or `interval_cases n using hl hu with h`.
-/
meta def interval_cases (n : parse texpr?)
  (bounds : parse (tk "using" *> (prod.mk <$> ident <*> ident))?)
  (lname : parse (tk "with" *> ident)?) :
  tactic unit :=
do
  if h : n.is_some then (do
    guard bounds.is_none <|>
      fail "Do not use the `using` keyword if specifying the variable explicitly.",
    n ← to_expr (option.get h),
    (hl, hu) ← get_bounds n,
    tactic.interval_cases_using hl hu lname)
  else if h' : bounds.is_some then (do
    [hl, hu] ← [(option.get h').1, (option.get h').2].mmap get_local,
    tactic.interval_cases_using hl hu lname)
  else
    fail "Call `interval_cases n` (specifying a variable), or `interval_cases lb ub` (specifying a lower bound and upper bound on the same variable)."

/--
`interval_cases n` searches for upper and lower bounds on a variable `n`,
and if bounds are found,
splits into separate cases for each possible value of `n`.

As an example, in
```
example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
begin
  interval_cases n,
  all_goals {simp}
end
```
after `interval_cases n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.

You can also explicitly specify a lower and upper bound to use,
as `interval_cases using hl hu`.
The hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,
in which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ set.Ico a b`.

You can also explicitly specify a name to use for the hypothesis added,
as `interval_cases n with hn` or `interval_cases n using hl hu with hn`.

In particular, `interval_cases n`
1) inspects hypotheses looking for lower and upper bounds of the form `a ≤ n` and `n < b`
   (although in `ℕ`, `ℤ`, and `ℕ+` bounds of the form `a < n` and `n ≤ b` are also allowed),
   and also makes use of lower and upper bounds found via `le_top` and `bot_le`
   (so for example if `n : ℕ`, then the bound `0 ≤ n` is found automatically), then
2) calls `fin_cases` on the synthesised hypothesis `n ∈ set.Ico a b`,
   assuming an appropriate `fintype` instance can be found for the type of `n`.

The variable `n` can belong to any type `α`, with the following restrictions:
* only bounds on which `expr.to_rat` succeeds will be considered "explicit" (TODO: generalise this?)
* an instance of `decidable_eq α` is available,
* an explicit lower bound can be found amongst the hypotheses, or from `bot_le n`,
* an explicit upper bound can be found amongst the hypotheses, or from `le_top n`,
* if multiple bounds are located, an instance of `linear_order α` is available, and
* an instance of `fintype set.Ico l u` is available for the relevant bounds.
-/
add_tactic_doc
{ name       := "interval_cases",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.interval_cases],
  tags       := ["case bashing"] }

end interactive

end tactic
