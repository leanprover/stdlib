/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import tactic.norm_num
import data.tree

/-!
# A tactic for canceling numeric denominators

This file defines tactics that cancel numeric denominators from field expressions.

As an example, we want to transform a comparison `5*(a/3 + b/4) < c/3` into the equivalent
`5*(4*a + 3*b) < 4*c`.

## Implementation notes

The tooling here was originally written for `linarith`, not intended as an interactive tactic.
The interactive version has been split off because it is sometimes convenient to use on its own.
There are likely some rough edges to it.

Improving this tactic would be a good project for someone interested in learning tactic programming.
-/

namespace cancel_factors

/-! ### Lemmas used in the procedure -/

lemma mul_subst {α} [comm_ring α] {n1 n2 k e1 e2 t1 t2 : α} (h1 : n1 * e1 = t1) (h2 : n2 * e2 = t2)
     (h3 : n1*n2 = k) : k * (e1 * e2) = t1 * t2 :=
have h3 : n1 * n2 = k, from h3,
by rw [←h3, mul_comm n1, mul_assoc n2, ←mul_assoc n1, h1, ←mul_assoc n2, mul_comm n2, mul_assoc, h2]

lemma div_subst {α} [field α] {n1 n2 k e1 e2 t1 : α} (h1 : n1 * e1 = t1) (h2 : n2 / e2 = 1)
   (h3 : n1*n2 = k) : k * (e1 / e2) = t1 :=
by rw [←h3, mul_assoc, mul_div_comm, h2, ←mul_assoc, h1, mul_comm, one_mul]

lemma cancel_factors_eq_div {α} [field α] {n e e' : α} (h : n*e = e') (h2 : n ≠ 0) :
  e = e' / n :=
eq_div_of_mul_eq h2 $ by rwa mul_comm at h

lemma add_subst {α} [ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
      n * (e1 + e2) = t1 + t2 := by simp [left_distrib, *]

lemma sub_subst {α} [ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
      n * (e1 - e2) = t1 - t2 := by simp [left_distrib, *, sub_eq_add_neg]

lemma neg_subst {α} [ring α] {n e t : α} (h1 : n * e = t) : n * (-e) = -t := by simp *

lemma cancel_factors_lt {α} [linear_ordered_field α] {a b ad bd a' b' gcd : α} (ha : ad*a = a')
  (hb : bd*b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
  a < b = ((1/gcd)*(bd*a') < (1/gcd)*(ad*b')) :=
begin
  rw [mul_lt_mul_left, ←ha, ←hb, ←mul_assoc, ←mul_assoc, mul_comm bd, mul_lt_mul_left],
  exact mul_pos had hbd,
  exact one_div_pos.2 hgcd
end

lemma cancel_factors_le {α} [linear_ordered_field α] {a b ad bd a' b' gcd : α} (ha : ad*a = a')
  (hb : bd*b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd)  :
  a ≤ b = ((1/gcd)*(bd*a') ≤ (1/gcd)*(ad*b')) :=
begin
  rw [mul_le_mul_left, ←ha, ←hb, ←mul_assoc, ←mul_assoc, mul_comm bd, mul_le_mul_left],
  exact mul_pos had hbd,
  exact one_div_pos.2 hgcd
end

lemma cancel_factors_eq {α} [linear_ordered_field α] {a b ad bd a' b' gcd : α} (ha : ad*a = a')
  (hb : bd*b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
  a = b = ((1/gcd)*(bd*a') = (1/gcd)*(ad*b')) :=
begin
  rw [←ha, ←hb, ←mul_assoc bd, ←mul_assoc ad, mul_comm bd],
  ext, split,
  { rintro rfl, refl },
  { intro h,
    simp only [←mul_assoc] at h,
    refine mul_left_cancel' (mul_ne_zero _ _) h,
    apply mul_ne_zero, apply div_ne_zero,
    all_goals {apply ne_of_gt; assumption <|> exact zero_lt_one}}
end

open tactic expr

/-! ### Computing cancelation factors -/

open tree

/--
`find_cancel_factor e` produces a natural number `n`, such that multiplying `e` by `n` will
be able to cancel all the numeric denominators in `e`. The returned `tree` describes how to
distribute the value `n` over products inside `e`.
-/
meta def find_cancel_factor : expr → ℕ × tree ℕ
| `(%%e1 + %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, lcm := v1.lcm v2 in
  (lcm, node lcm t1 t2)
| `(%%e1 - %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, lcm := v1.lcm v2 in
  (lcm, node lcm t1 t2)
| `(%%e1 * %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, pd := v1*v2 in
  (pd, node pd t1 t2)
| `(%%e1 / %%e2) :=
  match e2.to_nonneg_rat with
  | some q := let (v1, t1) := find_cancel_factor e1, n := v1.lcm q.num.nat_abs in
    (n, node n t1 (node q.num.nat_abs tree.nil tree.nil))
  | none := (1, node 1 tree.nil tree.nil)
  end
| `(-%%e) := find_cancel_factor e
| _ := (1, node 1 tree.nil tree.nil)

/--
`mk_prod_prf n tr e` produces a proof of `n*e = e'`, where numeric denominators have been
canceled in `e'`, distributing `n` proportionally according to `tr`.
-/
meta def mk_prod_prf : ℕ → tree ℕ → expr → tactic expr
| v (node _ lhs rhs) `(%%e1 + %%e2) :=
  do v1 ← mk_prod_prf v lhs e1, v2 ← mk_prod_prf v rhs e2, mk_app ``add_subst [v1, v2]
| v (node _ lhs rhs) `(%%e1 - %%e2) :=
  do v1 ← mk_prod_prf v lhs e1, v2 ← mk_prod_prf v rhs e2, mk_app ``sub_subst [v1, v2]
| v (node n lhs@(node ln _ _) rhs) `(%%e1 * %%e2) :=
  do tp ← infer_type e1, v1 ← mk_prod_prf ln lhs e1, v2 ← mk_prod_prf (v/ln) rhs e2,
     ln' ← tp.of_nat ln, vln' ← tp.of_nat (v/ln), v' ← tp.of_nat v,
     ntp ← to_expr ``(%%ln' * %%vln' = %%v'),
     (_, npf) ← solve_aux ntp `[norm_num, done],
     mk_app ``mul_subst [v1, v2, npf]
| v (node n lhs rhs@(node rn _ _)) `(%%e1 / %%e2) :=
  do tp ← infer_type e1, v1 ← mk_prod_prf (v/rn) lhs e1,
     rn' ← tp.of_nat rn, vrn' ← tp.of_nat (v/rn), n' ← tp.of_nat n, v' ← tp.of_nat v,
     ntp ← to_expr ``(%%rn' / %%e2 = 1),
     (_, npf) ← solve_aux ntp `[norm_num, done],
     ntp2 ← to_expr ``(%%vrn' * %%n' = %%v'),
     (_, npf2) ← solve_aux ntp2 `[norm_num, done],
     mk_app ``div_subst [v1, npf, npf2]
| v t `(-%%e) := do v' ← mk_prod_prf v t e, mk_app ``neg_subst [v']
| v _ e :=
  do tp ← infer_type e,
     v' ← tp.of_nat v,
     e' ← to_expr ``(%%v' * %%e),
     mk_app `eq.refl [e']

/--
Given `e`, a term with rational division, produces a natural number `n` and a proof of `n*e = e'`,
where `e'` has no division. Assumes "well-behaved" division.
-/
meta def derive (e : expr) : tactic (ℕ × expr) :=
let (n, t) := find_cancel_factor e in
prod.mk n <$> mk_prod_prf n t e <|>
  fail!"cancel_factors.derive failed to normalize {e}. Are you sure this is well-behaved division?"

/--
Given `e`, a term with rational divison, produces a natural number `n` and a proof of `e = e' / n`,
where `e'` has no divison. Assumes "well-behaved" division.
-/
meta def derive_div (e : expr) : tactic (ℕ × expr) :=
do (n, p) ← derive e,
   tp ← infer_type e,
   n' ← tp.of_nat n, tgt ← to_expr ``(%%n' ≠ 0),
   (_, pn) ← solve_aux tgt `[norm_num, done],
   infer_type p >>= trace, infer_type pn >>= trace,
   prod.mk n <$> mk_mapp ``cancel_factors_eq_div [none, none, n', none, none, p, pn]

/--
`find_comp_lemma e` arranges `e` in the form `lhs R rhs`, where `R ∈ {<, ≤, =}`, and returns
`lhs`, `rhs`, and the `cancel_factors` lemma corresponding to `R`.
-/
meta def find_comp_lemma : expr → option (expr × expr × name)
| `(%%a < %%b) := (a, b, ``cancel_factors_lt)
| `(%%a ≤ %%b) := (a, b, ``cancel_factors_le)
| `(%%a = %%b) := (a, b, ``cancel_factors_eq)
| `(%%a ≥ %%b) := (b, a, ``cancel_factors_le)
| `(%%a > %%b) := (b, a, ``cancel_factors_lt)
| _ := none

/--
`cancel_denominators_in_type h` assumes that `h` is of the form `lhs R rhs`,
where `R ∈ {<, ≤, =, ≥, >}`.
It produces an expression `h'` of the form `lhs' R rhs'` and a proof that `h = h'`.
Numeric denominators have been canceled in `lhs'` and `rhs'`.
-/
meta def cancel_denominators_in_type (h : expr) : tactic (expr × expr) :=
do some (lhs, rhs, lem) ← return $ find_comp_lemma h | fail "cannot kill factors",
   (al, lhs_p) ← derive lhs,
   (ar, rhs_p) ← derive rhs,
   let gcd := al.gcd ar,
   tp ← infer_type lhs,
   al ← tp.of_nat al,
   ar ← tp.of_nat ar,
   gcd ← tp.of_nat gcd,
   al_pos ← to_expr ``(0 < %%al),
   ar_pos ← to_expr ``(0 < %%ar),
   gcd_pos ← to_expr ``(0 < %%gcd),
   (_, al_pos) ← solve_aux al_pos `[norm_num, done],
   (_, ar_pos) ← solve_aux ar_pos `[norm_num, done],
   (_, gcd_pos) ← solve_aux gcd_pos `[norm_num, done],
   pf ← mk_app lem [lhs_p, rhs_p, al_pos, ar_pos, gcd_pos],
   pf_tp ← infer_type pf,
   return ((find_comp_lemma pf_tp).elim (default _) (prod.fst ∘ prod.snd), pf)

end cancel_factors

/-! ### Interactive version -/

setup_tactic_parser
open tactic expr cancel_factors

/--
`cancel_denoms` attempts to remove numerals from the denominators of fractions.
It works on propositions that are field-valued inequalities.

```lean
variables {α : Type} [linear_ordered_field α] (a b c : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c :=
begin
  cancel_denoms at h,
  exact h
end

example (h : a > 0) : a / 5 > 0 :=
begin
  cancel_denoms,
  exact h
end
```
-/
meta def tactic.interactive.cancel_denoms (l : parse location) : tactic unit :=
do locs ← l.get_locals,
   tactic.replace_at cancel_denominators_in_type locs l.include_goal >>= guardb
     <|> fail "failed to cancel any denominators",
   tactic.interactive.norm_num [simp_arg_type.symm_expr ``(mul_assoc)] l

add_tactic_doc
{ name := "cancel_denoms",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.cancel_denoms],
  tags := ["simplification"] }
