/-
Copyright (c) 2019 Patrick Massot All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Patrick Massot, Simon Hudon

A tactic pushing negations into an expression
-/

import algebra.order

open tactic expr

namespace push_neg
section

universe u
variable  {α : Sort u}
variables (p q : Prop)
variable  (s : α → Prop)

local attribute [instance, priority 10] classical.prop_decidable
theorem not_not_eq : (¬ ¬ p) = p := propext not_not
theorem not_and_eq : (¬ (p ∧ q)) = (p → ¬ q) := propext not_and
theorem not_or_eq : (¬ (p ∨ q)) = (¬ p ∧ ¬ q) := propext not_or_distrib
theorem not_forall_eq : (¬ ∀ x, s x) = (∃ x, ¬ s x) := propext not_forall
theorem not_exists_eq : (¬ ∃ x, s x) = (∀ x, ¬ s x) := propext not_exists
theorem not_implies_eq : (¬ (p → q)) = (p ∧ ¬ q) := propext not_imp

theorem classical.implies_iff_not_or : (p → q) ↔ (¬ p ∨ q) := imp_iff_not_or


theorem not_eq (a b : α) : (¬ a = b) ↔ (a ≠ b) := iff.rfl

variable  {β : Type u}
variable [linear_order β]
theorem not_le_eq (a b : β) : (¬ (a ≤ b)) = (b < a) := propext not_le
theorem not_lt_eq (a b : β) : (¬ (a < b)) = (b ≤ a) := propext not_lt
end

meta def whnf_reducible (e : expr) : tactic expr := whnf e reducible

private meta def transform_negation_step (e : expr) :
  tactic (option (expr × expr)) :=
do e ← whnf_reducible e,
   match e with
   | `(¬ %%ne) :=
      (do ne ← whnf_reducible ne,
      match ne with
      | `(¬ %%a)      := do pr ← mk_app ``not_not_eq [a],
                            return (some (a, pr))
      | `(%%a ∧ %%b)  := do pr ← mk_app ``not_and_eq [a, b],
                            return (some (`((%%a : Prop) → ¬ %%b), pr))
      | `(%%a ∨ %%b)  := do pr ← mk_app ``not_or_eq [a, b],
                            return (some (`(¬ %%a ∧ ¬ %%b), pr))
      | `(%%a ≤ %%b)  := do e ← to_expr ``(%%b < %%a),
                            pr ← mk_app ``not_le_eq [a, b],
                            return (some (e, pr))
      | `(%%a < %%b)  := do e ← to_expr ``(%%b ≤ %%a),
                            pr ← mk_app ``not_lt_eq [a, b],
                            return (some (e, pr))
      | `(Exists %%p) := do pr ← mk_app ``not_exists_eq [p],
                            e ← match p with
                                | (lam n bi typ bo) := do
                                    body ← mk_app ``not [bo],
                                    return (pi n bi typ body)
                                | _ := tactic.fail "Unexpected failure negating ∃"
                                end,
                            return (some (e, pr))
      | (pi n bi d p) := if p.has_var then do
                            pr ← mk_app ``not_forall_eq [lam n bi d p],
                            body ← mk_app ``not [p],
                            e ←  mk_app ``Exists [lam n bi d body],
                            return (some (e, pr))
                         else do
                            pr ← mk_app ``not_implies_eq [d, p],
                            `(%%_ = %%e') ← infer_type pr,
                            return (some (e', pr))
      | _             := return none
      end)
    | _        := return none
  end

private meta def transform_negation : expr → tactic (option (expr × expr))
| e :=
do (some (e', pr)) ← transform_negation_step e | return none,
   (some (e'', pr')) ← transform_negation e' | return (some (e', pr)),
   pr'' ← mk_eq_trans pr pr',
   return (some (e'', pr''))

meta def normalize_negations (t : expr) : tactic (expr × expr) :=
do (_, e, pr) ← simplify_top_down ()
                   (λ _, λ e, do
                       oepr ← transform_negation e,
                       match oepr with
                       | (some (e', pr)) := return ((), e', pr)
                       | none            := do pr ← mk_eq_refl e, return ((), e, pr)
                       end)
                   t { eta := ff },
   return (e, pr)

meta def push_neg_at_hyp (h : name) : tactic unit :=
do H ← get_local h,
   t ← infer_type H,
   (e, pr) ← normalize_negations t,
   replace_hyp H e pr,
   skip

meta def push_neg_at_goal : tactic unit :=
do H ← target,
   (e, pr) ← normalize_negations H,
   replace_target e pr
end push_neg

open interactive (parse loc.ns loc.wildcard)
open interactive.types (location texpr)
open lean.parser (tk ident many) interactive.loc
local postfix `?`:9001 := optional
local postfix *:9001 := many
open push_neg

/--
Push negations in the goal of some assumption.

For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Variables names are conserved.

This tactic pushes negations inside expressions. For instance, given an assumption
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε, ε > 0 ∧ ∀ δ, δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|),
```

(the pretty printer does *not* use the abreviations `∀ δ > 0` and `∃ ε > 0` but this issue
has nothing to do with `push_neg`).
Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can also use this tactic at the goal using `push_neg`,
at every assumption and the goal using `push_neg at *` or at selected assumptions and the goal
using say `push_neg at h h' ⊢` as usual.
-/
meta def tactic.interactive.push_neg : parse location → tactic unit
| (loc.ns loc_l) := loc_l.mmap'
                      (λ l, match l with
                            | some h := do push_neg_at_hyp h,
                                            try `[simp only [push_neg.not_eq] at h { eta := ff }]
                            | none   := do push_neg_at_goal,
                                            try `[simp only [push_neg.not_eq] { eta := ff }]
                            end)
| loc.wildcard := do
    push_neg_at_goal,
    local_context >>= mmap' (λ h, push_neg_at_hyp (local_pp_name h)) ,
    try `[simp only [push_neg.not_eq] at * { eta := ff }]

add_tactic_doc
{ name       := "push_neg",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.push_neg],
  tags       := ["logic"] }

lemma imp_of_not_imp_not (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) :=
λ h hP, classical.by_contradiction (λ h', h h' hP)

/-- Matches either an identifier "h" or a pair of identifiers "h with k" -/
meta def name_with_opt : lean.parser (name × option name) :=
prod.mk <$> ident <*> (some <$> (tk "with" >> ident) <|> return none)

/--
Transforms the goal into its contrapositive.

* `contrapose`     turns a goal `P → Q` into `¬ Q → ¬ P`
* `contrapose!`    turns a goal `P → Q` into `¬ Q → ¬ P` and pushes negations inside `P` and `Q`
  using `push_neg`
* `contrapose h`   first reverts the local assumption `h`, and then uses `contrapose` and `intro h`
* `contrapose! h`  first reverts the local assumption `h`, and then uses `contrapose!` and `intro h`
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis
-/
meta def tactic.interactive.contrapose (push : parse (tk "!" )?) : parse name_with_opt? → tactic unit
| (some (h, h')) := get_local h >>= revert >> tactic.interactive.contrapose none >> intro (h'.get_or_else h) >> skip
| none :=
  do `(%%P → %%Q) ← target | fail "The goal is not an implication, and you didn't specify an assumption",
  cp ← mk_mapp ``imp_of_not_imp_not [P, Q] <|> fail "contrapose only applies to nondependent arrows between props",
  apply cp,
  when push.is_some $ try (tactic.interactive.push_neg (loc.ns [none]))

add_tactic_doc
{ name       := "contrapose",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.contrapose],
  tags       := ["logic"] }
