/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen, Keeley Hoek, Leonardo de Moura

Converter monad for building simplifiers.
-/
import tactic.core
import tactic.converter.old_conv

namespace old_conv
meta def save_info (p : pos) : old_conv unit :=
λ r lhs, do
  ts ← tactic.read,
  -- TODO(Leo): include context
  tactic.save_info_thunk p (λ _, ts.format_expr lhs) >>
  return ⟨(), lhs, none⟩

meta def step {α : Type} (c : old_conv α) : old_conv unit :=
c >> return ()

meta def istep {α : Type} (line0 col0 line col : nat) (c : old_conv α) : old_conv unit :=
λ r lhs ts, (@scope_trace _ line col (λ _, (c >> return ()) r lhs ts)).clamp_pos line0 line col

meta def execute (c : old_conv unit) : tactic unit :=
conversion c

namespace interactive
open lean.parser
open interactive
open interactive.types

meta def itactic : Type :=
old_conv unit

meta def whnf : old_conv unit :=
old_conv.whnf

meta def dsimp : old_conv unit :=
old_conv.dsimp

meta def trace_state : old_conv unit :=
old_conv.trace_lhs

meta def change (p : parse texpr) : old_conv unit :=
old_conv.change p

meta def find (p : parse lean.parser.pexpr) (c : itactic) : old_conv unit :=
λ r lhs, do
  pat ← tactic.pexpr_to_pattern p,
  s   ← simp_lemmas.mk_default, -- to be able to use congruence lemmas @[congr]
  (found, new_lhs, pr) ←
     tactic.ext_simplify_core ff {zeta := ff, beta := ff, single_pass := tt, eta := ff, proj := ff} s
       (λ u, return u)
       (λ found s r p e, do
         guard (not found),
         matched ← (tactic.match_pattern pat e >> return tt) <|> return ff,
         guard matched,
         ⟨u, new_e, pr⟩ ← c r e,
         return (tt, new_e, pr, ff))
       (λ a s r p e, tactic.failed)
       r lhs,
  if not found then tactic.fail "find converter failed, pattern was not found"
  else return ⟨(), new_lhs, some pr⟩

end interactive
end old_conv

namespace conv
open tactic

meta def replace_lhs (tac : expr → tactic (expr × expr)) : conv unit :=
do (e, pf) ← lhs >>= tac, update_lhs e pf

-- Attempts to discharge the equality of the current `lhs` using `tac`,
-- moving to the next goal on success.
meta def discharge_eq_lhs (tac : tactic unit) : conv unit :=
do pf ← lock_tactic_state (do m ← lhs >>= mk_meta_var,
                              set_goals [m],
                              tac >> done,
                              instantiate_mvars m),
   congr,
   the_rhs ← rhs,
   update_lhs the_rhs pf,
   skip,
   skip

namespace interactive
open interactive
open tactic.interactive (rw_rules)

/-- The `conv` tactic provides a `conv` within a `conv`. It allows the user to return to a
previous state of the outer conv block to continue editing an expression without having to
start a new conv block. -/
protected meta def conv (t : conv.interactive.itactic) : conv unit :=
do transitivity,
   a :: rest ← get_goals,
   set_goals [a],
   t,
   all_goals reflexivity,
   set_goals rest

meta def erw (q : parse rw_rules) (cfg : rewrite_cfg := {md := semireducible}) : conv unit :=
rw q cfg

open interactive.types

/--
`guard_target t` fails if the target of the conv goal is not `t`.
We use this tactic for writing tests.
-/
meta def guard_target (p : parse texpr) : conv unit :=
do `(%%t = _) ← target, tactic.interactive.guard_expr_eq t p

/--
When using `rw` in `conv` mode on conditional equality lemmas, sometimes `⊢` goals can be
introduced which are impossible to close with `conv` tactics. Note that goals like `⊢ a = 0` will
be displayed by conv mode as `| a`, making the problem difficult to diagnose at times.

The `exact` conv tactic allows these to be closed, and is sufficient to allow re-entering tactic
mode with `exact by { ... }`.

Discussion of how to fix `rw` in the longer term can be found in
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Closing.20.60.E2.8A.A2.60.20goals.20in.20.60conv.60.20mode/near/212181256
-/
meta def exact := tactic.interactive.exact

end interactive
end conv

namespace tactic
namespace interactive
open lean
open lean.parser
open interactive
local postfix `?`:9001 := optional

meta def old_conv (c : old_conv.interactive.itactic) : tactic unit :=
do t ← target,
   (new_t, pr) ← c.to_tactic `eq t,
   replace_target new_t pr

meta def find (p : parse lean.parser.pexpr) (c : old_conv.interactive.itactic) : tactic unit :=
old_conv $ old_conv.interactive.find p c

meta def conv_lhs (loc : parse (tk "at" *> ident)?)
              (p : parse (tk "in" *> parser.pexpr)?)
              (c : conv.interactive.itactic) : tactic unit :=
conv loc p (conv.interactive.to_lhs >> c)

meta def conv_rhs (loc : parse (tk "at" *> ident)?)
              (p : parse (tk "in" *> parser.pexpr)?)
              (c : conv.interactive.itactic) : tactic unit :=
conv loc p (conv.interactive.to_rhs >> c)

end interactive
end tactic
