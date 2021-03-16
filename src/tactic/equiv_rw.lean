/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.simp_result
import tactic.clear
import control.equiv_functor

/-!
# The `equiv_rw` tactic transports goals or hypotheses along equivalences.

The basic syntax is `equiv_rw e`, where `e : α ≃ β` is an equivalence.
This will try to replace occurrences of `α` in the goal with `β`, for example
transforming
* `⊢ α` to `⊢ β`,
* `⊢ option α` to `⊢ option β`
* `⊢ {a // P}` to `{b // P (⇑(equiv.symm e) b)}`

The tactic can also be used to rewrite hypotheses, using the syntax `equiv_rw e at h`.

## Implementation details

The main internal function is `equiv_rw_type e t`,
which attempts to turn an expression `e : α ≃ β` into a new equivalence with left hand side `t`.
As an example, with `t = option α`, it will generate `functor.map_equiv option e`.

This is achieved by generating a new synthetic goal `%%t ≃ _`,
and calling `solve_by_elim` with an appropriate set of congruence lemmas.
To avoid having to specify the relevant congruence lemmas by hand,
we mostly rely on `equiv_functor.map_equiv` and `bifunctor.map_equiv`
along with some structural congruence lemmas such as
* `equiv.arrow_congr'`,
* `equiv.subtype_equiv_of_subtype'`,
* `equiv.sigma_congr_left'`, and
* `equiv.Pi_congr_left'`.

The main `equiv_rw` function, when operating on the goal, simply generates a new equivalence `e'`
with left hand side matching the target, and calls `apply e'.inv_fun`.

When operating on a hypothesis `x : α`, we introduce a new fact `h : x = e.symm (e x)`,
revert this, and then attempt to `generalize`, replacing all occurrences of `e x` with a new constant `y`,
before `intro`ing and `subst`ing `h`, and renaming `y` back to `x`.

## Future improvements
In a future PR I anticipate that `derive equiv_functor` should work on many examples,
(internally using `transport`, which is in turn based on `equiv_rw`)
and we can incrementally bootstrap the strength of `equiv_rw`.

An ambitious project might be to add `equiv_rw!`,
a tactic which, when failing to find appropriate `equiv_functor` instances,
attempts to `derive` them on the spot.

For now `equiv_rw` is entirely based on `equiv`,
but the framework can readily be generalised to also work with other types of equivalences,
for example specific notations such as ring equivalence (`≃+*`),
or general categorical isomorphisms (`≅`).

This will allow us to transport across more general types of equivalences,
but this will wait for another subsequent PR.
-/

namespace tactic

/-- A list of lemmas used for constructing congruence equivalences. -/

-- Although this looks 'hard-coded', in fact the lemma `equiv_functor.map_equiv`
-- allows us to extend `equiv_rw` simply by constructing new instance so `equiv_functor`.

-- TODO: We should also use `category_theory.functorial` and `category_theory.hygienic` instances.
-- (example goal: we could rewrite along an isomorphism of rings (either as `R ≅ S` or `R ≃+* S`)
-- and turn an `x : mv_polynomial σ R` into an `x : mv_polynomial σ S`.).

meta def equiv_congr_lemmas : list (tactic expr) :=
[ `equiv.of_iff,
  -- TODO decide what to do with this; it's an equiv_bifunctor?
  `equiv.equiv_congr,
  -- The function arrow is technically a bifunctor `Typeᵒᵖ → Type → Type`,
  -- but the pattern matcher will never see this.
  `equiv.arrow_congr',
  -- Allow rewriting in subtypes:
  `equiv.subtype_equiv_of_subtype',
  -- Allow rewriting in the first component of a sigma-type:
  `equiv.sigma_congr_left',
  -- Allow rewriting ∀s:
  -- (You might think that repeated application of `equiv.forall_congr'
  -- would handle the higher arity cases, but unfortunately unification is not clever enough.)
  `equiv.forall₃_congr',
  `equiv.forall₂_congr',
  `equiv.forall_congr',
  -- Allow rewriting in argument of Pi types:
   `equiv.Pi_congr_left',
  -- Handles `sum` and `prod`, and many others:
  `bifunctor.map_equiv,
  -- Handles `list`, `option`, `unique`, and many others:
  `equiv_functor.map_equiv,
  -- We have to filter results to ensure we don't cheat and use exclusively `equiv.refl` and `iff.refl`!
  `equiv.refl,
  `iff.refl
  ].map (λ n, mk_const n)

declare_trace equiv_rw_type

/--
Configuration structure for `equiv_rw`.

* `max_depth` bounds the search depth for equivalences to rewrite along.
  The default value is 10.
  (e.g., if you're rewriting along `e : α ≃ β`, and `max_depth := 2`,
  you can rewrite `option (option α))` but not `option (option (option α))`.
-/
meta structure equiv_rw_cfg :=
(max_depth : ℕ := 10)

/--
Implementation of `equiv_rw_type`, using `solve_by_elim`.
Expects a goal of the form `t ≃ _`,
and tries to solve it using `eq : α ≃ β` and congruence lemmas.
-/
meta def equiv_rw_type_core (eq : expr) (cfg : equiv_rw_cfg) : tactic unit :=
do
  /-
    We now call `solve_by_elim` to try to generate the requested equivalence.
    There are a few subtleties!
    * We make sure that `eq` is the first lemma, so it is applied whenever possible.
    * In `equiv_congr_lemmas`, we put `equiv.refl` last so it is only used when it is not possible
      to descend further.
    * Since some congruence lemmas generate subgoals with `∀` statements,
      we use the `pre_apply` subtactic of `solve_by_elim` to preprocess each new goal with `intros`.
  -/
  solve_by_elim
  { use_symmetry := false,
    use_exfalso := false,
    lemma_thunks := some (pure eq :: equiv_congr_lemmas),
    ctx_thunk := pure [],
    max_depth := cfg.max_depth,
    -- Subgoals may contain function types,
    -- and we want to continue trying to construct equivalences after the binders.
    pre_apply := tactic.intros >> skip,
    backtrack_all_goals := tt,
    -- If solve_by_elim gets stuck, make sure it isn't because there's a later `≃` or `↔` goal
    -- that we should still attempt.
    discharger :=
      `[success_if_fail { match_target _ ≃ _ }] >> `[success_if_fail { match_target _ ↔ _ }] >>
      (`[show _ ≃ _] <|> `[show _ ↔ _]) <|>
      trace_if_enabled `equiv_rw_type "Failed, no congruence lemma applied!" >> failed,
    -- We use the `accept` tactic in `solve_by_elim` to provide tracing.
    accept := λ goals, lock_tactic_state (do
      when_tracing `equiv_rw_type (do
        goals.mmap pp >>= λ goals, trace format!"So far, we've built: {goals}"),
      done <|>
      when_tracing `equiv_rw_type (do
        gs ← get_goals,
        gs ← gs.mmap (λ g, infer_type g >>= pp),
        trace format!"Attempting to adapt to {gs}")) }

/--
`equiv_rw_type e t` rewrites the type `t` using the equivalence `e : α ≃ β`,
returning a new equivalence `t ≃ t'`.
-/
meta def equiv_rw_type (eqv : expr) (ty : expr) (cfg : equiv_rw_cfg) : tactic expr :=
do
  when_tracing `equiv_rw_type (do
    ty_pp ← pp ty,
    eqv_pp ← pp eqv,
    eqv_ty_pp ← infer_type eqv >>= pp,
    trace format!"Attempting to rewrite the type `{ty_pp}` using `{eqv_pp} : {eqv_ty_pp}`."),
  `(_ ≃ _) ← infer_type eqv | fail format!"{eqv} must be an `equiv`",
  -- We prepare a synthetic goal of type `(%%ty ≃ _)`, for some placeholder right hand side.
  equiv_ty ← to_expr ``(%%ty ≃ _),
  -- Now call `equiv_rw_type_core`.
  new_eqv ← prod.snd <$> (solve_aux equiv_ty $ equiv_rw_type_core eqv cfg),
  -- Check that we actually used the equivalence `eq`
  -- (`equiv_rw_type_core` will always find `equiv.refl`, but hopefully only after all other possibilities)
  new_eqv ← instantiate_mvars new_eqv,
  -- We previously had `guard (eqv.occurs new_eqv)` here, but `kdepends_on` is more reliable.
  kdepends_on new_eqv eqv >>= guardb <|> (do
    eqv_pp ← pp eqv,
    ty_pp ← pp ty,
    fail format!"Could not construct an equivalence from {eqv_pp} of the form: {ty_pp} ≃ _"),
  -- Finally we simplify the resulting equivalence,
  -- to compress away some `map_equiv equiv.refl` subexpressions.
  prod.fst <$> new_eqv.simp {fail_if_unchanged := ff}

mk_simp_attribute equiv_rw_simp "The simpset `equiv_rw_simp` is used by the tactic `equiv_rw` to
simplify applications of equivalences and their inverses."

attribute [equiv_rw_simp] equiv.symm_symm equiv.apply_symm_apply equiv.symm_apply_apply

/--
Attempt to replace the hypothesis with name `x`
by transporting it along the equivalence in `e : α ≃ β`.
-/
meta def equiv_rw_hyp (x : name) (e : expr) (cfg : equiv_rw_cfg := {}) : tactic unit :=
-- We call `dsimp_result` to perform the beta redex introduced by `revert`
dsimp_result (do
  x' ← get_local x,
  x_ty ← infer_type x',
  -- Adapt `e` to an equivalence with left-hand-side `x_ty`.
  e ← equiv_rw_type e x_ty cfg,
  eq ← to_expr ``(%%x' = equiv.symm %%e (equiv.to_fun %%e %%x')),
  prf ← to_expr ``((equiv.symm_apply_apply %%e %%x').symm),
  h ← note_anon eq prf,
  -- Revert the new hypothesis, so it is also part of the goal.
  revert h,
  ex ← to_expr ``(equiv.to_fun %%e %%x'),
  -- Now call `generalize`,
  -- attempting to replace all occurrences of `e x`,
  -- calling it for now `j : β`, with `k : x = e.symm j`.
  generalize ex (by apply_opt_param) transparency.none,
  -- Reintroduce `x` (now of type `b`), and the hypothesis `h`.
  intro x,
  h ← intro1,
  -- Finally, if we're working on properties, substitute along `h`, then do some cleanup,
  -- and if we're working on data, just throw out the old `x`.
  b ← target >>= is_prop,
  if b then do
    subst h,
    `[try { simp only with equiv_rw_simp }]
  else
    -- We may need to unfreeze `x` before we can `clear` it.
    unfreezing_hyp x' (clear' tt [x']) <|>
      fail format!"equiv_rw expected to be able to clear the original hypothesis {x}, but couldn't.",
  skip)
  {fail_if_unchanged := ff} tt -- call `dsimp_result` with `no_defaults := tt`.

/-- Rewrite the goal using an equiv `e`. -/
meta def equiv_rw_target (e : expr) (cfg : equiv_rw_cfg := {}) : tactic unit :=
do
  t ← target,
  e ← equiv_rw_type e t cfg,
  s ← to_expr ``(equiv.inv_fun %%e),
  tactic.eapply s,
  skip

end tactic

namespace tactic.interactive
open lean.parser
open interactive interactive.types
open tactic

local postfix `?`:9001 := optional

/--
`equiv_rw e at h`, where `h : α` is a hypothesis, and `e : α ≃ β`,
will attempt to transport `h` along `e`, producing a new hypothesis `h : β`,
with all occurrences of `h` in other hypotheses and the goal replaced with `e.symm h`.

`equiv_rw e` will attempt to transport the goal along an equivalence `e : α ≃ β`.
In its minimal form it replaces the goal `⊢ α` with `⊢ β` by calling `apply e.inv_fun`.

`equiv_rw` will also try rewriting under (equiv_)functors, so can turn
a hypothesis `h : list α` into `h : list β` or
a goal `⊢ unique α` into `⊢ unique β`.

The maximum search depth for rewriting in subexpressions is controlled by
`equiv_rw e {max_depth := n}`.
-/
meta def equiv_rw (e : parse texpr) (loc : parse $ (tk "at" *> ident)?) (cfg : equiv_rw_cfg := {}) : itactic :=
do e ← to_expr e,
   match loc with
   | (some hyp) := equiv_rw_hyp hyp e cfg
   | none := equiv_rw_target e cfg
   end

add_tactic_doc
{ name        := "equiv_rw",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.equiv_rw],
  tags        := ["rewriting", "equiv", "transport"] }

/--
Solve a goal of the form `t ≃ _`,
by constructing an equivalence from `e : α ≃ β`.
This is the same equivalence that `equiv_rw` would use to rewrite a term of type `t`.

A typical usage might be:
```
have e' : option α ≃ option β := by equiv_rw_type e
```
-/
meta def equiv_rw_type (e : parse texpr) (cfg : equiv_rw_cfg := {}) : itactic :=
do
 `(%%t ≃ _) ← target | fail "`equiv_rw_type` solves goals of the form `t ≃ _`.",
 e ← to_expr e,
 tactic.equiv_rw_type e t cfg >>= tactic.exact

add_tactic_doc
{ name        := "equiv_rw_type",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.equiv_rw_type],
  tags        := ["rewriting", "equiv", "transport"] }

end tactic.interactive
