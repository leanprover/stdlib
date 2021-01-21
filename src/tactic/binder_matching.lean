/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import meta.expr

/-!
# Matching expressions with leading binders

This module defines a family of tactics for matching expressions with leading Π
or λ binders, similar to Core's `mk_local_pis`. They all iterate over an
expression, processing one leading binder at a time. The bound variable is
replaced by either a fresh local constant or a fresh metavariable in the binder
body, 'opening' the binder. We then recurse into this new body. This scheme is
implemented by `tactic.open_binders` and `tactic.open_n_binders`.

Based on these general tactics, we define many variations of this recipe:

- `open_pis` opens all leading Π binders and replaces them with
  fresh local constants. This is defined in core.
- `open_lambdas` opens leading λ binders instead. Example:

  ```
  open_lambdas `(λ (x : X) (y : Y), f x y) =
    ([`(_fresh.1), `(_fresh.2)], `(f _fresh.1 _fresh.2))
  ```

  `_fresh.1` and `_fresh.2` are fresh local constants (with types `X` and `Y`,
  respectively). The second component of the pair is the lambda body with
  `x` replaced by `_fresh.1` and `y` replaced by `_fresh.2`.
- `open_pis_metas` opens all leading Π binders and replaces them with fresh
  metavariables (instead of local constants).
- `open_n_pis` opens only the first `n` leading Π binders and fails if there are
  not at least `n` leading binders. Example:

  ```
  open_n_pis `(Π (x : X) (y : Y), P x y) 1 =
    ([`(_fresh.1)], `(Π (y : Y), P _fresh.1 y))
  ```
- `open_lambdas_whnf` normalises the input expression each time before trying to
  match a binder. Example:

  ```
  open_lambdas_whnf `(let f := λ (x : X), g x y in f) =
    ([`(_fresh.1)], `(g _fresh.1 y))
  ```
- Any combination of these features is also provided, e.g.
  `open_n_lambdas_metas_whnf` to open `n` λ binders up to normalisation,
  replacing them with fresh metavariables.

The `open_*` functions are commonly used like this:

1. Open (some of) the binders of an expression `e`, producing local constants
   `lcs` and the 'body' `e'` of `e`.
2. Process `e'` in some way.
3. Reconstruct the binders using `tactic.pis` or `tactic.lambdas`, which
   Π/λ-bind the `lcs` in `e'`. This reverts the effect of `open_*`.
-/

namespace tactic

open expr

/--
`get_binder do_whnf pi_or_lambda e` matches `e` of the form `λ x, e'` or
`Π x, e`. Returns information about the leading binder (its name, `binder_info`,
type and body), or `none` if `e` does not start with a binder.

If `do_whnf = some (md, unfold_ginductive)`, then `e` is weak head normalised
with transparency `md` before matching on it. `unfold_ginductive` controls
whether constructors of generalised inductive data types are unfolded during
normalisation.

If `pi_or_lambda` is `tt`, we match a leading Π binder; otherwise a leading λ
binder.
-/
@[inline] meta def get_binder (do_whnf : option (transparency × bool))
  (pi_or_lambda : bool) (e : expr) :
  tactic (option (name × binder_info × expr × expr)) := do
  e ← do_whnf.elim (pure e) (λ p, whnf e p.1 p.2),
  pure $ if pi_or_lambda then match_pi e else match_lam e

/--
`mk_binder_replacement local_or_meta b` creates an expression that can be used
to replace the binder `b`. If `local_or_meta` is true, we create a fresh local
constant with `b`'s display name, `binder_info` and type; otherwise a fresh
metavariable with `b`'s type.
-/
meta def mk_binder_replacement (local_or_meta : bool) (b : binder) :
  tactic expr :=
if local_or_meta then mk_local' b.name b.info b.type else mk_meta_var b.type

/--
`open_binders` is a generalisation of functions like `open_pis`,
`mk_meta_lambdas` etc. `open_binders do_whnf pis_or_lamdas local_or_metas e`
proceeds as follows:

- Match a leading λ or Π binder using `get_binder do_whnf pis_or_lambdas`.
  See `get_binder` for details. Return `e` unchanged (and an empty list) if
  `e` does not start with a λ/Π.
- Construct a replacement for the bound variable using
  `mk_binder_replacement locals_or_metas`. See `mk_binder_replacement` for
  details. Replace the bound variable with this replacement in the binder body.
- Recurse into the binder body.

Returns the constructed replacement expressions and `e` without its leading
binders.
-/
meta def open_binders (do_whnf : option (transparency × bool))
  (pis_or_lambdas : bool) (locals_or_metas : bool) :
  expr → tactic (list expr × expr) :=
λ e, do
  some (name, bi, type, body) ← get_binder do_whnf pis_or_lambdas e
    | pure ([], e),
  replacement ← mk_binder_replacement locals_or_metas ⟨name, bi, type⟩,
  (rs, rest) ← open_binders (body.instantiate_var replacement),
  pure (replacement :: rs, rest)

/--
`open_n_binders do_whnf pis_or_lambdas local_or_metas e n` is like
`open_binders do_whnf pis_or_lambdas local_or_metas e`, but it matches exactly `n`
leading Π/λ binders of `e`. If `e` does not start with at least `n` Π/λ binders,
(after normalisation, if `do_whnf` is given), the tactic fails.
-/
meta def open_n_binders (do_whnf : option (transparency × bool))
  (pis_or_lambdas : bool) (locals_or_metas : bool) :
  expr → ℕ → tactic (list expr × expr)
| e 0 := pure ([], e)
| e (d + 1) := do
  some (name, bi, type, body) ← get_binder do_whnf pis_or_lambdas e | failed,
  replacement ← mk_binder_replacement locals_or_metas ⟨name, bi, type⟩,
  (rs, rest) ← open_n_binders (body.instantiate_var replacement) d,
  pure (replacement :: rs, rest)

/--
`open_pis e` instantiates all leading Π binders of `e` with fresh local
constants. Returns the local constants and the remainder of `e`. This is an
alias for `tactic.mk_local_pis`.
-/
meta abbreviation open_pis : expr → tactic (list expr × expr) :=
mk_local_pis

/--
`open_pis_metas e` instantiates all leading Π binders of `e` with fresh
metavariables. Returns the metavariables and the remainder of `e`. This is
`open_pis` but with metavariables instead of local constants.
-/
meta def open_pis_metas : expr → tactic (list expr × expr) :=
open_binders none tt ff

/--
`open_n_pis e n` instantiates the first `n` Π binders of `e` with fresh local
constants. Returns the local constants and the remainder of `e`. Fails if
`e` does not start with at least `n` Π binders. This is `open_pis` but limited
to `n` binders.
-/
meta def open_n_pis : expr → ℕ → tactic (list expr × expr) :=
open_n_binders none tt tt

/--
`open_n_pis_metas e n` instantiates the first `n` Π binders of `e` with fresh
metavariables. Returns the metavariables and the remainder of `e`. This is
`open_n_pis` but with metavariables instead of local constants.
-/
meta def open_n_pis_metas : expr → ℕ → tactic (list expr × expr) :=
open_n_binders none tt ff

/--
`open_pis_whnf e md unfold_ginductive` instantiates all leading Π binders of `e`
with fresh local constants. The leading Π binders of `e` are matched up to
normalisation with transparency `md`. `unfold_ginductive` determines whether
constructors of generalised inductive types are unfolded during normalisation.
This is `open_pis` up to normalisation.
-/
meta def open_pis_whnf (e : expr) (md := semireducible)
  (unfold_ginductive := tt) : tactic (list expr × expr) :=
open_binders (some (md, unfold_ginductive)) tt tt e

/--
`open_pis_metas_whnf e md unfold_ginductive` instantiates all leading Π binders
of `e` with fresh metavariables. The leading Π binders of `e` are matched up to
normalisation with transparency `md`. `unfold_ginductive` determines whether
constructors of generalised inductive types are unfolded during normalisation.
This is `open_pis_metas` up to normalisation.
-/
meta def open_pis_metas_whnf (e : expr) (md := semireducible)
  (unfold_ginductive := tt) : tactic (list expr × expr) :=
open_binders (some (md, unfold_ginductive)) tt ff e

/--
`open_n_pis_whnf e n md unfold_ginductive` instantiates the first `n` Π binders
of `e` with fresh local constants. The leading Π binders of `e` are matched up
to normalisation with transparency `md`. `unfold_ginductive` determines whether
constructors of generalised inductive types are unfolded during normalisation.
This is `open_pis_whnf` but restricted to `n` binders.
-/
meta def open_n_pis_whnf (e : expr) (n : ℕ) (md := semireducible)
  (unfold_ginductive := tt) : tactic (list expr × expr) :=
open_n_binders (some (md, unfold_ginductive)) tt tt e n

/--
`open_n_pis_metas_whnf e n md unfold_ginductive` instantiates the first `n` Π
binders of `e` with fresh metavariables. The leading Π binders of `e` are
matched up to normalisation with transparency `md`. `unfold_ginductive`
determines whether constructors of generalised inductive types are unfolded
during normalisation. This is `open_pis_metas_whnf` but restricted to `n`
binders.
-/
meta def open_n_pis_metas_whnf (e : expr) (n : ℕ) (md := semireducible)
  (unfold_ginductive := tt) : tactic (list expr × expr) :=
open_n_binders (some (md, unfold_ginductive)) tt ff e n

/--
`get_pi_binders e` instantiates all leading Π binders of `e` with fresh local
constants (like `open_pis`). Returns the remainder of `e` and information about
the binders that were instantiated (but not the new local constants). See also
`expr.pi_binders` (which produces open terms).
-/
meta def get_pi_binders (e : expr) : tactic (list binder × expr) := do
  (lcs, rest) ← open_pis e,
  pure (lcs.map to_binder, rest)

private meta def get_pi_binders_nondep_aux :
  ℕ → expr → tactic (list (ℕ × binder) × expr) :=
λ i e, do
  some (name, bi, type, body) ← get_binder none tt e | pure ([], e),
  replacement ← mk_local' name bi type,
  (rs, rest) ←
    get_pi_binders_nondep_aux (i + 1) (body.instantiate_var replacement),
  let rs' := if body.has_var then rs else (i, replacement.to_binder) :: rs,
  pure (rs', rest)

/--
`get_pi_binders_nondep e` instantiates all leading Π binders of `e` with fresh
local constants (like `open_pis`). Returns the remainder of `e` and information
about the *nondependent* binders that were instantiated (but not the new local
constants). A nondependent binder is one that does not appear later in the
expression. Also returns the index of each returned binder (starting at 0).
-/
meta def get_pi_binders_nondep : expr → tactic (list (ℕ × binder) × expr) :=
get_pi_binders_nondep_aux 0

/--
`open_lambdas e` instantiates all leading λ binders of `e` with fresh local
constants. Returns the new local constants and the remainder of `e`. This is
`open_pis` but for λ binders rather than Π binders.
-/
meta def open_lambdas : expr → tactic (list expr × expr) :=
open_binders none ff tt

/--
`open_lambdas_metas e` instantiates all leading λ binders of `e` with fresh
metavariables. Returns the new metavariables and the remainder of `e`. This is
`open_lambdas` but with metavariables instead of local constants.
-/
meta def open_lambdas_metas : expr → tactic (list expr × expr) :=
open_binders none ff ff

/--
`open_n_lambdas e n` instantiates the first `n` λ binders of `e` with fresh
local constants. Returns the new local constants and the remainder of `e`. Fails
if `e` does not start with at least `n` λ binders. This is `open_lambdas` but
restricted to the first `n` binders.
-/
meta def open_n_lambdas : expr → ℕ → tactic (list expr × expr) :=
open_n_binders none ff tt

/--
`open_n_lambdas_metas e n` instantiates the first `n` λ binders of `e` with
fresh metavariables. Returns the new metavariables and the remainder of `e`.
Fails if `e` does not start with at least `n` λ binders. This is
`open_lambdas_metas` but restricted to the first `n` binders.
-/
meta def open_n_lambdas_metas : expr → ℕ → tactic (list expr × expr) :=
open_n_binders none ff ff

/--
`open_lambdas_whnf e md unfold_ginductive` instantiates all leading λ binders of
`e` with fresh local constants. The leading λ binders of `e` are matched up to
normalisation with transparency `md`. `unfold_ginductive` determines whether
constructors of generalised inductive types are unfolded during normalisation.
This is `open_lambdas` up to normalisation.
-/
meta def open_lambdas_whnf (e : expr) (md := semireducible)
  (unfold_ginductive := tt) : tactic (list expr × expr) :=
open_binders (some (md, unfold_ginductive)) ff tt e

/--
`open_lambdas_metas_whnf e md unfold_ginductive` instantiates all leading λ
binders of `e` with fresh metavariables. The leading λ binders of `e` are
matched up to normalisation with transparency `md`. `unfold_ginductive`
determines whether constructors of generalised inductive types are unfolded
during normalisation. This is `open_lambdas_metas` up to normalisation.
-/
meta def open_lambdas_metas_whnf (e : expr) (md := semireducible)
  (unfold_ginductive := tt) : tactic (list expr × expr) :=
open_binders (some (md, unfold_ginductive)) ff ff e

/--
`open_n_lambdas_whnf e md unfold_ginductive` instantiates the first `n` λ
binders of `e` with fresh local constants. The λ binders are matched up to
normalisation with transparency `md`. `unfold_ginductive` determines whether
constructors of generalised inductive types are unfolded during normalisation.
Fails if `e` does not start with `n` λ binders (after normalisation). This is
`open_n_lambdas` up to normalisation.
-/
meta def open_n_lambdas_whnf (e : expr) (n : ℕ) (md := semireducible)
  (unfold_ginductive := tt) : tactic (list expr × expr) :=
open_n_binders (some (md, unfold_ginductive)) ff tt e n

/--
`open_n_lambdas_metas_whnf e md unfold_ginductive` instantiates the first `n` λ
binders of `e` with fresh metavariables. The λ binders are matched up to
normalisation with transparency `md`. `unfold_ginductive` determines whether
constructors of generalised inductive types are unfolded during normalisation.
Fails if `e` does not start with `n` λ binders (after normalisation). This is
`open_n_lambdas_metas` up to normalisation.
-/
meta def open_n_lambdas_metas_whnf (e : expr) (n : ℕ) (md := semireducible)
  (unfold_ginductive := tt) : tactic (list expr × expr) :=
open_n_binders (some (md, unfold_ginductive)) ff ff e n

/-!
## Special-purpose tactics

The following tactics are variations of the 'opening binders' theme that do not
quite fit in the above scheme.
-/

/--
`open_pis_whnf_dep e` instantiates all leading Π binders of `e` with fresh local
constants (like `tactic.open_pis`). It returns the remainder of the expression
and, for each binder, the corresponding local constant and whether the binder
was dependent.
-/
meta def open_pis_whnf_dep :
  expr → tactic (list (expr × bool) × expr) := λ e, do
  e' ← whnf e,
  match e' with
  | (pi n bi t rest) := do
    c ← mk_local' n bi t,
    let dep := rest.has_var,
    (cs, rest) ← open_pis_whnf_dep $ rest.instantiate_var c,
    pure ((c, dep) :: cs, rest)
  | _ := pure ([], e)
  end

/--
`open_n_pis_metas' e n` instantiates the first `n` leading Π binders of `e` with
fresh metavariables. It returns the remainder of the expression and, for each
binder, the corresponding metavariable, the name of the bound variable and the
binder's `binder_info`. Fails if `e` does not have at least `n` leading Π
binders.
-/
meta def open_n_pis_metas' :
  expr → ℕ → tactic (list (expr × name × binder_info) × expr)
| e 0 := pure ([], e)
| (pi nam bi t rest) (n + 1) := do
  m ← mk_meta_var t,
  (ms, rest) ← open_n_pis_metas' (rest.instantiate_var m) n,
  pure ((m, nam, bi) :: ms, rest)
| e (n + 1) := fail $
  to_fmt "expected an expression starting with a Π, but got: " ++ to_fmt e

end tactic
