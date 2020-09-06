/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek
-/
import data.dlist.basic
import logic.function.basic
import control.basic
import meta.expr
import meta.rb_map
import data.bool
import tactic.binder_matching
import tactic.lean_core_docs
import tactic.interactive_expr
import system.io

universe variable u

attribute [derive [has_reflect, decidable_eq]] tactic.transparency

instance : has_lt pos :=
{ lt := λ x y, (x.line, x.column) < (y.line, y.column) }

namespace expr
open tactic

/-- Given an expr `α` representing a type with numeral structure,
`of_nat α n` creates the `α`-valued numeral expression corresponding to `n`. -/
protected meta def of_nat (α : expr) : ℕ → tactic expr :=
nat.binary_rec
  (tactic.mk_mapp ``has_zero.zero [some α, none])
  (λ b n tac, if n = 0 then mk_mapp ``has_one.one [some α, none] else
    do e ← tac, tactic.mk_app (cond b ``bit1 ``bit0) [e])

/-- Given an expr `α` representing a type with numeral structure,
`of_int α n` creates the `α`-valued numeral expression corresponding to `n`.
The output is either a numeral or the negation of a numeral. -/
protected meta def of_int (α : expr) : ℤ → tactic expr
| (n : ℕ) := expr.of_nat α n
| -[1+ n] := do
  e ← expr.of_nat α (n+1),
  tactic.mk_app ``has_neg.neg [e]

/-- Generates an expression of the form `∃(args), inner`. `args` is assumed to be a list of local
constants. When possible, `p ∧ q` is used instead of `∃(_ : p), q`. -/
meta def mk_exists_lst (args : list expr) (inner : expr) : tactic expr :=
args.mfoldr (λarg i:expr, do
    t ← infer_type arg,
    sort l ← infer_type t,
    return $ if arg.occurs i ∨ l ≠ level.zero
      then (const `Exists [l] : expr) t (i.lambdas [arg])
      else (const `and [] : expr) t i)
  inner

/-- `traverse f e` applies the monadic function `f` to the direct descendants of `e`. -/
meta def traverse {m : Type → Type u} [applicative m]
  {elab elab' : bool} (f : expr elab → m (expr elab')) :
  expr elab → m (expr elab')
 | (var v)  := pure $ var v
 | (sort l) := pure $ sort l
 | (const n ls) := pure $ const n ls
 | (mvar n n' e) := mvar n n' <$> f e
 | (local_const n n' bi e) := local_const n n' bi <$> f e
 | (app e₀ e₁) := app <$> f e₀ <*> f e₁
 | (lam n bi e₀ e₁) := lam n bi <$> f e₀ <*> f e₁
 | (pi n bi e₀ e₁) := pi n bi <$> f e₀ <*> f e₁
 | (elet n e₀ e₁ e₂) := elet n <$> f e₀ <*> f e₁ <*> f e₂
 | (macro mac es) := macro mac <$> list.traverse f es

/-- `mfoldl f a e` folds the monadic function `f` over the subterms of the expression `e`,
with initial value `a`. -/
meta def mfoldl {α : Type} {m} [monad m] (f : α → expr → m α) : α → expr → m α
| x e := prod.snd <$> (state_t.run (e.traverse $ λ e',
    (get >>= monad_lift ∘ flip f e' >>= put) $> e') x : m _)

/-- `kreplace e old new` replaces all occurrences of the expression `old` in `e`
with `new`. The occurrences of `old` in `e` are determined using keyed matching
with transparency `md`; see `kabstract` for details. If `unify` is true,
we may assign metavariables in `e` as we match subterms of `e` against `old`. -/
meta def kreplace (e old new : expr) (md := semireducible) (unify := tt)
  : tactic expr := do
  e ← kabstract e old md unify,
  pure $ e.instantiate_var new

end expr

namespace interaction_monad
open result

variables {σ : Type} {α : Type u}

/-- `get_state` returns the underlying state inside an interaction monad, from within that monad. -/
-- Note that this is a generalization of `tactic.read` in core.
meta def get_state : interaction_monad σ σ :=
λ state, success state state

/-- `set_state` sets the underlying state inside an interaction monad, from within that monad. -/
-- Note that this is a generalization of `tactic.write` in core.
meta def set_state (state : σ) : interaction_monad σ unit :=
λ _, success () state

/--
`run_with_state state tac` applies `tac` to the given state `state` and returns the result,
subsequently restoring the original state.
If `tac` fails, then `run_with_state` does too.
-/
meta def run_with_state (state : σ) (tac : interaction_monad σ α) : interaction_monad σ α :=
λ s, match tac state with
     | success val _      := success val s
     | exception fn pos _ := exception fn pos s
     end

end interaction_monad

namespace format

/-- `join' [a,b,c]` produces the format object `abc`.
It differs from `format.join` by using `format.nil` instead of `""` for the empty list. -/
meta def join' (xs : list format) : format :=
xs.foldl compose nil

/-- `intercalate x [a, b, c]` produces the format object `a.x.b.x.c`,
where `.` represents `format.join`. -/
meta def intercalate (x : format) : list format → format :=
join' ∘ list.intersperse x

/-- `soft_break` is similar to `line`. Whereas in `group (x ++ line ++ y ++ line ++ z)`
the result either fits on one line or in three, `x ++ soft_break ++ y ++ soft_break ++ z`
each line break is decided independently -/
meta def soft_break : format :=
group line

end format

section format
open format

/-- format a `list` by separating elements with `soft_break` instead of `line` -/
meta def list.to_line_wrap_format {α : Type u} [has_to_format α] : list α → format
| [] := to_fmt "[]"
| xs := to_fmt "[" ++ group (nest 1 $ intercalate ("," ++ soft_break) $ xs.map to_fmt) ++ to_fmt "]"

end format

namespace tactic
open function

/-- Private work function for `add_local_consts_as_local_hyps`: given
    `mappings : list (expr × expr)` corresponding to pairs `(var, hyp)` of variables and the local
    hypothesis created as a result and `(var :: rest) : list expr` of more local variables we
    examine `var` to see if it contains any other variables in `rest`. If it does, we put it to the
    back of the queue and recurse. If it does not, then we perform replacements inside the type of
    `var` using the `mappings`, create a new associate local hypothesis, add this to the list of
    mappings, and recurse. We are done once all local hypotheses have been processed.

    If the list of passed local constants have types which depend on one another (which can only
    happen by hand-crafting the `expr`s manually), this function will loop forever. -/
private meta def add_local_consts_as_local_hyps_aux
  : list (expr × expr) → list expr → tactic (list (expr × expr))
| mappings [] := return mappings
| mappings (var :: rest) := do
  /- Determine if `var` contains any local variables in the lift `rest`. -/
  let is_dependent := var.local_type.fold ff $ λ e n b,
    if b then b else e ∈ rest,

  /- If so, then skip it---add it to the end of the variable queue. -/
  if is_dependent then
    add_local_consts_as_local_hyps_aux mappings (rest ++ [var])
  else do
    /- Otherwise, replace all of the local constants referenced by the type of `var` with the
       respective new corresponding local hypotheses as recorded in the list `mappings`. -/
    let new_type := var.local_type.replace_subexprs mappings,

    /- Introduce a new local new local hypothesis `hyp` for `var`, with the correct type. -/
    hyp ← assertv var.local_pp_name new_type (var.local_const_set_type new_type),

    /- Process the next variable in the queue, with the mapping list updated to include the local
       hypothesis which we just created. -/
    add_local_consts_as_local_hyps_aux ((var, hyp) :: mappings) rest

/-- `add_local_consts_as_local_hyps vars` add the given list `vars` of `expr.local_const`s to the
    tactic state. This is harder than it sounds, since the list of local constants which we have
    been passed can have dependencies between their types.

    For example, suppose we have two local constants `n : ℕ` and `h : n = 3`. Then we cannot blindly
    add `h` as a local hypothesis, since we need the `n` to which it refers to be the `n` created as
    a new local hypothesis, not the old local constant `n` with the same name. Of course, these
    dependencies can be nested arbitrarily deep.

    If the list of passed local constants have types which depend on one another (which can only
    happen by hand-crafting the `expr`s manually), this function will loop forever. -/
meta def add_local_consts_as_local_hyps (vars : list expr) : tactic (list (expr × expr)) :=
/- The `list.reverse` below is a performance optimisation since the list of available variables
   reported by the system is often mostly the reverse of the order in which they are dependent. -/
add_local_consts_as_local_hyps_aux [] vars.reverse.erase_dup

private meta def get_expl_pi_arity_aux : expr → tactic nat
| (expr.pi n bi d b) :=
  do m     ← mk_fresh_name,
     let l := expr.local_const m n bi d,
     new_b ← whnf (expr.instantiate_var b l),
     r     ← get_expl_pi_arity_aux new_b,
     if bi = binder_info.default then
       return (r + 1)
     else
       return r
| e := return 0

/-- Compute the arity of explicit arguments of `type`. -/
meta def get_expl_pi_arity (type : expr) : tactic nat :=
whnf type >>= get_expl_pi_arity_aux

/-- Compute the arity of explicit arguments of `fn`'s type. -/
meta def get_expl_arity (fn : expr) : tactic nat :=
infer_type fn >>= get_expl_pi_arity

/--
Auxiliary function for `get_app_fn_args_whnf`.
-/
private meta def get_app_fn_args_whnf_aux (md : transparency)
  (unfold_ginductive : bool) : list expr → expr → tactic (expr × list expr) :=
λ args e, do
  (expr.app t u) ← whnf e md unfold_ginductive | pure (e, args),
  get_app_fn_args_whnf_aux (u :: args) t

/--
For `e = f x₁ ... xₙ`, `get_app_fn_args_whnf e` returns `(f, [x₁, ..., xₙ])`. `e`
is normalised as necessary; for example:

```
get_app_fn_args_whnf `(let f := g x in f y) = (`(g), [`(x), `(y)])
```
-/
meta def get_app_fn_args_whnf (e : expr) (md := semireducible)
  (unfold_ginductive := tt) : tactic (expr × list expr) :=
get_app_fn_args_whnf_aux md unfold_ginductive [] e

/--
`get_app_fn_whnf e md unfold_ginductive` is like `expr.get_app_fn e` but `e` is
normalised as necessary (with transparency `md`). `unfold_ginductive` controls
whether constructors of generalised inductive types are unfolded.
-/
meta def get_app_fn_whnf : expr → opt_param _ semireducible → opt_param _ tt → tactic expr
| e md unfold_ginductive := do
  (expr.app f _) ← whnf e md unfold_ginductive | pure e,
  get_app_fn_whnf f md

/-- `pis loc_consts f` is used to create a pi expression whose body is `f`.
`loc_consts` should be a list of local constants. The function will abstract these local
constants from `f` and bind them with pi binders.

For example, if `a, b` are local constants with types `Ta, Tb`,
``pis [a, b] `(f a b)`` will return the expression
`Π (a : Ta) (b : Tb), f a b`. -/
meta def pis : list expr → expr → tactic expr
| (e@(expr.local_const uniq pp info _) :: es) f := do
  t ← infer_type e,
  f' ← pis es f,
  pure $ expr.pi pp info t (expr.abstract_local f' uniq)
| _ f := pure f

/-- `lambdas loc_consts f` is used to create a lambda expression whose body is `f`.
`loc_consts` should be a list of local constants. The function will abstract these local
constants from `f` and bind them with lambda binders.

For example, if `a, b` are local constants with types `Ta, Tb`,
``lambdas [a, b] `(f a b)`` will return the expression
`λ (a : Ta) (b : Tb), f a b`. -/
meta def lambdas : list expr → expr → tactic expr
| (e@(expr.local_const uniq pp info _) :: es) f := do
  t ← infer_type e,
  f' ← lambdas es f,
  pure $ expr.lam pp info t (expr.abstract_local f' uniq)
| _ f := pure f

-- TODO: move to `declaration` namespace in `meta/expr.lean`
/-- `mk_theorem n ls t e` creates a theorem declaration with name `n`, universe parameters named
`ls`, type `t`, and body `e`. -/
meta def mk_theorem (n : name) (ls : list name) (t : expr) (e : expr) : declaration :=
declaration.thm n ls t (task.pure e)

/-- `add_theorem_by n ls type tac` uses `tac` to synthesize a term with type `type`, and adds this
to the environment as a theorem with name `n` and universe parameters `ls`. -/
meta def add_theorem_by (n : name) (ls : list name) (type : expr) (tac : tactic unit) :
  tactic expr :=
do ((), body) ← solve_aux type tac,
   body ← instantiate_mvars body,
   add_decl $ mk_theorem n ls type body,
   return $ expr.const n $ ls.map level.param

/-- `eval_expr' α e` attempts to evaluate the expression `e` in the type `α`.
This is a variant of `eval_expr` in core. Due to unexplained behavior in the VM, in rare
situations the latter will fail but the former will succeed. -/
meta def eval_expr' (α : Type*) [_inst_1 : reflected α] (e : expr) : tactic α :=
mk_app ``id [e] >>= eval_expr α

/-- `mk_fresh_name` returns identifiers starting with underscores,
which are not legal when emitted by tactic programs. `mk_user_fresh_name`
turns the useful source of random names provided by `mk_fresh_name` into
names which are usable by tactic programs.

The returned name has four components which are all strings. -/
meta def mk_user_fresh_name : tactic name :=
do nm ← mk_fresh_name,
   return $ `user__ ++ nm.pop_prefix.sanitize_name ++ `user__

/-- `has_attribute' attr_name decl_name` checks
whether `decl_name` exists and has attribute `attr_name`. -/
meta def has_attribute' (attr_name decl_name : name) : tactic bool :=
succeeds (has_attribute attr_name decl_name)

/-- Checks whether the name is a simp lemma -/
meta def is_simp_lemma : name → tactic bool :=
has_attribute' `simp

/-- Checks whether the name is an instance. -/
meta def is_instance : name → tactic bool :=
has_attribute' `instance

/-- `local_decls` returns a dictionary mapping names to their corresponding declarations.
Covers all declarations from the current file. -/
meta def local_decls : tactic (name_map declaration) :=
do e ← tactic.get_env,
   let xs := e.fold native.mk_rb_map
     (λ d s, if environment.in_current_file e d.to_name
             then s.insert d.to_name d else s),
   pure xs

/-- `get_decls_from` returns a dictionary mapping names to their
corresponding declarations.  Covers all declarations the files listed
in `fs`, with the current file listed as `none`.

The path of the file names is expected to be relative to
the root of the project (i.e. the location of `leanpkg.toml` when it
is present); e.g. `"src/tactic/core.lean"`

Possible issue: `get_decls_from` uses `get_cwd`, the current working
directory, which may not always point at the root of the project.
It would work better if it searched for the root directory or,
better yet, if Lean exposed its path information.
-/
meta def get_decls_from (fs : list (option string)) : tactic (name_map declaration) :=
do root ← unsafe_run_io $ io.env.get_cwd,
   let fs := fs.map (option.map $ λ path, root ++ "/" ++ path),
   err ← unsafe_run_io $ (fs.filter_map id).mfilter $ (<$>) bnot ∘ io.fs.file_exists,
   guard (err = []) <|> fail format!"File not found: {err}",
   e ← tactic.get_env,
   let xs := e.fold native.mk_rb_map
     (λ d s,
       let source := e.decl_olean d.to_name in
       if source ∈ fs ∧ (source = none → e.in_current_file d.to_name)
       then s.insert d.to_name d else s),
   pure xs

/-- If `{nm}_{n}` doesn't exist in the environment, returns that, otherwise tries `{nm}_{n+1}` -/
meta def get_unused_decl_name_aux (e : environment) (nm : name) : ℕ → tactic name | n :=
let nm' := nm.append_suffix ("_" ++ to_string n) in
if e.contains nm' then get_unused_decl_name_aux (n+1) else return nm'

/-- Return a name which doesn't already exist in the environment. If `nm` doesn't exist, it
returns that, otherwise it tries `nm_2`, `nm_3`, ... -/
meta def get_unused_decl_name (nm : name) : tactic name :=
get_env >>= λ e, if e.contains nm then get_unused_decl_name_aux e nm 2 else return nm

/--
Returns a pair `(e, t)`, where `e ← mk_const d.to_name`, and `t = d.type`
but with universe params updated to match the fresh universe metavariables in `e`.

This should have the same effect as just
```lean
do e ← mk_const d.to_name,
   t ← infer_type e,
   return (e, t)
```
but is hopefully faster.
-/
meta def decl_mk_const (d : declaration) : tactic (expr × expr) :=
do subst ← d.univ_params.mmap $ λ u, prod.mk u <$> mk_meta_univ,
   let e : expr := expr.const d.to_name (prod.snd <$> subst),
   return (e, d.type.instantiate_univ_params subst)

/--
Replace every universe metavariable in an expression with a universe parameter.

(This is useful when making new declarations.)
-/
meta def replace_univ_metas_with_univ_params (e : expr) : tactic expr :=
do
  e.list_univ_meta_vars.enum.mmap (λ n, do
    let n' := (`u).append_suffix ("_" ++ to_string (n.1+1)),
    unify (expr.sort (level.mvar n.2)) (expr.sort (level.param n'))),
  instantiate_mvars e

/-- `mk_local n` creates a dummy local variable with name `n`.
The type of this local constant is a constant with name `n`, so it is very unlikely to be
a meaningful expression. -/
meta def mk_local (n : name) : expr :=
expr.local_const n n binder_info.default (expr.const n [])

/-- `mk_psigma [x,y,z]`, with `[x,y,z]` list of local constants of types `x : tx`,
`y : ty x` and `z : tz x y`, creates an expression of sigma type:
`⟨x,y,z⟩ : Σ' (x : tx) (y : ty x), tz x y`.
-/
meta def mk_psigma : list expr → tactic expr
| [] := mk_const ``punit
| [x@(expr.local_const _ _ _ _)] := pure x
| (x@(expr.local_const _ _ _ _) :: xs) :=
  do y ← mk_psigma xs,
     α ← infer_type x,
     β ← infer_type y,
     t ← lambdas [x] β >>= instantiate_mvars,
     r ← mk_mapp ``psigma.mk [α,t],
     pure $ r x y
| _ := fail "mk_psigma expects a list of local constants"

/-- `elim_gen_prod n e _ ns` with `e` an expression of type `psigma _`, applies `cases` on `e` `n`
times and uses `ns` to name the resulting variables. Returns a triple: list of new variables,
remaining term and unused variable names.
-/
meta def elim_gen_prod : nat → expr → list expr → list name → tactic (list expr × expr × list name)
| 0       e hs ns := return (hs.reverse, e, ns)
| (n + 1) e hs ns := do
  t ← infer_type e,
  if t.is_app_of `eq then return (hs.reverse, e, ns)
  else do
    [(_, [h, h'], _)] ← cases_core e (ns.take 1),
    elim_gen_prod n h' (h :: hs) (ns.drop 1)

private meta def elim_gen_sum_aux : nat → expr → list expr → tactic (list expr × expr)
| 0       e hs := return (hs, e)
| (n + 1) e hs := do
  [(_, [h], _), (_, [h'], _)] ← induction e [],
  swap,
  elim_gen_sum_aux n h' (h::hs)

/-- `elim_gen_sum n e` applies cases on `e` `n` times. `e` is assumed to be a local constant whose
type is a (nested) sum `⊕`. Returns the list of local constants representing the components of `e`.
-/
meta def elim_gen_sum (n : nat) (e : expr) : tactic (list expr) := do
  (hs, h') ← elim_gen_sum_aux n e [],
  gs ← get_goals,
  set_goals $ (gs.take (n+1)).reverse ++ gs.drop (n+1),
  return $ hs.reverse ++ [h']

/-- Given `elab_def`, a tactic to solve the current goal,
`extract_def n trusted elab_def` will create an auxiliary definition named `n` and use it
to close the goal. If `trusted` is false, it will be a meta definition. -/
meta def extract_def (n : name) (trusted : bool) (elab_def : tactic unit) : tactic unit :=
do cxt ← list.map expr.to_implicit_local_const <$> local_context,
   t ← target,
   (eqns,d) ← solve_aux t elab_def,
   d ← instantiate_mvars d,
   t' ← pis cxt t,
   d' ← lambdas cxt d,
   let univ := t'.collect_univ_params,
   add_decl $ declaration.defn n univ t' d' (reducibility_hints.regular 1 tt) trusted,
   applyc n

/-- Attempts to close the goal with `dec_trivial`. -/
meta def exact_dec_trivial : tactic unit := `[exact dec_trivial]

/-- Runs a tactic for a result, reverting the state after completion. -/
meta def retrieve {α} (tac : tactic α) : tactic α :=
λ s, result.cases_on (tac s)
 (λ a s', result.success a s)
 result.exception

/-- Runs a tactic for a result, reverting the state after completion or error. -/
meta def retrieve' {α} (tac : tactic α) : tactic α :=
λ s, result.cases_on (tac s)
 (λ a s', result.success a s)
 (λ msg pos s', result.exception msg pos s)

/-- Repeat a tactic at least once, calling it recursively on all subgoals,
until it fails. This tactic fails if the first invocation fails. -/
meta def repeat1 (t : tactic unit) : tactic unit := t; repeat t

/-- `iterate_range m n t`: Repeat the given tactic at least `m` times and
at most `n` times or until `t` fails. Fails if `t` does not run at least `m` times. -/
meta def iterate_range : ℕ → ℕ → tactic unit → tactic unit
| 0 0     t := skip
| 0 (n+1) t := try (t >> iterate_range 0 n t)
| (m+1) n t := t >> iterate_range m (n-1) t

/--
Given a tactic `tac` that takes an expression
and returns a new expression and a proof of equality,
use that tactic to change the type of the hypotheses listed in `hs`,
as well as the goal if `tgt = tt`.

Returns `tt` if any types were successfully changed.
-/
meta def replace_at (tac : expr → tactic (expr × expr)) (hs : list expr) (tgt : bool) :
  tactic bool :=
do to_remove ← hs.mfilter $ λ h, do {
    h_type ← infer_type h,
    succeeds $ do
      (new_h_type, pr) ← tac h_type,
      assert h.local_pp_name new_h_type,
      mk_eq_mp pr h >>= tactic.exact },
  goal_simplified ← succeeds $ do {
    guard tgt,
    (new_t, pr) ← target >>= tac,
    replace_target new_t pr },
  to_remove.mmap' (λ h, try (clear h)),
  return (¬ to_remove.empty ∨ goal_simplified)

/-- `revert_after e` reverts all local constants after local constant `e`. -/
meta def revert_after (e : expr) : tactic ℕ := do
  l ← local_context,
  [pos] ← return $ l.indexes_of e | pp e >>= λ s, fail format!"No such local constant {s}",
  let l := l.drop pos.succ, -- all local hypotheses after `e`
  revert_lst l

/-- `revert_target_deps` reverts all local constants on which the target depends (recursively).
  Returns the number of local constants that have been reverted. -/
meta def revert_target_deps : tactic ℕ :=
do tgt ← target,
   ctx ← local_context,
   l ← ctx.mfilter (kdepends_on tgt),
   n ← revert_lst l,
   if l = [] then return n
     else do m ← revert_target_deps, return (m + n)

/-- `generalize' e n` generalizes the target with respect to `e`. It creates a new local constant
with name `n` of the same type as `e` and replaces all occurrences of `e` by `n`.

`generalize'` is similar to `generalize` but also succeeds when `e` does not occur in the
goal, in which case it just calls `assert`.
In contrast to `generalize` it already introduces the generalized variable. -/
meta def generalize' (e : expr) (n : name) : tactic expr :=
(generalize e n >> intro n) <|> note n none e

/--
`intron_no_renames n` calls `intro` `n` times, using the pretty-printing name
provided by the binder to name the new local constant.
Unlike `intron`, it does not rename introduced constants if the names shadow existing constants.
-/
meta def intron_no_renames : ℕ → tactic unit
| 0 := pure ()
| (n+1) := do
  expr.pi pp_n _ _ _ ← target,
  intro pp_n,
  intron_no_renames n

/-!
### Various tactics related to local definitions (local constants of the form `x : α := t`)

We call `t` the value of `x`.
-/

/-- `local_def_value e` returns the value of the expression `e`, assuming that `e` has been defined
  locally using a `let` expression. Otherwise it fails. -/
meta def local_def_value (e : expr) : tactic expr :=
pp e >>= λ s, -- running `pp` here, because we cannot access it in the `type_context` monad.
tactic.unsafe.type_context.run $ do
  lctx <- tactic.unsafe.type_context.get_local_context,
  some ldecl <- return $ lctx.get_local_decl e.local_uniq_name |
    tactic.unsafe.type_context.fail format!"No such hypothesis {s}.",
  some let_val <- return ldecl.value |
    tactic.unsafe.type_context.fail format!"Variable {e} is not a local definition.",
  return let_val

/-- `revert_deps e` reverts all the hypotheses that depend on one of the local
constants `e`, including the local definitions that have `e` in their definition.
This fixes a bug in `revert_kdeps` that does not revert local definitions for which `e` only
appears in the definition. -/
/- We cannot implement it as `revert e >> intro1`, because that would change the local constant in
the context. -/
meta def revert_deps (e : expr) : tactic ℕ := do
  n ← revert_kdeps e,
  l ← local_context,
  [pos] ← return $ l.indexes_of e,
  let l := l.drop pos.succ, -- local hypotheses after `e`
  ls ← l.mfilter $ λ e', try_core (local_def_value e') >>= λ o, return $ o.elim ff $ λ e'',
    e''.has_local_constant e,
  n' ← revert_lst ls,
  return $ n + n'

/-- `is_local_def e` succeeds when `e` is a local definition (a local constant of the form
`e : α := t`) and otherwise fails. -/
meta def is_local_def (e : expr) : tactic unit :=
retrieve $ do revert e, expr.elet _ _ _ _ ← target, skip

/-- like `split_on_p p xs`, `partition_local_deps_aux vs xs acc` searches for matches in `xs`
(using membership to `vs` instead of a predicate) and breaks `xs` when matches are found.
whereas `split_on_p p xs` removes the matches, `partition_local_deps_aux vs xs acc` includes
them in the following partition. Also, `partition_local_deps_aux vs xs acc` discards the partition
running up to the first match. -/
private def partition_local_deps_aux {α} [decidable_eq α] (vs : list α) : list α → list α → list (list α)
| [] acc := [acc.reverse]
| (l :: ls) acc :=
  if l ∈ vs then acc.reverse :: partition_local_deps_aux ls [l]
  else partition_local_deps_aux ls (l :: acc)

/-- `partition_local_deps vs`, with `vs` a list of local constants,
reorders `vs` in the order they appear in the local context together
with the variables that follow them. If local context is `[a,b,c,d,e,f]`,
and that we call `partition_local_deps [d,b]`, we get `[[d,e,f], [b,c]]`.
The head of each list is one of the variables given as a parameter. -/
meta def partition_local_deps (vs : list expr) : tactic (list (list expr)) :=
do ls ← local_context,
   pure (partition_local_deps_aux vs ls []).tail.reverse

/-- `clear_value [e₀, e₁, e₂, ...]` clears the body of the local definitions `e₀`, `e₁`, `e₂`, ... changing them into regular
hypotheses. A hypothesis `e : α := t` is changed to `e : α`. The order of locals `e₀`, `e₁`, `e₂` does not
matter as a permutation will be chosen so as to preserve type correctness.
This tactic is called `clearbody` in Coq. -/
meta def clear_value (vs : list expr) : tactic unit := do
  ls ← partition_local_deps vs,
  ls.mmap' $ λ vs, do
  { revert_lst vs,
    (expr.elet v t d b) ← target | fail format!"Cannot clear the body of {vs.head}. It is not a local definition.",
    let e := expr.pi v binder_info.default t b,
    type_check e <|> fail format!"Cannot clear the body of {vs.head}. The resulting goal is not type correct.",
    g ← mk_meta_var e,
    h ← note `h none g,
    tactic.exact $ h d,
    gs ← get_goals,
    set_goals $ g :: gs },
  ls.reverse.mmap' $ λ vs, intro_lst $ vs.map expr.local_pp_name

/-- A variant of `simplify_bottom_up`. Given a tactic `post` for rewriting subexpressions,
`simp_bottom_up post e` tries to rewrite `e` starting at the leaf nodes. Returns the resulting
expression and a proof of equality. -/
meta def simp_bottom_up' (post : expr → tactic (expr × expr)) (e : expr) (cfg : simp_config := {}) :
  tactic (expr × expr) :=
prod.snd <$> simplify_bottom_up () (λ _, (<$>) (prod.mk ()) ∘ post) e cfg

/-- Caches unary type classes on a type `α : Type.{univ}`. -/
meta structure instance_cache :=
(α : expr)
(univ : level)
(inst : name_map expr)

/-- Creates an `instance_cache` for the type `α`. -/
meta def mk_instance_cache (α : expr) : tactic instance_cache :=
do u ← mk_meta_univ,
   infer_type α >>= unify (expr.sort (level.succ u)),
   u ← get_univ_assignment u,
   return ⟨α, u, mk_name_map⟩

namespace instance_cache

/-- If `n` is the name of a type class with one parameter, `get c n` tries to find an instance of
`n c.α` by checking the cache `c`. If there is no entry in the cache, it tries to find the instance
via type class resolution, and updates the cache. -/
meta def get (c : instance_cache) (n : name) : tactic (instance_cache × expr) :=
match c.inst.find n with
| some i := return (c, i)
| none := do e ← mk_app n [c.α] >>= mk_instance,
  return (⟨c.α, c.univ, c.inst.insert n e⟩, e)
end

open expr
/-- If `e` is a `pi` expression that binds an instance-implicit variable of type `n`,
`append_typeclasses e c l` searches `c` for an instance `p` of type `n` and returns `p :: l`. -/
meta def append_typeclasses : expr → instance_cache → list expr →
  tactic (instance_cache × list expr)
| (pi _ binder_info.inst_implicit (app (const n _) (var _)) body) c l :=
  do (c, p) ← c.get n, return (c, p :: l)
| _ c l := return (c, l)

/-- Creates the application `n c.α p l`, where `p` is a type class instance found in the cache `c`.
-/
meta def mk_app (c : instance_cache) (n : name) (l : list expr) : tactic (instance_cache × expr) :=
do d ← get_decl n,
   (c, l) ← append_typeclasses d.type.binding_body c l,
   return (c, (expr.const n [c.univ]).mk_app (c.α :: l))

/-- `c.of_nat n` creates the `c.α`-valued numeral expression corresponding to `n`. -/
protected meta def of_nat (c : instance_cache) (n : ℕ) : tactic (instance_cache × expr) :=
if n = 0 then c.mk_app ``has_zero.zero [] else do
  (c, ai) ← c.get ``has_add,
  (c, oi) ← c.get ``has_one,
  (c, one) ← c.mk_app ``has_one.one [],
  return (c, n.binary_rec one $ λ b n e,
    if n = 0 then one else
    cond b
      ((expr.const ``bit1 [c.univ]).mk_app [c.α, oi, ai, e])
      ((expr.const ``bit0 [c.univ]).mk_app [c.α, ai, e]))

/-- `c.of_int n` creates the `c.α`-valued numeral expression corresponding to `n`.
The output is either a numeral or the negation of a numeral. -/
protected meta def of_int (c : instance_cache) : ℤ → tactic (instance_cache × expr)
| (n : ℕ) := c.of_nat n
| -[1+ n] := do
  (c, e) ← c.of_nat (n+1),
  c.mk_app ``has_neg.neg [e]

end instance_cache

/-- A variation on `assert` where a (possibly incomplete)
proof of the assertion is provided as a parameter.

``(h,gs) ← local_proof `h p tac`` creates a local `h : p` and
use `tac` to (partially) construct a proof for it. `gs` is the
list of remaining goals in the proof of `h`.

The benefits over assert are:
- unlike with ``h ← assert `h p, tac`` , `h` cannot be used by `tac`;
- when `tac` does not complete the proof of `h`, returning the list
  of goals allows one to write a tactic using `h` and with the confidence
  that a proof will not boil over to goals left over from the proof of `h`,
  unlike what would be the case when using `tactic.swap`.
-/
meta def local_proof (h : name) (p : expr) (tac₀ : tactic unit) :
  tactic (expr × list expr) :=
focus1 $
do h' ← assert h p,
   [g₀,g₁] ← get_goals,
   set_goals [g₀], tac₀,
   gs ← get_goals,
   set_goals [g₁],
   return (h', gs)

/-- `var_names e` returns a list of the unique names of the initial pi bindings in `e`. -/
meta def var_names : expr → list name
| (expr.pi n _ _ b) := n :: var_names b
| _ := []

/-- When `struct_n` is the name of a structure type,
`subobject_names struct_n` returns two lists of names `(instances, fields)`.
The names in `instances` are the projections from `struct_n` to the structures that it extends
(assuming it was defined with `old_structure_cmd false`).
The names in `fields` are the standard fields of `struct_n`. -/
meta def subobject_names (struct_n : name) : tactic (list name × list name) :=
do env ← get_env,
   c ← match env.constructors_of struct_n with
       | [c] := pure c
       | [] :=
         if env.is_inductive struct_n
           then fail format!"{struct_n} does not have constructors"
           else fail format!"{struct_n} is not an inductive type"
       | _ := fail "too many constructors"
       end,
   vs  ← var_names <$> (mk_const c >>= infer_type),
   fields ← env.structure_fields struct_n,
   return $ fields.partition (λ fn, ↑("_" ++ fn.to_string) ∈ vs)

private meta def expanded_field_list' : name → tactic (dlist $ name × name) | struct_n :=
do (so,fs) ← subobject_names struct_n,
   ts ← so.mmap (λ n, do
     (_, e) ← mk_const (n.update_prefix struct_n) >>= infer_type >>= open_pis,
     expanded_field_list' $ e.get_app_fn.const_name),
   return $ dlist.join ts ++ dlist.of_list (fs.map $ prod.mk struct_n)
open functor function

/-- `expanded_field_list struct_n` produces a list of the names of the fields of the structure
named `struct_n`. These are returned as pairs of names `(prefix, name)`, where the full name
of the projection is `prefix.name`.

`struct_n` cannot be a synonym for a `structure`, it must be itself a `structure` -/
meta def expanded_field_list (struct_n : name) : tactic (list $ name × name) :=
dlist.to_list <$> expanded_field_list' struct_n

/--
Return a list of all type classes which can be instantiated
for the given expression.
-/
meta def get_classes (e : expr) : tactic (list name) :=
attribute.get_instances `class >>= list.mfilter (λ n,
  succeeds $ mk_app n [e] >>= mk_instance)

/--
  Finds an instance of an implication `cond → tgt`.
  Returns a pair of a local constant `e` of type `cond`, and an instance of `tgt` that can mention `e`.
  The local constant `e` is added as an hypothesis to the tactic state, but should not be used, since
  it has been "proven" by a metavariable.
-/
meta def mk_conditional_instance (cond tgt : expr) : tactic (expr × expr) := do
f ← mk_meta_var cond,
e ← assertv `c cond f, swap,
reset_instance_cache,
inst ← mk_instance tgt,
return (e, inst)

open nat

/-- Create a list of `n` fresh metavariables. -/
meta def mk_mvar_list : ℕ → tactic (list expr)
| 0 := pure []
| (succ n) := (::) <$> mk_mvar <*> mk_mvar_list n

/-- Returns the only goal, or fails if there isn't just one goal. -/
meta def get_goal : tactic expr :=
do gs ← get_goals,
   match gs with
   | [a] := return a
   | []  := fail "there are no goals"
   | _   := fail "there are too many goals"
   end

/-- `iterate_at_most_on_all_goals n t`: repeat the given tactic at most `n` times on all goals,
or until it fails. Always succeeds. -/
meta def iterate_at_most_on_all_goals : nat → tactic unit → tactic unit
| 0        tac := trace "maximal iterations reached"
| (succ n) tac := tactic.all_goals' $ (do tac, iterate_at_most_on_all_goals n tac) <|> skip

/-- `iterate_at_most_on_subgoals n t`: repeat the tactic `t` at most `n` times on the first
goal and on all subgoals thus produced, or until it fails. Fails iff `t` fails on
current goal. -/
meta def iterate_at_most_on_subgoals : nat → tactic unit → tactic unit
| 0        tac := trace "maximal iterations reached"
| (succ n) tac := focus1 (do tac, iterate_at_most_on_all_goals n tac)

/-- This makes sure that the execution of the tactic does not change the tactic state.
This can be helpful while using rewrite, apply, or expr munging.
Remember to instantiate your metavariables before you're done! -/
meta def lock_tactic_state {α} (t : tactic α) : tactic α
| s := match t s with
       | result.success a s' := result.success a s
       | result.exception msg pos s' := result.exception msg pos s
end

/--
`apply_list l`, for `l : list (tactic expr)`,
tries to apply the lemmas generated by the tactics in `l` on the first goal, and
fail if none succeeds.
-/
meta def apply_list_expr (opt : apply_cfg) : list (tactic expr) → tactic unit
| []     := fail "no matching rule"
| (h::t) := (do e ← h, interactive.concat_tags (apply e opt)) <|> apply_list_expr t

/--
Constructs a list of `tactic expr` given a list of p-expressions, as follows:
- if the p-expression is the name of a theorem, use `i_to_expr_for_apply` on it
- if the p-expression is a user attribute, add all the theorems with this attribute
  to the list.

We need to return a list of `tactic expr`, rather than just `expr`, because these expressions
will be repeatedly applied against goals, and we need to ensure that metavariables don't get stuck.
-/
meta def build_list_expr_for_apply : list pexpr → tactic (list (tactic expr))
| [] := return []
| (h::t) := do
  tail ← build_list_expr_for_apply t,
  a ← i_to_expr_for_apply h,
  (do l ← attribute.get_instances (expr.const_name a),
      m ← l.mmap (λ n, _root_.to_pexpr <$> mk_const n),
      -- We reverse the list of lemmas marked with an attribute,
      -- on the assumption that lemmas proved earlier are more often applicable
      -- than lemmas proved later. This is a performance optimization.
      build_list_expr_for_apply (m.reverse ++ t))
  <|> return ((i_to_expr_for_apply h) :: tail)

/--`apply_rules hs n`: apply the list of rules `hs` (given as pexpr) and `assumption` on the
first goal and the resulting subgoals, iteratively, at most `n` times.

Unlike `solve_by_elim`, `apply_rules` does not do any backtracking, and just greedily applies
a lemma from the list until it can't.
 -/
meta def apply_rules (hs : list pexpr) (n : nat) (opt : apply_cfg) : tactic unit :=
do l ← lock_tactic_state $ build_list_expr_for_apply hs,
   iterate_at_most_on_subgoals n (assumption <|> apply_list_expr opt l)

/-- `replace h p` elaborates the pexpr `p`, clears the existing hypothesis named `h` from the local
context, and adds a new hypothesis named `h`. The type of this hypothesis is the type of `p`.
Fails if there is nothing named `h` in the local context. -/
meta def replace (h : name) (p : pexpr) : tactic unit :=
do h' ← get_local h,
   p ← to_expr p,
   note h none p,
   clear h'

/-- Auxiliary function for `iff_mp` and `iff_mpr`. Takes a name, which should be either `` `iff.mp``
or `` `iff.mpr``. If the passed expression is an iterated function type eventually producing an
`iff`, returns an expression with the `iff` converted to either the forwards or backwards
implication, as requested. -/
meta def mk_iff_mp_app (iffmp : name) : expr → (nat → expr) → option expr
| (expr.pi n bi e t) f := expr.lam n bi e <$> mk_iff_mp_app t (λ n, f (n+1) (expr.var n))
| `(%%a ↔ %%b) f := some $ @expr.const tt iffmp [] a b (f 0)
| _ f := none

/-- `iff_mp_core e ty` assumes that `ty` is the type of `e`.
If `ty` has the shape `Π ..., A ↔ B`, returns an expression whose type is `Π ..., A → B`. -/
meta def iff_mp_core (e ty: expr) : option expr :=
mk_iff_mp_app `iff.mp ty (λ_, e)

/-- `iff_mpr_core e ty` assumes that `ty` is the type of `e`.
If `ty` has the shape `Π ..., A ↔ B`, returns an expression whose type is `Π ..., B → A`. -/
meta def iff_mpr_core (e ty: expr) : option expr :=
mk_iff_mp_app `iff.mpr ty (λ_, e)

/-- Given an expression whose type is (a possibly iterated function producing) an `iff`,
create the expression which is the forward implication. -/
meta def iff_mp (e : expr) : tactic expr :=
do t ← infer_type e,
   iff_mp_core e t <|> fail "Target theorem must have the form `Π x y z, a ↔ b`"

/-- Given an expression whose type is (a possibly iterated function producing) an `iff`,
create the expression which is the reverse implication. -/
meta def iff_mpr (e : expr) : tactic expr :=
do t ← infer_type e,
   iff_mpr_core e t <|> fail "Target theorem must have the form `Π x y z, a ↔ b`"

/--
Attempts to apply `e`, and if that fails, if `e` is an `iff`,
try applying both directions separately.
-/
meta def apply_iff (e : expr) : tactic (list (name × expr)) :=
let ap e := tactic.apply e {new_goals := new_goals.non_dep_only} in
ap e <|> (iff_mp e >>= ap) <|> (iff_mpr e >>= ap)

/--
Configuration options for `apply_any`:
* `use_symmetry`: if `apply_any` fails to apply any lemma, call `symmetry` and try again.
* `use_exfalso`: if `apply_any` fails to apply any lemma, call `exfalso` and try again.
* `apply`: specify an alternative to `tactic.apply`; usually `apply := tactic.eapply`.
-/
meta structure apply_any_opt extends apply_cfg :=
(use_symmetry : bool := tt)
(use_exfalso : bool := tt)

/--
This is a version of `apply_any` that takes a list of `tactic expr`s instead of `expr`s,
and evaluates these as thunks before trying to apply them.

We need to do this to avoid metavariables getting stuck during subsequent rounds of `apply`.
-/
meta def apply_any_thunk
  (lemmas : list (tactic expr))
  (opt : apply_any_opt := {})
  (tac : tactic unit := skip)
  (on_success : expr → tactic unit := (λ _, skip))
  (on_failure : tactic unit := skip) : tactic unit :=
do
  let modes := [skip]
    ++ (if opt.use_symmetry then [symmetry] else [])
    ++ (if opt.use_exfalso then [exfalso] else []),
  modes.any_of (λ m, do m,
    lemmas.any_of (λ H, H >>= (λ e, do apply e opt.to_apply_cfg, on_success e, tac))) <|>
  (on_failure >> fail "apply_any tactic failed; no lemma could be applied")

/--
`apply_any lemmas` tries to apply one of the list `lemmas` to the current goal.

`apply_any lemmas opt` allows control over how lemmas are applied.
`opt` has fields:
* `use_symmetry`: if no lemma applies, call `symmetry` and try again. (Defaults to `tt`.)
* `use_exfalso`: if no lemma applies, call `exfalso` and try again. (Defaults to `tt`.)
* `apply`: use a tactic other than `tactic.apply` (e.g. `tactic.fapply` or `tactic.eapply`).

`apply_any lemmas tac` calls the tactic `tac` after a successful application.
Defaults to `skip`. This is used, for example, by `solve_by_elim` to arrange
recursive invocations of `apply_any`.
-/
meta def apply_any
  (lemmas : list expr)
  (opt : apply_any_opt := {})
  (tac : tactic unit := skip) : tactic unit :=
apply_any_thunk (lemmas.map pure) opt tac

/-- Try to apply a hypothesis from the local context to the goal. -/
meta def apply_assumption : tactic unit :=
local_context >>= apply_any

/-- `change_core e none` is equivalent to `change e`. It tries to change the goal to `e` and fails
if this is not a definitional equality.

`change_core e (some h)` assumes `h` is a local constant, and tries to change the type of `h` to `e`
by reverting `h`, changing the goal, and reintroducing hypotheses. -/
meta def change_core (e : expr) : option expr → tactic unit
| none     := tactic.change e
| (some h) :=
  do num_reverted : ℕ ← revert h,
     expr.pi n bi d b ← target,
     tactic.change $ expr.pi n bi e b,
     intron num_reverted

/--
`change_with_at olde newe hyp` replaces occurences of `olde` with `newe` at hypothesis `hyp`,
assuming `olde` and `newe` are defeq when elaborated.
-/
meta def change_with_at (olde newe : pexpr) (hyp : name) : tactic unit :=
do h ← get_local hyp,
   tp ← infer_type h,
   olde ← to_expr olde, newe ← to_expr newe,
   let repl_tp := tp.replace (λ a n, if a = olde then some newe else none),
   when (repl_tp ≠ tp) $ change_core repl_tp (some h)

/-- Returns a list of all metavariables in the current partial proof. This can differ from
the list of goals, since the goals can be manually edited. -/
meta def metavariables : tactic (list expr) :=
expr.list_meta_vars <$> result

/--
`sorry_if_contains_sorry` will solve any goal already containing `sorry` in its type with `sorry`,
and fail otherwise.
-/
meta def sorry_if_contains_sorry : tactic unit :=
do
  g ← target,
  guard g.contains_sorry <|> fail "goal does not contain `sorrry`",
  tactic.admit

/-- Fail if the target contains a metavariable. -/
meta def no_mvars_in_target : tactic unit :=
expr.has_meta_var <$> target >>= guardb ∘ bnot

/-- Succeeds only if the current goal is a proposition. -/
meta def propositional_goal : tactic unit :=
do g :: _ ← get_goals,
   is_proof g >>= guardb

/-- Succeeds only if we can construct an instance showing the
  current goal is a subsingleton type. -/
meta def subsingleton_goal : tactic unit :=
do g :: _ ← get_goals,
   ty ← infer_type g >>= instantiate_mvars,
   to_expr ``(subsingleton %%ty) >>= mk_instance >> skip

/--
Succeeds only if the current goal is "terminal",
in the sense that no other goals depend on it
(except possibly through shared metavariables; see `independent_goal`).
-/
meta def terminal_goal : tactic unit :=
propositional_goal <|> subsingleton_goal <|>
do g₀ :: _ ← get_goals,
   mvars ← (λ L, list.erase L g₀) <$> metavariables,
   mvars.mmap' $ λ g, do
     t ← infer_type g >>= instantiate_mvars,
     d ← kdepends_on t g₀,
     monad.whenb d $
       pp t >>= λ s, fail ("The current goal is not terminal: " ++ s.to_string ++ " depends on it.")

/--
Succeeds only if the current goal is "independent", in the sense
that no other goals depend on it, even through shared meta-variables.
-/
meta def independent_goal : tactic unit :=
no_mvars_in_target >> terminal_goal

/-- `triv'` tries to close the first goal with the proof `trivial : true`. Unlike `triv`,
it only unfolds reducible definitions, so it sometimes fails faster. -/
meta def triv' : tactic unit := do c ← mk_const `trivial, exact c reducible

variable {α : Type}

/-- Apply a tactic as many times as possible, collecting the results in a list.
Fail if the tactic does not succeed at least once. -/
meta def iterate1 (t : tactic α) : tactic (list α) :=
do r ← decorate_ex "iterate1 failed: tactic did not succeed" t,
   L ← iterate t,
   return (r :: L)

/-- Introduces one or more variables and returns the new local constants.
Fails if `intro` cannot be applied. -/
meta def intros1 : tactic (list expr) :=
iterate1 intro1

/-- Run a tactic "under binders", by running `intros` before, and `revert` afterwards. -/
meta def under_binders {α : Type} (t : tactic α) : tactic α :=
do
  v ← intros,
  r ← t,
  revert_lst v,
  return r

namespace interactive
/-- Run a tactic "under binders", by running `intros` before, and `revert` afterwards. -/
meta def under_binders (i : itactic) : itactic := tactic.under_binders i
end interactive

/-- `successes` invokes each tactic in turn, returning the list of successful results. -/
meta def successes (tactics : list (tactic α)) : tactic (list α) :=
list.filter_map id <$> monad.sequence (tactics.map (λ t, try_core t))

/--
Try all the tactics in a list, each time starting at the original `tactic_state`,
returning the list of successful results,
and reverting to the original `tactic_state`.
-/
-- Note this is not the same as `successes`, which keeps track of the evolving `tactic_state`.
meta def try_all {α : Type} (tactics : list (tactic α)) : tactic (list α) :=
λ s, result.success
(tactics.map $
λ t : tactic α,
  match t s with
  | result.success a s' := [a]
  | _ := []
  end).join s

/--
Try all the tactics in a list, each time starting at the original `tactic_state`,
returning the list of successful results sorted by
the value produced by a subsequent execution of the `sort_by` tactic,
and reverting to the original `tactic_state`.
-/
meta def try_all_sorted {α : Type} (tactics : list (tactic α)) (sort_by : tactic ℕ := num_goals) :
  tactic (list (α × ℕ)) :=
λ s, result.success
((tactics.map $
λ t : tactic α,
  match (do a ← t, n ← sort_by, return (a, n)) s with
  | result.success a s' := [a]
  | _ := []
  end).join.qsort (λ p q : α × ℕ, p.2 < q.2)) s

/-- Return target after instantiating metavars and whnf. -/
private meta def target' : tactic expr :=
target >>= instantiate_mvars >>= whnf

/--
Just like `split`, `fsplit` applies the constructor when the type of the target is
an inductive data type with one constructor.
However it does not reorder goals or invoke `auto_param` tactics.
-/
-- FIXME check if we can remove `auto_param := ff`
meta def fsplit : tactic unit :=
do [c] ← target' >>= get_constructors_for |
     fail "fsplit tactic failed, target is not an inductive datatype with only one constructor",
   mk_const c >>= λ e, apply e {new_goals := new_goals.all, auto_param := ff} >> skip

run_cmd add_interactive [`fsplit]

add_tactic_doc
{ name                     := "fsplit",
  category                 := doc_category.tactic,
  decl_names               := [`tactic.interactive.fsplit],
  tags                     := ["logic", "goal management"] }

/-- Calls `injection` on each hypothesis, and then, for each hypothesis on which `injection`
succeeds, clears the old hypothesis. -/
meta def injections_and_clear : tactic unit :=
do l ← local_context,
   results ← successes $ l.map $ λ e, injection e >> clear e,
   when (results.empty) (fail "could not use `injection` then `clear` on any hypothesis")

run_cmd add_interactive [`injections_and_clear]

add_tactic_doc
{ name                     := "injections_and_clear",
  category                 := doc_category.tactic,
  decl_names               := [`tactic.interactive.injections_and_clear],
  tags                     := ["context management"] }

/-- Calls `cases` on every local hypothesis, succeeding if
it succeeds on at least one hypothesis. -/
meta def case_bash : tactic unit :=
do l ← local_context,
   r ← successes (l.reverse.map (λ h, cases h >> skip)),
   when (r.empty) failed

/--
`note_anon t v`, given a proof `v : t`,
adds `h : t` to the current context, where the name `h` is fresh.

`note_anon none v` will infer the type `t` from `v`.
-/
-- While `note` provides a default value for `t`, it doesn't seem this could ever be used.
meta def note_anon (t : option expr) (v : expr) : tactic expr :=
do h ← get_unused_name `h none,
   note h t v

/-- `find_local t` returns a local constant with type t, or fails if none exists. -/
meta def find_local (t : pexpr) : tactic expr :=
do t' ← to_expr t,
   (prod.snd <$> solve_aux t' assumption >>= instantiate_mvars) <|>
     fail format!"No hypothesis found of the form: {t'}"

/-- `dependent_pose_core l`: introduce dependent hypotheses, where the proofs depend on the values
of the previous local constants. `l` is a list of local constants and their values. -/
meta def dependent_pose_core (l : list (expr × expr)) : tactic unit := do
  let lc := l.map prod.fst,
  let lm := l.map (λ⟨l, v⟩, (l.local_uniq_name, v)),
  old::other_goals ← get_goals,
  t ← infer_type old,
  new_goal ← mk_meta_var (t.pis lc),
  set_goals (old :: new_goal :: other_goals),
  exact ((new_goal.mk_app lc).instantiate_locals lm),
  return ()

/--
Instantiates metavariables that appear in the current goal.
-/
meta def instantiate_mvars_in_target : tactic unit :=
target >>= instantiate_mvars >>= change

/--
Instantiates metavariables in all goals.
-/
meta def instantiate_mvars_in_goals : tactic unit :=
all_goals' $ instantiate_mvars_in_target

/-- Protect the declaration `n` -/
meta def mk_protected (n : name) : tactic unit :=
do env ← get_env, set_env (env.mk_protected n)

end tactic

namespace lean.parser
open tactic interaction_monad

/-- `emit_command_here str` behaves as if the string `str` were placed as a user command at the
current line. -/
meta def emit_command_here (str : string) : lean.parser string :=
do (_, left) ← with_input command_like str,
   return left

/-- `emit_code_here str` behaves as if the string `str` were placed at the current location in
source code. -/
meta def emit_code_here : string → lean.parser unit
| str := do left ← emit_command_here str,
            if left.length = 0 then return ()
            else emit_code_here left

/-- `get_current_namespace` returns the current namespace (it could be `name.anonymous`).

This function deserves a C++ implementation in core lean, and will fail if it is not called from
the body of a command (i.e. anywhere else that the `lean.parser` monad can be invoked). -/
meta def get_current_namespace : lean.parser name :=
do n ← tactic.mk_user_fresh_name,
   emit_code_here $ sformat!"def {n} := ()",
   nfull ← tactic.resolve_constant n,
   return $ nfull.get_nth_prefix n.components.length

/-- `get_variables` returns a list of existing variable names, along with their types and binder
info. -/
meta def get_variables : lean.parser (list (name × binder_info × expr)) :=
list.map expr.get_local_const_kind <$> list_available_include_vars

/-- `get_included_variables` returns those variables `v` returned by `get_variables` which have been
"included" by an `include v` statement and are not (yet) `omit`ed. -/
meta def get_included_variables : lean.parser (list (name × binder_info × expr)) :=
do ns ← list_include_var_names,
   list.filter (λ v, v.1 ∈ ns) <$> get_variables

/-- From the `lean.parser` monad, synthesize a `tactic_state` which includes all of the local
variables referenced in `es : list pexpr`, and those variables which have been `include`ed in the
local context---precisely those variables which would be ambiently accessible if we were in a
tactic-mode block where the goals had types `es.mmap to_expr`, for example.

Returns a new `ts : tactic_state` with these local variables added, and
`mappings : list (expr × expr)`, for which pairs `(var, hyp)` correspond to an existing variable
`var` and the local hypothesis `hyp` which was added to the tactic state `ts` as a result. -/
meta def synthesize_tactic_state_with_variables_as_hyps (es : list pexpr)
  : lean.parser (tactic_state × list (expr × expr)) :=
do /- First, in order to get `to_expr e` to resolve declared `variables`, we add all of the
      declared variables to a fake `tactic_state`, and perform the resolution. At the end,
      `to_expr e` has done the work of determining which variables were actually referenced, which
      we then obtain from `fe` via `expr.list_local_consts` (which, importantly, is not defined for
      `pexpr`s). -/
   vars ← list_available_include_vars,
   fake_es ← lean.parser.of_tactic $ lock_tactic_state $ do {
     /- Note that `add_local_consts_as_local_hyps` returns the mappings it generated, but we discard
        them on this first pass. (We return the mappings generated by our second invocation of this
        function below.) -/
     add_local_consts_as_local_hyps vars,
     es.mmap to_expr
   },

   /- Now calculate lists of a) the explicitly `include`ed variables and b) the variables which were
      referenced in `e` when it was resolved to `fake_e`.

      It is important that we include variables of the kind a) because we want `simp` to have access
      to declared local instances, and it is important that we only restrict to variables of kind a)
      and b) together since we do not to recognise a hypothesis which is posited as a `variable`
      in the environment but not referenced in the `pexpr` we were passed.

      One use case for this behaviour is running `simp` on the passed `pexpr`, since we do not want
      simp to use arbitrary hypotheses which were declared as `variables` in the local environment
      but not referenced in the expression to simplify (as one would be expect generally in tactic
      mode). -/
   included_vars ← list_include_var_names,
   let referenced_vars := list.join $ fake_es.map $ λ e, e.list_local_consts.map expr.local_pp_name,

   /- Look up the explicit `included_vars` and the `referenced_vars` (which have appeared in the
      `pexpr` list which we were passed.)  -/
   let directly_included_vars := vars.filter $ λ var,
     (var.local_pp_name ∈ included_vars) ∨ (var.local_pp_name ∈ referenced_vars),

   /- Inflate the list `directly_included_vars` to include those variables which are "implicitly
      included" by virtue of reference to one or multiple others. For example, given
      `variables (n : ℕ) [prime n] [ih : even n]`, a reference to `n` implies that the typeclass
      instance `prime n` should be included, but `ih : even n` should not. -/
   let all_implicitly_included_vars :=
     expr.all_implicitly_included_variables vars directly_included_vars,

   /- Capture a tactic state where both of these kinds of variables have been added as local
      hypotheses, and resolve `e` against this state with `to_expr`, this time for real. -/
   lean.parser.of_tactic $ do {
      mappings ← add_local_consts_as_local_hyps all_implicitly_included_vars,
      ts ← get_state,
      return (ts, mappings)
   }

end lean.parser

namespace tactic

variables {α : Type}

/--
Hole command used to fill in a structure's field when specifying an instance.

In the following:

```lean
instance : monad id :=
{! !}
```

invoking the hole command "Instance Stub" ("Generate a skeleton for the structure under
construction.") produces:

```lean
instance : monad id :=
{ map := _,
  map_const := _,
  pure := _,
  seq := _,
  seq_left := _,
  seq_right := _,
  bind := _ }
```
-/
@[hole_command] meta def instance_stub : hole_command :=
{ name := "Instance Stub",
  descr := "Generate a skeleton for the structure under construction.",
  action := λ _,
  do tgt ← target >>= whnf,
     let cl := tgt.get_app_fn.const_name,
     env ← get_env,
     fs ← expanded_field_list cl,
     let fs := fs.map prod.snd,
     let fs := format.intercalate (",\n  " : format) $ fs.map (λ fn, format!"{fn} := _"),
     let out := format.to_string format!"{{ {fs} }",
     return [(out,"")] }

add_tactic_doc
{ name                     := "instance_stub",
  category                 := doc_category.hole_cmd,
  decl_names               := [`tactic.instance_stub],
  tags                     := ["instances"] }

/-- Like `resolve_name` except when the list of goals is
empty. In that situation `resolve_name` fails whereas
`resolve_name'` simply proceeds on a dummy goal -/
meta def resolve_name' (n : name) : tactic pexpr :=
do [] ← get_goals | resolve_name n,
   g ← mk_mvar,
   set_goals [g],
   resolve_name n <* set_goals []

private meta def strip_prefix' (n : name) : list string → name → tactic name
| s name.anonymous := pure $ s.foldl (flip name.mk_string) name.anonymous
| s (name.mk_string a p) :=
  do let n' := s.foldl (flip name.mk_string) name.anonymous,
     do { n'' ← tactic.resolve_constant n',
          if n'' = n
            then pure n'
            else strip_prefix' (a :: s) p }
     <|> strip_prefix' (a :: s) p
| s n@(name.mk_numeral a p) := pure $ s.foldl (flip name.mk_string) n

/-- Strips unnecessary prefixes from a name, e.g. if a namespace is open. -/
meta def strip_prefix : name → tactic name
| n@(name.mk_string a a_1) :=
  if (`_private).is_prefix_of n
    then let n' := n.update_prefix name.anonymous in
            n' <$ resolve_name' n' <|> pure n
    else strip_prefix' n [a] a_1
| n := pure n

/-- Used to format return strings for the hole commands `match_stub` and `eqn_stub`. -/
meta def mk_patterns (t : expr) : tactic (list format) :=
do let cl := t.get_app_fn.const_name,
   env ← get_env,
   let fs := env.constructors_of cl,
   fs.mmap $ λ f,
     do { (vs,_) ← mk_const f >>= infer_type >>= open_pis,
          let vs := vs.filter (λ v, v.is_default_local),
          vs ← vs.mmap (λ v,
            do v' ← get_unused_name v.local_pp_name,
               pose v' none `(()),
               pure v' ),
          vs.mmap' $ λ v, get_local v >>= clear,
          let args := list.intersperse (" " : format) $ vs.map to_fmt,
          f ← strip_prefix f,
          if args.empty
            then pure $ format!"| {f} := _\n"
            else pure format!"| ({f} {format.join args}) := _\n" }

/--
Hole command used to generate a `match` expression.

In the following:

```lean
meta def foo (e : expr) : tactic unit :=
{! e !}
```

invoking hole command "Match Stub" ("Generate a list of equations for a `match` expression")
produces:

```lean
meta def foo (e : expr) : tactic unit :=
match e with
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
end
```
-/
@[hole_command] meta def match_stub : hole_command :=
{ name := "Match Stub",
  descr := "Generate a list of equations for a `match` expression.",
  action := λ es,
  do [e] ← pure es | fail "expecting one expression",
     e ← to_expr e,
     t ← infer_type e >>= whnf,
     fs ← mk_patterns t,
     e ← pp e,
     let out := format.to_string format!"match {e} with\n{format.join fs}end\n",
     return [(out,"")] }

add_tactic_doc
{ name                     := "Match Stub",
  category                 := doc_category.hole_cmd,
  decl_names               := [`tactic.match_stub],
  tags                     := ["pattern matching"] }

/--
Invoking hole command "Equations Stub" ("Generate a list of equations for a recursive definition")
in the following:

```lean
meta def foo : {! expr → tactic unit !} -- `:=` is omitted
```

produces:

```lean
meta def foo : expr → tactic unit
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
```

A similar result can be obtained by invoking "Equations Stub" on the following:

```lean
meta def foo : expr → tactic unit := -- do not forget to write `:=`!!
{! !}
```

```lean
meta def foo : expr → tactic unit := -- don't forget to erase `:=`!!
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
```

-/
@[hole_command] meta def eqn_stub : hole_command :=
{ name := "Equations Stub",
  descr := "Generate a list of equations for a recursive definition.",
  action := λ es,
  do t ← match es with
         | [t] := to_expr t
         | [] := target
         | _ := fail "expecting one type"
         end,
     e ← whnf t,
     (v :: _,_) ← open_pis e | fail "expecting a Pi-type",
     t' ← infer_type v,
     fs ← mk_patterns t',
     t ← pp t,
     let out :=
         if es.empty then
           format.to_string format!"-- do not forget to erase `:=`!!\n{format.join fs}"
           else format.to_string format!"{t}\n{format.join fs}",
     return [(out,"")] }

add_tactic_doc
{ name                     := "Equations Stub",
  category                 := doc_category.hole_cmd,
  decl_names               := [`tactic.eqn_stub],
  tags                     := ["pattern matching"] }

/--
This command lists the constructors that can be used to satisfy the expected type.

Invoking "List Constructors" ("Show the list of constructors of the expected type")
in the following hole:

```lean
def foo : ℤ ⊕ ℕ :=
{! !}
```

produces:

```lean
def foo : ℤ ⊕ ℕ :=
{! sum.inl, sum.inr !}
```

and will display:

```lean
sum.inl : ℤ → ℤ ⊕ ℕ

sum.inr : ℕ → ℤ ⊕ ℕ
```

-/
@[hole_command] meta def list_constructors_hole : hole_command :=
{ name := "List Constructors",
  descr := "Show the list of constructors of the expected type.",
  action := λ es,
  do t ← target >>= whnf,
     (_,t) ← open_pis t,
     let cl := t.get_app_fn.const_name,
     let args := t.get_app_args,
     env ← get_env,
     let cs := env.constructors_of cl,
     ts ← cs.mmap $ λ c,
       do { e ← mk_const c,
            t ← infer_type (e.mk_app args) >>= pp,
            c ← strip_prefix c,
            pure format!"\n{c} : {t}\n" },
     fs ← format.intercalate ", " <$> cs.mmap (strip_prefix >=> pure ∘ to_fmt),
     let out := format.to_string format!"{{! {fs} !}",
     trace (format.join ts).to_string,
     return [(out,"")] }

add_tactic_doc
{ name                     := "List Constructors",
  category                 := doc_category.hole_cmd,
  decl_names               := [`tactic.list_constructors_hole],
  tags                     := ["goal information"] }

/-- Makes the declaration `classical.prop_decidable` available to type class inference.
This asserts that all propositions are decidable, but does not have computational content. -/
meta def classical : tactic unit :=
do h ← get_unused_name `_inst,
   mk_const `classical.prop_decidable >>= note h none,
   reset_instance_cache

open expr

/-- `mk_comp v e` checks whether `e` is a sequence of nested applications `f (g (h v))`, and if so,
returns the expression `f ∘ g ∘ h`. -/
meta def mk_comp (v : expr) : expr → tactic expr
| (app f e) :=
  if e = v then pure f
  else do
    guard (¬ v.occurs f) <|> fail "bad guard",
    e' ← mk_comp e >>= instantiate_mvars,
    f ← instantiate_mvars f,
    mk_mapp ``function.comp [none,none,none,f,e']
| e :=
  do guard (e = v),
     t ← infer_type e,
     mk_mapp ``id [t]

/--
From a lemma of the shape `∀ x, f (g x) = h x`
derive an auxiliary lemma of the form `f ∘ g = h`
for reasoning about higher-order functions.
-/
meta def mk_higher_order_type : expr → tactic expr
| (pi n bi d b@(pi _ _ _ _)) :=
  do v ← mk_local_def n d,
     let b' := (b.instantiate_var v),
     (pi n bi d ∘ flip abstract_local v.local_uniq_name) <$> mk_higher_order_type b'
| (pi n bi d b) :=
  do v ← mk_local_def n d,
     let b' := (b.instantiate_var v),
     (l,r) ← match_eq b' <|> fail format!"not an equality {b'}",
     l' ← mk_comp v l,
     r' ← mk_comp v r,
     mk_app ``eq [l',r']
 | e := failed

open lean.parser interactive.types

/-- A user attribute that applies to lemmas of the shape `∀ x, f (g x) = h x`.
It derives an auxiliary lemma of the form `f ∘ g = h` for reasoning about higher-order functions.
-/
@[user_attribute]
meta def higher_order_attr : user_attribute unit (option name) :=
{ name := `higher_order,
  parser := optional ident,
  descr :=
"From a lemma of the shape `∀ x, f (g x) = h x` derive an auxiliary lemma of the
form `f ∘ g = h` for reasoning about higher-order functions.",
  after_set := some $ λ lmm _ _,
    do env  ← get_env,
       decl ← env.get lmm,
       let num := decl.univ_params.length,
       let lvls := (list.iota num).map (`l).append_after,
       let l : expr := expr.const lmm $ lvls.map level.param,
       t ← infer_type l >>= instantiate_mvars,
       t' ← mk_higher_order_type t,
       (_,pr) ← solve_aux t' $ do {
         intros, applyc ``_root_.funext, intro1, applyc lmm; assumption },
       pr ← instantiate_mvars pr,
       lmm' ← higher_order_attr.get_param lmm,
       lmm' ← (flip name.update_prefix lmm.get_prefix <$> lmm') <|> pure lmm.add_prime,
       add_decl $ declaration.thm lmm' lvls t' (pure pr),
       copy_attribute `simp lmm lmm',
       copy_attribute `functor_norm lmm lmm' }

add_tactic_doc
{ name                     := "higher_order",
  category                 := doc_category.attr,
  decl_names               := [`tactic.higher_order_attr],
  tags                     := ["lemma derivation"] }

attribute [higher_order map_comp_pure] map_pure

/--
Copies a definition into the `tactic.interactive` namespace to make it usable
in proof scripts. It allows one to write

```lean
@[interactive]
meta def my_tactic := ...
```

instead of

```lean
meta def my_tactic := ...

run_cmd add_interactive [``my_tactic]
```
-/
@[user_attribute]
meta def interactive_attr : user_attribute :=
{ name := `interactive,
  descr :=
"Put a definition in the `tactic.interactive` namespace to make it usable
in proof scripts.",
  after_set := some $ λ tac _ _, add_interactive [tac] }

add_tactic_doc
{ name                     := "interactive",
  category                 := doc_category.attr,
  decl_names               := [``tactic.interactive_attr],
  tags                     := ["environment"] }

/-- Attribute `needed` is used to mark declarations that are featured
in the current file.  Then, the `#unneeded` command can be used to
list the declaration present in the file that do not support the main
features of the file. -/
@[user_attribute]
meta def needed_attr : user_attribute :=
{ name := `needed,
  descr := "tag essential declarations to help identify unused definitions" }

/-- `unneeded n m` removes from the map of unneeded declarations those
referenced by declaration named `n` which is considerred to be a
needed declaration -/
private meta def unneeded : name → name_map declaration → tactic (name_map declaration)
| n m :=
  do d ← get_decl n,
     if m.contains n then do
       let m := m.erase n,
       let ns := d.value.list_constant.union d.type.list_constant,
       ns.mfold m unneeded
     else pure m

/-- In the current file, list all the declaration that are not marked as `@[needed]` and
that are not referenced by such declarations -/
meta def all_unneeded : tactic (name_map declaration) :=
do ds ← local_decls,
   ls ← ds.keys.mfilter (succeeds ∘ user_attribute.get_param_untyped needed_attr),
   ds ← ls.mfoldl (flip unneeded) ds,
   ds.mfilter $ λ n d, do
     e ← get_env,
     return $ !d.is_auto_generated e &&
       !(n.get_prefix.last = "equations") &&
       !(n.last = "_sunfold") &&
       !(string.is_prefix_of "_match_" n.last) &&
       !(string.is_prefix_of "_proof_" n.last) &&
       !(string.is_prefix_of "_main" n.last) &&
       !(name.is_suffix_of `_main._meta_aux n)

/--
Use `refine` to partially discharge the goal,
or call `fconstructor` and try again.
-/
private meta def use_aux (h : pexpr) : tactic unit :=
(focus1 (refine h >> done)) <|> (fconstructor >> use_aux)

/-- Similar to `existsi`, `use l` will use entries in `l` to instantiate existential obligations
at the beginning of a target. Unlike `existsi`, the pexprs in `l` are elaborated with respect to
the expected type.

```lean
example : ∃ x : ℤ, x = x :=
by tactic.use ``(42)
```

See the doc string for `tactic.interactive.use` for more information.
 -/
protected meta def use (l : list pexpr) : tactic unit :=
focus1 $ seq' (l.mmap' $ λ h, use_aux h <|> fail format!"failed to instantiate goal with {h}")
              instantiate_mvars_in_target

/-- `clear_aux_decl_aux l` clears all expressions in `l` that represent aux decls from the
local context. -/
meta def clear_aux_decl_aux : list expr → tactic unit
| []     := skip
| (e::l) := do cond e.is_aux_decl (tactic.clear e) skip, clear_aux_decl_aux l

/-- `clear_aux_decl` clears all expressions from the local context that represent aux decls. -/
meta def clear_aux_decl : tactic unit :=
local_context >>= clear_aux_decl_aux

/-- `apply_at_aux e et [] h ht` (with `et` the type of `e` and `ht` the type of `h`)
finds a list of expressions `vs` and returns `(e.mk_args (vs ++ [h]), vs)`. -/
meta def apply_at_aux (arg t : expr) : list expr → expr → expr → tactic (expr × list expr)
| vs e (pi n bi d b) :=
  do { v ← mk_meta_var d,
       apply_at_aux (v :: vs) (e v) (b.instantiate_var v) } <|>
  (e arg, vs) <$ unify d t
| vs e _ := failed

/-- `apply_at e h` applies implication `e` on hypothesis `h` and replaces `h` with the result. -/
meta def apply_at (e h : expr) : tactic unit :=
do ht ← infer_type h,
   et ← infer_type e,
   (h', gs') ← apply_at_aux h ht [] e et,
   note h.local_pp_name none h',
   clear h,
   gs' ← gs'.mfilter is_assigned,
   (g :: gs) ← get_goals,
   set_goals (g :: gs' ++ gs)

/-- `symmetry_hyp h` applies `symmetry` on hypothesis `h`. -/
meta def symmetry_hyp (h : expr) (md := semireducible) : tactic unit :=
do tgt   ← infer_type h,
   env   ← get_env,
   let r := get_app_fn tgt,
   match env.symm_for (const_name r) with
   | (some symm) := do s ← mk_const symm,
                       apply_at s h
   | none        := fail "symmetry tactic failed, target is not a relation application with the expected property."
   end

precedence `setup_tactic_parser`:0

/-- `setup_tactic_parser` is a user command that opens the namespaces used in writing
interactive tactics, and declares the local postfix notation `?` for `optional` and `*` for `many`.
It does *not* use the `namespace` command, so it will typically be used after
`namespace tactic.interactive`.
-/
@[user_command]
meta def setup_tactic_parser_cmd (_ : interactive.parse $ tk "setup_tactic_parser") :
  lean.parser unit :=
emit_code_here "
open lean
open lean.parser
open interactive interactive.types

local postfix `?`:9001 := optional
local postfix *:9001 := many .
"

/-- `finally tac finalizer` runs `tac` first, then runs `finalizer` even if
`tac` fails. `finally tac finalizer` fails if either `tac` or `finalizer` fails. -/
meta def finally {β} (tac : tactic α) (finalizer : tactic β) : tactic α :=
λ s, match tac s with
     | (result.success r s') := (finalizer >> pure r) s'
     | (result.exception msg p s') := (finalizer >> result.exception msg p) s'
     end

/--
`on_exception handler tac` runs `tac` first, and then runs `handler` only if `tac` failed.
-/
meta def on_exception {β} (handler : tactic β) (tac : tactic α) : tactic α | s :=
match tac s with
| result.exception msg p s' := (handler *> result.exception msg p) s'
| ok := ok
end

/-- `decorate_error add_msg tac` prepends `add_msg` to an exception produced by `tac` -/
meta def decorate_error (add_msg : string) (tac : tactic α) : tactic α | s :=
match tac s with
| result.exception msg p s :=
  let msg (_ : unit) : format := match msg with
    | some msg := add_msg ++ format.line ++ msg ()
    | none := add_msg
    end in
  result.exception msg p s
| ok := ok
end

/-- Applies tactic `t`. If it succeeds, revert the state, and return the value. If it fails,
  returns the error message. -/
meta def retrieve_or_report_error {α : Type u} (t : tactic α) : tactic (α ⊕ string) :=
λ s, match t s with
| (interaction_monad.result.success a s') := result.success (sum.inl a) s
| (interaction_monad.result.exception msg' _ s') :=
  result.success (sum.inr (msg'.iget ()).to_string) s
end

/-- Applies tactic `t`. If it succeeds, return the value. If it fails, returns the error message. -/
meta def try_or_report_error {α : Type u} (t : tactic α) : tactic (α ⊕ string) :=
λ s, match t s with
| (interaction_monad.result.success a s') := result.success (sum.inl a) s'
| (interaction_monad.result.exception msg' _ s') :=
  result.success (sum.inr (msg'.iget ()).to_string) s
end

/-- This tactic succeeds if `t` succeeds or fails with message `msg` such that `p msg` is `tt`.
-/
meta def succeeds_or_fails_with_msg {α : Type} (t : tactic α) (p : string → bool) : tactic unit :=
do x ← retrieve_or_report_error t,
match x with
| (sum.inl _) := skip
| (sum.inr msg) := if p msg then skip else fail msg
end

add_tactic_doc
{ name                     := "setup_tactic_parser",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.setup_tactic_parser_cmd],
  tags                     := ["parsing", "notation"] }

/-- `trace_error msg t` executes the tactic `t`. If `t` fails, traces `msg` and the failure message
of `t`. -/
meta def trace_error (msg : string) (t : tactic α) : tactic α
| s := match t s with
       | (result.success r s') := result.success r s'
       | (result.exception (some msg') p s') := (trace msg >> trace (msg' ()) >> result.exception (some msg') p) s'
       | (result.exception none p s') := result.exception none p s'
       end

/--
``trace_if_enabled `n msg`` traces the message `msg`
only if tracing is enabled for the name `n`.

Create new names registered for tracing with `declare_trace n`.
Then use `set_option trace.n true/false` to enable or disable tracing for `n`.
-/
meta def trace_if_enabled
  (n : name) {α : Type u} [has_to_tactic_format α] (msg : α) : tactic unit :=
when_tracing n (trace msg)

/--
``trace_state_if_enabled `n msg`` prints the tactic state,
preceded by the optional string `msg`,
only if tracing is enabled for the name `n`.
-/
meta def trace_state_if_enabled
  (n : name) (msg : string := "") : tactic unit :=
when_tracing n ((if msg = "" then skip else trace msg) >> trace_state)

/--
This combinator is for testing purposes. It succeeds if `t` fails with message `msg`,
and fails otherwise.
-/
meta def success_if_fail_with_msg {α : Type u} (t : tactic α) (msg : string) : tactic unit :=
λ s, match t s with
| (interaction_monad.result.exception msg' _ s') :=
  let expected_msg := (msg'.iget ()).to_string in
  if msg = expected_msg then result.success () s
  else mk_exception format!"failure messages didn't match. Expected:\n{expected_msg}" none s
| (interaction_monad.result.success a s) :=
   mk_exception "success_if_fail_with_msg combinator failed, given tactic succeeded" none s
end

/--
Construct a `refine ...` or `exact ...` string which would construct `g`.
-/
meta def tactic_statement (g : expr) : tactic string :=
do g ← instantiate_mvars g,
   g ← head_beta g,
   r ← pp (replace_mvars g),
   if g.has_meta_var
   then return (sformat!"Try this: refine {r}")
   else return (sformat!"Try this: exact {r}")

/-- `with_local_goals gs tac` runs `tac` on the goals `gs` and then restores the
initial goals and returns the goals `tac` ended on. -/
meta def with_local_goals {α} (gs : list expr) (tac : tactic α) : tactic (α × list expr) :=
do gs' ← get_goals,
   set_goals gs,
   finally (prod.mk <$> tac <*> get_goals) (set_goals gs')

/-- like `with_local_goals` but discards the resulting goals -/
meta def with_local_goals' {α} (gs : list expr) (tac : tactic α) : tactic α :=
prod.fst <$> with_local_goals gs tac

/-- Representation of a proof goal that lends itself to comparison. The
following goal:

```lean
l₀ : T,
l₁ : T
⊢ ∀ v : T, foo
```

is represented as

```
(2, ∀ l₀ l₁ v : T, foo)
```

The number 2 indicates that first the two bound variables of the
`∀` are actually local constant. Comparing two such goals with `=`
rather than `=ₐ` or `is_def_eq` tells us that proof script should
not see the difference between the two.
 -/
meta def packaged_goal := ℕ × expr

/-- proof state made of multiple `goal` meant for comparing
the result of running different tactics -/
meta def proof_state := list packaged_goal

meta instance goal.inhabited : inhabited packaged_goal := ⟨(0,var 0)⟩
meta instance proof_state.inhabited : inhabited proof_state :=
(infer_instance : inhabited (list packaged_goal))

/-- create a `packaged_goal` corresponding to the current goal -/
meta def get_packaged_goal : tactic packaged_goal := do
ls ← local_context,
tgt ← target >>= instantiate_mvars,
tgt ← pis ls tgt,
pure (ls.length, tgt)

/-- `goal_of_mvar g`, with `g` a meta variable, creates a
`packaged_goal` corresponding to `g` interpretted as a proof goal -/
meta def goal_of_mvar (g : expr) : tactic packaged_goal :=
with_local_goals' [g] get_packaged_goal

/-- `get_proof_state` lists the user visible goal for each goal
of the current state and for each goal, abstracts all of the
meta variables of the other gaols.

This produces a list of goals in the form of `ℕ × expr` where
the `expr` encodes the following proof state:

```lean
2 goals
l₁ : t₁,
l₂ : t₂,
l₃ : t₃
⊢ tgt₁

⊢ tgt₂
```

as

```lean
[ (3, ∀ (mv : tgt₁) (mv : tgt₂) (l₁ : t₁) (l₂ : t₂) (l₃ : t₃), tgt₁),
  (0, ∀ (mv : tgt₁) (mv : tgt₂), tgt₂) ]
```

with 2 goals, the first 2 bound variables encode the meta variable
of all the goals, the next 3 (in the first goal) and 0 (in the second goal)
are the local constants.

This representation allows us to compare goals and proof states while
ignoring information like the unique name of local constants and
the equality or difference of meta variables that encode the same goal.
-/
meta def get_proof_state : tactic proof_state :=
do gs ← get_goals,
   gs.mmap $ λ g, do
     ⟨n,g⟩ ← goal_of_mvar g,
     g ← gs.mfoldl (λ g v, do
       g ← kabstract g v reducible ff,
       pure $ pi `goal binder_info.default `(true) g ) g,
     pure (n,g)

/--
Run `tac` in a disposable proof state and return the state.
See `proof_state`, `goal` and `get_proof_state`.
-/
meta def get_proof_state_after (tac : tactic unit) : tactic (option proof_state) :=
try_core $ retrieve $ tac >> get_proof_state

open lean interactive

/-- A type alias for `tactic format`, standing for "pretty print format". -/
meta def pformat := tactic format

/-- `mk` lifts `fmt : format` to the tactic monad (`pformat`). -/
meta def pformat.mk (fmt : format) : pformat := pure fmt

/-- an alias for `pp`. -/
meta def to_pfmt {α} [has_to_tactic_format α] (x : α) : pformat :=
pp x

meta instance pformat.has_to_tactic_format : has_to_tactic_format pformat :=
⟨ id ⟩

meta instance : has_append pformat :=
⟨ λ x y, (++) <$> x <*> y ⟩

meta instance tactic.has_to_tactic_format [has_to_tactic_format α] :
  has_to_tactic_format (tactic α) :=
⟨ λ x, x >>= to_pfmt ⟩

private meta def parse_pformat : string → list char → parser pexpr
| acc []            := pure ``(to_pfmt %%(reflect acc))
| acc ('\n'::s)     :=
do f ← parse_pformat "" s,
   pure ``(to_pfmt %%(reflect acc) ++ pformat.mk format.line ++ %%f)
| acc ('{'::'{'::s) := parse_pformat (acc ++ "{") s
| acc ('{'::s) :=
do (e, s) ← with_input (lean.parser.pexpr 0) s.as_string,
   '}'::s ← return s.to_list | fail "'}' expected",
   f ← parse_pformat "" s,
   pure ``(to_pfmt %%(reflect acc) ++ to_pfmt %%e ++ %%f)
| acc (c::s) := parse_pformat (acc.str c) s

reserve prefix `pformat! `:100

/-- See `format!` in `init/meta/interactive_base.lean`.

The main differences are that `pp` is called instead of `to_fmt` and that we can use
arguments of type `tactic α` in the quotations.

Now, consider the following:
```lean
e ← to_expr ``(3 + 7),
trace format!"{e}"  -- outputs `has_add.add.{0} nat nat.has_add (bit1.{0} nat nat.has_one nat.has_add (has_one.one.{0} nat nat.has_one)) ...`
trace pformat!"{e}" -- outputs `3 + 7`
```

The difference is significant. And now, the following is expressible:

```lean
e ← to_expr ``(3 + 7),
trace pformat!"{e} : {infer_type e}" -- outputs `3 + 7 : ℕ`
```

See also: `trace!` and `fail!`
-/
@[user_notation]
meta def pformat_macro (_ : parse $ tk "pformat!") (s : string) : parser pexpr :=
do e ← parse_pformat "" s.to_list,
   return ``(%%e : pformat)

reserve prefix `fail! `:100

/--
The combination of `pformat` and `fail`.
-/
@[user_notation]
meta def fail_macro (_ : parse $ tk "fail!") (s : string) : parser pexpr :=
do e ← pformat_macro () s,
   pure ``((%%e : pformat) >>= fail)

reserve prefix `trace! `:100
/--
The combination of `pformat` and `trace`.
-/
@[user_notation]
meta def trace_macro (_ : parse $ tk "trace!") (s : string) : parser pexpr :=
do e ← pformat_macro () s,
   pure ``((%%e : pformat) >>= trace)

/-- A hackish way to get the `src` directory of mathlib. -/
meta def get_mathlib_dir : tactic string :=
do e ← get_env,
  s ← e.decl_olean `tactic.reset_instance_cache,
  return $ s.popn_back 17

/-- Checks whether a declaration with the given name is declared in mathlib.
If you want to run this tactic many times, you should use `environment.is_prefix_of_file` instead,
since it is expensive to execute `get_mathlib_dir` many times. -/
meta def is_in_mathlib (n : name) : tactic bool :=
do ml ← get_mathlib_dir, e ← get_env, return $ e.is_prefix_of_file ml n

/--
Runs a tactic by name.
If it is a `tactic string`, return whatever string it returns.
If it is a `tactic unit`, return the name.
(This is mostly used in invoking "self-reporting tactics", e.g. by `tidy` and `hint`.)
-/
meta def name_to_tactic (n : name) : tactic string :=
do d ← get_decl n,
   e ← mk_const n,
   let t := d.type,
   if (t =ₐ `(tactic unit)) then
     (eval_expr (tactic unit) e) >>= (λ t, t >> (name.to_string <$> strip_prefix n))
   else if (t =ₐ `(tactic string)) then
     (eval_expr (tactic string) e) >>= (λ t, t)
   else fail!"name_to_tactic cannot take `{n} as input: its type must be `tactic string` or `tactic unit`"

/-- auxiliary function for `apply_under_n_pis` -/
private meta def apply_under_n_pis_aux (func arg : pexpr) : ℕ → ℕ → expr → pexpr
| n 0 _ :=
  let vars := ((list.range n).reverse.map (@expr.var ff)),
      bd := vars.foldl expr.app arg.mk_explicit in
  func bd
| n (k+1) (expr.pi nm bi tp bd) := expr.pi nm bi (pexpr.of_expr tp) (apply_under_n_pis_aux (n+1) k bd)
| n (k+1) t := apply_under_n_pis_aux n 0 t

/--
Assumes `pi_expr` is of the form `Π x1 ... xn xn+1..., _`.
Creates a pexpr of the form `Π x1 ... xn, func (arg x1 ... xn)`.
All arguments (implicit and explicit) to `arg` should be supplied. -/
meta def apply_under_n_pis (func arg : pexpr) (pi_expr : expr) (n : ℕ) : pexpr :=
apply_under_n_pis_aux func arg 0 n pi_expr

/--
Assumes `pi_expr` is of the form `Π x1 ... xn, _`.
Creates a pexpr of the form `Π x1 ... xn, func (arg x1 ... xn)`.
All arguments (implicit and explicit) to `arg` should be supplied. -/
meta def apply_under_pis (func arg : pexpr) (pi_expr : expr) : pexpr :=
apply_under_n_pis func arg pi_expr pi_expr.pi_arity

/--
If `func` is a `pexpr` representing a function that takes an argument `a`,
`get_pexpr_arg_arity_with_tgt func tgt` returns the arity of `a`.
When `tgt` is a `pi` expr, `func` is elaborated in a context
with the domain of `tgt`.

Examples:
* ```get_pexpr_arg_arity ``(ring) `(true)``` returns 0, since `ring` takes one non-function argument.
* ```get_pexpr_arg_arity_with_tgt ``(monad) `(true)``` returns 1, since `monad` takes one argument of type `α → α`.
* ```get_pexpr_arg_arity_with_tgt ``(module R) `(Π (R : Type), comm_ring R → true)``` returns 0
 -/
meta def get_pexpr_arg_arity_with_tgt (func : pexpr) (tgt : expr) : tactic ℕ :=
lock_tactic_state $ do
  mv ← mk_mvar,
  solve_aux tgt $ intros >> to_expr ``(%%func %%mv),
  expr.pi_arity <$> (infer_type mv >>= instantiate_mvars)

/-- `find_private_decl n none` finds a private declaration named `n` in any of the imported files.

`find_private_decl n (some m)` finds a private declaration named `n` in the same file where a
declaration named `m` can be found. -/
meta def find_private_decl (n : name) (fr : option name) : tactic name :=
do env ← get_env,
   fn ← option_t.run (do
         fr ← option_t.mk (return fr),
         d ← monad_lift $ get_decl fr,
         option_t.mk (return $ env.decl_olean d.to_name) ),
   let p : string → bool :=
     match fn with
     | (some fn) := λ x, fn = x
     | none := λ _, tt
     end,
   let xs := env.decl_filter_map (λ d,
     do fn ← env.decl_olean d.to_name,
        guard ((`_private).is_prefix_of d.to_name ∧ p fn ∧ d.to_name.update_prefix name.anonymous = n),
        pure d.to_name),
   match xs with
   | [n] := pure n
   | [] := fail "no such private found"
   | _ := fail "many matches found"
   end

open lean.parser interactive

/-- `import_private foo from bar` finds a private declaration `foo` in the same file as `bar`
and creates a local notation to refer to it.

`import_private foo` looks for `foo` in all imported files.

When possible, make `foo` non-private rather than using this feature.
 -/
@[user_command]
meta def import_private_cmd (_ : parse $ tk "import_private") : lean.parser unit :=
do n  ← ident,
   fr ← optional (tk "from" *> ident),
   n ← find_private_decl n fr,
   c ← resolve_constant n,
   d ← get_decl n,
   let c := @expr.const tt c d.univ_levels,
   new_n ← new_aux_decl_name,
   add_decl $ declaration.defn new_n d.univ_params d.type c reducibility_hints.abbrev d.is_trusted,
   let new_not := sformat!"local notation `{n.update_prefix name.anonymous}` := {new_n}",
   emit_command_here $ new_not,
   skip .

add_tactic_doc
{ name                     := "import_private",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.import_private_cmd],
  tags                     := ["renaming"] }

/--
The command `mk_simp_attribute simp_name "description"` creates a simp set with name `simp_name`.
Lemmas tagged with `@[simp_name]` will be included when `simp with simp_name` is called.
`mk_simp_attribute simp_name none` will use a default description.

Appending the command with `with attr1 attr2 ...` will include all declarations tagged with
`attr1`, `attr2`, ... in the new simp set.

This command is preferred to using ``run_cmd mk_simp_attr `simp_name`` since it adds a doc string
to the attribute that is defined. If you need to create a simp set in a file where this command is
not available, you should use
```lean
run_cmd mk_simp_attr `simp_name
run_cmd add_doc_string `simp_attr.simp_name "Description of the simp set here"
```
-/
@[user_command]
meta def mk_simp_attribute_cmd (_ : parse $ tk "mk_simp_attribute") : lean.parser unit :=
do n ← ident,
   d ← parser.pexpr,
   d ← to_expr ``(%%d : option string),
   descr ← eval_expr (option string) d,
   with_list ← types.with_ident_list <|> return [],
   mk_simp_attr n with_list,
   add_doc_string (name.append `simp_attr n) $ descr.get_or_else $ "simp set for " ++ to_string n

add_tactic_doc
{ name                     := "mk_simp_attribute",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.mk_simp_attribute_cmd],
  tags                     := ["simplification"] }

/--
Given a user attribute name `attr_name`, `get_user_attribute_name attr_name` returns
the name of the declaration that defines this attribute.
Fails if there is no user attribute with this name.
Example: ``get_user_attribute_name `norm_cast`` returns `` `norm_cast.norm_cast_attr`` -/
meta def get_user_attribute_name (attr_name : name) : tactic name := do
ns ← attribute.get_instances `user_attribute,
ns.mfirst (λ nm, do
  d ← get_decl nm,
  e ← mk_app `user_attribute.name [d.value],
  attr_nm ← eval_expr name e,
  guard $ attr_nm = attr_name,
  return nm) <|> fail!"'{attr_name}' is not a user attribute."

/-- A tactic to set either a basic attribute or a user attribute, as long as the user attribute has
  no parameter.
  If a user attribute with a parameter (that is not `unit`) is set, this function will raise an
  error. -/
-- possible enhancement if needed: use default value for a user attribute with parameter.
meta def set_attribute (attr_name : name) (c_name : name) (persistent := tt)
  (prio : option nat := none) : tactic unit := do
get_decl c_name <|> fail!"unknown declaration {c_name}",
s ← try_or_report_error (set_basic_attribute attr_name c_name persistent prio),
sum.inr msg ← return s | skip,
if msg = (format!"set_basic_attribute tactic failed, '{attr_name}' is not a basic attribute").to_string
then do
  user_attr_nm ← get_user_attribute_name attr_name,
  user_attr_const ← mk_const user_attr_nm,
  tac ← eval_pexpr (tactic unit) ``(user_attribute.set %%user_attr_const %%c_name () %%persistent) <|>
    fail!"Cannot set attribute @[{attr_name}]. The corresponding user attribute {user_attr_nm} has a parameter.",
  tac
else fail msg

/-- The command `#unneeded` lists the declarations that do not support the main features of
the present file. The main features of a file are taken as the declaration tagged with @[needed]. -/
@[user_command]
meta def unneeded_cmd (_ : parse $ tk "#unneeded") : lean.parser unit :=
show tactic unit, from
do ds ← all_unneeded,
   ds.to_list.mmap' $ λ ⟨n,_⟩, trace!"#print {n}"

end tactic

/--
`find_defeq red m e` looks for a key in `m` that is defeq to `e` (up to transparency `red`),
and returns the value associated with this key if it exists.
Otherwise, it fails.
-/
meta def list.find_defeq (red : tactic.transparency) {v} (m : list (expr × v)) (e : expr) :
  tactic (expr × v) :=
m.mfind $ λ ⟨e', val⟩, tactic.is_def_eq e e' red
