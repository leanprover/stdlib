/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.dlist
import tactic.core
import tactic.clear

/-!

# Recursive cases (`rcases`) tactic and related tactics

`rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* An alteration pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

The patterns are fairly liberal about the exact shape of the constructors, and will insert
additional alternation branches and tuple arguments if there are not enough arguments provided, and
reuse the tail for further matches if there are too many arguments provided to alternation and
tuple patterns.

This file also contains the `obtain` and `rintro` tactics, which use the same syntax of `rcases`
patterns but with a slightly different use case:

* `rintro` (or `rintros`) is used like `rintro x ⟨y, z⟩` and is the same as `intros` followed by
  `rcases` on the newly introduced arguments.
* `obtain` is the same as `rcases` but with a syntax styled after `have` rather than `cases`.
  `obtain ⟨hx, hy⟩ | hz := foo` is equivalent to `rcases foo with ⟨hx, hy⟩ | hz`. Unlike `rcases`,
  `obtain` also allows one to omit `:= foo`, although a type must be provided in this case,
  as in `obtain ⟨hx, hy⟩ | hz : a ∧ b ∨ c`, in which case it produces a subgoal for proving
  `a ∧ b ∨ c` in addition to the subgoals `hx : a, hy : b |- goal` and `hz : c |- goal`.

## Tags

rcases, rintro, obtain, destructuring, cases, pattern matching, match
-/

open lean lean.parser

namespace tactic

/-!
These synonyms for `list` are used to clarify the meanings of the many
usages of lists in this module.

- `listΣ` is used where a list represents a disjunction, such as the
  list of possible constructors of an inductive type.

- `listΠ` is used where a list represents a conjunction, such as the
  list of arguments of an individual constructor.

These are merely type synonyms, and so are not checked for consistency
by the compiler.

The `def`/`local notation` combination makes Lean retain these
annotations in reported types.
-/

/-- A list, with a disjunctive meaning (like a list of inductive constructors, or subgoals) -/
@[reducible] def list_Sigma := list

/-- A list, with a conjunctive meaning (like a list of constructor arguments, or hypotheses) -/
@[reducible] def list_Pi := list

local notation `listΣ` := list_Sigma
local notation `listΠ` := list_Pi

/-- A metavariable representing a subgoal, together with a list of local constants to clear. -/
@[reducible] meta def uncleared_goal := list expr × expr

/--
An `rcases` pattern can be one of the following, in a nested combination:

* A name like `foo`
* The special keyword `rfl` (for pattern matching on equality using `subst`)
* A hyphen `-`, which clears the active hypothesis and any dependents.
* A type ascription like `pat : ty` (parentheses are optional)
* A tuple constructor like `⟨p1, p2, p3⟩`
* An alternation / variant pattern `p1 | p2 | p3`

Parentheses can be used for grouping; alternation is higher precedence than type ascription, so
`p1 | p2 | p3 : ty` means `(p1 | p2 | p3) : ty`.

N-ary alternations are treated as a group, so `p1 | p2 | p3` is not the same as `p1 | (p2 | p3)`,
and similarly for tuples. However, note that an n-ary alternation or tuple can match an n-ary
conjunction or disjunction, because if the number of patterns exceeds the number of constructors in
the type being destructed, the extra patterns will match on the last element, meaning that
`p1 | p2 | p3` will act like `p1 | (p2 | p3)` when matching `a1 ∨ a2 ∨ a3`. If matching against a
type with 3 constructors,  `p1 | (p2 | p3)` will act like `p1 | (p2 | p3) | _` instead.
-/
meta inductive rcases_patt : Type
| one : name → rcases_patt
| clear : rcases_patt
| typed : rcases_patt → pexpr → rcases_patt
| tuple : listΠ rcases_patt → rcases_patt
| alts : listΣ rcases_patt → rcases_patt

namespace rcases_patt
meta instance inhabited : inhabited rcases_patt :=
⟨one `_⟩

/-- Get the name from a pattern, if provided -/
meta def name : rcases_patt → option name
| (one `_) := none
| (one `rfl) := none
| (one n) := some n
| (typed p _) := p.name
| (alts [p]) := p.name
| _ := none

/-- Interpret an rcases pattern as a tuple, where `p` becomes `⟨p⟩`
if `p` is not already a tuple. -/
meta def as_tuple : rcases_patt → listΠ rcases_patt
| (tuple ps) := ps
| p := [p]

/-- Interpret an rcases pattern as an alternation, where non-alternations are treated as one
alternative. -/
meta def as_alts : rcases_patt → listΣ rcases_patt
| (alts ps) := ps
| p := [p]

/-- Convert a list of patterns to a tuple pattern, but mapping `[p]` to `p` instead of `⟨p⟩`. -/
meta def tuple' : listΠ rcases_patt → rcases_patt
| [p] := p
| ps := tuple ps

/-- Convert a list of patterns to an alternation pattern, but mapping `[p]` to `p` instead of
a unary alternation `|p`. -/
meta def alts' : listΣ rcases_patt → rcases_patt
| [p] := p
| ps := alts ps

/-- This function is used for producing rcases patterns based on a case tree. Suppose that we have
a list of patterns `ps` that will match correctly against the branches of the case tree for one
constructor. This function will merge tuples at the end of the list, so that `[a, b, ⟨c, d⟩]`
becomes `⟨a, b, c, d⟩` instead of `⟨a, b, ⟨c, d⟩⟩`.

We must be careful to turn `[a, ⟨⟩]` into `⟨a, ⟨⟩⟩` instead of `⟨a⟩` (which will not perform the
nested match). -/
meta def tuple₁_core : listΠ rcases_patt → listΠ rcases_patt
| [] := []
| [tuple []] := [tuple []]
| [tuple ps] := ps
| (p :: ps) := p :: tuple₁_core ps

/-- This function is used for producing rcases patterns based on a case tree. This is like
`tuple₁_core` but it produces a pattern instead of a tuple pattern list, converting `[n]` to `n`
instead of `⟨n⟩` and `[]` to `_`, and otherwise just converting `[a, b, c]` to `⟨a, b, c⟩`. -/
meta def tuple₁ : listΠ rcases_patt → rcases_patt
| [] := default _
| [one n] := one n
| ps := tuple (tuple₁_core ps)

/-- This function is used for producing rcases patterns based on a case tree. Here we are given
the list of patterns to apply to each argument of each constructor after the main case, and must
produce a list of alternatives with the same effect. This function calls `tuple₁` to make the
individual alternatives, and handles merging `[a, b, c | d]` to `a | b | c | d` instead of
`a | b | (c | d)`. -/
meta def alts₁_core : listΣ (listΠ rcases_patt) → listΣ rcases_patt
| [] := []
| [[alts ps]] := ps
| (p :: ps) := tuple₁ p :: alts₁_core ps

/-- This function is used for producing rcases patterns based on a case tree. This is like
`alts₁_core`, but it produces a cases pattern directly instead of a list of alternatives. We
specially translate the empty alternation to `⟨⟩`, and translate `|(a | b)` to `⟨a | b⟩` (because we
don't have any syntax for unary alternation). Otherwise we can use the regular merging of
alternations at the last argument so that `a | b | (c | d)` becomes `a | b | c | d`. -/
meta def alts₁ : listΣ (listΠ rcases_patt) → rcases_patt
| [[]] := tuple []
| [[alts ps]] := tuple [alts ps]
| ps := alts' (alts₁_core ps)

meta instance has_reflect : has_reflect rcases_patt
| (one n) := `(_)
| clear := `(_)
| (typed l e) :=
  (`(typed).subst (has_reflect l)).subst (reflect e)
| (tuple l) := `(λ l, tuple l).subst $
  by haveI := has_reflect; exact list.reflect l
| (alts l) := `(λ l, alts l).subst $
  by haveI := has_reflect; exact list.reflect l

/-- Formats an `rcases` pattern. If the `bracket` argument is true, then it will be
printed at high precedence, i.e. it will have parentheses around it if it is not already a tuple
or atomic name. -/
protected meta def format : ∀ bracket : bool, rcases_patt → tactic _root_.format
| _ (one n) := pure $ to_fmt n
| _ clear := pure "-"
| _ (tuple []) := pure "⟨⟩"
| _ (tuple ls) := do
  fs ← ls.mmap $ format ff,
  pure $ "⟨" ++ _root_.format.group (_root_.format.nest 1 $
    _root_.format.join $ list.intersperse ("," ++ _root_.format.line) fs) ++ "⟩"
| br (alts ls) := do
  fs ← ls.mmap $ format tt,
  let fmt := _root_.format.join $ list.intersperse (↑" |" ++ _root_.format.space) fs,
  pure $ if br then _root_.format.bracket "(" ")" fmt else fmt
| br (typed p e) := do
  fp ← format ff p,
  fe ← pp e,
  let fmt := fp ++ " : " ++ fe,
  pure $ if br then _root_.format.bracket "(" ")" fmt else fmt

meta instance has_to_tactic_format : has_to_tactic_format rcases_patt := ⟨rcases_patt.format ff⟩

end rcases_patt

/-- Takes the number of fields of a single constructor and patterns to match its fields against
(not necessarily the same number). The returned lists each contain one element per field of the
constructor. The `name` is the name which will be used in the top-level `cases` tactic, and the
`rcases_patt` is the pattern which the field will be matched against by subsequent `cases`
tactics. -/
meta def rcases.process_constructor :
  nat → listΠ rcases_patt → listΠ name × listΠ rcases_patt
| 0     ps  := ([], [])
| 1     []  := ([`_], [default _])
| 1     [p] := ([p.name.get_or_else `_], [p])

-- The interesting case: we matched the last field against multiple
-- patterns, so split off the remaining patterns into a subsequent
-- match. This handles matching `α × β × γ` against `⟨a, b, c⟩`.
| 1     ps  := ([`_], [rcases_patt.tuple ps])

| (n+1) ps  :=
  let hd := ps.head, (ns, tl) := rcases.process_constructor n ps.tail in
  (hd.name.get_or_else `_ :: ns, hd :: tl)

/-- Takes a list of constructor names, and an (alternation) list of patterns, and matches each
pattern against its constructor. It returns the list of names that will be passed to `cases`,
and the list of `(constructor name, patterns)` for each constructor, where `patterns` is the
(conjunctive) list of patterns to apply to each constructor argument. -/
meta def rcases.process_constructors (params : nat) :
  listΣ name → listΣ rcases_patt →
  tactic (dlist name × listΣ (name × listΠ rcases_patt))
| []      ps := pure (dlist.empty, [])
| (c::cs) ps := do
  n ← mk_const c >>= get_arity,
  let (h, t) := (match cs, ps.tail with
  -- We matched the last constructor against multiple patterns,
  -- so split off the remaining constructors. This handles matching
  -- `α ⊕ β ⊕ γ` against `a|b|c`.
  | [], _::_ := ([rcases_patt.alts ps], [])
  | _, _ := (ps.head.as_tuple, ps.tail)
  end : _),
  let (ns, ps) := rcases.process_constructor (n - params) h,
  (l, r) ← rcases.process_constructors cs t,
  pure (dlist.of_list ns ++ l, (c, ps) :: r)

/-- Like `zip`, but only elements satisfying a matching predicate `p` will go in the list,
and elements of the first list that fail to match the second list will be skipped. -/
private def align {α β} (p : α → β → Prop) [∀ a b, decidable (p a b)] :
  list α → list β → list (α × β)
| (a::as) (b::bs) :=
  if p a b then (a, b) :: align as bs else align as (b::bs)
| _ _ := []

/-- Given a local constant `e`, get its type. *But* if `e` does not exist, go find a hypothesis
with the same pretty name as `e` and get it instead. This is needed because we can sometimes lose
track of the unique names of hypotheses when they are revert/intro'd by `change` and `cases`. (A
better solution would be for these tactics to return a map of renamed hypotheses so that we don't
lose track of them.) -/
private meta def get_local_and_type (e : expr) : tactic (expr × expr) :=
(do t ← infer_type e, pure (t, e)) <|> (do
    e ← get_local e.local_pp_name,
    t ← infer_type e, pure (t, e))

/--
* `rcases_core p e` will match a pattern `p` against a local hypothesis `e`.
  It returns the list of subgoals that were produced.
* `rcases.continue pes` will match a (conjunctive) list of `(p, e)` pairs which refer to
  patterns and local hypotheses to match against, and applies all of them. Note that this can
  involve matching later arguments multiple times given earlier arguments, for example
  `⟨a | b, ⟨c, d⟩⟩` performs the `⟨c, d⟩` match twice, once on the `a` branch and once on `b`.
-/
meta mutual def rcases_core, rcases.continue
with rcases_core : rcases_patt → expr → tactic (list uncleared_goal)
| (rcases_patt.one `rfl) e := do
  (t, e) ← get_local_and_type e,
  subst' e,
  list.map (prod.mk []) <$> get_goals
-- If the pattern is any other name, we already bound the name in the
-- top-level `cases` tactic, so there is no more work to do for it.
| (rcases_patt.one _) _ := list.map (prod.mk []) <$> get_goals
| rcases_patt.clear e := do
  m ← try_core (get_local_and_type e),
  list.map (prod.mk $ m.elim [] (λ ⟨_, e⟩, [e])) <$> get_goals
| (rcases_patt.typed p ty) e := do
  (t, e) ← get_local_and_type e,
  ty ← i_to_expr_no_subgoals ``(%%ty : Sort*),
  unify t ty,
  t ← instantiate_mvars t,
  ty ← instantiate_mvars ty,
  e ← if t =ₐ ty then pure e else
    change_core ty (some e) >> get_local e.local_pp_name,
  rcases_core p e
| (rcases_patt.alts [p]) e := rcases_core p e
| pat e := do
  (t, e) ← get_local_and_type e,
  t ← whnf t,
  env ← get_env,
  let I := t.get_app_fn.const_name,
  let pat := pat.as_alts,
  (ids, r, l) ← (if I ≠ `quot
  then do
    when (¬env.is_inductive I) $
      fail format!"rcases tactic failed: {e} : {I} is not an inductive datatype",
    let params := env.inductive_num_params I,
    let c := env.constructors_of I,
    (ids, r) ← rcases.process_constructors params c pat,
    l ← cases_core e ids.to_list,
    pure (ids, r, l)
  else do
    (ids, r) ← rcases.process_constructors 2 [`quot.mk] pat,
    [(_, d)] ← induction e ids.to_list `quot.induction_on |
      fail format!"quotient induction on {e} failed. Maybe goal is not in Prop?",
    -- the result from `induction` is missing the information that the original constructor was
    -- `quot.mk` so we fix this up:
    pure (ids, r, [(`quot.mk, d)])),
  gs ← get_goals,
  -- `cases_core` may not generate a new goal for every constructor,
  -- as some constructors may be impossible for type reasons. (See its
  -- documentation.) Match up the new goals with our remaining work
  -- by constructor name.
  let ls := align (λ (a : name × _) (b : _ × name × _), a.1 = b.2.1) r (gs.zip l),
  list.join <$> ls.mmap (λ⟨⟨_, ps⟩, g, _, hs, _⟩, set_goals [g] >> rcases.continue (ps.zip hs))

with rcases.continue : listΠ (rcases_patt × expr) → tactic (list uncleared_goal)
| [] := list.map (prod.mk []) <$> get_goals
| ((pat, e) :: pes) := do
  gs ← rcases_core pat e,
  list.join <$> gs.mmap (λ ⟨cs, g⟩, do
    set_goals [g],
    ugs ← rcases.continue pes,
    pure $ ugs.map $ λ ⟨cs', gs⟩, (cs ++ cs', gs))

/-- Given a list of `uncleared_goal`s, each of which is a goal metavariable and
a list of variables to clear, actually perform the clear and set the goals with the result. -/
meta def clear_goals (ugs : list uncleared_goal) : tactic unit := do
  gs ← ugs.mmap (λ ⟨cs, g⟩, do
    set_goals [g],
    cs ← cs.mfoldr (λ c cs,
      (do (_, c) ← get_local_and_type c, pure (c :: cs)) <|> pure cs) [],
    clear' tt cs,
    [g] ← get_goals,
    pure g),
  set_goals gs

/-- `rcases h e pat` performs case distinction on `e` using `pat` to
name the arising new variables and assumptions. If `h` is `some` name,
a new assumption `h : e = pat` will relate the expression `e` with the
current pattern. See the module comment for the syntax of `pat`. -/
meta def rcases (h : option name) (p : pexpr) (pat : rcases_patt) : tactic unit := do
  let p := match pat with
  | rcases_patt.typed _ ty := ``(%%p : %%ty)
  | _ := p
  end,
  e ← match h with
    | some h := do
      x ← get_unused_name $ pat.name.get_or_else `this,
      interactive.generalize h () (p, x),
      get_local x
    | none := i_to_expr p
    end,
  if e.is_local_constant then
    focus1 (rcases_core pat e >>= clear_goals)
  else do
    x ← pat.name.elim mk_fresh_name pure,
    n ← revert_kdependencies e semireducible,
    tactic.generalize e x <|> (do
      t ← infer_type e,
      tactic.assertv x t e,
      get_local x >>= tactic.revert,
      pure ()),
    h ← tactic.intro1,
    focus1 (rcases_core pat h >>= clear_goals)

/-- `rcases_many es pats` performs case distinction on the `es` using `pat` to
name the arising new variables and assumptions.
See the module comment for the syntax of `pat`. -/
meta def rcases_many (ps : listΠ pexpr) (pat : rcases_patt) : tactic unit := do
  let (_, pats) := rcases.process_constructor ps.length pat.as_tuple,
  pes ← (ps.zip pats).mmap (λ ⟨p, pat⟩, do
    let p := match pat with
    | rcases_patt.typed _ ty := ``(%%p : %%ty)
    | _ := p
    end,
    e ← i_to_expr p,
    if e.is_local_constant then
      pure (pat, e)
    else do
      x ← pat.name.elim mk_fresh_name pure,
      n ← revert_kdependencies e semireducible,
      tactic.generalize e x <|> (do
        t ← infer_type e,
        tactic.assertv x t e,
        get_local x >>= tactic.revert,
        pure ()),
      prod.mk pat <$> tactic.intro1),
  focus1 (rcases.continue pes >>= clear_goals)

/-- `rintro pat₁ pat₂ ... patₙ` introduces `n` arguments, then pattern matches on the `patᵢ` using
the same syntax as `rcases`. -/
meta def rintro (ids : listΠ rcases_patt) : tactic unit :=
do l ← ids.mmap (λ id, do
    e ← intro $ id.name.get_or_else `_,
    pure (id, e)),
  focus1 (rcases.continue l >>= clear_goals)

/-- Like `zip_with`, but if the lists don't match in length, the excess elements will be put at the
end of the result. -/
def merge_list {α} (m : α → α → α) : list α → list α → list α
| [] l₂ := l₂
| l₁ [] := l₁
| (a :: l₁) (b :: l₂) := m a b :: merge_list l₁ l₂

/-- Merge two `rcases` patterns. This is used to underapproximate a case tree by an `rcases`
pattern. The two patterns come from cases in two branches, that due to the syntax of `rcases`
patterns are forced to overlap. The rule here is that we take only the case splits that are in
common between both branches. For example if one branch does `⟨a, b⟩` and the other does `c`,
then we return `c` because we don't know that a case on `c` would be safe to do. -/
meta def rcases_patt.merge : rcases_patt → rcases_patt → rcases_patt
| (rcases_patt.alts p₁) p₂ := rcases_patt.alts (merge_list rcases_patt.merge p₁ p₂.as_alts)
| p₁ (rcases_patt.alts p₂) := rcases_patt.alts (merge_list rcases_patt.merge p₁.as_alts p₂)
| (rcases_patt.tuple p₁) p₂ := rcases_patt.tuple (merge_list rcases_patt.merge p₁ p₂.as_tuple)
| p₁ (rcases_patt.tuple p₂) := rcases_patt.tuple (merge_list rcases_patt.merge p₁.as_tuple p₂)
| (rcases_patt.typed p₁ e) p₂ := rcases_patt.typed (p₁.merge p₂) e
| p₁ (rcases_patt.typed p₂ e) := rcases_patt.typed (p₁.merge p₂) e
| (rcases_patt.one `rfl) (rcases_patt.one `rfl) := rcases_patt.one `rfl
| (rcases_patt.one `_) p := p
| p (rcases_patt.one `_) := p
| rcases_patt.clear p := p
| p rcases_patt.clear := p
| (rcases_patt.one n) _ := rcases_patt.one n

/--
* `rcases_hint_core depth e` does the same as `rcases p e`, except the pattern `p` is an output
  instead of an input, controlled only by the case depth argument `depth`. We use `cases` to depth
  `depth` and then reconstruct an `rcases` pattern `p` that would, if passed to `rcases`, perform
  the same thing as the case tree we just constructed (or at least, the nearest expressible
  approximation to this.)
* `rcases_hint.process_constructors depth cs l` takes a list of constructor names `cs` and a
  matching list `l` of elements `(g, c', hs, _)` where  `c'` is a constructor name (used for
  alignment with `cs`), `g` is the subgoal, and `hs` is the list of local hypotheses created by
  `cases` in that subgoal. It matches on all of them, and then produces a `ΣΠ`-list of `rcases`
  patterns describing the result, and the list of generated subgoals.
* `rcases_hint.continue depth es` does the same as `rcases.continue (ps.zip es)`, except the
  patterns `ps` are an output instead of an input, created by matching on everything to depth
  `depth` and recording the successful cases. It returns `ps`, and the list of generated subgoals.
-/
meta mutual def rcases_hint_core, rcases_hint.process_constructors, rcases_hint.continue
with rcases_hint_core : ℕ → expr → tactic (rcases_patt × list expr)
| depth e := do
  (t, e) ← get_local_and_type e,
  t ← whnf t,
  env ← get_env,
  let I := t.get_app_fn.const_name,
  (do guard (I = ``eq),
    subst' e,
    prod.mk (rcases_patt.one `rfl) <$> get_goals) <|>
  (do
    let c := env.constructors_of I,
    some l ← try_core (guard (depth ≠ 0) >> cases_core e) |
      let n := match e.local_pp_name with name.anonymous := `_ | n := n end in
      prod.mk (rcases_patt.one n) <$> get_goals,
    gs ← get_goals,
    if gs.empty then
      pure (rcases_patt.tuple [], [])
    else do
      (ps, gs') ← rcases_hint.process_constructors (depth - 1) c (gs.zip l),
      pure (rcases_patt.alts₁ ps, gs'))

with rcases_hint.process_constructors : ℕ → listΣ name →
  list (expr × name × listΠ expr × list (name × expr)) →
  tactic (listΣ (listΠ rcases_patt) × list expr)
| depth [] _  := pure ([], [])
| depth cs [] := pure (cs.map (λ _, []), [])
| depth (c::cs) ls@((g, c', hs, _) :: l) :=
  if c ≠ c' then do
    (ps, gs) ← rcases_hint.process_constructors depth cs ls,
    pure ([] :: ps, gs)
  else do
    (p, gs) ← set_goals [g] >> rcases_hint.continue depth hs,
    (ps, gs') ← rcases_hint.process_constructors depth cs l,
    pure (p :: ps, gs ++ gs')

with rcases_hint.continue : ℕ → listΠ expr → tactic (listΠ rcases_patt × list expr)
| depth [] := prod.mk [] <$> get_goals
| depth (e :: es) := do
  (p, gs) ← rcases_hint_core depth e,
  (ps, gs') ← gs.mfoldl (λ (r : listΠ rcases_patt × list expr) g,
    do (ps, gs') ← set_goals [g] >> rcases_hint.continue depth es,
      pure (merge_list rcases_patt.merge r.1 ps, r.2 ++ gs')) ([], []),
  pure (p :: ps, gs')

/--
* `rcases? e` is like `rcases e with ...`, except it generates `...` by matching on everything it
can, and it outputs an `rcases` invocation that should have the same effect.
* `rcases? e : n` can be used to control the depth of case splits (especially important for
recursive types like `nat`, which can be cased as many times as you like). -/
meta def rcases_hint (p : pexpr) (depth : nat) : tactic rcases_patt :=
do e ← i_to_expr p,
  if e.is_local_constant then
    focus1 $ do (p, gs) ← rcases_hint_core depth e, set_goals gs, pure p
  else do
    x ← mk_fresh_name,
    n ← revert_kdependencies e semireducible,
    tactic.generalize e x <|> (do
      t ← infer_type e,
      tactic.assertv x t e,
      get_local x >>= tactic.revert,
      pure ()),
    h ← tactic.intro1,
    focus1 $ do (p, gs) ← rcases_hint_core depth h, set_goals gs, pure p

/--
* `rcases? ⟨e1, e2, e3⟩` is like `rcases ⟨e1, e2, e3⟩ with ...`, except it
  generates `...` by matching on everything it can, and it outputs an `rcases`
  invocation that should have the same effect.
* `rcases? ⟨e1, e2, e3⟩ : n` can be used to control the depth of case splits
  (especially important for recursive types like `nat`, which can be cased as many
  times as you like). -/
meta def rcases_hint_many (ps : list pexpr) (depth : nat) : tactic (listΠ rcases_patt) :=
do es ← ps.mmap (λ p, do
    e ← i_to_expr p,
    if e.is_local_constant then pure e
    else do
      x ← mk_fresh_name,
      n ← revert_kdependencies e semireducible,
      tactic.generalize e x <|> (do
        t ← infer_type e,
        tactic.assertv x t e,
        get_local x >>= tactic.revert,
        pure ()),
      tactic.intro1),
  focus1 $ do
    (ps, gs) ← rcases_hint.continue depth es,
    set_goals gs,
    pure ps

/--
* `rintro?` is like `rintro ...`, except it generates `...` by introducing and matching on
everything it can, and it outputs an `rintro` invocation that should have the same effect.
* `rintro? : n` can be used to control the depth of case splits (especially important for
recursive types like `nat`, which can be cased as many times as you like). -/
meta def rintro_hint (depth : nat) : tactic (listΠ rcases_patt) :=
do l ← intros,
  focus1 $ do
    (p, gs) ← rcases_hint.continue depth l,
    set_goals gs,
    pure p

setup_tactic_parser

/--
* `rcases_patt_parse tt` will parse a high precedence `rcases` pattern, `patt_hi`.
  This means only tuples and identifiers are allowed; alternations and type ascriptions
  require `(...)` instead, which switches to `patt`.
* `rcases_patt_parse ff` will parse a low precedence `rcases` pattern, `patt`. This consists of a
  `patt_med` (which deals with alternations), optionally followed by a `: ty` type ascription. The
  expression `ty` is at `texpr` precedence because it can appear at the end of a tactic, for
  example in `rcases e with x : ty <|> skip`.
* `rcases_patt_parse_list` will parse an alternation list, `patt_med`, one or more `patt`
  patterns separated by `|`. It does not parse a `:` at the end, so that `a | b : ty` parses as
  `(a | b) : ty` where `a | b` is the `patt_med` part.
* `rcases_patt_parse_list_rest a` parses an alternation list after the initial pattern, `| b | c`.

```lean
patt ::= patt_med (":" expr)?
patt_med ::= (patt_hi "|")* patt_hi
patt_hi ::= id | "rfl" | "_" | "⟨" (patt ",")* patt "⟩" | "(" patt ")"
```
-/
meta mutual def rcases_patt_parse, rcases_patt_parse_list, rcases_patt_parse_list_rest
with rcases_patt_parse : bool → parser rcases_patt
| tt := with_desc "patt_hi" $
  (brackets "(" ")" (rcases_patt_parse ff)) <|>
  (rcases_patt.tuple <$> brackets "⟨" "⟩" (sep_by (tk ",") (rcases_patt_parse ff))) <|>
  (tk "-" $> rcases_patt.clear) <|>
  (rcases_patt.one <$> ident_)
| ff := with_desc "patt" $ do
  pat ← rcases_patt.alts' <$> rcases_patt_parse_list,
  (tk ":" *> pat.typed <$> texpr) <|> pure pat

with rcases_patt_parse_list : parser (listΣ rcases_patt)
| x := (with_desc "patt_med" $ rcases_patt_parse tt >>= rcases_patt_parse_list_rest) x

with rcases_patt_parse_list_rest : rcases_patt → parser (listΣ rcases_patt)
| pat :=
  (tk "|" *> list.cons pat <$> rcases_patt_parse_list) <|>
  -- hack to support `-|-` patterns, because `|-` is a token
  (tk "|-" *> list.cons pat <$> rcases_patt_parse_list_rest rcases_patt.clear) <|>
  pure [pat]

/-- Parse the optional depth argument `(: n)?` of `rcases?` and `rintro?`, with default depth 5. -/
meta def rcases_parse_depth : parser nat :=
do o ← (tk ":" *> small_nat)?, pure $ o.get_or_else 5

/-- The arguments to `rcases`, which in fact dispatch to several other tactics.
* `rcases? expr (: n)?` or `rcases? ⟨expr, ...⟩ (: n)?` calls `rcases_hint`
* `rcases? ⟨expr, ...⟩ (: n)?` calls `rcases_hint_many`
* `rcases (h :)? expr (with patt)?` calls `rcases`
* `rcases ⟨expr, ...⟩ (with patt)?` calls `rcases_many`
-/
@[derive has_reflect]
meta inductive rcases_args
| hint (tgt : pexpr ⊕ list pexpr) (depth : nat)
| rcases (name : option name) (tgt : pexpr) (pat : rcases_patt)
| rcases_many (tgt : listΠ pexpr) (pat : rcases_patt)

/-- Syntax for a `rcases` pattern:
* `rcases? expr (: n)?`
* `rcases (h :)? expr (with patt_list (: expr)?)?`. -/
meta def rcases_parse : parser rcases_args :=
with_desc "('?' expr (: n)?) | ((h :)? expr (with patt)?)" $ do
  hint ← (tk "?")?,
  p ← (sum.inr <$> brackets "⟨" "⟩" (sep_by (tk ",") (parser.pexpr 0))) <|>
      (sum.inl <$> texpr),
  match hint with
  | none := do
    p ← (do
      sum.inl (expr.local_const h _ _ _) ← pure p,
      tk ":" *> (@sum.inl _ (pexpr ⊕ list pexpr) ∘ prod.mk h) <$> texpr) <|>
      pure (sum.inr p),
    ids ← (tk "with" *> rcases_patt_parse ff)?,
    let ids := ids.get_or_else (rcases_patt.tuple []),
    pure $ match p with
    | sum.inl (name, tgt) := rcases_args.rcases (some name) tgt ids
    | sum.inr (sum.inl tgt) := rcases_args.rcases none tgt ids
    | sum.inr (sum.inr tgts) := rcases_args.rcases_many tgts ids
    end
  | some _ := do
    depth ← rcases_parse_depth,
    pure $ rcases_args.hint p depth
  end

/--
`rintro_patt_parse_hi` and `rintro_patt_parse` are like `rcases_patt_parse`, but is used for
parsing top level `rintro` patterns, which allow sequences like `(x y : t)` in addition to simple
`rcases` patterns.

* `rintro_patt_parse_hi` will parse a high precedence `rcases` pattern, `rintro_patt_hi` below.
  This means only tuples and identifiers are allowed; alternations and type ascriptions
  require `(...)` instead, which switches to `patt`.
* `rintro_patt_parse tt` will parse a low precedence `rcases` pattern, `rintro_patt` below.
  This consists of either a sequence of patterns `p1 p2 p3` or an alternation list `p1 | p2 | p3`
  treated as a single pattern, optionally followed by a `: ty` type ascription, which applies to
  every pattern in the list.
* `rintro_patt_parse ff` parses `rintro_patt_low`, which is the same as `rintro_patt_parse tt` but
  it does not permit an unparenthesized alternation list, it must have the form `p1 p2 p3 (: ty)?`.

```lean
rintro_patt ::= (rintro_patt_hi+ | patt_med) (":" expr)?
rintro_patt_low ::= rintro_patt_hi* (":" expr)?
rintro_patt_hi ::= patt_hi | "(" rintro_patt ")"
```
-/
meta mutual def rintro_patt_parse_hi, rintro_patt_parse
with rintro_patt_parse_hi : parser (listΠ rcases_patt)
| x := (with_desc "rintro_patt_hi" $
  brackets "(" ")" (rintro_patt_parse tt) <|>
  (do p ← rcases_patt_parse tt, pure [p])) x
with rintro_patt_parse : bool → parser (listΠ rcases_patt)
| med := with_desc "rintro_patt" $ do
  ll ← rintro_patt_parse_hi*,
  pats ← match med, ll.join with
  | tt, [] := failure
  | tt, [pat] := do l ← rcases_patt_parse_list_rest pat, pure [rcases_patt.alts' l]
  | _, pats := pure pats
  end,
  (do tk ":", e ← texpr, pure (pats.map (λ p, rcases_patt.typed p e))) <|>
  pure pats

/-- Syntax for a `rintro` pattern: `('?' (: n)?) | rintro_patt`. -/
meta def rintro_parse : parser (listΠ rcases_patt ⊕ nat) :=
with_desc "('?' (: n)?) | patt*" $
(tk "?" >> sum.inr <$> rcases_parse_depth) <|>
sum.inl <$> rintro_patt_parse ff

namespace interactive
open interactive interactive.types expr

/--
`rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* An alteration pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive datatype,
naming the first three parameters of the first constructor as `a,b,c` and the
first two of the second constructor `d,e`. If the list is not as long as the
number of arguments to the constructor or the number of constructors, the
remaining variables will be automatically named. If there are nested brackets
such as `⟨⟨a⟩, b | c⟩ | d` then these will cause more case splits as necessary.
If there are too many arguments, such as `⟨a, b, c⟩` for splitting on
`∃ x, ∃ y, p x`, then it will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last
parameter as necessary.

`rcases` also has special support for quotient types: quotient induction into Prop works like
matching on the constructor `quot.mk`.

`rcases h : e with PAT` will do the same as `rcases e with PAT` with the exception that an
assumption `h : e = PAT` will be added to the context.

`rcases? e` will perform case splits on `e` in the same way as `rcases e`,
but rather than accepting a pattern, it does a maximal cases and prints the
pattern that would produce this case splitting. The default maximum depth is 5,
but this can be modified with `rcases? e : n`.
-/
meta def rcases : parse rcases_parse → tactic unit
| (rcases_args.rcases h p ids) := tactic.rcases h p ids
| (rcases_args.rcases_many ps ids) := tactic.rcases_many ps ids
| (rcases_args.hint p depth) := do
  (pe, patt) ← match p with
  | sum.inl p := prod.mk <$> pp p <*> rcases_hint p depth
  | sum.inr ps := do
    patts ← rcases_hint_many ps depth,
    pes ← ps.mmap pp,
    pure (format.bracket "⟨" "⟩" (format.comma_separated pes), rcases_patt.tuple patts)
  end,
  ppat ← pp patt,
  trace $ ↑"Try this: rcases " ++ pe ++ " with " ++ ppat

add_tactic_doc
{ name       := "rcases",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.rcases],
  tags       := ["induction"] }

/--
The `rintro` tactic is a combination of the `intros` tactic with `rcases` to
allow for destructuring patterns while introducing variables. See `rcases` for
a description of supported patterns. For example, `rintro (a | ⟨b, c⟩) ⟨d, e⟩`
will introduce two variables, and then do case splits on both of them producing
two subgoals, one with variables `a d e` and the other with `b c d e`.

`rintro`, unlike `rcases`, also supports the form `(x y : ty)` for introducing
and type-ascripting multiple variables at once, similar to binders.

`rintro?` will introduce and case split on variables in the same way as
`rintro`, but will also print the `rintro` invocation that would have the same
result. Like `rcases?`, `rintro? : n` allows for modifying the
depth of splitting; the default is 5.

`rintros` is an alias for `rintro`.
-/
meta def rintro : parse rintro_parse → tactic unit
| (sum.inl []) := intros []
| (sum.inl l)  := tactic.rintro l
| (sum.inr depth) := do
  ps ← tactic.rintro_hint depth,
  fs ← ps.mmap (λ p, do
    f ← pp $ p.format tt,
    pure $ format.space ++ format.group f),
  trace $ ↑"Try this: rintro" ++ format.join fs

/-- Alias for `rintro`. -/
meta def rintros := rintro

add_tactic_doc
{ name       := "rintro",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.rintro, `tactic.interactive.rintros],
  tags       := ["induction"],
  inherit_description_from := `tactic.interactive.rintro }

setup_tactic_parser

/-- Parses `patt? (: expr)? (:= expr)?`, the arguments for `obtain`.
 (This is almost the same as `rcases_patt_parse ff`,
but it allows the pattern part to be empty.) -/
meta def obtain_parse :
  parser ((option rcases_patt × option pexpr) × option (pexpr ⊕ list pexpr)) :=
with_desc "patt? (: expr)? (:= expr)?" $ do
  (pat, tp) ←
    (do pat ← rcases_patt_parse ff,
      pure $ match pat with
      | rcases_patt.typed pat tp := (some pat, some tp)
      | _ := (some pat, none)
      end) <|>
    prod.mk none <$> (tk ":" >> texpr)?,
  prod.mk (pat, tp) <$> (do
    tk ":=",
    (guard tp.is_none >>
      sum.inr <$> brackets "⟨" "⟩" (sep_by (tk ",") (parser.pexpr 0))) <|>
    (sum.inl <$> texpr))?

/--
The `obtain` tactic is a combination of `have` and `rcases`. See `rcases` for
a description of supported patterns.

```lean
obtain ⟨patt⟩ : type,
{ ... }
```
is equivalent to
```lean
have h : type,
{ ... },
rcases h with ⟨patt⟩
```

The syntax `obtain ⟨patt⟩ : type := proof` is also supported.

If `⟨patt⟩` is omitted, `rcases` will try to infer the pattern.

If `type` is omitted, `:= proof` is required.
-/
meta def obtain : parse obtain_parse → tactic unit
| ((pat, _), some (sum.inr val)) :=
  tactic.rcases_many val (pat.get_or_else (default _))
| ((pat, none), some (sum.inl val)) :=
  tactic.rcases none val (pat.get_or_else (default _))
| ((pat, some tp), some (sum.inl val)) :=
  tactic.rcases none val $ (pat.get_or_else (default _)).typed tp
| ((pat, some tp), none) := do
  nm ← mk_fresh_name,
  e ← to_expr tp >>= assert nm,
  (g :: gs) ← get_goals,
  set_goals gs,
  tactic.rcases none ``(%%e) (pat.get_or_else (rcases_patt.one `this)),
  gs ← get_goals,
  set_goals (g::gs)
| ((pat, none), none) :=
  fail $ "`obtain` requires either an expected type or a value.\n" ++
         "usage: `obtain ⟨patt⟩? : type (:= val)?` or `obtain ⟨patt⟩? (: type)? := val`"

add_tactic_doc
{ name       := "obtain",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.obtain],
  tags       := ["induction"] }

end interactive
end tactic
