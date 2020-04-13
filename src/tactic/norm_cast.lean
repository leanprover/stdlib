/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine, Robert Y. Lewis

Normalizing casts inside expressions.
-/

import tactic.basic tactic.interactive

/-!
# A tactic for normalizing casts inside expressions

This tactic normalizes casts inside expressions.
It can be thought of as a call to the simplifier with a specific set of lemmas to
move casts upwards in the expression.
It has special handling of numerals and a simple heuristic to help moving
casts "past" binary operators.
Contrary to simp, it should be safe to use as a non-terminating tactic.

## Important definitions
* `tactic.interactive.norm_cast`
* `tactic.interactive.push_cast`
* `tactic.interactive.exact_mod_cast`
* `tactic.interactive.apply_mod_cast`
* `tactic.interactive.rw_mod_cast`
* `tactic.interactive.assumption_mod_cast`
-/

namespace tactic

/--
Runs `mk_instance` with a time limit.

This is a work around to the fact that in some cases
mk_instance times out instead of failing,
for example: `has_lift_t ℤ ℕ`

`mk_instance'` is used when we assume the type class search
should end instantly.
-/
meta def mk_instance' (e : expr) (timeout := 1000) : tactic expr :=
try_for timeout (mk_instance e)

end tactic

namespace expr

open tactic expr

/--
`flip_aux tp prf` assumes that `prf` has type `tp`, and `tp` has the form `Π ..., b = a` or
`Π ..., b ↔ a`. It returns two `pexpr`s. The first is the Prop `Π ..., a = b` and the second
is a proof of this prop.
-/
meta def flip_aux : expr → expr → option (pexpr × pexpr)
| `(%%a = %%b) e := some (``(%%b = %%a), ``(eq.symm %%e))
| `(%%a ↔ %%b) e := some (``(%%b ↔ %%a), ``(iff.symm %%e))
| (pi n bi d b) e := do
  (b', e') ← flip_aux b (expr.lift_vars e 0 1 (var 0)),
  let d' := pexpr.of_expr d,
  let new_ty := pi n bi d' b',
  let new_e := lam n bi d' e',
  some (new_ty, new_e)
| _ _ := none

/--
TODO: describe
-/
meta def flip (ty e : expr) : tactic (expr × expr) :=
do
  (new_ty, new_e) ← flip_aux ty e,
  new_ty ← to_expr new_ty,
  new_e ← to_expr new_e,
  return (new_ty, new_e)

--TODO: don't count coercions inside implicit parts of the expression?
/--
`is_coe' e` returns `tt` if `e` is a coe function, including the implicit arguments.
`coe has more implicit arguments than `coe_fn.
-/
meta def is_coe' : expr → bool
| (app (app (app (const `has_coe.coe _) _) _) _) := tt
| (app (app (app (const `coe _) _) _) _)         := tt
| (app (app (const `has_coe_to_fun.coe _) _) _)  := tt
| (app (app (const `coe_fn _) _) _)              := tt
| (app (app (const `has_coe_to_sort.coe _) _) _) := tt
| (app (app (const `coe_sort _) _) _)            := tt
| _ := ff

/-- auxiliary function for `count_coes' -/
meta def count_coes_aux : ℕ → expr → ℕ
| n (app f x) := if f.is_coe' then count_coes_aux (n+1) x else count_coes_aux (count_coes_aux n f) x
| n (lam _ _ _ e) := count_coes_aux n e
| n (pi _ _ _ e) := count_coes_aux n e
| n (elet _ a _ b) := count_coes_aux (count_coes_aux n a) b
| n x := n

/-- count how many coercions are inside the expression -/
meta def count_coes : expr → ℕ := count_coes_aux 0

end expr

namespace norm_cast

open tactic expr

mk_simp_attribute push_cast "The `push_cast` simp attribute uses `norm_cast` lemmas
to move casts toward the leaf nodes of the expression."

/--
`label` is a type used to classify `norm_cast` lemmas.
elim lemma:   LHS has 0 head coes and ≥ 1 initial coe,  RHS has 0 coes
move lemma:   LHS has 1 head coe and 0 initial coes,    RHS has 0 head coes and ≥ 1 intenal coes
push lemma:   LHS has 1 head coe and 0 initial coes,    RHS has 0 coes
suqash lemma: LHS has ≥ 2 head coes and 0 initial coes, RHS has fewer initial coes
-/
@[derive [decidable_eq, has_reflect, inhabited]]
inductive label
| elim   : label
| move   : label
| squash : label

namespace label

/-- Convert `label` into `string`. -/
protected def to_string : label → string
| elim   := "elim"
| move   := "move"
| squash := "squash"

instance has_to_string : has_to_string label := ⟨label.to_string⟩

/-- Convert `string` into `label`. -/
def of_string : string -> option label
| "elim" := some elim
| "move" := some move
| "squash" := some squash
| _ := none

end label

open label

/-- Count how many coercions are at the top of the expression. -/
private meta def count_head_coes : expr → ℕ
| (app f x) := if is_coe' f then 1 + count_head_coes x else 0
| _ := 0

/-- Count how many coercions are inside the expression, excluding the top ones. -/
private meta def count_internal_coes (e : expr) : ℕ :=
count_coes e - count_head_coes e

/--
aux function for `norm_cast.classify_type`

remark: the classifier is a little bit less restrictive than the rules describing to the labels.
This is a consequence of the fact that the rules apply to the explicit coercions appearing in the expression.
'coe_to_sort' can tipically appear in type annotations that are implicit in the displayed expression, but
will be accounted for in 'count_coes'.
TODO: see 'count_coes'
-/
private meta def classify_type_aux (lhs rhs : expr) : tactic label :=
do
  when (count_coes lhs = 0) (fail "norm_cast: badly shaped lemma, lhs must contain at least one coe"),
  let lhs_head_coes     := count_head_coes lhs,
  let lhs_internal_coes := count_internal_coes lhs,
  let rhs_head_coes     := count_head_coes rhs,
  let rhs_internal_coes := count_internal_coes rhs,
  if lhs_head_coes = 0 then do
    --TODO: second condition removed until 'count_coes' is updated
    when (¬ (rhs_head_coes = 0 /-∧ rhs_internal_coes = 0-/)) (fail "norm_cast: badly shaped elim lemma, rhs can't contain coes"),
    return elim
  else if lhs_head_coes = 1 then do
    guard (rhs_head_coes = 0) <|> fail "norm_cast: badly shaped lemma, rhs can't start with coe",
    if rhs_internal_coes = 0 then
      return squash
    else
      return move
  else if (rhs_head_coes < lhs_head_coes) then do
    return squash
  else do
    fail "norm_cast: badly shaped shaped squash lemma, rhs must have fewer head coes than lhs"

/-- TODO: update and describe -/
meta def classify_type (ty : expr) : tactic label :=
do (args, tp) ← mk_local_pis ty,
match tp with
| `(%%lhs = %%rhs) := classify_type_aux lhs rhs
| `(%%lhs ↔ %%rhs) := classify_type_aux lhs rhs
| _ := fail "norm_cast: lemma must be = or ↔"
end

/-- The cache for `norm_cast` attribute stores three `simp_lemma` objects. -/
meta structure norm_cast_cache :=
(up : simp_lemmas)
(down : simp_lemmas)
(squash : simp_lemmas)

/-- Empty `norm_cast_cache`. -/
meta def empty_cache : norm_cast_cache :=
{ up     := simp_lemmas.mk,
  down   := simp_lemmas.mk,
  squash := simp_lemmas.mk, }

meta instance : inhabited norm_cast_cache := ⟨empty_cache⟩

/-- `add_elim cache e` adds `e` as an `elim` lemma to `cache`. -/
meta def add_elim (cache : norm_cast_cache) (e : expr) : tactic norm_cast_cache :=
do
  new_up ← simp_lemmas.add cache.up e,
  return
  { up     := new_up,
    down   := cache.down,
    squash := cache.squash, }

/-- `add_move cache e` adds `e` as a `move` lemma to `cache`. -/
meta def add_move (cache : norm_cast_cache) (e : expr) : tactic norm_cast_cache :=
do
  ty ← infer_type e,
  (rev_ty, rev_e) ← expr.flip ty e,
  new_up ← simp_lemmas.add cache.up rev_e,
  new_down ← simp_lemmas.add cache.down e,
  return {
    up     := new_up,
    down   := new_down,
    squash := cache.squash, }

/-- `add_squash cache e` adds `e` as an `squash` lemma to `cache`. -/
meta def add_squash (cache : norm_cast_cache) (e : expr) : tactic norm_cast_cache :=
do
  new_squash ← simp_lemmas.add cache.squash e,
  new_down ← simp_lemmas.add cache.down e,
  return {
    up     := cache.up,
    down   := new_down,
    squash := new_squash, }

/--
The type of the `norm_cast` attribute.
The optional label is used to overwrite the classifier.
-/
meta def norm_cast_attr_ty : Type := user_attribute norm_cast_cache (option label)

/--
`add_lemma cache decl` infers the proper `norm_cast` attribute for `decl` and adds it to `cache`.
-/
meta def add_lemma (attr : norm_cast_attr_ty) (cache : norm_cast_cache) (decl : name) :
  tactic norm_cast_cache :=
do
  e ← mk_const decl,
  ty ← infer_type e,
  param ← attr.get_param decl,
  l ← param <|> classify_type ty,
  match l with
  | elim   := add_elim cache e
  | move   := add_move cache e
  | squash := add_squash cache e
  end

-- special lemmas to handle the ≥, > and ≠ operators
private lemma ge_from_le {α} [has_le α] : ∀ (x y : α), x ≥ y ↔ y ≤ x := λ _ _, iff.rfl
private lemma gt_from_lt {α} [has_lt α] : ∀ (x y : α), x > y ↔ y < x := λ _ _, iff.rfl
private lemma ne_from_not_eq {α} : ∀ (x y : α), x ≠ y ↔ ¬(x = y) := λ _ _, iff.rfl

/--
`mk_cache names` creates a `norm_cast_cache`. It infers the proper `norm_cast` attributes
for names in `names`, and collects the lemmas attributed with specific `norm_cast` attributes.
-/
meta def mk_cache (attr : thunk norm_cast_attr_ty) (names : list name) : tactic norm_cast_cache :=
do
  cache ← monad.foldl (add_lemma (attr ())) empty_cache names,

  --some special lemmas to handle binary relations
  new_up ← simp_lemmas.add_simp cache.up ``ge_from_le,
  new_up ← simp_lemmas.add_simp new_up   ``gt_from_lt,
  new_up ← simp_lemmas.add_simp new_up   ``ne_from_not_eq,

  return {
    up     := new_up,
    down   := cache.down,
    squash := cache.squash, }

/-- parse the optional argument to the attribute -/
meta def parse_label : lean.parser (option label) :=
(do
  n <- lean.parser.ident,
  l <- label.of_string (to_string n) <|> failure,
  return (some l)
) <|> return none

/--
The `norm_cast` attribute.
-/
@[user_attribute] meta def norm_cast_attr : user_attribute norm_cast_cache (option label) :=
{ name      := `norm_cast,
  descr     := "attribute for norm_cast",
  parser    := parse_label,
  after_set := some (λ decl n b, do
    e ← mk_const decl,
    ty ← infer_type e,
    param ← norm_cast_attr.get_param decl,
    l ← param <|> classify_type ty,
    when (l ≠ elim) $ simp_attr.push_cast.set decl () tt),
  before_unset := some $ λ _ _, tactic.skip,
  cache_cfg := { mk_cache := mk_cache norm_cast_attr, dependencies := [] } }

/-- Classify a declaration as a `norm_cast` rule. -/
meta def make_guess (decl : name) : tactic label :=
do
  e ← mk_const decl,
  ty ← infer_type e,
  classify_type ty

/--
Gets the `norm_cast` classification label for a declaration. Applies the
override specified on the attribute, if necessary.
-/
meta def get_label (decl : name) : tactic label :=
do
  param ← norm_cast_attr.get_param decl,
  param <|> make_guess decl

end norm_cast

namespace tactic.interactive
open tactic interactive tactic.interactive interactive.types expr lean.parser
open norm_cast

/--
`push_cast` rewrites the expression to move casts toward the leaf nodes.
For example, `↑(a + b)` will be written to `↑a + ↑b`.
Equivalent to `simp only with push_cast`.
Can also be used at hypotheses.
-/
meta def push_cast (l : parse location): tactic unit :=
tactic.interactive.simp none tt [] [`push_cast] l

end tactic.interactive

namespace norm_cast
open tactic expr

/-- Prove `a = b` by simplifying using move and squash lemmas. -/
meta def aux_down (a b : expr) : tactic expr :=
do
  h ← to_expr ``(%%a = %%b),
  cache ← norm_cast_attr.get_cache,
  s ← simp_lemmas.mk_default, --TODO: only use norm_cast lemmas.
  let s := simp_lemmas.join s cache.down,
  (_, pr) ← simplify s [] h,
  some (_, tmp) ← expr.is_eq <$> infer_type pr,
  is_def_eq tmp `(true) reducible,
  to_expr ``(eq.mpr %%pr trivial)

/--
This is the main heuristic used alongside the elim and move lemmas.
The goal is to help casts move past operators by adding intermediate casts.
An expression of the shape: op (↑(x : α) : γ) (↑(y : β) : γ)
is rewritten to:            op (↑(↑(x : α) : β) : γ) (↑(y : β) : γ)
when (↑(↑(x : α) : β) : γ) = (↑(x : α) : γ) can be proven with a squash lemma
-/
meta def splitting_procedure : expr → tactic (unit × expr × expr)
| (app (app op x) y) :=
(do
  `(@coe %%α %%δ %%coe1 %%xx) ← return x,
  `(@coe %%β %%γ %%coe2 %%yy) ← return y,
  success_if_fail $ is_def_eq α β,
  is_def_eq δ γ,

  (do
    coe3 ← mk_app `has_lift_t [α, β] >>= mk_instance',
    new_x ← to_expr ``(@coe %%β %%δ %%coe2 (@coe %%α %%β %%coe3 %%xx)),
    let new_e := app (app op new_x) y,
    eq_x ← aux_down x new_x,
    pr ← mk_congr_arg op eq_x,
    pr ← mk_congr_fun pr y,
    return ((), new_e, pr)
  ) <|> (do
    coe3 ← mk_app `has_lift_t [β, α] >>= mk_instance',
    new_y ← to_expr ``(@coe %%α %%δ %%coe1 (@coe %%β %%α %%coe3 %%yy)),
    let new_e := app (app op x) new_y,
    eq_y ← aux_down y new_y,
    pr ← mk_congr_arg (app op x) eq_y,
    return ((), new_e, pr)
  )
) <|> (do
  `(@coe %%α %%β %%coe1 %%xx) ← return x,
  `(@has_one.one %%β %%h1) ← return y,
  h2 ← to_expr ``(has_one %%α) >>= mk_instance',
  new_y ← to_expr ``(@coe %%α %%β %%coe1 (@has_one.one %%α %%h2)),
  eq_y ← aux_down y new_y,
  let new_e := app (app op x) new_y,
  pr ← mk_congr_arg (app op x) eq_y,
  return ((), new_e, pr)
 ) <|> (do
  `(@coe %%α %%β %%coe1 %%xx) ← return x,
  `(@has_zero.zero %%β %%h1) ← return y,
  h2 ← to_expr ``(has_zero %%α) >>= mk_instance',
  new_y ← to_expr ``(@coe %%α %%β %%coe1 (@has_zero.zero %%α %%h2)),
  eq_y ← aux_down y new_y,
  let new_e := app (app op x) new_y,
  pr ← mk_congr_arg (app op x) eq_y,
  return ((), new_e, pr)
) <|> (do
  `(@has_one.one %%β %%h1) ← return x,
  `(@coe %%α %%β %%coe1 %%xx) ← return y,
  h1 ← to_expr ``(has_one %%α) >>= mk_instance',
  new_x ← to_expr ``(@coe %%α %%β %%coe1 (@has_one.one %%α %%h1)),
  eq_x ← aux_down x new_x,
  let new_e := app (app op new_x) y,
  pr ← mk_congr_arg (lam `x binder_info.default β (app (app op (var 0)) y)) eq_x,
  return ((), new_e, pr)
) <|> (do
  `(@has_zero.zero %%β %%h1) ← return x,
  `(@coe %%α %%β %%coe1 %%xx) ← return y,
  h1 ← to_expr ``(has_zero %%α) >>= mk_instance',
  new_x ← to_expr ``(@coe %%α %%β %%coe1 (@has_zero.zero %%α %%h1)),
  eq_x ← aux_down x new_x,
  let new_e := app (app op new_x) y,
  pr ← mk_congr_arg (lam `x binder_info.default β (app (app op (var 0)) y)) eq_x,
  return ((), new_e, pr)
)
| _ := failed

/--
assumption is used to discharge proofs in step 2
TODO: norm_cast takes a list of expressions to use as lemmas for the discharger
TODO: a tactic to print the results the discharger fails to proove
-/
private meta def prove : tactic unit := assumption

/--
This is an auxiliary function used in step 2.
It tries to rewrite an expression using the elim and move lemmas.
On failure, it calls the splitting procedure heuristic.
-/
@[nolint unused_arguments] -- unused `unit` argument required by simplify
meta def post (s : simp_lemmas) (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
(do
  r ← mcond (is_prop e) (return `iff) (return `eq),
  (new_e, pr) ← s.rewrite e prove r,
  pr ← match r with
  | `iff := mk_app `propext [pr]
  | _    := return pr
  end,
  return ((), new_e, pr)
) <|> splitting_procedure e

/-!
The following auxiliary functions are used to handle numerals.
-/

/-- if possible, rewrite (n : α) to ((n : ℕ) : α) where n is a numeral and α ≠ ℕ -/
@[nolint unused_arguments] -- unused `unit` argument required by simplify
meta def aux_num_1 (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
do
  α ← infer_type e,
  success_if_fail $ is_def_eq α `(ℕ),
  n ← e.to_nat,
  h1 ← mk_app `has_lift_t [`(ℕ), α] >>= mk_instance',
  new_e ← expr.of_nat `(ℕ) n,
  new_e ← to_expr ``(@coe ℕ %%α %%h1 %%new_e),
  pr ← aux_down e new_e,
  return ((), new_e, pr)

/-- if possible, rewrite (↑n : α) to (n : α) where n is a numeral -/
@[nolint unused_arguments] -- unused `unit` argument required by simplify
meta def aux_num_2 (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
do
  `(@coe ℕ %%α %%h1 %%e') ← return e,
  n ← e'.to_nat,
  new_e ← expr.of_nat α n,
  h ← to_expr ``(%%e = %%new_e),
  pr ← aux_down e new_e,
  return ((), new_e, pr)

/-- A local variant on `simplify_top_down`. -/
private meta def simplify_top_down' {α} (a : α) (pre : α → expr → tactic (α × expr × expr))
  (e : expr) (cfg : simp_config := {}) : tactic (α × expr × expr) :=
ext_simplify_core a cfg simp_lemmas.mk (λ _, failed)
  (λ a _ _ _ e, do
    (new_a, new_e, pr) ← pre a e,
    guard (¬ new_e =ₐ e),
    return (new_a, new_e, some pr, ff))
  (λ _ _ _ _ _, failed)
  `eq e

/--
The core simplification routine of `norm_cast`.
-/
meta def derive (e : expr) : tactic (expr × expr) :=
do
  cache ← norm_cast_attr.get_cache,
  e ← instantiate_mvars e,
  let cfg : simp_config := {
    zeta := ff,
    beta := ff,
    eta  := ff,
    proj := ff,
    iota := ff,
    iota_eqn := ff,
    fail_if_unchanged := ff },
  let e0 := e,

  -- step 1: pre-processing of numerals
  ((), e1, pr1) ← simplify_top_down' () aux_num_1 e0 cfg,

  -- step 2: casts are moved upwards and eliminated
  let s2 := cache.up,
  ((), e2, pr2) ← simplify_bottom_up () (post s2) e1 cfg,

  -- step 3: casts are squashed
  let s3 := cache.squash,
  (e3, pr3) ← simplify s3 [] e2 cfg,

  -- step 4: post-processing of numerals
  ((), e4, pr4) ← simplify_top_down' () aux_num_2 e3 cfg,

  let new_e := e3,
  guard (¬ new_e =ₐ e),
  pr ← mk_eq_trans pr1 pr2,
  pr ← mk_eq_trans pr pr3,
  pr ← mk_eq_trans pr pr4,
  return (new_e, pr)

end norm_cast

namespace tactic
open tactic expr
open norm_cast

/-- `aux_mod_cast e` runs `norm_cast` on `e` and returns the result. If `include_goal` is true, it
also normalizes the goal. -/
meta def aux_mod_cast (e : expr) (include_goal : bool := tt) : tactic expr :=
match e with
| local_const _ lc _ _ := do
  e ← get_local lc,
  replace_at derive [e] include_goal,
  get_local lc
| e := do
  t ← infer_type e,
  e ← assertv `this t e,
  replace_at derive [e] include_goal,
  get_local `this
end

/-- `exact_mod_cast e` runs `norm_cast` on the goal and `e`, and tries to use `e` to close the goal. -/
meta def exact_mod_cast (e : expr) : tactic unit :=
(do
  new_e ← aux_mod_cast e,
  exact new_e
) <|> fail "exact_mod_cast failed"

/-- `apply_mod_cast e` runs `norm_cast` on the goal and `e`, and tries to apply `e`. -/
meta def apply_mod_cast (e : expr) : tactic (list (name × expr)) :=
(do
  new_e ← aux_mod_cast e,
  apply new_e
) <|> fail "apply_mod_cast failed"

/-- `assumption_mod_cast` runs `norm_cast` on the goal. For each local hypothesis `h`, it also
normalizes `h` and tries to use that to close the goal. -/
meta def assumption_mod_cast : tactic unit :=
do {
  let cfg : simp_config := {
    fail_if_unchanged := ff,
    canonize_instances := ff,
    canonize_proofs := ff,
    proj := ff
  },
  replace_at derive [] tt,
  ctx ← local_context,
  try_lst $ ctx.map (λ h, aux_mod_cast h ff >>= tactic.exact)
} <|> fail "assumption_mod_cast failed"

end tactic

namespace tactic.interactive
open tactic interactive tactic.interactive interactive.types expr lean.parser
open norm_cast

local postfix `?`:9001 := optional

/--
Normalize casts at the given locations by moving them "upwards".
As opposed to simp, norm_cast can be used without necessarily closing the goal.
-/
meta def norm_cast (loc : parse location) : tactic unit :=
do
  ns ← loc.get_locals,
  tt ← replace_at derive ns loc.include_goal | fail "norm_cast failed to simplify",
  when loc.include_goal $ try tactic.reflexivity,
  when loc.include_goal $ try tactic.triv,
  when (¬ ns.empty) $ try tactic.contradiction

/--
Rewrite with the given rules and normalize casts between steps.
-/
meta def rw_mod_cast (rs : parse rw_rules) (loc : parse location) : tactic unit :=
(do
  let cfg_norm : simp_config := {},
  let cfg_rw : rewrite_cfg := {},
  ns ← loc.get_locals,
  monad.mapm' (λ r : rw_rule, do
    save_info r.pos,
    replace_at derive ns loc.include_goal,
    rw ⟨[r], none⟩ loc {}
  ) rs.rules,
  replace_at derive ns loc.include_goal,
  skip
) <|> fail "rw_mod_cast failed"

/--
Normalize the goal and the given expression, then close the goal with exact.
-/
meta def exact_mod_cast (e : parse texpr) : tactic unit :=
do
  e ← i_to_expr e <|> do {
    ty ← target,
    e ← i_to_expr_strict ``(%%e : %%ty),
    pty ← pp ty, ptgt ← pp e,
    fail ("exact_mod_cast failed, expression type not directly " ++
    "inferrable. Try:\n\nexact_mod_cast ...\nshow " ++
    to_fmt pty ++ ",\nfrom " ++ ptgt : format)
  },
  tactic.exact_mod_cast e

/--
Normalize the goal and the given expression, then apply the expression to the goal.
-/
meta def apply_mod_cast (e : parse texpr) : tactic unit :=
do
  e ← i_to_expr_for_apply e,
  concat_tags $ tactic.apply_mod_cast e

/--
Normalize the goal and every expression in the local context, then close the goal with assumption.
-/
meta def assumption_mod_cast : tactic unit :=
tactic.assumption_mod_cast

end tactic.interactive

namespace conv.interactive
open conv tactic tactic.interactive interactive interactive.types
open norm_cast (derive)

/-- the converter version of `norm_cast' -/
meta def norm_cast : conv unit := replace_lhs derive

end conv.interactive

-- lemmas defined in core
attribute [norm_cast] int.coe_nat_zero
attribute [norm_cast] int.coe_nat_one
attribute [norm_cast] int.nat_abs_of_nat
attribute [norm_cast] int.coe_nat_succ
attribute [norm_cast] int.coe_nat_add
attribute [norm_cast] int.coe_nat_sub
attribute [norm_cast] int.coe_nat_mul

-- TODO: move this elsewhere?
@[norm_cast] lemma ite_cast {α β : Type} [has_coe α β]
  {c : Prop} [decidable c] {a b : α} :
  ↑(ite c a b) = ite c (↑a : β) (↑b : β) :=
by by_cases h : c; simp [h]

namespace norm_cast

open tactic expr label

/- scripts to compare two classifiers -/
-- they are meant to be used before an update of the classifier,
-- to make sure nothing is mislabeled
-- for instance, this command compare the classifiers with and without the manual overwrite
--run_cmd test_classifiers make_guess get_label

/-- a type to store the test results -/
@[derive inhabited]
inductive test_result : Type
| agree     : name → label → test_result         -- classifiers make same guess
| disagree  : name → label → label → test_result -- classifiers make different guesses
| progress  : name → label → test_result         -- first classifier fails
| failure   : name → option label → test_result  -- second classifier fails

open test_result

/-- output the name of tested declaration -/
def get_decl : test_result → name
| (agree n _)      := n
| (disagree n _ _) := n
| (progress n _)   := n
| (failure n _)    := n

/-- output the label given by the first classifier -/
def get_first : test_result → option label
| (agree _ l)      := some l
| (disagree _ l _) := some l
| (progress _ _)   := none
| (failure _ ol)   := ol

/-- output the label given by the second classifier -/
def get_second : test_result → option label
| (agree _ l)      := some l
| (disagree _ _ l) := some l
| (progress _ l)   := some l
| (failure _ _)    := none

/-- convert `test_result' into `string' -/
protected def test_result.to_string (tr : test_result) : string :=
"#check @" ++ to_string (get_decl tr)
++ "\n  -- first:  " ++ to_string (get_first tr)
++ "\n  -- second: " ++ to_string (get_second tr)

instance test_result.has_to_string : has_to_string test_result := ⟨test_result.to_string⟩

/-- a basic structure used to sort test results -/
@[derive inhabited]
structure test_cache : Type :=
(a : list test_result) -- agree
(b : list test_result) -- disagree
(c : list test_result) -- progress
(d : list test_result) -- failure

/-- insert a test result into the structure -/
def aux : test_cache → test_result → test_cache
| ⟨a, b, c, d⟩ r := match r with
| (agree _ _)      := ⟨r::a, b, c, d⟩
| (disagree _ _ _) := ⟨a, r::b, c, d⟩
| (progress _ _)   := ⟨a, b, r::c, d⟩
| (failure _ _)    := ⟨a, b, c, r::d⟩
end

/-- run classifiers `f' and `g' on `decl' and output the result -/
meta def test_decl (f g : name → tactic label) (decl : name) : tactic test_result :=
do
  first_guess ← (some <$> f decl) <|> return none,
  second_guess ← (some <$> g decl) <|> return none,
  return $ match (first_guess, second_guess) with
  | (some a, some b) := if a = b then agree decl a else disagree decl a b
  | (_, some l) := progress decl l
  | (_, none) := failure decl first_guess
  end

/-- run classifiers `f' and `g' on all lemmas with the `norm_cast' attribute and print the results -/
meta def test_classifiers (f g : name → tactic label) : tactic unit :=
do
  decls ← attribute.get_instances `norm_cast,
  res ← monad.mapm (test_decl f g) decls,
  let ⟨l1, l2, l3, l4⟩ := list.foldl aux ⟨[], [], [], []⟩ res,
  trace "\n/- classifiers disagree -/",
  monad.mapm (trace ∘ to_string) l2,
  trace "\n/- firt classifier can't guess -/",
  monad.mapm (trace ∘ to_string) l3,
  trace "\n/- second classifier can't guess -/",
  monad.mapm (trace ∘ to_string) l4,
  trace "\n/- classifiers agree -/",
  monad.mapm (trace ∘ to_string) l1,
  skip

end norm_cast

add_hint_tactic "norm_cast at *"

/--
The `norm_cast` family of tactics is used to normalize casts inside expressions.
It is basically a simp tactic with a specific set of lemmas to move casts
upwards in the expression.
Therefore it can be used more safely as a non-terminating tactic.
It also has special handling of numerals.

For instance, given an assumption
```lean
a b : ℤ
h : ↑a + ↑b < (10 : ℚ)
```

writing `norm_cast at h` will turn `h` into
```lean
h : a + b < 10
```

You can also use `exact_mod_cast`, `apply_mod_cast`, `rw_mod_cast`
or `assumption_mod_cast`.
Writing `exact_mod_cast h` and `apply_mod_cast h` will normalize the goal and h before using `exact h` or `apply h`.
Writing `assumption_mod_cast` will normalize the goal and for every
expression `h` in the context it will try to normalize `h` and use
`exact h`.
`rw_mod_cast` acts like the `rw` tactic but it applies `norm_cast` between steps.

`push_cast` rewrites the expression to move casts toward the leaf nodes.
This uses `norm_cast` lemmas in the forward direction.
For example, `↑(a + b)` will be written to `↑a + ↑b`.
It is equivalent to `simp only with push_cast`, and can also be used at hypotheses
with `push_cast at h`.
-/
add_tactic_doc
{ name := "norm_cast",
  category   := doc_category.tactic,
  decl_names := [``tactic.interactive.norm_cast, ``tactic.interactive.rw_mod_cast,
                 ``tactic.interactive.apply_mod_cast, ``tactic.interactive.assumption_mod_cast,
                 ``tactic.interactive.exact_mod_cast, ``tactic.interactive.push_cast],
  tags       := ["coercions", "simplification"] }

/--
The `norm_cast` attribute should be given to lemmas that describe the
behaviour of a coercion in regard to an operator, a relation, or a particular
function.
It only concerns lemmas involving `↑`, `⇑` and `↥`, and not the explicit
functions that define the coercions.

Examples:
```lean
@[norm_cast] theorem coe_nat_inj' {m n : ℕ} : (↑m : ℤ) = ↑n ↔ m = n

@[norm_cast] theorem coe_int_denom (n : ℤ) : (n : ℚ).denom = 1

@[norm_cast] theorem cast_id : ∀ n : ℚ, ↑n = n

@[norm_cast] theorem coe_nat_add (m n : ℕ) : (↑(m + n) : ℤ) = ↑m + ↑n

@[norm_cast] theorem cast_sub [add_group α] [has_one α] {m n} (h : m ≤ n) : ((n - m : ℕ) : α) = n - m

@[norm_cast] theorem coe_nat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n

@[norm_cast] theorem cast_coe_nat (n : ℕ) : ((n : ℤ) : α) = n

@[norm_cast] theorem cast_one : ((1 : ℚ) : α) = 1
```

TODO: more details about the different categories of lemmas?
TODO: bad examples?
-/
add_tactic_doc
{ name := "norm_cast attributes",
  category   := doc_category.attr,
  decl_names := [``norm_cast.norm_cast_attr],
  tags       := ["coercions", "simplification"] }
