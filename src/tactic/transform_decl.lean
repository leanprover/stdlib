/-
Copyright (c) 2017 Mario Carneiro All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import tactic.core

namespace tactic

open expr
/-- Auxilliary function for `additive_test`. The bool argument *only* matters when applied
to exactly a constant. -/
meta def additive_test_aux (f : name → option name) (ignore : name_map $ list ℕ) :
  bool → expr → bool
| b (var n)                := tt
| b (sort l)               := tt
| b (const n ls)           := b || (f n).is_some
| b (mvar n m t)           := tt
| b (local_const n m bi t) := tt
| b (app e f)              := additive_test_aux tt e &&
  -- this might be inefficient.
  -- If it becomes a performance problem: we can give this info for the recursive call to `e`.
    match ignore.find e.get_app_fn.const_name with
    | some l := if e.get_app_num_args + 1 ∈ l then tt else additive_test_aux ff f
    | none   := additive_test_aux ff f
    end
| b (lam n bi e t)         := additive_test_aux ff t
| b (pi n bi e t)          := additive_test_aux ff t
| b (elet n g e f)         := additive_test_aux ff e && additive_test_aux ff f
| b (macro d args)         := tt

/--
`additive_test f replace_all ignore e` tests whether the expression `e` contains no constant
`nm` that is not applied to any arguments, and such that `f nm = none`.
This is used in `@[to_additive]` for deciding which subexpressions to transform: we only transform
constants if `additive_test` applied to their first argument returns `tt`.
This means we will replace expression applied to e.g. `α` or `α × β`, but not when applied to
e.g. `ℕ` or `ℝ × α`.
`f` is the dictionary of declarations that are in the `to_additive` dictionary.
We ignore all arguments specified in the `name_map` `ignore`.
If `replace_all` is `tt` the test always return `tt`.
-/
meta def additive_test (f : name → option name) (replace_all : bool) (ignore : name_map $ list ℕ)
  (e : expr) : bool :=
if replace_all then tt else additive_test_aux f ignore ff e

private meta def transform_decl_with_prefix_fun_aux (f : name → option name)
  (replace_all trace : bool) (ignore reorder : name_map $ list ℕ) (pre tgt_pre : name)
  (attrs : list name) : name → command :=
λ src,
do
  let tgt := src.map_prefix (λ n, if n = pre then some tgt_pre else none),
  (get_decl tgt >> skip) <|>
  do
    decl ← get_decl src,
    (decl.type.list_names_with_prefix pre).mfold () (λ n _, transform_decl_with_prefix_fun_aux n),
    (decl.value.list_names_with_prefix pre).mfold () (λ n _, transform_decl_with_prefix_fun_aux n),
    is_protected ← is_protected_decl src,
    env ← get_env,
    let decl :=
      decl.update_with_fun env (name.map_prefix f) (additive_test f replace_all ignore) reorder tgt,
    pp_decl ← pp decl,
    when trace $ trace!"[to_additive] > generating\n{pp_decl}",
    decorate_error (format!"@[to_additive] failed. Type mismatch in additive declaration.
For help, see the docstring of `to_additive.attr`, section `Troubleshooting`.
Failed to add declaration\n{pp_decl}

Nested error message:\n").to_string $ -- empty line is intentional
      if is_protected then add_protected_decl decl else add_decl decl,
    attrs.mmap' (λ n, copy_attribute n src tgt)

/--
Make a new copy of a declaration,
replacing fragments of the names of identifiers in the type and the body using the function `f`.
This is used to implement `@[to_additive]`.
-/
meta def transform_decl_with_prefix_fun (f : name → option name) (replace_all trace : bool)
  (ignore reorder : name_map $ list ℕ) (src tgt : name) (attrs : list name) : command :=
do transform_decl_with_prefix_fun_aux f replace_all trace ignore reorder src tgt attrs src,
   ls ← get_eqn_lemmas_for tt src,
   ls.mmap' $ transform_decl_with_prefix_fun_aux f replace_all trace ignore reorder src tgt attrs

/--
Make a new copy of a declaration,
replacing fragments of the names of identifiers in the type and the body using the dictionary `dict`.
This is used to implement `@[to_additive]`.
-/
meta def transform_decl_with_prefix_dict (dict : name_map name) (replace_all trace : bool)
  (ignore reorder : name_map $ list ℕ) (src tgt : name) (attrs : list name) : command :=
transform_decl_with_prefix_fun dict.find replace_all trace ignore reorder src tgt attrs

end tactic
