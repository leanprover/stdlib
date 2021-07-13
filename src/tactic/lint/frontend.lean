/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
import tactic.lint.basic

/-!
# Linter frontend and commands

This file defines the linter commands which spot common mistakes in the code.
* `#lint`: check all declarations in the current file
* `#lint_mathlib`: check all declarations in mathlib (so excluding core or other projects,
  and also excluding the current file)
* `#lint_all`: check all declarations in the environment (the current file and all
  imported files)

For a list of default / non-default linters, see the "Linting Commands" user command doc entry.

The command `#list_linters` prints a list of the names of all available linters.

You can append a `*` to any command (e.g. `#lint_mathlib*`) to omit the slow tests (4).

You can append a `-` to any command (e.g. `#lint_mathlib-`) to run a silent lint
that suppresses the output if all checks pass.
A silent lint will fail if any test fails.

You can append a `+` to any command (e.g. `#lint_mathlib+`) to run a verbose lint
that reports the result of each linter, including  the successes.

You can append a sequence of linter names to any command to run extra tests, in addition to the
default ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.

You can append `only name1 name2 ...` to any command to run a subset of linters, e.g.
`#lint only unused_arguments`

You can add custom linters by defining a term of type `linter` in the `linter` namespace.
A linter defined with the name `linter.my_new_check` can be run with `#lint my_new_check`
or `lint only my_new_check`.
If you add the attribute `@[linter]` to `linter.my_new_check` it will run by default.

Adding the attribute `@[nolint doc_blame unused_arguments]` to a declaration
omits it from only the specified linter checks.

## Tags

sanity check, lint, cleanup, command, tactic
-/

open tactic expr native
setup_tactic_parser

/--
Verbosity for the linter output.
* `low`: only print failing checks, print nothing on success.
* `medium`: only print failing checks, print confirmation on success.
* `high`: print output of every check.
-/
@[derive [decidable_eq, inhabited]]
inductive lint_verbosity | low | medium | high

/-- `get_checks slow extra use_only` produces a list of linters.
`extras` is a list of names that should resolve to declarations with type `linter`.
If `use_only` is true, it only uses the linters in `extra`.
Otherwise, it uses all linters in the environment tagged with `@[linter]`.
If `slow` is false, it only uses the fast default tests. -/
meta def get_checks (slow : bool) (extra : list name) (use_only : bool) :
  tactic (list (name × linter)) := do
  default ← if use_only then return [] else attribute.get_instances `linter >>= get_linters,
  let default := if slow then default else default.filter (λ l, l.2.is_fast),
  list.append default <$> get_linters extra

/--
`lint_core all_decls non_auto_decls checks` applies the linters `checks` to the list of
declarations.
If `auto_decls` is false for a linter (default) the linter is applied to `non_auto_decls`.
If `auto_decls` is true, then it is applied to `all_decls`.
The resulting list has one element for each linter, containing the linter as
well as a map from declaration name to warning.
-/
meta def lint_core (all_decls non_auto_decls : list declaration) (checks : list (name × linter)) :
  tactic (list (name × linter × rb_map name string)) := do
checks.mmap $ λ ⟨linter_name, linter⟩, do
  let test_decls := if linter.auto_decls then all_decls else non_auto_decls,
  test_decls ← test_decls.mfilter (λ decl, should_be_linted linter_name decl.to_name),
  s ← read,
  let results := test_decls.map_async $ λ decl, prod.mk decl.to_name $
      match linter.test decl s with
      | result.success w _ := w
      | result.exception msg _ _ :=
        some $ "LINTER FAILED:\n" ++ msg.elim "(no message)" (λ msg, to_string $ msg ())
      end,
  let results := results.foldl (λ (results : rb_map name string) warning,
    match warning with
    | (decl_name, some w) := results.insert decl_name w
    | (_, none) := results
    end) mk_rb_map,
  pure (linter_name, linter, results)

/-- Sorts a map with declaration keys as names by line number. -/
meta def sort_results {α} (e : environment) (results : rb_map name α) : list (name × α) :=
list.reverse $ rb_lmap.values $ rb_lmap.of_list $
  results.fold [] $ λ decl linter_warning results,
    (((e.decl_pos decl).get_or_else ⟨0,0⟩).line, (decl, linter_warning)) :: results

/-- Formats a linter warning as `#print` command with comment. -/
meta def print_warning (decl_name : name) (warning : string) : format :=
"#print " ++ to_fmt decl_name ++ " /- " ++ warning ++ " -/"

/-- Formats a map of linter warnings using `print_warning`, sorted by line number. -/
meta def print_warnings (env : environment) (results : rb_map name string) : format :=
format.intercalate format.line $ (sort_results env results).map $
  λ ⟨decl_name, warning⟩, print_warning decl_name warning

/--
Formats a map of linter warnings grouped by filename with `-- filename` comments.
The first `drop_fn_chars` characters are stripped from the filename.
-/
meta def grouped_by_filename (e : environment) (results : rb_map name string) (drop_fn_chars := 0)
  (formatter: rb_map name string → format) : format :=
let results := results.fold (rb_map.mk string (rb_map name string)) $
  λ decl_name linter_warning results,
    let fn := (e.decl_olean decl_name).get_or_else "" in
    results.insert fn (((results.find fn).get_or_else mk_rb_map).insert
      decl_name linter_warning) in
let l := results.to_list.reverse.map (λ ⟨fn, results⟩,
  ("-- " ++ fn.popn drop_fn_chars ++ "\n" ++ formatter results : format)) in
format.intercalate "\n\n" l ++ "\n"

/--
Formats the linter results as Lean code with comments and `#print` commands.
-/
meta def format_linter_results
  (env : environment)
  (results : list (name × linter × rb_map name string))
  (decls non_auto_decls : list declaration)
  (group_by_filename : option nat)
  (where_desc : string) (slow : bool) (verbose : lint_verbosity) :
  format := do
let formatted_results := results.map $ λ ⟨linter_name, linter, results⟩,
  let report_str : format := to_fmt "/- The `" ++ to_fmt linter_name ++ "` linter reports: -/\n" in
  if ¬ results.empty then
    let warnings := match group_by_filename with
      | none := print_warnings env results
      | some dropped := grouped_by_filename env results dropped (print_warnings env)
      end in
    report_str ++ "/- " ++ linter.errors_found ++ " -/\n" ++ warnings ++ "\n"
  else if verbose = lint_verbosity.high then
    "/- OK: " ++ linter.no_errors_found ++ " -/"
  else format.nil,
let s := format.intercalate "\n" (formatted_results.filter (λ f, ¬ f.is_nil)),
let s := if verbose = lint_verbosity.low then s else
  format!("/- Checking {non_auto_decls.length} declarations (plus " ++
  "{decls.length - non_auto_decls.length} automatically generated ones) {where_desc} -/\n\n") ++ s,
let s := if slow then s else s ++ "/- (slow tests skipped) -/\n",
s

/-- The common denominator of `#lint[|mathlib|all]`.
The different commands have different configurations for `l`,
`group_by_filename` and `where_desc`.
If `slow` is false, doesn't do the checks that take a lot of time.
If `verbose` is false, it will suppress messages from passing checks.
By setting `checks` you can customize which checks are performed.

Returns a `name_set` containing the names of all declarations that fail any check in `check`,
and a `format` object describing the failures. -/
meta def lint_aux (decls : list declaration) (group_by_filename : option nat)
    (where_desc : string) (slow : bool) (verbose : lint_verbosity) (checks : list (name × linter)) :
  tactic (name_set × format) := do
e ← get_env,
let non_auto_decls := decls.filter (λ d, ¬ d.is_auto_or_internal e),
results ← lint_core decls non_auto_decls checks,
let s := format_linter_results e results decls non_auto_decls
  group_by_filename where_desc slow verbose,
let ns := name_set.of_list (do (_,_,rs) ← results, rs.keys),
pure (ns, s)

/-- Return the message printed by `#lint` and a `name_set` containing all declarations that fail. -/
meta def lint (slow : bool := tt) (verbose : lint_verbosity := lint_verbosity.medium)
  (extra : list name := []) (use_only : bool := ff) : tactic (name_set × format) := do
  checks ← get_checks slow extra use_only,
  e ← get_env,
  let l := e.filter (λ d, e.in_current_file d.to_name),
  lint_aux l none "in the current file" slow verbose checks

/-- Returns the declarations considered by the mathlib linter. -/
meta def lint_mathlib_decls : tactic (list declaration) := do
e ← get_env,
ml ← get_mathlib_dir,
pure $ e.filter $ λ d, e.is_prefix_of_file ml d.to_name

/-- Return the message printed by `#lint_mathlib` and a `name_set` containing all declarations
that fail. -/
meta def lint_mathlib (slow : bool := tt) (verbose : lint_verbosity := lint_verbosity.medium)
  (extra : list name := []) (use_only : bool := ff) : tactic (name_set × format) := do
checks ← get_checks slow extra use_only,
decls ← lint_mathlib_decls,
mathlib_path_len ← string.length <$> get_mathlib_dir,
lint_aux decls mathlib_path_len "in mathlib (only in imported files)" slow verbose checks

/-- Return the message printed by `#lint_all` and a `name_set` containing all declarations
that fail. -/
meta def lint_all (slow : bool := tt) (verbose : lint_verbosity := lint_verbosity.medium)
  (extra : list name := []) (use_only : bool := ff) : tactic (name_set × format) := do
  checks ← get_checks slow extra use_only,
  e ← get_env,
  let l := e.get_decls,
  lint_aux l (some 0) "in all imported files (including this one)" slow verbose checks

/-- Parses an optional `only`, followed by a sequence of zero or more identifiers.
Prepends `linter.` to each of these identifiers. -/
private meta def parse_lint_additions : parser (bool × list name) :=
prod.mk <$> only_flag <*> (list.map (name.append `linter) <$> ident_*)

/--
Parses a "-" or "+", returning `lint_verbosity.low` or `lint_verbosity.high` respectively,
or returns `none`.
-/
private meta def parse_verbosity : parser (option lint_verbosity) :=
tk "-" >> return lint_verbosity.low <|>
tk "+" >> return lint_verbosity.high <|>
return none

/-- The common denominator of `lint_cmd`, `lint_mathlib_cmd`, `lint_all_cmd` -/
private meta def lint_cmd_aux
  (scope : bool → lint_verbosity → list name → bool → tactic (name_set × format)) :
  parser unit :=
do verbosity ← parse_verbosity,
   fast_only ← optional (tk "*"),
   -- allow either order of *-
   verbosity ← if verbosity.is_some then return verbosity else parse_verbosity,
   let verbosity := verbosity.get_or_else lint_verbosity.medium,
   (use_only, extra) ← parse_lint_additions,
   (failed, s) ← scope fast_only.is_none verbosity extra use_only,
   when (¬ s.is_nil) $ trace s,
   when (verbosity = lint_verbosity.low ∧ ¬ failed.empty) $
    fail "Linting did not succeed",
   when (verbosity = lint_verbosity.medium ∧ failed.empty) $
    trace "/- All linting checks passed! -/"

/-- The command `#lint` at the bottom of a file will warn you about some common mistakes
in that file. Usage: `#lint`, `#lint linter_1 linter_2`, `#lint only linter_1 linter_2`.
`#lint-` will suppress the output if all checks pass.
`#lint+` will enable verbose output.

Use the command `#list_linters` to see all available linters. -/
@[user_command] meta def lint_cmd (_ : parse $ tk "#lint") : parser unit :=
lint_cmd_aux @lint

/-- The command `#lint_mathlib` checks all of mathlib for certain mistakes.
Usage: `#lint_mathlib`, `#lint_mathlib linter_1 linter_2`, `#lint_mathlib only linter_1 linter_2`.
`#lint_mathlib-` will suppress the output if all checks pass.
`lint_mathlib+` will enable verbose output.

Use the command `#list_linters` to see all available linters. -/
@[user_command] meta def lint_mathlib_cmd (_ : parse $ tk "#lint_mathlib") : parser unit :=
lint_cmd_aux @lint_mathlib

/-- The command `#lint_all` checks all imported files for certain mistakes.
Usage: `#lint_all`, `#lint_all linter_1 linter_2`, `#lint_all only linter_1 linter_2`.
`#lint_all-` will suppress the output if all checks pass.
`lint_all+` will enable verbose output.

Use the command `#list_linters` to see all available linters. -/
@[user_command] meta def lint_all_cmd (_ : parse $ tk "#lint_all") : parser unit :=
lint_cmd_aux @lint_all

/-- The command `#list_linters` prints a list of all available linters. -/
@[user_command] meta def list_linters (_ : parse $ tk "#list_linters") : parser unit :=
do env ← get_env,
let ns := env.decl_filter_map $ λ dcl,
    if (dcl.to_name.get_prefix = `linter) && (dcl.type = `(linter)) then some dcl.to_name else none,
   trace "Available linters:\n  linters marked with (*) are in the default lint set\n",
   ns.mmap' $ λ n, do
     b ← has_attribute' `linter n,
     trace $ n.pop_prefix.to_string ++ if b then " (*)" else ""


/--
Invoking the hole command `lint` ("Find common mistakes in current file") will print text that
indicates mistakes made in the file above the command. It is equivalent to copying and pasting the
output of `#lint`. On large files, it may take some time before the output appears.
-/
@[hole_command] meta def lint_hole_cmd : hole_command :=
{ name := "Lint",
  descr := "Lint: Find common mistakes in current file.",
  action := λ es, do (_, s) ← lint, return [(s.to_string,"")] }

add_tactic_doc
{ name                     := "Lint",
  category                 := doc_category.hole_cmd,
  decl_names               := [`lint_hole_cmd],
  tags                     := ["linting"] }
