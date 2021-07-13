import system.io
import tactic.lint

universe u

declare_trace tcache

open tactic

namespace tcache

/-- Generic pure error function. -/
meta def error {α : Sort u} (message : string) : α := undefined_core message

section io

/-- The cache directory name (placed in the project root directory). -/
def CACHE_DIR := ".cache"

/-- `mk_cache_dir` creates the cache directory if it does not exist. -/
def mk_cache_dir : io unit :=
io.proc.spawn {
  cmd := "mkdir",
  args := ["-p", CACHE_DIR],
  stdout := io.process.stdio.null,
  stderr := io.process.stdio.null
} >> return ()

/-- `rm_cache_dir` removes the cache directory and its contents if it exists. -/
def rm_cache_dir : io unit :=
io.proc.spawn {
  cmd := "rm",
  args := ["-rf", CACHE_DIR],
  stdout := io.process.stdio.null,
  stderr := io.process.stdio.null
} >> return ()

/-- `init_tcache` makes sure the `tcache` is ready to function. -/
meta def init_tcache : tactic unit := tactic.unsafe_run_io mk_cache_dir

/-- `clear_tcache` erases the `tcache`. -/
meta def clear_tcache : tactic unit := tactic.unsafe_run_io rm_cache_dir

end io

section
open interaction_monad

/-- Evaluate the passed error message thunk. -/
private meta def eval_msg : option (unit → format) → string
| none := ""
| (some e) := to_string $ e ()

/-- Variant of `interaction_monad_orelse` which passes the error message string to the backup
tactic. -/
meta def interaction_monad_orelse' {α : Type u} (t₁ : tactic α) (t₂ : string → tactic α) : tactic α :=
λ s, result.cases_on (t₁ s)
  result.success
  (λ e ref₁ s', result.cases_on (t₂ (eval_msg e) s)
    result.success
    result.exception
  )

end

/-- The `tcache`-internal tracing function. -/
meta def trace {α : Type u} [has_to_tactic_format α] (hash : string) (a : thunk α) : tactic unit := do
  f ← has_to_tactic_format.to_tactic_format $ a (),
  when_tracing `tcache $ tactic.trace $ format!"tc@{hash} - {f}"

/-- The `tcache`-internal pure timing function. -/
meta def timeit {α : Type u} (hash s : string) (f : thunk α) : α :=
if is_trace_enabled_for `tcache then _root_.timeit sformat!"tc@{hash} - {s}" (f ())
else f ()

/-- The `tcache`-internal tactic timing function. -/
meta def timetac {α : Type u} (hash s : string) (f : thunk (tactic α)) : tactic α :=
if is_trace_enabled_for `tcache then tactic.timetac sformat!"tc@{hash} - {s}" (f ())
else f ()

/-- Remove all nondeterministic elements from the given `expr`. -/
meta def sanitize_expr : expr → expr
| (expr.const n l) := expr.const n l
| (expr.app f a) := expr.app (sanitize_expr f) (sanitize_expr a)
| (expr.sort l) := expr.sort l
| (expr.pi n bi t v) := expr.pi n bi (sanitize_expr t) (sanitize_expr v)
| (expr.lam n bi t v) := expr.lam n bi (sanitize_expr t) (sanitize_expr v)
| (expr.var n) := expr.var n
| (expr.local_const n₁ n₂ bi v) := expr.local_const n₂ n₂ bi (sanitize_expr v)
| (expr.mvar _ _ _) := expr.const name.anonymous []
| (expr.macro m _) := expr.const (expr.macro_def_name m) [] -- Do something with the `expr` list?
| (expr.elet n e₁ e₂ e₃) := expr.elet n (sanitize_expr e₁) (sanitize_expr e₂) (sanitize_expr e₃)

/-- Compute a hash of the type of the metavariable `e`. -/
meta def hash_goal (e : expr) : tactic ℕ := do
  t ← infer_type e,
  return $ (sanitize_expr t).hash

/-- Hash all of the goals, in the scope of the declaration `n`. -/
meta def hash_goals (n : name) : tactic string := do
  -- FIXME this xor is probably really slow
  v ← get_goals >>= list.mfoldl (λ v d, nat.lxor v <$> hash_goal d) 0,
  return sformat!"{n}.{v}"

/-- Convert a hash to the name of a cache file. -/
meta def cache_file_name (hash : string) : string :=
CACHE_DIR ++ "/" ++ hash ++ ".leancache"

/-- Final a local constant by pretty-name in a list of local constants. -/
meta def find_local_const (n : name) : list expr → expr
| [] := error sformat!"unknown const {n}"
| (e :: rest) :=
  if e.local_pp_name = n then e else find_local_const rest

/-- Use the list `lc` to replace the local constants we find in the passed `expr` by matching pretty
name; meant to be passed to `expr.replace`, thus we don't use the `ℕ` argument. -/
@[nolint unused_arguments]
meta def fixup_local_consts (lc : list expr) : expr → ℕ → option expr
| (expr.local_const _ n _ _) _ := some $ find_local_const n lc
| _ _ := none

variables (hash : string)

/-- Close the goal with `pf` and assert that there are no more goals. -/
meta def solve_goal (pf : expr) : tactic unit := exact pf >> done

/-- Load and deserialise a proof of the expr with the passed `hash : string`. -/
meta def deserialise_proof : io expr := do
  h ← io.mk_file_handle (cache_file_name hash) io.mode.read tt,
  pf ← io.deserialize h,
  io.fs.close h,
  return pf

/-- Serialise a proof of the expr with the passed `hash : string`, and store it. -/
meta def serialise_proof (e : expr) : tactic unit :=
unsafe_run_io $ do {
  h ← io.mk_file_handle (cache_file_name hash) io.mode.write tt,
  io.serialize h e,
  io.fs.close h
}

/-- Report an error message (if enabled) if we could not recall a proof of an `expr`, given that
we were actually able to load the cached proof. -/
meta def handle_recall_failed (pf : expr) (msg : string) : tactic unit := do
  s₂ ← infer_type pf,
  trace hash sformat!"failed to recall proof: {msg}\n\n{pf.to_raw_fmt}\n\n{s₂.to_raw_fmt}"

/-- Search the cache for a proof with the given hash in the context of the declaration with name
`n`, closing the current goal with this proof if found. -/
meta def try_cache (lc : list expr) : tactic unit := do
  pf ← timetac hash "deserialising proof" $ unsafe_run_io $ deserialise_proof hash,
  let pf := timeit hash "loading proof took" (pf.replace $ fixup_local_consts lc),
  interaction_monad_orelse' (solve_goal pf) (handle_recall_failed hash pf)

/-- Add `e : expr` to the cache, assinging the passed `hash : string`. -/
meta def put_cache (e : expr) : tactic unit := do
  interaction_monad_orelse' (serialise_proof hash e) $ λ msg,
  interaction_monad_orelse' (init_tcache >> serialise_proof hash e) $ λ _,
  trace hash sformat!"proof serialisation failure: {msg}\n\n{e}\n\n{e.to_raw_fmt}"

/-- Given that there is exactly one goal, close the goal with `t : tactic unit` and return the value
of the assigned goal metavariable. -/
meta def execute_capture (t : tactic unit) : tactic expr := do
  [m] ← get_goals,
  t >> done,
  instantiate_mvars m

/-- Try to recompute the cache entry for the given `hash : string` using `t : tactic unit`, saving
the result back to the cache on success. -/
meta def try_recompute (t : tactic unit) : tactic unit := do
  trace hash "need to regenerate proof",
  e ← timetac hash "success, took" $ execute_capture t,
  put_cache hash e

/-- Main entry-point. Attempts to discharge the current goals using the cache, resorting to running
`t : tactic unit` (and saving the result) on failure. -/
meta def discharge_goals (t : tactic unit) : tactic unit := do
  hash ← decl_name >>= hash_goals,
  lc ← local_context,
  try_cache hash lc <|> try_recompute hash t

end tcache
