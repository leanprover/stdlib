import tactic.tcache.executor
import tactic.tcache.store

namespace tcache

open lean.parser interactive interaction_monad

/--
  `cache_file` enables caching the results of tactic-block executions present after this line.

  See `cache_clear` to clear the cache.
-/
@[user_command]
meta def cache_file_cmd (_ : parse $ tk "cache_file") : lean.parser unit :=
emit_code_here $ "local attribute [instance, priority 2000] tcache.executor"

add_tactic_doc
{ name                     := "cache_file",
  category                 := doc_category.cmd,
  decl_names               := [`tcache.cache_file_cmd],
  tags                     := ["caching", "environment"] }

/--
  `cache_file?` enables caching the results of tactic-block executions present after this line,
  tracing some performance info at the site of each cache lookup.

  See `cache_clear` to clear the cache.
-/
@[user_command]
meta def cache_file_verbose_cmd (_ : parse $ tk "cache_file?") : lean.parser unit :=
emit_code_here $ "local attribute [instance, priority 2000] tcache.executor\n"
  ++ "set_option trace.tcache true"

add_tactic_doc
{ name                     := "cache_file?",
  category                 := doc_category.cmd,
  decl_names               := [`tcache.cache_file_verbose_cmd],
  tags                     := ["caching", "environment"] }

/--
  `cache_clear` clears the entire cache over the scope of all files.
-/
@[user_command]
meta def cache_clear_cmd (_ : parse $ tk "cache_clear") : lean.parser unit := do
  n ← ident,
  match n with
  | `tcache := clear_tcache >> tactic.trace "cache cleared"
  | _ := fail "unknown item to clear"
  end

add_tactic_doc
{ name                     := "cache_clear",
  category                 := doc_category.cmd,
  decl_names               := [`tcache.cache_clear_cmd],
  tags                     := ["caching", "environment"] }

end tcache
