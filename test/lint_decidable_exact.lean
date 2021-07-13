import tactic.lint

-- see Note [function coercion]
lemma infered_arg {α : Type*} [inhabited α] [decidable_eq α] (x : α × α) :
  (if x = default _ then 0 else 0) = (if x = default _ then 0 else 0) :=
rfl

lemma direct_arg {α : Type*} [inhabited α] [decidable_eq (α × α)] (x : α × α) :
  (if x = default _ then 0 else 0) = (if x = default _ then 0 else 0) :=
rfl

-- should complain
open tactic

run_cmd do
  decl ← get_decl ``infered_arg,
  (some msg) ← linter.decidable_exact.test decl,
  trace msg
