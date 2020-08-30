/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/

import testing.slim_check.testable

/-!
## How to get started

A proposition can be tested by writing it out as:

```lean
#eval testable.check (∀ xs : list ℕ, (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))
-- ===================
-- Found problems!

-- xs := [0, 5]
-- x := 0
-- y := 5
-- -------------------

#eval testable.check (∀ x : ℕ, 2 ∣ x → x < 100)
-- ===================
-- Found problems!

-- x := 258
-- -------------------

#eval testable.check (∀ (α : Type) (xs ys : list α), xs ++ ys = ys ++ xs)
-- ===================
-- Found problems!

-- α := ℤ
-- xs := [-4]
-- ys := [1]
-- -------------------

#eval testable.check (∀ x ∈ [1,2,3], x < 4)
-- Success
```

`testable.check p` finds a `testable p` instance which lets us find
data to test the proposition `p`.  For instance, `testable.check (∀ x
: ℕ, 2 ∣ x → x < 100)` builds the `testable` instance step by step
with:

```
testable (∀ x : ℕ, 2 ∣ x → x < 100) -: sampleable ℕ, decidable (λ x, 2 ∣ x), testable (λ x, x < 100)
testable (λ x, x < 100)              -: decidable (λ x, x < 100)
```

`sampleable ℕ` lets us create random data of type `ℕ` in a way that
helps find small counter-examples.  Next, the test of the proposition
hinges on `2 ∣ 100` and `x < 100` to both be decidable. The
implication between the two could be tested as a whole but it would be
less informative. Indeed, we could generate a hundred odd numbers and
the property would be shown to hold for each but the right conclusion
is that we haven't found meaningful examples. Instead, when `2 ∣ x`
does not hold, we reject the example (i.e.  we do not count it toward
the 100 required positive examples) and we start over. Therefore, when
`testable.check` prints `Success`, it means that a hundred even
numbers were found to be less than 100.

### Proof tactic

`slim_check` can be used as a proof tactic. Let's consider the
following proof goal.

```lean
xs : list ℕ,
h : ∃ (x : ℕ) (H : x ∈ xs), x < 3
⊢ ∀ (y : ℕ), y ∈ xs → y < 5
```

The local constants will be reverted and an instance will be found for
`testable (∀ (xs : list ℕ), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))`.
The `testable` instance is supported by an instance of `sampleable (list ℕ)`,
`decidable (x < 3)` and `decidable (y < 5)`.

Examples will be creeated in ascending order of size (more or less)

The first counter-examples found will be printed and will result in an error:

```
===================
Found problems!

xs := [1, 28]
x := 1
y := 28
-------------------
```

If no counter-examples are found, `slim_check` behaves like `admit`.

For more information on writing your own `sampleable` and `testable`
instances, see `testing.slim_check.testable`.
-/

namespace tactic.interactive
open tactic slim_check

declare_trace slim_check.instance
declare_trace slim_check.decoration
declare_trace slim_check.discared
open expr

/-- Tree structure representing `testable` a instance. -/
meta inductive instance_tree
| node : name → expr → list instance_tree → instance_tree

/-- Gather information about a `testable` instance. Given
an expression of type `testable ?p`, gather the
name of the `testable` instances that it is built from
and the proposition that they test. -/
meta def summarize_instance : expr → tactic instance_tree
| (lam n bi d b) := do
   v ← mk_local' n bi d,
   summarize_instance $ b.instantiate_var v
| e@(app f x) := do
   `(testable %%p) ← infer_type e,
   xs ← e.get_app_args.mmap_filter (try_core ∘ summarize_instance),
   pure $ instance_tree.node e.get_app_fn.const_name p xs
| e := do
  failed

/-- format as `instance_tree` -/
meta def instance_tree.to_format : instance_tree → tactic format
| (instance_tree.node n p xs) := do
  xs ← format.join <$> (xs.mmap $ λ t, flip format.indent 2 <$> instance_tree.to_format t),
  ys ← pformat!"testable ({p})",
  pformat!"+ {n} :{format.indent ys 2}\n{xs}"

meta instance instance_tree.has_to_tactic_format : has_to_tactic_format instance_tree :=
⟨ instance_tree.to_format ⟩

/--
`slim_check` considers a proof goal and tries to generate examples
that would contradict the statement.

Let's consider the following proof goal.

```lean
xs : list ℕ,
h : ∃ (x : ℕ) (H : x ∈ xs), x < 3
⊢ ∀ (y : ℕ), y ∈ xs → y < 5
```

The local constants will be reverted and an instance will be found for
`testable (∀ (xs : list ℕ), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))`.
The `testable` instance is supported by an instance of `sampleable (list ℕ)`,
`decidable (x < 3)` and `decidable (y < 5)`.

Examples will be creeated in ascending order of size (more or less)

The first counter-examples found will be printed and will result in an error:

```
===================
Found problems!

xs := [1, 28]
x := 1
y := 28
-------------------
```

If no counter-examples are found, `slim_check` behaves like `admit`.

For more information on writing your own `sampleable` and `testable`
instances, see `testing.slim_check.testable`.

Optional arguments given with `slim_check_cfg`
 * num_inst (default 100): number of examples to test properties with
 * max_size (default 100): final size argument
 * enable_tracing (default ff): enable the printing of discarded samples

Options:
  * `set_option trace.slim_check.decoration true`: print the proposition with quantifier annotations
  * `set_option trace.slim_check.discared true`: print the examples discarded because they do not satisfy assumptions
  * `set_option trace.slim_check.instance true`: print the instances of `testable` being used to test the proposition
-/
meta def slim_check (cfg : slim_check_cfg := {}) : tactic unit := do
{ tgt ← retrieve $ tactic.revert_all >> target,
  let tgt' := tactic.add_decorations tgt,
  let cfg := { cfg with enable_tracing := cfg.enable_tracing || is_trace_enabled_for `slim_check.discared },
  e ← mk_mapp ``testable.check [tgt, `(cfg), tgt', none],
  `(@testable.check _ _ _ %%inst) ← pure e,
  when_tracing `slim_check.decoration trace!"[testable decoration]\n  {tgt'}",
  when_tracing `slim_check.instance   $ do
  { inst ← summarize_instance inst >>= pp,
    trace!"\n[testable instance]{format.indent inst 2}" },
  code ← eval_expr (io bool) e,
  b ← unsafe_run_io code,
  if b then admit else failed }

end tactic.interactive
