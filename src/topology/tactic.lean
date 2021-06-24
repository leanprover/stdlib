/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility
import tactic.show_term
import topology.basic
/-!
# Tactics for topology

Currently we have one domain-specific tactic for topology: `continuity`.

-/

/-!
### `continuity` tactic

Automatically solve goals of the form `continuous f`.

Mark lemmas with `@[continuity]` to add them to the set of lemmas
used by `continuity`.
-/

/-- User attribute used to mark tactics used by `continuity`. -/
@[user_attribute]
meta def continuity : user_attribute :=
{ name := `continuity,
  descr := "lemmas usable to prove continuity" }

-- Mark some continuity lemmas already defined in `topology.basic`
attribute [continuity]
  continuous_id
  continuous_const

-- As we will be using `apply_rules` with `md := semireducible`,
-- we need another version of `continuous_id`.
@[continuity] lemma continuous_id' {α : Type*} [topological_space α] : continuous (λ a : α, a) :=
continuous_id

namespace tactic

/--
Tactic to apply `continuous.comp` when appropriate.

Applying `continuous.comp` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove continuous is actually
  constant, and that constant is a function application `f z`, then
  continuous.comp would produce new goals `continuous f`, `continuous
  (λ _, z)`, which is silly. We avoid this by failing if we could
  apply continuous_const.

* continuous.comp will always succeed on `continuous (λ x, f x)` and
  produce new goals `continuous (λ x, x)`, `continuous f`. We detect
  this by failing if a new goal can be closed by applying
  continuous_id.
-/
meta def apply_continuous.comp : tactic unit :=
`[fail_if_success { exact continuous_const };
  refine continuous.comp _ _;
  fail_if_success { exact continuous_id }]

/-- List of tactics used by `continuity` internally. -/
meta def continuity_tactics (md : transparency := reducible) : list (tactic string) :=
[
  intros1               >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  apply_rules [``(continuity)] 50 { md := md }
                        >> pure "apply_rules continuity",
  apply_continuous.comp >> pure "refine continuous.comp _ _"
]

namespace interactive
setup_tactic_parser

/--
Solve goals of the form `continuous f`. `continuity?` reports back the proof term it found.
-/
meta def continuity
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) :
  tactic unit :=
let md              := if bang.is_some then semireducible else reducible,
    continuity_core := tactic.tidy { tactics := continuity_tactics md, ..cfg },
    trace_fn        := if trace.is_some then show_term else id in
trace_fn continuity_core

/-- Version of `continuity` for use with auto_param. -/
meta def continuity' : tactic unit := continuity none none {}

/--
`continuity` solves goals of the form `continuous f` by applying lemmas tagged with the
`continuity` user attribute.

```
example {X Y : Type*} [topological_space X] [topological_space Y]
  (f₁ f₂ : X → Y) (hf₁ : continuous f₁) (hf₂ : continuous f₂)
  (g : Y → ℝ) (hg : continuous g) : continuous (λ x, (max (g (f₁ x)) (g (f₂ x))) + 1) :=
by continuity
```
will discharge the goal, generating a proof term like
`((continuous.comp hg hf₁).max (continuous.comp hg hf₂)).add continuous_const`

You can also use `continuity!`, which applies lemmas with `{ md := semireducible }`.
The default behaviour is more conservative, and only unfolds `reducible` definitions
when attempting to match lemmas with the goal.

`continuity?` reports back the proof term it found.
-/
add_tactic_doc
{ name := "continuity / continuity'",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.continuity, `tactic.interactive.continuity'],
  tags := ["lemma application"]
}

end interactive

end tactic
