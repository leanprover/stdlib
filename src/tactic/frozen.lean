/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.dependencies

/-!
# Tactics About Frozen Local Instances

Under certain circumstances, Lean 'freezes' local constants which are instances.
This means that these local constants cannot be reverted: `revert` will throw an
error. The same applies to the dependencies of frozen local instances since
reverting a dependency would imply that we must revert the frozen local instance
as well. Example:

```lean
example {α} [i : has_add α] (x y : α) : x + y = y + x :=
begin
  revert i, -- error: i is a frozen local instance
  revert α, -- error: α is a dependency of i
end
```

Frozen local instances are good for performance: instances can be cached more
effectively if we know that they cannot be removed from the context.

This module provides various tactics related to frozen instances, e.g. to find
out whether a local constant is frozen or to unfreeze local instances if
necessary. We say that a local constant is frozen if it is either a frozen local
instance or a dependency of a frozen local instance.

Related core tactics: `tactic.frozen_local_instances`,
`tactic.freeze_local_instances`, `tactic.unfreeze_local_instances`,
`tactic.revertible_context`.
-/

open native
open name_set (local_list_to_name_set)

namespace tactic

/-- Returns true if local instances are frozen. Note that there may not
actually be instances in the local context, so the frozen status may not have
any effect. -/
meta def are_local_instances_frozen : tactic bool := do
  (some _) ← frozen_local_instances | pure ff,
  pure tt

/-- Returns the frozen local instances. If local instances are not frozen, or if
there are no local instances, the returned list is empty. Unlike
`tactic.frozen_local_instances`, this tactic never returns local constants
which do not appear in the context. -/
meta def frozen_local_instances' : tactic (list expr) := do
  (some frozen) ← frozen_local_instances | pure [],
  ctx ← local_context,
  let ctx := local_list_to_name_set ctx,
  pure $ frozen.filter (λ h, ctx.contains h.local_uniq_name)

/-- Returns the unique names of all frozen local constants. -/
meta def frozen_locals_name_set : tactic name_set := do
  frozen ← frozen_local_instances',
  deps ← dependency_name_sets_of_hyps_inclusive frozen,
  pure $ deps.foldl name_set.union mk_name_set

/-- Returns all frozen local constants. The local constants are returned in no
particular order. -/
meta def frozen_locals : tactic (list expr) := do
  frozen ← frozen_local_instances',
  deps ← dependencies_of_hyps_inclusive frozen,
  pure deps.join

/-- Returns all local constants that are *not* frozen. The locals are returned
in the order in which they appear in the context. This is a more precise (but
less efficient) version of `tactic.revertible_local_context`. -/
meta def non_frozen_locals : tactic (list expr) := do
  frozen ← frozen_locals_name_set,
  ctx ← local_context,
  pure $ ctx.filter (λ h, ¬ frozen.contains h.local_uniq_name)

/-- `is_frozen h` returns true if the local constant `h` is frozen. -/
meta def is_frozen (h : expr) : tactic bool := do
  frozen ← frozen_locals_name_set,
  pure $ frozen.contains h.local_uniq_name

/-- `any_is_frozen_name_set hs` returns true if any of the local constants whose
unique names appear in `hs` are frozen. -/
meta def any_is_frozen_name_set (hs : name_set) : tactic bool := do
  frozen ← frozen_locals_name_set,
  pure $ frozen.fold ff (λ n b, b || hs.contains n)

/-- `any_is_frozen hs` returns true if any of the local constants `hs` are
frozen. -/
meta def any_is_frozen (hs : list expr) : tactic bool :=
any_is_frozen_name_set $ local_list_to_name_set hs

/-- `unfreeze_if_necessary_for_name_set hs` unfreezes local instances if any of
the local constants whose unique names appear in `hs` are frozen. -/
meta def unfreeze_if_necessary_for_name_set (hs : name_set) : tactic bool := do
  tt ← any_is_frozen_name_set hs | pure ff,
  unfreeze_local_instances,
  pure tt

/-- `unfreeze_if_necessary_for hs` unfreezes local instances if any of the local
constants in `hs` are frozen. You can use this before `revert_lst hs` to make
sure that the `revert` will not fail due to frozen local instances. -/
meta def unfreeze_if_necessary_for (hs : list expr) : tactic bool :=
unfreeze_if_necessary_for_name_set $ local_list_to_name_set hs

end tactic
