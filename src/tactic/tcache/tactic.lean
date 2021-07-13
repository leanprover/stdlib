import tactic.core
import tactic.tcache.store

open tactic

namespace tactic

/-- True if any goals are present, false otherwise. If there is a single goal `true`, then we
we consider there to be no goals. -/
@[inline] meta def are_goals_present : tactic bool :=
lock_tactic_state $ do
   /- In a `run_cmd` or similar, there is a single goal
      with type `true`. If we can clear it using triv,
      disable caching. -/
   try triv,
   gs ← get_goals,
   return $ gs.length ≠ 0

/-- If goals are present run `t : tactic α`, else run `alt : tactic α`, and in either case return
the result. -/
@[inline] meta def if_goals_present {α : Type} (alt : tactic α) (t : tactic α) : tactic α :=
do r ← are_goals_present,
   if r then t else do
     hash ← decl_name >>= tcache.hash_goals,
     tcache.trace hash "skipping, no goals",
     alt

/-- Directly exposes the `tcache` system to the `tactic` namespace. -/
meta def tcache_core (t : tactic unit) : tactic unit := tcache.discharge_goals t

/-- Exposes the `tcache` system to the `tactic` namespace, skipping declarations which look like
`example : true := ...`. -/
meta def tcache (t : tactic unit) : tactic unit := if_goals_present t (tcache_core t)

/-- Abbreviation for `tactic.tcache`. -/
meta def tc : tactic unit → tactic unit := tactic.tcache

namespace interactive

/-- Caches the result of the given sub-tactic block, rerunning the block if the type of the goal
we need to discharge changes. -/
meta def tcache (t : interactive.itactic) : tactic unit := tactic.tcache t

/-- Abbreviation for `tcache`. -/
meta def tc (t : interactive.itactic) : tactic unit := tactic.tcache t

end interactive

end tactic
