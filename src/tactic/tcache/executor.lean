import tactic.tcache.tactic

namespace tcache

/-- The `interactive.executor` which first performs a tcache lookup before actually resorting to
    executing the passed tactic. -/
meta def executor : interactive.executor tactic :=
{ config_type := unit, execute_with := λ _, tactic.tcache_core }

end tcache
