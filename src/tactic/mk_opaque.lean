import tactic.core

namespace tactic

setup_tactic_parser

meta def interactive.mk_opaque1 (n : parse ident) : tactic unit :=
do h ← get_local n,
   n ← revert h,
   (expr.elet v t d b) ← target | fail "not a let expression",
   let e := expr.pi v binder_info.default t b,
   g ← mk_meta_var e,
   tactic.exact $ g d,
   gs ← get_goals,
   set_goals $ g :: gs,
   intron n

meta def interactive.mk_opaque (ns : parse ident*) : tactic unit :=
ns.mmap' interactive.mk_opaque1

end tactic
