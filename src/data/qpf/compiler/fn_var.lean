
-- import for_mathlib
import tactic.mk_has_to_format

namespace tactic

@[derive has_to_format]
meta structure fn_var :=
(dom codom fn : expr)

meta def mk_fn_var (v : expr) : tactic fn_var :=
do { let v := expr.to_implicit_local_const v,
     v' ← (infer_type v >>= mk_local' (name.add_prime v.local_pp_name) binder_info.implicit),
     f ← mk_local_def `f (v.imp v'),
     pure ⟨v,v',f⟩ }

meta def mk_pred_var (v : expr) : tactic (expr × expr) :=
do { let v := expr.to_implicit_local_const v,
     f ← mk_local_def `f $ v.imp `(Prop),
     pure ⟨v,f⟩ }

meta def mk_rel_var (v : expr) : tactic (expr × expr) :=
do { let v := expr.to_implicit_local_const v,
     f ← mk_local_def `f $ v.imp $ v.imp `(Prop),
     pure ⟨v,f⟩ }

meta def get_dom {α} : α ⊕ fn_var → option expr
| (sum.inr x) := some x.dom
| _ := none

meta def get_codom {α} : α ⊕ fn_var → option expr
| (sum.inr x) := some x.codom
| _ := none

meta def get_fn {α} : α ⊕ fn_var → option expr
| (sum.inr x) := some x.fn
| _ := none

meta def decls : expr ⊕ fn_var → list expr
| (sum.inl x) := [x]
| (sum.inr x) := [x.dom,x.codom,x.fn]

meta def decls' : expr ⊕ (expr × expr) → list expr
| (sum.inl x) := [x]
| (sum.inr (x,y)) := [x,y]

end tactic
