
import tactic.core data.sigma

noncomputable def classical.indefinite_description' {α : Sort*} (p : α → Prop) (h : ∃ (x : α), p x) : psigma p :=
let ⟨x,h'⟩ := classical.indefinite_description p h in ⟨x,h'⟩

namespace tactic

meta def mk_constructive_aux : expr → expr → tactic expr
| e `(∃ x : %%t, %%b) :=
  do let l := expr.lam `x binder_info.default t b,
     e ← mk_mapp ``classical.indefinite_description' [t,l,e],
     t ← infer_type e,
     mk_constructive_aux e t <|> pure e
| e `(@psigma %%α %%f) :=
  do id_f ← mk_mapp ``id [α],
     v ← mk_local_def `v α,
     f' ← head_beta $ f v,
     v' ← mk_local_def `v' f',
     fn ← mk_constructive_aux v' f',
     t ← infer_type fn >>= lambdas [v],
     fn ← lambdas [v,v'] fn,
     r ← mk_mapp ``psigma.map [α,α,f,t,id_f],
     pure $ r fn e
| e t := fail!"no match {t}"

setup_tactic_parser

meta def interactive.mk_constructive (n : parse ident) : tactic unit :=
do h ← get_local n,
   (vs,t) ← infer_type h >>= instantiate_mvars >>= mk_local_pis,
   e' ← mk_constructive_aux (h.mk_app vs) t,
   -- let e' := e.mk_app vs,
   e' ← lambdas vs e',
   note h.local_pp_name none e',
   clear h

end tactic
