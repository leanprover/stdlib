
import control.bitraversable.instances
-- import data.qpf.compiler.equations
import data.qpf.compiler.fn_var
import data.qpf.compiler.inductive_decl
import data.qpf.multivariate
import .for_mathlib

universes u v

namespace level

meta def pred : level → level
| level.zero := level.zero
| (level.succ a) := a
| (level.max a b) := max (pred a) (pred b)
| (level.imax a b) := max (pred a) (pred b)
| l@(level.param a) := l
| l@(level.mvar a) := l

end level

def reversed (m : Type u → Type v) := m
def reversed.mk {m : Type u → Type v} {α} (x : m α) : reversed m α := x
def reversed.run {m : Type u → Type v} {α} (x : reversed m α) : m α := x

instance {m : Type u → Type v} [F : functor m] : functor (reversed m) := F
instance {m : Type u → Type v} [functor m] [L : is_lawful_functor m] : is_lawful_functor (reversed m) := L

instance {m : Type u → Type v} [applicative m] : applicative (reversed m) :=
{ pure := λ α x, @pure m _ _ x,
  map := λ α β f (x : m α), show m β, from f <$> x,
  map_const := λ α β f (x : m _), show m α, from f <$ x,
  seq := λ α β f x, show m β, from flip id <$> x <*> f }

instance {m : Type u → Type v} [applicative m] [F : is_lawful_applicative m] : is_lawful_applicative (reversed m) :=
{ map_const_eq := λ α β, @map_const_eq m _ _ α β,
  pure_seq_eq_map := by intros; simp [(<*>),(<$>),pure,flip] with functor_norm,
  map_pure  := λ α β g x, @map_pure m _ _ _ _ g x,
  seq_pure  := by intros; simp [(<*>),(<$>),pure,flip] with functor_norm,
  seq_assoc := by intros; simp [(<*>),(<$>),pure,flip] with functor_norm,
  .. F.to_is_lawful_functor }

attribute [irreducible] reversed

namespace list

def mmap_reversed {t : Type u → Type u} [traversable t] {m : Type u → Type u} [applicative m] {α β} (f : α → m β) : t α → m (t β) :=
reversed.run ∘ traverse (reversed.mk ∘ f)

open bitraversable
variables {α β γ : Type u} {m : Type u → Type u} [monad m]

meta def mmap_dead (f : α → m γ) (xs : α ⊕ β) : m (γ ⊕ β) :=
tfst f xs

meta def mmap_live (f : β → m γ) (xs : α ⊕ β) : m (α ⊕ γ) :=
tsnd f xs

meta def map_dead (f : α → γ) (xs : α ⊕ β) : (γ ⊕ β) :=
sum.map f id xs

meta def map_live (f : β → γ) (xs : α ⊕ β) : (α ⊕ γ) :=
sum.map id f xs

meta def mmap_dead' (f : α → m γ) (xs : list $ α ⊕ β) : m (list $ γ ⊕ β) :=
xs.mmap (mmap_dead f)

meta def mmap_live' (f : β → m γ) (xs : list $ α ⊕ β) : m (list $ α ⊕ γ) :=
xs.mmap (mmap_live f)

meta def mmap_reversed_live' (f : β → m γ) (xs : list $ α ⊕ β) : m (list $ α ⊕ γ) :=
mmap_reversed (mmap_live f) xs

meta def par_join (xs : list (task unit)) : tactic unit :=
pure $ xs.foldl (function.const _ task.get) ()

meta def par_mmap' {α} (f : α → tactic unit) (xs : list α) : tactic unit :=
do ys ← xs.mmap $ tactic.run_async ∘ f,
   par_join ys

meta def par_mmap {α β} (f : α → tactic β) (xs : list α) : tactic (list β) :=
do ys ← xs.mmap $ tactic.run_async ∘ f,
   pure $ ys.map task.get

end list

namespace expr

meta def instantiate_pi : expr → list expr → expr
| (expr.pi n bi d b) (e::es) := instantiate_pi (b.instantiate_var e) es
| e _ := e

meta def sort_univ : expr → level
| (sort ls) := ls
| _ := level.zero

end expr

namespace tactic
-- setup_tactic_parser
-- meta def synth_pos (p : parse cur_pos) : tactic unit :=
-- refine ``(%%(p))

-- meta def bind {α β} (x : tactic α) (f : α → tactic β) (x : pos . synth_pos) : tactic β := fail "foo"

-- run_cmd do
--   x ← get_env,
--   trace "bar"

meta def simp_only (ls : list pexpr) (attrs : list name := []) (loc : option name := none) : tactic unit :=
do let ls := ls.map (simp_arg_type.expr), -- >>= simp_lemmas.append_pexprs simp_lemmas.mk [],
   -- interactive.dsimp tt ls [] (interactive.loc.ns [none])
   interactive.simp none tt ls attrs (interactive.loc.ns [loc])

meta def mk_substitution (vs : list expr) : tactic (list expr × list (name × expr)) :=
do vs' ← intron' vs.length,
   let σ := (vs.map expr.local_uniq_name).zip vs',
   pure (vs', σ)

meta def lambdas' (xs : list $ list expr) (e : expr) : tactic expr :=
xs.mfoldr lambdas e

meta def pis' (xs : list $ list expr) (e : expr) : tactic expr :=
xs.mfoldr pis e

meta def add_eqn_lemmas (n : name) : tactic unit :=
updateex_env $ λ e, pure $ e.add_eqn_lemma n

-- replace with `mk_local_pis`
meta def binders : expr → tactic (list expr)
| (expr.pi n bi d b) :=
  do v ← mk_local' n bi d,
     (::) v <$> binders (b.instantiate_var v)
| _ := pure []

meta def match_induct_hyp (n : name) : list expr → list expr → tactic (list $ expr × option expr)
| [] [] := pure []
| [] _ := fail "wrong number of inductive hypotheses"
| (x :: xs) [] := (::) (x,none) <$> match_induct_hyp xs []
| (x :: xs) (h :: hs) :=
do t ← infer_type x,
   if t.is_app_of n
     then (::) (x,h) <$> match_induct_hyp xs hs
     else (::) (x,none) <$> match_induct_hyp xs (h :: hs)

meta def rec_args_count (t c : name) : tactic ℕ :=
do ct ← mk_const c >>= infer_type,
   (list.length ∘ list.filter (λ v : expr, v.local_type.is_app_of t)) <$> binders ct

meta def better_induction (e : expr) : tactic $ list (name × list (expr × option expr) × list (name × expr)) :=
do t ← infer_type e,
   let tn := t.get_app_fn.const_name,
   env ← get_env,
   focus1 $
   do vs ← induction e,
      gs ← get_goals,
      vs' ← list.mzip_with₃ (λ n g (pat : name × list expr × list (name × expr)),
        do let ⟨_,args,σ⟩ := pat,
           set_goals [g],
           nrec ← rec_args_count tn n,
           let ⟨args,rec⟩ := args.split_at (args.length - nrec),
           args ← match_induct_hyp tn args rec,
           pure ((n,args,σ))) (env.constructors_of tn) gs vs,
      set_goals gs,
      pure vs'

meta def prove_goal_async' (xs : list expr) (tac : tactic unit) : tactic unit := do
tgt ← target, tgt' ← instantiate_mvars tgt >>= pis xs,
env ← get_env, tgt' ← return $ env.unfold_untrusted_macros tgt',
when tgt.has_meta_var (fail "goal contains metavariables"),
params ← return tgt.collect_univ_params,
lemma_name ← new_aux_decl_name,
proof ← run_async (do
  goal_meta ← mk_meta_var tgt,
  set_goals [goal_meta],
  tac,
  proof ← instantiate_mvars goal_meta,
  proof ← return $ env.unfold_untrusted_macros proof,
  proof ← lambdas xs proof,
  when proof.has_meta_var $ fail "async proof failed: contains metavariables",
  return proof),
add_decl $ declaration.thm lemma_name params tgt' proof,
exact $ (expr.const lemma_name (params.map level.param)).mk_app xs

meta def renew : expr → tactic expr
| (expr.local_const uniq pp bi t) := mk_local' pp bi t
| e := fail format!"{e} is not a local constant"

end tactic


def cache {α} (x : α) := { y : α // y = x }

def cache.init {α} {x : α} : cache x := ⟨x,rfl⟩

noncomputable def classical.indefinite_description' {α : Sort*} (p : α → Prop) (h : ∃ (x : α), p x) : psigma p :=
let ⟨x,h'⟩ := classical.indefinite_description p h in ⟨x,h'⟩

namespace tactic

meta def init_cache : tactic unit :=
refine ``(subtype.mk _ rfl)

end tactic

meta instance {α : Type*} [has_to_format α] {x : α} : has_to_format (cache x) :=
subtype.has_to_format

namespace tactic

open native

meta def solve_async (vs : list $ list expr) (p : expr) (tac : tactic unit) : tactic (task expr) :=
run_async $ do
  pr ← prod.snd <$> solve_aux p tac >>= instantiate_mvars,
  vs.reverse.mfoldl (flip lambdas) pr

def elim {α β γ} (f : α → γ) (g : β → γ) : α ⊕ β → γ :=
λ x, sum.rec_on x f g

meta def map_arg' (m : rb_map expr expr) : expr → expr → tactic expr
| e (expr.pi n bi d b) :=
do v ← mk_local' n bi d,
   e' ← head_beta (e v) >>= whnf,
   map_arg' e' (b.instantiate_var v) >>= lambdas [v]
| e v@(expr.local_const _ _ _ _) :=
do some f ← pure $ m.find v | pure e,
   pure $ f e
| e _ := pure e

meta def map_arg (m : rb_map expr expr) (e : expr) : tactic expr :=
infer_type e >>= whnf >>= map_arg' m e

meta def find_dead_occ (n : name) : rb_map expr ℕ → expr → rb_map expr ℕ
| m `(%%a → %%b) := find_dead_occ (a.list_local_consts.foldl rb_map.erase m) b
| m (expr.local_const _ _ _ _) := m
| m e :=
if e.get_app_fn.const_name = n
  then m
  else e.list_local_consts.foldl rb_map.erase m

meta def live_vars (induct : inductive_type) : tactic $ list $ expr × bool :=
do let n := induct.name,
   let params : list expr := induct.params,
   let e := (@expr.const tt n induct.u_params).mk_app induct.params,
   let vs := rb_map.of_list $ params.enum.map prod.swap,
   let ls := induct.ctors,
   ls ← ls.mmap $ λ c,
     do { ts ← c.args.mmap infer_type,
          pure $ ts.foldl (find_dead_occ n) vs },
   let m := ls.foldl rb_map.intersect vs,
   let m' := params.map $ λ x, (x,m.contains x),
   pure m'

meta instance : has_repr expr := ⟨ to_string ⟩
meta instance task.has_repr {α} [has_repr α] : has_repr (task α) := ⟨ repr ∘ task.get ⟩

open level
meta def level.repr : level → ℕ → string
| zero n := repr n
| (succ a) n := level.repr a n.succ
| (max x y) n := sformat!"(max {level.repr x n} {level.repr y n})"
| (imax x y) n := sformat!"(imax {level.repr x n} {level.repr y n})"
| (param a) n := if n = 0 then repr a
                          else sformat!"({n} + {repr a})"
| (mvar a) n := if n = 0 then repr a
                         else sformat!"({n} + {repr a})"

meta instance level.has_repr : has_repr level := ⟨ λ l, level.repr l 0 ⟩

def no_print {α} (x : string) (y : α) := y

meta instance no_print.has_to_format {msg : string} (x : Sort*) : has_to_format (no_print msg x) :=
⟨ λ _, format!"⟨ {msg} ⟩" ⟩

attribute [derive has_to_format] reducibility_hints

meta def both {α} : α ⊕ α → α
| (sum.inl x) := x
| (sum.inr x) := x

def get_left {α β} : α ⊕ β → option α
| (sum.inl x) := some x
| (sum.inr x) := none

def get_right {α β γ} (f : β → γ) : α ⊕ β → option γ
| (sum.inl x) := none
| (sum.inr x) := some (f x)

@[derive has_to_format]
meta structure internal_mvfunctor :=
(decl : no_print "declaration" declaration)
(induct : inductive_type)
(def_name eqn_name map_name abs_name repr_name pfunctor_name : name)
(univ_params : list level)
(vec_lvl : level)
-- (live_params : list $ expr × ℕ)
-- (dead_params : list $ expr × ℕ)
-- (params : list expr)
(params' : list $ expr ⊕ expr) -- dead on the left, live on the right
(live_params' : cache $ params'.filter_map (get_right id) . init_cache)
(dead_params' : cache $ params'.filter_map get_left . init_cache)
(type : expr)

-- meta def internal_mvfunctor.map_live (fn : internal_mvfunctor) (f : expr → expr) : list expr :=
-- fn.live_params.map $ f ∘ prod.fst

-- meta def internal_mvfunctor.mmap_live {m} [monad m] (fn : internal_mvfunctor) (f : expr → m expr) : m (list expr) :=
-- fn.live_params.mmap $ f ∘ prod.fst

-- meta def inductive_type.to_format (decl : inductive_type) : tactic format :=
-- do let n₀ := name.anonymous,
--    t ← pis decl.idx decl.type,
--    cn ← mk_local_def (decl.name.replace_prefix decl.pre n₀) t,
--    brs ← decl.ctors.mmap $ λ c,
--        do { let rt := cn.mk_app c.result,
--             t ← pis c.args rt >>= pp,
--             pure format!"| {(c.name.update_prefix n₀).to_string} : {t}" },
--    args ← decl.params.mmap $ λ p,
--      do { t ← infer_type p >>= pp,
--           pure $ expr.fmt_binder p.local_pp_name p.binding_info t },
--    t ← pp t,
--    let xs := format!"
-- inductive {cn} {format.intercalate \" \" args} : {t}
-- {format.intercalate \"\n\" brs}",
--    return xs

meta def internalize_mvfunctor (ind : inductive_type) : tactic internal_mvfunctor :=
do let decl := declaration.cnst ind.name ind.u_names ind.type tt,
   let n := decl.to_name,
   let df_name := n <.> "internal",
   let lm_name := n <.> "internal_eq",
   (params,t) ← mk_local_pis decl.type,
   let params := ind.params ++ params,
   ps ← live_vars ind,
   let ps := ps.map $ λ ⟨e,b⟩, if b then sum.inr e else sum.inl e,
   -- let m := rb_map.sort prod.snd m.to_list,
   -- let m' := rb_map.sort prod.snd m'.to_list,
   u ← mk_meta_univ,
   let vars := string.intercalate "," (ps.map to_string),
   (params.mmap' (λ e, infer_type e >>= unify (expr.sort u))
     <|> fail format!"live type parameters ({params}) are not in the same universe" : tactic _),
   (level.succ u) ← get_univ_assignment u <|> pure level.zero.succ,
   ts ← (params.mmap infer_type : tactic _),
   pure { decl := decl,
          induct := ind,
          def_name := df_name,
          eqn_name := lm_name,
          map_name := (df_name <.> "map"),
          abs_name := (df_name <.> "abs"),
          repr_name := (df_name <.> "repr"),
          pfunctor_name := n <.> "pfunctor",
          vec_lvl := u,
          univ_params := decl.univ_params.map level.param,
          -- live_params := m,
          -- dead_params := m',
          params' := ps,
          type := t }

meta def internal_mvfunctor.live_params (p : internal_mvfunctor) : list expr :=
p.live_params'.val
-- p.params'.filter_map $ λ v, sum.cases_on v some $ λ _, none -- λ ⟨x,l⟩, x <$ guard l

meta def internal_mvfunctor.dead_params (p : internal_mvfunctor) : list expr :=
p.dead_params'.val
-- filter_map $ λ v, sum.cases_on v (λ _, none) some

meta def internal_mvfunctor.params (p : internal_mvfunctor) : list expr :=
p.params'.map both

open bitraversable

notation `⦃ ` r:( foldr `, ` (h t, typevec.append1 t h) fin2.elim0 ) ` ⦄` := r
notation `⦃`  `⦄` := typevec.nil

local prefix `♯`:0 := cast (by try { simp only with typevec }; congr' 1; try { simp only with typevec })

meta def mk_internal_functor_def (func : internal_mvfunctor) : tactic unit :=
do let trusted := func.decl.is_trusted,
   let arity := func.live_params.length,
   let vec := @expr.const tt ``_root_.typevec [func.vec_lvl] `(arity),
   v_arg ← mk_local_def `v_arg vec,
   t ← pis (func.dead_params ++ [v_arg]) func.type,
   (_,df) ← @solve_aux unit t $ do
     { vs ← func.params'.mmap_dead' $ λ v, intro v.local_pp_name,
       vs ← vs.mmap_reversed_live' $ λ x : expr, do
         { refine ``(typevec.cases_cons _ _),
           x' ← intro x.local_pp_name,
           pure x' },
       refine ``(typevec.cases_nil _),
       let e := (@expr.const tt func.decl.to_name (func.decl.univ_params.map level.param)).mk_app $ vs.map both,
       exact e },
   df ← instantiate_mvars df,
   emit_decl func.def_name $ declaration.defn func.def_name func.decl.univ_params t df (reducibility_hints.regular 1 tt) trusted

meta def mk_live_vec (u : level) (vs : list expr) : tactic expr :=
trace_scope $
do let nil : expr := expr.const ``typevec.nil [u],
   vs.reverse.mfoldr (λ e s, mk_mapp ``typevec.append1 [none,s,e]) nil

meta def mk_map_vec (u u' : level) (vs : list expr) : tactic expr :=
do let nil : expr := expr.const ``typevec.nil [u],
   let nil' : expr := expr.const ``typevec.nil [u'], --  [u.succ.succ] (expr.sort u.succ),
   nil_fun ← mk_mapp ``typevec.nil_fun [nil,nil'],
   vs.reverse.mfoldr (λ e s, do
     app ← mk_const ``typevec.append_fun,
     mk_mapp ``typevec.append_fun [none,none,none,none,none,s,e]) nil_fun

meta def mk_internal_functor_app (func : internal_mvfunctor) : tactic expr :=
trace_scope $
do let decl := func.decl,
   vec ← mk_live_vec func.vec_lvl $ func.live_params,
   pure $ (@expr.const tt func.def_name decl.univ_levels).mk_app (func.dead_params ++ [vec])

meta def mk_internal_functor_eqn (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do let decl := func.decl,
   lhs ← mk_internal_functor_app func,
   let rhs := (@expr.const tt decl.to_name decl.univ_levels).mk_app func.params,
   p ← mk_app `eq [lhs,rhs] >>= pis func.params,
   pr ← solve_async [] p $ intros >> reflexivity,
   emit_decl func.def_name $ declaration.thm func.eqn_name decl.univ_params p pr

meta def mk_internal_functor (n : name) : tactic internal_mvfunctor :=
do d ← inductive_type.of_name n,
   func ← internalize_mvfunctor d,
   mk_internal_functor_def func,
   mk_internal_functor_eqn func,
   pure func

-- meta def mk_internal_functor' (d : interactive.inductive_decl) : tactic internal_mvfunctor :=
-- do d ← inductive_type.of_decl d,
--    mk_inductive _ d,
--    func ← internalize_mvfunctor d,
--    mk_internal_functor_def func,
--    mk_internal_functor_eqn func,
--    pure func

open typevec

meta def destruct_typevec₃ {α} (params : list (α ⊕ expr)) (v : name) : tactic (list $ α ⊕ fn_var) :=
do vs ← params.mmap_reversed_live' $ λ x : expr, do
     { refine ``(typevec.typevec_cases_cons₃ _ _),
       α ← get_unused_name `α >>= intro,
       β ← get_unused_name `β >>= intro,
       f ← get_unused_name `f >>= intro,
       pure $ fn_var.mk α β f },
   refine ``(typevec.typevec_cases_nil₃ _),
   pure vs

meta def destruct_typevec' {α} (params : list (α ⊕ expr)) (v : name) : tactic (list $ α ⊕ expr) :=
do vs ← params.mmap_reversed_live' $ λ x : expr, do
     { refine ``(typevec.cases_cons _ _),
       α ← get_unused_name `α >>= intro,
       pure α },
   refine ``(typevec.cases_nil _),
   pure vs

-- def mk_arg_list {α} (xs : list (α × ℕ)) : list α :=
-- (rb_map.sort prod.snd xs).map prod.fst

meta def internal_expr (func : internal_mvfunctor) :=
(@expr.const tt func.def_name func.decl.univ_levels).mk_app func.dead_params

meta def functor_expr (func : internal_mvfunctor) :=
(@expr.const tt func.pfunctor_name func.decl.univ_levels).mk_app func.dead_params

meta def mk_mvfunctor_map (func : internal_mvfunctor) : tactic expr :=
trace_scope $
do let decl := func.decl,
   let intl := internal_expr func,
   let arity := func.live_params.length,
   α ← mk_local_def `α $ @expr.const tt ``typevec [func.vec_lvl] `(arity),
   β ← mk_local_def `β $ @expr.const tt ``typevec [func.vec_lvl] `(arity),
   f ← mk_app ``typevec.arrow [α,β] >>= mk_local_def `f,
   let r := expr.imp (intl α) (intl β),

   map_t ← pis (func.dead_params ++ [α,β,f]) r,
   (_,df) ← @solve_aux unit map_t $ do
     { vs ← func.params'.mmap_dead' $ λ _, intro1,
       -- let vs := vs.zip $ func.dead_params.map prod.snd,
       mαβf ← destruct_typevec₃ vs `α,
       let m : rb_map expr expr := rb_map.of_list $ mαβf.filter_map $ get_right (λ ⟨α,β,f⟩, (α,f)),
       let mαβ : list expr := mαβf.map $ elim id fn_var.codom, -- λ ⟨α,β,f,i⟩, (β,i),
       target >>= instantiate_mvars >>= unsafe_change,
       let e := (@expr.const tt func.eqn_name func.decl.univ_levels),
       g ← target,
       (g',_) ← solve_aux g $
         repeat (rewrite_target e) >> target,
       unsafe_change g',
       x ← intro1,
       xs ← cases_core x,
       xs.mmap' $ λ ⟨c, args, _⟩, do
         { let e := (@expr.const tt c decl.univ_levels).mk_app mαβ,
           args' ← args.mmap (map_arg m),
           exact $ e.mk_app args' } },
   df ← instantiate_mvars df,
   emit_decl' func.def_name $ declaration.defn func.map_name decl.univ_params map_t df (reducibility_hints.regular 1 tt) decl.is_trusted
open expr

meta def mk_vecs {α} (l : level) (xs : list (α ⊕ fn_var)) : tactic (expr × expr × expr) :=
do let live := xs.filter_map $ get_right id,
   v  ← mk_live_vec l $ live.map fn_var.dom,
   v' ← mk_live_vec l $ live.map fn_var.codom,
   f ← mk_map_vec l l $ live.map fn_var.fn,
   pure (v,v',f)

meta def mk_functor_map (func : internal_mvfunctor) : tactic expr :=
do params ← func.params'.mmap $ bitraverse (pure ∘ to_implicit_local_const) mk_fn_var,
   let F := (@const tt func.induct.name func.induct.u_params).mk_app $ params.map $ elim id fn_var.dom,
   let F' := (@const tt func.induct.name func.induct.u_params).mk_app $ params.map $ elim id fn_var.codom,
   x ← mk_local_def `x F,
   (v,v',f) ← mk_vecs func.vec_lvl params,
   let map := (@const tt func.map_name func.univ_params).mk_app func.dead_params v v' f x,
   t ← pis' [params.bind decls, [x]] F',
   df ← lambdas' [params.bind decls, [x]] map,
   emit_decl' func.def_name $ mk_definition (func.induct.name <.> "map") func.induct.u_names t df

meta def mk_mvfunctor_map_eqn (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do env ← get_env,
   let decl := func.decl,
   let cs := env.constructors_of func.decl.to_name,
   params' ← func.params'.mmap_live' mk_fn_var,

   let arity := func.live_params.length,
   let m : rb_map expr expr := rb_map.of_list $ params'.filter_map $ get_right (λ x, (fn_var.dom x, fn_var.fn x)),
   let fs := params'.filter_map get_fn,
   let flat := params'.bind decls,
   α ← mk_live_vec func.vec_lvl func.live_params,
   β ← mk_live_vec func.vec_lvl $ params'.filter_map get_codom,
   f ← mk_map_vec func.vec_lvl func.vec_lvl fs,
   cs.enum.mmap' $ λ ⟨i,c⟩, do
     { let c := @expr.const tt c func.decl.univ_levels,
       let e := c.mk_app func.params,
       -- trace live_params',
       let e' := c.mk_app $ params'.map $ elim id fn_var.codom,
       t  ← infer_type e,
       (vs,_) ← mk_local_pis t,
       t' ← infer_type e',
       vs' ← vs.mmap (map_arg m),
       let x := e.mk_app vs,
       -- trace_expr x,
       let map_e := (@expr.const tt func.map_name func.decl.univ_levels).mk_app' [func.dead_params, [α,β,f,x]],
       let map_e' := (@expr.const tt (func.induct.name <.> "map") func.decl.univ_levels).mk_app' [flat, [x]],
       eqn ← mk_app `eq [map_e,(e'.mk_app vs')] >>= pis (params'.bind  decls++ vs) >>= instantiate_mvars,
       eqn' ← mk_app `eq [map_e',(e'.mk_app vs')] >>= pis (params'.bind  decls++ vs) >>= instantiate_mvars,
       pr ← solve_async [] eqn $ do
         { intros >> reflexivity },
       let n := func.map_name <.> ("_equation_" ++ to_string i),
       d ← emit_decl' func.def_name $ declaration.thm n decl.univ_params eqn pr,
       add_eqn_lemmas n,
       simp_attr.typevec.set n () tt,
       let n := func.induct.name <.> "map" <.> ("_equation_" ++ to_string i),
       d ← emit_decl' func.def_name $ declaration.thm n decl.univ_params eqn' pr,
       add_eqn_lemmas n,
       simp_attr.typevec.set n () tt,
       pure () },
   let n := func.induct.name <.> "map_eq_map",
   let t := expr.mk_app (const func.induct.name decl.univ_levels) (func.params),
   x ← mk_local_def `x t,
   let map_e := (@expr.const tt func.map_name func.decl.univ_levels).mk_app' [func.dead_params, [α,β,f,x]],
   let map_e' := (@expr.const tt (func.induct.name <.> "map") func.decl.univ_levels).mk_app' [flat,[x]],
   eqn ← mk_app `eq [map_e,map_e'],
   pr ← mk_app ``eq.refl [map_e] >>= lambdas' [params'.bind decls,[x]],
   eqn ← pis' [params'.bind decls,[x]] eqn,
   emit_decl func.def_name $ declaration.thm n decl.univ_params eqn (pure pr),
   pure ()

meta def mk_mvfunctor_instance (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do map_d ← mk_mvfunctor_map func,
   mk_functor_map func,
   mk_mvfunctor_map_eqn func,
   vec ← mk_live_vec func.vec_lvl $ func.live_params,
   let decl := func.decl,
   let vs := func.dead_params,
   let intl := (@expr.const tt func.def_name decl.univ_levels).mk_app vs,
   -- trace intl,
   t ← mk_app ``mvfunctor [intl] >>= pis vs,
   (_,df) ← @solve_aux unit t $ do
     { vs ← intro_lst $ vs.map expr.local_pp_name,
       to_expr ``( { mvfunctor . map := %%(map_d.mk_app vs) } ) >>= exact },
   df ← instantiate_mvars df,
   let inst_n := func.def_name <.> "mvfunctor",
   emit_decl func.def_name $ declaration.defn inst_n func.decl.univ_params t df (reducibility_hints.regular 1 tt) func.decl.is_trusted,
   set_basic_attribute `instance inst_n,
   pure ()

open expr (const)

meta def mk_head_t (decl : inductive_type) (func : internal_mvfunctor) : tactic inductive_type :=
do let n := decl.name,
   let head_n := (n <.> "head_t"),
   let sig_c  : expr := const n decl.u_params,
   cs ← decl.ctors.mmap $ λ d : type_cnstr,
   do { vs' ← d.args.mfilter $ λ v,
          do { t ← infer_type v,
               pure $ ¬ ∃ v ∈ func.live_params, expr.occurs v t },
        pure { name := d.name.update_prefix head_n, args := vs', .. d } },
   let decl' := { name := head_n, ctors := cs, params := func.dead_params, .. decl },
   decl' <$ mk_inductive n decl'

meta def mk_child_t (decl : inductive_type) (func : internal_mvfunctor) : tactic (list inductive_type) :=
do let n := decl.name,
   let dead := func.dead_params,
   let live := func.live_params,
   let mk_constr : name → expr := λ n', (const (n'.update_prefix $ n <.> "head_t") decl.u_params).mk_app dead,
   let head_t : expr := const (n <.> "head_t") decl.u_params,
   live.mmap $ λ l : expr,
     do let child_n := (n <.> "child_t" ++ l.local_pp_name),
        let sig_c  : expr := const n decl.u_params,
        cs ← (decl.ctors.mmap $ λ d : type_cnstr,
          do { (rec,vs') ← d.args.mpartition $ λ v,
                 do { t ← infer_type v,
                      pure $ expr.occurs l t },
               vs' ← vs'.mfilter $ λ v,
                 do { t ← infer_type v,
                      pure $ ¬ ∃ v ∈ live, expr.occurs v t },
               rec.enum.mmap $ λ ⟨i,r⟩, do
                 (args',r') ← infer_type r >>= mk_local_pis,
                 pure { name := (d.name.append_after i).update_prefix $ n <.> "child_t"  ++ l.local_pp_name,
                        args := vs' ++ args', result := [(mk_constr d.name).mk_app vs'], .. d } } : tactic _),
        idx ← (mk_local_def `i $ head_t.mk_app $ dead : tactic _),
        let decl' := { name := child_n,
                       params := dead,
                       idx := decl.idx ++ [idx],
                       ctors := cs.join, .. decl },
        decl' <$ mk_inductive n decl'

meta def inductive_type.of_pfunctor (func : internal_mvfunctor) : tactic inductive_type :=
do let d := func.decl,
   let params := func.params,
   (idx,t) ← mk_local_pis (d.type.instantiate_pi params),
   env ← get_env,
   cs ← (env.constructors_of d.to_name).mmap $ λ c : name,
   do { let e := @const tt c d.univ_levels,
        t ← infer_type $ e.mk_app params,
        (vs,t) ← mk_local_pis t,
        let infer := implicit_infer_kind_of $ vs.take params.length,
        pure (t.get_app_fn.const_name,{ type_cnstr .
               name := c,
               args := vs,
               result := t.get_app_args.drop $ env.inductive_num_params d.to_name,
               infer  := infer }) },
   pure { pre     := func.induct.pre,
          name    := d.to_name,
          u_names := d.univ_params,
          params  := params,
          idx     := idx, type := t,
          ctors   := cs.map prod.snd }

meta def mk_child_t_vec (decl : inductive_type) (func : internal_mvfunctor) (vs : list inductive_type) : tactic expr :=
do let n := decl.name,
   let dead := func.dead_params,
   let live := func.live_params,
   let head_t := (@const tt (n <.> "head_t") func.decl.univ_levels).mk_app dead,
   let child_n := (n <.> "child_t"),
   let arity := live.length,
   hd_v ← mk_local_def `hd head_t,
   (expr.sort u') ← pure decl.type,
   let u := u'.pred,
   let vec_t := @const tt ``typevec [u] (reflect arity),
   t ← pis (dead ++ [hd_v]) vec_t,
   let nil : expr := expr.const ``typevec.nil [u],
   vec ← live.reverse.mfoldr (λ e v,
     do c ← mk_const $ child_n ++ e.local_pp_name,
        let c := (@const tt (n <.> "child_t" ++ e.local_pp_name) func.decl.univ_levels).mk_app dead hd_v,
        mv ← mk_mvar,
        unify_app (const ``append1 [u]) [mv,v,c]) nil,
   df ← (instantiate_mvars vec >>= lambdas (dead ++ [hd_v]) : tactic _),
   let r := reducibility_hints.regular 1 tt,
   emit_decl' func.def_name $ declaration.defn child_n func.decl.univ_params t df r tt,
   pure $ expr.const child_n $ func.induct.u_params

meta def mk_pfunctor (func : internal_mvfunctor) : tactic unit :=
do d ← inductive_type.of_pfunctor func,
   hd ← mk_head_t d func,
   ch ← mk_child_t d func,
   mk_child_t_vec d func ch,
   let arity := func.live_params.length,
   (expr.sort u') ← pure d.type,
   let u := u'.pred,
   let dead := func.dead_params,
   let vec_t := @const tt ``mvpfunctor [u] $ reflect arity,
   t ← pis dead vec_t,
   let n := d.name,
   let head_t := (@const tt (n <.> "head_t") func.decl.univ_levels).mk_app dead,
   let child_t := (@const tt (n <.> "child_t") func.decl.univ_levels).mk_app dead,
   df ← (mk_mapp ``mvpfunctor.mk [some $ reflect arity, head_t,child_t] >>= lambdas dead : tactic _),
   emit_decl func.def_name $ mk_definition func.pfunctor_name func.decl.univ_params t df,
   pure ()

meta def mk_pfunc_constr (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do env ← get_env,
   let cs := env.constructors_of func.decl.to_name,
   let u := func.type.sort_univ.pred,
   let u' := func.univ_params.foldl level.max u,
   let dead := func.dead_params,
   let live := func.live_params,
   let out_t :=  (@const tt func.pfunctor_name func.univ_params).mk_app dead,
   vec_t ← mk_live_vec func.vec_lvl live,
   let arity := func.live_params.length,
   let fn := @const tt ``mvpfunctor.obj [u],
   r ← unify_app fn [reflect arity,out_t,vec_t],
   cs.mmap $ λ c,
     do { let p := c.update_prefix (c.get_prefix <.> "pfunctor"),
          let hd_c := c.update_prefix (func.decl.to_name <.> "head_t"),
          let e := (@const tt c func.univ_params).mk_app func.params,
          (args,_) ← infer_type e >>= mk_local_pis,
          sig ← pis (func.params ++ args) r,
          (rec,vs') ← args.mpartition $ λ v,
                 do { t ← infer_type v,
                      pure $ ¬ ∃ v ∈ live, expr.occurs v t },

          let e := ((@const tt hd_c func.univ_params).mk_app dead).mk_app rec,
          ms ← live.mmap $ λ l,
                do { let l_name := l.local_pp_name,
                     vs' ← vs'.mfilter $ λ v,
                       do { t ← infer_type v,
                            pure $ expr.occurs l t },
                     y ← infer_type e >>= mk_local_def `y,
                     hy ← mk_app `eq [y,e] >>= mk_local_def `hy,
                     let ch_t := (@const tt (func.decl.to_name <.> "child_t" ++ l_name) func.univ_params).mk_app func.dead_params y,
                     let ch_c := c.update_prefix (func.decl.to_name <.> "child_t" ++ l_name),
                     t ← pis (vs' ++ rec ++ [y,hy]) $ ch_t.imp l,
                     (_,f) ← @solve_aux unit t $ do
                       { (vs',σ₀) ← mk_substitution vs' ,
                         (rec,σ₁) ← mk_substitution rec ,
                         y ← intro1, hy ← intro1,
                         x ← intro `x,
                         interactive.generalize `hx () (to_pexpr x,`x'),
                         solve1 $ do
                         { a ← better_induction x,
                           gs ← get_goals,
                           rs ← mzip_with (λ (x : name × list (expr × option expr) × list (name × expr)) g,
                             do let ⟨ctor,a,b⟩ := x,
                                set_goals [g],
                                cases $ hy.instantiate_locals b,
                                gs ← get_goals,
                                pure $ gs.map $ λ g, (a,b,g)) a gs,
                           mzip_with' (λ (v : expr) (r : list (expr × option expr) × list (name × expr) × expr),
                             do let (a,b,g) := r,
                                set_goals [g],
                                x' ← get_local `x',
                                expr.app _ t ← infer_type x',
                                let ts := t.get_app_args.length - func.dead_params.length,
                                let a' := (a.drop ts).map prod.fst, exact $ v.mk_app a' ) vs' rs.join,
                           skip } },
                     pr ← mk_eq_refl e,
                     pure $ f.mk_app $ vs' ++ rec ++ [e,pr] },
          (_,df) ← solve_aux r $ do
            { m ← mk_map_vec func.vec_lvl func.vec_lvl ms,
              refine ``( ⟨ %%e, _ ⟩ ),
              exact m,
              pure () },
          let c' := c.update_prefix $ c.get_prefix <.> "pfunctor",
          let vs := func.params ++ args,
          r  ← pis vs r >>= instantiate_mvars,
          df ← instantiate_mvars df >>= lambdas vs,
          emit_decl func.def_name $ mk_definition c' func.decl.univ_params r df,
          pure () },
   pure ()

-- meta def saturate' : expr → expr → tactic expr
-- | (expr.pi n bi t b) e :=
-- do v ← mk_meta_var t,
--    t ← whnf $ b.instantiate_var v,
--    saturate' t (e v)
-- | t e := pure e

-- meta def saturate (e : expr) : tactic expr :=
-- do t ← infer_type e >>= whnf,
--    saturate' t e

open nat (hiding to_pexpr) expr

meta def mk_motive : tactic expr :=
do (pi en bi d b) ← target,
   pure $ lam en bi d b

meta def destruct_multimap' : ℕ → expr → expr → list expr → tactic (list expr)
| 0 v₀ v₁ xs :=
do C ← mk_motive,
   refine ``(@typevec_cases_nil₂ %%C _),
   pure xs
| (succ n) v₀ v₁ xs :=
do C ← mk_motive,
   a ← mk_mvar, b ← mk_mvar,
   to_expr ``(append1 %%a %%b) tt ff >>= unify v₀,
   `(append1 %%a' %%b') ← pure v₁,
   refine ``(@typevec_cases_cons₂ _ %%b %%b' %%a %%a' %%C _),
   f ← intro `f,
   destruct_multimap' n a a' (f :: xs)

open_locale mvfunctor

meta def destruct_multimap (e : expr) : tactic (list expr) :=
do `(%%v₀ ⟹ %%v₁) ← infer_type e,
   `(typevec %%n) ← infer_type v₀,
   n ← eval_expr ℕ n,
   n_h ← revert e,
   destruct_multimap' n v₀ v₁ [] <*
     intron (n_h-1)

def santas_helper {n} {P : mvpfunctor n} {α} (C : P.obj α → Sort*) {a : P.A} {b} (b')
  (x : C ⟨a,b⟩) (h : b = b') : C ⟨a,b'⟩ :=
by cases h; exact x

open list

section zip_vars
variables (n : name) (univs : list level)
  (args : list expr) (shape_args : list expr)

meta def mk_child_arg (e : expr × list expr) : list (expr × expr × ℕ) → list (expr × expr × ℕ) × list expr × expr
| [] := ([],shape_args.tail,shape_args.head)
| (⟨v,e',i⟩::vs) :=
if v.occurs e.1
  then let c : expr := const ( (n.update_prefix $ n.get_prefix ++ v.local_pp_name).append_after i ) univs
       in ( ⟨v,e',i+1⟩::vs, shape_args, expr.lambdas e.2 $ e' $ c.mk_app $ args ++ e.2)
  else prod.map (cons ⟨v,e',i⟩) id $ mk_child_arg vs

meta def zip_vars' : list expr → list (expr × expr × ℕ) → list (expr × list expr) → list expr
| _ xs [] := []
| shape_args xs (v :: vs) :=
let (xs',shape_args',v') := mk_child_arg n univs args shape_args v xs in
v' :: zip_vars' shape_args' xs' vs

meta def zip_vars (ls : list (expr × expr)) (vs : list expr) : tactic $ list expr :=
do vs' ← vs.mmap $ λ v, do { (vs,_) ← infer_type v >>= mk_local_pis, pure (v,vs) },
   pure $ zip_vars' n univs args shape_args (ls.map $ λ x, (x.1,x.2,0)) vs'

end zip_vars

meta def mk_pfunc_recursor (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do let u := fresh_univ func.induct.u_names,
   v ← mk_live_vec func.vec_lvl $ func.live_params,
   fn ← mk_app `mvpfunctor.obj [functor_expr func,v],
   C ← mk_local' `C binder_info.implicit (expr.imp fn $ expr.sort $ level.param u),
   let dead_params := func.dead_params,
   cases_t ← func.induct.ctors.par_mmap $ λ c,
   do { let n := c.name.update_prefix (func.decl.to_name <.> "pfunctor"),
        let e := (@expr.const tt n func.induct.u_params).mk_app' [func.params,c.args],
        prod.mk c <$> (pis c.args (C e) >>= mk_local_def `v) },
   n ← mk_local_def `n fn,
   (_,df) ← solve_aux (expr.pis [n] $ C n) $ do
     { n ← intro1, [(_, [n_fst,n_snd], _)] ← cases_core n,
       hs ← cases_core n_fst,
       gs ← get_goals,
       gs ← list.mzip_with₃ (λ h g v,
         do { let ⟨c,h⟩ := (h : type_cnstr × expr),
              set_goals [g],
              ⟨n,xs,[(_,n_snd)]⟩ ← pure (v : name × list expr × list (name × expr)),
              fs ← destruct_multimap n_snd,
              n_snd ← mk_map_vec func.vec_lvl func.vec_lvl fs,
              let child_n := c.name.update_prefix $ func.induct.name <.> "child_t",
              let subst := func.live_params.zip fs,
              h_args ← zip_vars child_n func.induct.u_params (dead_params ++ xs) xs subst c.args,
              let h := h.mk_app h_args,
              let n_fst := (@const tt n func.induct.u_params).mk_app $ func.dead_params ++ xs,
              vec ← mk_live_vec func.vec_lvl $ func.live_params,
              fn ← mk_const ``santas_helper,
              unify_mapp fn [none,none,vec,C,none,none,n_snd,h,none] >>= refine ∘ to_pexpr,
              reflexivity <|> (congr; ext [rcases_patt.many [[rcases_patt.one `_]]] none; reflexivity),
              done }) cases_t gs hs,
       pure () },
   let vs := [func.params.map expr.to_implicit_local_const, C :: cases_t.map prod.snd],
   df ← instantiate_mvars df >>= lambdas' vs,
   t ← pis' (vs ++ [[n]]) (C n),
   emit_decl func.def_name $ mk_definition (func.pfunctor_name <.> "rec") (u :: func.induct.u_names) t df,
   pure ()

meta def mk_pfunc_rec_eqns (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do let u := fresh_univ func.induct.u_names,
   let rec := (@const tt (func.pfunctor_name <.> "rec") (level.param u :: func.induct.u_params)).mk_app func.params,
   let eqn := (@const tt func.eqn_name func.induct.u_params).mk_app func.params,
   (C::fs,_) ← infer_type rec >>= mk_local_pis,
   let rec := rec C,
   let fs := fs.init,
   mzip_with' (λ (c : type_cnstr) (f : expr), do
   { let cn := c.name.update_prefix $ c.name.get_prefix <.> "pfunctor",
     let c := (@const tt cn func.induct.u_params).mk_app func.params,
     (args,_) ← infer_type c >>= mk_local_pis,
     let x := c.mk_app args,
     t ← mk_app `eq [rec.mk_app' [fs,[x]],f.mk_app args] >>= pis' [func.params,C :: fs,args],
     df ← solve_async [] t $ do
     { intros, reflexivity },
     let n := cn.append_suffix "_rec",
     emit_decl func.def_name $ declaration.thm n (u :: func.induct.u_names) t df,
     add_eqn_lemmas n,
     simp_attr.typevec.set n () tt }) func.induct.ctors fs,
   skip

meta def mk_qpf_abs (func : internal_mvfunctor) : tactic unit :=
do let n := func.live_params.length,
   let dead_params := func.dead_params,
   let e := (@const tt func.def_name func.induct.u_params).mk_app dead_params,
   let e' := (@const tt func.pfunctor_name func.induct.u_params).mk_app dead_params,
   t ← to_expr ``(∀ v, mvpfunctor.obj %%e' v → %%e v),
   (_,df) ← @solve_aux unit t $ do
   { params ← map both <$> destruct_typevec' func.params' `v,
     C ← mk_motive,
     -- let params := (rb_map.sort prod.snd $ func.dead_params ++ vs).map prod.fst,
     let rec := @const tt (func.pfunctor_name <.> "rec") $ level.succ func.vec_lvl :: func.induct.u_params,
     let branches := list.repeat (@none expr) func.induct.ctors.length,
     rec ← unify_mapp rec (params.map some ++ C :: branches),
     refine ∘ to_pexpr $ rec,
     let cs := func.induct.ctors,
     let c' := cs.map $ λ c : type_cnstr, c.name.update_prefix $ c.name.get_prefix <.> "pfunctor",
     let eqn := (@const tt func.eqn_name func.induct.u_params).mk_app params,
     cs.mmap $ λ c, solve1 $ do
       { xs ← intros,
         let n := c.name.update_prefix func.induct.name,
         let e := (@const tt n func.induct.u_params).mk_app' [params,xs],
         mk_eq_mpr eqn e >>= exact },
     done },
   t ← pis dead_params t,
   df ← instantiate_mvars df >>= lambdas dead_params,
   emit_decl func.def_name $ mk_definition func.abs_name func.induct.u_names t df

meta def mk_qpf_repr (func : internal_mvfunctor) : tactic unit :=
do let n := func.live_params.length,
   let dead_params := func.dead_params,
   let e := (@const tt func.def_name func.induct.u_params).mk_app dead_params,
   let e' := (@const tt func.pfunctor_name func.induct.u_params).mk_app dead_params,
   t ← to_expr ``(∀ v, %%e v → mvpfunctor.obj %%e' v),
   (_,df) ← @solve_aux unit t $ do
   { params ← map both <$> destruct_typevec' func.params' `v,
     C ← mk_motive,
     -- let params := (rb_map.sort prod.snd $ func.dead_params ++ vs),
     let rec := @const tt (func.induct.name <.> "rec") $ level.succ func.vec_lvl :: func.induct.u_params,
     let branches := list.repeat (@none expr) func.induct.ctors.length,
     rec ← unify_mapp rec (params.map some ++ C :: branches),
     refine ∘ to_pexpr $ rec,
     let cs := func.induct.ctors,
     let c' := cs.map $ λ c : type_cnstr, c.name.update_prefix $ c.name.get_prefix <.> "pfunctor",
     let eqn := (@const tt func.eqn_name func.induct.u_params).mk_app params,
     cs.mmap $ λ c, solve1 $ do
       { xs ← intros,
         let n := c.name.update_prefix func.pfunctor_name,
         let e := (@const tt n func.induct.u_params).mk_app' [params,xs],
         exact e },
     done },
   t ← pis dead_params t,
   df ← instantiate_mvars df >>= lambdas dead_params,
   emit_decl func.def_name $ mk_definition func.repr_name func.induct.u_names t df

open bitraversable

meta def mk_pfunctor_map_eqn (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do params ← mmap_live' mk_fn_var func.params',
   -- fs ← mzip_with (λ x y : expr, mk_local_def `f $ x.imp y) func.live_params β,
   let fs := params.filter_map $ elim (λ _, none) (some ∘ fn_var.fn),
   vf ← mk_map_vec func.vec_lvl func.vec_lvl fs,
   let cs := func.induct.ctors.map $ λ c : type_cnstr, c.name.update_prefix func.pfunctor_name,
   let params' := params.map $ elim id fn_var.codom,
   cs.mmap' $ λ cn,
     do { let c := (@const tt cn func.induct.u_params).mk_app func.params,
          let c' := (@const tt cn func.induct.u_params).mk_app params',
          (vs,_) ← infer_type c >>= mk_local_pis,
          lhs ← mk_app ``mvfunctor.map [vf,c.mk_app vs],
          vs' ← vs.mmap $ λ v,
            do { some ⟨_,_,f⟩ ← pure $ (params.filter_map $ get_right id).find $ λ x, x.dom.occurs v | pure v,
                 (ws,_) ← infer_type v >>= mk_local_pis,
                 lambdas ws (f $ v.mk_app ws) },
          let rhs := c'.mk_app vs',
          let params := params.bind decls,
          t ← mk_app `eq [lhs,rhs] >>= pis' [params, vs],
          df ← solve_async [] t $ do
          { intros,
            dunfold_target cs,
            map_eq ← mk_const ``mvpfunctor.map_eq, rewrite_target map_eq { md := semireducible },
            simp_only [``(append_fun_comp'),``(nil_fun_comp)],
            done <|> reflexivity <|> (congr; ext [rcases_patt.many [[rcases_patt.one `_]]] none; reflexivity),
            done },
          let n := cn.append_suffix "_map",
          emit_decl func.def_name $ declaration.thm n func.induct.u_names t df,
          simp_attr.typevec.set n () tt },
   skip

meta def prove_abs_repr (func : internal_mvfunctor) : tactic unit :=
do vs ← destruct_typevec' func.params' `α,
   let cs := func.induct.ctors.map $ λ c : type_cnstr, c.name.update_prefix func.pfunctor_name,
   x ← intro1, cases x,
   repeat $ do
   { dunfold_target [func.repr_name,func.abs_name],
     simp_only [``(typevec.cases_nil_append1),``(typevec.cases_cons_append1)],
     dunfold_target $ [func.pfunctor_name <.> "rec"] ++ cs,
     `[dsimp],
     reflexivity }

meta def prove_abs_map (func : internal_mvfunctor) : tactic unit :=
do vs ← destruct_typevec₃ func.params' `α,
   C ← mk_motive,
   -- let vs := vs.map $ λ ⟨α,β,f,i⟩, (α,i),
   -- let params := (rb_map.sort prod.snd $ func.dead_params ++ vs).map prod.fst,
   let params := vs.map $ elim id fn_var.dom,
   let rec_n := func.pfunctor_name <.> "rec",
   let rec := (@const tt rec_n $ level.zero :: func.induct.u_params).mk_app params C,
   let cs := func.induct.ctors.map $ λ c : type_cnstr, c.name.update_prefix func.pfunctor_name,
   apply rec,
   all_goals $ do
   { intros,
     dunfold_target [func.repr_name,func.abs_name],
     simp_only [``(typevec.cases_nil_append1),``(typevec.cases_cons_append1)] [`typevec],
     reflexivity },
   pure ()

meta def mk_mvqpf_instance (func : internal_mvfunctor) : tactic unit :=
do let n := func.live_params.length,
   let dead_params := func.dead_params,
   let e := (@const tt func.def_name func.induct.u_params).mk_app dead_params,
   let abs_fn := (@const tt func.abs_name func.induct.u_params).mk_app dead_params,
   let repr_fn := (@const tt func.repr_name func.induct.u_params).mk_app dead_params,
   mk_qpf_abs func,
   mk_qpf_repr func,
   mk_pfunctor_map_eqn func,
   pfunctor_i ← mk_mapp ``mvfunctor [some (reflect n),e] >>= mk_instance,
   mvqpf_t ← mk_mapp ``mvqpf [some (reflect n),e,pfunctor_i] >>= instantiate_mvars,
   (_,df) ← solve_aux mvqpf_t $ do
     { let p := (@const tt func.pfunctor_name func.induct.u_params).mk_app dead_params,
       refine ``( { P := %%p, abs := %%abs_fn, repr := %%repr_fn, .. } ),
       prove_goal_async' dead_params $ prove_abs_repr func,
       prove_goal_async' dead_params $ prove_abs_map func },
   df ← instantiate_mvars df >>= lambdas dead_params,
   mvqpf_t ← pis dead_params mvqpf_t,
   let inst_n := func.def_name <.> "mvqpf",
   emit_decl func.def_name $ mk_definition inst_n func.induct.u_names mvqpf_t df,
   set_basic_attribute `instance inst_n

meta def mk_conj : list expr → expr
| [] := `(true)
| [x] := x
| (x :: xs) := @const tt ``and [] x (mk_conj xs)

def list.lookup {α β} [decidable_eq α] (a : α) : list (α × β) → option β
| []             := none
| (⟨a', b⟩ :: l) := if h : a' = a then some b else list.lookup l

meta def replace_all (e : expr) (σ : list (expr × expr)) : expr :=
expr.replace e $ λ x _, list.lookup x σ

meta def mk_liftp_eqns (func : internal_mvfunctor) : tactic unit :=
do let my_t := (@const tt func.induct.name func.induct.u_params).mk_app func.params,
   let F := (@const tt func.def_name func.induct.u_params).mk_app $ func.dead_params,
   let internal_eq := (@const tt func.eqn_name func.induct.u_params).mk_app func.params,
   x ← mk_local_def `x my_t,
   x' ← mk_eq_mpr internal_eq x,
   let live_params := func.live_params,
   v ← mk_live_vec func.vec_lvl live_params,
   fs ← live_params.mmap $ λ v, mk_local_def `f $ v.imp `(Prop),
   let m := rb_map.of_list $ list.zip live_params fs,
   fv ← mk_map_vec func.vec_lvl level.zero fs,
   fv_map ← fs.mmap (λ f, mk_mapp ``subtype.val [none,f]) >>= mk_map_vec func.vec_lvl func.vec_lvl,
   fv_t ← fs.mmap (λ f, mk_mapp ``subtype [none,f]) >>= mk_live_vec func.vec_lvl,
   let n := func.live_params.length,
   df ← mk_mapp ``mvfunctor.liftp' [`(n),F,none,v,fv],
   func.induct.ctors.mmap $ λ c, do
   { let e := (@const tt c.name func.induct.u_params).mk_app' [func.params, c.args],
     x' ← mk_eq_mpr internal_eq e,
     args ← c.args.mmap $ λ arg, do
       { (args,rhs_t) ← infer_type arg >>= mk_local_pis,
         (some f) ← pure $ m.find rhs_t | pure [],
         list.ret <$> pis args (f $ arg.mk_app args) },
     let rhs := mk_conj args.join,
     t ← pis (c.args.map to_implicit_local_const) $ (df x').imp rhs,
     df ← solve_async [func.params,fs] t $ do
     { solve1 $ do
       { args ← intron' c.args.length,
         mk_const ``mvfunctor.liftp_def >>= rewrite_target,
         dunfold_target [``mvfunctor.map],
         h ← intro `h,
         t ← infer_type h,
         let n := func.live_params.length,
         x ← mk_mapp ``subtype_ [`(n),none,fv],
         y ← mk_mapp ``typevec.subtype_val [`(n),none,fv],
         h' ← assertv `h' (replace_all t [(x,fv_t),(y,fv_map)]) h, clear h,
         [(_,[x,y],_)] ← cases_core h',
         hs ← cases_core x,
         gs ← get_goals,
         gs ← (gs.zip hs.enum).mmap $ λ ⟨g,i,n,x,b⟩,
         do { set_goals [g],
              eqn ← mk_const $ (func.induct.name ++ `internal.map._equation).append_after i,
              h' ← rewrite_hyp eqn (y.instantiate_locals b) { md := semireducible },
              t ← target,
              cases h',
              get_goals },
         set_goals gs.join,
         repeat $ do { split, intros, applyc ``subtype.property },
         intros, applyc ``subtype.property <|> interactive.trivial,
         done },
       done },
     t ← pis ((func.params ++ fs).map to_implicit_local_const) t,
     let n := c.name.append_suffix "_liftp",
     emit_decl func.def_name $ declaration.thm n func.induct.u_names t df },
   skip

-- #check @typevec.liftr_def
-- #check @typevec.liftr'
-- #exit
meta def mk_exists : list expr → expr → tactic expr
| [] e := pure e
| (x :: xs) e :=
trace_scope $
  do e ← mk_exists xs e >>= lambdas [x],
     mk_app ``Exists [e]

meta def mk_liftp_defn' (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do let F := (@const tt func.induct.name func.induct.u_params).mk_app func.params,
   x ← mk_local_def `x F,
   params ← func.params'.mmap $ bitraverse (pure ∘ to_implicit_local_const) mk_pred_var,
   let fs := params.filter_map $ get_right prod.snd,
   let m := rb_map.of_list $ list.zip func.live_params fs,
   let n := func.induct.name <.> "liftp",
   cs ← func.induct.ctors.mmap $ λ c, do
   { let constr := @const tt c.name func.induct.u_params,
     args' ← c.args.mmap (λ arg₀ : expr, do
       { (args,rhs_t) ← infer_type arg₀ >>= mk_local_pis,
         (some f) ← pure $ m.find rhs_t | pure (sum.inl arg₀),
         v ← pis args (f (arg₀.mk_app args) ) >>= mk_local_def `h,
         pure (sum.inr (arg₀, v)) } ),
     let x := constr.mk_app $ func.params ++ args'.map (elim id prod.fst),
     pure { type_cnstr .
           name := n ++ c.name,
           args := args'.bind decls',
           result := [x],
           infer := environment.implicit_infer_kind.implicit  } },
   let decl : inductive_type :=
       { name := n,
         params := params.bind decls',
         idx := [x],
         type := `(Prop),
         ctors := cs,
         .. func.induct },
   mk_inductive func.induct.name decl,
   skip

meta def mk_liftr_defn' (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do let F := (@const tt func.induct.name func.induct.u_params).mk_app func.params,
   x ← mk_local_def `x F, y ← mk_local_def `y F,
   params ← func.params'.mmap $ bitraverse (pure ∘ to_implicit_local_const) mk_rel_var,
   let fs := params.filter_map $ get_right prod.snd,
   let m := rb_map.of_list $ list.zip func.live_params fs,
   let n := func.induct.name <.> "liftr",
   cs ← func.induct.ctors.mmap $ λ c, do
   { args ← c.args.mmap renew,
     let constr := @const tt c.name func.induct.u_params,
     args' ← mzip_with (λ arg₀ arg₁ : expr, do
       { (args,rhs_t) ← infer_type arg₀ >>= mk_local_pis,
         (some f) ← pure $ m.find rhs_t | pure (sum.inl arg₀),
         v ← pis args (f (arg₀.mk_app args) (arg₁.mk_app args) ) >>= mk_local_def `h,
         pure (sum.inr $ fn_var.mk arg₀ arg₁ v) } ) c.args args,
     let x := constr.mk_app $ func.params ++ args'.map (elim id fn_var.dom),
     let y := constr.mk_app $ func.params ++ args'.map (elim id fn_var.codom),
     pure { type_cnstr .
           name := n ++ c.name,
           args := args'.bind decls,
           result := [x,y],
           infer := environment.implicit_infer_kind.implicit  } },
   let decl : inductive_type :=
       { name := n,
         params := params.bind decls',
         idx := [x,y],
         type := `(Prop),
         ctors := cs,
         .. func.induct },
   mk_inductive func.induct.name decl,
   skip

meta def resolve : expr → tactic expr
| e@(local_const uniq pp bi t) :=
  do t ← infer_type e,
     pure (local_const uniq pp bi t)
| e := pure e

open function (uncurry)

lemma apply_uncurried {α β} {f : α → β → Sort*} : Π {x : α × β}, uncurry f x → f x.1 x.2
| (x,y) := id

lemma apply_curried {α β} {f : α → β → Sort*} : Π {x : α} {y : β}, f x y → uncurry f (x,y)
| x y := id

meta def intro_local_def (n : name) (t : expr) : tactic expr :=
do `(true) ← (↑`(true) <$ done) <|> target | fail "expecting trivial goal",
   v ← mk_meta_var $ pi n binder_info.default t `(true),
   set_goals [v],
   intro1

meta def zip_goals_with {α β} (xs : list α) (f : α → tactic β) : tactic (list β) :=
do gs ← get_goals,
   gs' ← mzip_with (λ x g,
       do set_goals [g],
          prod.mk <$> f x <*> get_goals ) xs gs,
   let ⟨xs',gs'⟩ := gs'.unzip,
   set_goals gs'.join,
   return xs'


meta def extract_pattern_p (σ : list (name × expr)) : tactic (list expr) :=
do [x] ← pure $ (σ.map prod.snd).filter $ λ x, is_app x,
   pure (x.get_app_args)

meta def extract_pattern_r (σ : list (name × expr)) : tactic (list expr × list expr) :=
do [x,y] ← pure $ (σ.map prod.snd).filter $ λ x, is_app x,
   pure (x.get_app_args, y.get_app_args)

meta def mk_pred_args (m : list (expr × expr)) : list expr → tactic (list expr)
| (x :: xs) :=
 do some p ← pure $ m.find (λ p : expr × expr, x.occurs p.2)
         | (::) x <$> mk_pred_args xs,
    (vs,t) ← mk_local_pis p.2,
    let f := t.get_app_fn,
    let p' := p.1.mk_app vs,
    x' ← mk_mapp ``subtype.mk [none,f,t.app_arg,p'] >>= lambdas vs,
    xs' ← mk_pred_args xs,
    return (x' :: xs')
| _ := pure []

meta def mk_rel_args (m : list (expr × expr)) : list expr → list expr → tactic (list expr)
| (x :: xs) (y :: ys) :=
trace_scope $
  if x = y then (::) x <$> mk_rel_args xs ys
           else do
             p ← m.find (λ p : expr × expr, x.occurs p.2),
             (vs,t) ← mk_local_pis p.2,
             unc ← mk_mapp ``uncurry [none,none,none,t.get_app_fn],
             x' ← mk_app ``prod.mk t.get_app_args,
             p' ← mk_app ``apply_curried [p.1.mk_app vs],
             x' ← mk_mapp ``subtype.mk [none,unc,x',p'] >>= lambdas vs,
             xs' ← mk_rel_args xs ys,
             return (x' :: xs')
| _ _ := pure []

meta def mk_rel_proof_map (s : expr_set) : list expr → tactic (list expr)
| [] := pure []
| (x :: xs) :=
  do ps ← mk_rel_proof_map xs,
     t ← infer_type x,
     let b : bool := t.fold ff $ λ e _ b, b ∨ (e.is_local_constant ∧ s.contains e),
     if b then pure $ x :: ps
          else pure ps

meta def mk_liftp_eqns₀ (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do params ← func.params'.mmap_live' mk_pred_var,
   let F := (@const tt func.induct.name func.induct.u_params).mk_app $ params.map $ elim id prod.fst,
   let F_intl := (@const tt func.def_name func.induct.u_params).mk_app func.dead_params,
   let n := func.live_params.length,
   vec ← mk_live_vec func.vec_lvl func.live_params,
   let fs := params.filter_map $ get_right prod.snd,
   map_f ← mk_map_vec func.vec_lvl func.vec_lvl fs,
   x ← mk_local_def `x F,
   let vs := [params.bind $ decls' ∘ bimap to_implicit_local_const (bimap to_implicit_local_const id),[x]],
   liftp ← mk_mapp ``mvfunctor.liftp' [`(n),F_intl,none,vec],
   let df := liftp map_f x,
   mk_const ``mvfunctor.liftp_def,
   fn ← mk_mapp ``is_lawful_mvfunctor [`(n),F_intl,none] >>= mk_instance,
   defn ← mk_mapp ``mvfunctor.liftp_def [`(n),F_intl,none,vec], -- ,map_f,none,x,y
   let defn := defn map_f fn x,
   param_sub ← params.mmap_live' $ λ ⟨α,f⟩,
   do { σ ← mk_mapp ``subtype [none,f],
        pure (α,f,σ) },
   let F_sub := (@const tt func.induct.name func.induct.u_params).mk_app $ param_sub.map $ elim id $ prod.snd ∘ prod.snd,
   u ← mk_local_def `u F_sub,
   args ← list.join <$> param_sub.mmap (elim (pure ∘ list.ret) $ λ ⟨α,unc,σ⟩,
           do { val ← mk_mapp ``subtype.val [none,unc],
                -- f ← to_expr ``(%%val),
                pure [σ,α,val] }),
   let map  := (@const tt (func.induct.name <.> "map") func.induct.u_params).mk_app args u,
   l ← mk_app ``eq [map,x],
   -- trace_expr df,
   `(@Exists %%t₀ _) ← whnf df,
   let lhs := df,
   rhs ← mk_exists [u] l,
   t ← mk_app `iff [lhs,rhs],
   is_def_eq F_sub t₀ <|> fail "not def eq",
   trace!"F_sub : {F_sub}",
   trace!"t₀    : {t₀}",
   -- trace!"t₀    : {whnf t₀}",
   trace!"defn  : {infer_type defn}",
   trace!"t     : {t}",
   (_,pr) ← solve_aux t $ refine ``(iff.trans %%defn (iff.refl _)),
   t ← pis' vs t,
   pr ← instantiate_mvars pr >>= lambdas' vs,
   let vars := pr.list_local_consts,
   emit_decl func.def_name $ mk_definition (func.induct.name <.> "liftp_def") func.induct.u_names t pr,
   skip

meta def mk_liftp_eqns₁ (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do let F := (@const tt func.induct.name func.univ_params).mk_app func.params,
   let F_intl := (@const tt func.def_name func.univ_params).mk_app func.dead_params,
   let n := func.live_params.length,
   α ← mk_live_vec func.vec_lvl func.live_params,
   -- let v_liftr :=
   params ← func.params'.mmap_live' mk_pred_var,
   let fs₀ := params.filter_map $ get_right id,
   fs' ← params.mmap_live' $ λ ⟨v,f⟩,
     do { t ← mk_mapp ``subtype [none,f],
          pure (f,t) },
   let fs := fs'.filter_map $ get_right prod.fst,
   let fsₛ := fs'.map $ elim id prod.snd,
   map_f ← mk_map_vec func.vec_lvl func.vec_lvl fs,
   lhs ← mk_mapp ``mvfunctor.liftp' [`(n),F_intl,none,α],
   x ← intro_local_def `x F,
   let lhs := lhs map_f x,
   let vs := [params.bind decls',[x]],
   let rhs := (@const tt (func.induct.name <.> "liftp") func.univ_params).mk_app' vs,
   t ← mk_app `iff [lhs,rhs],
   let fs' := (fs₀.map prod.snd).to_rb_set,
   pr ← solve_async vs t $
   do { mk_const (func.induct.name <.> "liftp_def") >>= rewrite_target,
        split,
        solve1 $
        do { x ← intro1,
             [(c,[x,h],_)] ← cases_core x [`a,`h],
             (s,u) ← mk_simp_set tt [`typevec] [],
             σ ← cases_core x,
             σ.mmap $ λ ⟨a,b,c⟩, solve1 $
             do { h ← simp_hyp s u (h.instantiate_locals c),
                  mk_eq_symm h >>= rewrite_target,
                  constructor,
                  all_goals $ solve1 $
                  do { intros,
                       (expr.app f (expr.app _ x)) ← target,
                       h ← mk_mapp ``subtype.property [none,none,x],
                       apply h,
                       skip } },
             skip },
        solve1 $
        do { x ← intro1,
             vs ← resolve x >>= cases_core,
             param_sub ← params.mmap_live' $ λ ⟨α,f⟩,
             do { σ ← mk_mapp ``subtype [none,f],
                  pure (α,f,σ) },
             let F_sub := (@const tt func.induct.name func.induct.u_params).mk_app $ param_sub.map $ elim id $ prod.snd ∘ prod.snd,
             zip_goals_with (func.induct.ctors.zip vs) $ λ ⟨c,c',vs,σ⟩,
               do { x ← extract_pattern_p σ,
                    m ← mk_rel_proof_map fs' vs,
                    m' ← m.mmap infer_type,
                    args ← mk_pred_args (m.zip m') x,
                    let u := (@const tt c.name func.univ_params).mk_app' [fsₛ, args.drop params.length],
                    existsi u,
                    `[simp only [(∘)] with typevec],
                    repeat $ () <$ split,
                    done },
             skip },
        done },
   t ← pis' vs t,
   emit_decl func.def_name $ declaration.thm (func.induct.name <.> "liftp_iff") func.induct.u_names t pr,
   skip

meta def mk_liftr_eqns₀ (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do params ← func.params'.mmap_live' mk_rel_var,
   let F := (@const tt func.induct.name func.induct.u_params).mk_app $ params.map $ elim id prod.fst,
   let F_intl := (@const tt func.def_name func.induct.u_params).mk_app func.dead_params,
   let n := func.live_params.length,
   vec ← mk_live_vec func.vec_lvl func.live_params,
   fs ← (params.filter_map $ get_right id).mmap $ λ ⟨v,f⟩,
     mk_mapp ``function.uncurry [none,none,none,f],
   map_f ← mk_map_vec func.vec_lvl func.vec_lvl fs,
   x ← mk_local_def `x F, y ← mk_local_def `y F,
   let vs := [params.bind $ decls' ∘ bimap to_implicit_local_const (bimap to_implicit_local_const id),[x,y]],
   liftr ← mk_mapp ``mvfunctor.liftr' [`(n),F_intl,none,vec],
   let df := liftr map_f x y,
   mk_const ``mvfunctor.liftr_def,
   fn ← mk_mapp ``is_lawful_mvfunctor [`(n),F_intl,none] >>= mk_instance,
   defn ← mk_mapp ``mvfunctor.liftr_def [`(n),F_intl,none,vec], -- ,map_f,none,x,y
   let defn := defn map_f fn x y,
   param_sub ← params.mmap_live' $ λ ⟨α,f⟩,
   do { unc ← mk_mapp ``function.uncurry [none,none,none,f],
        σ ← mk_mapp ``subtype [none,unc],
        pure (α,unc,σ) },
   let F_sub := (@const tt func.induct.name func.induct.u_params).mk_app $ param_sub.map $ elim id $ prod.snd ∘ prod.snd,
   u ← mk_local_def `u F_sub,
   let mk_args := λ prj : pexpr,
       list.join <$> param_sub.mmap (elim (pure ∘ list.ret) $ λ ⟨α,unc,σ⟩,
           do { val ← mk_mapp ``subtype.val [none,unc],
                f ← to_expr ``(%%prj ∘ %%val),
                pure [σ,α,f] }),
   args  ← mk_args ``(prod.fst),
   args' ← mk_args ``(prod.snd),
   let map  := (@const tt (func.induct.name <.> "map") func.induct.u_params).mk_app args u,
   let map' := (@const tt (func.induct.name <.> "map") func.induct.u_params).mk_app args' u,
   l ← mk_app ``eq [map,x],
   r ← mk_app ``eq [map',y],
   let lhs := df,
   rhs ← mk_app ``and [l,r] >>= mk_exists [u],
   t ← mk_app `iff [lhs,rhs],
   (_,pr) ← solve_aux t $ refine ``(iff.trans %%defn (iff.refl _)),
   t ← pis' vs t,
   pr ← instantiate_mvars pr >>= lambdas' vs,
   let vars := pr.list_local_consts,
   emit_decl func.def_name $ mk_definition (func.induct.name <.> "liftr_def") func.induct.u_names t pr,
   skip

meta def mk_liftr_eqns₁ (func : internal_mvfunctor) : tactic unit :=
trace_scope $
do let F := (@const tt func.induct.name func.univ_params).mk_app func.params,
   let F_intl := (@const tt func.def_name func.univ_params).mk_app func.dead_params,
   let n := func.live_params.length,
   α ← mk_live_vec func.vec_lvl func.live_params,
   -- let v_liftr :=
   params ← func.params'.mmap_live' mk_rel_var,
   let fs₀ := params.filter_map $ get_right id,
   fs' ← params.mmap_live' $ λ ⟨v,f⟩,
     do { f' ← mk_mapp ``function.uncurry [v,v,none,f],
          t ← mk_mapp ``subtype [none,f'],
          pure (f',t) },
   let fs := fs'.filter_map $ get_right prod.fst,
   let fsₛ := fs'.map $ elim id prod.snd,
   map_f ← mk_map_vec func.vec_lvl func.vec_lvl fs,
   lhs ← mk_mapp ``mvfunctor.liftr' [`(n),F_intl,none,α],
   x ← intro_local_def `x F,
   y ← intro_local_def `y F,
   let lhs := lhs map_f x y,
   let vs := [params.bind decls',[x,y]],
   let rhs := (@const tt (func.induct.name <.> "liftr") func.univ_params).mk_app' vs,
   t ← mk_app `iff [lhs,rhs],
   let fs' := (fs₀.map prod.snd).to_rb_set,
   pr ← solve_async vs t $
   do { mk_const (func.induct.name <.> "liftr_def") >>= rewrite_target,
        split,
        solve1 $
        do { x ← intro1,
             [(c,[x,h],_)] ← cases_core x [`a,`h],
             (s,u) ← mk_simp_set tt [`typevec] [],
             σ ← cases_core x,
             σ.mmap $ λ ⟨a,b,c⟩, solve1 $
             do { h ← simp_hyp s u (h.instantiate_locals c),
                  [(c,[h₀,h₁],_)] ← cases_core h [`h₀,`h₁],
                  mk_eq_symm h₀ >>= rewrite_target,
                  mk_eq_symm h₁ >>= rewrite_target,
                  constructor,
                  all_goals $ solve1 $
                  do { intros,
                       (expr.app (expr.app f (expr.app _ x)) y) ← target,
                       h ← mk_mapp ``subtype.property [none,none,x],
                       mk_app ``apply_uncurried [h] >>= apply,
                       skip } },
             skip },
        solve1 $
        do { x ← intro1,
             vs ← resolve x >>= cases_core,
             param_sub ← params.mmap_live' $ λ ⟨α,f⟩,
             do { unc ← mk_mapp ``function.uncurry [none,none,none,f],
                  σ ← mk_mapp ``subtype [none,unc],
                  pure (α,unc,σ) },
             let F_sub := (@const tt func.induct.name func.induct.u_params).mk_app $ param_sub.map $ elim id $ prod.snd ∘ prod.snd,
             zip_goals_with (func.induct.ctors.zip vs) $ λ ⟨c,c',vs,σ⟩,
               do { (x,y) ← extract_pattern_r σ,
                    m ← mk_rel_proof_map fs' vs,
                    m' ← m.mmap infer_type,
                    args ← mk_rel_args (m.zip m') x y,
                    let u := (@const tt c.name func.univ_params).mk_app' [fsₛ, args.drop params.length],
                    existsi u,
                    `[simp only [(∘)] with typevec],
                    repeat $ () <$ split,
                    done },
             skip },
        done },
   t ← pis' vs t,
   emit_decl func.def_name $ declaration.thm (func.induct.name <.> "liftr_iff") func.induct.u_names t pr,
   skip

-- meta def mk_liftr_defn (func : internal_mvfunctor) : tactic unit :=
-- do params ← func.params'.mmap_live' mk_rel_var,
--    let F := (@const tt func.induct.name func.induct.u_params).mk_app $ params.map $ elim id prod.fst,
--    let F_intl := (@const tt func.def_name func.induct.u_params).mk_app func.dead_params,
--    let n := func.live_params.length,
--    let internal_eq := (@const tt func.eqn_name func.induct.u_params).mk_app func.params,
--    vec ← mk_live_vec func.vec_lvl func.live_params,
--    fs ← (params.filter_map get_right).mmap $ λ ⟨v,f⟩,
--      mk_mapp ``function.uncurry [none,none,none,f],
--    map_f ← mk_map_vec func.vec_lvl func.vec_lvl fs,
--    x ← mk_local_def `x F, y ← mk_local_def `y F,
--    let vs := [params.bind $ decls' ∘ bimap to_implicit_local_const (bimap to_implicit_local_const id),[x,y]],
--    x' ← mk_eq_mpr internal_eq x, y' ← mk_eq_mpr internal_eq y,
--    liftr ← mk_mapp ``typevec.liftr' [`(n),F_intl,none,vec],
--    t ← pis' vs `(Prop),
--    df ← lambdas' vs $ liftr map_f x' y',
--    df ← emit_decl _' $ mk_definition (func.induct.name <.> "liftr") func.induct.u_names t df,

--    /- now generate equation -/
--    defn ← mk_mapp ``typevec.liftr_def [`(n),F_intl,none,vec,map_f,none,x',y'],
--    param_sub ← params.mmap_live' $ λ ⟨α,f⟩,
--    do { unc ← mk_mapp ``function.uncurry [none,none,none,f],
--         σ ← mk_mapp ``subtype [none,unc],
--         pure (α,unc,σ) },
--    let F_sub := (@const tt func.induct.name func.induct.u_params).mk_app $ param_sub.map $ elim id $ prod.snd ∘ prod.snd,
--    u ← mk_local_def `u F_sub,
--    let mk_args := λ prj : pexpr,
--        list.join <$> param_sub.mmap (elim (pure ∘ list.ret) $ λ ⟨α,unc,σ⟩,
--            do { val ← mk_mapp ``subtype.val [none,unc],
--                 f ← to_expr ``(%%prj ∘ %%val),
--                 pure [σ,α,f] }),
--    args  ← mk_args ``(prod.fst),
--    args' ← mk_args ``(prod.snd),
--    let map  := (@const tt (func.induct.name <.> "map") func.induct.u_params).mk_app args u,
--    let map' := (@const tt (func.induct.name <.> "map") func.induct.u_params).mk_app args' u,
--    l ← mk_app ``eq [map,x],
--    r ← mk_app ``eq [map',y],
--    let lhs := df.mk_app' vs,
--    rhs ← mk_app ``and [l,r] >>= mk_exists [u],
--    t ← mk_app `iff [lhs,rhs],
--    (_,pr) ← solve_aux t $ refine ``(iff.trans %%defn (iff.refl _)),
--    t ← pis' vs t,
--    pr ← instantiate_mvars pr >>= lambdas' vs,
--    let vars := pr.list_local_consts,
--    emit_decl _ $ mk_definition (func.induct.name <.> "liftr_def") func.induct.u_names t pr,
--    skip

-- meta def mk_liftr_eqns (func : internal_mvfunctor) : tactic unit :=
-- do let my_t := (@const tt func.induct.name func.induct.u_params).mk_app func.params,
--    let F := (@const tt func.def_name func.induct.u_params).mk_app $ func.dead_params,
--    let internal_eq := (@const tt func.eqn_name func.induct.u_params).mk_app func.params,
--    x ← mk_local_def `x my_t,
--    x' ← mk_eq_mpr internal_eq x,
--    params ← func.params'.mmap_live' mk_rel_var,
--    let live_params := func.live_params,
--    v ← mk_live_vec func.vec_lvl live_params,
--    let fs := params.filter_map $ (<$>) prod.snd ∘ get_right,
--    -- fs ← live_params.mmap $ λ v,
--    --   do { -- prod ← mk_app ``prod.mk [v,v],
--    --        v ← mk_local_def `f $ v.imp $ v.imp `(Prop),
--    --        v' ← mk_mapp ``function.uncurry [none,none,none,v],
--    --        pure (v,v') },
--    prod_params ← func.params'.mmap $ elim pure $ λ v, mk_app ``_root_.prod [v,v],
--    let internal_eq' := (@const tt func.eqn_name func.induct.u_params).mk_app prod_params,
--    let m := rb_map.of_list $ list.zip live_params fs,
--    -- fv ← mk_map_vec func.vec_lvl level.zero $ fs.map prod.snd,
--    -- fv_map ← fs.mmap (λ f, mk_mapp ``subtype.val [none,f.2]) >>= mk_map_vec func.vec_lvl func.vec_lvl,
--    -- fv_t ← fs.mmap (λ f, mk_mapp ``subtype [none,f.2]) >>= mk_live_vec func.vec_lvl,
--    let n := func.live_params.length,
--    -- df ← mk_mapp ``typevec.liftr' [`(n),F,none,v],
--    let df := (@const tt (func.induct.name <.> "liftr") func.induct.u_params).mk_app (params.bind decls'),
--    -- let df := df fv,
--    -- df ← mk_mapp ``typevec.liftr' [`(n),F,none,v,fv],
--    param_sub ← params.mmap_live' $ λ ⟨α,f⟩,
--    do { unc ← mk_mapp ``function.uncurry [none,none,none,f],
--         σ ← mk_mapp ``subtype [none,unc],
--         pure (α,unc,σ) },
--    let F_sub := (@const tt func.induct.name func.induct.u_params).mk_app $ param_sub.map $ elim id $ prod.snd ∘ prod.snd,
--    func.induct.ctors.mmap $ λ c, do
--    { args ← c.args.mmap renew,
--      let constr := @const tt c.name func.induct.u_params,
--      let e₀ := constr.mk_app $ func.params ++ c.args,
--      let e₁ := constr.mk_app $ func.params ++ args,
--      args' ← mzip_with (λ a b, mk_app ``prod.mk [a,b]) c.args args,
--      let e₂ := constr.mk_app $ prod_params ++ args',
--      -- x₀ ← mk_eq_mpr internal_eq e₀,
--      -- x₁ ← mk_eq_mpr internal_eq e₁,
--      x₂ ← mk_eq_mpr internal_eq' e₂,
--      args' ← mzip_with (λ arg₀ arg₁ : expr, do
--        { (args,rhs_t) ← infer_type arg₀ >>= mk_local_pis,
--          (some f) ← pure $ m.find rhs_t | pure [],
--          list.ret <$> pis args (f (arg₀.mk_app args) (arg₁.mk_app args) ) } ) c.args args,
--      trace "• 2",
--      -- let rhs := mk_conj args'.join,
--      let args' := args'.join,
--      t ← pis ((c.args ++ args).map to_implicit_local_const) $ args'.foldr (λ l r, l.imp r) (df e₀ e₁),
--      trace t,
--      (_,df) ← solve_aux t $ do
--      { solve1 $ do
--        { args₀ ← intron' c.args.length,
--          args₁ ← intron' c.args.length,
--          -- mk_const (func.induct.name <.> "liftr") >>= trace_expr,
--          mk_const (func.induct.name <.> "liftr_def") >>= rewrite_target,
--          -- dunfold_target [``mvfunctor.map],
--          hs ← intron' $ args'.length,

--          -- h ← intro `h,
--          -- t ← infer_type h,
--          let n := func.live_params.length,
--          u ← mk_meta_var F_sub,
--          gs ← get_goals, set_goals $ u :: gs,
--          constructor,
--          trace_state,

--          trace "\n• • •",
--          -- x ← mk_mapp ``subtype_ [`(n),none,fv],
--          trace_expr df,
--          trace_expr x,
--          trace "• • •\n",

--          trace_state,
--          -- existsi x₂,
--          done,
--          trace "•",
--          trace_state, done,
--    -- y ← mk_mapp ``typevec.subtype_val [`(n),none,fv],
--          -- h' ← assertv `h' (replace_all t [(x,fv_t),(y,fv_map)]) h, clear h,
--          -- [(_,[x,y],_)] ← cases_core h',
--          -- hs ← cases_core x,
--          -- gs ← get_goals,
--          -- gs ← (gs.zip hs.enum).mmap $ λ ⟨g,i,n,x,b⟩,
--          -- do { set_goals [g],
--          --      eqn ← mk_const $ (func.induct.name ++ `internal.map._equation).append_after i,
--          --      h' ← rewrite_hyp eqn (y.instantiate_locals b) { md := semireducible },
--          --      t ← target,
--          --      cases h',
--          --      get_goals },
--          -- set_goals gs.join,
--          -- repeat $ do { split, intros, applyc ``subtype.property },
--          -- intros, applyc ``subtype.property <|> interactive.trivial,
--          done },
--        done },
--      t ← pis ((params.bind decls').map to_implicit_local_const) t,
--      df ← instantiate_mvars df >>= lambdas (params.bind decls'),
--      -- trace_state,
--      -- emit_decl _ $ declaration.thm (c.name.append_suffix "_liftr") func.induct.u_names t (pure df),
--      skip },

--    skip

open interactive lean.parser lean

@[user_attribute]
meta def qpf_attribute : user_attribute :=
{ name := `qpf,
  descr := "derive qpf machinery for inductive type",
  after_set := some $ λ n p t,
-- trace_error
trace_scope $
(do func ← mk_internal_functor n,
    mk_mvfunctor_instance func,
    mk_pfunctor func,
    mk_pfunc_constr func,
    mk_pfunc_recursor func,
    -- trace_error $ mk_pfunc_rec_eqns func,
    -- mk_pfunc_map func,
    -- mk_pfunc_mvfunctor_instance func,
    mk_mvqpf_instance func,
    -- mk_liftp_eqns func,
    mk_liftp_defn' func,
    mk_liftp_eqns₀ func,
    mk_liftp_eqns₁ func,
    mk_liftr_defn' func,
    mk_liftr_eqns₀ func,
    mk_liftr_eqns₁ func,
    pure ())
 }

end tactic
open function typevec typevec.prod
