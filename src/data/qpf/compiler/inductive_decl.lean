/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import meta.expr
import tactic.core
import tactic.mk_has_to_format
import .for_mathlib

namespace tactic
open expr
open environment ( implicit_infer_kind intro_rule ) environment.implicit_infer_kind

attribute [derive has_to_format] binder_info implicit_infer_kind
attribute [derive has_reflect] implicit_infer_kind

@[derive [has_reflect,has_to_format]]
meta structure type_cnstr :=
(name : name)
(args : list expr)
(result : list expr)
(infer : implicit_infer_kind)

meta def local_ctor (n : name) : expr → expr :=
local_const n n binder_info.default

meta instance : has_to_format type_cnstr :=
{ to_format := λ ⟨n,a,r,_⟩, format!"{n} : {expr.pis a $ (@const tt `type []).mk_app r}" }


@[derive [has_reflect,has_to_format]]
meta structure inductive_type :=
(pre : name)
(name : name)
(u_names : list _root_.name)
(params : list expr)
(idx : list expr)
(type : expr)
(ctors : list type_cnstr)

-- meta instance inductive_type.has_to_tactic_format : has_to_tactic_format inductive_type :=
-- { to_tactic_format := λ a, pure $ to_fmt a }

meta def inductive_type.u_params (decl : inductive_type) :=
decl.u_names.map level.param

meta def inductive_type.type_ctor (decl : inductive_type) : expr :=
(@const tt decl.name decl.u_params).mk_app decl.params

meta def inductive_type.sig (decl : inductive_type) : tactic expr :=
local_ctor decl.name <$> pis decl.idx decl.type

meta def inductive_type.intros (decl : inductive_type) : tactic (list expr) :=
do let t := inductive_type.type_ctor decl,
   decl.ctors.mmap $ λ c, local_ctor c.name <$> pis c.args (t.mk_app c.result)

meta def type_cnstr.to_intro_rule (decl : inductive_type) (c : type_cnstr) : intro_rule :=
let t := inductive_type.type_ctor decl in
⟨ c.name, (t.mk_app c.result).pis c.args, c.infer ⟩

meta def inductive_type.mk_const (decl : inductive_type) (n : string) : expr :=
const (decl.name <.> n) $ decl.u_params

meta def inductive_type.mk_name (decl : inductive_type) (n : string) : name :=
decl.name <.> n

meta def inductive_type.is_constructor (decl : inductive_type) (n : name) : bool :=
n ∈ decl.ctors.map type_cnstr.name

meta def fresh_univ (xs : list name) (n : name := `u) : name :=
(((list.iota (xs.length + 1)).reverse.map n.append_after).diff xs).head
open expr (to_implicit_local_const)
meta def mk_cases_on (decl : inductive_type) : tactic unit :=
do let u := fresh_univ decl.u_names,
   let idx := decl.idx,
   let c := @const tt decl.name decl.u_params,
   n ← unify_app c ( decl.params ++ idx ) >>= mk_local_def `n,
   C ← pis (idx ++ [n]) (sort $ level.param u) >>= mk_local_def `C,
   cases ← decl.ctors.mmap $ λ c,
     do { cn ← get_unused_name "c",
          n ← unify_app (const c.name decl.u_params) $ decl.params ++ c.args,
          pis c.args (C.mk_app $ c.result ++ [n]) >>= mk_local_def cn },
   t ← pis ((decl.params ++ [C] ++ idx).map to_implicit_local_const ++ [n] ++ cases) (C.mk_app (idx ++ [n])),
   p ← mk_mapp (decl.name <.> "rec") $ (decl.params ++ [C] ++ cases ++ idx ++ [n]).map some,
   p ← lambdas (decl.params ++ [C] ++ idx ++ [n] ++ cases) p,
   d ← instantiate_mvars p,
   add_decl $ mk_definition (decl.name <.> "cases_on") (u :: decl.u_names) t d,
   updateex_env $ λ e, pure $ e.add_namespace decl.name,
   return ()

meta def inductive_type.mk_cases_on (decl : inductive_type) (C e : expr) (f : name → list expr → tactic expr) : tactic expr :=
do let cases_on_n := decl.mk_name "cases_on",
   cases_on ← mk_const cases_on_n,
   cs ← decl.ctors.mmap $ λ c,
     do { (args',_) ← pis c.args `(true) >>= mk_local_pis,
          f c.name args' >>= lambdas args' },
   unify_app cases_on (decl.params ++ [C] ++ decl.idx ++ [e] ++ cs)

meta def inductive_type.mk_cases_on' (decl : inductive_type) (C e' : expr) (f : name → list expr → tactic unit) : tactic (list expr) :=
do let cases_on_n := decl.mk_name "cases_on",
   cases_on ← mk_const cases_on_n,
   cs ← decl.ctors.mmap $ λ c,
     do { n ← unify_app (const c.name decl.u_params) $ decl.params ++ c.args,
          t ← pis (c.args) (C.mk_app $ c.result ++ [n]),
          mk_meta_var t  },
   gs ← get_goals,
   e ← unify_app cases_on (decl.params ++ [C] ++ decl.idx ++ [e'] ++ cs),
   mzip_with' (λ g (c : type_cnstr),
       do set_goals [g],
          intro_lst ( c.args.map expr.local_pp_name )
            >>= f c.name )
       cs decl.ctors,
   set_goals gs,
   apply e,
   (>>= list_meta_vars) <$> cs.mmap instantiate_mvars.

meta def mk_no_confusion_type (decl : inductive_type) : tactic unit :=
do let params := decl.params.map to_implicit_local_const,
   let t := (const decl.name $ decl.u_params).mk_app $ params ++ decl.idx,
   let u := fresh_univ decl.u_names,
   let cases_on_n := decl.mk_name "cases_on",
   cases_on ← mk_const cases_on_n,
   v1 ← mk_local_def `v1 t,
   v2 ← mk_local_def `v2 t,
   P  ← mk_local_def `P (expr.sort $ level.param u),
   C ← lambdas (decl.idx ++ [v1]) (sort $ level.param u),
   e ← decl.mk_cases_on C v1 $ λ c args,
     do { decl.mk_cases_on C v2 $ λ c' args',
          if c = c' then do
            hs ← mzip_with (λ x y,
              mk_app `eq [x,y] >>= mk_local_def `h)
              args args',
            h ← pis hs P,
            pure $ h.imp P
          else pure P },
   let vs := (params ++ decl.idx ++ [P,v1,v2]),
   e ← lambdas vs e,
   p ← pis vs (sort $ level.param u),
   infer_type e >>= unify p,
   e ← instantiate_mvars e,
   add_decl $ mk_definition (decl.mk_name "no_confusion_type") (u :: decl.u_names) p e

run_cmd mk_simp_attr `pseudo_eqn

meta def mk_no_confusion (decl : inductive_type) : tactic unit :=
do let params := decl.params.map to_implicit_local_const,
   let t := (const decl.name $ decl.u_params).mk_app $ params ++ decl.idx,
   let u := fresh_univ decl.u_names,
   v1 ← mk_local_def `v1 t,
   v2 ← mk_local_def `v2 t,
   P  ← mk_local_def `P (expr.sort $ level.param u),
   type ← mk_const (decl.mk_name "no_confusion_type"),
   Heq ← mk_app `eq [v1,v2] >>= mk_local_def `Heq,
   let vs := (params ++ decl.idx ++ [P,v1,v2]).map to_implicit_local_const,
   p ← unify_app type vs,
   let vs := vs ++ [Heq],
   (_,pr) ← solve_aux p $
     do { intros,
          dunfold_target [decl.mk_name "no_confusion_type"],
          tgt ← target,
          cases_on ← mk_const ``eq.rec,
          C ← pis [Heq] tgt >>= lambdas ([v2]),
          t ← infer_type v1,
          g ← mk_mvar,
          unify_app cases_on ([t,v1,C,g,v2,Heq,Heq]) >>= exact,
          set_goals [g],
          intro1,
          tgt ← target,
          C ← lambdas (decl.idx ++ [v1]) tgt,
          cases_on ← mk_const (decl.mk_name "cases_on"),
          decl.mk_cases_on' C v1 $ λ _ _,
            do { try $ `[simp only with pseudo_eqn],
                 h ← intro `h, () <$ apply h; reflexivity },
          done },
   p ← pis vs p,
   p ← instantiate_mvars p,
   pr ← instantiate_mvars pr,
   pr ← lambdas vs pr,
   add_decl $ mk_definition (decl.mk_name "no_confusion") (u :: decl.u_names) p pr,
   pure ()

meta def inductive_type.get_constructor (c_name : name) : inductive_type → option type_cnstr
| { ctors := ctors, .. } := ctors.find (λ c, c.name = c_name)

meta def type_cnstr.type (decl : inductive_type) : type_cnstr → tactic expr
| ⟨cn,vs,r,i⟩ :=
do let sig_c  : expr := const decl.name decl.u_params,
   ts ← vs.mmap infer_type,
   let params : list expr := match i with
                             | implicit := decl.params
                             | relaxed_implicit := decl.params.map to_implicit_local_const
                             | none := decl.params.map $ λ v, if v ∈ ts then to_implicit_local_const v
                                                                        else v
                             end,
   tactic.pis vs (sig_c.mk_app' [decl.params,r]) >>= pis params

meta def mk_inductive (parent : name) : inductive_type → tactic unit
| decl :=
trace_scope $
do opt ← get_options,
   updateex_env $ λ env, pure $ env.add_namespace decl.name,
   updateex_env $ λ e : environment,
     e.add_ginductive opt decl.u_names decl.params
     [((decl.name,decl.type.pis decl.idx),decl.ctors.map $ type_cnstr.to_intro_rule decl)] ff,
   when_tracing `generated_decl $ trace!"[generated for {parent}]\n  inductive {decl.name} : {decl.type.pis $ decl.params ++ decl.idx}",
   -- when_tracing `generated_decl.tests $ do
   -- { trace!"\n/- inductive declaration -/",
   --   trace!"#check (@{decl.name} : {decl.type.pis $ decl.params ++ decl.idx})",
   --   decl.ctors.mmap' $ λ c, trace!"#check (@{c.name} : {(c.to_intro_rule decl).type.pis decl.params})" },
   generated_attr.set decl.name parent tt,
   pure ()

open interactive

meta def implicit_infer_kind_of (us : list expr) : implicit_infer_kind :=
let b₀ := us.all $ λ v, v.local_binding_info = binder_info.default,
    b₁ := us.all $ λ v, v.local_binding_info ≠ binder_info.default in
if b₀ then if b₁ then implicit
                 else none
else if b₁ then relaxed_implicit
           else implicit

meta def inductive_type.of_name (decl : name) : tactic inductive_type :=
do d ← get_decl decl,
   (idx,t) ← mk_local_pis d.type,
   env ← get_env,
   let (params,idx) := idx.split_at $ env.inductive_num_params decl,
   cs ← (env.constructors_of decl).mmap $ λ c : name,
   do { let e := @const tt c d.univ_levels,
        t ← infer_type $ e.mk_app params,
        (vs,t) ← mk_local_pis t,
        (us,_) ← infer_type e >>= mk_local_pis,
        let infer := implicit_infer_kind_of $ us.take params.length,
        pure (t.get_app_fn.const_name,{ type_cnstr .
               name := c,
               args := vs,
               result := t.get_app_args.drop $ env.inductive_num_params decl,
               infer  := infer }) },
   pure { pre := decl.get_prefix,
          name := decl,
          u_names := d.univ_params,
          params := params,
          idx := idx, type := t,
          ctors := cs.map prod.snd }

-- meta def with_namespace (decl : inductive_decl) : tactic inductive_type :=
-- do
--    env ← get_env,

meta def inductive_type.of_decl (decl : inductive_decl) : tactic inductive_type :=
do [d] ← pure decl.decls | fail "mutually (co)inductive types are not supported",
   (idx,t) ← infer_type  d.sig >>= mk_local_pis,
   -- env ← get_env,
   cs ← d.intros.mmap $ λ c : expr,
   do { t ← infer_type c,
        (vs,t) ← mk_local_pis t,
        pure (t.get_app_fn.const_name,{ type_cnstr .
               name := c.local_pp_name,
               args := vs,
               result := t.get_app_args.drop $ decl.params.length,
               infer  := relaxed_implicit }) },
   let n := (prod.fst <$> cs.nth 0).get_or_else d.sig.local_pp_name,
   pure { pre := n.get_prefix,
          name := n,
          u_names := decl.u_names,
          params := decl.params,
          idx := idx, type := t,
          ctors := cs.map prod.snd }

end tactic
