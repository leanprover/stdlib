/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import algebra.ordered_ring

namespace tactic.interactive
open tactic list
open lean lean.parser interactive
open interactive.types

@[derive inhabited]
structure mono_cfg :=
  (unify := ff)

@[derive [decidable_eq, has_reflect, inhabited]]
inductive mono_selection : Type
| left : mono_selection
| right : mono_selection
| both : mono_selection

declare_trace mono.relation

section compare

parameter opt : mono_cfg

meta def compare (e₀ e₁ : expr) : tactic unit := do
if opt.unify then do
guard (¬ e₀.is_mvar ∧ ¬ e₁.is_mvar),
unify e₀ e₁
else is_def_eq e₀ e₁

meta def find_one_difference
: list expr → list expr → tactic (list expr × expr × expr × list expr)
 | (x :: xs) (y :: ys) :=
   do c ← try_core (compare x y),
      if c.is_some
      then prod.map (cons x) id <$> find_one_difference xs ys
      else do
        guard (xs.length = ys.length),
        mzip_with' compare xs ys,
        return ([],x,y,xs)
 | xs ys := fail format!"find_one_difference: {xs}, {ys}"

end compare

def last_two {α : Type*} (l : list α) : option (α × α) :=
match l.reverse with
| (x₁ :: x₀ :: _) := some (x₀, x₁)
| _ := none
end

meta def match_imp : expr → tactic (expr × expr)
 | `(%%e₀ → %%e₁) :=
   do guard (¬ e₁.has_var),
      return (e₀,e₁)
 | _ := failed

open expr

meta def same_operator : expr → expr → bool
| (app e₀ _) (app e₁ _) :=
let fn₀ := e₀.get_app_fn,
    fn₁ := e₁.get_app_fn in
    fn₀.is_constant ∧ fn₀.const_name = fn₁.const_name
| (pi _ _ _ _) (pi _ _ _ _) := tt
| _ _ := ff

meta def get_operator (e : expr) : option name :=
guard (¬ e.is_pi) >> pure e.get_app_fn.const_name

meta def monotonicity.check_rel (l r : expr) : tactic (option name) :=
do guard (same_operator l r) <|>
     do { fail format!"{l} and {r} should be the f x and f y for some f" },
   if l.is_pi then pure none
              else pure r.get_app_fn.const_name

@[reducible]
def mono_key := (with_bot name × with_bot name)

open nat

meta def mono_head_candidates : ℕ → list expr → expr → tactic mono_key
| 0 _ h := fail!"Cannot find relation in {h}"
| (succ n) xs h :=
  do { (rel,l,r) ← if h.is_arrow
           then pure (none,h.binding_domain,h.binding_body)
           else guard h.get_app_fn.is_constant >>
                prod.mk (some h.get_app_fn.const_name) <$> last_two h.get_app_args,
       prod.mk <$> monotonicity.check_rel l r <*> pure rel } <|>
         match xs with
         | [] := fail format!"oh? {h}"
         | (x::xs) := mono_head_candidates n xs (h.pis [x])
         end

meta def monotonicity.check (lm_n : name) : tactic mono_key :=
do lm ← mk_const lm_n,
   lm_t ← infer_type lm >>= instantiate_mvars,
   when_tracing `mono.relation trace!"[mono] Looking for relation in {lm_t}",
   s ← simp_lemmas.mk.add_simp ``monotone,
   lm_t ← s.dsimplify [] lm_t { fail_if_unchanged := ff },
   when_tracing `mono.relation trace!"[mono] Looking for relation in {lm_t} (after unfolding)",
   (xs,h) ← open_pis lm_t,
   mono_head_candidates 3 xs.reverse h

meta instance : has_to_format mono_selection :=
⟨ λ x, match x with
| mono_selection.left := "left"
| mono_selection.right := "right"
| mono_selection.both := "both"
end ⟩

meta def side : lean.parser mono_selection :=
with_desc "expecting 'left', 'right' or 'both' (default)" $
do some n ← optional ident | pure mono_selection.both,
   if n = `left then pure $ mono_selection.left
   else if n = `right then pure $ mono_selection.right
   else if n = `both then pure $ mono_selection.both
   else fail format!"invalid argument: {n}, expecting 'left', 'right' or 'both' (default)"


open function

@[user_attribute]
meta def monotonicity.attr : user_attribute
  (native.rb_lmap mono_key (name))
  (option mono_key × mono_selection) :=
{ name  := `mono
, descr := "monotonicity of function `f` wrt relations `R₀` and `R₁`: R₀ x y → R₁ (f x) (f y)"
, cache_cfg :=
  { dependencies := [],
    mk_cache := λ ls,
    do ps ← ls.mmap monotonicity.attr.get_param,
       let ps := ps.filter_map prod.fst,
       pure $ (ps.zip ls).foldl
         (flip $ uncurry (λ k n m, m.insert k n))
         (native.rb_lmap.mk mono_key _)  }
, after_set := some $ λ n prio p,
  do { (none,v) ← monotonicity.attr.get_param n | pure (),
       k ← monotonicity.check n,
       monotonicity.attr.set n (some k,v) p }
, parser := prod.mk none <$> side }

meta def filter_instances (e : mono_selection) (ns : list name) : tactic (list name) :=
ns.mfilter $ λ n,
do d ← user_attribute.get_param_untyped monotonicity.attr n,
   (_,d) ← to_expr ``(id %%d) >>= eval_expr (option mono_key × mono_selection),
   return (e = d : bool)

meta def get_monotonicity_lemmas (k : expr) (e : mono_selection) : tactic (list name) :=
do ns  ← monotonicity.attr.get_cache,
   k' ← if k.is_pi
        then pure (get_operator k.binding_domain,none)
        else do { (x₀,x₁) ← last_two k.get_app_args,
                  pure (get_operator x₀,some k.get_app_fn.const_name) },
   let ns := ns.find_def [] k',
   ns' ← filter_instances e ns,
   if e ≠ mono_selection.both then (++) ns' <$> filter_instances mono_selection.both ns
               else pure ns'

end tactic.interactive

attribute [mono] add_le_add mul_le_mul neg_le_neg
         mul_lt_mul_of_pos_left mul_lt_mul_of_pos_right
         imp_imp_imp le_implies_le_of_le_of_le
         sub_le_sub abs_le_abs sup_le_sup
         inf_le_inf
attribute [mono left] add_lt_add_of_le_of_lt mul_lt_mul'
attribute [mono right] add_lt_add_of_lt_of_le mul_lt_mul
