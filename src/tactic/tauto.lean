/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.hint
import tactic.ext

namespace tactic

open expr
open tactic.interactive ( casesm constructor_matching )

/--
  find all assumptions of the shape `¬ (p ∧ q)` or `¬ (p ∨ q)` and
  replace them using de Morgan's law.
-/
meta def distrib_not : tactic unit :=
do hs ← local_context,
   hs.for_each $ λ h,
    all_goals' $
    iterate_at_most' 3 $
      do h ← get_local h.local_pp_name,
         e ← infer_type h,
         match e with
         | `(¬ _ = _) := replace h.local_pp_name ``(mt iff.to_eq %%h)
         | `(_ ≠ _)   := replace h.local_pp_name ``(mt iff.to_eq %%h)
         | `(_ = _)   := replace h.local_pp_name ``(eq.to_iff %%h)
         | `(¬ (_ ∧ _))  := replace h.local_pp_name ``(decidable.not_and_distrib'.mp %%h) <|>
                            replace h.local_pp_name ``(decidable.not_and_distrib.mp %%h)
         | `(¬ (_ ∨ _))  := replace h.local_pp_name ``(not_or_distrib.mp %%h)
         | `(¬ ¬ _)      := replace h.local_pp_name ``(decidable.of_not_not %%h)
         | `(¬ (_ → (_ : Prop))) := replace h.local_pp_name ``(decidable.not_imp.mp %%h)
         | `(¬ (_ ↔ _)) := replace h.local_pp_name ``(decidable.not_iff.mp %%h)
         | `(_ ↔ _) := replace h.local_pp_name ``(decidable.iff_iff_and_or_not_and_not.mp %%h) <|>
                       replace h.local_pp_name ``(decidable.iff_iff_and_or_not_and_not.mp (%%h).symm) <|>
                       () <$ tactic.cases h
         | `(_ → _)     := replace h.local_pp_name ``(decidable.not_or_of_imp %%h)
         | _ := failed
         end

/-!
  The following definitions maintain a path compression datastructure, i.e. a forest such that:
    - every node is the type of a hypothesis
    - there is a edge between two nodes only if they are provably equivalent
    - every edge is labelled with a proof of equivalence for its vertices
    - edges are added when normalizing propositions.
-/

meta def tauto_state := ref $ expr_map (option (expr × expr))

meta def modify_ref {α : Type} (r : ref α) (f : α → α) :=
read_ref r >>= write_ref r ∘ f

meta def add_refl (r : tauto_state) (e : expr) : tactic (expr × expr) :=
do m ← read_ref r,
   p ← mk_mapp `rfl [none,e],
   write_ref r $ m.insert e none,
   return (e,p)

/--
  If there exists a symmetry lemma that can be applied to the hypothesis `e`,
  store it.
-/
meta def add_symm_proof (r : tauto_state) (e : expr) : tactic (expr × expr) :=
do env ← get_env,
   let rel := e.get_app_fn.const_name,
   some symm ← pure $ environment.symm_for env rel
     | add_refl r e,
   (do e' ← mk_meta_var `(Prop),
       iff_t ← to_expr ``(%%e = %%e'),
       (_,p) ← solve_aux iff_t
         (applyc `iff.to_eq ; () <$ split ; applyc symm),
       e' ← instantiate_mvars e',
       m ← read_ref r,
       write_ref r $ (m.insert e (e',p)).insert e' none,
       return (e',p) )
   <|> add_refl r e

meta def add_edge (r : tauto_state) (x y p : expr) : tactic unit :=
modify_ref r $ λ m, m.insert x (y,p)

/--
  Retrieve the root of the hypothesis `e` from the proof forest.
  If `e` has not been internalized, add it to the proof forest.
-/
meta def root (r : tauto_state) : expr → tactic (expr × expr) | e :=
do m ← read_ref r,
   let record_e : tactic (expr × expr) :=
       match e with
       | v@(expr.mvar _ _ _) :=
         (do (e,p) ← get_assignment v >>= root,
             add_edge r v e p,
             return (e,p)) <|>
         add_refl r e
       | _ := add_refl r e
       end,
   some e' ← pure $ m.find e | record_e,
   match e' with
   | (some (e',p')) :=
     do (e'',p'') ← root e',
        p'' ← mk_app `eq.trans [p',p''],
        add_edge r e e'' p'',
        pure (e'',p'')
   | none := prod.mk e <$> mk_mapp `rfl [none,some e]
   end

/--
  Given hypotheses `a` and `b`, build a proof that `a` is equivalent to `b`,
  applying congruence and recursing into arguments if `a` and `b`
  are applications of function symbols.
-/
meta def symm_eq (r : tauto_state) : expr → expr → tactic expr | a b :=
do m ← read_ref r,
   (a',pa) ← root r a,
   (b',pb) ← root r b,
   (unify a' b' >> add_refl r a' *> mk_mapp `rfl [none,a]) <|>
    do p ← match (a', b') with
           | (`(¬ %%a₀), `(¬ %%b₀)) :=
             do p  ← symm_eq a₀ b₀,
                p' ← mk_app `congr_arg [`(not),p],
                add_edge r a' b' p',
                return p'
           | (`(%%a₀ ∧ %%a₁), `(%%b₀ ∧ %%b₁)) :=
             do p₀ ← symm_eq a₀ b₀,
                p₁ ← symm_eq a₁ b₁,
                p' ← to_expr ``(congr (congr_arg and %%p₀) %%p₁),
                add_edge r a' b' p',
                return p'
           | (`(%%a₀ ∨ %%a₁), `(%%b₀ ∨ %%b₁)) :=
             do p₀ ← symm_eq a₀ b₀,
                p₁ ← symm_eq a₁ b₁,
                p' ← to_expr ``(congr (congr_arg or %%p₀) %%p₁),
                add_edge r a' b' p',
                return p'
           | (`(%%a₀ ↔ %%a₁), `(%%b₀ ↔ %%b₁)) :=
             (do p₀ ← symm_eq a₀ b₀,
                 p₁ ← symm_eq a₁ b₁,
                 p' ← to_expr ``(congr (congr_arg iff %%p₀) %%p₁),
                 add_edge r a' b' p',
                 return p') <|>
             do p₀ ← symm_eq a₀ b₁,
                p₁ ← symm_eq a₁ b₀,
                p' ← to_expr ``(eq.trans (congr (congr_arg iff %%p₀) %%p₁)
                                         (iff.to_eq iff.comm ) ),
                add_edge r a' b' p',
                return p'
           | (`(%%a₀ → %%a₁), `(%%b₀ → %%b₁)) :=
             if ¬ a₁.has_var ∧ ¬ b₁.has_var then
             do p₀ ← symm_eq a₀ b₀,
                p₁ ← symm_eq a₁ b₁,
                p' ← mk_app `congr_arg [`(implies),p₀,p₁],
                add_edge r a' b' p',
                return p'
             else unify a' b' >> add_refl r a' *> mk_mapp `rfl [none,a]
           | (_, _) :=
             (do guard $ a'.get_app_fn.is_constant ∧
                         a'.get_app_fn.const_name = b'.get_app_fn.const_name,
                 (a'',pa') ← add_symm_proof r a',
                 guard $ a'' =ₐ b',
                 pure pa' )
           end,
    p' ← mk_eq_trans pa p,
    add_edge r a' b' p',
    mk_eq_symm pb >>= mk_eq_trans p'

meta def find_eq_type (r : tauto_state) : expr → list expr → tactic (expr × expr)
| e []         := failed
| e (H :: Hs) :=
  do t  ← infer_type H,
     (prod.mk H <$> symm_eq r e t) <|> find_eq_type e Hs

private meta def contra_p_not_p (r : tauto_state) : list expr → list expr → tactic unit
| []         Hs := failed
| (H1 :: Rs) Hs :=
  do t ← (extract_opt_auto_param <$> infer_type H1) >>= whnf,
     (do a   ← match_not t,
         (H2,p)  ← find_eq_type r a Hs,
         H2 ← to_expr ``( (%%p).mpr %%H2 ),
         tgt ← target,
         pr  ← mk_app `absurd [tgt, H2, H1],
         tactic.exact pr)
     <|> contra_p_not_p Rs Hs

meta def contradiction_with (r : tauto_state) : tactic unit :=
contradiction <|>
do tactic.try intro1,
   ctx ← local_context,
   contra_p_not_p r ctx ctx

meta def contradiction_symm :=
using_new_ref (native.rb_map.mk _ _) contradiction_with

meta def assumption_with (r : tauto_state) : tactic unit :=
do { ctx ← local_context,
     t   ← target,
     (H,p) ← find_eq_type r t ctx,
     mk_eq_mpr p H >>= tactic.exact }
<|> fail "assumption tactic failed"

meta def assumption_symm :=
using_new_ref (native.rb_map.mk _ _) assumption_with

/--
  Configuration options for `tauto`.
  If `classical` is `tt`, runs `classical` before the rest of `tauto`.
  `closer` is run on any remaining subgoals left by `tauto_core; basic_tauto_tacs`.
-/
meta structure tauto_cfg :=
(classical : bool     := ff)
(closer : tactic unit := pure ())

meta def tautology (cfg : tauto_cfg := {}) : tactic unit := focus1 $
  let basic_tauto_tacs : list (tactic unit) :=
        [reflexivity, solve_by_elim,
          constructor_matching none [``(_ ∧ _),``(_ ↔ _),``(Exists _),``(true)]],

      tauto_core (r : tauto_state) : tactic unit :=
        do try (contradiction_with r);
           try (assumption_with r);
           repeat (do
             gs ← get_goals,
             repeat (() <$ tactic.intro1);
             distrib_not;
             casesm (some ()) [``(_ ∧ _),``(_ ∨ _),``(Exists _),``(false)];
             try (contradiction_with r);
             try (target >>= match_or >> refine ``( or_iff_not_imp_left.mpr _));
             try (target >>= match_or >> refine ``( or_iff_not_imp_right.mpr _));
             repeat (() <$ tactic.intro1);
             constructor_matching (some ()) [``(_ ∧ _),``(_ ↔ _),``(true)];
             try (assumption_with r),
             gs' ← get_goals,
             guard (gs ≠ gs') ) in

    do when cfg.classical classical,
       using_new_ref (expr_map.mk _) tauto_core;
       repeat (first basic_tauto_tacs); cfg.closer, done

namespace interactive
local postfix `?`:9001 := optional
setup_tactic_parser

/--
`tautology` breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
using `reflexivity` or `solve_by_elim`.
This is a finishing tactic: it either closes the goal or raises an error.
The variant `tautology!` uses the law of excluded middle.

`tautology {closer := tac}` will use `tac` on any subgoals created by `tautology`
that it is unable to solve before failing.
-/
meta def tautology (c : parse $ (tk "!")?) (cfg : tactic.tauto_cfg := {}) :=
tactic.tautology $ { classical := c.is_some, ..cfg }

-- Now define a shorter name for the tactic `tautology`.

/--
`tauto` breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
using `reflexivity` or `solve_by_elim`.
This is a finishing tactic: it either closes the goal or raises an error.
The variant `tauto!` uses the law of excluded middle.

`tauto {closer := tac}` will use `tac` on any subgoals created by `tauto`
that it is unable to solve before failing.
-/
meta def tauto (c : parse $ (tk "!")?) (cfg : tactic.tauto_cfg := {}) : tactic unit :=
tautology c cfg

add_hint_tactic "tauto"

/--
This tactic (with shorthand `tauto`) breaks down assumptions of the form
`_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
using `reflexivity` or `solve_by_elim`. This is a finishing tactic: it
either closes the goal or raises an error.

The variants `tautology!` and `tauto!` use the law of excluded middle.

For instance, one can write:
```lean
example (p q r : Prop) [decidable p] [decidable r] : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto
```
and the decidability assumptions can be dropped if `tauto!` is used
instead of `tauto`.

`tauto {closer := tac}` will use `tac` on any subgoals created by `tauto`
that it is unable to solve before failing.
-/
add_tactic_doc
{ name       := "tautology",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.tautology, `tactic.interactive.tauto],
  tags       := ["logic", "decision procedure"] }


/-- Prove tautological equality of two sets, using intuitionistic logic.
    For best results, import data.set.default or data.finset.default
    as appropriate.
 -/
meta def set_tauto : tactic unit :=
 `[{{ refl } <|> { ext1, try { simp [forall_and_distrib] }, try { tauto! }}}]


/--
This tactic solves set equality by using extensionality, simplification,
and classical logic.

This is a finishing tactic: it either closes the goal or raises an error.
-/
add_tactic_doc
{ name       := "set_tauto",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.set_tauto],
  tags       := ["logic", "decision procedure", "sets"] }

end interactive
end tactic

