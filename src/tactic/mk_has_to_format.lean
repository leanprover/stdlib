/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import tactic.core

namespace format

open tactic expr

meta def mk_to_string (t : expr) (fn of_string : name) (ls : list expr) (out : expr) (trusted : bool) : tactic expr :=
do let n := t.get_app_fn.const_name,
   d ← get_decl n,
   let r : reducibility_hints := reducibility_hints.regular 1 tt,
   env ← get_env,
   ls ← local_context,
   sig ← to_expr ``(%%t → %%out),
   of_string ← mk_const of_string,
   (_,df) ← solve_aux sig $ do
     { match env.structure_fields n with
       | (some fs) :=
       do a ← intro1,
          [(_,xs,_)] ← cases_core a,
          let l := xs.length,
          fn' ← mk_const fn,
          out ← list.mzip_with₄ (λ x (fn : name) (y : expr) z,
            do let fn := (fn.update_prefix name.anonymous).to_string,
               to_expr ``(%%of_string (%%(reflect x) ++ %%(reflect fn) ++ " := ") ++ %%fn' %%y ++ %%of_string %%(reflect z)))
            ("{ " :: list.repeat "  " (l-1)) fs xs (list.repeat ",\n" (l-1) ++ [" }"]),
          to_expr (out.foldr (λ e acc, ``(%%e ++ %%acc)) ``(%%of_string %%(reflect "" : expr))) >>= exact,
          pure ()
       | none :=
       do g ← main_goal,
          a ← intro1,
          xs ← cases_core a,
          fn ← mk_const fn,
          out ← xs.mmap $ λ ⟨c,xs,_⟩,
            do { out ← xs.mmap $ λ x, to_expr ``(%%of_string " (" ++ %%fn %%x ++ %%of_string ")"),
                 let c := (c.update_prefix name.anonymous).to_string,
                 to_expr (out.foldr (λ e acc, ``(%%e ++ %%acc)) ``(%%of_string %%(reflect c : expr))) >>= exact },
          pure () end },
   df ← instantiate_mvars df >>= lambdas ls,
   t ← infer_type df,
   add_decl' $ declaration.defn (n ++ fn) d.univ_params t df r (trusted ∧ d.is_trusted)

meta def mk_has_to_format : tactic unit :=
do `(has_to_format %%t) ← target,
   ls ← local_context,
   e ← mk_to_string t `to_fmt `format.of_string ls `(format) ff,
   refine ``( { to_format := %%(e.mk_app ls) } ),
   pure ()

meta def mk_has_repr : tactic unit :=
do `(has_repr %%t) ← target,
   ls ← local_context,
   e ← mk_to_string t `repr `id ls `(string) tt,
   refine ``( { repr := %%(e.mk_app ls) } ),
   pure ()

@[derive_handler]
meta def has_repr_derive_handler : derive_handler :=
instance_derive_handler ``has_repr mk_has_repr

@[derive_handler]
meta def has_to_format_derive_handler : derive_handler :=
instance_derive_handler ``has_to_format mk_has_to_format

end format
