/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek, Robert Y. Lewis, Floris van Doorn
-/
import data.string.defs
import data.option.defs
import tactic.derive_inhabited
/-!
# Additional operations on expr and related types

This file defines basic operations on the types expr, name, declaration, level, environment.

This file is mostly for non-tactics. Tactics should generally be placed in `tactic.core`.

## Tags

expr, name, declaration, level, environment, meta, metaprogramming, tactic
-/

attribute [derive has_reflect, derive decidable_eq] binder_info congr_arg_kind

@[priority 100] meta instance has_reflect.has_to_pexpr {α} [has_reflect α] : has_to_pexpr α :=
⟨λ b, pexpr.of_expr (reflect b)⟩

namespace binder_info

/-! ### Declarations about `binder_info` -/

instance : inhabited binder_info := ⟨ binder_info.default ⟩

/-- The brackets corresponding to a given binder_info. -/
def brackets : binder_info → string × string
| binder_info.implicit        := ("{", "}")
| binder_info.strict_implicit := ("{{", "}}")
| binder_info.inst_implicit   := ("[", "]")
| _                           := ("(", ")")

end binder_info

namespace name

/-! ### Declarations about `name` -/

/-- Find the largest prefix `n` of a `name` such that `f n ≠ none`, then replace this prefix
with the value of `f n`. -/
def map_prefix (f : name → option name) : name → name
| anonymous := anonymous
| (mk_string s n') := (f (mk_string s n')).get_or_else (mk_string s $ map_prefix n')
| (mk_numeral d n') := (f (mk_numeral d n')).get_or_else (mk_numeral d $ map_prefix n')

/-- If `nm` is a simple name (having only one string component) starting with `_`, then
`deinternalize_field nm` removes the underscore. Otherwise, it does nothing. -/
meta def deinternalize_field : name → name
| (mk_string s name.anonymous) :=
  let i := s.mk_iterator in
  if i.curr = '_' then i.next.next_to_string else s
| n := n

/-- `get_nth_prefix nm n` removes the last `n` components from `nm` -/
meta def get_nth_prefix : name → ℕ → name
| nm 0 := nm
| nm (n + 1) := get_nth_prefix nm.get_prefix n

/-- Auxiliary definition for `pop_nth_prefix` -/
private meta def pop_nth_prefix_aux : name → ℕ → name × ℕ
| anonymous n := (anonymous, 1)
| nm n := let (pfx, height) := pop_nth_prefix_aux nm.get_prefix n in
          if height ≤ n then (anonymous, height + 1)
          else (nm.update_prefix pfx, height + 1)

/-- Pops the top `n` prefixes from the given name. -/
meta def pop_nth_prefix (nm : name) (n : ℕ) : name :=
prod.fst $ pop_nth_prefix_aux nm n

/-- Pop the prefix of a name -/
meta def pop_prefix (n : name) : name :=
pop_nth_prefix n 1

/-- Auxiliary definition for `from_components` -/
private def from_components_aux : name → list string → name
| n [] := n
| n (s :: rest) := from_components_aux (name.mk_string s n) rest

/-- Build a name from components. For example `from_components ["foo","bar"]` becomes
  ``` `foo.bar``` -/
def from_components : list string → name :=
from_components_aux name.anonymous

/-- `name`s can contain numeral pieces, which are not legal names
  when typed/passed directly to the parser. We turn an arbitrary
  name into a legal identifier name by turning the numbers to strings. -/
meta def sanitize_name : name → name
| name.anonymous := name.anonymous
| (name.mk_string s p) := name.mk_string s $ sanitize_name p
| (name.mk_numeral s p) := name.mk_string sformat!"n{s}" $ sanitize_name p

/-- Append a string to the last component of a name. -/
def append_suffix : name → string → name
| (mk_string s n) s' := mk_string (s ++ s') n
| n _ := n

/-- Update the last component of a name. -/
def update_last (f : string → string) : name → name
| (mk_string s n) := mk_string (f s) n
| n := n

/-- `append_to_last nm s is_prefix` adds `s` to the last component of `nm`,
  either as prefix or as suffix (specified by `is_prefix`), separated by `_`.
  Used by `simps_add_projections`. -/
def append_to_last (nm : name) (s : string) (is_prefix : bool) : name :=
nm.update_last $ λ s', if is_prefix then s ++ "_" ++ s' else s' ++ "_" ++ s

/-- The first component of a name, turning a number to a string -/
meta def head : name → string
| (mk_string s anonymous) := s
| (mk_string s p)         := head p
| (mk_numeral n p)        := head p
| anonymous               := "[anonymous]"

/-- Tests whether the first component of a name is `"_private"` -/
meta def is_private (n : name) : bool :=
n.head = "_private"

/-- Get the last component of a name, and convert it to a string. -/
meta def last : name → string
| (mk_string s _)  := s
| (mk_numeral n _) := repr n
| anonymous        := "[anonymous]"

/-- Returns the number of characters used to print all the string components of a name,
  including periods between name segments. Ignores numerical parts of a name. -/
meta def length : name → ℕ
| (mk_string s anonymous) := s.length
| (mk_string s p)         := s.length + 1 + p.length
| (mk_numeral n p)        := p.length
| anonymous               := "[anonymous]".length

/-- Checks whether `nm` has a prefix (including itself) such that P is true -/
def has_prefix (P : name → bool) : name → bool
| anonymous := ff
| (mk_string s nm)  := P (mk_string s nm) ∨ has_prefix nm
| (mk_numeral s nm) := P (mk_numeral s nm) ∨ has_prefix nm

/-- Appends `'` to the end of a name. -/
meta def add_prime : name → name
| (name.mk_string s p) := name.mk_string (s ++ "'") p
| n := (name.mk_string "x'" n)

/-- `last_string n` returns the rightmost component of `n`, ignoring numeral components.
For example, ``last_string `a.b.c.33`` will return `` `c ``. -/
def last_string : name → string
| anonymous        := "[anonymous]"
| (mk_string s _)  := s
| (mk_numeral _ n) := last_string n

/--
Constructs a (non-simple) name from a string.

Example: ``name.from_string "foo.bar" = `foo.bar``
-/
meta def from_string (s : string) : name :=
from_components $ s.split (= '.')


/--
In surface Lean, we can write anonymous Π binders (i.e. binders where the
argument is not named) using the function arrow notation:

```lean
inductive test : Type
| intro : unit → test
```

After elaboration, however, every binder must have a name, so Lean generates
one. In the example, the binder in the type of `intro` is anonymous, so Lean
gives it the name `ᾰ`:

```lean
test.intro : ∀ (ᾰ : unit), test
```

When there are multiple anonymous binders, they are named `ᾰ_1`, `ᾰ_2` etc.

Thus, when we want to know whether the user named a binder, we can check whether
the name follows this scheme. Note, however, that this is not reliable. When the
user writes (for whatever reason)

```lean
inductive test : Type
| intro : ∀ (ᾰ : unit), test
```

we cannot tell that the binder was, in fact, named.

The function `name.is_likely_generated_binder_name` checks if
a name is of the form `ᾰ`, `ᾰ_1`, etc.
-/
library_note "likely generated binder names"

/--
Check whether a simple name was likely generated by Lean to name an anonymous
binder. Such names are either `ᾰ` or `ᾰ_n` for some natural `n`. See
note [likely generated binder names].
-/
meta def is_likely_generated_binder_simple_name : string → bool
| "ᾰ" := tt
| n :=
  match n.get_rest "ᾰ_" with
  | none := ff
  | some suffix := suffix.is_nat
  end

/--
Check whether a name was likely generated by Lean to name an anonymous binder.
Such names are either `ᾰ` or `ᾰ_n` for some natural `n`. See
note [likely generated binder names].
-/
meta def is_likely_generated_binder_name (n : name) : bool :=
match n with
| mk_string s anonymous := is_likely_generated_binder_simple_name s
| _ := ff
end

end name

namespace level

/-! ### Declarations about `level` -/

/-- Tests whether a universe level is non-zero for all assignments of its variables -/
meta def nonzero : level → bool
| (succ _) := tt
| (max l₁ l₂) := l₁.nonzero || l₂.nonzero
| (imax _ l₂) := l₂.nonzero
| _ := ff

/--
`l.fold_mvar f` folds a function `f : name → α → α`
over each `n : name` appearing in a `level.mvar n` in `l`.
-/
meta def fold_mvar {α} : level → (name → α → α) → α → α
| zero f := id
| (succ a) f := fold_mvar a f
| (param a) f := id
| (mvar a) f := f a
| (max a b) f := fold_mvar a f ∘ fold_mvar b f
| (imax a b) f := fold_mvar a f ∘ fold_mvar b f

end level

/-! ### Declarations about `binder` -/

/-- The type of binders containing a name, the binding info and the binding type -/
@[derive decidable_eq, derive inhabited]
meta structure binder :=
  (name : name)
  (info : binder_info)
  (type : expr)

namespace binder
/-- Turn a binder into a string. Uses expr.to_string for the type. -/
protected meta def to_string (b : binder) : string :=
let (l, r) := b.info.brackets in
l ++ b.name.to_string ++ " : " ++ b.type.to_string ++ r

open tactic
meta instance : has_to_string binder := ⟨ binder.to_string ⟩
meta instance : has_to_format binder := ⟨ λ b, b.to_string ⟩
meta instance : has_to_tactic_format binder :=
⟨ λ b, let (l, r) := b.info.brackets in
  (λ e, l ++ b.name.to_string ++ " : " ++ e ++ r) <$> pp b.type ⟩

end binder

/-!
### Converting between expressions and numerals

There are a number of ways to convert between expressions and numerals, depending on the input and
output types and whether you want to infer the necessary type classes.

See also the tactics `expr.of_nat`, `expr.of_int`, `expr.of_rat`.
-/


/--
`nat.mk_numeral n` embeds `n` as a numeral expression inside a type with 0, 1, and +.
`type`: an expression representing the target type. This must live in Type 0.
`has_zero`, `has_one`, `has_add`: expressions of the type `has_zero %%type`, etc.
 -/
meta def nat.mk_numeral (type has_zero has_one has_add : expr) : ℕ → expr :=
let z : expr := `(@has_zero.zero.{0} %%type %%has_zero),
    o : expr := `(@has_one.one.{0} %%type %%has_one) in
nat.binary_rec z
  (λ b n e, if n = 0 then o else
    if b then `(@bit1.{0} %%type %%has_one %%has_add %%e)
    else `(@bit0.{0} %%type %%has_add %%e))

/--
`int.mk_numeral z` embeds `z` as a numeral expression inside a type with 0, 1, +, and -.
`type`: an expression representing the target type. This must live in Type 0.
`has_zero`, `has_one`, `has_add`, `has_neg`: expressions of the type `has_zero %%type`, etc.
 -/
meta def int.mk_numeral (type has_zero has_one has_add has_neg : expr) : ℤ → expr
| (int.of_nat n) := n.mk_numeral type has_zero has_one has_add
| -[1+n] := let ne := (n+1).mk_numeral type has_zero has_one has_add in
            `(@has_neg.neg.{0} %%type %%has_neg %%ne)

/--
`nat.to_pexpr n` creates a `pexpr` that will evaluate to `n`.
The `pexpr` does not hold any typing information:
`to_expr ``((%%(nat.to_pexpr 5) : ℤ))` will create a native integer numeral `(5 : ℤ)`.
-/
meta def nat.to_pexpr : ℕ → pexpr
| 0 := ``(0)
| 1 := ``(1)
| n := if n % 2 = 0 then ``(bit0 %%(nat.to_pexpr (n/2))) else ``(bit1 %%(nat.to_pexpr (n/2)))
namespace expr

/--
Turns an expression into a natural number, assuming it is only built up from
`has_one.one`, `bit0`, `bit1`, `has_zero.zero`, `nat.zero`, and `nat.succ`.
-/
protected meta def to_nat : expr → option ℕ
| `(has_zero.zero) := some 0
| `(has_one.one) := some 1
| `(bit0 %%e) := bit0 <$> e.to_nat
| `(bit1 %%e) := bit1 <$> e.to_nat
| `(nat.succ %%e) := (+1) <$> e.to_nat
| `(nat.zero) := some 0
| _ := none

/--
Turns an expression into a integer, assuming it is only built up from
`has_one.one`, `bit0`, `bit1`, `has_zero.zero` and a optionally a single `has_neg.neg` as head.
-/
protected meta def to_int : expr → option ℤ
| `(has_neg.neg %%e) := do n ← e.to_nat, some (-n)
| e                  := coe <$> e.to_nat

/--
Turns an expression into a list, assuming it is only built up from `list.nil` and `list.cons`.
-/
protected meta def to_list {α} (f : expr → option α) : expr → option (list α)
| `(list.nil)          := some []
| `(list.cons %%x %%l) := list.cons <$> f x <*> l.to_list
| _                    := none

/--
`is_num_eq n1 n2` returns true if `n1` and `n2` are both numerals with the same numeral structure,
ignoring differences in type and type class arguments.
-/
meta def is_num_eq : expr → expr → bool
| `(@has_zero.zero _ _) `(@has_zero.zero _ _) := tt
| `(@has_one.one _ _) `(@has_one.one _ _) := tt
| `(bit0 %%a) `(bit0 %%b) := a.is_num_eq b
| `(bit1 %%a) `(bit1 %%b) := a.is_num_eq b
| `(-%%a) `(-%%b) := a.is_num_eq b
| `(%%a/%%a') `(%%b/%%b') :=  a.is_num_eq b
| _ _ := ff

end expr

/-! ### Declarations about `expr` -/

namespace expr
open tactic

/-- List of names removed by `clean`. All these names must resolve to functions defeq `id`. -/
meta def clean_ids : list name :=
[``id, ``id_rhs, ``id_delta, ``hidden]

/-- Clean an expression by removing `id`s listed in `clean_ids`. -/
meta def clean (e : expr) : expr :=
e.replace (λ e n,
     match e with
     | (app (app (const n _) _) e') :=
       if n ∈ clean_ids then some e' else none
     | (app (lam _ _ _ (var 0)) e') := some e'
     | _ := none
     end)

/-- `replace_with e s s'` replaces ocurrences of `s` with `s'` in `e`. -/
meta def replace_with (e : expr) (s : expr) (s' : expr) : expr :=
e.replace $ λc d, if c = s then some (s'.lift_vars 0 d) else none

/-- Implementation of `expr.mreplace`. -/
meta def mreplace_aux {m : Type* → Type*} [monad m] (R : expr → nat → m (option expr)) :
  expr → ℕ → m expr
| (app f x) n := option.mget_or_else (R (app f x) n)
  (do Rf ← mreplace_aux f n, Rx ← mreplace_aux x n, return $ app Rf Rx)
| (lam nm bi ty bd) n := option.mget_or_else (R (lam nm bi ty bd) n)
  (do Rty ← mreplace_aux ty n, Rbd ← mreplace_aux bd (n+1), return $ lam nm bi Rty Rbd)
| (pi nm bi ty bd) n := option.mget_or_else (R (pi nm bi ty bd) n)
  (do Rty ← mreplace_aux ty n, Rbd ← mreplace_aux bd (n+1), return $ pi nm bi Rty Rbd)
| (elet nm ty a b) n := option.mget_or_else (R (elet nm ty a b) n)
  (do Rty ← mreplace_aux ty n,
    Ra ← mreplace_aux a n,
    Rb ← mreplace_aux b n,
    return $ elet nm Rty Ra Rb)
| (macro c es) n := option.mget_or_else (R (macro c es) n) $
    macro c <$> es.mmap (λ e, mreplace_aux e n)
| e n := option.mget_or_else (R e n) (return e)

/--
Monadic analogue of `expr.replace`.

The `mreplace R e` visits each subexpression `s` of `e`, and is called with `R s n`, where
`n` is the number of binders above `e`.
If `R s n` fails, the whole replacement fails.
If `R s n` returns `some t`, `s` is replaced with `t` (and `mreplace` does not visit
its subexpressions).
If `R s n` return `none`, then `mreplace` continues visiting subexpressions of `s`.

WARNING: This function performs exponentially worse on large terms than `expr.replace`,
if a subexpression occurs more than once in an expression, `expr.replace` visits them only once,
but this function will visit every occurence of it. Do not use this on large expressions.
-/
meta def mreplace {m : Type* → Type*} [monad m] (R : expr → nat → m (option expr)) (e : expr) :
  m expr :=
mreplace_aux R e 0

/-- Match a variable. -/
meta def match_var {elab} : expr elab → option ℕ
| (var n) := some n
| _ := none

/-- Match a sort. -/
meta def match_sort {elab} : expr elab → option level
| (sort u) := some u
| _ := none

/-- Match a constant. -/
meta def match_const {elab} : expr elab → option (name × list level)
| (const n lvls) := some (n, lvls)
| _ := none

/-- Match a metavariable. -/
meta def match_mvar {elab} : expr elab →
  option (name × name × expr elab)
| (mvar unique pretty type) := some (unique, pretty, type)
| _ := none

/-- Match a local constant. -/
meta def match_local_const {elab} : expr elab →
  option (name × name × binder_info × expr elab)
| (local_const unique pretty bi type) := some (unique, pretty, bi, type)
| _ := none

/-- Match an application. -/
meta def match_app {elab} : expr elab → option (expr elab × expr elab)
| (app t u) := some (t, u)
| _ := none

/-- Match an application of `coe_fn`. -/
meta def match_app_coe_fn : expr → option (expr × expr × expr × expr)
| (app `(@coe_fn %%α %%inst %%fexpr) x) := some (α, inst, fexpr, x)
| _ := none

/-- Match an abstraction. -/
meta def match_lam {elab} : expr elab →
  option (name × binder_info × expr elab × expr elab)
| (lam var_name bi type body) := some (var_name, bi, type, body)
| _ := none

/-- Match a Π type. -/
meta def match_pi {elab} : expr elab →
  option (name × binder_info × expr elab × expr elab)
| (pi var_name bi type body) := some (var_name, bi, type, body)
| _ := none

/-- Match a let. -/
meta def match_elet {elab} : expr elab →
  option (name × expr elab × expr elab × expr elab)
| (elet var_name type assignment body) := some (var_name, type, assignment, body)
| _ := none

/-- Match a macro. -/
meta def match_macro {elab} : expr elab →
  option (macro_def × list (expr elab))
| (macro df args) := some (df, args)
| _ := none

/-- Tests whether an expression is a meta-variable. -/
meta def is_mvar : expr → bool
| (mvar _ _ _) := tt
| _            := ff

/-- Tests whether an expression is a sort. -/
meta def is_sort : expr → bool
| (sort _) := tt
| e         := ff

/-- Get the universe levels of a `const` expression -/
meta def univ_levels : expr → list level
| (const n ls) := ls
| _            := []

/--
Replace any metavariables in the expression with underscores, in preparation for printing
`refine ...` statements.
-/
meta def replace_mvars (e : expr) : expr :=
e.replace (λ e' _, if e'.is_mvar then some (unchecked_cast pexpr.mk_placeholder) else none)

/-- If `e` is a local constant, `to_implicit_local_const e` changes the binder info of `e` to
 `implicit`. See also `to_implicit_binder`, which also changes lambdas and pis. -/
meta def to_implicit_local_const : expr → expr
| (expr.local_const uniq n bi t) := expr.local_const uniq n binder_info.implicit t
| e := e

/-- If `e` is a local constant, lamda, or pi expression, `to_implicit_binder e` changes the binder
info of `e` to `implicit`. See also `to_implicit_local_const`, which only changes local constants.
-/
meta def to_implicit_binder : expr → expr
| (local_const n₁ n₂ _ d) := local_const n₁ n₂ binder_info.implicit d
| (lam n _ d b) := lam n binder_info.implicit d b
| (pi n _ d b) := pi n binder_info.implicit d b
| e  := e

/-- Returns a list of all local constants in an expression (without duplicates). -/
meta def list_local_consts (e : expr) : list expr :=
e.fold [] (λ e' _ es, if e'.is_local_constant then insert e' es else es)

/-- Returns the set of all local constants in an expression. -/
meta def list_local_consts' (e : expr) : expr_set :=
e.fold mk_expr_set (λ e' _ es, if e'.is_local_constant then es.insert e' else es)

/-- Returns the unique names of all local constants in an expression. -/
meta def list_local_const_unique_names (e : expr) : name_set :=
e.fold mk_name_set
  (λ e' _ es, if e'.is_local_constant then es.insert e'.local_uniq_name else es)

/-- Returns a name_set of all constants in an expression. -/
meta def list_constant (e : expr) : name_set :=
e.fold mk_name_set (λ e' _ es, if e'.is_constant then es.insert e'.const_name else es)

/-- Returns a list of all meta-variables in an expression (without duplicates). -/
meta def list_meta_vars (e : expr) : list expr :=
e.fold [] (λ e' _ es, if e'.is_mvar then insert e' es else es)

/-- Returns the set of all meta-variables in an expression. -/
meta def list_meta_vars' (e : expr) : expr_set :=
e.fold mk_expr_set (λ e' _ es, if e'.is_mvar then es.insert e' else es)

/-- Returns a list of all universe meta-variables in an expression (without duplicates). -/
meta def list_univ_meta_vars (e : expr) : list name :=
native.rb_set.to_list $ e.fold native.mk_rb_set $ λ e' i s,
match e' with
| (sort u) := u.fold_mvar (flip native.rb_set.insert) s
| (const _ ls) := ls.foldl (λ s' l, l.fold_mvar (flip native.rb_set.insert) s') s
| _ := s
end

/--
Test `t` contains the specified subexpression `e`, or a metavariable.
This represents the notion that `e` "may occur" in `t`,
possibly after subsequent unification.
-/
meta def contains_expr_or_mvar (t : expr) (e : expr) : bool :=
-- We can't use `t.has_meta_var` here, as that detects universe metavariables, too.
¬ t.list_meta_vars.empty ∨ e.occurs t

/-- Returns a name_set of all constants in an expression starting with a certain prefix. -/
meta def list_names_with_prefix (pre : name) (e : expr) : name_set :=
e.fold mk_name_set $ λ e' _ l,
  match e' with
  | expr.const n _ := if n.get_prefix = pre then l.insert n else l
  | _ := l
  end

/-- Returns true if `e` contains a name `n` where `p n` is true.
  Returns `true` if `p name.anonymous` is true. -/
meta def contains_constant (e : expr) (p : name → Prop) [decidable_pred p] : bool :=
e.fold ff (λ e' _ b, if p (e'.const_name) then tt else b)

/--
Returns true if `e` contains a `sorry`.
-/
meta def contains_sorry (e : expr) : bool :=
e.fold ff (λ e' _ b, if (is_sorry e').is_some then tt else b)

/--
`app_symbol_in e l` returns true iff `e` is an application of a constant whose name is in `l`.
-/
meta def app_symbol_in (e : expr) (l : list name) : bool :=
match e.get_app_fn with
| (expr.const n _) := n ∈ l
| _ := ff
end

/-- `get_simp_args e` returns the arguments of `e` that simp can reach via congruence lemmas. -/
meta def get_simp_args (e : expr) : tactic (list expr) :=
-- `mk_specialized_congr_lemma_simp` throws an assertion violation if its argument is not an app
if ¬ e.is_app then pure [] else do
cgr ← mk_specialized_congr_lemma_simp e,
pure $ do
  (arg_kind, arg) ← cgr.arg_kinds.zip e.get_app_args,
  guard $ arg_kind = congr_arg_kind.eq,
  pure arg

/-- Simplifies the expression `t` with the specified options.
  The result is `(new_e, pr)` with the new expression `new_e` and a proof
  `pr : e = new_e`. -/
meta def simp (t : expr)
  (cfg : simp_config := {}) (discharger : tactic unit := failed)
  (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) :
  tactic (expr × expr × name_set) :=
do (s, to_unfold) ← mk_simp_set no_defaults attr_names hs,
   simplify s to_unfold t cfg `eq discharger

/-- Definitionally simplifies the expression `t` with the specified options.
  The result is the simplified expression. -/
meta def dsimp (t : expr)
  (cfg : dsimp_config := {})
  (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) :
  tactic expr :=
do (s, to_unfold) ← mk_simp_set no_defaults attr_names hs,
   s.dsimplify to_unfold t cfg

/-- Get the names of the bound variables by a sequence of pis or lambdas. -/
meta def binding_names : expr → list name
| (pi n _ _ e)  := n :: e.binding_names
| (lam n _ _ e) := n :: e.binding_names
| e             := []

/-- head-reduce a single let expression -/
meta def reduce_let : expr → expr
| (elet _ _ v b) := b.instantiate_var v
| e              := e

/-- head-reduce all let expressions -/
meta def reduce_lets : expr → expr
| (elet _ _ v b) := reduce_lets $ b.instantiate_var v
| e              := e

/-- Instantiate lambdas in the second argument by expressions from the first. -/
meta def instantiate_lambdas : list expr → expr → expr
| (e'::es) (lam n bi t e) := instantiate_lambdas es (e.instantiate_var e')
| _        e              := e

/-- Repeatedly apply `expr.subst`. -/
meta def substs : expr → list expr → expr | e es := es.foldl expr.subst e

/-- `instantiate_lambdas_or_apps es e` instantiates lambdas in `e` by expressions from `es`.
If the length of `es` is larger than the number of lambdas in `e`,
then the term is applied to the remaining terms.
Also reduces head let-expressions in `e`, including those after instantiating all lambdas.

This is very similar to `expr.substs`, but this also reduces head let-expressions. -/
meta def instantiate_lambdas_or_apps : list expr → expr → expr
| (v::es) (lam n bi t b) := instantiate_lambdas_or_apps es $ b.instantiate_var v
| es      (elet _ _ v b) := instantiate_lambdas_or_apps es $ b.instantiate_var v
| es      e              := mk_app e es

/--
Some declarations work with open expressions, i.e. an expr that has free variables.
Terms will free variables are not well-typed, and one should not use them in tactics like
`infer_type` or `unify`. You can still do syntactic analysis/manipulation on them.
The reason for working with open types is for performance: instantiating variables requires
iterating through the expression. In one performance test `pi_binders` was more than 6x
quicker than `mk_local_pis` (when applied to the type of all imported declarations 100x).
-/
library_note "open expressions"

/-- Get the codomain/target of a pi-type.
  This definition doesn't instantiate bound variables, and therefore produces a term that is open.
  See note [open expressions]. -/
meta def pi_codomain : expr → expr
| (pi n bi d b) := pi_codomain b
| e             := e

/-- Get the body/value of a lambda-expression.
  This definition doesn't instantiate bound variables, and therefore produces a term that is open.
  See note [open expressions]. -/
meta def lambda_body : expr → expr
| (lam n bi d b) := lambda_body b
| e             := e

/-- Auxiliary defintion for `pi_binders`.
  See note [open expressions]. -/
meta def pi_binders_aux : list binder → expr → list binder × expr
| es (pi n bi d b) := pi_binders_aux (⟨n, bi, d⟩::es) b
| es e             := (es, e)

/-- Get the binders and codomain of a pi-type.
  This definition doesn't instantiate bound variables, and therefore produces a term that is open.
  The.tactic `get_pi_binders` in `tactic.core` does the same, but also instantiates the
  free variables.
  See note [open expressions]. -/
meta def pi_binders (e : expr) : list binder × expr :=
let (es, e) := pi_binders_aux [] e in (es.reverse, e)

/-- Auxiliary defintion for `get_app_fn_args`. -/
meta def get_app_fn_args_aux : list expr → expr → expr × list expr
| r (app f a) := get_app_fn_args_aux (a::r) f
| r e         := (e, r)

/-- A combination of `get_app_fn` and `get_app_args`: lists both the
  function and its arguments of an application -/
meta def get_app_fn_args : expr → expr × list expr :=
get_app_fn_args_aux []

/-- `drop_pis es e` instantiates the pis in `e` with the expressions from `es`. -/
meta def drop_pis : list expr → expr → tactic expr
| (v :: vs) (pi n bi d b) := do
  t ← infer_type v,
  guard (t =ₐ d),
  drop_pis vs (b.instantiate_var v)
| [] e := return e
| _  _ := failed

/-- `instantiate_pis es e` instantiates the pis in `e` with the expressions from `es`.
  Does not check whether the result remains type-correct. -/
meta def instantiate_pis : list expr → expr → expr
| (v :: vs) (pi n bi d b) := instantiate_pis vs (b.instantiate_var v)
| _ e := e

/-- `mk_op_lst op empty [x1, x2, ...]` is defined as `op x1 (op x2 ...)`.
  Returns `empty` if the list is empty. -/
meta def mk_op_lst (op : expr) (empty : expr) : list expr → expr
| []        := empty
| [e]       := e
| (e :: es) := op e $ mk_op_lst es

/-- `mk_and_lst [x1, x2, ...]` is defined as `x1 ∧ (x2 ∧ ...)`, or `true` if the list is empty. -/
meta def mk_and_lst : list expr → expr := mk_op_lst `(and) `(true)

/-- `mk_or_lst [x1, x2, ...]` is defined as `x1 ∨ (x2 ∨ ...)`, or `false` if the list is empty. -/
meta def mk_or_lst : list expr → expr := mk_op_lst `(or) `(false)

/-- `local_binding_info e` returns the binding info of `e` if `e` is a local constant.
Otherwise returns `binder_info.default`. -/
meta def local_binding_info : expr → binder_info
| (expr.local_const _ _ bi _) := bi
| _ := binder_info.default

/-- `is_default_local e` tests whether `e` is a local constant with binder info
`binder_info.default` -/
meta def is_default_local : expr → bool
| (expr.local_const _ _ binder_info.default _) := tt
| _ := ff

/-- `has_local_constant e l` checks whether local constant `l` occurs in expression `e` -/
meta def has_local_constant (e l : expr) : bool :=
e.has_local_in $ mk_name_set.insert l.local_uniq_name

/-- Turns a local constant into a binder -/
meta def to_binder : expr → binder
| (local_const _ nm bi t) := ⟨nm, bi, t⟩
| _                       := default binder

/-- Strip-away the context-dependent unique id for the given local const and return: its friendly
`name`, its `binder_info`, and its `type : expr`. -/
meta def get_local_const_kind : expr → name × binder_info × expr
| (expr.local_const _ n bi e) := (n, bi, e)
| _ := (name.anonymous, binder_info.default, expr.const name.anonymous [])

/-- `local_const_set_type e t` sets the type of `e` to `t`, if `e` is a `local_const`. -/
meta def local_const_set_type {elab : bool} : expr elab → expr elab → expr elab
| (expr.local_const x n bi t) new_t := expr.local_const x n bi new_t
| e                           new_t := e

/-- `unsafe_cast e` freely changes the `elab : bool` parameter of the passed `expr`. Mainly used to
access core `expr` manipulation functions for `pexpr`-based use, but which are restricted to
`expr tt` at the site of definition unnecessarily.

DANGER: Unless you know exactly what you are doing, this is probably not the function you are
looking for. For `pexpr → expr` see `tactic.to_expr`. For `expr → pexpr` see `to_pexpr`. -/
meta def unsafe_cast {elab₁ elab₂ : bool} : expr elab₁ → expr elab₂ := unchecked_cast

/-- `replace_subexprs e mappings` takes an `e : expr` and interprets a `list (expr × expr)` as
a collection of rules for variable replacements. A pair `(f, t)` encodes a rule which says "whenever
`f` is encountered in `e` verbatim, replace it with `t`". -/
meta def replace_subexprs {elab : bool} (e : expr elab) (mappings : list (expr × expr)) :
  expr elab :=
unsafe_cast $ e.unsafe_cast.replace $ λ e n,
  (mappings.filter $ λ ent : expr × expr, ent.1 = e).head'.map prod.snd

/-- `is_implicitly_included_variable e vs` accepts `e`, an `expr.local_const`, and a list `vs` of
    other `expr.local_const`s. It determines whether `e` should be considered "available in context"
    as a variable by virtue of the fact that the variables `vs` have been deemed such.

    For example, given `variables (n : ℕ) [prime n] [ih : even n]`, a reference to `n` implies that
    the typeclass instance `prime n` should be included, but `ih : even n` should not.

    DANGER: It is possible that for `f : expr` another `expr.local_const`, we have
    `is_implicitly_included_variable f vs = ff` but
    `is_implicitly_included_variable f (e :: vs) = tt`. This means that one usually wants to
    iteratively add a list of local constants (usually, the `variables` declared in the local scope)
    which satisfy `is_implicitly_included_variable` to an initial `vs`, repeating if any variables
    were added in a particular iteration. The function `all_implicitly_included_variables` below
    implements this behaviour.

    Note that if `e ∈ vs` then `is_implicitly_included_variable e vs = tt`. -/
meta def is_implicitly_included_variable (e : expr) (vs : list expr) : bool :=
if ¬(e.local_pp_name.to_string.starts_with "_") then
  e ∈ vs
else e.local_type.fold tt $ λ se _ b,
  if ¬b then ff
  else if ¬se.is_local_constant then tt
  else se ∈ vs

/-- Private work function for `all_implicitly_included_variables`, performing the actual series of
    iterations, tracking with a boolean whether any updates occured this iteration. -/
private meta def all_implicitly_included_variables_aux
  : list expr → list expr → list expr → bool → list expr
| []          vs rs tt := all_implicitly_included_variables_aux rs vs [] ff
| []          vs rs ff := vs
| (e :: rest) vs rs b :=
  let (vs, rs, b) :=
    if e.is_implicitly_included_variable vs then (e :: vs, rs, tt) else (vs, e :: rs, b) in
  all_implicitly_included_variables_aux rest vs rs b

/-- `all_implicitly_included_variables es vs` accepts `es`, a list of `expr.local_const`, and `vs`,
    another such list. It returns a list of all variables `e` in `es` or `vs` for which an inclusion
    of the variables in `vs` into the local context implies that `e` should also be included. See
    `is_implicitly_included_variable e vs` for the details.

    In particular, those elements of `vs` are included automatically. -/
meta def all_implicitly_included_variables (es vs : list expr) : list expr :=
all_implicitly_included_variables_aux es vs [] ff

/-- Infer the type of an application of the form `f x1 x2 ... xn`, where `f` is an identifier.
This also works if `x1, ... xn` contain free variables. -/
protected meta def simple_infer_type (env : environment) (e : expr) : exceptional expr := do
(@const tt n ls, es) ← return e.get_app_fn_args |
  exceptional.fail "expression is not a constant applied to arguments",
d ← env.get n,
return $ (d.type.instantiate_pis es).instantiate_univ_params $ d.univ_params.zip ls

/-- Auxilliary function for `head_eta_expand`. -/
meta def head_eta_expand_aux : ℕ → expr → expr → expr
| (n+1) e (pi x bi d b) :=
  lam x bi d $ head_eta_expand_aux n e b
| _ e _ := e

/-- `head_eta_expand n e t` eta-expands `e` `n` times, with the binders info and domains obtained
  by its type `t`. -/
meta def head_eta_expand (n : ℕ) (e t : expr) : expr :=
((e.lift_vars 0 n).mk_app $ (list.range n).reverse.map var).head_eta_expand_aux n t

/-- `e.eta_expand env dict` eta-expands all expressions that have as head a constant `n` in
`dict`. They are expanded until they are applied to one more argument than the maximum in
`dict.find n`. -/
protected meta def eta_expand (env : environment) (dict : name_map $ list ℕ) : expr → expr
| e := e.replace $ λ e _, do
  let (e0, es) := e.get_app_fn_args,
  let ns := (dict.find e0.const_name).iget,
  guard (bnot ns.empty),
  let e' := e0.mk_app $ es.map eta_expand,
  let needed_n := ns.foldr max 0 + 1,
  if needed_n ≤ es.length then some e'
  else do
    e'_type ← (e'.simple_infer_type env).to_option,
    some $ head_eta_expand (needed_n - es.length) e' e'_type

/--
`e.apply_replacement_fun f test` applies `f` to each identifier
(inductive type, defined function etc) in an expression, unless
* The identifier occurs in an application with first argument `arg`; and
* `test arg` is false.
* Reorder contains the information about what arguments to reorder:
  e.g. `g x₁ x₂ x₃ ... xₙ` becomes `g x₂ x₁ x₃ ... xₙ` if `reorder.find g = some [1]`.
  We assume that all functions where we want to reorder arguments are fully applied.
  This can be done by applying `expr.eta_expand` first.
-/
protected meta def apply_replacement_fun (f : name → name) (test : expr → bool)
  (reorder : name_map $ list ℕ) : expr → expr
| e := e.replace $ λ e _,
  match e with
  | const n ls := some $ const (f n) $
      -- if the first two arguments are reordered, we also reorder the first two universe parameters
      if 1 ∈ (reorder.find n).iget then ls.inth 1::ls.head::ls.drop 2 else ls
  | app g x :=
    let l := (reorder.find g.get_app_fn.const_name).iget in -- this might be inefficient
    if g.get_app_num_args ∈ l ∧ test g.get_app_args.head then
    -- interchange `x` and the last argument of `g`
    some $ apply_replacement_fun g.app_fn (apply_replacement_fun x) $
      apply_replacement_fun g.app_arg else
    if g.is_constant ∧ ¬ test x then some $ g (apply_replacement_fun x) else none
  | _ := none
  end

end expr

/-! ### Declarations about `environment` -/

namespace environment

/-- Tests whether `n` is a structure. -/
meta def is_structure (env : environment) (n : name) : bool :=
(env.structure_fields n).is_some

/-- Get the full names of all projections of the structure `n`. Returns `none` if `n` is not a
  structure. -/
meta def structure_fields_full (env : environment) (n : name) : option (list name) :=
(env.structure_fields n).map (list.map $ λ n', n ++ n')

/-- Tests whether `nm` is a generalized inductive type that is not a normal inductive type.
  Note that `is_ginductive` returns `tt` even on regular inductive types.
  This returns `tt` if `nm` is (part of a) mutually defined inductive type or a nested inductive
  type. -/
meta def is_ginductive' (e : environment) (nm : name) : bool :=
e.is_ginductive nm ∧ ¬ e.is_inductive nm

/-- For all declarations `d` where `f d = some x` this adds `x` to the returned list.  -/
meta def decl_filter_map {α : Type} (e : environment) (f : declaration → option α) : list α :=
  e.fold [] $ λ d l, match f d with
                     | some r := r :: l
                     | none := l
                     end

/-- Maps `f` to all declarations in the environment. -/
meta def decl_map {α : Type} (e : environment) (f : declaration → α) : list α :=
  e.decl_filter_map $ λ d, some (f d)

/-- Lists all declarations in the environment -/
meta def get_decls (e : environment) : list declaration :=
  e.decl_map id

/-- Lists all trusted (non-meta) declarations in the environment -/
meta def get_trusted_decls (e : environment) : list declaration :=
  e.decl_filter_map (λ d, if d.is_trusted then some d else none)

/-- Lists the name of all declarations in the environment -/
meta def get_decl_names (e : environment) : list name :=
  e.decl_map declaration.to_name

/-- Fold a monad over all declarations in the environment. -/
meta def mfold {α : Type} {m : Type → Type} [monad m] (e : environment) (x : α)
  (fn : declaration → α → m α) : m α :=
e.fold (return x) (λ d t, t >>= fn d)

/-- Filters all declarations in the environment. -/
meta def filter (e : environment) (test : declaration → bool) : list declaration :=
e.fold [] $ λ d ds, if test d then d::ds else ds

/-- Filters all declarations in the environment. -/
meta def mfilter (e : environment) (test : declaration → tactic bool) : tactic (list declaration) :=
e.mfold [] $ λ d ds, do b ← test d, return $ if b then d::ds else ds

/-- Checks whether `s` is a prefix of the file where `n` is declared.
  This is used to check whether `n` is declared in mathlib, where `s` is the mathlib directory. -/
meta def is_prefix_of_file (e : environment) (s : string) (n : name) : bool :=
s.is_prefix_of $ (e.decl_olean n).get_or_else ""

end environment

/-!
### `is_eta_expansion`

 In this section we define the tactic `is_eta_expansion` which checks whether an expression
  is an eta-expansion of a structure. (not to be confused with eta-expanion for `λ`).

-/

namespace expr

open tactic

/-- `is_eta_expansion_of args univs l` checks whether for all elements `(nm, pr)` in `l` we have
  `pr = nm.{univs} args`.
  Used in `is_eta_expansion`, where `l` consists of the projections and the fields of the value we
  want to eta-reduce. -/
meta def is_eta_expansion_of (args : list expr) (univs : list level) (l : list (name × expr)) :
  bool :=
l.all $ λ⟨proj, val⟩, val = (const proj univs).mk_app args

/-- `is_eta_expansion_test l` checks whether there is a list of expresions `args` such that for all
  elements `(nm, pr)` in `l` we have `pr = nm args`. If so, returns the last element of `args`.
  Used in `is_eta_expansion`, where `l` consists of the projections and the fields of the value we
  want to eta-reduce. -/
meta def is_eta_expansion_test : list (name × expr) → option expr
| []              := none
| (⟨proj, val⟩::l) :=
  match val.get_app_fn with
  | (const nm univs : expr) :=
    if nm = proj then
      let args := val.get_app_args in
      let e := args.ilast in
      if is_eta_expansion_of args univs l then some e else none
    else
      none
  | _                       := none
  end

/-- `is_eta_expansion_aux val l` checks whether `val` can be eta-reduced to an expression `e`.
  Here `l` is intended to consists of the projections and the fields of `val`.
  This tactic calls `is_eta_expansion_test l`, but first removes all proofs from the list `l` and
  afterward checks whether the resulting expression `e` unifies with `val`.
  This last check is necessary, because `val` and `e` might have different types. -/
meta def is_eta_expansion_aux (val : expr) (l : list (name × expr)) : tactic (option expr) :=
do l' ← l.mfilter (λ⟨proj, val⟩, bnot <$> is_proof val),
  match is_eta_expansion_test l' with
  | some e := option.map (λ _, e) <$> try_core (unify e val)
  | none   := return none
  end

/-- `is_eta_expansion val` checks whether there is an expression `e` such that `val` is the
  eta-expansion of `e`.
  With eta-expansion we here mean the eta-expansion of a structure, not of a function.
  For example, the eta-expansion of `x : α × β` is `⟨x.1, x.2⟩`.
  This assumes that `val` is a fully-applied application of the constructor of a structure.

  This is useful to reduce expressions generated by the notation
    `{ field_1 := _, ..other_structure }`
  If `other_structure` is itself a field of the structure, then the elaborator will insert an
  eta-expanded version of `other_structure`. -/
meta def is_eta_expansion (val : expr) : tactic (option expr) := do
  e ← get_env,
  type ← infer_type val,
  projs ← e.structure_fields_full type.get_app_fn.const_name,
  let args := (val.get_app_args).drop type.get_app_args.length,
  is_eta_expansion_aux val (projs.zip args)

end expr

/-! ### Declarations about `declaration` -/

namespace declaration
open tactic

/--
`declaration.update_with_fun f test tgt decl`
sets the name of the given `decl : declaration` to `tgt`, and applies both `expr.eta_expand` and
`expr.apply_replacement_fun` to the value and type of `decl`.
-/
protected meta def update_with_fun (env : environment) (f : name → name) (test : expr → bool)
  (reorder : name_map $ list ℕ) (tgt : name) (decl : declaration) : declaration :=
let decl := decl.update_name $ tgt in
let decl := decl.update_type $
  (decl.type.eta_expand env reorder).apply_replacement_fun f test reorder in
decl.update_value $ (decl.value.eta_expand env reorder).apply_replacement_fun f test reorder

/-- Checks whether the declaration is declared in the current file.
  This is a simple wrapper around `environment.in_current_file`
  Use `environment.in_current_file` instead if performance matters. -/
meta def in_current_file (d : declaration) : tactic bool :=
do e ← get_env, return $ e.in_current_file d.to_name

/-- Checks whether a declaration is a theorem -/
meta def is_theorem : declaration → bool
| (thm _ _ _ _) := tt
| _             := ff

/-- Checks whether a declaration is a constant -/
meta def is_constant : declaration → bool
| (cnst _ _ _ _) := tt
| _              := ff

/-- Checks whether a declaration is a axiom -/
meta def is_axiom : declaration → bool
| (ax _ _ _) := tt
| _          := ff

/-- Checks whether a declaration is automatically generated in the environment.
  There is no cheap way to check whether a declaration in the namespace of a generalized
  inductive type is automatically generated, so for now we say that all of them are automatically
  generated. -/
meta def is_auto_generated (e : environment) (d : declaration) : bool :=
e.is_constructor d.to_name ∨
(e.is_projection d.to_name).is_some ∨
(e.is_constructor d.to_name.get_prefix ∧
  d.to_name.last ∈ ["inj", "inj_eq", "sizeof_spec", "inj_arrow"]) ∨
(e.is_inductive d.to_name.get_prefix ∧
  d.to_name.last ∈ ["below", "binduction_on", "brec_on", "cases_on", "dcases_on", "drec_on", "drec",
  "rec", "rec_on", "no_confusion", "no_confusion_type", "sizeof", "ibelow", "has_sizeof_inst"]) ∨
d.to_name.has_prefix (λ nm, e.is_ginductive' nm)

/--
Returns true iff `d` is an automatically-generated or internal declaration.
-/
meta def is_auto_or_internal (env : environment) (d : declaration) : bool :=
d.to_name.is_internal || d.is_auto_generated env

/-- Returns the list of universe levels of a declaration. -/
meta def univ_levels (d : declaration) : list level :=
d.univ_params.map level.param

/-- Returns the `reducibility_hints` field of a `defn`, and `reducibility_hints.opaque` otherwise -/
protected meta def reducibility_hints : declaration → reducibility_hints
| (declaration.defn _ _ _ _ red _) := red
| _ := _root_.reducibility_hints.opaque

/-- formats the arguments of a `declaration.thm` -/
private meta def print_thm (nm : name) (tp : expr) (body : task expr) : tactic format :=
do tp ← pp tp, body ← pp body.get,
   return $ "<theorem " ++ to_fmt nm ++ " : " ++ tp ++ " := " ++ body ++ ">"

/-- formats the arguments of a `declaration.defn` -/
private meta def print_defn (nm : name) (tp : expr) (body : expr) (is_trusted : bool) :
  tactic format :=
do tp ← pp tp, body ← pp body,
   return $ "<" ++ (if is_trusted then "def " else "meta def ") ++ to_fmt nm ++ " : " ++ tp ++
     " := " ++ body ++ ">"

/-- formats the arguments of a `declaration.cnst` -/
private meta def print_cnst (nm : name) (tp : expr) (is_trusted : bool) : tactic format :=
do tp ← pp tp,
   return $ "<" ++ (if is_trusted then "constant " else "meta constant ") ++ to_fmt nm ++ " : "
     ++ tp ++ ">"

/-- formats the arguments of a `declaration.ax` -/
private meta def print_ax (nm : name) (tp : expr) : tactic format :=
do tp ← pp tp,
   return $ "<axiom " ++ to_fmt nm ++ " : " ++ tp ++ ">"

/-- pretty-prints a `declaration` object. -/
meta def to_tactic_format : declaration → tactic format
| (declaration.thm nm _ tp bd) := print_thm nm tp bd
| (declaration.defn nm _ tp bd _ is_trusted) := print_defn nm tp bd is_trusted
| (declaration.cnst nm _ tp is_trusted) := print_cnst nm tp is_trusted
| (declaration.ax nm _ tp) := print_ax nm tp

meta instance : has_to_tactic_format declaration :=
⟨to_tactic_format⟩

end declaration

meta instance pexpr.decidable_eq {elab} : decidable_eq (expr elab) :=
unchecked_cast
expr.has_decidable_eq
