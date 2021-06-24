/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov
-/
import tactic.transform_decl
import tactic.algebra

/-!
# Transport multiplicative to additive

This file defines an attribute `to_additive` that can be used to
automatically transport theorems and definitions (but not inductive
types and structures) from a multiplicative theory to an additive theory.

Usage information is contained in the doc string of `to_additive.attr`.

### Missing features

* Automatically transport structures and other inductive types.

* For structures, automatically generate theorems like `group α ↔
  add_group (additive α)`.

* Rewrite rules for the last part of the name that work in more
  cases. E.g., we can replace `monoid` with `add_monoid` etc.
-/

namespace to_additive
open tactic exceptional

section performance_hack -- see Note [user attribute parameters]

local attribute [semireducible] reflected

local attribute [instance, priority 9000]
private meta def hacky_name_reflect : has_reflect name :=
λ n, `(id %%(expr.const n []) : name)

/-- An auxiliary attribute used to store the names of the additive versions of declarations
that have been processed by `to_additive`. -/
@[user_attribute]
private meta def aux_attr : user_attribute (name_map name) name :=
{ name      := `to_additive_aux,
  descr     := "Auxiliary attribute for `to_additive`. DON'T USE IT",
  cache_cfg := ⟨λ ns,
                ns.mfoldl
                  (λ dict n', do
                   let n := match n' with
                            | name.mk_string s pre := if s = "_to_additive" then pre else n'
                            | _ := n'
                            end,
                    param ← aux_attr.get_param_untyped n',
                    pure $ dict.insert n param.app_arg.const_name)
                  mk_name_map, []⟩,
  parser    := lean.parser.ident }

end performance_hack

/-- A command that can be used to have future uses of `to_additive` change the `src` namespace
to the `tgt` namespace.

For example:
```
run_cmd to_additive.map_namespace `quotient_group `quotient_add_group
```

Later uses of `to_additive` on declarations in the `quotient_group` namespace will be created
in the `quotient_add_group` namespaces.
-/
meta def map_namespace (src tgt : name) : command :=
do let n := src.mk_string "_to_additive",
   let decl := declaration.thm n [] `(unit) (pure (reflect ())),
   add_decl decl,
   aux_attr.set n tgt tt

/-- `value_type` is the type of the arguments that can be provided to `to_additive`.
`to_additive.parser` parses the provided arguments into `name` for the target and an
optional doc string. -/
@[derive has_reflect, derive inhabited]
structure value_type : Type := (tgt : name) (doc : option string)

/-- `add_comm_prefix x s` returns `"comm_" ++ s` if `x = tt` and `s` otherwise. -/
meta def add_comm_prefix : bool → string → string
| tt s := ("comm_" ++ s)
| ff s := s

/-- Dictionary used by `to_additive.guess_name` to autogenerate names. -/
meta def tr : bool → list string → list string
| is_comm ("one" :: "le" :: s)        := add_comm_prefix is_comm "nonneg"    :: tr ff s
| is_comm ("one" :: "lt" :: s)        := add_comm_prefix is_comm "pos"       :: tr ff s
| is_comm ("le" :: "one" :: s)        := add_comm_prefix is_comm "nonpos"    :: tr ff s
| is_comm ("lt" :: "one" :: s)        := add_comm_prefix is_comm "neg"       :: tr ff s
| is_comm ("mul" :: "support" :: s)   := add_comm_prefix is_comm "support"   :: tr ff s
| is_comm ("mul" :: "indicator" :: s) := add_comm_prefix is_comm "indicator" :: tr ff s
| is_comm ("mul" :: s)                := add_comm_prefix is_comm "add"       :: tr ff s
| is_comm ("smul" :: s)               := add_comm_prefix is_comm "vadd"      :: tr ff s
| is_comm ("inv" :: s)                := add_comm_prefix is_comm "neg"       :: tr ff s
| is_comm ("div" :: s)                := add_comm_prefix is_comm "sub"       :: tr ff s
| is_comm ("one" :: s)                := add_comm_prefix is_comm "zero"      :: tr ff s
| is_comm ("prod" :: s)               := add_comm_prefix is_comm "sum"       :: tr ff s
| is_comm ("finprod" :: s)            := add_comm_prefix is_comm "finsum"    :: tr ff s
| is_comm ("npow" :: s)               := add_comm_prefix is_comm "nsmul"     :: tr ff s
| is_comm ("gpow" :: s)               := add_comm_prefix is_comm "gsmul"     :: tr ff s
| is_comm ("monoid" :: s)      := ("add_" ++ add_comm_prefix is_comm "monoid")    :: tr ff s
| is_comm ("submonoid" :: s)   := ("add_" ++ add_comm_prefix is_comm "submonoid") :: tr ff s
| is_comm ("group" :: s)       := ("add_" ++ add_comm_prefix is_comm "group")     :: tr ff s
| is_comm ("subgroup" :: s)    := ("add_" ++ add_comm_prefix is_comm "subgroup")  :: tr ff s
| is_comm ("semigroup" :: s)   := ("add_" ++ add_comm_prefix is_comm "semigroup") :: tr ff s
| is_comm ("magma" :: s)       := ("add_" ++ add_comm_prefix is_comm "magma")     :: tr ff s
| is_comm ("comm" :: s)        := tr tt s
| is_comm (x :: s)             := (add_comm_prefix is_comm x :: tr ff s)
| tt []                        := ["comm"]
| ff []                        := []

/-- Autogenerate target name for `to_additive`. -/
meta def guess_name : string → string :=
string.map_tokens ''' $
λ s, string.intercalate (string.singleton '_') $
tr ff (s.split_on '_')

/-- Return the provided target name or autogenerate one if one was not provided. -/
meta def target_name (src tgt : name) (dict : name_map name) : tactic name :=
(if tgt.get_prefix ≠ name.anonymous -- `tgt` is a full name
 then pure tgt
 else match src with
      | (name.mk_string s pre) :=
        do let tgt_auto := guess_name s,
           guard (tgt.to_string ≠ tgt_auto)
             <|> trace ("`to_additive " ++ src.to_string ++ "`: correctly autogenerated target " ++
               "name, you may remove the explicit " ++ tgt_auto ++ " argument."),
           pure $ name.mk_string
                 (if tgt = name.anonymous then tgt_auto else tgt.to_string)
                 (pre.map_prefix dict.find)
      | _ := fail ("to_additive: can't transport " ++ src.to_string)
      end) >>=
(λ res,
  if res = src
  then fail ("to_additive: can't transport " ++ src.to_string ++ " to itself")
  else pure res)

/-- the parser for the arguments to `to_additive` -/
meta def parser : lean.parser value_type :=
do
  tgt ← optional lean.parser.ident,
  e ← optional interactive.types.texpr,
  doc ← match e with
      | some pe := some <$> ((to_expr pe >>= eval_expr string) : tactic string)
      | none := pure none
      end,
  return ⟨tgt.get_or_else name.anonymous, doc⟩

private meta def proceed_fields_aux (src tgt : name) (prio : ℕ) (f : name → tactic (list string)) :
  command :=
do
  src_fields ← f src,
  tgt_fields ← f tgt,
  guard (src_fields.length = tgt_fields.length) <|>
    fail ("Failed to map fields of " ++ src.to_string),
  (src_fields.zip tgt_fields).mmap' $
    λ names, guard (names.fst = names.snd) <|>
      aux_attr.set (src.append names.fst) (tgt.append names.snd) tt prio

/-- Add the `aux_attr` attribute to the structure fields of `src`
so that future uses of `to_additive` will map them to the corresponding `tgt` fields. -/
meta def proceed_fields (env : environment) (src tgt : name) (prio : ℕ) : command :=
let aux := proceed_fields_aux src tgt prio in
do
aux (λ n, pure $ list.map name.to_string $ (env.structure_fields n).get_or_else []) >>
aux (λ n, (list.map (λ (x : name), "to_" ++ x.to_string) <$> get_tagged_ancestors n)) >>
aux (λ n, (env.constructors_of n).mmap $
          λ cs, match cs with
                | (name.mk_string s pre) :=
                  (guard (pre = n) <|> fail "Bad constructor name") >>
                  pure s
                | _ := fail "Bad constructor name"
                end)

/--
The attribute `to_additive` can be used to automatically transport theorems
and definitions (but not inductive types and structures) from a multiplicative
theory to an additive theory.

To use this attribute, just write:

```
@[to_additive]
theorem mul_comm' {α} [comm_semigroup α] (x y : α) : x * y = y * x := comm_semigroup.mul_comm
```

This code will generate a theorem named `add_comm'`.  It is also
possible to manually specify the name of the new declaration, and
provide a documentation string:

```
@[to_additive add_foo "add_foo doc string"]
/-- foo doc string -/
theorem foo := sorry
```

The transport tries to do the right thing in most cases using several
heuristics described below.  However, in some cases it fails, and
requires manual intervention.

If the declaration to be transported has attributes which need to be
copied to the additive version, then `to_additive` should come last:

```
@[simp, to_additive] lemma mul_one' {G : Type*} [group G] (x : G) : x * 1 = x := mul_one x
```

The exception to this rule is the `simps` attribute, which should come after `to_additive`:

```
@[to_additive, simps]
instance {M N} [has_mul M] [has_mul N] : has_mul (M × N) := ⟨λ p q, ⟨p.1 * q.1, p.2 * q.2⟩⟩
```

## Implementation notes

The transport process generally works by taking all the names of
identifiers appearing in the name, type, and body of a declaration and
creating a new declaration by mapping those names to additive versions
using a simple string-based dictionary and also using all declarations
that have previously been labeled with `to_additive`.

In the `mul_comm'` example above, `to_additive` maps:
* `mul_comm'` to `add_comm'`,
* `comm_semigroup` to `add_comm_semigroup`,
* `x * y` to `x + y` and `y * x` to `y + x`, and
* `comm_semigroup.mul_comm'` to `add_comm_semigroup.add_comm'`.

Even when `to_additive` is unable to automatically generate the additive
version of a declaration, it can be useful to apply the attribute manually:

```
attribute [to_additive foo_add_bar] foo_bar
```

This will allow future uses of `to_additive` to recognize that
`foo_bar` should be replaced with `foo_add_bar`.

### Handling of hidden definitions

Before transporting the “main” declaration `src`, `to_additive` first
scans its type and value for names starting with `src`, and transports
them. This includes auxiliary definitions like `src._match_1`,
`src._proof_1`.

After transporting the “main” declaration, `to_additive` transports
its equational lemmas.

### Structure fields and constructors

If `src` is a structure, then `to_additive` automatically adds
structure fields to its mapping, and similarly for constructors of
inductive types.

For new structures this means that `to_additive` automatically handles
coercions, and for old structures it does the same, if ancestry
information is present in `@[ancestor]` attributes. The `ancestor`
attribute must come before the `to_additive` attribute, and it is
essential that the order of the base structures passed to `ancestor` matches
between the multiplicative and additive versions of the structure.

### Name generation

* If `@[to_additive]` is called without a `name` argument, then the
  new name is autogenerated.  First, it takes the longest prefix of
  the source name that is already known to `to_additive`, and replaces
  this prefix with its additive counterpart. Second, it takes the last
  part of the name (i.e., after the last dot), and replaces common
  name parts (“mul”, “one”, “inv”, “prod”) with their additive versions.

* Namespaces can be transformed using `map_namespace`. For example:
  ```
  run_cmd to_additive.map_namespace `quotient_group `quotient_add_group
  ```

  Later uses of `to_additive` on declarations in the `quotient_group`
  namespace will be created in the `quotient_add_group` namespaces.

* If `@[to_additive]` is called with a `name` argument `new_name`
  /without a dot/, then `to_additive` updates the prefix as described
  above, then replaces the last part of the name with `new_name`.

* If `@[to_additive]` is called with a `name` argument
  `new_namespace.new_name` /with a dot/, then `to_additive` uses this
  new name as is.

As a safety check, in the first two cases `to_additive` double checks
that the new name differs from the original one.

-/
@[user_attribute]
protected meta def attr : user_attribute unit value_type :=
{ name      := `to_additive,
  descr     := "Transport multiplicative to additive",
  parser    := parser,
  after_set := some $ λ src prio persistent, do
    guard persistent <|> fail "`to_additive` can't be used as a local attribute",
    env ← get_env,
    val ← attr.get_param src,
    dict ← aux_attr.get_cache,
    tgt ← target_name src val.tgt dict,
    aux_attr.set src tgt tt,
    let dict := dict.insert src tgt,
    if env.contains tgt
    then proceed_fields env src tgt prio
    else do
      transform_decl_with_prefix_dict dict src tgt
        [`reducible, `_refl_lemma, `simp, `norm_cast, `instance, `refl, `symm, `trans,
          `elab_as_eliminator, `no_rsimp, `continuity, `ext, `ematch, `measurability],
      mwhen (has_attribute' `simps src)
        (trace "Apply the simps attribute after the to_additive attribute"),
      match val.doc with
      | some doc := add_doc_string tgt doc
      | none := skip
      end }

add_tactic_doc
{ name                     := "to_additive",
  category                 := doc_category.attr,
  decl_names               := [`to_additive.attr],
  tags                     := ["transport", "environment", "lemma derivation"] }

end to_additive

/- map operations -/
attribute [to_additive] has_mul has_one has_inv has_div
