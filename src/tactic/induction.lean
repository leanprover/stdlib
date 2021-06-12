/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.dependencies
import tactic.fresh_names
import tactic.generalizes
import tactic.has_variable_names
import tactic.unify_equations

/-!
# A better tactic for induction and case analysis

This module defines the tactics `tactic.interactive.induction'` and
`tactic.interactive.cases'`, which are variations on Lean's builtin `induction`
and `cases`. The primed variants feature various improvements over the builtin
tactics; in particular, they generate more human-friendly names and `induction'`
deals much better with indexed inductive types. See the tactics' documentation
for more details. We also provide corresponding non-interactive induction
tactics `tactic.eliminate_hyp` and `tactic.eliminate_expr`.

The design and implementation of these tactics is described in a
[draft paper](https://limperg.de/paper/cpp2021-induction/).
-/

open expr native
open tactic.interactive (case_tag.from_tag_hyps)

namespace tactic
namespace eliminate


/-!
## Tracing

We set up two tracing functions to be used by `eliminate_hyp` and its supporting
tactics. Their output is enabled by setting `trace.eliminate_hyp` to `true`.
-/


declare_trace eliminate_hyp

/--
`trace_eliminate_hyp msg` traces `msg` if the option `trace.eliminate_hyp` is
`true`.
-/
meta def trace_eliminate_hyp {α} [has_to_format α] (msg : thunk α) : tactic unit :=
when_tracing `eliminate_hyp $ trace $ to_fmt "eliminate_hyp: " ++ to_fmt (msg ())

/--
`trace_state_eliminate_hyp msg` traces `msg` followed by the tactic state if the
option `trace.eliminate_hyp` is `true`.
-/
meta def trace_state_eliminate_hyp {α} [has_to_format α] (msg : thunk α) :
  tactic unit := do
  state ← read,
  trace_eliminate_hyp $ format.join
    [to_fmt (msg ()), "\n-----\n", to_fmt state, "\n-----"]


/-!
## Information Gathering

We define data structures for information relevant to the induction, and
functions to collect this information for a specific goal.
-/


/--
Information about a constructor argument. E.g. given the declaration

```
induction ℕ : Type
| zero : ℕ
| suc (n : ℕ) : ℕ
```

the `zero` constructor has no arguments and the `suc` constructor has one
argument, `n`.

We record the following information:

- `aname`: the argument's name. If the argument was not explicitly named in the
  declaration, the elaborator generates a name for it.
- `type` : the argument's type.
- `dependent`: whether the argument is dependent, i.e. whether it occurs in the
  remainder of the constructor type.
- `index_occurrences`: the index arguments of the constructor's return type
  in which this argument occurs. If the constructor return type is
  `I i₀ ... iₙ` and the argument under consideration is `a`, and `a` occurs in
  `i₁` and `i₂`, then the `index_occurrences` are `1, 2`. As an additional
  requirement, for `iⱼ` to be considered an index occurrences,
  the type of `iⱼ` must match that of `a` according to
  `index_occurrence_type_match`.
- `is_recursive`: whether this is a recursive constructor argument.
-/
@[derive has_reflect]
meta structure constructor_argument_info :=
(aname : name)
(type : expr)
(dependent : bool)
(index_occurrences : list ℕ)
(is_recursive : bool)

/--
Information about a constructor. Contains:

- `cname`: the constructor's name.
- `non_param_args`: information about the arguments of the constructor,
  excluding the arguments induced by the parameters of the inductive type.
- `num_non_param_args`: the length of `non_param_args`.
- `rec_args`: the subset of `non_param_args` which are recursive constructor
  arguments.
- `num_rec_args`: the length of `rec_args`.

For example, take the constructor
```
list.cons : ∀ {α} (x : α) (xs : list α), list α
```
`α` is a parameter of `list`, so `non_param_args` contains information about `x`
and `xs`. `rec_args` contains information about `xs`.
-/
@[derive has_reflect]
meta structure constructor_info :=
(cname : name)
(non_param_args : list constructor_argument_info)
(num_non_param_args : ℕ)
(rec_args : list constructor_argument_info)
(num_rec_args : ℕ)

/--
When we construct the goal for the minor premise of a given constructor, this is
the number of hypotheses we must name.
-/
meta def constructor_info.num_nameable_hypotheses (c : constructor_info) : ℕ :=
c.num_non_param_args + c.num_rec_args

/--
Information about an inductive type. Contains:

- `iname`: the type's name.
- `constructors`: information about the type's constructors.
- `num_constructors`: the length of `constructors`.
- `type`: the type's type.
- `num_param`: the type's number of parameters.
- `num_indices`: the type's number of indices.
-/
@[derive has_reflect]
meta structure inductive_info :=
(iname : name)
(constructors : list constructor_info)
(num_constructors : ℕ)
(type : expr)
(num_params : ℕ)
(num_indices : ℕ)

/--
Information about a major premise (i.e. the hypothesis on which we are
performing induction). Contains:

- `mpname`: the major premise's name.
- `mpexpr`: the major premise itself.
- `type`: the type of `mpexpr`.
- `args`: the arguments of the major premise. The major premise has type
  `I x₀ ... xₙ`, where `I` is an inductive type. `args` is the map
  `[0 → x₀, ..., n → xₙ]`.
-/
meta structure major_premise_info :=
(mpname : name)
(mpexpr : expr)
(type : expr)
(args : rb_map ℕ expr)

/--
`index_occurrence_type_match t s` is true iff `t` and `s` are definitionally
equal.
-/
-- We could extend this check to be more permissive. E.g. if a constructor
-- argument has type `list α` and the index has type `list β`, we may want to
-- consider these types sufficiently similar to inherit the name. Same (but even
-- more obvious) with `vec α n` and `vec α (n + 1)`.
meta def index_occurrence_type_match (t s : expr) : tactic bool :=
succeeds $ is_def_eq t s

/--
From the return type of a constructor `C` of an inductive type `I`, determine
the index occurrences of the constructor arguments of `C`.

Input:

- `num_params:` the number of parameters of `I`.
- `ret_type`: the return type of `C`. `e` must be of the form `I x₁ ... xₙ`.

Output: A map associating each local constant `c` that appears in any of the `xᵢ`
with the set of indexes `j` such that `c` appears in `xⱼ` and `xⱼ`'s type
matches that of `c` according to `tactic.index_occurrence_type_match`.
-/
meta def get_index_occurrences (num_params : ℕ) (ret_type : expr) :
  tactic (rb_lmap expr ℕ) := do
  ret_args ← get_app_args_whnf ret_type,
  ret_args.mfoldl_with_index
    (λ i occ_map ret_arg, do
      if i < num_params
        then pure occ_map
        else do
          let ret_arg_consts := ret_arg.list_local_consts',
          ret_arg_consts.mfold occ_map $ λ c occ_map, do
            ret_arg_type ← infer_type ret_arg,
            eq ← index_occurrence_type_match c.local_type ret_arg_type,
            pure $ if eq then occ_map.insert c i else occ_map)
    mk_rb_map

/--
Returns true iff `arg_type` is the local constant named `type_name`
(possibly applied to some arguments). If `arg_type` is the type of an argument
of one of `type_name`'s constructors and this function returns true, then the
constructor argument is a recursive occurrence.
-/
meta def is_recursive_constructor_argument (type_name : name) (arg_type : expr) :
  bool :=
let base := arg_type.get_app_fn in
match base with
| (expr.const base _) := base = type_name
| _ := ff
end

/--
Get information about the arguments of a constructor `C` of an inductive type
`I`.

Input:

- `inductive_name`: the name of `I`.
- `num_params`: the number of parameters of `I`.
- `T`: the type of `C`.

Output: a `constructor_argument_info` structure for each argument of `C`.
-/
meta def get_constructor_argument_info (inductive_name : name)
  (num_params : ℕ) (T : expr) :
  tactic (list constructor_argument_info) := do
  ⟨args, ret⟩ ← open_pis_whnf_dep T,
  index_occs ← get_index_occurrences num_params ret,
  pure $ args.map $ λ ⟨c, dep⟩,
    let occs := rb_set.of_list $ index_occs.find c in
    let type := c.local_type in
    let is_recursive := is_recursive_constructor_argument inductive_name type in
    ⟨c.local_pp_name, type, dep, occs.to_list, is_recursive⟩

/--
Get information about a constructor `C` of an inductive type `I`.

Input:

- `iname`: the name of `I`.
- `num_params`: the number of parameters of `I`.
- `c` : the name of `C`.

Output:

A `constructor_info` structure for `C`.
-/
meta def get_constructor_info (iname : name) (num_params : ℕ) (c : name) :
  tactic constructor_info := do
  env ← get_env,
  when (¬ env.is_constructor c) $ fail! "Expected {c} to be a constructor.",
  decl ← env.get c,
  args ← get_constructor_argument_info iname num_params decl.type,
  let non_param_args := args.drop num_params,
  let rec_args := non_param_args.filter $ λ ainfo, ainfo.is_recursive,
  pure
    { cname := decl.to_name,
      non_param_args := non_param_args,
      num_non_param_args := non_param_args.length,
      rec_args := rec_args,
      num_rec_args := rec_args.length
    }

/--
Get information about an inductive type `I`, given `I`'s name.
-/
meta def get_inductive_info (I : name) : tactic inductive_info := do
  env ← get_env,
  when (¬ env.is_inductive I) $ fail! "Expected {I} to be an inductive type.",
  decl ← env.get I,
  let type := decl.type,
  let num_params := env.inductive_num_params I,
  let num_indices := env.inductive_num_indices I,
  let constructor_names := env.constructors_of I,
  constructors ← constructor_names.mmap
    (get_constructor_info I num_params),
  pure
    { iname := I,
      constructors := constructors,
      num_constructors := constructors.length,
      type := type,
      num_params := num_params,
      num_indices := num_indices }

/--
Get information about a major premise. The given `expr` must be a local
hypothesis.
-/
meta def get_major_premise_info (major_premise : expr) :
  tactic major_premise_info := do
  type ← infer_type major_premise,
  ⟨f, args⟩ ← get_app_fn_args_whnf type,
  pure
    { mpname := major_premise.local_pp_name,
      mpexpr := major_premise,
      type := type,
      args := args.to_rb_map }


/-!
## Constructor Argument Naming

We define the algorithm for naming constructor arguments (which is a remarkably
big part of the tactic).
-/


/--
Information used when naming a constructor argument.
-/
meta structure constructor_argument_naming_info :=
(mpinfo : major_premise_info)
(iinfo : inductive_info)
(cinfo : constructor_info)
(ainfo : constructor_argument_info)

/--
A constructor argument naming rule takes a `constructor_argument_naming_info`
structure and returns a list of suitable names for the argument. If the rule is
not applicable to the given constructor argument, the returned list is empty.
-/
@[reducible] meta def constructor_argument_naming_rule : Type :=
constructor_argument_naming_info → tactic (list name)

/--
Naming rule for recursive constructor arguments.
-/
meta def constructor_argument_naming_rule_rec : constructor_argument_naming_rule :=
λ i, pure $ if i.ainfo.is_recursive then [i.mpinfo.mpname] else []

/--
Naming rule for constructor arguments associated with an index.
-/
meta def constructor_argument_naming_rule_index : constructor_argument_naming_rule :=
λ i,
let index_occs := i.ainfo.index_occurrences in
let major_premise_args := i.mpinfo.args in
let get_major_premise_arg_local_names : ℕ → option (name × name) := λ i, do {
  arg ← major_premise_args.find i,
  (uname, ppname, _) ← arg.match_local_const,
  pure (uname, ppname)
} in
let local_index_instantiations :=
  (index_occs.map get_major_premise_arg_local_names).all_some in
/-
Right now, this rule only triggers if the major premise arg is exactly a
local const. We could consider a more permissive rule where the major premise
arg can be an arbitrary term as long as that term *contains* only a single local
const.
-/
pure $
  match local_index_instantiations with
  | none := []
  | some [] := []
  | some ((uname, ppname) :: is) :=
    if is.all (λ ⟨uname', _⟩, uname' = uname)
      then [ppname]
      else []
  end

/--
Naming rule for constructor arguments which are named in the constructor
declaration.
-/
meta def constructor_argument_naming_rule_named : constructor_argument_naming_rule :=
λ i,
let arg_name := i.ainfo.aname in
let arg_dep := i.ainfo.dependent in
pure $
  if ! arg_dep && arg_name.is_likely_generated_binder_name
    then []
    else [arg_name]

/--
Naming rule for constructor arguments whose type is associated with a list of
typical variable names. See `tactic.typical_variable_names`.
-/
meta def constructor_argument_naming_rule_type : constructor_argument_naming_rule :=
λ i, typical_variable_names i.ainfo.type <|> pure []

/--
Naming rule for constructor arguments whose type is in `Prop`.
-/
meta def constructor_argument_naming_rule_prop : constructor_argument_naming_rule :=
λ i, do
  (sort level.zero) ← infer_type i.ainfo.type | pure [],
  pure [`h]

/--
Fallback constructor argument naming rule. This rule never fails.
-/
meta def constructor_argument_naming_rule_fallback : constructor_argument_naming_rule :=
λ _, pure [`x]

/--
`apply_constructor_argument_naming_rules info rules` applies the constructor
argument naming rules in `rules` to the constructor argument given by `info`.
Returns the result of the first applicable rule. Fails if no rule is applicable.
-/
meta def apply_constructor_argument_naming_rules
  (info : constructor_argument_naming_info)
  (rules : list constructor_argument_naming_rule) : tactic (list name) := do
  names ← try_core $ rules.mfirst (λ r, do
    names ← r info,
    match names with
    | [] := failed
    | _ := pure names
    end),
  match names with
  | none := fail
      "apply_constructor_argument_naming_rules: no applicable naming rule"
  | (some names) := pure names
  end

/--
Get possible names for a constructor argument. This tactic applies all the
previously defined rules in order. It cannot fail and always returns a nonempty
list.
-/
meta def constructor_argument_names (info : constructor_argument_naming_info) :
  tactic (list name) :=
apply_constructor_argument_naming_rules info
  [ constructor_argument_naming_rule_rec
  , constructor_argument_naming_rule_index
  , constructor_argument_naming_rule_named
  , constructor_argument_naming_rule_type
  , constructor_argument_naming_rule_prop
  , constructor_argument_naming_rule_fallback ]

/--
`intron_fresh n` introduces `n` hypotheses with names generated by
`tactic.mk_fresh_name`.
-/
meta def intron_fresh (n : ℕ) : tactic (list expr) :=
iterate_exactly n (mk_fresh_name >>= intro)

/--
Introduce the new hypotheses generated by the minor premise for a given
constructor. The new hypotheses are given fresh (unique, non-human-friendly)
names. They are later renamed by `constructor_renames`. We delay the generation
of the human-friendly names because when `constructor_renames` is called, more
names may have become unused.

Input:

- `generate_induction_hyps`: whether we generate induction hypotheses (i.e.
  whether `eliminate_hyp` is in `induction` or `cases` mode).
- `cinfo`: information about the constructor.

Output:

- For each constructor argument, the pretty name of the newly introduced
  hypothesis corresponding to the argument and its `constructor_argument_info`.
- For each newly introduced induction hypothesis, its pretty name and the name
  of the recursive constructor argument from which it was derived.
-/
meta def constructor_intros (generate_induction_hyps : bool)
  (cinfo : constructor_info) :
  tactic (list (name × constructor_argument_info) × list (name × name)) := do
  let args := cinfo.non_param_args,
  arg_hyps ← intron_fresh cinfo.num_non_param_args,
  let arg_hyp_names :=
    list.map₂ (λ (h : expr) ainfo, (h.local_pp_name, ainfo)) arg_hyps args,
  tt ← pure generate_induction_hyps | pure (arg_hyp_names, []),

  let rec_args := arg_hyp_names.filter $ λ x, x.2.is_recursive,
  ih_hyps ← intron_fresh cinfo.num_rec_args,
  let ih_hyp_names :=
    list.map₂
      (λ (h : expr) (arg : name × constructor_argument_info),
        (h.local_pp_name, arg.1))
      ih_hyps rec_args,
  pure (arg_hyp_names, ih_hyp_names)

/--
`ih_name arg_name` is the name `ih_<arg_name>`.
-/
meta def ih_name (arg_name : name) : name :=
mk_simple_name ("ih_" ++ arg_name.to_string)

private meta def get_with_name : option name → option name
| (some `_) := none
| (some n) := some n
| none := none

/--
Rename the new hypotheses in the goal for a minor premise.

Input:

- `generate_induction_hyps`: whether we generate induction hypotheses (i.e.
  whether `eliminate_hyp` is in `induction` or `cases` mode).
- `mpinfo`: information about the major premise.
- `iinfo`: information about the inductive type.
- `cinfo`: information about the constructor whose minor premise we are
  processing.
- `with_names`: a list of names given by the user. These are used to name
  constructor arguments and induction hypotheses. Our own naming logic only
  kicks in if this list does not contain enough names.
- `args` and `ihs`: the output of `constructor_intros`.

Output:

- The newly introduced hypotheses corresponding to constructor arguments.
- The newly introduced induction hypotheses.
-/
meta def constructor_renames (generate_induction_hyps : bool)
  (mpinfo : major_premise_info) (iinfo : inductive_info)
  (cinfo : constructor_info) (with_names : list name)
  (args : list (name × constructor_argument_info)) (ihs : list (name × name)) :
  tactic (list expr × list expr) := do

  -- Rename constructor arguments
  let arg_pp_name_set := name_set.of_list $ args.map prod.fst,
  let iname := iinfo.iname,
  let ⟨args, with_names⟩ := args.zip_left' with_names,
  arg_renames : list (name × list name) ←
    args.mmap_filter $ λ ⟨⟨old_ppname, ainfo⟩, with_name⟩, do {
      new ←
        match get_with_name with_name with
        | some with_name := pure [with_name]
        | none := constructor_argument_names ⟨mpinfo, iinfo, cinfo, ainfo⟩
        end,
      -- Some of the arg hyps may have been cleared by earlier simplification
      -- steps, so get_local may fail.
      (some old) ← try_core $ get_local old_ppname | pure none,
      pure $ some (old.local_uniq_name, new)
    },
  let arg_renames := rb_map.of_list arg_renames,
  arg_hyp_map ← rename_fresh arg_renames mk_name_set,
  let new_arg_hyps := arg_hyp_map.filter_map $ λ ⟨old, new⟩,
    if arg_pp_name_set.contains old.local_pp_name then some new else none,
  let arg_hyp_map : name_map expr :=
    rb_map.of_list $ arg_hyp_map.map $ λ ⟨old, new⟩, (old.local_pp_name, new),

  -- Rename induction hypotheses (if we generated them)
  tt ← pure generate_induction_hyps | pure (new_arg_hyps, []),
  let ih_pp_name_set := name_set.of_list $ ihs.map prod.fst,
  let ihs := ihs.zip_left with_names,
  ih_renames ← ihs.mmap_filter $ λ ⟨⟨ih_hyp_ppname, arg_hyp_ppname⟩, with_name⟩, do {
    some arg_hyp ← pure $ arg_hyp_map.find arg_hyp_ppname
      | fail! "internal error in constructor_renames",
    let new :=
      match get_with_name with_name with
      | some with_name := sum.inl with_name
      | none := sum.inr $ ih_name arg_hyp.local_pp_name
      end,
    (some ih_hyp) ← try_core $ get_local ih_hyp_ppname | pure none,
    pure $ some (ih_hyp.local_uniq_name, new)
  },
  let ih_renames : list (name × list name) :=
    -- Special case: When there's only one IH and it hasn't been named
    -- explicitly in a "with" clause, we call it simply "ih" (unless that name
    -- is already taken).
    match ih_renames with
    | [(h, sum.inr n)] := [(h, ["ih", n])]
    | ns := ns.map (λ ⟨h, n⟩, (h, [n.elim id id]))
    end,
  ih_hyp_map ← rename_fresh (rb_map.of_list ih_renames) mk_name_set,
  let new_ih_hyps := ih_hyp_map.filter_map $ λ ⟨old, new⟩,
    if ih_pp_name_set.contains old.local_pp_name then some new else none,
  pure (new_arg_hyps, new_ih_hyps)


/-!
## Generalisation

`induction'` can generalise the goal before performing an induction, which gives
us a more general induction hypothesis. We call this 'auto-generalisation'.
-/


/--
A value of `generalization_mode` describes the behaviour of the
auto-generalisation functionality:

- `generalize_all_except hs` means that the `hs` remain fixed and all other
  hypotheses are generalised. However, there are three exceptions:

  * Hypotheses depending on any `h` in `hs` also remain fixed. If we were to
    generalise them, we would have to generalise `h` as well.
  * Hypotheses which do not occur in the target and which do not mention the
    major premise or its dependencies are never generalised. Generalising them
    would not lead to a more general induction hypothesis.
  * Frozen local instances and their dependencies are never generalised.

- `generalize_only hs` means that only the `hs` are generalised. Exception:
  hypotheses which depend on the major premise are generalised even if they do
  not appear in `hs`.
-/
@[derive has_reflect]
inductive generalization_mode
| generalize_all_except (hs : list name) : generalization_mode
| generalize_only (hs : list name) : generalization_mode

instance : inhabited generalization_mode :=
⟨ generalization_mode.generalize_all_except []⟩

namespace generalization_mode

/--
Given the major premise and a generalization_mode, this function returns the
unique names of the hypotheses that should be generalized. See
`generalization_mode` for what these are.
-/
meta def to_generalize (major_premise : expr) :
  generalization_mode → tactic name_set
| (generalize_only ns) := do
  major_premise_rev_deps ← reverse_dependencies_of_hyps [major_premise],
  let major_premise_rev_deps :=
    name_set.of_list $ major_premise_rev_deps.map local_uniq_name,
  ns ← ns.mmap (functor.map local_uniq_name ∘ get_local),
  pure $ major_premise_rev_deps.insert_list ns
| (generalize_all_except fixed) := do
  fixed ← fixed.mmap get_local,
  tgt ← target,
  let tgt_dependencies := tgt.list_local_const_unique_names,
  major_premise_type ← infer_type major_premise,
  major_premise_dependencies ← dependency_name_set_of_hyp_inclusive major_premise,
  fixed_dependencies ←
    (major_premise :: fixed).mmap dependency_name_set_of_hyp_inclusive,
  let fixed_dependencies := fixed_dependencies.foldl name_set.union mk_name_set,
  ctx ← revertible_local_context,
  to_revert ← ctx.mmap_filter $ λ h, do {
    h_depends_on_major_premise_deps ←
      -- TODO `hyp_depends_on_local_name_set` is somewhat expensive
      hyp_depends_on_local_name_set h major_premise_dependencies,
    let h_name := h.local_uniq_name,
    let rev :=
      ¬ fixed_dependencies.contains h_name ∧
      (h_depends_on_major_premise_deps ∨ tgt_dependencies.contains h_name),
    /-
    I think `h_depends_on_major_premise_deps` is an overapproximation. What we
    actually want is any hyp that depends either on the major_premise or on one
    of the major_premise's index args. (But the overapproximation seems to work
    okay in practice as well.)
    -/
    pure $ if rev then some h_name else none
  },
  pure $ name_set.of_list to_revert

end generalization_mode

/--
Generalize hypotheses for the given major premise and generalization mode. See
`generalization_mode` and `to_generalize`.
-/
meta def generalize_hyps (major_premise : expr) (gm : generalization_mode) :
  tactic ℕ := do
  to_revert ← gm.to_generalize major_premise,
  ⟨n, _⟩ ← revert_name_set to_revert,
  pure n


/-!
## Complex Index Generalisation

A *complex* expression is any expression that is not merely a local constant.
When such a complex expression appears as an argument of the major premise, and
when that argument is an index of the inductive type, we must generalise the
complex expression. E.g. when we operate on the major premise `fin (2 + n)`
(assuming that `fin` is encoded as an inductive type), the `2 + n` is a complex
index argument. To generalise it, we replace it with a new hypothesis
`index : ℕ` and add an equation `induction_eq : index = 2 + n`.
-/

/--
Generalise the complex index arguments.

Input:

- `major premise`: the major premise.
- `num_params`: the number of parameters of the inductive type.
- `generate_induction_hyps`: whether we generate induction hypotheses (i.e.
  whether `eliminate_hyp` is in `induction` or `cases` mode).

Output:

- The new major premise. This procedure may change the major premise's type
  signature, so the old major premise hypothesis is invalidated.
- The number of index placeholder hypotheses we introduced.
- The index placeholder hypotheses we introduced.
- The number of hypotheses which were reverted because they contain complex
  indices.
-/
/-
TODO The following function currently replaces complex index arguments
everywhere in the goal, not only in the major premise. Such replacements are
sometimes necessary to make sure that the goal remains type-correct. However,
the replacements can also have the opposite effect, yielding unprovable
subgoals. The test suite contains one such case. There is probably a middle
ground between 'replace everywhere' and 'replace only in the major premise', but
I don't know what exactly this middle ground is. See also the discussion at
https://github.com/leanprover-community/mathlib/pull/5027#discussion_r538902424
-/
meta def generalize_complex_index_args (major_premise : expr) (num_params : ℕ)
  (generate_induction_hyps : bool) : tactic (expr × ℕ × list name × ℕ) :=
focus1 $ do
  major_premise_type ← infer_type major_premise,
  (major_premise_head, major_premise_args) ←
    get_app_fn_args_whnf major_premise_type,
  let ⟨major_premise_param_args, major_premise_index_args⟩ :=
    major_premise_args.split_at num_params,

  -- TODO Add equations only for complex index args (not all index args).
  -- This shouldn't matter semantically, but we'd get simpler terms.

  let js := major_premise_index_args,
  ctx ← revertible_local_context,
  tgt ← target,
  major_premise_deps ← dependency_name_set_of_hyp_inclusive major_premise,

  -- Revert the hypotheses which depend on the index args or the major_premise.
  -- We exclude dependencies of the major premise because we can't replace their
  -- index occurrences anyway when we apply the recursor.
  relevant_ctx ← ctx.mfilter $ λ h, do {
    let dep_of_major_premise := major_premise_deps.contains h.local_uniq_name,
    dep_on_major_premise ← hyp_depends_on_locals h [major_premise],
    H ← infer_type h,
    dep_of_index ← js.many $ λ j, kdepends_on H j,
    -- TODO We need a variant of `kdepends_on` that takes local defs into account.
    pure $
      (dep_on_major_premise ∧ h ≠ major_premise) ∨
      (dep_of_index ∧ ¬ dep_of_major_premise)
  },
  ⟨relevant_ctx_size, relevant_ctx⟩ ← revert_lst' relevant_ctx,
  revert major_premise,

  -- Create the local constants that will replace the index args. We have to be
  -- careful to get the right types.
  let go : expr → list expr → tactic (list expr) :=
        λ j ks, do {
          J ← infer_type j,
          k ← mk_local' `index binder_info.default J,
          ks ← ks.mmap $ λ k', kreplace k' j k,
          pure $ k :: ks
        },
  ks ← js.mfoldr go [],

  let js_ks := js.zip ks,

  -- Replace the index args in the relevant context.
  new_ctx ← relevant_ctx.mmap $ λ h, js_ks.mfoldr (λ ⟨j, k⟩ h, kreplace h j k) h,

  -- Replace the index args in the major premise.
  let new_major_premise_type :=
    major_premise_head.mk_app (major_premise_param_args ++ ks),
  let new_major_premise :=
    local_const major_premise.local_uniq_name major_premise.local_pp_name
      major_premise.binding_info new_major_premise_type,

  -- Replace the index args in the target.
  new_tgt ← js_ks.mfoldr (λ ⟨j, k⟩ tgt, kreplace tgt j k) tgt,
  let new_tgt := new_tgt.pis (new_major_premise :: new_ctx),

  -- Generate the index equations and their proofs.
  let eq_name := if generate_induction_hyps then `induction_eq else `cases_eq,
  let step2_input := js_ks.map $ λ ⟨j, k⟩, (eq_name, j, k),
  eqs_and_proofs ← generalizes.step2 reducible step2_input,
  let eqs := eqs_and_proofs.map prod.fst,
  let eq_proofs := eqs_and_proofs.map prod.snd,

  -- Assert the generalized goal and derive the current goal from it.
  generalizes.step3 new_tgt js ks eqs eq_proofs,

  -- Introduce the index variables and major premise. The index equations
  -- and the relevant context remain reverted.
  let num_index_vars := js.length,
  index_vars ← intron' num_index_vars,
  index_equations ← intron' num_index_vars,
  major_premise ← intro1,
  revert_lst index_equations,

  let index_vars := index_vars.map local_pp_name,
  pure (major_premise, index_vars.length, index_vars, relevant_ctx_size)


/-!
## Simplification of Induction Hypotheses

Auto-generalisation and complex index generalisation may produce unnecessarily
complex induction hypotheses. We define a simplification algorithm that recovers
understandable induction hypotheses in many practical cases.
-/


/--
Process one index equation for `simplify_ih`.

Input: a local constant `h : x = y` or `h : x == y`.

Output: A proof of `x = y` or `x == y` and possibly a local constant of type
`x = y` or `x == y` used in the proof. More specifically:

- For `h : x = y` and `x` defeq `y`, we return the proof of `x = y` by
  reflexivity and `none`.
- For `h : x = y` and `x` not defeq `y`, we return `h` and `h`.
- For `h : x == y` where `x` and `y` have defeq types:
  - If `x` defeq `y`, we return the proof of `x == y` by reflexivity and `none`.
  - If `x` not defeq `y`, we return `heq_of_eq h'` and a fresh local constant
    `h' : x = y`.
- For `h : x == y` where `x` and `y` do not have defeq types, we return
  `h` and `h`.

Checking for definitional equality of the left- and right-hand sides may assign
metavariables.
-/
meta def process_index_equation : expr → tactic (expr × option expr)
| h@(local_const _ ppname binfo
    T@(app (app (app (const `eq [u]) type) lhs) rhs)) := do
  rhs_eq_lhs ← succeeds $ unify lhs rhs,
  if rhs_eq_lhs
    then pure ((const `eq.refl [u]) type lhs, none)
    else do
      pure (h, some h)
| h@(local_const uname ppname binfo
    T@(app (app (app (app (const `heq [u]) lhs_type) lhs) rhs_type) rhs)) := do
  lhs_type_eq_rhs_type ← succeeds $ is_def_eq lhs_type rhs_type,
  if ¬ lhs_type_eq_rhs_type
    then do
      pure (h, some h)
    else do
      lhs_eq_rhs ← succeeds $ unify lhs rhs,
      if lhs_eq_rhs
        then pure ((const `heq.refl [u]) lhs_type lhs, none)
        else do
          c ← mk_local' ppname binfo $ (const `eq [u]) lhs_type lhs rhs,
          let arg := (const `heq_of_eq [u]) lhs_type lhs rhs c,
          pure (arg, some c)
| (local_const _ _ _ T) := fail!
  "process_index_equation: expected a homogeneous or heterogeneous equation, but got:\n{T}"
| e := fail!
  "process_index_equation: expected a local constant, but got:\n{e}"

/--
`assign_local_to_unassigned_mvar mv pp_name binfo`, where `mv` is a
metavariable, acts as follows:

- If `mv` is assigned, it is not changed and the tactic returns `none`.
- If `mv` is not assigned, it is assigned a fresh local constant with
  the type of `mv`, pretty name `pp_name` and binder info `binfo`. This local
  constant is returned.
-/
meta def assign_local_to_unassigned_mvar (mv : expr) (pp_name : name)
  (binfo : binder_info) : tactic (option expr) := do
  ff ← is_assigned mv | pure none,
  type ← infer_type mv,
  c ← mk_local' pp_name binfo type,
  unify mv c,
  pure c

/--
Apply `assign_local_to_unassigned_mvar` to a list of metavariables. Returns the
newly created local constants.
-/
meta def assign_locals_to_unassigned_mvars
  (mvars : list (expr × name × binder_info)) : tactic (list expr) :=
mvars.mmap_filter $ λ ⟨mv, pp_name, binfo⟩,
  assign_local_to_unassigned_mvar mv pp_name binfo

/--
Simplify an induction hypothesis.

Input: a local constant
```
ih : ∀ (x₁ : T₁) ... (xₙ : Tₙ) (eq₁ : y₁ = z₁) ... (eqₘ : yₘ = zₘ), P
```
where `n = num_generalized` and `m = num_index_vars`. The `xᵢ` are hypotheses
that we generalised over before performing induction. The `eqᵢ` are index
equations.

Output: a new local constant
```
ih' : ∀ (x'₁ : T'₁) ... (x'ₖ : T'ₖ) (eq'₁ : y'₁ = z'₁) ... (eq'ₗ : y'ₗ = z'ₗ), P'
```
This new induction hypothesis is derived from `ih` by removing those `eqᵢ` whose
left- and right-hand sides can be unified. This unification may also determine
some of the `xᵢ`. The `x'ᵢ` and `eq'ᵢ` are those `xᵢ` and `eqᵢ` that were not
removed by this process.

Some of the `eqᵢ` may be heterogeneous: `eqᵢ : yᵢ == zᵢ`. In this case, we
proceed as follows:

- If `yᵢ` and `zᵢ` are defeq, then `eqᵢ` is removed.
- If `yᵢ` and `zᵢ` are not defeq but their types are, then `eqᵢ` is replaced by
  `eq'ᵢ : x = y`.
- Otherwise `eqᵢ` remains unchanged.
-/
/-
TODO `simplify_ih` currently uses Lean's builtin unification procedure to
process the index equations. This procedure has some limitations. For example,
we would like to clear an IH that assumes `0 = 1` since this IH can never be
applied, but Lean's unification doesn't allow us to conclude this.

It would therefore be preferable to use the algorithm from
`tactic.unify_equations` instead. There is no problem with this in principle,
but it requires a complete refactoring of `unify_equations` so that it works
not only on hypotheses but on arbitrary terms.
-/
meta def simplify_ih (num_generalized : ℕ) (num_index_vars : ℕ) (ih : expr) :
  tactic expr := do
  T ← infer_type ih,

  -- Replace the `xᵢ` with fresh metavariables.
  (generalized_arg_mvars, body) ← open_n_pis_metas' T num_generalized,

  -- Replace the `eqᵢ` with fresh local constants.
  (index_eq_lcs, body) ← open_n_pis body num_index_vars,

  -- Process the `eqᵢ` local constants, yielding
  -- - `new_args`: proofs of `yᵢ = zᵢ`.
  -- - `new_index_eq_lcs`: local constants of type `yᵢ = zᵢ` or `yᵢ == zᵢ` used
  --   in `new_args`.
  new_index_eq_lcs_new_args ← index_eq_lcs.mmap process_index_equation,
  let (new_args, new_index_eq_lcs) := new_index_eq_lcs_new_args.unzip,
  let new_index_eq_lcs := new_index_eq_lcs.reduce_option,

  -- Assign fresh local constants to those `xᵢ` metavariables that were not
  -- assigned by the previous step.
  new_generalized_arg_lcs ←
    assign_locals_to_unassigned_mvars generalized_arg_mvars,

  -- Instantiate the metavariables assigned in the previous steps.
  new_generalized_arg_lcs ← new_generalized_arg_lcs.mmap instantiate_mvars,
  new_index_eq_lcs ← new_index_eq_lcs.mmap instantiate_mvars,

  -- Construct a proof of the new induction hypothesis by applying `ih` to the
  -- `xᵢ` metavariables and the `new_args`, then abstracting over the
  -- `new_index_eq_lcs` and the `new_generalized_arg_lcs`.
  b ← instantiate_mvars $
    ih.mk_app (generalized_arg_mvars.map prod.fst ++ new_args),
  new_ih ← lambdas (new_generalized_arg_lcs ++ new_index_eq_lcs) b,

  -- Type-check the new induction hypothesis as a sanity check.
  type_check new_ih <|> fail!
    "internal error in simplify_ih: constructed term does not type check:\n{new_ih}",

  -- Replace the old induction hypothesis with the new one.
  ih' ← note ih.local_pp_name none new_ih,
  clear ih,
  pure ih'


/-!
## Temporary utilities

The utility functions in this section should be removed pending certain changes
to Lean's standard library.
-/


/--
  Updates the tags of new subgoals produced by `cases` or `induction`. `in_tag`
  is the initial tag, i.e. the tag of the goal on which `cases`/`induction` was
  applied. `rs` should contain, for each subgoal, the constructor name
  associated with that goal and the hypotheses that were introduced.
-/
-- TODO Copied from init.meta.interactive. Make that function non-private.
meta def set_cases_tags (in_tag : tag) (rs : list (name × list expr)) : tactic unit :=
do gs ← get_goals,
   match gs with
    -- if only one goal was produced, we should not make the tag longer
   | [g] := set_tag g in_tag
   | _   :=
     let tgs : list (name × list expr × expr) :=
       rs.map₂ (λ ⟨n, new_hyps⟩ g, ⟨n, new_hyps, g⟩) gs in
     tgs.mmap' $ λ ⟨n, new_hyps, g⟩, with_enable_tags $
        set_tag g $
          (case_tag.from_tag_hyps (n :: in_tag) (new_hyps.map expr.local_uniq_name)).render
   end

end eliminate


/-!
## The Elimination Tactics

Finally, we define the tactics `induction'` and `cases'` tactics as well as the
non-interactive variant `eliminate_hyp.`
-/


open eliminate

/--
`eliminate_hyp generate_ihs h gm with_names` performs induction or case analysis
on the hypothesis `h`. If `generate_ihs` is true, the tactic performs induction,
otherwise case analysis.

In case analysis mode, `eliminate_hyp` is very similar to `tactic.cases`. The
only differences (assuming no bugs in `eliminate_hyp`) are that `eliminate_hyp`
can do case analysis on a slightly larger class of hypotheses and that it
generates more human-friendly names.

In induction mode, `eliminate_hyp` is similar to `tactic.induction`, but with
more significant differences:

- If `h` (the hypothesis we are performing induction on) has complex indices,
  `eliminate_hyp` 'remembers' them. A complex expression is any expression that
  is not merely a local hypothesis. A hypothesis `h : I p₁ ... pₙ j₁ ... jₘ`,
  where `I` is an inductive type with `n` parameters and `m` indices, has a
  complex index if any of the `jᵢ` are complex. In this situation, standard
  `induction` effectively forgets the exact values of the complex indices,
  which often leads to unprovable goals. `eliminate_hyp` 'remembers' them by
  adding propositional equalities. As a result, you may find equalities named
  `induction_eq` in your goal, and the induction hypotheses may also quantify
  over additional equalities.
- `eliminate_hyp` generalises induction hypotheses as much as possible by
  default. This means that if you eliminate `n` in the goal
  ```
  n m : ℕ
  ⊢ P n m
  ```
  the induction hypothesis is `∀ m, P n m` instead of `P n m`.

  You can modify this behaviour by giving a different generalisation mode `gm`;
  see `tactic.eliminate.generalization_mode`.
- `eliminate_hyp` generates much more human-friendly names than `induction`. It
  also clears more redundant hypotheses.
- `eliminate_hyp` currently does not support custom induction principles a la
  `induction using`.

If `with_names` is nonempty, `eliminate_hyp` uses the given names for the new
hypotheses it introduces (like `cases with` and `induction with`).

To debug this tactic, use

```
set_option trace.eliminate_hyp true
```
-/
meta def eliminate_hyp (generate_ihs : bool) (major_premise : expr)
  (gm := generalization_mode.generalize_all_except [])
  (with_names : list name := []) : tactic unit :=
focus1 $ do
  mpinfo ← get_major_premise_info major_premise,
  let major_premise_type := mpinfo.type,
  let major_premise_args := mpinfo.args.values.reverse,
  env ← get_env,

  -- Get info about the inductive type
  iname ← get_app_fn_const_whnf major_premise_type <|> fail!
    "The type of {major_premise} should be an inductive type, but it is\n{major_premise_type}",
  iinfo ← get_inductive_info iname,

  -- We would like to disallow mutual/nested inductive types, since these have
  -- complicated recursors which we probably don't support. However, there seems
  -- to be no way to find out whether an inductive type is mutual/nested.
  -- (`environment.is_ginductive` doesn't seem to work.)

  trace_state_eliminate_hyp "State before complex index generalisation:",

  -- Generalise complex indices
  (major_premise, num_index_vars, index_var_names, num_index_generalized) ←
    generalize_complex_index_args major_premise iinfo.num_params generate_ihs,

  trace_state_eliminate_hyp
    "State after complex index generalisation and before auto-generalisation:",

  -- Generalise hypotheses according to the given generalization_mode.
  num_auto_generalized ← generalize_hyps major_premise gm,
  let num_generalized := num_index_generalized + num_auto_generalized,

  -- NOTE: The previous step may have changed the unique names of all hyps in
  -- the context.

  -- Record the current case tag and the unique names of all hypotheses in the
  -- context.
  in_tag ← get_main_tag,

  trace_state_eliminate_hyp
    "State after auto-generalisation and before recursor application:",

  -- Apply the recursor. We first try the nondependent recursor, then the
  -- dependent recursor (if available).

  -- Construct a pexpr `@rec _ ... _ major_premise`. Why not
  -- ```(%%rec %%major_premise)?` Because for whatever reason, `false.rec_on`
  -- takes the motive not as an implicit argument, like any other recursor, but
  -- as an explicit one. Why not something based on `mk_app` or `mk_mapp`?
  -- Because we need the special elaborator support for `elab_as_eliminator`
  -- definitions.
  let rec_app : name → pexpr := λ rec_suffix,
    (unchecked_cast expr.mk_app : pexpr → list pexpr → pexpr)
      (pexpr.mk_explicit (const (iname ++ rec_suffix) []))
      (list.repeat pexpr.mk_placeholder (major_premise_args.length + 1) ++
        [to_pexpr major_premise]),
  let rec_suffix := if generate_ihs then "rec_on" else "cases_on",
  let drec_suffix := if generate_ihs then "drec_on" else "dcases_on",
  interactive.apply (rec_app rec_suffix)
    <|> interactive.apply (rec_app drec_suffix)
    <|> fail! "Failed to apply the (dependent) recursor for {iname} on {major_premise}.",

  -- Prepare the "with" names for each constructor case.
  let with_names := prod.fst $
    with_names.take_list
      (iinfo.constructors.map constructor_info.num_nameable_hypotheses),
  let constrs := iinfo.constructors.zip with_names,

  -- For each case (constructor):
  cases : list (option (name × list expr)) ←
    focus $ constrs.map $ λ ⟨cinfo, with_names⟩, do {
      trace_eliminate_hyp "============",
      trace_eliminate_hyp $ format! "Case {cinfo.cname}",
      trace_state_eliminate_hyp "Initial state:",

      -- Get the major premise's arguments. (Some of these may have changed due
      -- to the generalising step above.)
      major_premise_type ← infer_type major_premise,
      major_premise_args ← get_app_args_whnf major_premise_type,

      -- Clear the eliminated hypothesis (if possible)
      try $ clear major_premise,

      -- Clear the index args (unless other stuff in the goal depends on them)
      major_premise_args.mmap' (try ∘ clear),

      trace_state_eliminate_hyp
        "State after clearing the major premise (and its arguments) and before introductions:",

      -- Introduce the constructor arguments
      (constructor_arg_names, ih_names) ←
        constructor_intros generate_ihs cinfo,

      -- Introduce the auto-generalised hypotheses.
      intron num_auto_generalized,

      -- Introduce the index equations
      index_equations ← intron' num_index_vars,
      let index_equations := index_equations.map local_pp_name,

      -- Introduce the hypotheses that were generalised during index
      -- generalisation.
      intron num_index_generalized,

      trace_state_eliminate_hyp
        "State after introductions and before simplifying index equations:",

      -- Simplify the index equations. Stop after this step if the goal has been
      -- solved by the simplification.
      ff ← unify_equations index_equations
        | trace_eliminate_hyp "Case solved while simplifying index equations." >>
          pure none,

      trace_state_eliminate_hyp
        "State after simplifying index equations and before simplifying IHs:",

      -- Simplify the induction hypotheses
      -- NOTE: The previous step may have changed the unique names of the
      -- induction hypotheses, so we have to locate them again. Their pretty
      -- names should be unique in the context, so we can use these.
      (ih_names.map prod.fst).mmap'
        (get_local >=> simplify_ih num_auto_generalized num_index_vars),

      trace_state_eliminate_hyp
        "State after simplifying IHs and before clearing index variables:",

      -- Try to clear the index variables. These often become unused during
      -- the index equation simplification step.
      index_var_names.mmap $ λ h, try (get_local h >>= clear),

      trace_state_eliminate_hyp
        "State after clearing index variables and before renaming:",

      -- Rename the constructor names and IHs. We do this here (rather than
      -- earlier, when we introduced them) because there may now be less
      -- hypotheses in the context, and therefore more of the desired
      -- names may be free.
      (constructor_arg_hyps, ih_hyps) ←
        constructor_renames generate_ihs mpinfo iinfo cinfo with_names
          constructor_arg_names ih_names,

      trace_state_eliminate_hyp "Final state:",

      -- Return the constructor name and the renamable new hypotheses. These are
      -- the hypotheses that can later be renamed by the `case` tactic. Note
      -- that index variables and index equations are not renamable. This may be
      -- counterintuitive in some cases, but it's surprisingly difficult to
      -- catch exactly the relevant hyps here.
      pure $ some (cinfo.cname, constructor_arg_hyps ++ ih_hyps)
    },

  set_cases_tags in_tag cases.reduce_option,

  pure ()

/--
A variant of `tactic.eliminate_hyp` which performs induction or case analysis on
an arbitrary expression. `eliminate_hyp` requires that the major premise is a
hypothesis. `eliminate_expr` lifts this restriction by generalising the goal
over the major premise before calling `eliminate_hyp`. The generalisation
replaces the major premise with a new hypothesis `x` everywhere in the goal.
If `eq_name` is `some h`, an equation `h : major_premise = x` is added to
remember the value of the major premise.
-/
meta def eliminate_expr (generate_induction_hyps : bool) (major_premise : expr)
  (eq_name : option name := none) (gm := generalization_mode.generalize_all_except [])
  (with_names : list name := []) : tactic unit := do
  ctx ← local_context,
  revdeps ← ctx.mfilter $ λ h, do {
    H ← infer_type h,
    kdepends_on H major_premise
  },
  num_reverted ← revert_lst revdeps,
  hyp ← match eq_name with
      | some h := do
          x ← get_unused_name `x,
          interactive.generalize h () (to_pexpr major_premise, x),
          get_local x
      | none := do
          if major_premise.is_local_constant
            then pure major_premise
            else do
              x ← get_unused_name `x,
              generalize' major_premise x
      end,
  intron num_reverted,
  eliminate_hyp generate_induction_hyps hyp gm with_names

end tactic


namespace tactic.interactive

open tactic tactic.eliminate interactive interactive.types lean.parser

/--
Parse a `fixing` or `generalizing` clause for `induction'` or `cases'`.
-/
meta def generalisation_mode_parser : lean.parser generalization_mode :=
  (tk "fixing" *>
    ((tk "*" *> pure (generalization_mode.generalize_only []))
      <|>
      generalization_mode.generalize_all_except <$> many ident))
  <|>
  (tk "generalizing" *> generalization_mode.generalize_only <$> many ident)
  <|>
  pure (generalization_mode.generalize_all_except [])

precedence `fixing`:0

/--
A variant of `tactic.interactive.induction`, with the following differences:

- If the major premise (the hypothesis we are performing induction on) has
  complex indices, `induction'` 'remembers' them. A complex expression is any
  expression that is not merely a local hypothesis. A major premise
  `h : I p₁ ... pₙ j₁ ... jₘ`, where `I` is an inductive type with `n`
  parameters and `m` indices, has a complex index if any of the `jᵢ` are
  complex. In this situation, standard `induction` effectively forgets the exact
  values of the complex indices, which often leads to unprovable goals.
  `induction'` 'remembers' them by adding propositional equalities. As a
  result, you may find equalities named `induction_eq` in your goal, and the
  induction hypotheses may also quantify over additional equalities.
- `induction'` generalises induction hypotheses as much as possible by default.
  This means that if you eliminate `n` in the goal
  ```
  n m : ℕ
  ⊢ P n m
  ```
  the induction hypothesis is `∀ m, P n m` instead of `P n m`.
- `induction'` generates much more human-friendly names than `induction`. It
  also clears redundant hypotheses more aggressively.
- `induction'` currently does not support custom induction principles a la
  `induction using`.

Like `induction`, `induction'` supports some modifiers:

`induction' e with n₁ ... nₘ` uses the names `nᵢ` for the new hypotheses.

`induction' e fixing h₁ ... hₙ` fixes the hypotheses `hᵢ`, so the induction
hypothesis is not generalised over these hypotheses.

`induction' e fixing *` fixes all hypotheses. This disables the generalisation
functionality, so this mode behaves like standard `induction`.

`induction' e generalizing h₁ ... hₙ` generalises only the hypotheses `hᵢ`. This
mode behaves like `induction e generalizing h₁ ... hₙ`.

`induction' t`, where `t` is an arbitrary term (rather than a hypothesis),
generalises the goal over `t`, then performs induction on the generalised goal.

`induction' h : t = x` is similar, but also adds an equation `h : t = x` to
remember the value of `t`.

To debug this tactic, use

```
set_option trace.eliminate_hyp true
```
-/
meta def induction' (major_premise : parse cases_arg_p)
  (gm : parse generalisation_mode_parser)
  (with_names : parse (optional with_ident_list)) : tactic unit := do
  let ⟨eq_name, e⟩ := major_premise,
  e ← to_expr e,
  eliminate_expr tt e eq_name gm (with_names.get_or_else [])

/--
A variant of `tactic.interactive.cases`, with minor changes:

- `cases'` can perform case analysis on some (rare) goals that `cases` does not
  support.
- `cases'` generates much more human-friendly names for the new hypotheses it
  introduces.

This tactic supports the same modifiers as `cases`, e.g.

```
cases' H : e = x with n m o
```

This is almost exactly the same as `tactic.interactive.induction'`, only that no
induction hypotheses are generated.

To debug this tactic, use

```
set_option trace.eliminate_hyp true
```
-/
meta def cases' (major_premise : parse cases_arg_p)
  (with_names : parse (optional with_ident_list)) : tactic unit := do
  let ⟨eq_name, e⟩ := major_premise,
  e ← to_expr e,
  eliminate_expr ff e eq_name (generalization_mode.generalize_only [])
    (with_names.get_or_else [])

end tactic.interactive
