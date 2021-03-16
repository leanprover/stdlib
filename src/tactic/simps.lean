/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import tactic.core

/-!
# simps attribute

This file defines the `@[simps]` attribute, to automatically generate simp-lemmas
reducing a definition when projections are applied to it.

## Implementation Notes

There are three attributes being defined here
* `@[simps]` is the attribute for objects of a structure or instances of a class. It will
  automatically generate simplification lemmas for each projection of the object/instance that
  contains data. See the doc strings for `simps_attr` and `simps_cfg` for more details and
  configuration options.
* `@[_simps_str]` is automatically added to structures that have been used in `@[simps]` at least
  once. This attribute contains the data of the projections used for this structure by all following
  invocations of `@[simps]`.
* `@[notation_class]` should be added to all classes that define notation, like `has_mul` and
  `has_zero`. This specifies that the projections that `@[simps]` used are the projections from
  these notation classes instead of the projections of the superclasses.
  Example: if `has_mul` is tagged with `@[notation_class]` then the projection used for `semigroup`
  will be `λ α hα, @has_mul.mul α (@semigroup.to_has_mul α hα)` instead of `@semigroup.mul`.

## Tags

structures, projections, simp, simplifier, generates declarations
-/

open tactic expr

setup_tactic_parser
declare_trace simps.verbose
declare_trace simps.debug

/--
The `@[_simps_str]` attribute specifies the preferred projections of the given structure,
used by the `@[simps]` attribute.
- This will usually be tagged by the `@[simps]` tactic.
- You can also generate this with the command `initialize_simps_projections`.
- To change the default value, see Note [custom simps projection].
- You are strongly discouraged to add this attribute manually.
- The first argument is the list of names of the universe variables used in the structure
- The second argument is a list that consists of
  - a custom name for each projection of the structure
  - an expressions for each projections of the structure (definitionally equal to the
    corresponding projection). These expressions can contain the universe parameters specified
    in the first argument).
-/
@[user_attribute] meta def simps_str_attr : user_attribute unit (list name × list (name × expr)) :=
{ name := `_simps_str,
  descr := "An attribute specifying the projection of the given structure.",
  parser := do e ← texpr, eval_pexpr _ e }

/--
  The `@[notation_class]` attribute specifies that this is a notation class,
  and this notation should be used instead of projections by @[simps].
  * The first argument `tt` for notation classes and `ff` for classes applied to the structure,
    like `has_coe_to_sort` and `has_coe_to_fun`
  * The second argument is the name of the projection (by default it is the first projection
    of the structure)
-/
@[user_attribute] meta def notation_class_attr : user_attribute unit (bool × option name) :=
{ name := `notation_class,
  descr := "An attribute specifying that this is a notation class. Used by @[simps].",
  parser := prod.mk <$> (option.is_none <$> (tk "*")?) <*> ident? }

attribute [notation_class] has_zero has_one has_add has_mul has_inv has_neg has_sub has_div has_dvd
  has_mod has_le has_lt has_append has_andthen has_union has_inter has_sdiff has_equiv has_subset
  has_ssubset has_emptyc has_insert has_singleton has_sep has_mem has_pow

attribute [notation_class* coe_sort] has_coe_to_sort
attribute [notation_class* coe_fn] has_coe_to_fun

/--
  Get the projections used by `simps` associated to a given structure `str`. The second component is
  the list of projections, and the first component the (shared) list of universe levels used by the
  projections.

  The returned information is also stored in a parameter of the attribute `@[_simps_str]`, which
  is given to `str`. If `str` already has this attribute, the information is read from this
  attribute instead.

  The returned universe levels are the universe levels of the structure. For the projections there
  are three cases
  * If the declaration `{structure_name}.simps.{projection_name}` has been declared, then the value
    of this declaration is used (after checking that it is definitionally equal to the actual
    projection
  * Otherwise, for every class with the `notation_class` attribute, and the structure has an
    instance of that notation class, then the projection of that notation class is used for the
    projection that is definitionally equal to it (if there is such a projection).
    This means in practice that coercions to function types and sorts will be used instead of
    a projection, if this coercion is definitionally equal to a projection. Furthermore, for
    notation classes like `has_mul` and `has_zero` those projections are used instead of the
    corresponding projection
  * Otherwise, the projection of the structure is chosen.
    For example: ``simps_get_raw_projections env `prod`` gives the default projections
```
  ([u, v], [prod.fst.{u v}, prod.snd.{u v}])
```
    while ``simps_get_raw_projections env `equiv`` gives
```
  ([u_1, u_2], [λ α β, coe_fn, λ {α β} (e : α ≃ β), ⇑(e.symm), left_inv, right_inv])
```
    after declaring the coercion from `equiv` to function and adding the declaration
```
  def equiv.simps.inv_fun {α β} (e : α ≃ β) : β → α := e.symm
```

  Optionally, this command accepts two optional arguments
  * If `trace_if_exists` the command will always generate a trace message when the structure already
    has the attribute `@[_simps_str]`.
  * The `name_changes` argument accepts a list of pairs `(old_name, new_name)`. This is used to
    change the projection name `old_name` to the custom projection name `new_name`. Example:
    for the structure `equiv` the projection `to_fun` could be renamed `apply`. This name will be
    used for parsing and generating projection names. This argument is ignored if the structure
    already has an existing attribute.
-/
-- if performance becomes a problem, possible heuristic: use the names of the projections to
-- skip all classes that don't have the corresponding field.
meta def simps_get_raw_projections (e : environment) (str : name) (trace_if_exists : bool := ff)
  (name_changes : list (name × name) := []) : tactic (list name × list (name × expr)) := do
  has_attr ← has_attribute' `_simps_str str,
  if has_attr then do
    data ← simps_str_attr.get_param str,
    to_print ← data.2.mmap $ λ s, to_string <$> pformat!"Projection {s.1}: {s.2}",
    let to_print := string.join $ to_print.intersperse "\n        > ",
    -- We always trace this when called by `initialize_simps_projections`,
    -- because this doesn't do anything extra (so should not occur in mathlib).
    -- It can be useful to find the projection names.
    when (is_trace_enabled_for `simps.verbose || trace_if_exists) trace!
      "[simps] > Already found projection information for structure {str}:\n        > {to_print}",
    return data
  else do
    when_tracing `simps.verbose trace!
      "[simps] > generating projection information for structure {str}:",
    d_str ← e.get str,
    projs ← e.structure_fields_full str,
    let raw_univs := d_str.univ_params,
    let raw_levels := level.param <$> raw_univs,
    /- Define the raw expressions for the projections, by default as the projections
    (as an expression), but this can be overriden by the user. -/
    raw_exprs ← projs.mmap (λ proj, let raw_expr : expr := expr.const proj raw_levels in do
      custom_proj ← (do
        decl ← e.get (str ++ `simps ++ proj.last),
        let custom_proj := decl.value.instantiate_univ_params $ decl.univ_params.zip raw_levels,
        when_tracing `simps.verbose trace!
          "[simps] > found custom projection for {proj}:\n        > {custom_proj}",
        return custom_proj) <|> return raw_expr,
      is_def_eq custom_proj raw_expr <|>
        -- if the type of the expression is different, we show a different error message, because
        -- that is more likely going to be helpful.
        do {
          custom_proj_type ← infer_type custom_proj,
          raw_expr_type ← infer_type raw_expr,
          b ← succeeds (is_def_eq custom_proj_type raw_expr_type),
          if b then fail!"Invalid custom projection:\n  {custom_proj}
Expression is not definitionally equal to {raw_expr}."
          else fail!"Invalid custom projection:\n  {custom_proj}
Expression has different type than {raw_expr}. Given type:\n  {custom_proj_type}
Expected type:\n  {raw_expr_type}" },
      return custom_proj),
    /- Check for other coercions and type-class arguments to use as projections instead. -/
    (args, _) ← open_pis d_str.type,
    let e_str := (expr.const str raw_levels).mk_app args,
    automatic_projs ← attribute.get_instances `notation_class,
    raw_exprs ← automatic_projs.mfoldl (λ (raw_exprs : list expr) class_nm, (do
      (is_class, proj_nm) ← notation_class_attr.get_param class_nm,
      proj_nm ← proj_nm <|> (e.structure_fields_full class_nm).map list.head,
      /- For this class, find the projection. `raw_expr` is the projection found applied to `args`,
        and `lambda_raw_expr` has the arguments `args` abstracted. -/
      (raw_expr, lambda_raw_expr) ← if is_class then (do
        guard $ args.length = 1,
        let e_inst_type := (expr.const class_nm raw_levels).mk_app args,
        (hyp, e_inst) ← try_for 1000 (mk_conditional_instance e_str e_inst_type),
        raw_expr ← mk_mapp proj_nm [args.head, e_inst],
        clear hyp,
        -- Note: `expr.bind_lambda` doesn't give the correct type
        raw_expr_lambda ← lambdas [hyp] raw_expr,
        return (raw_expr, raw_expr_lambda.lambdas args))
      else (do
        e_inst_type ← to_expr ((expr.const class_nm []).app (pexpr.of_expr e_str)),
        e_inst ← try_for 1000 (mk_instance e_inst_type),
        raw_expr ← mk_mapp proj_nm [e_str, e_inst],
        return (raw_expr, raw_expr.lambdas args)),
      raw_expr_whnf ← whnf raw_expr,
      let relevant_proj := raw_expr_whnf.binding_body.get_app_fn.const_name,
      /- Use this as projection, if the function reduces to a projection, and this projection has
        not been overrriden by the user. -/
      guard (projs.any (= relevant_proj) ∧ ¬ e.contains (str ++ `simps ++ relevant_proj.last)),
      let pos := projs.find_index (= relevant_proj),
      when_tracing `simps.verbose trace!
        "        > using {proj_nm} instead of the default projection {relevant_proj.last}.",
      return $ raw_exprs.update_nth pos lambda_raw_expr) <|> return raw_exprs) raw_exprs,
    proj_names ← e.structure_fields str,
    -- if we find the name in name_changes, change the name
    let proj_names : list name := proj_names.map $
      λ nm, (name_changes.find $ λ p : _ × _, p.1 = nm).elim nm prod.snd,
    let projs := proj_names.zip raw_exprs,
    when_tracing `simps.verbose $ do {
      to_print ← projs.mmap $ λ s, to_string <$> pformat!"Projection {s.1}: {s.2}",
      let to_print := string.join $ to_print.intersperse "\n        > ",
      trace!"[simps] > generated projections for {str}:\n        > {to_print}" },
    simps_str_attr.set str (raw_univs, projs) tt,
    return (raw_univs, projs)

/--
  You can specify custom projections for the `@[simps]` attribute.
  To do this for the projection `my_structure.awesome_projection` by adding a declaration
  `my_structure.simps.awesome_projection` that is definitionally equal to
  `my_structure.awesome_projection` but has the projection in the desired (simp-normal) form.

  You can initialize the projections `@[simps]` uses with `initialize_simps_projections`
  (after declaring any custom projections). This is not necessary, it has the same effect
  if you just add `@[simps]` to a declaration.

  If you do anything to change the default projections, make sure to call either `@[simps]` or
  `initialize_simps_projections` in the same file as the structure declaration. Otherwise, you might
  have a file that imports the structure, but not your custom projections.
-/
library_note "custom simps projection"

/-- Specify simps projections, see Note [custom simps projection].
  You can specify custom names by writing e.g.
  `initialize_simps_projections equiv (to_fun → apply, inv_fun → symm_apply)`.
  Set `trace.simps.verbose` to true to see the generated projections.
  If the projections were already specified before, you can call `initialize_simps_projections`
  again to see the generated projections. -/
@[user_command] meta def initialize_simps_projections_cmd
  (_ : parse $ tk "initialize_simps_projections") : parser unit := do
  env ← get_env,
  ns ← (prod.mk <$> ident <*> (tk "(" >>
    sep_by (tk ",") (prod.mk <$> ident <*> (tk "->" >> ident)) <* tk ")")?)*,
  ns.mmap' $ λ data, do
    nm ← resolve_constant data.1,
    simps_get_raw_projections env nm tt $ data.2.get_or_else []

/--
  Get the projections of a structure used by `@[simps]` applied to the appropriate arguments.
  Returns a list of quadruples
  (projection expression, given projection name, original (full) projection name,
    corresponding right-hand-side),
  one for each projection. The given projection name is the name for the projection used by the user
  used to generate (and parse) projection names. The original projection name is the actual
  projection name in the structure, which is only used to check whether the expression is an
  eta-expansion of some other expression. For example, in the structure

  Example 1: ``simps_get_projection_exprs env `(α × β) `(⟨x, y⟩)`` will give the output
  ```
    [(`(@prod.fst.{u v} α β), `fst, `prod.fst, `(x)),
     (`(@prod.snd.{u v} α β), `snd, `prod.snd, `(y))]
  ```

  Example 2: ``simps_get_projection_exprs env `(α ≃ α) `(⟨id, id, λ _, rfl, λ _, rfl⟩)``
  will give the output
  ```
    [(`(@equiv.to_fun.{u u} α α), `apply, `equiv.to_fun, `(id)),
     (`(@equiv.inv_fun.{u u} α α), `symm_apply, `equiv.inv_fun, `(id)),
     ...,
     ...]
  ```
  The last two fields of the list correspond to the propositional fields of the structure,
  and are rarely/never used.
-/
-- This function does not use `tactic.mk_app` or `tactic.mk_mapp`, because the the given arguments
-- might not uniquely specify the universe levels yet.
meta def simps_get_projection_exprs (e : environment) (tgt : expr)
  (rhs : expr) : tactic $ list $ expr × name × name × expr := do
  let params := get_app_args tgt, -- the parameters of the structure
  (params.zip $ (get_app_args rhs).take params.length).mmap' (λ ⟨a, b⟩, is_def_eq a b)
    <|> fail "unreachable code (1)",
  let str := tgt.get_app_fn.const_name,
  let rhs_args := (get_app_args rhs).drop params.length, -- the fields of the object
  (raw_univs, projs_and_raw_exprs) ← simps_get_raw_projections e str,
  guard (rhs_args.length = projs_and_raw_exprs.length) <|> fail "unreachable code (2)",
  let univs := raw_univs.zip tgt.get_app_fn.univ_levels,
  let projs := projs_and_raw_exprs.map $ prod.fst,
  original_projection_names ← e.structure_fields_full str,
  let raw_exprs := projs_and_raw_exprs.map $ prod.snd,
  let proj_exprs := raw_exprs.map $
    λ raw_expr, (raw_expr.instantiate_univ_params univs).instantiate_lambdas_or_apps params,
  return $ proj_exprs.zip $ projs.zip $ original_projection_names.zip rhs_args

/--
  Configuration options for the `@[simps]` attribute.
  * `attrs` specifies the list of attributes given to the generated lemmas. Default: ``[`simp]``.
    The attributes can be either basic attributes, or user attributes without parameters.
    There are two attributes which `simps` might add itself:
    * If ``[`simp]`` is in the list, then ``[`_refl_lemma]`` is added automatically if appropriate.
    * If the definition is marked with `@[to_additive ...]` then all generated lemmas are marked
      with `@[to_additive]`
  * `short_name` gives the generated lemmas a shorter name. This only has an effect when multiple
    projections are applied in a lemma. When this is `ff` (default) all projection names will be
    appended to the definition name to form the lemma name, and when this is `tt`, only the
    last projection name will be appended.
  * if `simp_rhs` is `tt` then the right-hand-side of the generated lemmas will be put in
    simp-normal form. More precisely: `dsimp, simp` will be called on all these expressions.
    See note [dsimp, simp].
  * `type_md` specifies how aggressively definitions are unfolded in the type of expressions
    for the purposes of finding out whether the type is a function type.
    Default: `instances`. This will unfold coercion instances (so that a coercion to a function type
    is recognized as a function type), but not declarations like `set`.
  * `value_md` specifies how aggressively definitions in the declaration are unfolded.  The value
    of the definition is then reduced to whnf with this transparency setting.
    Default: `none`
  * `rhs_md` specifies how aggressively definition in the declaration are unfolded for the purposes
    of finding out whether it is a constructor.
    Default: `none`
    Exception: `@[simps]` will automatically add the options
    `{rhs_md := semireducible, simp_rhs := tt}` if the given definition is not a constructor with
    the given reducibility setting for `rhs_md`.
  * If `fully_applied` is `ff` then the generated simp-lemmas will be between non-fully applied
    terms, i.e. equalities between functions. This does not restrict the recursive behavior of
    `@[simps]`, so only the "final" projection will be non-fully applied.
    However, it can be used in combination with explicit field names, to get a partially applied
    intermediate projection.
  * The option `not_recursive` contains the list of names of types for which `@[simps]` doesn't
    recursively apply projections. For example, given an equivalence `α × β ≃ β × α` one usually
    wants to only apply the projections for `equiv`, and not also those for `×`. This option is
    only relevant if no explicit projection names are given as argument to `@[simps]`.
-/
@[derive [has_reflect, inhabited]] structure simps_cfg :=
(attrs         := [`simp])
(short_name    := ff)
(simp_rhs      := ff)
(type_md       := transparency.instances)
(value_md      := transparency.none)
(rhs_md        := transparency.none)
(fully_applied := tt)
(not_recursive := [`prod, `pprod])

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
  `args` is the list of local constants occurring, and `univs` is the list of universe variables.
  If `add_simp` then we make the resulting lemma a simp-lemma. -/
meta def simps_add_projection (nm : name) (type lhs rhs : expr) (args : list expr)
  (univs : list name) (cfg : simps_cfg) : tactic unit := do
  when_tracing `simps.debug trace!
    "[simps] > Planning to add the equality\n        > {lhs} = ({rhs} : {type})",
  -- simplify `rhs` if `cfg.simp_rhs` is true
  (rhs, prf) ← do { guard cfg.simp_rhs,
    rhs' ← rhs.dsimp {fail_if_unchanged := ff},
    when_tracing `simps.debug $ when (rhs ≠ rhs') trace!
      "[simps] > `dsimp` simplified rhs to\n        > {rhs'}",
    (rhsprf1, rhsprf2, ns) ← rhs'.simp {fail_if_unchanged := ff},
    when_tracing `simps.debug $ when (rhs' ≠ rhsprf1) trace!
      "[simps] > `simp` simplified rhs to\n        > {rhsprf1}",
    return (prod.mk rhsprf1 rhsprf2) }
    <|> prod.mk rhs <$> mk_app `eq.refl [type, lhs],
  eq_ap ← mk_mapp `eq $ [type, lhs, rhs].map some,
  decl_name ← get_unused_decl_name nm,
  let decl_type := eq_ap.pis args,
  let decl_value := prf.lambdas args,
  let decl := declaration.thm decl_name univs decl_type (pure decl_value),
  when_tracing `simps.verbose trace!
    "[simps] > adding projection {decl_name}:\n        > {decl_type}",
  decorate_error ("failed to add projection lemma " ++ decl_name.to_string ++ ". Nested error:") $
    add_decl decl,
  b ← succeeds $ is_def_eq lhs rhs,
  when (b ∧ `simp ∈ cfg.attrs) (set_basic_attribute `_refl_lemma decl_name tt),
  cfg.attrs.mmap' $ λ nm, set_attribute nm decl_name tt

/-- Derive lemmas specifying the projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`. -/
meta def simps_add_projections : ∀(e : environment) (nm : name) (suffix : string)
  (type lhs rhs : expr) (args : list expr) (univs : list name) (must_be_str : bool)
  (cfg : simps_cfg) (todo : list string), tactic unit
| e nm suffix type lhs rhs args univs must_be_str cfg todo := do
  -- we don't want to unfold non-reducible definitions (like `set`) to apply more arguments
  when_tracing `simps.debug trace!
    "[simps] > Trying to add simp-lemmas for\n        > {lhs}
[simps] > Type of the expression before normalizing: {type}",
  (type_args, tgt) ← open_pis_whnf type cfg.type_md,
  when_tracing `simps.debug trace!
    "[simps] > Type after removing pi's: {tgt}",
  tgt ← whnf tgt,
  when_tracing `simps.debug trace!
    "[simps] > Type after reduction: {tgt}",
  let new_args := args ++ type_args,
  let lhs_ap := lhs.mk_app type_args,
  let rhs_ap := rhs.instantiate_lambdas_or_apps type_args,
  let str := tgt.get_app_fn.const_name,
  let new_nm := nm.append_suffix suffix,
  /- We want to generate the current projection if it is in `todo` -/
  let todo_next := todo.filter (≠ ""),
  /- Don't recursively continue if `str` is not a structure or if the structure is in
    `not_recursive`. -/
  if e.is_structure str ∧ ¬(todo = [] ∧ str ∈ cfg.not_recursive ∧ ¬must_be_str) then do
    [intro] ← return $ e.constructors_of str | fail "unreachable code (3)",
    rhs_whnf ← whnf rhs_ap cfg.rhs_md,
    (rhs_ap, todo_now) ← if h : ¬ is_constant_of rhs_ap.get_app_fn intro ∧
      is_constant_of rhs_whnf.get_app_fn intro then
      /- If this was a desired projection, we want to apply it before taking the whnf.
        However, if the current field is an eta-expansion (see below), we first want
        to eta-reduce it and only then construct the projection.
        This makes the flow of this function hard to follow. -/
      when ("" ∈ todo) (if cfg.fully_applied then
        simps_add_projection new_nm tgt lhs_ap rhs_ap new_args univs cfg else
        simps_add_projection new_nm type lhs rhs args univs cfg) >>
      return (rhs_whnf, ff) else
      return (rhs_ap, "" ∈ todo),
    if is_constant_of (get_app_fn rhs_ap) intro then do -- if the value is a constructor application
      tuples ← simps_get_projection_exprs e tgt rhs_ap,
      let projs := tuples.map $ λ x, x.2.1,
      let pairs := tuples.map $ λ x, x.2.2,
      eta ← rhs_ap.is_eta_expansion_aux pairs, -- check whether `rhs_ap` is an eta-expansion
      let rhs_ap := eta.lhoare rhs_ap, -- eta-reduce `rhs_ap`
      /- As a special case, we want to automatically generate the current projection if `rhs_ap`
        was an eta-expansion. Also, when this was a desired projection, we need to generate the
        current projection if we haven't done it above. -/
      when (todo_now ∨ (todo = [] ∧ eta.is_some)) $
        if cfg.fully_applied then
          simps_add_projection new_nm tgt lhs_ap rhs_ap new_args univs cfg else
          simps_add_projection new_nm type lhs rhs args univs cfg,
      /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
      automatically choose projections -/
      when ¬(todo = [""] ∨ (eta.is_some ∧ todo = [])) $ do
        let todo := todo_next,
        -- check whether all elements in `todo` have a projection as prefix
        guard (todo.all $ λ x, projs.any $ λ proj, ("_" ++ proj.last).is_prefix_of x) <|>
          let x := (todo.find $ λ x, projs.all $ λ proj, ¬ ("_" ++ proj.last).is_prefix_of x).iget,
            simp_lemma := nm.append_suffix $ suffix ++ x,
            needed_proj := (x.split_on '_').tail.head in
          fail!
"Invalid simp-lemma {simp_lemma}. Structure {str} does not have projection {needed_proj}.
The known projections are:
  {projs}
You can also see this information by running
  `initialize_simps_projections {str}`.
Note: the projection names used by @[simps] might not correspond to the projection names in the structure.",
        tuples.mmap' $ λ ⟨proj_expr, proj, _, new_rhs⟩, do
          new_type ← infer_type new_rhs,
          let new_todo := todo.filter_map $ λ x, string.get_rest x $ "_" ++ proj.last,
          b ← is_prop new_type,
          -- we only continue with this field if it is non-propositional or mentioned in todo
          when ((¬ b ∧ todo = []) ∨ new_todo ≠ []) $ do
            let new_lhs := proj_expr.instantiate_lambdas_or_apps [lhs_ap],
            let new_suffix := if cfg.short_name then "_" ++ proj.last else
              suffix ++ "_" ++ proj.last,
            simps_add_projections e nm new_suffix new_type new_lhs new_rhs new_args univs
              ff cfg new_todo
    -- if I'm about to run into an error, try to set the transparency for `rhs_md` higher.
    else if cfg.rhs_md = transparency.none ∧ (must_be_str ∨ todo_next ≠ []) then do
      when_tracing `simps.verbose trace!
        "[simps] > The given definition is not a constructor application:
        >   {rhs_ap}
        > Retrying with the options {{ rhs_md := semireducible, simp_rhs := tt}.",
      simps_add_projections e nm suffix type lhs rhs args univs must_be_str
        { rhs_md := semireducible, simp_rhs := tt, ..cfg} todo
    else do
      when must_be_str $
        fail!"Invalid `simps` attribute. The body is not a constructor application:\n  {rhs_ap}",
      when (todo_next ≠ []) $
        fail!"Invalid simp-lemma {nm.append_suffix $ suffix ++ todo_next.head}.
The given definition is not a constructor application:\n  {rhs_ap}",
      if cfg.fully_applied then
        simps_add_projection new_nm tgt lhs_ap rhs_ap new_args univs cfg else
        simps_add_projection new_nm type lhs rhs args univs cfg
  else do
    when must_be_str $
      fail!"Invalid `simps` attribute. Target {str} is not a structure",
    when (todo_next ≠ [] ∧ str ∉ cfg.not_recursive) $
        fail!"Invalid simp-lemma {nm.append_suffix $ suffix ++ todo_next.head}.
Projection {(todo_next.head.split_on '_').tail.head} doesn't exist, because target is not a structure.",
    if cfg.fully_applied then
      simps_add_projection new_nm tgt lhs_ap rhs_ap new_args univs cfg else
      simps_add_projection new_nm type lhs rhs args univs cfg

/-- `simps_tac` derives simp-lemmas for all (nested) non-Prop projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  If `short_nm` is true, the generated names will only use the last projection name. -/
meta def simps_tac (nm : name) (cfg : simps_cfg := {}) (todo : list string := []) :
  tactic unit :=
do
  e ← get_env,
  d ← e.get nm,
  let lhs : expr := const d.to_name (d.univ_params.map level.param),
  let todo := todo.erase_dup.map $ λ proj, "_" ++ proj,
  b ← has_attribute' `to_additive nm,
  let cfg := if b then { attrs := cfg.attrs ++ [`to_additive], ..cfg } else cfg,
  (xs, val) ← open_lambdas_whnf d.value cfg.value_md,
  value ← whnf val cfg.value_md >>= tactic.lambdas xs,
  simps_add_projections e nm "" d.type lhs value [] d.univ_params tt cfg todo

/-- The parser for the `@[simps]` attribute. -/
meta def simps_parser : parser (list string × simps_cfg) := do
/- note: we don't check whether the user has written a nonsense namespace in an argument. -/
prod.mk <$> many (name.last <$> ident) <*>
  (do some e ← parser.pexpr? | return {}, eval_pexpr simps_cfg e)

/--
The `@[simps]` attribute automatically derives lemmas specifying the projections of this
declaration.

Example:
```lean
@[simps] def foo : ℕ × ℤ := (1, 2)
```
derives two simp-lemmas:
```lean
@[simp] lemma foo_fst : foo.fst = 1
@[simp] lemma foo_snd : foo.snd = 2
```

* It does not derive simp-lemmas for the prop-valued projections.
* It will automatically reduce newly created beta-redexes, but will not unfold any definitions.
* If the structure has a coercion to either sorts or functions, and this is defined to be one
  of the projections, then this coercion will be used instead of the projection.
* If the structure is a class that has an instance to a notation class, like `has_mul`, then this
  notation is used instead of the corresponding projection.
* You can specify custom projections, by giving a declaration with name
  `{structure_name}.simps.{projection_name}`. See Note [custom simps projection].

  Example:
  ```lean
  def equiv.simps.inv_fun (e : α ≃ β) : β → α := e.symm
  @[simps] def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩
  ```
  generates
  ```
  @[simp] lemma equiv.trans_to_fun : ∀ {α β γ} (e₁ e₂) (a : α), ⇑(e₁.trans e₂) a = (⇑e₂ ∘ ⇑e₁) a
  @[simp] lemma equiv.trans_inv_fun : ∀ {α β γ} (e₁ e₂) (a : γ),
    ⇑((e₁.trans e₂).symm) a = (⇑(e₁.symm) ∘ ⇑(e₂.symm)) a
  ```

* You can specify custom projection names, by specifying the new projection names using
  `initialize_simps_projections`.
  Example: `initialize_simps_projections equiv (to_fun → apply, inv_fun → symm_apply)`.

* If one of the fields itself is a structure, this command will recursively create
  simp-lemmas for all fields in that structure.
  * Exception: by default it will not recursively create simp-lemmas for fields in the structures
    `prod` and `pprod`. Give explicit projection names to override this behavior.

  Example:
  ```lean
  structure my_prod (α β : Type*) := (fst : α) (snd : β)
  @[simps] def foo : prod ℕ ℕ × my_prod ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_snd_fst : foo.snd.fst = 3
  @[simp] lemma foo_snd_snd : foo.snd.snd = 4
  ```

* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections.
* Recursive projection names can be specified using `proj1_proj2_proj3`.
  This will create a lemma of the form `foo.proj1.proj2.proj3 = ...`.

  Example:
  ```lean
  structure my_prod (α β : Type*) := (fst : α) (snd : β)
  @[simps fst fst_fst snd] def foo : prod ℕ ℕ × my_prod ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_fst_fst : foo.fst.fst = 1
  @[simp] lemma foo_snd : foo.snd = {fst := 3, snd := 4}
  ```
* If one of the values is an eta-expanded structure, we will eta-reduce this structure.

  Example:
  ```lean
  structure equiv_plus_data (α β) extends α ≃ β := (data : bool)
  @[simps] def bar {α} : equiv_plus_data α α := { data := tt, ..equiv.refl α }
  ```
  generates the following, even though Lean inserts an eta-expanded version of `equiv.refl α` in the
  definition of `bar`:
  ```lean
  @[simp] lemma bar_to_equiv : ∀ {α : Sort u_1}, bar.to_equiv = equiv.refl α
  @[simp] lemma bar_data : ∀ {α : Sort u_1}, bar.data = tt
  ```
* For configuration options, see the doc string of `simps_cfg`.
* The precise syntax is `('simps' ident* e)`, where `e` is an expression of type `simps_cfg`.
* `@[simps]` reduces let-expressions where necessary.
* If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens).
* When option `trace.simps.verbose` is true, `simps` will print the projections it finds and the
  lemmas it generates.
* Use `@[to_additive, simps]` to apply both `to_additive` and `simps` to a definition, making sure
  that `simps` comes after `to_additive`. This will also generate the additive versions of all
  simp-lemmas. Note however, that the additive versions of the simp-lemmas always use the default
  name generated by `to_additive`, even if a custom name is given for the additive version of the
  definition.
  -/

@[user_attribute] meta def simps_attr : user_attribute unit (list string × simps_cfg) :=
{ name := `simps,
  descr := "Automatically derive lemmas specifying the projections of this declaration.",
  parser := simps_parser,
  after_set := some $
    λ n _ persistent, do
      guard persistent <|> fail "`simps` currently cannot be used as a local attribute",
      (todo, cfg) ← simps_attr.get_param n,
      simps_tac n cfg todo }

add_tactic_doc
{ name                     := "simps",
  category                 := doc_category.attr,
  decl_names               := [`simps_attr],
  tags                     := ["simplification"] }
