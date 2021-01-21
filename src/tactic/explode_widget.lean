/-
Copyright (c) 2020 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Minchao Wu
-/
import tactic.explode
/-!
# `#explode_widget` command

Render a widget that displays an `#explode` proof, providing more 
interactivity such as jumping to definitions and exploding constants 
occurring in the exploded proofs.
-/
open widget tactic tactic.explode

namespace tactic
namespace explode_widget
open widget_override.interactive_expression 
open tagged_format
open widget.html widget.attr

/-- Redefine some of the style attributes for better formatting. -/
meta def get_block_attrs {γ}: sf → tactic (sf × list (attr γ))
| (sf.block i a) := do
  let s : attr (γ) := style [
    ("display", "inline-block"),
    ("white-space", "pre-wrap"),
    ("vertical-align", "top")
  ],
  (a,rest) ← get_block_attrs a,
  pure (a, s :: rest)
| (sf.highlight c a) := do
  (a, rest) ← get_block_attrs a,
  pure (a, (cn c.to_string) :: rest)
| a := pure (a,[])

/-- Explode button for subsequent exploding. -/
meta def insert_explode {γ} : expr → tactic (list (html (action γ)))
| (expr.const n _) := (do 
    pure $ [h "button" [
      cn "pointer ba br3 mr1",
      on_click (λ _, action.effect $ widget.effect.insert_text ("#explode_widget " ++ n.to_string)),
      attr.val "title" "explode"] ["💥"]]
  ) <|> pure []
| e := pure []

/--
Render a subexpression as a list of html elements.
-/
meta def view {γ} (tooltip_component : tc subexpr (action γ)) 
  (click_address : option expr.address) 
  (select_address : option expr.address) :
  subexpr → sf → tactic (list (html (action γ)))
| ⟨ce, current_address⟩ (sf.tag_expr ea e m) := do
  let new_address := current_address ++ ea,
  let select_attrs : list (attr (action γ)) := 
    if some new_address = select_address then 
       [className "highlight"] else [],
  click_attrs  : list (attr (action γ)) ←
    if some new_address = click_address then do
      content ← tc.to_html tooltip_component (e, new_address),
      efmt : string ← format.to_string <$> tactic.pp e,
      gd_btn ← goto_def_button e,
      epld_btn ← insert_explode e,
      pure [tooltip $ h "div" [] [
          h "div" [cn "fr"] (gd_btn ++ epld_btn ++ [
            h "button" [cn "pointer ba br3 mr1", on_click 
                       (λ _, action.effect $ widget.effect.copy_text efmt), 
                       attr.val "title" "copy expression to clipboard"] ["📋"],
            h "button" [cn "pointer ba br3", on_click 
                       (λ _, action.on_close_tooltip), 
                       attr.val "title" "close"] ["×"]
          ]),
          content
      ]]
    else pure [],
  (m, block_attrs) ← get_block_attrs m,
  let as := [className "expr-boundary", key (ea)] ++ select_attrs ++ 
            click_attrs ++ block_attrs,
  inner ← view (e,new_address) m,
  pure [h "span" as inner]
| ca (sf.compose x y) := pure (++) <*> view ca x <*> view ca y
| ca (sf.of_string s) := pure
  [h "span" [
    on_mouse_enter (λ _, action.on_mouse_enter ca),
    on_click (λ _, action.on_click ca),
    key s
  ] [html.of_string s]]
| ca b@(sf.block _ _) := do
  (a, attrs) ← get_block_attrs b,
  inner ← view ca a,
  pure [h "span" attrs inner]
| ca b@(sf.highlight _ _) := do
  (a, attrs) ← get_block_attrs b,
  inner ← view ca a,
  pure [h "span" attrs inner]

/-- Make an interactive expression. -/
meta def mk {γ} (tooltip : tc subexpr γ) : tc expr γ :=
let tooltip_comp :=
   component.with_should_update 
   (λ (x y : tactic_state × expr × expr.address), x.2.2 ≠ y.2.2)
   $ component.map_action (action.on_tooltip_action) tooltip in
   component.filter_map_action
   (λ _ (a : γ ⊕ widget.effect), sum.cases_on a some (λ _, none))
$ component.with_effects (λ _ (a : γ ⊕ widget.effect),
  match a with
  | (sum.inl g) := []
  | (sum.inr s) := [s]
  end
)
$ tc.mk_simple
  (action γ)
  (option subexpr × option subexpr)
  (λ e, pure $ (none, none))
  (λ e ⟨ca, sa⟩ act, pure $
    match act with
    | (action.on_mouse_enter ⟨e, ea⟩) := ((ca, some (e, ea)), none)
    | (action.on_mouse_leave_all)     := ((ca, none), none)
    | (action.on_click ⟨e, ea⟩)       := if some (e,ea) = ca then 
                                         ((none, sa), none) else 
                                         ((some (e, ea), sa), none)
    | (action.on_tooltip_action g)    := ((none, sa), some $ sum.inl g)
    | (action.on_close_tooltip)       := ((none, sa), none)
    | (action.effect e)               := ((ca,sa), some $ sum.inr $ e)
    end
  )
  (λ e ⟨ca, sa⟩, do
    m ← sf.of_eformat <$> tactic.pp_tagged e,
    let m := m.elim_part_apps,
    let m := m.flatten,
    let m := m.tag_expr [] e,
    v ← view tooltip_comp (prod.snd <$> ca) (prod.snd <$> sa) ⟨e, []⟩ m,
    pure $
    [ h "span" [
          className "expr",
          key e.hash,
          on_mouse_leave (λ _, action.on_mouse_leave_all) ] $ v
      ]
  )

/-- Render the implicit arguments for an expression in fancy, little pills. -/
meta def implicit_arg_list (tooltip : tc subexpr empty) (e : expr) : tactic $ html empty := do
  fn ← (mk tooltip) $ expr.get_app_fn e,
  args ← list.mmap (mk tooltip) $ expr.get_app_args e,
  pure $ h "div" []
    ( (h "span" [className "bg-blue br3 ma1 ph2 white"] [fn]) ::
      list.map (λ a, h "span" [className "bg-gray br3 ma1 ph2 white"] [a]) args
    )

/--
Component for the type tooltip.
-/
meta def type_tooltip : tc subexpr empty :=
tc.stateless (λ ⟨e,ea⟩, do
    y ← tactic.infer_type e,
    y_comp ← mk type_tooltip y,
    implicit_args ← implicit_arg_list type_tooltip e,
    pure [h "div" [style [("minWidth", "12rem")]] [
          h "div" [cn "pl1"] [y_comp],
          h "hr" [] [],
          implicit_args
        ]
      ]
  )

/--
Component that shows a type.
-/
meta def show_type_component : tc expr empty :=
tc.stateless (λ x, do
  y ← infer_type x,
  y_comp ← mk type_tooltip $ y,
  pure y_comp
)

/--
Component that shows a constant.
-/
meta def show_constant_component : tc expr empty :=
tc.stateless (λ x, do
  y_comp ← mk type_tooltip x,
  pure y_comp
)

/--
Search for an entry that has the specified line number.
-/
meta def lookup_lines : entries → nat → entry
| ⟨_, []⟩ n := ⟨default _, 0, 0, status.sintro, thm.string "", []⟩
| ⟨rb, (hd::tl)⟩ n := if hd.line = n then hd else lookup_lines ⟨rb, tl⟩ n

/--
Render a row that shows a goal.
-/
meta def goal_row (e : expr) (show_expr := tt): tactic (list (html empty)) := 
do t ← explode_widget.show_type_component e,
return $ [h "td" [cn "ba bg-dark-green tc"] "Goal", 
          h "td" [cn "ba tc"] 
          (if show_expr then [html.of_name e.local_pp_name, " : ", t] else t)]

/--
Render a row that shows the ID of a goal.
-/
meta def id_row {γ} (l : nat): tactic (list (html γ)) := 
return $ [h "td" [cn "ba bg-dark-green tc"] "ID", 
          h "td" [cn "ba tc"] (to_string l)]

/--
Render a row that shows the rule or theorem being applied.
-/
meta def rule_row : thm →  tactic (list (html empty))
| (thm.expr e) := do t ← explode_widget.show_constant_component e,
                     return $ [h "td" [cn "ba bg-dark-green tc"] "Rule", 
                               h "td" [cn "ba tc"] t]
| t := return $ [h "td" [cn "ba bg-dark-green tc"] "Rule", 
                 h "td" [cn "ba tc"] t.to_string]

/--
Render a row that contains the sub-proofs, i.e., the proofs of the
arguments.
-/
meta def proof_row {γ} (args : list (html γ)): list (html γ) := 
[h "td" [cn "ba bg-dark-green tc"] "Proofs", h "td" [cn "ba tc"] 
    [h "details" [] $
        (h "summary" 
            [attr.style [("color", "orange")]] 
                "Details")::args]
]

/--
Combine the goal row, id row, rule row and proof row to make them a table.
-/
meta def assemble_table {γ} (gr ir rr) : list (html γ) → html γ
| [] := 
h "table" [cn "collapse"] 
    [h "tbody" []
        [h "tr" [] gr, h "tr" [] ir, h "tr" [] rr]
    ]
| pr := 
h "table" [cn "collapse"] 
    [h "tbody" []
        [h "tr" [] gr, h "tr" [] ir, h "tr" [] rr, h "tr" [] pr]
    ]

/--
Render a table for a given entry.
-/
meta def assemble (es : entries): entry → tactic (html empty)
| ⟨e, l, d, status.sintro, t, ref⟩ := do
    gr ← goal_row e, ir ← id_row l, rr ← rule_row $ thm.string "Assumption",
    return $ assemble_table gr ir rr []
| ⟨e, l, d, status.intro, t, ref⟩ := do
    gr ← goal_row e, ir ← id_row l, rr ← rule_row $ thm.string  "Assumption",
    return $ assemble_table gr ir rr []
| ⟨e, l, d, st, t, ref⟩ := do 
    gr ← goal_row e ff, ir ← id_row l, rr ← rule_row t,
    let el : list entry := list.map (lookup_lines es) ref, 
    ls ← monad.mapm assemble el,
    let pr := proof_row $ ls.intersperse (h "br" [] []),
    return $ assemble_table gr ir rr pr

/--
Render a widget from given entries.
-/
meta def explode_component (es : entries) : tactic (html empty) := 
let concl := lookup_lines es (es.l.length - 1) in assemble es concl

/--
Explode a theorem and return entries.
-/
meta def explode_entries (n : name) (hide_non_prop := tt) : tactic entries :=
do expr.const n _ ← resolve_name n | fail "cannot resolve name",
  d ← get_decl n,
  v ← match d with
  | (declaration.defn _ _ _ v _ _) := return v
  | (declaration.thm _ _ _ v)      := return v.get
  | _                  := fail "not a definition"
  end,
  t ← pp d.type,
  explode_expr v hide_non_prop

end explode_widget

open lean lean.parser interactive explode_widget

/--
User command of the explode widget.
-/
@[user_command]
meta def explode_widget_cmd (_ : parse $ tk "#explode_widget") : lean.parser unit :=
do ⟨li,co⟩ ← cur_pos,
    n ← ident,
    es ← explode_entries n,
    comp ← parser.of_tactic (do html ← explode_component es,
    c ← pure $ component.stateless (λ _, [html]),
    pure $ component.ignore_props $ component.ignore_action $ c),
    save_widget ⟨li, co - "#explode_widget".length - 1⟩ comp,
    trace "successfully rendered widget",
    skip
    .

end tactic
