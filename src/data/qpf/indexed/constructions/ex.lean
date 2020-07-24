#exit
import
  logic.relation

open function relation

open tactic
meta instance : has_to_tactic_format tactic.tag := list.has_to_tactic_format

-- import_private parse_arguments
open name

private meta def parse_arguments : list name → list name × list name
| [] := ⟨[], []⟩
| (mk_string "_arg" n :: ns) :=
  let ⟨args, rest⟩ := parse_arguments ns in
  if n = anonymous then ⟨args, rest⟩
  else ⟨n :: args, rest⟩
| ns := ⟨[], ns⟩

meta def parse : list name → option interactive.case_tag
| [] := none
| (mk_numeral n `_case.pi :: ns) := do
  guard $ ns.all (λ n, ¬ n.is_internal),
  some $ interactive.case_tag.pi ns n.to_nat
| (`_case.hyps :: ns) := do
  let ⟨args, ns⟩ := parse_arguments ns,
  guard $ ns.all (λ n, ¬ n.is_internal),
  some $ interactive.case_tag.hyps ns args
| _ := none


private meta def goals_with_matching_tag (ns : list name) :
  tactic (list (expr × interactive.case_tag) × list (expr × interactive.case_tag)) :=
do gs ← get_goals,
   (gs : list (expr × tag)) ← gs.mmap (λ g, do t ← get_tag g, pure (g, t)),
   pure $ gs.foldr
     (λ ⟨g, t⟩ ⟨exact_matches, suffix_matches⟩,
       match parse t with
       | none := ⟨exact_matches, suffix_matches⟩
       | some t :=
         match interactive.case_tag.match_tag ns t with
         | interactive.case_tag.match_result.exact_match := ⟨⟨g, t⟩ :: exact_matches, suffix_matches⟩
         | interactive.case_tag.match_result.fuzzy_match := ⟨exact_matches, ⟨g, t⟩ :: suffix_matches⟩
         | interactive.case_tag.match_result.no_match := ⟨exact_matches, suffix_matches⟩
         end
       end)
     ([], [])

private meta def goal_with_matching_tag (ns : list name) : tactic (expr × interactive.case_tag) :=
do ⟨exact_matches, suffix_matches⟩ ← goals_with_matching_tag ns,
   match exact_matches, suffix_matches with
   | [] , []  := fail format!
     "Invalid `case`: there is no goal tagged with suffix {ns}."
   | [] , [g] := pure g
   | [] , _   :=
     let tags : list (list name) := suffix_matches.map (λ ⟨_, t⟩, t.case_names.reverse) in
     fail format!
     "Invalid `case`: there is more than one goal tagged with suffix {ns}.\nMatching tags: {tags}"
   | [g], _   := pure g
   | _  , _   := fail format!
     "Invalid `case`: there is more than one goal tagged with tag {ns}."
   end

setup_tactic_parser

@[interactive]
meta def case' (ns : parse ident_*) (ids : parse $ (tk ":" *> ident_*)?) (tac : interactive.itactic) : tactic unit :=
do ⟨goal, tag⟩ ← goal_with_matching_tag ns,
   let ids := ids.get_or_else [],
   let num_ids := ids.length,
   goals ← get_goals,
   set_goals $ goal :: goals.filter (≠ goal),
   match tag with
   | (interactive.case_tag.pi _ num_args) := do
     intro_lst ids,
     when (num_ids < num_args) $ intron (num_args - num_ids)
   | (interactive.case_tag.hyps _ new_hyp_names) := do
       let num_new_hyps := new_hyp_names.length,
       when (num_ids > num_new_hyps) $ fail format!
         "Invalid `case`: You gave {num_ids} names, but the case introduces
         {num_new_hyps} new hypotheses.",
       let renamings := native.rb_map.of_list (new_hyp_names.zip ids),
       interactive.propagate_tags $ tactic.rename_many renamings tt tt
   end,
   solve1 tac


def foo
  {α : Type}
  {r : α × α → Prop}
  {x : α × α}
  (h : uncurry (trans_gen (curry r)) x) :
  true :=
begin
  cases h,
  case' relation.trans_gen.tail : a b c { admit }
end





def foo
  {α : Type}
  {r : α × α → Prop}
  {x : α × α}
  (h : uncurry (trans_gen (curry r)) x) :
  true :=
begin
  -- cases x,
  -- cases h,
  -- (do
  --   [_, g] ← get_goals,
  --   t ← get_tag g,
  --   trace t,
  --   -- [_case.hyps, 0._fresh.2815.6053._arg, _arg, 0._fresh.2815.6055._arg, 0._fresh.2815.6093._arg, relation.trans_gen.tail]
  --   trace "",
  --   trace (parse_arguments $ list.tail t),
  --   trace "",
  --   trace (interactive.case_tag.parse t)
  --   -- (some (hyps [relation.trans_gen.tail] [0._fresh.2815.6053, [anonymous], 0._fresh.2815.6055, 0._fresh.2815.6093]))
  --   ),

(do
    e ← i_to_expr ```(h),
    rs ← tactic.cases e [],
    trace rs),

end
