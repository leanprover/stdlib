
/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import data.pfun
import data.list.sort
import data.lazy_list2

universes u v w

lemma eq_mp_heq :
  ∀ {α β : Sort*} {a : α} {a' : β} (h₂ : a == a'), (eq.mp (type_eq_of_heq h₂) a) = a'
| α ._ a a' heq.rfl := rfl

namespace sigma
variables {α₁ α₂ α₃ : Type u}
variables {β₁ : α₁ → Type v} {β₂ : α₂ → Type v} {β₃ : α₃ → Type v}
variables {g : sigma β₂ → sigma β₃} {f : sigma β₁ → sigma β₂}

theorem eq_fst {s₁ s₂ : sigma β₁} : s₁ = s₂ → s₁.1 = s₂.1 :=
by cases s₁; cases s₂; cc

theorem eq_snd {s₁ s₂ : sigma β₁} : s₁ = s₂ → s₁.2 == s₂.2 :=
by cases s₁; cases s₂; cc

@[ext]
lemma ext {x₀ x₁ : sigma β₁}
  (h₀ : x₀.1 = x₁.1)
  (h₁ : x₀.1 = x₁.1 → x₀.2 == x₁.2) :
  x₀ = x₁ :=
by casesm* sigma _; cases h₀; cases h₁ h₀; refl

end sigma

namespace list

variables {m : Type u → Type v} [applicative m]

-- def mmap_enum_if' {α} (p : α → Prop) [decidable_pred p] (f : ℕ → α → m α) : ℕ → list α → m (list α)
-- | n [] := pure []
-- | n (x :: xs) :=
--   if p x then (::) <$> f n x <*> mmap_enum_if' (n+1) xs
--          else cons x <$> mmap_enum_if' n xs

-- def mmap_enum_if {α} (p : α → Prop) [decidable_pred p] (f : ℕ → α → m α) : list α → m (list α) :=
-- mmap_enum_if' p f 0
open nat
def mrepeat {α} : ℕ → m α → m (list α)
| 0        cmd := pure []
| (succ n) cmd := (::) <$> cmd <*> mrepeat n cmd

open function

end list
namespace roption
variables {α : Type*} {β : Type*} {γ : Type*}

open function
lemma assert_if_neg {p : Prop}
  (x : p → roption α)
  (h : ¬ p)
: assert p x = roption.none :=
by { dsimp [assert,roption.none],
     have : (∃ (h : p), (x h).dom) ↔ false,
     { split ; intros h' ; repeat { cases h' with h' },
       exact h h' },
     congr,
     repeat { rw this <|> apply hfunext },
     intros h h', cases h', }

lemma assert_if_pos {p : Prop}
  (x : p → roption α)
  (h : p)
: assert p x = x h :=
by { dsimp [assert],
     have : (∃ (h : p), (x h).dom) ↔ (x h).dom,
     { split ; intros h'
       ; cases h' <|> split
       ; assumption, },
     cases hx : x h, congr, rw [this,hx],
     apply hfunext, rw [this,hx],
     intros, simp [hx] }

@[simp]
lemma roption.none_bind {α β : Type*} (f : α → roption β)
: roption.none >>= f = roption.none :=
by simp [roption.none,has_bind.bind,roption.bind,assert_if_neg]

end roption

namespace monad

@[simp]
lemma bind_pure_star {m} [monad m] [is_lawful_monad m] (x : m punit) :
  x >>= (λ (_x : punit), pure punit.star : punit → m punit) = x :=
by { transitivity,
     { apply congr_arg, ext z, cases z, refl },
     { simp } }

variables {α β γ : Type u}
variables {m : Type u → Type v} [monad m]

@[reducible]
def pipe (a : α → m β) (b : β → m γ) : α → m γ :=
λ x, a x >>= b

infixr ` >=> `:55 := pipe

@[functor_norm]
lemma map_bind_eq_bind_comp {α β γ} {m} [monad m] [is_lawful_monad m]
  (f : α → β) (cmd : m α) (g : β → m γ) :
  (f <$> cmd) >>= g = cmd >>= g ∘ f :=
by rw [← bind_pure_comp_eq_map,bind_assoc,(∘)]; simp

@[functor_norm]
lemma bind_map {α β γ} {m} [monad m] [is_lawful_monad m]
  (f : α → γ → β) (cmd : m α) (g : α → m γ) :
  cmd >>= (λ x, f x <$> g x) = do { x ← cmd, y ← g x, pure $ f x y }  :=
by congr; ext; rw [← bind_pure (g x),map_bind]; simp

@[functor_norm]
lemma bind_seq {α β γ : Type u} {m} [monad m] [is_lawful_monad m]
  (f : α → m (γ → β)) (cmd : m α) (g : α → m γ) :
  cmd >>= (λ x, f x <*> g x) = do { x ← cmd, h ← f x, y ← g x, pure $ h y }  :=
by congr; ext; simp [seq_eq_bind_map] with functor_norm

end monad

attribute [functor_norm] bind_assoc has_bind.and_then map_bind seq_left_eq seq_right_eq

namespace sum

variables {e : Type v} {α β : Type u}

protected def seq : Π (x : sum e (α → β)) (f : sum e α), sum e β
| (sum.inl e) _ := sum.inl e
| (sum.inr f) x := f <$> x

instance : applicative (sum e) :=
{ seq := @sum.seq e,
  pure := @sum.inr e }

instance : is_lawful_applicative (sum e) :=
by constructor; intros;
   casesm* _ ⊕ _; simp [(<*>),sum.seq,pure,(<$>)];
   refl

end sum

namespace functor
def foldl (α : Type u) (β : Type v) := α → α
def foldr (α : Type u) (β : Type v) := α → α

instance foldr.applicative {α} : applicative (foldr α) :=
{ pure := λ _ _, id,
  seq := λ _ _ f x, f ∘ x }

instance foldl.applicative {α} : applicative (foldl α) :=
{ pure := λ _ _, id,
  seq := λ _ _ f x, x ∘ f }

instance foldr.is_lawful_applicative {α} : is_lawful_applicative (foldr α) :=
by refine { .. }; intros; refl

instance foldl.is_lawful_applicative {α} : is_lawful_applicative (foldl α) :=
by refine { .. }; intros; refl

def foldr.eval {α β} (x : foldr α β) : α → α := x

def foldl.eval {α β} (x : foldl α β) : α → α := x

def foldr.mk {α β} (x : α → α) : foldr α β := x

def foldl.mk {α β} (x : α → α) : foldl α β := x

def foldl.cons {α β} (x : α) : foldl (list α) β :=
list.cons x

def foldr.cons {α β} (x : α) : foldr (list α) β :=
list.cons x

def foldl.cons' {α} (x : α) : foldl (list α) punit :=
list.cons x

def foldl.lift {α} (x : α → α) : foldl α punit := x
def foldr.lift {α} (x : α → α) : foldr α punit := x

end functor

instance {α : Type u} : traversable (prod.{u u} α) :=
{ map := λ β γ f (x : α × β), prod.mk x.1 $ f x.2,
  traverse := λ m _ β γ f (x : α × β), by exactI prod.mk x.1 <$> f x.2 }

-- namespace traversable

-- variables {t : Type u → Type u} [traversable t]

-- -- def to_list {α} (x : t α) : list α :=
-- -- @functor.foldr.eval _ (t punit) (traverse functor.foldr.cons x) []

-- end traversable


namespace name

-- def append_suffix : name → string → name
-- | (mk_string s n) s' := mk_string (s ++ s') n
-- | n _ := n

def bundle : name → name → name
| (mk_string s n) (mk_string s' _) := mk_string (s ++ "_" ++ s') n
| n _ := n

end name

namespace native
namespace rb_map

-- #check rb_map

variables {key : Type} {val val' : Type}

-- section

variables [has_lt key] [decidable_rel ((<) : key → key → Prop)]
variables (f : val → val → val)

-- def intersect' : list (key × val) → list (key × val) → list (key × val)
-- | [] m := []
-- | ((k,x)::xs) [] := []
-- | ((k,x)::xs) ((k',x')::xs') :=
-- if h : k < k' then intersect' xs ((k',x')::xs')
-- else if k' < k then intersect' ((k,x)::xs) xs'
-- else (k,f x x') :: intersect' xs xs'

open function (on_fun)
def sort {α : Type} (f : α → key) : list α → list α := list.merge_sort (on_fun (<) f)

-- end

-- meta def filter_map (f : key → val → option val') (x : rb_map key val) : rb_map key val' :=
-- fold x (mk _ _) $ λa b m', (insert m' a <$> f a b).get_or_else m'

-- meta def intersect_with (m m' : rb_map key val) : rb_map key val :=
-- m.filter_map $ λ k x, f x <$> m'.find k

-- meta def intersect (x y : rb_map key val) : rb_map key val :=
-- intersect_with (function.const val) x y

-- meta def difference (m m' : rb_map key val) : rb_map key val :=
-- m.filter_map (λ k x, guard (¬ m'.contains k) >> pure x)

end rb_map
end native

namespace string

open nat

def pop (s : string) : string :=
(s.mk_iterator.next).next_to_string

lemma nextn_next (it : iterator) (n : ℕ) : iterator.nextn it.next n = iterator.next (iterator.nextn it n) :=
by induction n generalizing it; simp [iterator.nextn,*]

lemma nextn_succ (it : iterator) (n : ℕ) : iterator.nextn it (succ n) = iterator.next (iterator.nextn it n) :=
by simp [iterator.nextn, nextn_next]

lemma popn_zero (s : string) : popn s 0 = s :=
by simp [popn, iterator.nextn]

lemma length_pop (s : string) : length (pop s) = length s - 1 :=
by simp [pop]

lemma to_string_next (it : iterator) : (iterator.next it).next_to_string = it.next_to_string.pop :=
by { cases it; cases it_snd; refl, }

lemma popn_succ' (n : ℕ) (s : string) : popn s (succ n) = pop (popn s n) :=
by simp [popn, nextn_succ, to_string_next]

@[simp]
lemma next_to_string_nextn (it : iterator) (n : ℕ) : (iterator.nextn it n).next_to_string = it.next_to_string.popn n :=
begin
  induction n generalizing it, simp [iterator.nextn, popn],
  rw [popn_succ', nextn_succ, to_string_next, n_ih, popn]
end

@[simp]
lemma length_popn (s : string) (n : ℕ) : (s.popn n).length = s.length - n :=
begin
  induction n generalizing s, rw [popn_zero,nat.sub_zero],
  rw [popn_succ',length_pop,n_ih,sub_succ _ n_n,sub_one],
end

private def split_with_core (sep : string) (h' : 0 < sep.length) : iterator → iterator → list string
| start stop :=
if h : stop.has_next then
  -- wf hint
  have stop.next_to_string.length - 1 < stop.next_to_string.length,
    from nat.sub_lt (iterator.zero_lt_length_next_to_string_of_has_next h) dec_trivial,
  have stop.next_to_string.length - sep.length < stop.next_to_string.length,
    from nat.sub_lt (iterator.zero_lt_length_next_to_string_of_has_next h) h',
  if sep.is_prefix_of stop.next_to_string then
    let rest := stop.next.next_to_string,
        stop' := stop.nextn sep.length in
    (start.extract stop).get_or_else "" :: split_with_core stop' stop'
  else
    split_with_core start stop.next
else
  [start.next_to_string]
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ e, e.2.next_to_string.length)⟩] }

def split_with (sep s : string) : list string :=
if h : 0 < sep.length
  then split_with_core sep h (mk_iterator s) (mk_iterator s)
  else s.to_list.map string.singleton

private def replace_core (sep t : string) (h' : 0 < sep.length) : iterator → iterator → string → string
| start stop s :=
if h : stop.has_next then
  have stop.next_to_string.length - 1 < stop.next_to_string.length,
    from nat.sub_lt (iterator.zero_lt_length_next_to_string_of_has_next h) dec_trivial,
  have stop.next_to_string.length - sep.length < stop.next_to_string.length,
    from nat.sub_lt (iterator.zero_lt_length_next_to_string_of_has_next h) h',
  if sep.is_prefix_of stop.next_to_string then
    let rest := stop.next.next_to_string,
        stop' := stop.nextn sep.length,
        pre := (start.extract stop).get_or_else "" in
    replace_core stop' stop' (s ++ pre ++ t)
  else
    replace_core start stop.next s
else
  s ++ start.next_to_string
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ e, e.2.1.next_to_string.length)⟩] }

def replace (s sep t : string) : string :=
if h : 0 < sep.length
  then replace_core sep t h (mk_iterator s) (mk_iterator s) ""
  else string.intercalate t (s.to_list.map string.singleton)

end string

namespace expr

meta def is_local_constant' {elab} : expr elab → bool
| (expr.local_const _ _ _ _) := tt
| _ := ff

meta def replace_all (e : expr) (p : expr → Prop) [decidable_pred p] (r : expr) : expr :=
e.replace $ λ e i, guard (p e) >> pure (r.lift_vars 0 i)

meta def const_params : expr → list level
| (const _ ls) := ls
| _ := []

meta def collect_meta_univ (e : expr) : list name :=
native.rb_set.to_list $ e.fold native.mk_rb_set $ λ e' i s,
match e' with
| (sort u) := u.fold_mvar (flip native.rb_set.insert) s
| (const _ ls) := ls.foldl (λ s' l, l.fold_mvar (flip native.rb_set.insert) s') s
| _ := s
end

meta def list_univ (e : expr) : list level :=
e.fold [] $ λ e' i s,
match e' with
| (sort u) := s.insert u
| (const _ ls) := s ∪ ls
| _ := s
end

-- meta def replace_aux {elab} (f : expr elab → ℕ → option (expr elab)) : expr elab → ℕ → option (expr elab)
-- | e@(var a) i := f e i
-- | e@(sort a) i := f e i
-- | e@(const a a_1) i := f e i
-- | e@(mvar unique pretty type) i := f e i
-- | e@(local_const unique pretty bi type) i x := fold_aux type i (f e i x)
-- | e@(app fn arg) i x := fold_aux arg i $ fold_aux fn i (f e i x)
-- | e@(lam var_name bi var_type body) i x := fold_aux body (i+1) $ fold_aux var_type i (f e i x)
-- | e@(pi var_name bi var_type body) i x := fold_aux body (i+1) $ fold_aux var_type i (f e i x)
-- | e@(elet var_name type assignment body) i x := fold_aux body (i+1) $ fold_aux assignment i $ fold_aux type i (f e i x)
-- | e@(macro a xs) i x := xs.foldl (λ acc x, fold_aux x i acc) (f e i x)

-- meta def fold_aux {α elab} (f : expr elab → ℕ → α → α) : expr elab → ℕ → α → α
-- | e@(var a) i x := f e i x
-- | e@(sort a) i x := f e i x
-- | e@(const a a_1) i x := f e i x
-- | e@(mvar unique pretty type) i x := fold_aux type i $ f e i x
-- | e@(local_const unique pretty bi type) i x := fold_aux type i (f e i x)
-- | e@(app fn arg) i x := fold_aux arg i $ fold_aux fn i (f e i x)
-- | e@(lam var_name bi var_type body) i x := fold_aux body (i+1) $ fold_aux var_type i (f e i x)
-- | e@(pi var_name bi var_type body) i x := fold_aux body (i+1) $ fold_aux var_type i (f e i x)
-- | e@(elet var_name type assignment body) i x := fold_aux body (i+1) $ fold_aux assignment i $ fold_aux type i (f e i x)
-- | e@(macro a xs) i x := xs.foldl (λ acc x, fold_aux x i acc) (f e i x)

-- meta def fold' {α elab} (f : expr elab → ℕ → α → α) (e : expr elab) : α → α :=
-- fold_aux f e 0

end expr

namespace tactic

meta def instantiate_unify_pi : expr → list expr → tactic expr
| (expr.pi n bi d b) (e::es) :=
  do infer_type e >>= unify d,
     instantiate_unify_pi (b.instantiate_var e) es
| e _ := pure e

meta def unify_univ (u u' : level) : tactic unit :=
unify (expr.sort u) (expr.sort u')

meta def trace_expr (e : expr) : tactic expr :=
do t ← infer_type e >>= pp,
   e' ← pp e,
   trace format!"{e'} : {t}",
   pure e

open declaration (defn)
meta def trace_def (n : name) : tactic unit :=
do (defn n _ t df _ _) ← get_decl n,
   t ← pp t, df ← pp df,
   trace format!"\ndef {n} : {t} :=\n{df}\n"

meta def is_type (e : expr) : tactic bool :=
do (expr.sort _) ← infer_type e | pure ff,
   pure tt

meta def list_macros : expr → list (name × list expr) | e :=
e.fold [] (λ m i s,
  match m with
  | (expr.macro m args) := (expr.macro_def_name m, args) :: s
  | _ := s end)

meta def expand_untrusted (tac : tactic unit) : tactic unit :=
do tgt ← target,
   mv  ← mk_meta_var tgt,
   gs ← get_goals,
   set_goals [mv],
   tac,
   env ← get_env,
   pr ← env.unfold_untrusted_macros <$> instantiate_mvars mv,
   set_goals gs,
   exact pr

-- meta def is_recursive_type (n : name) : tactic bool :=
-- do e ← get_env,
--    let cs := e.constructors_of n,
--    rs ← cs.mmap (rec_args_count n),
--    pure $ rs.any (λ r, r > 0)

meta def extract_def' {α} (n : name) (trusted : bool) (elab_def : tactic α) : tactic α :=
do cxt ← list.map expr.to_implicit_binder <$> local_context,
   t ← target,
   (r,d) ← solve_aux t elab_def,
   d ← instantiate_mvars d,
   t' ← pis cxt t,
   d' ← lambdas cxt d,
   let univ := t'.collect_univ_params,
   add_decl $ declaration.defn n univ t' d' (reducibility_hints.regular 1 tt) trusted,
   r <$ (applyc n; assumption)

open expr list nat

meta def remove_intl_const : expr → tactic expr
| v@(local_const uniq pp bi _) :=
  do t ← infer_type v,
     pure $ local_const uniq pp bi t
| e := pure e

instance name.has_repr : has_repr name :=
{ repr := λ x, "`" ++ x.to_string }

private meta def report_invalid_simp_lemma {α : Type} (n : name): tactic α :=
fail format!"invalid simplification lemma '{n}' (use command 'set_option trace.simp_lemmas true' for more details)"

private meta def check_no_overload (p : pexpr) : tactic unit :=
when p.is_choice_macro $
  match p with
  | macro _ ps :=
    fail $ to_fmt "ambiguous overload, possible interpretations" ++
           format.join (ps.map (λ p, (to_fmt p).indent 4))
  | _ := failed
  end

private meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

-- private meta def simp_lemmas.resolve_and_add (s : simp_lemmas) (u : list name) (n : name) (ref : pexpr) : tactic (simp_lemmas × list name) :=
-- do
--   p ← resolve_name n,
--   check_no_overload p,
--   -- unpack local refs
--   let e := p.erase_annotations.get_app_fn.erase_annotations,
--   match e with
--   | const n _           :=
--     (do b ← is_valid_simp_lemma_cnst n, guard b, save_const_type_info n ref, s ← s.add_simp n, return (s, u))
--     <|>
--     (do eqns ← get_eqn_lemmas_for tt tt n, guard (eqns.length > 0), save_const_type_info n ref, s ← add_simps s eqns, return (s, u))
--     <|>
--     (do env ← get_env, guard (env.is_projection n).is_some, return (s, n::u))
--     <|>
--     report_invalid_simp_lemma n
--   | _ :=
--     (do e ← i_to_expr_no_subgoals p, b ← is_valid_simp_lemma e, guard b, try (save_type_info e ref), s ← s.add e, return (s, u))
--     <|>
--     report_invalid_simp_lemma n
--   end

-- meta def simp_lemmas.add_pexpr (s : simp_lemmas) (u : list name) (p : pexpr) : tactic (simp_lemmas × list name) :=
-- match p with
-- | (const c [])          := simp_lemmas.resolve_and_add s u c p
-- | (local_const c _ _ _) := simp_lemmas.resolve_and_add s u c p
-- | _                     := do new_e ← i_to_expr_no_subgoals p, s ← s.add new_e, return (s, u)
-- end

-- meta def simp_lemmas.append_pexprs : simp_lemmas → list name → list pexpr → tactic (simp_lemmas × list name)
-- | s u []      := return (s, u)
-- | s u (l::ls) := do (s, u) ← simp_lemmas.add_pexpr s u l, simp_lemmas.append_pexprs s u ls


meta def generalize_with (h x : name) (e : expr) : tactic unit :=
do t ← infer_type e,
   v ← mk_local_def x t,
   h ← mk_app `eq [e,v] >>= mk_local_def h,
   tgt ← target,
   (tgt',_) ← solve_aux tgt $ do
   { generalize e,
     pi _ _ _ e' ← target,
     pure $ e'.instantiate_var v } <|> pure tgt,
   tgt' ← pis [v,h] tgt',
   new_goal ← mk_meta_var tgt',
   heq ← mk_eq_refl e,
   exact $ new_goal e heq,
   gs ← get_goals, set_goals $ new_goal :: gs

meta def solve_sync (vs : list $ list expr) (p : expr) (tac : tactic unit) : tactic (task expr) :=
do pr ← prod.snd <$> solve_aux p tac >>= instantiate_mvars,
   return <$> vs.reverse.mfoldl (flip lambdas) pr

meta def mk_mvar_pis : expr → tactic (list expr)
| (pi n bi d b) :=
do v ← mk_meta_var d,
   cons v <$> mk_mvar_pis (b.instantiate_var v)
| _ := pure []

open interactive.types interactive lean.parser

@[user_command]
meta def test_signature_cmd (_ : parse $ tk "#test") : lean.parser unit :=
do e ← ident,
show tactic unit, from
do d ← get_decl e,
   let e := @const tt d.to_name d.univ_levels,
   t ← infer_type e >>= pp,
   e.collect_meta_univ.enum.mmap' $ λ ⟨i,v⟩, unify_univ (level.mvar v) (level.param ("u_" ++ to_string i : string)),
   e ← instantiate_mvars e,
   e ← pp e,
   trace format!"\nexample : {t} :=\n{e}\n",
   pure ()

end tactic

namespace tactic.interactive

open lean lean.parser interactive interactive.types tactic

local postfix `*`:9000 := many

meta def splita := split; [skip, assumption]

@[hole_command]
meta def whnf_type_hole : hole_command :=
{ name := "Reduce expected type",
  descr := "Reduce expected type",
  action := λ es,
    do t ← match es with
           | [h] := to_expr h >>= infer_type >>= whnf
           | [] := target >>= whnf
           | _ := fail "too many expressions"
           end,
       trace t,
       pure [] }

@[hole_command]
meta def dsimp_hole : hole_command :=
{ name := "dsimp expected type",
  descr := "dsimp expected type",
  action := λ es,
    do -- s ← simp_lemmas.mk_default,
       -- s ← es.mmap to_expr >>= s.append,
       (s, u) ← mk_simp_set ff [] $ es.map simp_arg_type.expr,
       dsimp_target s u,
       tgt ← target,
       s ← pformat!"(_ : {tgt})",
       pure [(to_string s, "")] }

@[hole_command]
meta def constructor_hole : hole_command :=
{ name := "constructor",
  descr := "apply constructor",
  action := λ es,
    do g ← main_goal,
       constructor,
       g ← instantiate_mvars g,
       let g := g.replace $ λ e _,
         match e with
         | expr.mvar _ _ t := some $ expr.const `_ []
         | _ := none end,
       s ← pp g,
       let s := if es.empty
         then (to_string s).replace "«_»" "_"
         else (to_string s).replace "«_»" "{!!}",
       pure [(to_string s, "")] }

meta def trace_error {α} (tac : tactic α) : tactic α
| s :=
match tac s with
| r@(interaction_monad.result.success a a_1) := r
| r@(interaction_monad.result.exception none a_1 a_2) := (trace "(no error message)" >> interaction_monad.result.exception none a_1) s
| r@(interaction_monad.result.exception (some msg) a_1 a_2) := (trace (msg ()) >> interaction_monad.result.exception none a_1) s
end


end tactic.interactive

instance subsingleton.fin0 {α} : subsingleton (fin 0 → α) :=
subsingleton.intro $ λ a b, funext $ λ i, fin.elim0 i

attribute [ext] function.hfunext

meta def options.list_names (o : options) : list name := o.fold [] (::)

namespace expr

meta def bracket (p : ℕ) (fmt : format) (p' : ℕ) : format :=
if p' < p then format.paren fmt else fmt

meta def fmt_binder (n : name) : binder_info → format → format
| binder_info.default t := format!"({n} : {t})"
| binder_info.implicit t := format!"{{{n} : {t}}"
| binder_info.strict_implicit t := format!"⦃{n} : {t}⦄"
| binder_info.inst_implicit t := format!"[{n} : {t}]"
| binder_info.aux_decl t := "_"

meta def parsable_printer' : expr → list name → ℕ → format
| (expr.var a) l := λ _, format!"@{(l.nth a).get_or_else name.anonymous}"
| (expr.sort level.zero) l := λ _, to_fmt "Prop"
| (expr.sort (level.succ u)) l := λ _, format!"Type.{{{u}}"
| (expr.sort u) l := λ _, format!"Sort.{{{u}}"
| (expr.const a []) l := λ _, format!"@{a}"
| (expr.const a ls) l := λ _, format!"@{a}.{{{format.intercalate  \" \" $ list.map to_fmt ls}}"
| (expr.mvar a a_1 a_2) l := λ _, to_fmt a
| (expr.local_const a a_1 a_2 a_3) l := λ _, to_fmt a_1
| (expr.app a a_1) l := bracket 10 $ format!"{parsable_printer' a l 10} {parsable_printer' a_1 l 9}"
| (expr.lam a a_1 a_2 a_3) l := bracket 8 $ format!"λ {fmt_binder a a_1 $ parsable_printer' a_2 l 10}, {parsable_printer' a_3 (a :: l) 10}"
| (expr.pi a a_1 a_2 a_3) l :=
       if a_3.has_var_idx 0
          then bracket 8 $ format!"Π {fmt_binder a a_1 $ parsable_printer' a_2 l 10}, {parsable_printer' a_3 (a :: l) 10}"
          else bracket 8 $ format!"{parsable_printer' a_2 l 7} → {parsable_printer' a_3 (a :: l) 7}"
| (expr.elet a a_1 a_2 a_3) l := bracket 8 $ format!"let {a} : {parsable_printer' a_1 l 10} := {parsable_printer' a_2 l 10} in {parsable_printer' a_3 (a :: l) 10}"
| (expr.macro a a_1) l := λ _, to_fmt "unsupported"

meta def parsable_printer (e : expr) : format := parsable_printer' e [] 10

meta def as_binder (e : expr) := fmt_binder e.local_pp_name e.binding_info (parsable_printer e.local_type)

end expr

meta def enclosing_name : tactic unit :=
do n ← tactic.decl_name,
   tactic.exact `(n)

meta def on_error {α β} (tac : tactic α) (hdl : tactic β) : tactic α
| s := match tac s with
       | (result.success a a_1) := result.success a a_1
       | (result.exception a a_1 s) := (hdl >> result.exception a a_1) s
       end

meta def finally {α β} (tac : tactic α) (hdl : tactic β) : tactic α :=
on_error tac hdl <* hdl

-- meta def brackets {α β} (tac : tactic α) (hdl : tactic β) : tactic α :=
-- on_error tac hdl <* hdl

meta def with_options {α} (xs : list name) (tac : tactic α) : tactic α :=
do opt ← tactic.get_options,
   tactic.set_options $ xs.foldl (λ o n, o.set_bool n tt) opt,
   finally tac (tactic.set_options opt)

declare_trace trace_scope.begin_end
declare_trace trace_scope.error

meta def trace_scope {α} (tac : tactic α) (n : name . enclosing_name) : tactic α :=
do tactic.when_tracing `trace_scope.begin_end $ trace!"• begin {n}",
   r ← on_error tac (tactic.when_tracing `trace_scope.error $ trace!"• error in {n}"),
   tactic.when_tracing `trace_scope.begin_end $ trace!"• end {n}",
   pure r

meta def stack_trace : vm_monitor ℕ :=
{ init := 0,
  step := λ i,
  do j ← vm.stack_size,
     if i = j then pure i else do
       fn ← vm.curr_fn,
       vm.put_str $ (list.repeat ' ' j).as_string ++ fn.to_string,
       pure j }

lemma mpr_mpr : Π {α β} (h : α = β) (h' : β = α) (x : α), h.mpr (h'.mpr x) = x
| _ _ rfl rfl x := rfl

lemma eq_mpr_of_mp_eq : Π {α β} {h : α = β} {x : α} {y : β} (h' : h.mp x = y), x = h.mpr y
| _ _ rfl _ _ := id

lemma mp_eq_of_eq_mpr : Π {α β} {h : α = β} {x : α} {y : β} (h' : x = h.mpr y), h.mp x = y
| _ _ rfl _ _ := id

lemma mp_eq_of_heq : Π {α β} {h : α = β} {x : α} {y : β} (h' : x == y), h.mp x = y
| _ _ rfl _ _ heq.rfl := rfl

namespace lazy_list

protected def pure {α} (x : α) : lazy_list α :=
lazy_list.cons x lazy_list.nil

protected def bind {α β} : lazy_list α → (α → lazy_list β) → lazy_list β
| lazy_list.nil _ := lazy_list.nil
| (lazy_list.cons x xs) f := (f x).append (bind (xs ()) f)

instance : monad lazy_list :=
{ pure := @lazy_list.pure,
  bind := @lazy_list.bind }

variables
{α β γ : Type u}
(x : α) (x' : lazy_list α)
(f : α → lazy_list β)
(g : β → lazy_list γ)

lemma append_nil (xs : lazy_list α) : xs.append nil = xs :=
begin
  induction xs; simp only [*, true_and, eq_self_iff_true, append],
  ext ⟨ ⟩; refl
end

lemma append_assoc (xs ys zs : lazy_list α) : (xs.append ys).append zs = xs.append (ys.append zs) :=
by induction xs; simp only [*, true_and, eq_self_iff_true, append]

lemma pure_bind : lazy_list.bind (lazy_list.pure x) f = f x :=
by simp only [lazy_list.pure,lazy_list.bind,append_nil]

lemma bind_pure : lazy_list.bind x' pure = x' :=
begin
  induction x'; simp [lazy_list.bind,has_pure.pure,lazy_list.pure,append],
  ext ⟨ ⟩, apply x'_ih
end

lemma bind_append {xs ys : lazy_list α} :
  lazy_list.bind (xs.append ys) f = (xs.bind f).append (ys.bind f) :=
by induction xs; simp only [*,append,lazy_list.bind,append_assoc]

lemma bind_assoc : lazy_list.bind (lazy_list.bind x' f) g = lazy_list.bind x' (λ a, lazy_list.bind (f a) g) :=
begin
  induction x', refl,
  dsimp at x'_ih,
  simp only [lazy_list.bind,*],
  rw [← x'_ih,bind_append],
end

instance : is_lawful_monad lazy_list :=
{ pure_bind := λ α β, pure_bind,
  bind_assoc := @bind_assoc,
  id_map := by intros; apply bind_pure
   }

end lazy_list

namespace lean.parser

meta def returnex {α : Type} (e : exceptional α) : lean.parser α :=
λ s, match e with
| exceptional.success a      := result.success a s
| exceptional.exception f := result.exception (some (λ u, f s.options)) none s
end

end lean.parser

namespace tactic

setup_tactic_parser

meta def apply_symm (n : name) : tactic expr :=
do e ← mk_const n,
   (vs,t) ← infer_type e >>= mk_local_pis,
   e' ← mk_eq_symm $ e.mk_app vs,
   lambdas vs e'

@[interactive]
meta def fold (ns : parse ident*) (ls : parse location) : tactic unit :=
do hs ← ns.mmap $ get_eqn_lemmas_for tt,
   hs ← hs.join.mmap apply_symm,
   (s,u) ← mk_simp_set tt [] (hs.map $ simp_arg_type.expr ∘ to_pexpr),
   ls.try_apply (λ h, () <$ simp_hyp s u h) (simp_target s u)

meta def decl_kind : declaration → string
| (declaration.defn a a_1 a_2 a_3 a_4 a_5) := "def"
| (declaration.thm a a_1 a_2 a_3) := "theorem"
| (declaration.cnst a a_1 a_2 a_3) := "constant"
| (declaration.ax a a_1 a_2) := "axiom"

declare_trace generated_decl
declare_trace generated_decl.tests

@[user_attribute]
meta def generated_attr : user_attribute (native.rb_lmap name name) name :=
{ name := `generated,
  parser := ident,
  cache_cfg :=
    { mk_cache := λ ls, ls.mfoldl (λ m d, do gen ← generated_attr.get_param d, pure $ m.insert gen d)
                                  (native.rb_lmap.mk _ _),
      dependencies := [] },
  descr := "mark generated declarations and tag them with the declaration that generated them" }

meta def emit_decl' (n : name) (d : declaration) : tactic expr :=
do when_tracing `generated_decl $ trace!"[generated for {n}]\n  {decl_kind d} {d.to_name} : {d.type}",
   when_tracing `generated_decl.tests $ trace!"#check (@{d.to_name} : {d.type})",
   generated_attr.set d.to_name n tt,
   add_decl' d

meta def emit_decl (n : name) (d : declaration) : tactic unit :=
emit_decl' n d >> pure ()

end tactic

namespace psigma

variables {α : Sort u} {β : α → Sort v} {γ : Sort w}

def curry (f : psigma β → γ) : Π a (b : β a), γ :=
λ x y, f ⟨x,y⟩

def uncurry (f : Π a (b : β a), γ) : psigma β → γ
| ⟨a,b⟩ := f a b

end psigma
