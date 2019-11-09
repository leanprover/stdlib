import tactic.vampire.frm

namespace vampire

local notation f `₀↦` a := assign a f
local notation `v*` := xtrm.vr
local notation `f*` := xtrm.fn
local notation `[]*` := xtrm.nil
local notation h `::*` ts  := xtrm.cons h ts
local notation `r*`     := atm.rl 
local notation t `=*` s := atm.eq t s 
local notation `+*`     := frm.atm tt
local notation `-*`     := frm.atm ff
local notation p `∨*` q := frm.bin tt p q
local notation p `∧*` q := frm.bin ff p q
local notation `∃*` p   := frm.qua tt p
local notation `∀*` p   := frm.qua ff p

@[derive decidable_eq]
meta inductive preterm : Type
| var : bool → nat → preterm
| exp : expr → preterm
| app : preterm → preterm → preterm

meta def preterm.repr : preterm → string
| (preterm.var tt k) := "X" ++ k.to_subs
| (preterm.var ff k) := "S" ++ k.to_subs
| (preterm.exp x)    := (to_fmt x).to_string
| (preterm.app t s)  := "(" ++ t.repr ++ " " ++ s.repr ++ ")"

meta inductive preatom : Type
| rel : preterm → preatom
| eq  : preterm → preterm → preatom

meta def preatom.repr : preatom → string
| (preatom.rel t)  := t.repr
| (preatom.eq t s) := "(" ++ t.repr ++ " = " ++ s.repr ++ ")"

meta inductive prefrm : Type
| lit : bool → preatom → prefrm
| bin : bool → prefrm → prefrm → prefrm
| qua : bool → prefrm → prefrm

meta def prefrm.repr : prefrm → string
| (prefrm.lit tt a)   := a.repr
| (prefrm.lit ff a)   := "¬" ++ a.repr
| (prefrm.bin tt f g) := "(" ++ f.repr ++ " ∨ " ++ g.repr ++ ")"
| (prefrm.bin ff f g) := "(" ++ f.repr ++ " ∧ " ++ g.repr ++ ")"
| (prefrm.qua ff f) := "∀ " ++ f.repr
| (prefrm.qua tt f) := "∃ " ++ f.repr

meta instance prefrm.has_to_format : has_to_format prefrm :=
⟨λ x, x.repr⟩

open tactic expr

meta def to_preterm : expr → tactic preterm
| (var k) :=
  return (preterm.var tt k)
| (app x y) :=
  do t ← to_preterm x,
     s ← to_preterm y,
     return (preterm.app t s)
| x := return (preterm.exp x)

meta def to_preatom : expr → tactic preatom
| `(%%tx = %%sx) :=
  do t ← to_preterm tx,
     s ← to_preterm sx,
     return (preatom.eq t s)
| ax :=
  do t ← to_preterm ax,
     return (preatom.rel t)

meta def to_prefrm : expr → tactic prefrm
| `(%%px ∨ %%qx) :=
  do φ ← to_prefrm px,
     χ ← to_prefrm qx,
     return (prefrm.bin tt φ χ)
| `(%%px ∧ %%qx) :=
  do φ ← to_prefrm px,
     χ ← to_prefrm qx,
     return (prefrm.bin ff φ χ)
| (pi _ _ _ px) :=
  do φ ← to_prefrm px,
     return (prefrm.qua ff φ)
| `(Exists %%(expr.lam _ _ _ px)) :=
  do φ ← to_prefrm px,
     return (prefrm.qua tt φ)
| `(Exists %%prx) :=
  do φ ← to_prefrm (app (prx.lift_vars 0 1) (var 0)),
     return (prefrm.qua tt φ)
| `(¬ %%px) :=
  do a ← to_preatom px,
     return (prefrm.lit ff a)
| px        :=
  do a ← to_preatom px,
     return (prefrm.lit tt a)

meta def to_trm : preterm → trms → tactic trm
| (preterm.var tt k) []*       := return (v* k)
| (preterm.var tt k) (_ ::* _) := fail "Variables cannot have arguments"
| (preterm.var ff k) ts        := return (f* k ts)
| (preterm.exp x)    _         := failed
| (preterm.app pt ps) ts :=
  do s ← to_trm ps []*,
     to_trm pt (s ::* ts)

meta def to_atm_aux : preterm → list trm → tactic atm
| (preterm.var ff k) ts := return (r* k ts)
| (preterm.var tt k) _  := failed
| (preterm.exp x)    _  := failed
| (preterm.app pt ps) ts :=
  do t ← to_trm ps []*,
     to_atm_aux pt (t :: ts)

meta def to_atm : preatom → tactic atm
| (preatom.rel pt) := to_atm_aux pt []
| (preatom.eq pt ps) :=
  do t ← to_trm pt []*,
     s ← to_trm ps []*,
     return (t =* s)

meta def to_frm : prefrm → tactic frm
| foo@(prefrm.lit b pa)   :=
  do a ← to_atm pa,
     return (frm.atm b a)
| foo@(prefrm.bin b pf pg) :=
  do f ← to_frm pf,
     g ← to_frm pg,
     return (frm.bin b f g)
| foo@(prefrm.qua b pf) :=
  do f ← to_frm pf,
     return (frm.qua b f)

meta def is_sym_type (b : bool) (αx : expr) : expr → bool
| `(%%x → %%y) := (x = αx) && (is_sym_type y)
| x            := if b then x = `(Prop) else x = αx

meta def preterm.to_expr : preterm → tactic expr
| (preterm.exp x) := return x
| (preterm.app t s) :=
  do x ← t.to_expr,
     y ← s.to_expr,
     return (app x y)
| _ := failed

meta def preterm.is_sym (b : bool) (αx) (t : preterm) : tactic unit :=
do tx ← t.to_expr >>= infer_type,
   if is_sym_type b αx tx
   then skip
   else failed

meta def preterm.get_sym (b : bool) (αx : expr) : preterm → tactic preterm
| r@(preterm.app t s) :=
  t.get_sym <|>
  s.get_sym <|>
  (r.is_sym b αx >> return r)
| t := t.is_sym b αx >> return t

meta def preatom.get_sym (b : bool) (αx : expr) : preatom → tactic preterm
| (preatom.rel t)  := t.get_sym b αx
| (preatom.eq t s) := t.get_sym b αx <|> s.get_sym b αx

meta def prefrm.get_sym (b : bool) (αx : expr) : prefrm → tactic preterm
| (prefrm.lit _ x)   := x.get_sym b αx
| (prefrm.bin _ x y) := x.get_sym <|> y.get_sym
| (prefrm.qua _ x)   := x.get_sym

meta def preterm.subst (s : preterm) (k : nat) : preterm → preterm
| t@(preterm.app t1 t2) :=
  if t = s
  then preterm.var ff k
  else preterm.app t1.subst t2.subst
| t :=
  if t = s
  then preterm.var ff k
  else t

meta def preatom.subst (r : preterm) (k : nat) : preatom → preatom
| (preatom.rel t)  := preatom.rel (preterm.subst r k t)
| (preatom.eq t s) := preatom.eq (preterm.subst r k t) (preterm.subst r k s)

meta def prefrm.subst (s : preterm) (k : nat) : prefrm → prefrm
| (prefrm.lit b l)   := prefrm.lit b (l.subst s k)
| (prefrm.bin b f g) := prefrm.bin b f.subst g.subst
| (prefrm.qua b f)   := prefrm.qua b f.subst

meta def abst (αx : expr) : bool → nat → prefrm → tactic prefrm
| b k f :=
  (do s ← f.get_sym b αx,
      abst b (k + 1) (f.subst s k)) <|>
  (if b then return f else abst tt 0 f)

meta def reify (αx : expr) : tactic frm :=
do t ← target,
   x ← to_prefrm t,
   y ← abst αx ff 0 x,
   z ← to_frm y,
   return z

end vampire
