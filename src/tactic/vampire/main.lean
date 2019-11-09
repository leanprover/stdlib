import system.io
import logic.basic
import data.list.min_max
import tactic.vampire.reify
import tactic.vampire.cnf
import tactic.vampire.skolemize

namespace vampire

local notation `v*` := xtrm.vr
local notation `f*` := xtrm.fn
local notation `[]*` := xtrm.nil
local notation h `::*` ts  := xtrm.cons h ts
local notation `r*`     := atm.rl 
local notation t `=*` s := atm.eq t s 
local notation p `∨*` q := frm.bin tt p q
local notation p `∧*` q := frm.bin ff p q
local notation `∃*` p   := frm.qua tt p
local notation `∀*` p   := frm.qua ff p
local notation R `;` F `;` V `⊨` f := frm.holds R F V f

run_cmd mk_simp_attr `sugars

attribute [sugars]
  -- logical constants
  or_false  false_or
  and_false false_and
  or_true   true_or
  and_true  true_and
  -- implication elimination
  classical.imp_iff_not_or
  classical.iff_iff_not_or_and_or_not
  -- NNF
  classical.not_not
  not_exists
  not_or_distrib
  classical.not_and_distrib
  classical.not_forall

meta def desugar := `[try {simp only with sugars}]

meta def get_domain_core : expr → tactic expr
| `(¬ %%p)     := get_domain_core p
| `(%%p ∨ %%q) := get_domain_core p <|> get_domain_core q
| `(%%p ∧ %%q) := get_domain_core p <|> get_domain_core q
| `(%%p ↔ %%q) := get_domain_core p <|> get_domain_core q
| (expr.pi _ _ p q) :=
  mcond (tactic.is_prop p) (get_domain_core p <|> get_domain_core q) (return p)
| `(@Exists %%t _)  := return t
| _ := tactic.failed

meta def get_domain : tactic expr :=
(tactic.target >>= get_domain_core) <|> return `(unit)

meta def get_inhabitance (αx : expr) : tactic expr :=
do ihx ← tactic.to_expr ``(inhabited),
   tactic.mk_instance (expr.app ihx αx)

variables {α : Type} 

inductive proof (m : mat) : cla → Type
| H (k : nat) : proof (m.nth k)
| C (l : lit) (c : cla) :
  proof (l :: l :: c) → proof (l :: c)
| R (a : atm) (c d : cla) :
  proof ((ff, a) :: c) →
  proof ((tt, a) :: d) →
  proof (c ++ d)
| S (μs : vmaps) (c : cla) : 
  proof c → proof (c.vsubs μs)
| T (k : nat) (c : cla) :
  proof c → proof (c.rot k)
| P (l : lit) (t s : trm) (c d : cla) :
  proof (l :: c) →
  proof (((tt, t =* s) :: d)) →
  proof (l.replace t s :: c ++ d)
| Y (b : bool) (t s : trm) (c : cla) :
  proof ((b, t =* s) :: c) → 
  proof ((b, s =* t) :: c)
| V (t : trm) (c : cla) :
  proof ((ff, t =* t) :: c) → proof c

/- Same as is.fs.read_to_end and io.cmd,
   except for configurable read length. -/
def io.fs.read_to_end' (h : io.handle) : io char_buffer :=
io.iterate mk_buffer $ λ r,
  do done ← io.fs.is_eof h,
    if done
    then return none
    else do
      c ← io.fs.read h 65536,
      return $ some (r ++ c)

def io.cmd' (args : io.process.spawn_args) : io string :=
do child ← io.proc.spawn { stdout := io.process.stdio.piped, ..args },
  buf ← io.fs.read_to_end' child.stdout,
  io.fs.close child.stdout,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
  return buf.to_string
open tactic

universe u

class has_to_asm (α : Type u) :=
(to_asm : α → string)

def to_asm {α : Type u} [has_to_asm α] : α → string :=
has_to_asm.to_asm

instance nat.has_to_asm : has_to_asm nat := ⟨λ k, "b" ++ k.bstr⟩

def xtrm.to_asm : ∀ {b : bool}, xtrm b → string
| _ []*        := "n"
| _ (t ::* ts) := ts.to_asm ++ t.to_asm ++ "c"
| _ (v* k)     := to_asm k ++ "v"
| _ (f* k ts)  := ts.to_asm ++ to_asm k ++ "f"

instance trm.has_to_asm : has_to_asm trm :=
⟨xtrm.to_asm⟩ 

def list.to_asm [has_to_asm α] : list α → string 
| []        := "n"
| (a :: as) := list.to_asm as ++ to_asm a ++ "c"

instance list.has_to_asm [has_to_asm α] : has_to_asm (list α) :=
⟨list.to_asm⟩  

def atm.to_asm : atm → string
| (r* k ts) := to_asm ts ++ to_asm k ++ "r"
| (t =* s)  := to_asm t ++ to_asm s ++ "e"

instance atm.has_to_asm : has_to_asm atm := ⟨atm.to_asm⟩

def lit.to_asm : lit → string
| (b, a) := to_asm a ++ if b then "+" else "-"

instance lit.has_to_asm : has_to_asm lit := ⟨lit.to_asm⟩

meta def get_asm (m : mat) : tactic string :=
unsafe_run_io $ io.cmd'
{ cmd := "main.pl",
  args := [to_asm m] }

meta inductive item : Type
| nl                       : item
| nm  (n : nat)            : item
| trm (t : trm)            : item
| trms (ts : trms)         : item
| mp (μ : vmap)            : item
| mps (μs : vmaps)         : item
| prf (x : expr) (c : cla) : item

namespace item
 
meta def repr : item → string 
| item.nl        := "()"
| (item.nm n)    := n.repr
| (item.trm t)   := t.repr
| (item.trms ts) := ts.repr
| (item.mp m)    := "VMAP"
| (item.mps m)   := "VMAPS"
| (item.prf x c) := c.repr

meta instance has_repr : has_repr item := ⟨repr⟩ 

meta instance has_to_format : has_to_format item := ⟨λ x, repr x⟩ 

end item

meta def vmap.to_expr : vmap → expr
| (k, t) := expr.mk_app `(@prod.mk nat trm) [k.to_expr, t.to_expr]

meta def vmaps.to_expr : vmaps → expr
| []        := `(@list.nil vmap)
| (m :: ms) := expr.mk_app `(@list.cons vmap) [m.to_expr, vmaps.to_expr ms]

set_option eqn_compiler.max_steps 4096

meta def build_proof_core (m : mat) (mx : expr) :
  list item → list char → tactic expr
| (item.prf x _ :: stk) [] := return x
| stk (' ' :: chs) :=
  build_proof_core stk chs
| stk ('\n' :: chs) :=
  build_proof_core stk chs
| (item.nm k :: stk) ('H' :: infs) :=
  let πx := expr.mk_app `(@proof.H) [mx, k.to_expr] in
  build_proof_core (item.prf πx (m.nth k) :: stk) infs
| (item.mps μs :: item.prf πx c :: stk) ('S' :: infs) :=
  let c' := c.vsubs μs in
  let πx' := expr.mk_app `(@proof.S) [mx, μs.to_expr, cla.to_expr c, πx] in
  build_proof_core (item.prf πx' c' :: stk) infs
| ((item.prf σx ((tt, a) :: d)) :: (item.prf πx ((ff, b) :: c)) :: stk) ('R' :: infs) :=
  let πx := expr.mk_app `(@proof.R) [mx, a.to_expr, cla.to_expr c, cla.to_expr d, πx, σx] in
  build_proof_core (item.prf πx (c ++ d) :: stk) infs
| (item.nm k :: item.prf πx c :: stk) ('T' :: chs) :=
  let πx := expr.mk_app `(@proof.T) [mx, k.to_expr, c.to_expr, πx] in
  build_proof_core (item.prf πx (c.rot k) :: stk) chs
| ((item.prf πx (l :: _ :: c)) :: stk) ('C' :: chs) :=
  let πx := expr.mk_app `(@proof.C) [mx, l.to_expr, cla.to_expr c, πx] in
  build_proof_core (item.prf πx (l :: c) :: stk) chs
| ( (item.prf σx ((tt, t =* s) :: d)) :: (item.prf πx (l :: c)) :: stk ) ('P' :: chs) :=
  let ρx := expr.mk_app `(@proof.P) 
    [mx, l.to_expr, t.to_expr, s.to_expr, cla.to_expr c, cla.to_expr d, πx, σx] in
  build_proof_core (item.prf ρx (l.replace t s :: c ++ d) :: stk) chs
| ((item.prf πx ((b, t =* s) :: c)) :: stk) ('Y' :: chs) :=
  let πx' := expr.mk_app `(@proof.Y) [mx, b.to_expr, t.to_expr, s.to_expr, cla.to_expr c, πx] in
  build_proof_core (item.prf πx' ((b, s =* t) :: c) :: stk) chs
| ((item.prf πx ((ff, t =* _) :: c)) :: stk) ('V' :: chs) :=
  let πx' := expr.mk_app `(@proof.V) [mx, t.to_expr, cla.to_expr c, πx] in
  build_proof_core (item.prf πx' c :: stk) chs
| stk ('b' :: chs) :=
  build_proof_core (item.nm 0 :: stk) chs
| (item.nm k :: stk) ('0' :: chs) :=
  build_proof_core (item.nm (k * 2) :: stk) chs
| (item.nm k :: stk) ('1' :: chs) :=
  build_proof_core (item.nm ((k * 2) + 1) :: stk) chs
| (item.nm k :: stk) ('v' :: chs) :=
  build_proof_core (item.trm (v* k) :: stk) chs
| (item.nm k :: item.nl :: stk) ('f' :: chs) :=
  build_proof_core (item.trm (f* k []*) :: stk) chs
| (item.nm k :: item.trms ts :: stk) ('f' :: chs) :=
  build_proof_core (item.trm (f* k ts) :: stk) chs
| stk ('n' :: chs) :=
  build_proof_core (item.nl :: stk) chs
| (item.nm k :: item.trm t :: stk) ('m' :: infs) :=
  build_proof_core (item.mp (k, t) :: stk) infs
| (item.trm t :: item.nl :: stk) ('c' :: infs) :=
  build_proof_core (item.trms (t ::* []*) :: stk) infs
| (item.trm t :: item.trms ts :: stk) ('c' :: infs) :=
  build_proof_core (item.trms (t ::* ts) :: stk) infs
| (item.mp μ :: item.nl :: stk) ('c' :: infs) :=
  build_proof_core (item.mps [μ] :: stk) infs
| (item.mp μ :: item.mps μs :: stk) ('c' :: infs) :=
  build_proof_core (item.mps (μ :: μs) :: stk) infs
| (X :: Y :: _) chs := 
  trace "Stack top : " >> trace X >> trace Y >> 
  trace "Remaining proof" >> trace chs >> failed
| (X :: _) chs := 
  trace "Stack top : " >> trace X >>
  trace "Remaining proof" >> trace chs >> failed
| [] chs := trace "Stack empty, remaining proof : " >> trace chs >> failed

variables {R : rls α} {F : fns α} {V : vas α}
variables {b : bool} (f g : frm)

def normalize (f : frm) : frm :=
skolemize $ pnf $ f.neg

def clausify (f : frm) : mat :=
cnf $ frm.strip_fa $ normalize f

lemma lit.holds_vsubs (μs : vmaps) (l : lit) :
  (l.vsubs μs).holds R F V ↔
  l.holds R F (V.vsubs F μs) :=
begin
  cases l with b a; cases b;
  simp only [ lit.holds, lit.vsubs, atm.holds_vsubs ]
end

lemma cla.holds_vsubs {μs : vmaps} {c : cla} :
  (c.vsubs μs).holds R F V ↔
  c.holds R F (V.vsubs F μs) :=
by { apply @list.exists_mem_map_iff,
     apply lit.holds_vsubs }

open list

lemma holds_cla_of_proof {m : mat}
  (h0 : ∀ V : vas α, m.holds R F V) :
  ∀ {c : cla}, proof m c →
  (∀ V : vas α, c.holds R F V) :=
begin
  intros c π, 
  induction π with
    k 
    l d π h1
    t c1 c2 π1 π2 h1 h2
    μs c π h1
    k d π h1
    l t s c d π σ h1 h2
    b t s d h1 h2
    t d h1 h2,
  { unfold mat.nth,
    cases h1 : list.nth m k;
    unfold option.get_or_else,
    { apply holds_tautology },
    intro V, apply h0,
    apply list.mem_iff_nth.elim_right,
    refine ⟨_, h1⟩ },
  { intro V,
    rcases h1 V with ⟨t, h2 | h2 | h2, h3⟩;
    refine ⟨_, _, h3⟩,
    { left, exact h2 },
    { left, exact h2 },
    right, exact h2 },
  { intro V,
    apply exists_mem_append.elim_right,
    rcases h1 V with ⟨la, hla1 | hla1, hla2⟩,
    { rcases h2 V with ⟨lb, hlb1 | hlb1, hlb2⟩,
      { subst hla1, subst hlb1, cases hla2 hlb2 },
      right, refine ⟨_, hlb1, hlb2⟩ },
    left, refine ⟨_, hla1, hla2⟩ },
  { intro V,  
    rw cla.holds_vsubs,
    apply h1 },
  { intro V,
    rcases (h1 V) with ⟨t, ht1, ht2⟩,
    refine ⟨t, _, ht2⟩,
    apply mem_rot _ ht1 },
  { intro V,
    rcases (exists_mem_cons_iff _ _ _).elim_left 
      (h1 V) with h3 | ⟨w, h3, h4⟩,
    { rcases (exists_mem_cons_iff _ _ _).elim_left 
        (h2 V) with h4 | ⟨w, h4, h5⟩,
      { refine ⟨_, or.inl rfl, _⟩, 
        rw lit.holds_replace h4,
        exact h3 },
      refine ⟨w, or.inr (mem_append_right _ h4), h5⟩ },
    refine ⟨w, or.inr (mem_append_left _ h3), h4⟩ },
  { intro V, cases b;
    { rcases h2 V with ⟨l, h2 | h2, h3⟩, 
      { refine ⟨_, or.inl rfl, _⟩, 
        rw h2 at h3,
        try { apply ne.symm h3 },
        try { apply eq.symm h3 } },
      refine ⟨l, or.inr h2, h3⟩ } },
  { intro V,
    rcases h2 V with ⟨l, h2 | h2, h3⟩, 
    { rw h2 at h3,
      exfalso, apply h3 rfl },
    refine ⟨l, h2, h3⟩ }
end

lemma frxffx_of_proof [inhabited α]
  (rn : nat) (R : rls α) (fn : nat) (F : fns α) (f : frm) :
  (normalize f).vnew = 0 →
  proof (clausify f) [] → f.frxffx rn R fn F :=
begin
  intros hz h0,
  apply frxffx_of_forall_rxt,
  intros R' h1 F' h2,
  apply classical.by_contradiction,
  rw ← holds_neg, intro h3,
  rw ← pnf_eqv at h3,
  rcases holds_skolemize h3 with ⟨F'', h4, h5⟩,
  have hAF : (skolemize (pnf (frm.neg f))).AF,
  { apply AF_skolemize,
    apply QF_pnf },
  have h6 := holds_strip_fa hAF _ (forall_ext_zero h5),
  { have h7 : ∀ (W : vas α), (clausify f).holds R' F'' W,
    { intro W, apply holds_cnf _ (h6 _),
      apply F_strip_fa _ hAF },
    have h8 := holds_cla_of_proof h7 h0 (Vdf α),
    apply not_holds_empty_cla h8 },
  apply le_of_eq hz
end

instance decidable_vnew_eq_zero (f : frm) :
  decidable ((normalize f).vnew = 0) := by apply_instance

meta def build_proof (chs : list char)
  (αx ix : expr) (f : frm) (m : mat) : tactic expr :=
do πx ← build_proof_core m m.to_expr [] chs,
   let rnx : expr := f.rnew.to_expr,
   let fnx : expr := f.fnew.to_expr,
   let Rx : expr := `(Rdf %%αx),
   let Fx : expr := `(@Fdf %%αx %%ix),
   let fx : expr := f.to_expr,
   let eqx  : expr := `(frm.vnew (normalize %%fx) = 0 : Prop),
   let decx : expr := expr.mk_app `(vampire.decidable_vnew_eq_zero) [fx],
   let hx   : expr := expr.mk_app `(@of_as_true) [eqx, decx, `(trivial)],
   let x : expr := expr.mk_app `(@frxffx_of_proof)
     [αx, ix, rnx, Rx, fnx, Fx, fx, hx, πx],
   return x

meta def vampire (inp : option string) : tactic unit :=
do desugar,
   αx ← get_domain,
   ix ← get_inhabitance αx,
   f  ← reify αx,
   let m := clausify f,
   s ← (inp <|> get_asm m),
   x ← build_proof s.data αx ix f m,
   apply x,
   if inp = none
   then trace s
   else skip

end vampire
 
open lean.parser interactive vampire tactic

meta def tactic.interactive.vampire
  (ids : parse (many ident))
  (inp : option string := none) : tactic unit :=
( if `all ∈ ids
  then local_context >>= monad.filter is_proof >>=
       revert_lst >> skip
  else do hs ← mmap tactic.get_local ids,
               revert_lst hs, skip ) >>
vampire.vampire inp