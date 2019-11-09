import logic.basic
import data.bool
import data.nat.basic
import algebra.order_functions
import tactic.vampire.list
import tactic.vampire.misc

universes u v

namespace vampire

open nat list

variables {α β : Type}
variables {A : Type u}
variables {B : Type v}

local notation f `₀↦` a := assign a f

def rl  (α : Type) : Type := list α → Prop
def fn  (α : Type) : Type := list α → α
def rls (α : Type) : Type := nat → rl α
def fns (α : Type) : Type := nat → fn α
def vas (α : Type) : Type := nat → α

variables {R : rls α} {F : fns α} {V  : vas α}

def nrl (α : Type) : nat → Type
| 0       := Prop
| (k + 1) := α → nrl k

def nfn (α : Type) : nat → Type
| 0       := α
| (k + 1) := α → nfn k

def nrl.unfix : ∀ {k : nat}, nrl α k → rl α
| 0       f []        := f
| 0       f (_ :: _)  := false
| (k + 1) f []        := false
| (k + 1) f (a :: as) := nrl.unfix (f a) as

def nfn.unfix [inhabited α] : ∀ {k : nat}, nfn α k → fn α
| 0       f []        := f
| 0       f (_ :: _)  := default α
| (k + 1) f []        := default α
| (k + 1) f (a :: as) := nfn.unfix (f a) as

def Rdf (α : Type) : rls α := λ _ _, false
def Fdf (α : Type) [inhabited α] : fns α := λ _ _, default α
def Vdf (α : Type) [inhabited α] : vas α := λ _, default α

local notation f `₀↦` a := assign a f

@[derive decidable_eq]
inductive xtrm : bool → Type 
| vr   : nat → xtrm ff
| fn   : nat → xtrm tt → xtrm ff
| nil  : xtrm tt 
| cons : xtrm ff → xtrm tt → xtrm tt 

@[reducible] def trm  := xtrm ff
@[reducible] def trms := xtrm tt

local notation `v*` := xtrm.vr
local notation `f*` := xtrm.fn
local notation `[]*` := xtrm.nil
local notation h `::*` ts  := xtrm.cons h ts

namespace xtrm 

def size : ∀ {b : bool}, xtrm b → nat
| ff (v* k)      := 0
| ff (f* k ts)   := ts.size + 1
| tt []*        := 0
| tt (t ::* ts) := t.size + ts.size + 1

lemma succ_size_tail_le_size_cons {t : trm} {ts : trms} : 
  succ (size ts) ≤ size (t::*ts) := 
@eq.rec nat (size t + (size ts + 1)) (λ x, (size ts).succ ≤ x) 
  (nat.le_add_left _ _) _ rfl

lemma size_tail_lt_size_cons {t : trm} {ts : trms} : 
  (size ts) < size (cons t ts) :=  
@nat.lt_of_lt_of_le _ (size ts).succ _ (lt_succ_self _) 
  succ_size_tail_le_size_cons

lemma size_head_lt_size_cons {t : trm} {ts : trms} :
  xtrm.size t < xtrm.size (t ::* ts) := 
nat.lt_of_le_of_lt 
  (nat.le_add_right _ (xtrm.size ts)) 
  (nat.lt_succ_self _)

end xtrm

namespace trms

def mem (t : trm) : trms → Prop
| []*        := false
| (s ::* ts) := t = s ∨ mem ts
using_well_founded {
  dec_tac := `[ apply xtrm.size_tail_lt_size_cons ],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf xtrm.size⟩]
}

instance has_mem : has_mem trm trms := ⟨mem⟩ 

lemma mem_cons_iff (t s : trm) (ts : trms) : 
  t ∈ (s ::* ts) ↔ t = s ∨ t ∈ ts := iff.refl _

def length : trms → nat 
| []*        := 0
| (_ ::* ts) := length ts + 1

def lmap (f : trm → A) : trms → list A 
| []*        := []
| (t ::* ts) := f t :: lmap ts
using_well_founded {
  dec_tac := `[ apply xtrm.size_tail_lt_size_cons ],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf xtrm.size⟩]
}

def dlmap : ∀ {ts : trms}, (∀ t : trm, t ∈ ts → A) → list A 
| []*        := λ _, []
| (t ::* ts) := λ f, (f t (or.inl rfl) :: @dlmap ts (λ x h, f x $ or.inr h))
using_well_founded {
  dec_tac := `[ apply xtrm.size_tail_lt_size_cons ],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf xtrm.size⟩]
}

def tmap (f : trm → trm) : trms → trms 
| []*        := []*
| (t ::* ts) := f t ::* tmap ts
using_well_founded {
  dec_tac := `[ apply xtrm.size_tail_lt_size_cons ],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf xtrm.size⟩]
}

def dtmap : ∀ {ts : trms}, (∀ t : trm, t ∈ ts → trm) → trms  
| []*        := λ _, []*
| (t ::* ts) := λ f, (f t (or.inl rfl) ::* @dtmap ts (λ x h, f x $ or.inr h))
using_well_founded {
  dec_tac := `[ apply xtrm.size_tail_lt_size_cons ],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf xtrm.size⟩]
}

/- Lemmas -/

lemma dlmap_eq_lmap (f : trm → A) :
  ∀ ts : trms, dlmap (λ x, λ _ : x ∈ ts, f x) = lmap f ts 
| []*        := rfl
| (t ::* ts) := 
  by { unfold dlmap, unfold lmap,
       apply congr_arg,
       apply dlmap_eq_lmap }

lemma dtmap_eq_tmap (f : trm → trm) :
  ∀ ts : trms, dtmap (λ x, λ _ : x ∈ ts, f x) = tmap f ts 
| []*        := rfl
| (t ::* ts) := 
  by { unfold dtmap, unfold tmap,
       apply congr_arg,
       apply dtmap_eq_tmap }

lemma lmap_tmap (f : trm → A) (g : trm → trm) :
  ∀ ts : trms, lmap f (tmap g ts) = lmap (f ∘ g) ts 
| []*        := rfl
| (t ::* ts) := 
  by { unfold tmap, unfold lmap,
       apply congr_arg,
       apply lmap_tmap }

lemma tmap_tmap (f : trm → trm) (g : trm → trm) :
  ∀ ts : trms, tmap f (tmap g ts) = tmap (f ∘ g) ts 
| []*        := rfl
| (t ::* ts) := 
  by { unfold tmap, apply congr_arg, apply tmap_tmap }

lemma forall_mem_of_forall_mem_cons 
  {p : trm → Prop} {t : trm} {ts : trms} :
  (∀ x : trm, x ∈ (t ::* ts) → p x) → 
  (∀ x : trm, x ∈ ts → p x) := 
λ h0 t h1, h0 _ (or.inr h1)

lemma lmap_eq_lmap {f g : trm → A} :
  ∀ {ts : trms}, 
  (∀ t : trm, t ∈ ts → f t = g t) → 
  lmap f ts = lmap g ts
| []* := λ _, rfl
| (t ::* ts) :=
  by { intro h0, unfold lmap,
       rw [ h0 _ (or.inl rfl), @lmap_eq_lmap ts ],
       apply forall_mem_of_forall_mem_cons h0 }
  
end trms

lemma xtrm.size_lt_size_of_mem :
  ∀ {ts : trms} {s : trm}, 
  s ∈ ts → xtrm.size s < xtrm.size ts   
| []*        := by rintros _ ⟨_⟩
| (t ::* ts) := 
  λ s h0, 
    or.rec_on ((trms.mem_cons_iff _ _ _).elim_left h0) 
    (λ h1, @eq.rec _ t (λ x, xtrm.size x < xtrm.size (t ::* ts)) 
      xtrm.size_head_lt_size_cons s h1.symm)
    (λ h1, nat.lt_trans (@xtrm.size_lt_size_of_mem ts s h1) 
       (@xtrm.size_tail_lt_size_cons t ts)) 
using_well_founded {
  dec_tac := `[ apply xtrm.size_tail_lt_size_cons ],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf xtrm.size⟩]
}

lemma xtrm.lt_size_fn {k : nat} {s : trm} {ts : trms} :
  s ∈ ts → xtrm.size s < xtrm.size (f* k ts) := 
λ h0, nat.lt_trans (xtrm.size_lt_size_of_mem h0) (nat.lt_succ_self _)

def vmap  : Type := nat × trm
def vmaps : Type := list vmap

def vmaps.get (k : nat) : vmaps → option trm
| []             := none
| ((m, t) :: μs) := if k = m then some t else vmaps.get μs

def trm.rec {C : trm → Sort u} 
  (f : ∀ k : nat, C ((v* k))) 
  (g : ∀ k : nat, ∀ ts : trms, 
    (∀ t ∈ ts, C t) → C (f* k ts)) : 
  ∀ t : trm, C t 
| (v* k)    := f _
| (f* k ts) := g _ _ (λ x h, trm.rec _)
using_well_founded {
  dec_tac := `[ apply xtrm.lt_size_fn, assumption ],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf xtrm.size⟩]
}

def trm.val (F : fns α) (V : vas α) : trm → α :=
trm.rec V (λ k _ f, F k (trms.dlmap f))

def vas.vsubs (F : fns α) (μ : vmaps) (V : vas α) (k : nat) : α :=
option.rec (V k) (trm.val F V) (μ.get k)

namespace trm

meta def rec_fn_t : tactic unit := 
`[ unfold rec, apply congr_arg, apply trms.dtmap_eq_tmap ]

meta def rec_fn_l : tactic unit := 
`[ unfold rec, apply congr_arg, apply trms.dlmap_eq_lmap ]

def repr : trm → string := 
rec 
  (λ k, "X" ++ k.to_subs) 
  (λ k ts f, "f" ++ k.to_subs ++ string.tuplize (trms.dlmap f))

instance has_repr : has_repr trm := ⟨repr⟩

meta instance has_to_format : has_to_format trm := ⟨λ x, repr x⟩ 

meta def to_expr : trm → expr :=
rec 
  (λ k, expr.app `(xtrm.vr) k.to_expr) 
  (λ k ts f, expr.mk_app `(xtrm.fn) 
    [k.to_expr, (foldr (λ x y, expr.mk_app `(xtrm.cons) [x, y]) `(xtrm.nil) (trms.dlmap f))])

def vnew : trm → nat :=
rec succ (λ _ _ f, nats.max (trms.dlmap f))

lemma vnew_fn (k : nat) (ts : trms) :
  vnew (f* k ts) = nats.max (trms.lmap vnew ts) := 
by { unfold vnew, unfold rec, 
    apply congr_arg, apply trms.dlmap_eq_lmap }

def fnew : trm → nat :=
rec (λ _, 0) (λ k _ f, nat.max (k + 1) (nats.max (trms.dlmap f)))

def vinc (m n : nat) : trm → trm :=
rec 
  (λ k, v* (if k < m then k else k + n)) 
  (λ k ts f, f* k (trms.dtmap f))

lemma vinc_vr (k m n : nat) : 
  vinc m n (v* k) = v* (if k < m then k else k + n) := rfl

lemma vinc_fn (k m n : nat) (ts : trms) : 
  vinc m n (f* k ts) = f* k (trms.tmap (vinc m n) ts) :=
by { unfold vinc, unfold rec,
     apply congr_arg, apply trms.dtmap_eq_tmap }


lemma val_vr (F : fns α) (V : vas α) (k : nat) : 
  val F V (v* k) = V k := rfl

lemma val_fn (F : fns α) (V : vas α) (k : nat) (ts : trms) : 
  val F V (f* k ts) = F k (trms.lmap (val F V) ts) := 
by { unfold val, rec_fn_l }

def finc : trm → trm :=
rec 
  (λ k, v* k)
  (λ k ts f, f* (k + 1) (trms.dtmap f))
  
lemma finc_vr (k : nat) :
  finc (v* k) = v* k := rfl

lemma finc_fn (k : nat) (ts : trms) :
  finc (f* k ts) = f* (k + 1) (trms.tmap finc ts) :=
by { unfold finc, rec_fn_t }

def vdec (m : nat) : trm → trm :=
rec 
  (λ k, v* (if m < k then k - 1 else k))
  (λ k ts f, f* k (trms.dtmap f))

lemma vdec_vr (k m : nat) : 
  vdec m (v* k) = v* (if m < k then k - 1 else k) := rfl

lemma vdec_fn (k m : nat) (ts : trms) : 
  vdec m (f* k ts) = f* k (trms.tmap (vdec m) ts) := 
by { unfold vdec, rec_fn_t }

def vsub (m : nat) (r : trm) : trm → trm :=
rec 
  (λ k, if k = m then r else v* k)
  (λ k ts f, f* k (trms.dtmap f))

lemma vsub_vr (k m : nat) (r : trm) : 
  vsub m r (v* k) = 
  if k = m then r else v* k := rfl

lemma vsub_fn (k m : nat) (r : trm) (ts : trms) : 
  vsub m r (f* k ts) = f* k (trms.tmap (vsub m r) ts) := 
by { unfold vsub, rec_fn_t }

def vsubs (μs : vmaps) : trm → trm :=
rec
  (λ k, option.rec (v* k) id (μs.get k)) 
  (λ k ts f, f* k (trms.dtmap f))

lemma vsubs_vr (μs : vmaps) (k : nat) : 
  vsubs μs (v* k) = 
  option.rec (v* k) id (μs.get k) := rfl

lemma vsubs_fn (μs : vmaps) (k : nat) (ts : trms) : 
  vsubs μs (f* k ts) = f* k (trms.tmap (vsubs μs) ts) := 
by { unfold vsubs, rec_fn_t }

def farity (m : nat) : trm → option nat :=
rec 
  (λ _, none)
  (λ k ts f, if k = m 
             then some (trms.length ts) 
             else (trms.dlmap f).orelse)

def vocc (m : nat) : trm → Prop :=
rec (λ k, k = m) (λ _ _ f, (trms.dlmap f).disj)

lemma exists_mem_cons_iff 
  (p : trm → Prop) (t : trm) (ts : trms) :
  (∃ x ∈ (t ::* ts), p x) ↔ p t ∨ ∃ x ∈ ts, p x :=
by { constructor,
     { rintro ⟨s, h0, h1⟩, 
       rw trms.mem_cons_iff at h0,
       cases h0,
       { left, rw ← h0, exact h1 },
       right, refine ⟨s, h0, h1⟩ },
     rintro (h0 | ⟨s, h0, h1⟩),
     { refine ⟨t, or.inl rfl, h0⟩ },
     refine ⟨s, or.inr h0, h1⟩ }

lemma disj_iff_exists_mem (p : trm → Prop) :
  ∀ ts : trms, (trms.lmap p ts).disj ↔ ∃ x ∈ ts, p x
| []*        := by constructor; rintro ⟨_, ⟨_⟩, _⟩
| (t ::* ts) := 
  by { unfold trms.lmap,
       rw [disj_cons, exists_mem_cons_iff,
         disj_iff_exists_mem ts] }

lemma vocc_fn (k m : nat) (ts : trms) : 
  vocc m (f* k ts) ↔ ∃ t ∈ ts, trm.vocc m t := 
by { have h0 : vocc m (f* k ts) = (trms.lmap (vocc m) ts).disj,
     { unfold vocc, unfold rec,
       apply congr_arg, apply trms.dlmap_eq_lmap },
     rw h0, apply disj_iff_exists_mem }
  
def replace (t s : trm) : trm → trm :=
rec
  (λ k, if (v* k) = t then s else (v* k))
  (λ k ts f, if f* k ts = t 
             then s 
             else f* k (trms.dtmap f))
            
lemma replace_vr (k : nat) (t s : trm) :
  trm.replace t s (v* k) = 
  if (v* k) = t then s else (v* k) := rfl

lemma replace_fn (k : nat) (t s : trm) (ts : trms) :
  trm.replace t s (f* k ts) = 
  if f* k ts = t 
  then s 
  else f* k (trms.tmap (trm.replace t s) ts) :=
by { unfold replace, unfold rec,
     by_cases h0 : f* k ts = t, 
     { rw [if_pos h0, if_pos h0] },
     rw [if_neg h0, if_neg h0],
     apply congr_arg,
     apply trms.dtmap_eq_tmap } 

lemma val_vsubs (F : fns α) (V : vas α) (μs : vmaps) :
  ∀ t : trm, (t.vsubs μs).val F V = t.val F (V.vsubs F μs) :=  
trm.rec 
 (begin
    intro k, 
    rw [trm.vsubs_vr, trm.val_vr],
    unfold vas.vsubs,
    cases (μs.get k); refl
  end)
 (begin
    intros k ts ih,
    rw [trm.vsubs_fn, trm.val_fn, 
      trm.val_fn, trms.lmap_tmap],
    apply congr_arg,
    apply trms.lmap_eq_lmap ih
  end)

lemma val_replace {t s : trm} (h0 : t.val F V = s.val F V) : 
  ∀ r : trm, (trm.replace t s r).val F V = r.val F V :=
trm.rec 
 (begin
    intro k,
    rw replace_vr,
    by_cases h1 : (v* k = t),
    { rw [if_pos h1, h1, h0] },
    rw if_neg h1
  end)
 (begin
    intros k ts ih, 
    rw replace_fn,
    by_cases h1 : f* k ts = t,
    { rw [if_pos h1, h1, h0] },
    rw [if_neg h1, trm.val_fn, 
      val_fn, trms.lmap_tmap],
    apply congr_arg,
    apply trms.lmap_eq_lmap ih
  end)
end trm

def trms.repr (ts : trms) : string :=
string.tuplize (trms.lmap trm.repr ts)

meta def trmlst.to_expr : list trm → expr 
| []        := `(@list.nil trm)
| (t :: ts) := 
  expr.mk_app `(@list.cons trm) [t.to_expr, trmlst.to_expr ts]

inductive atm : Type 
| rl : nat → list trm → atm
| eq : trm → trm →  atm

local notation `r*`     := atm.rl 
local notation t `=*` s := atm.eq t s 

namespace atm

def repr : atm → string
| (atm.rl k ts) := "r" ++ k.to_subs ++ string.tuplize (ts.map trm.repr)
| (atm.eq t s) := t.repr ++ " = " ++ s.repr

meta def to_expr : atm → expr
| (atm.rl k ts) := 
  expr.mk_app `(atm.rl) [k.to_expr, trmlst.to_expr ts]
| (atm.eq t s) := 
  expr.mk_app `(atm.eq) [t.to_expr, s.to_expr]

def vnew : atm → nat
| (atm.rl _ ts) := nats.max (ts.map trm.vnew)
| (atm.eq t s)  := nat.max t.vnew s.vnew

def fnew : atm → nat
| (atm.rl _ ts) := nats.max (ts.map trm.fnew)
| (atm.eq t s)  := nat.max t.fnew s.fnew

def rnew : atm → nat
| (atm.rl k _) := k + 1
| (atm.eq _ _) := 0

def vinc (m n : nat) : atm → atm
| (atm.rl k ts) := atm.rl k (ts.map $ trm.vinc m n)
| (atm.eq t s)  := atm.eq (t.vinc m n) (s.vinc m n)

def default : atm := atm.eq (f* 0 []*) (f* 0 []*)

def holds (R : rls α) (F : fns α) (V : vas α) : atm → Prop
| (atm.rl k ts) := R k (ts.map $ trm.val F V)
| (atm.eq t s)  := t.val F V = s.val F V

def vdec (m : nat) : atm → atm
| (atm.rl k ts) := atm.rl k (ts.map $ trm.vdec m)
| (atm.eq t s)  := atm.eq (t.vdec m) (s.vdec m)

def finc : atm → atm
| (atm.rl k ts) := atm.rl k (ts.map trm.finc) 
| (atm.eq t s)  := atm.eq t.finc s.finc

def vsub (m : nat) (r : trm) : atm → atm
| (atm.rl k ts) := atm.rl k (ts.map $ trm.vsub m r)
| (atm.eq t s)  := atm.eq (trm.vsub m r t) (trm.vsub m r s)

def vsubs (μs : vmaps) : atm → atm
| (atm.rl k ts) := atm.rl k (ts.map $ trm.vsubs μs)
| (atm.eq t s)  := atm.eq (t.vsubs μs) (s.vsubs μs)


def rarity (m : nat) : atm → option nat
| (atm.rl k ts) := if k = m then some ts.length else none
| (atm.eq _ _)  := none 

def farity (m : nat) : atm → option nat
| (atm.rl k ts) := (ts.map $ trm.farity m).orelse
| (atm.eq t s)  := t.farity m <|> s.farity m 

def vocc (m : nat) : atm → Prop
| (atm.rl _ ts) := ∃ t ∈ ts, trm.vocc m t
| (atm.eq t s)  := t.vocc m ∨ s.vocc m

def replace (r u : trm) : atm → atm
| (atm.rl k ts) := atm.rl k (ts.map $ trm.replace r u)
| (atm.eq t s)  := atm.eq (trm.replace r u t) (trm.replace r u s) 

lemma holds_vsubs (μs : vmaps) :
  ∀ a : atm,
  (a.vsubs μs).holds R F V ↔
  a.holds R F (V.vsubs F μs) 
| (r* k ts) := 
  begin
    unfold vsubs,
    unfold holds,
    rw list.map_map,
    have h0 : trm.val F V ∘ trm.vsubs μs = 
      trm.val F (vas.vsubs F μs V),
    { apply funext, intro x,
      apply trm.val_vsubs },
    rw h0,
  end
| (t =* s)  := 
  begin
    unfold vsubs,
    unfold holds,
    repeat {rw trm.val_vsubs},
  end

lemma holds_replace {r u : trm} 
  (h0 : r.val F V = u.val F V) : 
  ∀ a : atm, (a.replace r u).holds R F V ↔ a.holds R F V 
| (r* k ts) := 
  begin
    have h3 : ((trm.val F V) ∘ trm.replace r u) = (trm.val F V),
       { apply funext, intro x,
         apply trm.val_replace h0 },
    unfold replace, 
    unfold holds,
    rw [ list.map_map, h3 ],
  end
| (t =* s) := 
  begin
    unfold replace, 
    unfold holds, 
    rw [ trm.val_replace h0,
         trm.val_replace h0 ]
  end

end atm

inductive frm : Type
| atm : bool → atm → frm
| bin : bool → frm → frm → frm
| qua : bool → frm → frm

local notation `+*`     := frm.atm tt
local notation `-*`     := frm.atm ff
local notation p `∨*` q := frm.bin tt p q
local notation p `∧*` q := frm.bin ff p q
local notation `∃*` p   := frm.qua tt p
local notation `∀*` p   := frm.qua ff p

namespace frm

def repr : frm → string
| (+* a)   :=          a.repr
| (-* a)   := "¬"   ++ a.repr
| (p ∨* q) := "("   ++ p.repr ++ " ∨ " ++ q.repr ++ ")"
| (p ∧* q) := "("   ++ p.repr ++ " ∧ " ++ q.repr ++ ")"
| (∀* p)   := "(∀ " ++ p.repr ++ ")"
| (∃* p)   := "(∃ " ++ p.repr ++ ")"

instance has_repr : has_repr frm := ⟨repr⟩

meta instance has_to_format : has_to_format frm := ⟨λ x, repr x⟩

meta def to_expr : frm → expr
| (frm.atm b a)   := expr.mk_app `(frm.atm) [b.to_expr, a.to_expr]
| (frm.bin b f g) := expr.mk_app `(frm.bin) [b.to_expr, f.to_expr, g.to_expr]
| (frm.qua b f)   := expr.mk_app `(frm.qua) [b.to_expr, f.to_expr]

def rnew : frm → nat
| (frm.atm _ a)   := a.rnew
| (frm.bin _ f g) := nat.max f.rnew g.rnew
| (frm.qua _ f)   := f.rnew

def fnew : frm → nat
| (frm.atm _ a)   := a.fnew
| (frm.bin _ f g) := nat.max (f.fnew) (g.fnew)
| (frm.qua _ f)   := f.fnew

def vnew : frm → nat
| (frm.atm _ a)   := a.vnew
| (frm.bin _ f g) := nat.max f.vnew g.vnew
| (frm.qua _ f)   := f.vnew - 1

def vinc : nat → nat → frm → frm
| m n (frm.atm b a)   := frm.atm b (a.vinc m n)
| m n (frm.bin b f g) := frm.bin b (f.vinc m n) (g.vinc m n)
| m n (frm.qua b f)   := frm.qua b (f.vinc (m + 1) n)

def default : frm := +* atm.default 

def holds (R : rls α) (F : fns α) : vas α → frm → Prop
| V (+* a)   :=   a.holds R F V
| V (-* a)   := ¬ a.holds R F V
| V (p ∨* q) := p.holds V ∨ q.holds V
| V (p ∧* q) := p.holds V ∧ q.holds V
| V (∀* p)   := ∀ x : α, p.holds (V ₀↦ x)
| V (∃* p)   := ∃ x : α, p.holds (V ₀↦ x)

def neg : frm → frm
| (frm.atm b a)   := frm.atm (bnot b) a
| (frm.bin b f g) := frm.bin (bnot b) f.neg g.neg
| (frm.qua b f)   := frm.qua (bnot b) f.neg

def vdec : nat → frm → frm
| m (frm.atm b a)   := frm.atm b (a.vdec m)
| m (frm.bin b f g) := frm.bin b (f.vdec m) (g.vdec m)
| m (frm.qua b f)   := frm.qua b (f.vdec $ m + 1)

def finc : frm → frm
| (frm.atm b a)   := frm.atm b a.finc
| (frm.bin b f g) := frm.bin b f.finc g.finc
| (frm.qua b f)   := frm.qua b f.finc

def vsub : nat → trm → frm → frm
| k t (frm.atm b a)   := frm.atm b (a.vsub k t)
| k t (frm.bin b f g) := frm.bin b (f.vsub k t) (g.vsub k t)
| k t (frm.qua b f)   := frm.qua b (f.vsub (k + 1) (t.vinc 0 1))

def fvx (R : rls α) (F : fns α) : nat → vas α → frm → Prop
| 0       V f := f.holds R F V
| (k + 1) V f := ∀ x : α, fvx k (V ₀↦ x) f

def rarity_core (rdx : nat) : frm → option nat
| (frm.atm b a)   := a.rarity rdx
| (frm.bin _ f g) := f.rarity_core <|> g.rarity_core
| (frm.qua _ f)   := f.rarity_core

def rarity (rdx : nat) (f : frm) : nat :=
option.get_or_else (f.rarity_core rdx) 0

def farity_core (fdx : nat) : frm → option nat
| (frm.atm _ a)   := a.farity fdx
| (frm.bin _ f g) := f.farity_core <|> g.farity_core
| (frm.qua _ f)   := f.farity_core

def farity (fdx : nat) (f : frm) : nat :=
option.get_or_else (f.farity_core fdx) 0

def ffx [inhabited α] (R : rls α) : nat → fns α → frm → Prop
| 0       F f := f.holds R F (Vdf α)
| (m + 1) F f := ∀ x : nfn α (f.farity m), f.ffx m (F ₀↦ x.unfix)

def frxffx [inhabited α] : nat → rls α → nat → fns α → frm → Prop
| 0       R m F f := f.ffx R m F
| (k + 1) R m F f := ∀ x : nrl α (f.rarity k), f.frxffx k (R ₀↦ x.unfix) m F

def vocc : frm → nat → Prop
| (frm.atm _ a)   k := a.vocc k
| (frm.bin _ f g) k := f.vocc k ∨ g.vocc k
| (frm.qua _ f)   k := f.vocc (k + 1)

def cons_qua_count : frm → nat
| (frm.qua _ f) := f.cons_qua_count + 1
| _             := 0

def F : frm → Prop
| (frm.atm _ a)   := true
| (frm.bin _ p q) := F p ∧ F q
| (frm.qua _ p)   := false

def QF : frm → Prop
| (frm.qua _ f) := f.QF 
| f             := f.F

instance F.decidable : decidable_pred frm.F
| (frm.atm _ _)   := decidable.true
| (frm.bin _ f g) :=
  @and.decidable _ _ (F.decidable f) (F.decidable g)
| (frm.qua _ _)   := decidable.false

def AF : frm → Prop
| (∀* f) := AF f
| (∃* _) := false
| f      := f.F

instance AF.decidable : decidable_pred AF
| (frm.atm _ _)   := frm.F.decidable _
| (frm.bin _ _ _) := frm.F.decidable _
| (∀* f)          := AF.decidable f
| (∃* f)          := decidable.false

def strip_fa : frm → frm
| (∀* f) := strip_fa f
| f      := f

end frm

/- Lemmas -/

variables {b : bool} (f f1 f2 g g1 g2 : frm)

lemma holds_neg : ∀ {V : vas α} {f : frm},
  (f.neg.holds R F V) ↔ ¬ (f.holds R F V)
| _ (+* a)   := iff.refl _
| _ (-* a)   := 
  by simp only [ frm.neg, frm.holds,
       bnot, classical.not_not ]
| _ (p ∨* q) :=
  begin
    unfold frm.holds,
    rw not_or_distrib,
    apply pred_mono_2;
    apply holds_neg
  end
| _ (p ∧* q) :=
  begin
    unfold frm.holds,
    rw @not_and_distrib _ _ (classical.dec _),
    apply pred_mono_2; apply holds_neg
  end
| _ (∀* p)   :=
  begin
    unfold frm.holds,
    rw @not_forall _ _ (classical.dec _) (classical.dec_pred _),
    apply exists_congr,
    intro v, apply holds_neg
  end
| _ (∃* p)   :=
  begin
    unfold frm.holds,
    rw @not_exists,
    apply forall_congr,
    intro v, apply holds_neg
  end

def ext (k : nat) (f g : nat → β) : Prop := ∀ m, f (m + k) = g m

lemma ext_zero_refl (f : nat → β) : ext 0 f f := λ _, rfl

lemma eq_of_ext_zero {f f' : nat → β} :
  ext 0 f f' → f = f' :=
by { intros h0, apply funext, intro k, apply h0 }

lemma ext_succ {k : nat} {f g : nat → β} {b : β} :
  ext k f (g ₀↦ b) → ext (k + 1) f g :=
begin
  intros h0 m,
  apply eq.trans _ (h0 (m + 1)),
  apply congr_arg,
  rw add_assoc,
  apply congr_arg _ (add_comm _ _)
end

lemma ext_assign {k : nat} {f g : nat → β} :
  ext (k + 1) f g → ext k f (g ₀↦ f k) :=
by { rintros h0 ⟨m⟩,
     { rw zero_add, refl },
     simp only [nat.succ_add, assign, (h0 m).symm],
     refl }

def forall_ext (k : nat) (f : nat → β) (p : (nat → β) → Prop) : Prop :=
∀ f' : nat → β, ext k f' f → p f'

def exists_ext (k : nat) (f : nat → β) (p : (nat → β) → Prop) : Prop :=
∃ f' : nat → β, ext k f' f ∧ p f'

local notation F `∀⟹` k := forall_ext k F
local notation F `∃⟹` k := exists_ext k F

lemma trm.val_eq_val (F : fns α) {V W : vas α} :
  ∀ t : trm, (∀ m : nat, t.vocc m → V m = W m) →
  (t.val F V = t.val F W) :=
trm.rec 
  (begin 
     intros k h0, 
     apply h0 k rfl,
   end) 
  (begin
     intros k ts ih h0,
     rw [trm.val_fn, trm.val_fn],
     apply congr_arg,
     apply trms.lmap_eq_lmap,
     intros t h1, apply ih _ h1,
     intros m h2, apply h0,
     rw trm.vocc_fn,
     refine ⟨t, h1, h2⟩
   end)

lemma atm.holds_iff_holds {l : atm} {V W : vas α} 
  (h0 : ∀ m : nat, l.vocc m → V m = W m) :
  (l.holds R F V ↔ l.holds R F W) :=
begin
  cases l with k ts t s,
  { have h1 : ts.map (λ x, x.val F V) = ts.map (λ x, x.val F W),
    { apply list.map_eq_map_of_forall_mem_eq,
      intros t h1,
      rw trm.val_eq_val,
      intros m h2,
      apply h0 _ ⟨t, h1, h2⟩ },
    unfold atm.holds; rw h1 },
  unfold atm.holds,
  rw [ trm.val_eq_val F t,
       trm.val_eq_val F s ];
  intros k h1; apply h0,
  { right, exact h1 },
  left, exact h1 
end

lemma holds_iff_holds  :
  ∀ f : frm, ∀ V W : vas α,
  (∀ m : nat, f.vocc m → V m = W m) →
  (f.holds R F V ↔ f.holds R F W)
| (frm.atm b a) V W h0 := 
  by { cases b; unfold frm.holds;
       rw atm.holds_iff_holds h0 }
| (frm.bin b f g) V W h0 :=
  begin
    cases b;
    apply pred_mono_2;
    apply holds_iff_holds;
    intros m h1; apply h0;
    try {left, assumption};
    right; assumption
  end
| (frm.qua b f) V W h0 :=
  begin
    cases b;
    try {apply forall_congr};
    try {apply exists_congr};
    intro a; apply holds_iff_holds;
    intros m h1; cases m with m;
    try {refl}; apply h0; exact h1
  end

lemma trms.mem_lmap {s : trm} {f : trm → A} :
  ∀ {ts : trms}, s ∈ ts → f s ∈ trms.lmap f ts 
| []*        := by rintro ⟨_⟩ 
| (t ::* ts) := 
  by { intro h0,
       rw trms.mem_cons_iff at h0,
       unfold trms.lmap, cases h0,
       { subst h0, apply or.inl rfl },
       right, apply trms.mem_lmap h0 }
 
lemma trm.lt_of_vnew_le {m n : nat} :
  ∀ {t : trm}, t.vnew ≤ m → t.vocc n → n < m :=
trm.rec 
 (begin 
    rintros k h0 ⟨h1⟩ ,
    apply nat.lt_of_succ_le h0,
  end)
 (begin 
    intros k ts ih h0 h1,
    rw trm.vocc_fn at h1,
    rcases h1 with ⟨t, h2, h3⟩,
    apply ih _ h2 _ h3,
    rw trm.vnew_fn at h0,
    apply le_trans _ h0,
    apply nats.le_max_of_mem,
    apply trms.mem_lmap h2
  end)

lemma atm.lt_of_vnew_le :
  ∀ {l : atm}, ∀ {k m : nat},
  l.vnew ≤ k → l.vocc m → m < k
| (atm.rl _ ts) k m h0 h1 :=
  by { rcases h1 with ⟨t, h2, h3⟩, 
       apply trm.lt_of_vnew_le _ h3,
       apply le_trans _ h0,
       apply nats.le_max_of_mem,
       apply list.mem_map_of_mem trm.vnew h2 }
| (atm.eq t s) k m h0 h1 :=
  by { have ht := le_trans (nat.le_max_left t.vnew s.vnew) h0,
       have hs := le_trans (nat.le_max_right t.vnew s.vnew) h0,
       cases h1;
       apply trm.lt_of_vnew_le _ h1;
       assumption }

lemma frm.lt_of_vnew_le :
  ∀ {f : frm}, ∀ {k m : nat},
  f.vnew ≤ k → f.vocc m → m < k
| (frm.atm _ _) k m h0 h1 :=
  atm.lt_of_vnew_le h0 h1
| (frm.bin _ f g) k m h0 h1 :=
  begin
    cases h1;
    apply frm.lt_of_vnew_le _ h1,
    { apply le_trans (nat.le_max_left f.vnew g.vnew) h0 },
    apply le_trans (nat.le_max_right f.vnew g.vnew) h0,
  end
| (frm.qua _ f) k m h0 h1 :=
  begin
    rw ← nat.succ_lt_succ_iff,
    apply @frm.lt_of_vnew_le f (k + 1) (m + 1) _ h1,
    unfold frm.vnew at h0,
    cases f.vnew with n,
    { apply nat.zero_le },
    rw nat.succ_le_succ_iff,
    apply h0
  end

lemma ffx_of_forall_fxt [inhabited α] {R : rls α} :
  ∀ {m : nat} {F : fns α} {f : frm},
  (F ∀⟹ m) (λ F', (f.holds R F' (Vdf α))) → f.ffx R m F
| 0       F f h0 := h0 _ (ext_zero_refl _)
| (m + 1) F f h0 :=
  begin
    intro x,
    apply ffx_of_forall_fxt,
    intros F' h1, apply h0,
    apply ext_succ h1,
  end

lemma frxffx_of_forall_rxt [inhabited α] :
  ∀ {k : nat} {R : rls α} {m : nat} {F : fns α} {f : frm},
  (R ∀⟹ k) (λ R', (F ∀⟹ m) (λ F', f.holds R' F' (Vdf α))) →
  f.frxffx k R m F
| 0 R m F f h0 :=
  by { apply ffx_of_forall_fxt,
       apply h0 _ (ext_zero_refl _) }
| (k + 1) R m F f h0 :=
  begin
    intro x,
    apply frxffx_of_forall_rxt,
    intros R' h1, apply h0,
    apply ext_succ h1
  end

def prepend (k : nat) (f g : nat → β) : nat → β
| m := if m < k then f m else g (m - k)

lemma ext_prepend (k : nat) (f g : nat → β) :
  ext k (prepend k f g) g
| m :=
  begin
    unfold prepend,
    rw if_neg,
    { rw nat.add_sub_cancel },
    rw not_lt,
    apply nat.le_add_left,
  end

lemma forall_ext_holds_of_fvx :
  ∀ k : nat, ∀ V : vas α,
  f.fvx R F k V → ∀ W : vas α, ext k W V → f.holds R F W 
| 0 V h0 W h1 :=
  begin
    have h2 : W = V,
    { apply funext h1 },
    rw h2, exact h0
  end
| (k + 1) V h0 W h1 :=
  begin
    unfold frm.fvx at h0,
    apply forall_ext_holds_of_fvx k (V ₀↦ W k) (h0 _) W,
    intro m, cases m with m,
    { rw zero_add, refl },
    rw nat.succ_add, apply h1
  end

lemma holds_of_forall_vxt_holds {k : nat} {f : frm} :
  f.vnew ≤ k → (V ∀⟹ k) (λ V', f.holds R F V') →
  ∀ W : vas α, f.holds R F W :=
  begin
    intros h0 h1 W,
    rw holds_iff_holds f W (prepend k W V) _,
    { apply h1, apply ext_prepend },
    intros m h2,
    unfold prepend,
    rw if_pos,
    apply frm.lt_of_vnew_le h0 h2,
  end

lemma ext_comp_of_ext_succ {k : nat} {f g : nat → β} :
  ext (k + 1) f g → ext k (f ∘ nat.succ) g :=
by { intros h0 m, rw ← (h0 m), refl }

lemma forall_vxt_succ_holds {k : nat} {f : frm} :
  (V ∀⟹ k + 1) (λ V', f.holds R F V') ↔
  (V ∀⟹ k) (λ V', (∀* f).holds R F V') :=
by { constructor; intros h0 V' h1,
     { intro a,
       apply h0 (V' ₀↦ a) h1 },
     have h2 : V' = ((V' ∘ nat.succ) ₀↦ V' 0),
     { apply funext,
       rintro ⟨m⟩; refl },
     rw h2,
     apply h0 (V' ∘ nat.succ)
       (ext_comp_of_ext_succ h1) (V' 0) }

lemma vnew_neg :
  ∀ f : frm, f.neg.vnew = f.vnew
| (frm.atm _ _)   := rfl
| (frm.bin _ f g) :=
  by simp only [frm.neg, frm.vnew,
       vnew_neg f, vnew_neg g]
| (frm.qua _ f)   :=
  by simp only [frm.neg, frm.vnew, vnew_neg f]

lemma forall_ext_zero :
  ∀ {f : frm}, (f.holds R F V) →
  (V ∀⟹ 0) (λ V', f.holds R F V') :=
begin
  intros f h0 V' h1,
  have h2 : V' = V,
  { apply funext (λ k, _),
    rw ← h1 k, refl },
  rw h2, exact h0
end

lemma holds_strip_fa :
  ∀ {f : frm} {k : nat}, 
  f.AF → f.vnew ≤ k →
  (V ∀⟹ k) (λ V', f.holds R F V') →
  ∀ W : vas α, f.strip_fa.holds R F W
| (frm.atm _ _) k h0 h1 h2 W :=
  begin
    unfold frm.strip_fa,
    apply holds_of_forall_vxt_holds h1 h2
  end
| (frm.bin b f g) k h0 h1 h2 W :=
  begin
    unfold frm.strip_fa,
    apply holds_of_forall_vxt_holds h1 h2
  end
| (∃* f) k h0 h1 h2 W := by cases h0
| (∀* f) k h0 h1 h2 W :=
  begin
    unfold frm.AF at h0,
    unfold frm.vnew at h1,
    unfold frm.strip_fa,
    rw ← forall_vxt_succ_holds at h2,
    apply holds_strip_fa h0 _ h2,
    cases f.vnew,
    { apply nat.zero_le },
    apply nat.succ_le_succ h1,
  end

lemma F_strip_fa :
  ∀ f : frm, f.AF → f.strip_fa.F
| (frm.atm _ _) h   := trivial
| (frm.bin _ f g) h := h
| (∀* f) h          := F_strip_fa f h
| (∃* f) h          := by cases h

lemma holds_bin_of_holds_bin {R' : rls α} {F' : fns α}
  {V' : vas α} {b : bool} {f g f' g' : frm} :
  (f.holds R F V → f'.holds R' F' V') →
  (g.holds R F V → g'.holds R' F' V') →
  (frm.bin b f g).holds R F V →
  (frm.bin b f' g').holds R' F' V' :=
begin
  intros h0 h1 h2, cases b,
  { refine ⟨h0 h2.left, h1 h2.right⟩ },
  cases h2,
  { left, apply h0 h2 },
  right, apply h1 h2
end

end vampire