/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Pulling quantifiers for Skolemization and prenex normalization.
-/

import algebra.order
import tactic.rcases
import data.nat.basic
import tactic.vampire.frm

namespace vampire

open nat

variables {α : Type}
variables {R : rls α} {F : fns α} {V : vas α}

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
local notation R `;` F `;` V `⊨` f := frm.holds R F V f

def pull_core (b : bool) : nat → frm → frm → frm
| 0       f      g      := frm.bin b f g
| (k + 1) (∀* f) g      := ∀* (pull_core k f (g.vinc 0 1))
| (k + 1) f      (∀* g) := ∀* (pull_core k (f.vinc 0 1) g)
| (k + 1) (∃* f) g      := ∃* (pull_core k f (g.vinc 0 1))
| (k + 1) f      (∃* g) := ∃* (pull_core k (f.vinc 0 1) g)
| (k + 1) _      _      := frm.default

def pull (b : bool) (f g : frm) : frm :=
pull_core b (f.cons_qua_count + g.cons_qua_count) f g

def eqv (α : Type) (f g : frm) : Prop :=
∀ R : rls α, ∀ F : fns α, ∀ V : vas α, ((R ; F ; V ⊨ f) ↔ (R ; F ; V ⊨ g))

notation p `<==` α `==>` q := eqv α p q

lemma eqv_refl (f : frm) : f <==α==> f := λ _ _ _, iff.rfl

lemma eqv_trans {α : Type} {f g h : frm} :
  (f <==α==> g) → (g <==α==> h) → (f <==α==> h) :=
λ h0 h1 R F V, iff.trans (h0 _ _ _) (h1 _ _ _)

lemma qua_eqv_qua {p q : frm} {b : bool} :
  (p <==α==> q) → (frm.qua b p <==α==> frm.qua b q) :=
begin
  intros h0 R F V,
  cases b,
  { apply forall_congr,
    intro a, apply h0 },
  apply exists_congr,
  intro a, apply h0
end

def insert_result {α : Type} (k : nat) (V W : vas α) : Prop :=
  (∀ m < k, V m = W m) ∧ (∀ m ≥ k, V (m + 1) = W m)

lemma trm.val_vinc
  {k : nat} {V W : vas α} (h0 : insert_result k V W) :
  ∀ t : trm, (t.vinc k 1).val F V = t.val F W :=
trm.rec 
 (begin
    intro m,
    rw trm.vinc_vr,
    by_cases h1 : m < k,
    { rw if_pos h1,
      unfold trm.val,
      apply h0.left _ h1 },
    rw if_neg h1,
    rw not_lt at h1,
    apply h0.right _ h1
  end)
 (begin
    intros k ts ih, 
    rw [trm.vinc_fn, trm.val_fn, trm.val_fn],
    apply congr_arg,
    rw trms.lmap_tmap,
    apply trms.lmap_eq_lmap ih
  end)

lemma atm.holds_vinc {R : rls α} {F : fns α}
  {m : nat} {V W : vas α} (h0 : insert_result m V W) :
  ∀ a : atm, (a.vinc m 1).holds R F V = a.holds R F W
| (r* k ts) := 
  by { have h1 : (trm.val F V ∘ trm.vinc m 1) = trm.val F W,
       { apply funext, intro x,
         apply trm.val_vinc h0 },
       unfold atm.vinc,
       unfold atm.holds,
       apply congr_arg,
       rw [list.map_map, h1] }
| (t =* s) := 
  by { unfold atm.vinc, unfold atm.holds,
       rw [trm.val_vinc h0, trm.val_vinc h0] }


lemma neg_vinc :
  ∀ k : nat, ∀ f : frm, (f.vinc k 1).neg = f.neg.vinc k 1
| k (frm.atm b a)   := by cases b; refl
| k (frm.bin b p q) :=
  by simp only [frm.neg, frm.vinc,
     eq_self_iff_true, neg_vinc, and_self ]
| k (frm.qua b p) :=
  by simp only [frm.neg, frm.vinc,
     eq_self_iff_true, neg_vinc, and_self ]


lemma neg_eqv_neg (f g : frm) :
  (f.neg <==α==> g.neg) ↔ (f <==α==> g) :=
begin
  apply forall_congr, intro R,
  apply forall_congr, intro F,
  apply forall_congr, intro V,
  rw [holds_neg, holds_neg, @not_iff_not _ _ _ _],
  repeat {apply classical.dec _}
end

lemma holds_bin_iff_holds_bin
  {R1 R2 : rls α} {F1 F2 : fns α} {V1 V2 : vas α} 
  {f1 f2 g1 g2 : frm} {b : bool} :
  (f1.holds R1 F1 V1 ↔ f2.holds R2 F2 V2) →
  ((R1 ; F1; V1 ⊨ g1) ↔ (R2; F2; V2 ⊨ g2)) →
  ( (R1 ; F1 ; V1 ⊨ frm.bin b f1 g1) ↔
    (R2 ; F2 ; V2 ⊨ frm.bin b f2 g2) ) :=
by { intros h0 h1, cases b;
     apply pred_mono_2; assumption }

lemma holds_qua_iff_holds_qua 
  (b : bool) (f g : frm) (R1 R2 : rls α) (F1 F2 : fns α) (V1 V2 : vas α) :
  (∀ a : α, (f.holds R1 F1 (V1 ₀↦ a)) ↔ (g.holds R2 F2 (V2 ₀↦ a))) →
  ((frm.qua b f).holds R1 F1 V1 ↔ (frm.qua b g).holds R2 F2 V2) :=
begin
  intro h0, cases b,
  apply forall_congr h0,
  apply exists_congr h0
end

lemma bin_eqv_bin 
  (b : bool) (f1 f2 g1 g2 : frm) :
  (f1 <==α==> f2) → (g1 <==α==> g2) →
  (frm.bin b f1 g1 <==α==> frm.bin b f2 g2) :=
by { intros h0 h1 R F V,
     apply holds_bin_iff_holds_bin (h0 _ _ _) (h1 _ _ _) }

lemma insert_result_zero (V : vas α) (a : α) :
  insert_result 0 (V ₀↦ a) V :=
⟨λ _ h, by cases h, λ _ _, rfl⟩

def insert_result_succ {k : nat} {V W : vas α} {a : α} :
   insert_result k V W →
   insert_result (k + 1) (V ₀↦ a) (W ₀↦ a) :=
begin
  rintro ⟨h0, h1⟩,
  constructor; intros m h2; cases m,
  { refl },
  { apply h0 _ (lt_of_succ_lt_succ h2) },
  { cases (not_lt_zero _ (lt_of_succ_le h2)) },
  apply h1 _ (succ_le_succ_iff.elim_left h2)
end

lemma frm.holds_vinc :
  ∀ {k : nat}, ∀ {V W : vas α}, (insert_result k V W) →
  ∀ f : frm, (f.vinc k 1).holds R F V ↔ f.holds R F W 
| k V W h0 (frm.atm b a)   := 
  by { cases b; unfold frm.vinc;
       unfold frm.holds;
       rw atm.holds_vinc h0 }
| k V W h0 (frm.bin b f g) :=
  by { apply holds_bin_iff_holds_bin;
       apply frm.holds_vinc h0 _ }
| k V W h0 (frm.qua b f) :=
  begin
    apply holds_qua_iff_holds_qua, intro v,
    apply @frm.holds_vinc (k + 1) _ _
      (insert_result_succ h0)
  end

lemma holds_vinc_zero (a : α) (f : frm) :
  (R ; F ; (V ₀↦ a) ⊨ f.vinc 0 1) ↔ (R ; F ; V ⊨ f) :=
frm.holds_vinc (insert_result_zero _ _) _

def fa_bin_vinc_zero [inhabited α] (b : bool) (f g : frm) :
  ∀* (frm.bin b f (g.vinc 0 1)) <==α==> frm.bin b (∀* f) g :=
begin
  intros R F V,
  have a : α := (default α),
  constructor; intro h0; cases b,
  { constructor,
    { intro w, exact (h0 w).left },
    rw ← holds_vinc_zero a g,
    exact (h0 a).right },
  { cases classical.em (R ; F ; (V ₀↦ a) ⊨ g.vinc 0 1) with h2 h2,
    { rw holds_vinc_zero at h2,
      right, exact h2 },
    left, intro w,
    cases (h0 w) with h3 h3,
    { exact h3 },
    rw holds_vinc_zero at h2,
    rw holds_vinc_zero at h3,
    cases (h2 h3) },
  { intro w,
    refine ⟨h0.left _, _⟩,
    rw holds_vinc_zero,
    exact h0.right },
  { intro w,
    cases classical.em (R ; F ; (V ₀↦ w) ⊨ g.vinc 0 1) with h1 h1,
    { right, exact h1 },
    left, cases h0 with h2 h2,
    { apply h2 },
    rw holds_vinc_zero at h1,
    cases (h1 h2) }
end
def ex_bin_vinc_zero [inhabited α] (b : bool) (f g : frm) :
  ∃* (frm.bin b f (g.vinc 0 1)) <==α==> (frm.bin b (∃* f) g) :=
by { rw ← neg_eqv_neg,
     simp only [ frm.neg, neg_vinc 0,
       bnot, fa_bin_vinc_zero ] }




def qua_bin_vinc_zero [inhabited α] (ae ao : bool) (p q : frm) :
  frm.qua ae (frm.bin ao p (q.vinc 0 1)) <==α==>
  frm.bin ao (frm.qua ae p) q :=
by { cases ae,
     apply fa_bin_vinc_zero,
     apply ex_bin_vinc_zero }



lemma bin_comm (b : bool) (p q : frm) :
  frm.bin b p q <==α==> frm.bin b q p :=
by { intros R F V, cases b, apply and.comm, apply or.comm }

def qua_vinc_zero_bin [inhabited α] (ae ao : bool) (p q : frm) :
  frm.qua ae (frm.bin ao (p.vinc 0 1) q) <==α==>
  frm.bin ao p (frm.qua ae q) :=
begin
  have h0 : (frm.qua ae (frm.bin ao (p.vinc 0 1) q) <==α==>
             frm.qua ae (frm.bin ao q (p.vinc 0 1))),
  { apply qua_eqv_qua (bin_comm _ _ _) },
  intros R F V,
  simp only [ h0 R F V, qua_bin_vinc_zero ae ao q p R F V,
    bin_comm ao p (frm.qua ae q) R F V ]
end


lemma cons_qua_count_vinc :
  ∀ f : frm, ∀ k : nat,
  (f.vinc k 1).cons_qua_count = f.cons_qua_count
| (frm.atm _ _)   k := rfl
| (frm.bin b f g) k := rfl
| (frm.qua b f) k   :=
  by simp only [frm.vinc,
      frm.cons_qua_count,
      cons_qua_count_vinc _ (k + 1)]

lemma pull_core_eqv [inhabited α] (b : bool) :
  ∀ (k : nat) {f g : frm},
  k = f.cons_qua_count + g.cons_qua_count →
  (pull_core b k f g <==α==> frm.bin b f g)
| 0       := λ f g h0, eqv_refl _
| (k + 1) :=
  begin
    intros f g h0,
    rcases f with ⟨bf, af⟩ | ⟨bf, f1, f2⟩ | ⟨_ | _, f⟩;
    rcases g with ⟨bf, ag⟩ | ⟨bg, g1, g2⟩ | ⟨_ | _, g⟩;
    try { apply false.elim (succ_ne_zero _ h0) } ;
    { apply eqv_trans (qua_eqv_qua $ pull_core_eqv k _),
      try { apply qua_vinc_zero_bin },
      try { apply qua_bin_vinc_zero },
      simp only [ frm.cons_qua_count, zero_add, add_zero,
        cons_qua_count_vinc, succ_add, add_def ] at *,
      apply succ_inj h0 },
  end

lemma F_vinc :
  ∀ f : frm, ∀ m : nat,
  f.F → (f.vinc m 1).F 
| (frm.atm _ _)   m h0 := trivial
| (frm.bin _ f g) m h0 :=
  by { cases h0, constructor;
       apply F_vinc; assumption }

lemma QF_vinc :
  ∀ f : frm, ∀ m : nat,
  f.QF → (f.vinc m 1).QF
| (frm.atm _ _)   m h0 := trivial
| (frm.bin _ f g) m h0 :=
  by { cases h0, constructor;
       apply F_vinc; assumption }
| (frm.qua _ f) m h0 := QF_vinc f _ h0

lemma pull_eqv [inhabited α] (b : bool) (f g : frm) :
  (pull b f g <==α==> frm.bin b f g) := pull_core_eqv _ _ rfl

lemma F_of_QF_of_cons_qua_count_eq_zero :
  ∀ f : frm, f.QF → f.cons_qua_count = 0 → f.F :=
by { intros f h0 h1, cases f with l b f g b f;
     try { trivial }, apply h0 }

lemma QF_pull_core (b : bool) :
  ∀ (k : nat) {f g : frm},
  f.QF → g.QF →
  k = f.cons_qua_count + g.cons_qua_count →
  (pull_core b k f g).QF
| 0 f g hf0 hg0 h1 :=
  begin
    cases eq_zero_of_add_eq_zero h1.symm with hf1 hg1,
    unfold pull_core, constructor;
    apply F_of_QF_of_cons_qua_count_eq_zero;
    assumption,
  end
| (k + 1) f g hf0 hg0 h1 :=
  begin
    rcases f with ⟨bf, af⟩ | ⟨bf, f1, f2⟩ | ⟨_ | _, f⟩;
    rcases g with ⟨bg, ag⟩ | ⟨bg, g1, g2⟩ | ⟨_ | _, g⟩;
    try { trivial };
    try {
      try { cases hf0 with hf00 hf01 },
      try { cases hg0 with hg00 hg01 },

      apply QF_pull_core k;
      try { trivial };
      try { assumption };
      try { constructor; apply F_vinc; assumption };
      try { apply QF_vinc; assumption },
      try { simp only [frm.cons_qua_count,
            cons_qua_count_vinc, add_assoc,
            succ_add] at * },
      apply succ_inj h1 }
  end

lemma QF_pull (b : bool) (f g : frm) :
  f.QF → g.QF → (pull b f g).QF :=
begin
  intros h0 h1,
  apply QF_pull_core _ _ _ _ rfl;
  assumption,
end

def pnf : frm → frm
| (frm.atm b a)   := frm.atm b a 
| (frm.bin b f g) := pull b (pnf f) (pnf g)
| (frm.qua b f)   := frm.qua b (pnf f)

lemma QF_pnf :
  ∀ f : frm, (pnf f).QF
| (frm.atm b a)   := trivial
| (frm.bin b f g) :=
  by { apply QF_pull; apply QF_pnf }
| (frm.qua b f)   := QF_pnf f

lemma pnf_eqv [inhabited α] :
  ∀ f : frm, pnf f <==α==> f
| (frm.atm _ _)   := eqv_refl _
| (frm.bin b f g) :=
  begin
    apply eqv_trans (@pull_eqv α _ _ _ _),
    apply bin_eqv_bin; apply pnf_eqv,
  end
| (frm.qua b f) := qua_eqv_qua (pnf_eqv _)

end vampire