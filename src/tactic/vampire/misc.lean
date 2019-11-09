/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Miscellaneous.
-/

import tactic.rcases
import data.nat.basic

universe u

variables {α β γ δ : Type u}

def string.tuplize : list string → string 
| []        := ""
| (s :: ss) := 
  "(" ++ list.foldl (λ s1 s2, s1 ++ "," ++ s2) s ss ++ ")" 

def spaces (k : nat) : string := ⟨list.repeat ' ' k⟩

def bool.repr : bool → string
| tt := "tt"
| ff := "ff"

meta def bool.to_expr : bool → expr
| ff := `(ff)
| tt := `(tt)

def option.if_is_some (p : α → Prop) : option α → Prop
| none     := true
| (some a) := p a

lemma bnot_eq_iff_ne {a b : bool} :
  bnot a = b ↔ a ≠ b :=
by cases a; cases b; simp only
   [bnot, ne, not_false_iff, eq_self_iff_true, not_true]

lemma eq_bnot_iff_ne {a b : bool} :
  a = bnot b ↔ a ≠ b :=
by cases a; cases b; simp only
   [bnot, ne, not_false_iff, eq_self_iff_true, not_true]

lemma ite_cases {r : α → Prop} {p : Prop} [decidable p] {a b : α} :
  r a → r b → r (ite p a b) :=
by { intros h0 h1, by_cases h2 : p,
     { rw if_pos h2, exact h0 },
     rw if_neg h2, exact h1 }

lemma dite_cases {r : α → Prop} {p : Prop} [decidable p] {a b : α} :
  (p → r a) → (¬ p → r b) → r (ite p a b) :=
by { intros h0 h1, by_cases h2 : p,
     { rw if_pos h2, exact h0 h2 },
       rw if_neg h2, exact h1 h2 }
       
lemma pred_mono_2 {c : Prop → Prop → Prop} {a1 a2 b1 b2 : Prop} :
  (a1 ↔ a2) → (b1 ↔ b2) → (c a1 b1 ↔ c a2 b2) :=
λ h1 h2, by rw [h1, h2]

lemma fun_mono_2 {f : α → β → γ} {a1 a2 : α} {b1 b2 : β} :
  (a1 = a2) → (b1 = b2) → (f a1 b1 = f a2 b2) :=
λ h1 h2, by rw [h1, h2]

def assign (a : α) (f : nat → α) : nat → α
| 0       := a
| (k + 1) := f k

def digit_to_subs : char → char
| '0' := '₀'
| '1' := '₁'
| '2' := '₂'
| '3' := '₃'
| '4' := '₄'
| '5' := '₅'
| '6' := '₆'
| '7' := '₇'
| '8' := '₈'
| '9' := '₉'
| _   := ' '

def nat.to_subs (n : nat) : string :=
⟨n.repr.data.map digit_to_subs⟩

def nat.max : nat → nat → nat 
| 0 m := m 
| k 0 := k 
| (k + 1) (m + 1) := (nat.max k m) + 1

lemma nat.le_max_left : ∀ k m : nat, k ≤ nat.max k m 
| 0       m       := nat.zero_le _
| k       0       := by cases k; apply le_refl 
| (k + 1) (m + 1) := 
  begin
    unfold nat.max,
    rw nat.succ_le_succ_iff,
    apply nat.le_max_left
  end

lemma nat.le_max_right : ∀ k m : nat, m ≤ nat.max k m 
| 0       m       := le_refl _
| k       0       := nat.zero_le _
| (k + 1) (m + 1) := 
  begin
    unfold nat.max,
    rw nat.succ_le_succ_iff,
    apply nat.le_max_right
  end

def nats.max : list nat → nat 
| []        := 0
| (k :: ks) := nat.max k (nats.max ks)

lemma nats.le_max_of_mem :
  ∀ {ks : list nat}, ∀ m ∈ ks, m ≤ nats.max ks 
| [] _        := by rintro ⟨_⟩ 
| (k :: ks) m := 
  begin
    rintro (h0 | h0),  
    { rw h0, apply nat.le_max_left },
    apply le_trans
      (@nats.le_max_of_mem ks _ h0) 
      (nat.le_max_right _ _),
  end

namespace nat

  def bstr_core : nat → string :=
  @nat.binary_rec (λ _, string) ""
    (λ b k s, if b then (s ++ "1") else (s ++ "0"))

  def bstr (k : nat) : string :=
    let s := bstr_core k in
    if s = "" then "0" else s

  meta def to_expr : nat → expr
  | 0            := `(0)
  | (nat.succ k) := expr.app `(nat.succ) k.to_expr

  lemma succ_lt_succ_iff :
    ∀ {a b : ℕ}, a.succ < b.succ ↔ a < b :=
  begin
    intros a b, apply iff.intro,
    apply lt_of_succ_lt_succ,
    apply succ_lt_succ
  end

  lemma succ_eq_succ_iff (k m : nat) :
    k.succ = m.succ ↔ k = m :=
  by { constructor; intro h0,
       {cases h0, refl}, rw h0 }

  lemma succ_ne_succ {k m : nat} :
    k ≠ m → k.succ ≠ m.succ :=
  by { intros h0 h1, apply h0,
       rwa succ_eq_succ_iff at h1 }

  lemma zero_ne_succ {k : nat} : 0 ≠ k.succ :=
  λ h, by cases h

  lemma pos_of_lt {k m : nat} : k < m → 0 < m :=
  λ h0, lt_of_le_of_lt (nat.zero_le _) h0

end nat
