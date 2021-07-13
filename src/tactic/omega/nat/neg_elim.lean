/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/

/-
Negation elimination.
-/

import tactic.omega.nat.form

namespace omega
namespace nat

open_locale omega.nat

/-- push_neg p returns the result of normalizing ¬ p by
    pushing the outermost negation all the way down,
    until it reaches either a negation or an atom -/
@[simp] def push_neg : preform → preform
| (p ∨* q) := (push_neg p) ∧* (push_neg q)
| (p ∧* q) := (push_neg p) ∨* (push_neg q)
| (¬*p)    := p
| p        := ¬* p

lemma push_neg_equiv :
  ∀ {p : preform}, preform.equiv (push_neg p) (¬* p) :=
begin
  preform.induce `[intros v; try {refl}],
  { simp only [not_not, preform.holds, push_neg] },
  { simp only [preform.holds, push_neg, not_or_distrib, ihp v, ihq v] },
  { simp only [preform.holds, push_neg, not_and_distrib, ihp v, ihq v] }
end

/-- NNF transformation -/
def nnf : preform → preform
| (¬* p)   := push_neg (nnf p)
| (p ∨* q) := (nnf p) ∨* (nnf q)
| (p ∧* q) := (nnf p) ∧* (nnf q)
| a        := a

/-- Asserts that the given preform is in NNF -/
def is_nnf : preform → Prop
| (t =* s) := true
| (t ≤* s) := true
| ¬*(t =* s) := true
| ¬*(t ≤* s) := true
| (p ∨* q) := is_nnf p ∧ is_nnf q
| (p ∧* q) := is_nnf p ∧ is_nnf q
| _ := false

lemma is_nnf_push_neg : ∀ p : preform, is_nnf p → is_nnf (push_neg p) :=
begin
  preform.induce `[intro h1; try {trivial}],
  { cases p; try {cases h1}; trivial },
  { cases h1, constructor; [{apply ihp}, {apply ihq}]; assumption },
  { cases h1, constructor; [{apply ihp}, {apply ihq}]; assumption }
end

lemma is_nnf_nnf : ∀ p : preform, is_nnf (nnf p) :=
begin
  preform.induce `[try {trivial}],
  { apply is_nnf_push_neg _ ih },
  { constructor; assumption },
  { constructor; assumption }
end

lemma nnf_equiv : ∀ {p : preform}, preform.equiv (nnf p) p :=
begin
  preform.induce `[intros v; try {refl}; simp only [nnf]],
  { rw push_neg_equiv,
    apply not_iff_not_of_iff, apply ih },
  { apply pred_mono_2' (ihp v) (ihq v) },
  { apply pred_mono_2' (ihp v) (ihq v) }
end

@[simp] def neg_elim_core : preform → preform
| (¬* (t =* s)) := (t.add_one ≤* s) ∨* (s.add_one ≤* t)
| (¬* (t ≤* s)) := s.add_one ≤* t
| (p ∨* q) := (neg_elim_core p) ∨* (neg_elim_core q)
| (p ∧* q) := (neg_elim_core p) ∧* (neg_elim_core q)
| p        := p

lemma neg_free_neg_elim_core : ∀ p, is_nnf p → (neg_elim_core p).neg_free :=
begin
  preform.induce `[intro h1, try {simp only [neg_free, neg_elim_core]}, try {trivial}],
  { cases p; try {cases h1}; try {trivial},
    constructor; trivial },
  { cases h1, constructor; [{apply ihp}, {apply ihq}]; assumption },
  { cases h1, constructor; [{apply ihp}, {apply ihq}]; assumption }
end

lemma le_and_le_iff_eq {α : Type} [partial_order α] {a b : α} :
  (a ≤ b ∧ b ≤ a) ↔ a = b :=
begin
  constructor; intro h1,
  { cases h1, apply le_antisymm; assumption },
  { constructor; apply le_of_eq; rw h1  }
end

lemma implies_neg_elim_core : ∀ {p : preform},
  preform.implies p (neg_elim_core p) :=
begin
  preform.induce `[intros v h, try {apply h}],
  { cases p with t s t s; try {apply h},
    { apply or.symm,
      simpa only [preform.holds, le_and_le_iff_eq.symm,
        not_and_distrib, not_le] using h },
    simpa only [preform.holds, not_le, ←lt_iff_add_one_le] using h },
  { simp only [neg_elim_core], cases h;
    [{left, apply ihp}, {right, apply ihq}];
    assumption },
  apply and.imp (ihp _) (ihq _) h
end

/-- Eliminate all negations in a preform -/
def neg_elim : preform → preform := neg_elim_core ∘ nnf

lemma neg_free_neg_elim {p : preform} : (neg_elim p).neg_free :=
neg_free_neg_elim_core _ (is_nnf_nnf _)

lemma implies_neg_elim {p : preform} : preform.implies p (neg_elim p) :=
begin
  intros v h1, apply implies_neg_elim_core,
  apply (nnf_equiv v).elim_right h1
end

end nat

end omega
