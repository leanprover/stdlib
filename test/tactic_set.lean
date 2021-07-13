/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich
-/
import tactic.ext
import tactic.tauto
import data.set.default
import data.finset.default

/-! The set equality lemmas from the file data.set.basic, reproven with set_taut or set_taut'.

    Did not include iff lemmas nor those that had additional
    conditions that didn't work. -/
open set
open tactic
open tactic.interactive

/-- Prove tautological equality of two sets, using intuitionistic logic.
    For best results, import data.set.default or data.finset.default
    as appropriate.
 -/
meta def set_tauto_int_impl : tactic unit :=
 `[{{ refl } <|> { ext1, simp [forall_and_distrib], try { tauto }}}]

/-- Prove tautological equality of two sets, using classical logic.
    For best results, import data.set.default or data.finset.default
    as appropriate.
 -/
meta def set_tauto_classic_impl : tactic unit :=
 `[{{ refl } <|> { ext1, simp [forall_and_distrib], try { tauto! }}}]

meta def set_tauto_classic_impl2 : tactic unit :=
 `[{{ refl } <|> { ext1, try {simp [forall_and_distrib]}, try { tauto! }}}]

/-- Helper for set_tauto4. -/
meta def set_tauto3 : tactic unit :=
do tactic.ext1 [],
do lemmas ← simp_lemmas.mk_default,
do lemmas' ← simp_lemmas.add_simp lemmas `forall_and_distrib,
do tactic.simp_all lemmas' [],
do tactic.tautology  {classical := tt}

/-- Works on some stuff where set_tauto fails. -/
meta def set_tauto4 : tactic unit :=
  `[{{ refl } <|> set_tauto3 }]

/-- Exact suggestion, for comparison. -/ 
meta def set_tauto2 : tactic unit :=
  `[ ext1, simp [forall_and_distrib], try { tauto! }]

/- In order to make testing easier, I created a bridge
that categorizes the different lemmas by "difficulty".

Overall, these tactics take roughly 120 - 160 ms.
refl takes 1 ms. I haven't analyzed noise,
as I am not sure if we are even in the right
ballpark yet.

Minimal working solution on all problems
124.181 ms avg
meta def refl_int = `[refl]
meta def set_tauto_int := set_tauto_int_impl
meta def set_tauto_classic := set_tauto_classic_impl
meta def set_tauto_hard := set_tauto4

There is not much loss for just running set_tauto2.
set_tauto2 except the hardest problems
166.186 ms avg
meta def refl_int = set_tauto2
meta def set_tauto_int := set_tauto2
meta def set_tauto_classic := set_tauto2
meta def set_tauto_hard := set_tauto4

Using refl gives a 20 ms advantage.
set_tauto_classic_impl on all but the hardest
141.333 ms avg
meta def refl_int := set_tauto_classic_impl
meta def set_tauto_int := set_tauto_classic_impl
meta def set_tauto_classic := set_tauto_classic_impl
meta def set_tauto_hard := set_tauto4

set_tauto_classic2_impl works nearly identically.
139.655 ms avg
meta def refl_int := set_tauto_classic_impl2
meta def set_tauto_int := set_tauto_classic_impl2
meta def set_tauto_classic := set_tauto_classic_impl2
meta def set_tauto_hard := set_tauto4

Intuitionistic is 10 ms faster, but fails on 29 more problems.
Minimal working solution except refl on all problems
131.271 ms avg
meta def refl_int = set_tauto_int_impl
meta def set_tauto_int := set_tauto_int_impl
meta def set_tauto_classic := set_tauto_classic_impl
meta def set_tauto_hard := set_tauto4

set_tauto4 on all problems. This is what I would go for,
but probably need to diagnose what is happening in
set_tauto_classic such that it fails on these problems.
161.757 ms avg
meta def refl_int := set_tauto4
meta def set_tauto_int := set_tauto4
meta def set_tauto_classic := set_tauto4
meta def set_tauto_hard := set_tauto4

refl on all problems
98 failures out of 133, 1.408 ms avg
meta def refl_int := `[refl]
meta def set_tauto_int := `[refl]
meta def set_tauto_classic := `[refl]
meta def set_tauto_hard := `[refl]

 -/

/-- Problems solvable by refl (36 problems) -/ 
meta def refl_int := set_tauto_classic_impl2
/-- Problems solvable by intuitionistic logic (68 problems) -/
meta def set_tauto_int := set_tauto_classic_impl2
/-- Problems solvable by classical logic. (24 problems) -/
meta def set_tauto_classic := set_tauto_classic_impl2
/-- Problems that require the longer version, set_tauto4
    Five timed + 1 needing additional help. -/
meta def set_tauto_hard := set_tauto4


namespace set_tests
universe v
variables {α β: Type*} {a:α} {s t u : set α} {f g : β → set α}

lemma top_eq_univ : (⊤ : set α) = univ := by timetac "top_eq_univ" refl_int
lemma bot_eq_empty : (⊥ : set α) = ∅ :=  by timetac "bot_eq_empty" refl_int
lemma sup_eq_union (s t : set α) : s ⊔ t = s ∪ t := by timetac "sup_eq_union" refl_int
lemma inf_eq_inter (s t : set α) : s ⊓ t = s ∩ t := by timetac "inf_eq_inter" refl_int
lemma le_eq_subset (s t : set α) : s ≤ t = (s ⊆ t) := by timetac "le_eq_subset" refl_int

theorem set_of_set {s : set α} : set_of s = s := by timetac "set_of_set" refl_int

lemma sep_set_of {p q : α → Prop} : {a ∈ {a | p a } | q a} = {a | p a ∧ q a} := by timetac "sep_set_of" refl_int

lemma set_of_and {p q : α → Prop} : {a | p a ∧ q a} = {a | p a} ∩ {a | q a} := by timetac "set_of_and" refl_int

lemma set_of_or {p q : α → Prop} : {a | p a ∨ q a} = {a | p a} ∪ {a | q a} := by timetac "set_of_or" refl_int
theorem empty_def : (∅ : set α) = {x | false} :=  by timetac "empty_def" refl_int

theorem set_of_false : {a : α | false} = ∅ := by timetac "set_of_false" refl_int

theorem set_of_true : {x : α | true} = univ := by timetac "set_of_true" refl_int

theorem union_def {s₁ s₂ : set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂} := by timetac "union_def" refl_int

theorem union_self (a : set α) : a ∪ a = a := by timetac "union_self" set_tauto_int

theorem union_empty (a : set α) : a ∪ ∅ = a := by timetac "union_empty" set_tauto_int

theorem empty_union (a : set α) : ∅ ∪ a = a := by timetac "empty_union" set_tauto_int

theorem union_comm (a b : set α) : a ∪ b = b ∪ a := by timetac "union_comm" set_tauto_int

theorem union_assoc (a b c : set α) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
by timetac "union_assoc" set_tauto_int

theorem union_left_comm (s₁ s₂ s₃ : set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
by timetac "union_left_comm" set_tauto_int

theorem union_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
by timetac "union_right_comm" set_tauto_int

theorem union_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∪ t = t :=
by timetac "union_eq_self_of_subset_left" set_tauto_int

theorem union_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∪ t = s :=
by timetac "union_eq_self_of_subset_right" set_tauto_int

lemma union_univ {s : set α} : s ∪ univ = univ :=
by timetac "union_univ" set_tauto_int

lemma univ_union {s : set α} : univ ∪ s = univ :=
by timetac "univ_union" set_tauto_int

theorem inter_def {s₁ s₂ : set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂} :=
by timetac "inter_def" refl_int


theorem inter_self (a : set α) : a ∩ a = a := by timetac "inter_self" set_tauto_int

theorem inter_empty (a : set α) : a ∩ ∅ = ∅ := by timetac "inter_empty" set_tauto_int

theorem empty_inter (a : set α) : ∅ ∩ a = ∅ := by timetac "empty_inter" set_tauto_int

lemma inter_comm : s ∩ t = t ∩ s :=
by timetac "inter_comm" set_tauto_int

theorem inter_assoc (a b c : set α) : (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
by timetac "empty_inter" set_tauto_int

theorem inter_left_comm (s₁ s₂ s₃ : set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
by timetac "inter_left_comm" set_tauto_int

theorem inter_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
by timetac "inter_right_comm" set_tauto_int

theorem inter_univ (a : set α) : a ∩ univ = a :=
by timetac "inter_univ" set_tauto_int

theorem univ_inter (a : set α) : univ ∩ a = a :=
by timetac "univ_inter" set_tauto_int

theorem union_inter_cancel_left {s t : set α} : (s ∪ t) ∩ s = s :=
by timetac "union_inter_cancel_left" set_tauto_int

theorem union_inter_cancel_right {s t : set α} : (s ∪ t) ∩ t = t :=
by timetac "union_inter_cancel_right" set_tauto_int

/-! ### Distributivity laws -/

theorem inter_distrib_left (s t u : set α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
by timetac "inter_distrib_left" set_tauto_classic

theorem inter_distrib_right (s t u : set α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
by timetac "inter_distrib_right" set_tauto_classic

theorem union_distrib_left (s t u : set α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
by timetac "union_distrib_left" set_tauto_int

theorem union_distrib_right (s t u : set α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
by timetac "union_distrib_right" set_tauto_classic

theorem insert_def (x : α) (s : set α) : insert x s = { y | y = x ∨ y ∈ s } :=
by timetac "insert_def" refl_int

theorem insert_eq_of_mem {a : α} {s : set α} (h : a ∈ s) : insert a s = s :=
by timetac "insert_eq_of_mem" set_tauto_hard

theorem insert_comm (a b : α) (s : set α) : insert a (insert b s) = insert b (insert a s) :=
by timetac "insert_comm" set_tauto_int

theorem insert_union (a:α) : insert a s ∪ t = insert a (s ∪ t) :=
by timetac "insert_union" set_tauto_int

theorem union_insert (a:α) : s ∪ insert a t = insert a (s ∪ t) :=
by timetac "union_insert" set_tauto_int

lemma insert_inter (x : α) (s t : set α) : insert x (s ∩ t) = insert x s ∩ insert x t :=
by timetac "insert_inter" set_tauto_int

/-! ### Lemmas about singletons -/

theorem singleton_def (a : α) : ({a} : set α) = insert a ∅ :=
by timetac "singleton_def" set_tauto_int

lemma set_of_eq_eq_singleton {a : α} : {n | n = a} = {a} :=
by timetac "set_of_eq_eq_singleton" refl_int

theorem insert_eq (x : α) (s : set α) : insert x s = ({x} : set α) ∪ s :=
by timetac "insert_eq" refl_int

theorem pair_eq_singleton (a : α) : ({a, a} : set α) = {a} :=
by timetac "pair_eq_singleton" set_tauto_int

theorem pair_comm (a b : α) : ({a, b} : set α) = {b, a} :=
by timetac "pair_comm" set_tauto_int

theorem set_compr_eq_eq_singleton {a : α} : {b | b = a} = {a} :=
by timetac "set_compr_eq_eq_singleton" refl_int

theorem singleton_union : {a} ∪ s = insert a s :=
by timetac "singleton_union" refl_int

theorem union_singleton : s ∪ {a} = insert a s :=
by timetac "union_singleton" set_tauto_int

theorem sep_mem_eq {s t : set α} : {x ∈ s | x ∈ t} = s ∩ t :=
by timetac "sep_mem_eq" refl_int

theorem mem_sep_eq {s : set α} {p : α → Prop} {x : α} :
  x ∈ {x ∈ s | p x} = (x ∈ s ∧ p x) :=
by timetac "mem_sep_eq" refl_int

theorem eq_sep_of_subset {s t : set α} (h : s ⊆ t) : s = {x ∈ t | x ∈ s} :=
by timetac "eq_sep_of_subset" set_tauto_int

lemma sep_univ {α} {p : α → Prop} : {a ∈ (univ : set α) | p a} = {a | p a} :=
by timetac "sep_univ" set_tauto_int

lemma compl_set_of {α} (p : α → Prop) : {a | p a}ᶜ = { a | ¬ p a } :=
by timetac "compl_set_of" refl_int

theorem mem_compl_eq (s : set α) (x : α) : x ∈ sᶜ = (x ∉ s) :=
by timetac "mem_compl_eq" refl_int

theorem inter_compl_self (s : set α) : s ∩ sᶜ = ∅ :=
by timetac "inter_compl_self" set_tauto_int

theorem compl_inter_self (s : set α) : sᶜ ∩ s = ∅ :=
by timetac "compl_inter_self" set_tauto_int

theorem compl_empty : (∅ : set α)ᶜ = univ :=
by timetac "compl_empty" set_tauto_int


theorem compl_union (s t : set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
by timetac "compl_union" set_tauto_classic

theorem compl_inter (s t : set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ :=
by timetac "compl_inter" set_tauto_classic

theorem compl_univ : (univ : set α)ᶜ = ∅ := by timetac "compl_univ" set_tauto_classic


lemma compl_singleton_eq (a : α) : ({a} : set α)ᶜ = {x | x ≠ a} :=
by timetac "compl_singleton_eq" refl_int

lemma compl_ne_eq_singleton (a : α) : ({x | x ≠ a} : set α)ᶜ = {a} :=
by timetac "compl_ne_eq_singleton" set_tauto_int

theorem union_eq_compl_compl_inter_compl (s t : set α) : s ∪ t = (sᶜ ∩ tᶜ)ᶜ :=
by timetac "union_eq_compl_compl_inter_compl" set_tauto_int

theorem inter_eq_compl_compl_union_compl (s t : set α) : s ∩ t = (sᶜ ∪ tᶜ)ᶜ :=
by timetac "inter_eq_compl_compl_union_compl" set_tauto_int

theorem union_compl_self (s : set α) : s ∪ sᶜ = univ := by timetac "union_compl_self" set_tauto_int

theorem compl_union_self (s : set α) : sᶜ ∪ s = univ := by timetac "compl_union_self" set_tauto_int

theorem compl_comp_compl : compl ∘ compl = @id (set α) := by timetac "compl_comp_compl" set_tauto_int

theorem diff_eq (s t : set α) : s \ t = s ∩ tᶜ := by timetac "diff_eq" refl_int

theorem diff_eq_compl_inter {s t : set α} : s \ t = tᶜ ∩ s :=
by timetac "diff_eq_compl_inter" set_tauto_int

theorem union_diff_cancel' {s t u : set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : t ∪ (u \ s) = u :=
by timetac "union_diff_cancel'" set_tauto_int


theorem union_diff_cancel {s t : set α} (h : s ⊆ t) : s ∪ (t \ s) = t :=
by timetac "union_diff_cancel" set_tauto_int


theorem union_diff_left {s t : set α} : (s ∪ t) \ s = t \ s :=
by timetac "union_diff_left" set_tauto_int

theorem union_diff_right {s t : set α} : (s ∪ t) \ t = s \ t :=
by timetac "union_diff_right" set_tauto_int

theorem union_diff_distrib {s t u : set α} : (s ∪ t) \ u = s \ u ∪ t \ u :=
by timetac "union_diff_distrib" set_tauto_classic

theorem inter_union_distrib_left {s t u : set α} : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by timetac "inter_union_distrib_left" set_tauto_classic

theorem inter_union_distrib_right {s t u : set α} : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
by timetac "inter_union_distrib_right" set_tauto_classic

theorem union_inter_distrib_left {s t u : set α} : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
by timetac "union_inter_distrib_left" set_tauto_classic

theorem union_inter_distrib_right {s t u : set α} : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
by timetac "union_inter_distrib_right" set_tauto_classic

theorem inter_diff_assoc (a b c : set α) : (a ∩ b) \ c = a ∩ (b \ c) :=
by timetac "inter_diff_assoc" set_tauto_int

theorem inter_diff_self (a b : set α) : a ∩ (b \ a) = ∅ :=
by timetac "inter_diff_self" set_tauto_int

theorem inter_union_diff (s t : set α) : (s ∩ t) ∪ (s \ t) = s :=
by timetac "inter_union_diff" set_tauto_int

theorem inter_union_compl (s t : set α) : (s ∩ t) ∪ (s ∩ tᶜ) = s :=
by timetac "inter_union_compl" set_tauto_int

theorem compl_eq_univ_diff (s : set α) : sᶜ = univ \ s :=
by timetac "compl_eq_univ_diff" set_tauto_int

lemma empty_diff (s : set α) : (∅ \ s : set α) = ∅ := by timetac "empty_diff" set_tauto_int


theorem diff_empty {s : set α} : s \ ∅ = s := by timetac "diff_empty" set_tauto_int

theorem diff_diff {u : set α} : s \ t \ u = s \ (t ∪ u) := by timetac "diff_diff" set_tauto_int

-- the following statement contains parentheses to help the reader
lemma diff_diff_comm {s t u : set α} : (s \ t) \ u = (s \ u) \ t :=
by timetac "diff_diff_comm" set_tauto_int

lemma diff_inter {s t u : set α} : s \ (t ∩ u) = (s \ t) ∪ (s \ u) :=
by timetac "diff_inter" set_tauto_classic

lemma diff_inter_diff {s t u : set α} : s \ t ∩ (s \ u) = s \ (t ∪ u) :=
by timetac "diff_inter_diff" set_tauto_classic

lemma diff_compl : s \ tᶜ = s ∩ t := by timetac "diff_compl" set_tauto_classic

lemma diff_diff_right {s t u : set α} : s \ (t \ u) = (s \ t) ∪ (s ∩ u) :=
by timetac "diff_diff_right" set_tauto_classic

theorem insert_diff_of_mem (s) (h : a ∈ t) : insert a s \ t = s \ t :=
by timetac "insert_diff_of_mem" set_tauto_hard

lemma insert_diff_self_of_not_mem {a : α} {s : set α} (h : a ∉ s) :
  insert a s \ {a} = s :=
by timetac "insert_diff_self_of_not_mem" set_tauto_hard


theorem union_diff_self {s t : set α} : s ∪ (t \ s) = s ∪ t :=
by timetac "union_diff_self" set_tauto_classic

theorem diff_union_self {s t : set α} : (s \ t) ∪ t = s ∪ t :=
by timetac "diff_union_self" set_tauto_classic

theorem diff_inter_self {a b : set α} : (b \ a) ∩ a = ∅ :=
by timetac "diff_inter_self" set_tauto_classic

theorem diff_inter_self_eq_diff {s t : set α} : s \ (t ∩ s) = s \ t :=
by timetac "diff_inter_self_eq_diff" set_tauto_classic

theorem diff_self_inter {s t : set α} : s \ (s ∩ t) = s \ t :=
by timetac "diff_self_inter" set_tauto_classic

theorem diff_singleton_eq_self {a : α} {s : set α} (h : a ∉ s) : s \ {a} = s :=
by timetac "diff_singleton_eq_self" set_tauto_hard

theorem insert_diff_singleton {a : α} {s : set α} :
  insert a (s \ {a}) = insert a s := by timetac "insert_diff_singleton" set_tauto_classic

lemma diff_self {s : set α} : s \ s = ∅ := by timetac "diff_self" set_tauto_classic

lemma diff_diff_cancel_left {s t : set α} (h : s ⊆ t) : t \ (t \ s) = s :=
by timetac "diff_diff_cancel_left" set_tauto_classic

end set_tests

namespace set_tests
variables {α β γ:Type*}
section preimage
variables {f : α → β} {g : β → γ}

theorem preimage_empty : f ⁻¹' ∅ = ∅ := by timetac "preimage_empty" refl_int


lemma preimage_congr {f g : α → β} {s : set β} (h : ∀ (x : α), f x = g x) : f ⁻¹' s = g ⁻¹' s := by timetac "preimage_congr" set_tauto_hard

theorem preimage_univ : f ⁻¹' univ = univ := by timetac "preimage_univ" refl_int

theorem preimage_inter {s t : set β} : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t :=
by timetac "preimage_inter" refl_int

theorem preimage_union {s t : set β} : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t :=
by timetac "preimage_union" refl_int

theorem preimage_compl {s : set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ :=
by timetac "preimage_compl" refl_int

theorem preimage_diff (f : α → β) (s t : set β) :
  f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t := by timetac "preimage_diff" refl_int

theorem preimage_set_of_eq {p : α → Prop} {f : β → α} : f ⁻¹' {a | p a} = {a | p (f a)} :=
by timetac "preimage_set_of_eq" refl_int

theorem preimage_id {s : set α} : id ⁻¹' s = s := by timetac "preimage_id" refl_int

theorem preimage_id' {s : set α} : (λ x, x) ⁻¹' s = s := by timetac "preimage_id'" refl_int

theorem preimage_const_of_mem {b : β} {s : set β} (h : b ∈ s) :
  (λ (x : α), b) ⁻¹' s = univ := by timetac "preimage_const_of_mem" set_tauto_int

theorem preimage_const_of_not_mem {b : β} {s : set β} (h : b ∉ s) :
  (λ (x : α), b) ⁻¹' s = ∅ := by timetac "preimage_const_of_not_mem" set_tauto_int

theorem preimage_const (b : β) (s : set β) [decidable (b ∈ s)] :
  (λ (x : α), b) ⁻¹' s = if b ∈ s then univ else ∅ := begin
  cases decidable.em (b ∈ s) ; set_tauto_hard,
end

theorem preimage_comp {s : set γ} : (g ∘ f) ⁻¹' s = f ⁻¹' (g ⁻¹' s) :=
by timetac "preimage_comp" refl_int

lemma preimage_preimage {g : β → γ} {f : α → β} {s : set γ} :
  f ⁻¹' (g ⁻¹' s) = (λ x, g (f x)) ⁻¹' s :=
by timetac "preimage_preimage" refl_int

--Although this is set equality, set_tauto_classic totally fails.
lemma preimage_coe_coe_diagonal {α : Type*} (s : set α) :
  (prod.map coe coe) ⁻¹' (diagonal α) = diagonal s := begin
  ext ⟨⟨x, x_in⟩, ⟨y, y_in⟩⟩,
  simp [set.diagonal],
end

end preimage

end set_tests

namespace set_tests
universe v
variables {α β: Type*} {a:α} {s t u : set α} {f g : β → set α}

--TODO: test the rest of the file data.set.basic.

/- Here are some more complex lemmas
   Inter_inter_eq_Inter_inter is what requires the additional lemma in
   set_tauto. -/
lemma Inter_inter_eq_Inter_inter : (⋂ b, f b ∩ g b) = ⋂ b, (g b ∩ f b) :=
by timetac "Inter_inter_eq_Inter_inter" set_tauto_classic

lemma Inter_inter_eq_Inter_inter'' : (⋂ b, f b) ∩ (⋂ b, g b) = ⋂ b, (g b ∩ f b) :=
by timetac "Inter_inter_eq_Inter_inter''" set_tauto_int

lemma Union_inter_eq_Union_inter' : (⋃ b, f b ∩ g b) = ⋃ b, (g b ∩ f b) :=
by timetac "Union_inter_eq_Union_inter'" set_tauto_int

lemma Inter_inter_eq_Inter_inter_of_nonempty {κ : Type*} [nonempty κ]
  (f : κ → set α) : (⋂ b, f b) ∩ s = ⋂ b, f b ∩ s  :=
by timetac "Inter_inter_eq_Inter_inter_of_nonempty" set_tauto_int

end set_tests

section finset_tests
variables {α β: Type*} [decidable_eq α] {s t u : finset α} {f : β → set α}
lemma inter_comm' : s ∩ t = t ∩ s := by timetac "inter_comm'" set_tauto_int

lemma union_comm' : s ∪ t = t ∪ s := by timetac "union_comm'" set_tauto_int

lemma inter_assoc' : (s ∩ t) ∩ u = s ∩ (t ∩ u) := by timetac "inter_assoc'" set_tauto_int

lemma union_assoc' : (s ∪ t) ∪ u = s ∪ (t ∪ u) := by timetac "union_assoc'" set_tauto_int

lemma union_distrib : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
by timetac "union_distrib" set_tauto_int

lemma union_distrib_comm : (s ∪ t) ∩ u = (t ∩ u) ∪ (s ∩ u) :=
by timetac "union_distrib_comm" set_tauto_int

lemma Inter_union : (s ∪ t) ∩ u = (t ∩ u) ∪ (s ∩ u) := by timetac "Inter_union" set_tauto_int

end finset_tests

