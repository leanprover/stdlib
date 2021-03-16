/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import algebra.order_functions
import control.monad.basic
import data.nat.choose.basic
import order.rel_classes

/-!
# Basic properties of lists
-/

open function nat

namespace list
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

attribute [inline] list.head

instance : is_left_id (list α) has_append.append [] :=
⟨ nil_append ⟩

instance : is_right_id (list α) has_append.append [] :=
⟨ append_nil ⟩

instance : is_associative (list α) has_append.append :=
⟨ append_assoc ⟩

theorem cons_ne_nil (a : α) (l : list α) : a::l ≠ [].

theorem cons_ne_self (a : α) (l : list α) : a::l ≠ l :=
mt (congr_arg length) (nat.succ_ne_self _)

theorem head_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : list α} :
      (h₁::t₁) = (h₂::t₂) → h₁ = h₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pheq)

theorem tail_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : list α} :
      (h₁::t₁) = (h₂::t₂) → t₁ = t₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pteq)

@[simp] theorem cons_injective {a : α} : injective (cons a) :=
assume l₁ l₂, assume Pe, tail_eq_of_cons_eq Pe

theorem cons_inj (a : α) {l l' : list α} : a::l = a::l' ↔ l = l' :=
cons_injective.eq_iff

theorem exists_cons_of_ne_nil {l : list α} (h : l ≠ nil) : ∃ b L, l = b :: L :=
by { induction l with c l',  contradiction,  use [c,l'], }

/-! ### mem -/

theorem mem_singleton_self (a : α) : a ∈ [a] := mem_cons_self _ _

theorem eq_of_mem_singleton {a b : α} : a ∈ [b] → a = b :=
assume : a ∈ [b], or.elim (eq_or_mem_of_mem_cons this)
  (assume : a = b, this)
  (assume : a ∈ [], absurd this (not_mem_nil a))

@[simp] theorem mem_singleton {a b : α} : a ∈ [b] ↔ a = b :=
⟨eq_of_mem_singleton, or.inl⟩

theorem mem_of_mem_cons_of_mem {a b : α} {l : list α} : a ∈ b::l → b ∈ l → a ∈ l :=
assume ainbl binl, or.elim (eq_or_mem_of_mem_cons ainbl)
  (assume : a = b, begin subst a, exact binl end)
  (assume : a ∈ l, this)

theorem eq_or_ne_mem_of_mem {a b : α} {l : list α} (h : a ∈ b :: l) : a = b ∨ (a ≠ b ∧ a ∈ l) :=
classical.by_cases or.inl $ assume : a ≠ b, h.elim or.inl $ assume h, or.inr ⟨this, h⟩

theorem not_mem_append {a : α} {s t : list α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t :=
mt mem_append.1 $ not_or_distrib.2 ⟨h₁, h₂⟩

theorem ne_nil_of_mem {a : α} {l : list α} (h : a ∈ l) : l ≠ [] :=
by intro e; rw e at h; cases h

theorem mem_split {a : α} {l : list α} (h : a ∈ l) : ∃ s t : list α, l = s ++ a :: t :=
begin
  induction l with b l ih, {cases h}, rcases h with rfl | h,
  { exact ⟨[], l, rfl⟩ },
  { rcases ih h with ⟨s, t, rfl⟩,
    exact ⟨b::s, t, rfl⟩ }
end

theorem mem_of_ne_of_mem {a y : α} {l : list α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
or.elim (eq_or_mem_of_mem_cons h₂) (λe, absurd e h₁) (λr, r)

theorem ne_of_not_mem_cons {a b : α} {l : list α} : a ∉ b::l → a ≠ b :=
assume nin aeqb, absurd (or.inl aeqb) nin

theorem not_mem_of_not_mem_cons {a b : α} {l : list α} : a ∉ b::l → a ∉ l :=
assume nin nainl, absurd (or.inr nainl) nin

theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : list α} : a ≠ y → a ∉ l → a ∉ y::l :=
assume p1 p2, not.intro (assume Pain, absurd (eq_or_mem_of_mem_cons Pain) (not_or p1 p2))

theorem ne_and_not_mem_of_not_mem_cons {a y : α} {l : list α} : a ∉ y::l → a ≠ y ∧ a ∉ l :=
assume p, and.intro (ne_of_not_mem_cons p) (not_mem_of_not_mem_cons p)

theorem mem_map_of_mem (f : α → β) {a : α} {l : list α} (h : a ∈ l) : f a ∈ map f l :=
begin
  induction l with b l' ih,
  {cases h},
  {rcases h with rfl | h,
    {exact or.inl rfl},
    {exact or.inr (ih h)}}
end

theorem exists_of_mem_map {f : α → β} {b : β} {l : list α} (h : b ∈ map f l) :
  ∃ a, a ∈ l ∧ f a = b :=
begin
  induction l with c l' ih,
  {cases h},
  {cases (eq_or_mem_of_mem_cons h) with h h,
    {exact ⟨c, mem_cons_self _ _, h.symm⟩},
    {rcases ih h with ⟨a, ha₁, ha₂⟩,
      exact ⟨a, mem_cons_of_mem _ ha₁, ha₂⟩ }}
end

@[simp] theorem mem_map {f : α → β} {b : β} {l : list α} : b ∈ map f l ↔ ∃ a, a ∈ l ∧ f a = b :=
⟨exists_of_mem_map, λ ⟨a, la, h⟩, by rw [← h]; exact mem_map_of_mem f la⟩

theorem mem_map_of_injective {f : α → β} (H : injective f) {a : α} {l : list α} :
  f a ∈ map f l ↔ a ∈ l :=
⟨λ m, let ⟨a', m', e⟩ := exists_of_mem_map m in H e ▸ m', mem_map_of_mem _⟩

lemma forall_mem_map_iff {f : α → β} {l : list α} {P : β → Prop} :
  (∀ i ∈ l.map f, P i) ↔ ∀ j ∈ l, P (f j) :=
begin
  split,
  { assume H j hj,
    exact H (f j) (mem_map_of_mem f hj) },
  { assume H i hi,
    rcases mem_map.1 hi with ⟨j, hj, ji⟩,
    rw ← ji,
    exact H j hj }
end

@[simp] lemma map_eq_nil {f : α → β} {l : list α} : list.map f l = [] ↔ l = [] :=
⟨by cases l; simp only [forall_prop_of_true, map, forall_prop_of_false, not_false_iff],
  λ h, h.symm ▸ rfl⟩

@[simp] theorem mem_join {a : α} : ∀ {L : list (list α)}, a ∈ join L ↔ ∃ l, l ∈ L ∧ a ∈ l
| []       := ⟨false.elim, λ⟨_, h, _⟩, false.elim h⟩
| (c :: L) := by simp only [join, mem_append, @mem_join L, mem_cons_iff, or_and_distrib_right,
  exists_or_distrib, exists_eq_left]

theorem exists_of_mem_join {a : α} {L : list (list α)} : a ∈ join L → ∃ l, l ∈ L ∧ a ∈ l :=
mem_join.1

theorem mem_join_of_mem {a : α} {L : list (list α)} {l} (lL : l ∈ L) (al : a ∈ l) : a ∈ join L :=
mem_join.2 ⟨l, lL, al⟩

@[simp]
theorem mem_bind {b : β} {l : list α} {f : α → list β} : b ∈ list.bind l f ↔ ∃ a ∈ l, b ∈ f a :=
iff.trans mem_join
  ⟨λ ⟨l', h1, h2⟩, let ⟨a, al, fa⟩ := exists_of_mem_map h1 in ⟨a, al, fa.symm ▸ h2⟩,
  λ ⟨a, al, bfa⟩, ⟨f a, mem_map_of_mem _ al, bfa⟩⟩

theorem exists_of_mem_bind {b : β} {l : list α} {f : α → list β} :
  b ∈ list.bind l f → ∃ a ∈ l, b ∈ f a :=
mem_bind.1

theorem mem_bind_of_mem {b : β} {l : list α} {f : α → list β} {a} (al : a ∈ l) (h : b ∈ f a) :
  b ∈ list.bind l f :=
mem_bind.2 ⟨a, al, h⟩

lemma bind_map {g : α → list β} {f : β → γ} :
  ∀(l : list α), list.map f (l.bind g) = l.bind (λa, (g a).map f)
| [] := rfl
| (a::l) := by simp only [cons_bind, map_append, bind_map l]

/-! ### length -/

theorem length_eq_zero {l : list α} : length l = 0 ↔ l = [] :=
⟨eq_nil_of_length_eq_zero, λ h, h.symm ▸ rfl⟩

@[simp] lemma length_singleton (a : α) : length [a] = 1 := rfl

theorem length_pos_of_mem {a : α} : ∀ {l : list α}, a ∈ l → 0 < length l
| (b::l) _ := zero_lt_succ _

theorem exists_mem_of_length_pos : ∀ {l : list α}, 0 < length l → ∃ a, a ∈ l
| (b::l) _ := ⟨b, mem_cons_self _ _⟩

theorem length_pos_iff_exists_mem {l : list α} : 0 < length l ↔ ∃ a, a ∈ l :=
⟨exists_mem_of_length_pos, λ ⟨a, h⟩, length_pos_of_mem h⟩

theorem ne_nil_of_length_pos {l : list α} : 0 < length l → l ≠ [] :=
λ h1 h2, lt_irrefl 0 ((length_eq_zero.2 h2).subst h1)

theorem length_pos_of_ne_nil {l : list α} : l ≠ [] → 0 < length l :=
λ h, pos_iff_ne_zero.2 $ λ h0, h $ length_eq_zero.1 h0

theorem length_pos_iff_ne_nil {l : list α} : 0 < length l ↔ l ≠ [] :=
⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩

theorem length_eq_one {l : list α} : length l = 1 ↔ ∃ a, l = [a] :=
⟨match l with [a], _ := ⟨a, rfl⟩ end, λ ⟨a, e⟩, e.symm ▸ rfl⟩

lemma exists_of_length_succ {n} :
  ∀ l : list α, l.length = n + 1 → ∃ h t, l = h :: t
| [] H := absurd H.symm $ succ_ne_zero n
| (h :: t) H := ⟨h, t, rfl⟩

@[simp] lemma length_injective_iff : injective (list.length : list α → ℕ) ↔ subsingleton α :=
begin
  split,
  { intro h, refine ⟨λ x y, _⟩, suffices : [x] = [y], { simpa using this }, apply h, refl },
  { intros hα l1 l2 hl, induction l1 generalizing l2; cases l2,
    { refl }, { cases hl }, { cases hl },
    congr, exactI subsingleton.elim _ _, apply l1_ih, simpa using hl }
end

@[simp] lemma length_injective [subsingleton α] : injective (length : list α → ℕ) :=
length_injective_iff.mpr $ by apply_instance

/-! ### set-theoretic notation of lists -/

lemma empty_eq : (∅ : list α) = [] := by refl
lemma singleton_eq (x : α) : ({x} : list α) = [x] := rfl
lemma insert_neg [decidable_eq α] {x : α} {l : list α} (h : x ∉ l) :
  has_insert.insert x l = x :: l :=
if_neg h
lemma insert_pos [decidable_eq α] {x : α} {l : list α} (h : x ∈ l) :
  has_insert.insert x l = l :=
if_pos h
lemma doubleton_eq [decidable_eq α] {x y : α} (h : x ≠ y) : ({x, y} : list α) = [x, y] :=
by { rw [insert_neg, singleton_eq], rwa [singleton_eq, mem_singleton] }

/-! ### bounded quantifiers over lists -/

theorem forall_mem_nil (p : α → Prop) : ∀ x ∈ @nil α, p x.

theorem forall_mem_cons : ∀ {p : α → Prop} {a : α} {l : list α},
  (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
ball_cons

theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : list α}
    (h : ∀ x ∈ a :: l, p x) :
  ∀ x ∈ l, p x :=
(forall_mem_cons.1 h).2

theorem forall_mem_singleton {p : α → Prop} {a : α} : (∀ x ∈ [a], p x) ↔ p a :=
by simp only [mem_singleton, forall_eq]

theorem forall_mem_append {p : α → Prop} {l₁ l₂ : list α} :
  (∀ x ∈ l₁ ++ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ (∀ x ∈ l₂, p x) :=
by simp only [mem_append, or_imp_distrib, forall_and_distrib]

theorem not_exists_mem_nil (p : α → Prop) : ¬ ∃ x ∈ @nil α, p x.

theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : list α) (h : p a) :
  ∃ x ∈ a :: l, p x :=
bex.intro a (mem_cons_self _ _) h

theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : list α} (h : ∃ x ∈ l, p x) :
  ∃ x ∈ a :: l, p x :=
bex.elim h (λ x xl px, bex.intro x (mem_cons_of_mem _ xl) px)

theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : list α} (h : ∃ x ∈ a :: l, p x) :
  p a ∨ ∃ x ∈ l, p x :=
bex.elim h (λ x xal px,
  or.elim (eq_or_mem_of_mem_cons xal)
    (assume : x = a, begin rw ←this, left, exact px end)
    (assume : x ∈ l, or.inr (bex.intro x this px)))

theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : list α) :
  (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
iff.intro or_exists_of_exists_mem_cons
  (assume h, or.elim h (exists_mem_cons_of l) exists_mem_cons_of_exists)

/-! ### list subset -/

theorem subset_def {l₁ l₂ : list α} : l₁ ⊆ l₂ ↔ ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂ := iff.rfl

theorem subset_append_of_subset_left (l l₁ l₂ : list α) : l ⊆ l₁ → l ⊆ l₁++l₂ :=
λ s, subset.trans s $ subset_append_left _ _

theorem subset_append_of_subset_right (l l₁ l₂ : list α) : l ⊆ l₂ → l ⊆ l₁++l₂ :=
λ s, subset.trans s $ subset_append_right _ _

@[simp] theorem cons_subset {a : α} {l m : list α} :
  a::l ⊆ m ↔ a ∈ m ∧ l ⊆ m :=
by simp only [subset_def, mem_cons_iff, or_imp_distrib, forall_and_distrib, forall_eq]

theorem cons_subset_of_subset_of_mem {a : α} {l m : list α}
  (ainm : a ∈ m) (lsubm : l ⊆ m) : a::l ⊆ m :=
cons_subset.2 ⟨ainm, lsubm⟩

theorem append_subset_of_subset_of_subset {l₁ l₂ l : list α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
  l₁ ++ l₂ ⊆ l :=
λ a h, (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)

@[simp] theorem append_subset_iff {l₁ l₂ l : list α} :
  l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l :=
begin
  split,
  { intro h, simp only [subset_def] at *, split; intros; simp* },
  { rintro ⟨h1, h2⟩, apply append_subset_of_subset_of_subset h1 h2 }
end

theorem eq_nil_of_subset_nil : ∀ {l : list α}, l ⊆ [] → l = []
| []     s := rfl
| (a::l) s := false.elim $ s $ mem_cons_self a l

theorem eq_nil_iff_forall_not_mem {l : list α} : l = [] ↔ ∀ a, a ∉ l :=
show l = [] ↔ l ⊆ [], from ⟨λ e, e ▸ subset.refl _, eq_nil_of_subset_nil⟩

theorem map_subset {l₁ l₂ : list α} (f : α → β) (H : l₁ ⊆ l₂) : map f l₁ ⊆ map f l₂ :=
λ x, by simp only [mem_map, not_and, exists_imp_distrib, and_imp]; exact λ a h e, ⟨a, H h, e⟩

theorem map_subset_iff {l₁ l₂ : list α} (f : α → β) (h : injective f) :
  map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ :=
begin
  refine ⟨_, map_subset f⟩, intros h2 x hx,
  rcases mem_map.1 (h2 (mem_map_of_mem f hx)) with ⟨x', hx', hxx'⟩,
  cases h hxx', exact hx'
end

/-! ### append -/

lemma append_eq_has_append {L₁ L₂ : list α} : list.append L₁ L₂ = L₁ ++ L₂ := rfl

@[simp] lemma singleton_append {x : α} {l : list α} : [x] ++ l = x :: l := rfl

theorem append_ne_nil_of_ne_nil_left (s t : list α) : s ≠ [] → s ++ t ≠ [] :=
by induction s; intros; contradiction

theorem append_ne_nil_of_ne_nil_right (s t : list α) : t ≠ [] → s ++ t ≠ [] :=
by induction s; intros; contradiction

@[simp] lemma append_eq_nil {p q : list α} : (p ++ q) = [] ↔ p = [] ∧ q = [] :=
by cases p; simp only [nil_append, cons_append, eq_self_iff_true, true_and, false_and]

@[simp] lemma nil_eq_append_iff {a b : list α} : [] = a ++ b ↔ a = [] ∧ b = [] :=
by rw [eq_comm, append_eq_nil]

lemma append_eq_cons_iff {a b c : list α} {x : α} :
  a ++ b = x :: c ↔ (a = [] ∧ b = x :: c) ∨ (∃a', a = x :: a' ∧ c = a' ++ b) :=
by cases a; simp only [and_assoc, @eq_comm _ c, nil_append, cons_append, eq_self_iff_true,
  true_and, false_and, exists_false, false_or, or_false, exists_and_distrib_left, exists_eq_left']

lemma cons_eq_append_iff {a b c : list α} {x : α} :
  (x :: c : list α) = a ++ b ↔ (a = [] ∧ b = x :: c) ∨ (∃a', a = x :: a' ∧ c = a' ++ b) :=
by rw [eq_comm, append_eq_cons_iff]

lemma append_eq_append_iff {a b c d : list α} :
  a ++ b = c ++ d ↔ (∃a', c = a ++ a' ∧ b = a' ++ d) ∨ (∃c', a = c ++ c' ∧ d = c' ++ b) :=
begin
  induction a generalizing c,
  case nil { rw nil_append, split,
    { rintro rfl, left, exact ⟨_, rfl, rfl⟩ },
    { rintro (⟨a', rfl, rfl⟩ | ⟨a', H, rfl⟩), {refl}, {rw [← append_assoc, ← H], refl} } },
  case cons : a as ih {
    cases c,
    { simp only [cons_append, nil_append, false_and, exists_false, false_or, exists_eq_left'],
      exact eq_comm },
    { simp only [cons_append, @eq_comm _ a, ih, and_assoc, and_or_distrib_left,
        exists_and_distrib_left] } }
end

@[simp] theorem split_at_eq_take_drop : ∀ (n : ℕ) (l : list α), split_at n l = (take n l, drop n l)
| 0        a         := rfl
| (succ n) []        := rfl
| (succ n) (x :: xs) := by simp only [split_at, split_at_eq_take_drop n xs, take, drop]

@[simp] theorem take_append_drop : ∀ (n : ℕ) (l : list α), take n l ++ drop n l = l
| 0        a         := rfl
| (succ n) []        := rfl
| (succ n) (x :: xs) := congr_arg (cons x) $ take_append_drop n xs

-- TODO(Leo): cleanup proof after arith dec proc
theorem append_inj :
  ∀ {s₁ s₂ t₁ t₂ : list α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂
| []      []      t₁ t₂ h hl := ⟨rfl, h⟩
| (a::s₁) []      t₁ t₂ h hl := list.no_confusion $ eq_nil_of_length_eq_zero hl
| []      (b::s₂) t₁ t₂ h hl := list.no_confusion $ eq_nil_of_length_eq_zero hl.symm
| (a::s₁) (b::s₂) t₁ t₂ h hl := list.no_confusion h $ λab hap,
  let ⟨e1, e2⟩ := @append_inj s₁ s₂ t₁ t₂ hap (succ.inj hl) in
  by rw [ab, e1, e2]; exact ⟨rfl, rfl⟩

theorem append_inj_right {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂)
  (hl : length s₁ = length s₂) : t₁ = t₂ :=
(append_inj h hl).right

theorem append_inj_left {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂)
  (hl : length s₁ = length s₂) : s₁ = s₂ :=
(append_inj h hl).left

theorem append_inj' {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) :
  s₁ = s₂ ∧ t₁ = t₂ :=
append_inj h $ @nat.add_right_cancel _ (length t₁) _ $
let hap := congr_arg length h in by simp only [length_append] at hap; rwa [← hl] at hap

theorem append_inj_right' {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂)
  (hl : length t₁ = length t₂) : t₁ = t₂ :=
(append_inj' h hl).right

theorem append_inj_left' {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂)
  (hl : length t₁ = length t₂) : s₁ = s₂ :=
(append_inj' h hl).left

theorem append_left_cancel {s t₁ t₂ : list α} (h : s ++ t₁ = s ++ t₂) : t₁ = t₂ :=
append_inj_right h rfl

theorem append_right_cancel {s₁ s₂ t : list α} (h : s₁ ++ t = s₂ ++ t) : s₁ = s₂ :=
append_inj_left' h rfl

theorem append_right_injective (s : list α) : function.injective (λ t, s ++ t) :=
λ t₁ t₂, append_left_cancel

theorem append_right_inj {t₁ t₂ : list α} (s) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ :=
(append_right_injective s).eq_iff

theorem append_left_injective (t : list α) : function.injective (λ s, s ++ t) :=
λ s₁ s₂, append_right_cancel

theorem append_left_inj {s₁ s₂ : list α} (t) : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ :=
(append_left_injective t).eq_iff

theorem map_eq_append_split {f : α → β} {l : list α} {s₁ s₂ : list β}
  (h : map f l = s₁ ++ s₂) : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = s₁ ∧ map f l₂ = s₂ :=
begin
  have := h, rw [← take_append_drop (length s₁) l] at this ⊢,
  rw map_append at this,
  refine ⟨_, _, rfl, append_inj this _⟩,
  rw [length_map, length_take, min_eq_left],
  rw [← length_map f l, h, length_append],
  apply nat.le_add_right
end

/-! ### repeat -/

@[simp] theorem repeat_succ (a : α) (n) : repeat a (n + 1) = a :: repeat a n := rfl

theorem mem_repeat {a b : α} : ∀ {n}, b ∈ repeat a n ↔ n ≠ 0 ∧ b = a
| 0 := by simp
| (n + 1) := by simp [mem_repeat]

theorem eq_of_mem_repeat {a b : α} {n} (h :  b ∈ repeat a n) : b = a :=
(mem_repeat.1 h).2

theorem eq_repeat_of_mem {a : α} : ∀ {l : list α}, (∀ b ∈ l, b = a) → l = repeat a l.length
| []     H := rfl
| (b::l) H := by cases forall_mem_cons.1 H with H₁ H₂;
  unfold length repeat; congr; [exact H₁, exact eq_repeat_of_mem H₂]

theorem eq_repeat' {a : α} {l : list α} : l = repeat a l.length ↔ ∀ b ∈ l, b = a :=
⟨λ h, h.symm ▸ λ b, eq_of_mem_repeat, eq_repeat_of_mem⟩

theorem eq_repeat {a : α} {n} {l : list α} : l = repeat a n ↔ length l = n ∧ ∀ b ∈ l, b = a :=
⟨λ h, h.symm ▸ ⟨length_repeat _ _, λ b, eq_of_mem_repeat⟩,
 λ ⟨e, al⟩, e ▸ eq_repeat_of_mem al⟩

theorem repeat_add (a : α) (m n) : repeat a (m + n) = repeat a m ++ repeat a n :=
by induction m; simp only [*, zero_add, succ_add, repeat]; split; refl

theorem repeat_subset_singleton (a : α) (n) : repeat a n ⊆ [a] :=
λ b h, mem_singleton.2 (eq_of_mem_repeat h)

@[simp] theorem map_const (l : list α) (b : β) : map (function.const α b) l = repeat b l.length :=
by induction l; [refl, simp only [*, map]]; split; refl

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : list α} (h : b₁ ∈ map (function.const α b₂) l) :
  b₁ = b₂ :=
by rw map_const at h; exact eq_of_mem_repeat h

@[simp] theorem map_repeat (f : α → β) (a : α) (n) : map f (repeat a n) = repeat (f a) n :=
by induction n; [refl, simp only [*, repeat, map]]; split; refl

@[simp] theorem tail_repeat (a : α) (n) : tail (repeat a n) = repeat a n.pred :=
by cases n; refl

@[simp] theorem join_repeat_nil (n : ℕ) : join (repeat [] n) = @nil α :=
by induction n; [refl, simp only [*, repeat, join, append_nil]]

lemma repeat_left_injective {n : ℕ} (hn : n ≠ 0) :
  function.injective (λ a : α, repeat a n) :=
λ a b h, (eq_repeat.1 h).2 _ $ mem_repeat.2 ⟨hn, rfl⟩

lemma repeat_left_inj {a b : α} {n : ℕ} (hn : n ≠ 0) :
  repeat a n = repeat b n ↔ a = b :=
(repeat_left_injective hn).eq_iff

@[simp] lemma repeat_left_inj' {a b : α} :
  ∀ {n}, repeat a n = repeat b n ↔ n = 0 ∨ a = b
| 0 := by simp
| (n + 1) := (repeat_left_inj n.succ_ne_zero).trans $ by simp only [n.succ_ne_zero, false_or]

lemma repeat_right_injective (a : α) : function.injective (repeat a) :=
function.left_inverse.injective (length_repeat a)

@[simp] lemma repeat_right_inj {a : α} {n m : ℕ} :
  repeat a n = repeat a m ↔ n = m :=
(repeat_right_injective a).eq_iff

/-! ### pure -/

@[simp] theorem mem_pure {α} (x y : α) :
  x ∈ (pure y : list α) ↔ x = y := by simp! [pure,list.ret]

/-! ### bind -/

@[simp] theorem bind_eq_bind {α β} (f : α → list β) (l : list α) :
  l >>= f = l.bind f := rfl

-- TODO: duplicate of a lemma in core
theorem bind_append (f : α → list β) (l₁ l₂ : list α) :
  (l₁ ++ l₂).bind f = l₁.bind f ++ l₂.bind f :=
append_bind _ _ _

@[simp] theorem bind_singleton (f : α → list β) (x : α) : [x].bind f = f x :=
append_nil (f x)

/-! ### concat -/

theorem concat_nil (a : α) : concat [] a = [a] := rfl

theorem concat_cons (a b : α) (l : list α) : concat (a :: l) b = a :: concat l b := rfl

@[simp] theorem concat_eq_append (a : α) (l : list α) : concat l a = l ++ [a] :=
by induction l; simp only [*, concat]; split; refl

theorem init_eq_of_concat_eq {a : α} {l₁ l₂ : list α} : concat l₁ a = concat l₂ a → l₁ = l₂ :=
begin
  intro h,
  rw [concat_eq_append, concat_eq_append] at h,
  exact append_right_cancel h
end

theorem last_eq_of_concat_eq {a b : α} {l : list α} : concat l a = concat l b → a = b :=
begin
  intro h,
  rw [concat_eq_append, concat_eq_append] at h,
  exact head_eq_of_cons_eq (append_left_cancel h)
end

theorem concat_ne_nil (a : α) (l : list α) : concat l a ≠ [] :=
by simp

theorem concat_append (a : α) (l₁ l₂ : list α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ :=
by simp

theorem length_concat (a : α) (l : list α) : length (concat l a) = succ (length l) :=
by simp only [concat_eq_append, length_append, length]

theorem append_concat (a : α) (l₁ l₂ : list α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a :=
by simp

/-! ### reverse -/

@[simp] theorem reverse_nil : reverse (@nil α) = [] := rfl

local attribute [simp] reverse_core

@[simp] theorem reverse_cons (a : α) (l : list α) : reverse (a::l) = reverse l ++ [a] :=
have aux : ∀ l₁ l₂, reverse_core l₁ l₂ ++ [a] = reverse_core l₁ (l₂ ++ [a]),
by intro l₁; induction l₁; intros; [refl, simp only [*, reverse_core, cons_append]],
(aux l nil).symm

theorem reverse_core_eq (l₁ l₂ : list α) : reverse_core l₁ l₂ = reverse l₁ ++ l₂ :=
by induction l₁ generalizing l₂; [refl, simp only [*, reverse_core, reverse_cons, append_assoc]];
  refl

theorem reverse_cons' (a : α) (l : list α) : reverse (a::l) = concat (reverse l) a :=
by simp only [reverse_cons, concat_eq_append]

@[simp] theorem reverse_singleton (a : α) : reverse [a] = [a] := rfl

@[simp] theorem reverse_append (s t : list α) : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
by induction s; [rw [nil_append, reverse_nil, append_nil],
simp only [*, cons_append, reverse_cons, append_assoc]]

theorem reverse_concat (l : list α) (a : α) : reverse (concat l a) = a :: reverse l :=
by rw [concat_eq_append, reverse_append, reverse_singleton, singleton_append]

@[simp] theorem reverse_reverse (l : list α) : reverse (reverse l) = l :=
by induction l; [refl, simp only [*, reverse_cons, reverse_append]]; refl

@[simp] theorem reverse_involutive : involutive (@reverse α) :=
λ l, reverse_reverse l

@[simp] theorem reverse_injective : injective (@reverse α) :=
reverse_involutive.injective

@[simp] theorem reverse_inj {l₁ l₂ : list α} : reverse l₁ = reverse l₂ ↔ l₁ = l₂ :=
reverse_injective.eq_iff

@[simp] theorem reverse_eq_nil {l : list α} : reverse l = [] ↔ l = [] :=
@reverse_inj _ l []

theorem concat_eq_reverse_cons (a : α) (l : list α) : concat l a = reverse (a :: reverse l) :=
by simp only [concat_eq_append, reverse_cons, reverse_reverse]

@[simp] theorem length_reverse (l : list α) : length (reverse l) = length l :=
by induction l; [refl, simp only [*, reverse_cons, length_append, length]]

@[simp] theorem map_reverse (f : α → β) (l : list α) : map f (reverse l) = reverse (map f l) :=
by induction l; [refl, simp only [*, map, reverse_cons, map_append]]

theorem map_reverse_core (f : α → β) (l₁ l₂ : list α) :
  map f (reverse_core l₁ l₂) = reverse_core (map f l₁) (map f l₂) :=
by simp only [reverse_core_eq, map_append, map_reverse]

@[simp] theorem mem_reverse {a : α} {l : list α} : a ∈ reverse l ↔ a ∈ l :=
by induction l; [refl, simp only [*, reverse_cons, mem_append, mem_singleton, mem_cons_iff,
  not_mem_nil, false_or, or_false, or_comm]]

@[simp] theorem reverse_repeat (a : α) (n) : reverse (repeat a n) = repeat a n :=
eq_repeat.2 ⟨by simp only [length_reverse, length_repeat],
  λ b h, eq_of_mem_repeat (mem_reverse.1 h)⟩

/-! ### is_nil -/

lemma is_nil_iff_eq_nil {l : list α} : l.is_nil ↔ l = [] :=
list.cases_on l (by simp [is_nil]) (by simp [is_nil])

/-! ### init -/

@[simp] theorem length_init : ∀ (l : list α), length (init l) = length l - 1
| [] := rfl
| [a] := rfl
| (a :: b :: l) :=
begin
  rw init,
  simp only [add_left_inj, length, succ_add_sub_one],
  exact length_init (b :: l)
end

/-! ### last -/

@[simp] theorem last_cons {a : α} {l : list α} :
  ∀ (h₁ : a :: l ≠ nil) (h₂ : l ≠ nil), last (a :: l) h₁ = last l h₂ :=
by {induction l; intros, contradiction, reflexivity}

@[simp] theorem last_append {a : α} (l : list α) (h : l ++ [a] ≠ []) : last (l ++ [a]) h = a :=
by induction l;
  [refl, simp only [cons_append, last_cons _ (λ H, cons_ne_nil _ _ (append_eq_nil.1 H).2), *]]

theorem last_concat {a : α} (l : list α) (h : concat l a ≠ []) : last (concat l a) h = a :=
by simp only [concat_eq_append, last_append]

@[simp] theorem last_singleton (a : α) (h : [a] ≠ []) : last [a] h = a := rfl

@[simp] theorem last_cons_cons (a₁ a₂ : α) (l : list α) (h : a₁::a₂::l ≠ []) :
  last (a₁::a₂::l) h = last (a₂::l) (cons_ne_nil a₂ l) := rfl

theorem init_append_last : ∀ {l : list α} (h : l ≠ []), init l ++ [last l h] = l
| [] h := absurd rfl h
| [a] h := rfl
| (a::b::l) h :=
begin
  rw [init, cons_append, last_cons (cons_ne_nil _ _) (cons_ne_nil _ _)],
  congr,
  exact init_append_last (cons_ne_nil b l)
end

theorem last_congr {l₁ l₂ : list α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
  last l₁ h₁ = last l₂ h₂ :=
by subst l₁

theorem last_mem : ∀ {l : list α} (h : l ≠ []), last l h ∈ l
| [] h := absurd rfl h
| [a] h := or.inl rfl
| (a::b::l) h := or.inr $ by { rw [last_cons_cons], exact last_mem (cons_ne_nil b l) }

lemma last_repeat_succ (a m : ℕ) :
  (repeat a m.succ).last (ne_nil_of_length_eq_succ
  (show (repeat a m.succ).length = m.succ, by rw length_repeat)) = a :=
begin
  induction m with k IH,
  { simp },
  { simpa only [repeat_succ, last] }
end

/-! ### last' -/

@[simp] theorem last'_is_none :
  ∀ {l : list α}, (last' l).is_none ↔ l = []
| [] := by simp
| [a] := by simp
| (a::b::l) := by simp [@last'_is_none (b::l)]

@[simp] theorem last'_is_some : ∀ {l : list α}, l.last'.is_some ↔ l ≠ []
| [] := by simp
| [a] := by simp
| (a::b::l) := by simp [@last'_is_some (b::l)]

theorem mem_last'_eq_last : ∀ {l : list α} {x : α}, x ∈ l.last' → ∃ h, x = last l h
| [] x hx := false.elim $ by simpa using hx
| [a] x hx := have a = x, by simpa using hx, this ▸ ⟨cons_ne_nil a [], rfl⟩
| (a::b::l) x hx :=
  begin
    rw last' at hx,
    rcases mem_last'_eq_last hx with ⟨h₁, h₂⟩,
    use cons_ne_nil _ _,
    rwa [last_cons]
  end

theorem mem_of_mem_last' {l : list α} {a : α} (ha : a ∈ l.last') : a ∈ l :=
let ⟨h₁, h₂⟩ := mem_last'_eq_last ha in h₂.symm ▸ last_mem _

theorem init_append_last' : ∀ {l : list α} (a ∈ l.last'), init l ++ [a] = l
| [] a ha := (option.not_mem_none a ha).elim
| [a] _ rfl := rfl
| (a :: b :: l) c hc := by { rw [last'] at hc, rw [init, cons_append, init_append_last' _ hc] }

theorem ilast_eq_last' [inhabited α] : ∀ l : list α, l.ilast = l.last'.iget
| [] := by simp [ilast, arbitrary]
| [a] := rfl
| [a, b] := rfl
| [a, b, c] := rfl
| (a :: b :: c :: l) := by simp [ilast, ilast_eq_last' (c :: l)]

@[simp] theorem last'_append_cons : ∀ (l₁ : list α) (a : α) (l₂ : list α),
  last' (l₁ ++ a :: l₂) = last' (a :: l₂)
| [] a l₂ := rfl
| [b] a l₂ := rfl
| (b::c::l₁) a l₂ := by rw [cons_append, cons_append, last', ← cons_append, last'_append_cons]

theorem last'_append_of_ne_nil (l₁ : list α) : ∀ {l₂ : list α} (hl₂ : l₂ ≠ []),
  last' (l₁ ++ l₂) = last' l₂
| [] hl₂ := by contradiction
| (b::l₂) _ := last'_append_cons l₁ b l₂

/-! ### head(') and tail -/

theorem head_eq_head' [inhabited α] (l : list α) : head l = (head' l).iget :=
by cases l; refl

theorem mem_of_mem_head' {x : α} : ∀ {l : list α}, x ∈ l.head' → x ∈ l
| [] h := (option.not_mem_none _ h).elim
| (a::l) h := by { simp only [head', option.mem_def] at h, exact h ▸ or.inl rfl }

@[simp] theorem head_cons [inhabited α] (a : α) (l : list α) : head (a::l) = a := rfl

@[simp] theorem tail_nil : tail (@nil α) = [] := rfl

@[simp] theorem tail_cons (a : α) (l : list α) : tail (a::l) = l := rfl

@[simp] theorem head_append [inhabited α] (t : list α) {s : list α} (h : s ≠ []) :
  head (s ++ t) = head s :=
by {induction s, contradiction, refl}

theorem tail_append_singleton_of_ne_nil {a : α} {l : list α} (h : l ≠ nil) :
  tail (l ++ [a]) = tail l ++ [a] :=
by { induction l,  contradiction, rw [tail,cons_append,tail], }

theorem cons_head'_tail : ∀ {l : list α} {a : α} (h : a ∈ head' l), a :: tail l = l
| [] a h := by contradiction
| (b::l) a h := by { simp at h, simp [h] }

theorem head_mem_head' [inhabited α] : ∀ {l : list α} (h : l ≠ []), head l ∈ head' l
| [] h := by contradiction
| (a::l) h := rfl

theorem cons_head_tail [inhabited α] {l : list α} (h : l ≠ []) : (head l)::(tail l) = l :=
cons_head'_tail (head_mem_head' h)

@[simp] theorem head'_map (f : α → β) (l) : head' (map f l) = (head' l).map f := by cases l; refl

/-! ### Induction from the right -/

/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
@[elab_as_eliminator] def reverse_rec_on {C : list α → Sort*}
  (l : list α) (H0 : C [])
  (H1 : ∀ (l : list α) (a : α), C l → C (l ++ [a])) : C l :=
begin
  rw ← reverse_reverse l,
  induction reverse l,
  { exact H0 },
  { rw reverse_cons, exact H1 _ _ ih }
end

/-- Bidirectional induction principle for lists: if a property holds for the empty list, the
singleton list, and `a :: (l ++ [b])` from `l`, then it holds for all lists. This can be used to
prove statements about palindromes. The principle is given for a `Sort`-valued predicate, i.e., it
can also be used to construct data. -/
def bidirectional_rec {C : list α → Sort*}
    (H0 : C []) (H1 : ∀ (a : α), C [a])
    (Hn : ∀ (a : α) (l : list α) (b : α), C l → C (a :: (l ++ [b]))) : ∀ l, C l
| [] := H0
| [a] := H1 a
| (a :: b :: l) :=
let l' := init (b :: l), b' := last (b :: l) (cons_ne_nil _ _) in
have length l' < length (a :: b :: l), by { change _ < length l + 2, simp },
begin
  rw ←init_append_last (cons_ne_nil b l),
  have : C l', from bidirectional_rec l',
  exact Hn a l' b' ‹C l'›
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩] }

/-- Like `bidirectional_rec`, but with the list parameter placed first. -/
@[elab_as_eliminator] def bidirectional_rec_on {C : list α → Sort*}
    (l : list α) (H0 : C []) (H1 : ∀ (a : α), C [a])
    (Hn : ∀ (a : α) (l : list α) (b : α), C l → C (a :: (l ++ [b]))) : C l :=
bidirectional_rec H0 H1 Hn l

/-! ### sublists -/

@[simp] theorem nil_sublist : Π (l : list α), [] <+ l
| []       := sublist.slnil
| (a :: l) := sublist.cons _ _ a (nil_sublist l)

@[refl, simp] theorem sublist.refl : Π (l : list α), l <+ l
| []       := sublist.slnil
| (a :: l) := sublist.cons2 _ _ a (sublist.refl l)

@[trans] theorem sublist.trans {l₁ l₂ l₃ : list α} (h₁ : l₁ <+ l₂) (h₂ : l₂ <+ l₃) : l₁ <+ l₃ :=
sublist.rec_on h₂ (λ_ s, s)
  (λl₂ l₃ a h₂ IH l₁ h₁, sublist.cons _ _ _ (IH l₁ h₁))
  (λl₂ l₃ a h₂ IH l₁ h₁, @sublist.cases_on _ (λl₁ l₂', l₂' = a :: l₂ → l₁ <+ a :: l₃) _ _ h₁
    (λ_, nil_sublist _)
    (λl₁ l₂' a' h₁' e, match a', l₂', e, h₁' with ._, ._, rfl, h₁ :=
      sublist.cons _ _ _ (IH _ h₁) end)
    (λl₁ l₂' a' h₁' e, match a', l₂', e, h₁' with ._, ._, rfl, h₁ :=
      sublist.cons2 _ _ _ (IH _ h₁) end) rfl)
  l₁ h₁

@[simp] theorem sublist_cons (a : α) (l : list α) : l <+ a::l :=
sublist.cons _ _ _ (sublist.refl l)

theorem sublist_of_cons_sublist {a : α} {l₁ l₂ : list α} : a::l₁ <+ l₂ → l₁ <+ l₂ :=
sublist.trans (sublist_cons a l₁)

theorem cons_sublist_cons {l₁ l₂ : list α} (a : α) (s : l₁ <+ l₂) : a::l₁ <+ a::l₂ :=
sublist.cons2 _ _ _ s

@[simp] theorem sublist_append_left : Π (l₁ l₂ : list α), l₁ <+ l₁++l₂
| []      l₂ := nil_sublist _
| (a::l₁) l₂ := cons_sublist_cons _ (sublist_append_left l₁ l₂)

@[simp] theorem sublist_append_right : Π (l₁ l₂ : list α), l₂ <+ l₁++l₂
| []      l₂ := sublist.refl _
| (a::l₁) l₂ := sublist.cons _ _ _ (sublist_append_right l₁ l₂)

theorem sublist_cons_of_sublist (a : α) {l₁ l₂ : list α} : l₁ <+ l₂ → l₁ <+ a::l₂ :=
sublist.cons _ _ _

theorem sublist_append_of_sublist_left {l l₁ l₂ : list α} (s : l <+ l₁) : l <+ l₁++l₂ :=
s.trans $ sublist_append_left _ _

theorem sublist_append_of_sublist_right {l l₁ l₂ : list α} (s : l <+ l₂) : l <+ l₁++l₂ :=
s.trans $ sublist_append_right _ _

theorem sublist_of_cons_sublist_cons {l₁ l₂ : list α} : ∀ {a : α}, a::l₁ <+ a::l₂ → l₁ <+ l₂
| ._ (sublist.cons  ._ ._ a s) := sublist_of_cons_sublist s
| ._ (sublist.cons2 ._ ._ a s) := s

theorem cons_sublist_cons_iff {l₁ l₂ : list α} {a : α} : a::l₁ <+ a::l₂ ↔ l₁ <+ l₂ :=
⟨sublist_of_cons_sublist_cons, cons_sublist_cons _⟩

@[simp] theorem append_sublist_append_left {l₁ l₂ : list α} : ∀ l, l++l₁ <+ l++l₂ ↔ l₁ <+ l₂
| []     := iff.rfl
| (a::l) := cons_sublist_cons_iff.trans (append_sublist_append_left l)

theorem sublist.append_right {l₁ l₂ : list α} (h : l₁ <+ l₂) (l) : l₁++l <+ l₂++l :=
begin
  induction h with _ _ a _ ih _ _ a _ ih,
  { refl },
  { apply sublist_cons_of_sublist a ih },
  { apply cons_sublist_cons a ih }
end

theorem sublist_or_mem_of_sublist {l l₁ l₂ : list α} {a : α} (h : l <+ l₁ ++ a::l₂) :
  l <+ l₁ ++ l₂ ∨ a ∈ l :=
begin
  induction l₁ with b l₁ IH generalizing l,
  { cases h, { left, exact ‹l <+ l₂› }, { right, apply mem_cons_self } },
  { cases h with _ _ _ h _ _ _ h,
    { exact or.imp_left (sublist_cons_of_sublist _) (IH h) },
    { exact (IH h).imp (cons_sublist_cons _) (mem_cons_of_mem _) } }
end

theorem sublist.reverse {l₁ l₂ : list α} (h : l₁ <+ l₂) : l₁.reverse <+ l₂.reverse :=
begin
  induction h with _ _ _ _ ih _ _ a _ ih, {refl},
  { rw reverse_cons, exact sublist_append_of_sublist_left ih },
  { rw [reverse_cons, reverse_cons], exact ih.append_right [a] }
end

@[simp] theorem reverse_sublist_iff {l₁ l₂ : list α} : l₁.reverse <+ l₂.reverse ↔ l₁ <+ l₂ :=
⟨λ h, l₁.reverse_reverse ▸ l₂.reverse_reverse ▸ h.reverse, sublist.reverse⟩

@[simp] theorem append_sublist_append_right {l₁ l₂ : list α} (l) : l₁++l <+ l₂++l ↔ l₁ <+ l₂ :=
⟨λ h, by simpa only [reverse_append, append_sublist_append_left, reverse_sublist_iff]
  using h.reverse,
 λ h, h.append_right l⟩

theorem sublist.append {l₁ l₂ r₁ r₂ : list α}
  (hl : l₁ <+ l₂) (hr : r₁ <+ r₂) : l₁ ++ r₁ <+ l₂ ++ r₂ :=
(hl.append_right _).trans ((append_sublist_append_left _).2 hr)

theorem sublist.subset : Π {l₁ l₂ : list α}, l₁ <+ l₂ → l₁ ⊆ l₂
| ._ ._ sublist.slnil             b h := h
| ._ ._ (sublist.cons  l₁ l₂ a s) b h := mem_cons_of_mem _ (sublist.subset s h)
| ._ ._ (sublist.cons2 l₁ l₂ a s) b h :=
  match eq_or_mem_of_mem_cons h with
  | or.inl h := h ▸ mem_cons_self _ _
  | or.inr h := mem_cons_of_mem _ (sublist.subset s h)
  end

theorem singleton_sublist {a : α} {l} : [a] <+ l ↔ a ∈ l :=
⟨λ h, h.subset (mem_singleton_self _), λ h,
let ⟨s, t, e⟩ := mem_split h in e.symm ▸
  (cons_sublist_cons _ (nil_sublist _)).trans (sublist_append_right _ _)⟩

theorem eq_nil_of_sublist_nil {l : list α} (s : l <+ []) : l = [] :=
eq_nil_of_subset_nil $ s.subset

theorem repeat_sublist_repeat (a : α) {m n} : repeat a m <+ repeat a n ↔ m ≤ n :=
⟨λ h, by simpa only [length_repeat] using length_le_of_sublist h,
 λ h, by induction h; [refl, simp only [*, repeat_succ, sublist.cons]] ⟩

theorem eq_of_sublist_of_length_eq : ∀ {l₁ l₂ : list α}, l₁ <+ l₂ → length l₁ = length l₂ → l₁ = l₂
| ._ ._ sublist.slnil             h := rfl
| ._ ._ (sublist.cons  l₁ l₂ a s) h :=
  absurd (length_le_of_sublist s) $ not_le_of_gt $ by rw h; apply lt_succ_self
| ._ ._ (sublist.cons2 l₁ l₂ a s) h :=
  by rw [length, length] at h; injection h with h; rw eq_of_sublist_of_length_eq s h

theorem eq_of_sublist_of_length_le {l₁ l₂ : list α} (s : l₁ <+ l₂) (h : length l₂ ≤ length l₁) :
  l₁ = l₂ :=
eq_of_sublist_of_length_eq s (le_antisymm (length_le_of_sublist s) h)

theorem sublist.antisymm {l₁ l₂ : list α} (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁) : l₁ = l₂ :=
eq_of_sublist_of_length_le s₁ (length_le_of_sublist s₂)

instance decidable_sublist [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <+ l₂)
| []      l₂      := is_true $ nil_sublist _
| (a::l₁) []      := is_false $ λh, list.no_confusion $ eq_nil_of_sublist_nil h
| (a::l₁) (b::l₂) :=
  if h : a = b then
    decidable_of_decidable_of_iff (decidable_sublist l₁ l₂) $
      by rw [← h]; exact ⟨cons_sublist_cons _, sublist_of_cons_sublist_cons⟩
  else decidable_of_decidable_of_iff (decidable_sublist (a::l₁) l₂)
    ⟨sublist_cons_of_sublist _, λs, match a, l₁, s, h with
    | a, l₁, sublist.cons ._ ._ ._ s', h := s'
    | ._, ._, sublist.cons2 t ._ ._ s', h := absurd rfl h
    end⟩

/-! ### index_of -/

section index_of
variable [decidable_eq α]

@[simp] theorem index_of_nil (a : α) : index_of a [] = 0 := rfl

theorem index_of_cons (a b : α) (l : list α) :
  index_of a (b::l) = if a = b then 0 else succ (index_of a l) := rfl

theorem index_of_cons_eq {a b : α} (l : list α) : a = b → index_of a (b::l) = 0 :=
assume e, if_pos e

@[simp] theorem index_of_cons_self (a : α) (l : list α) : index_of a (a::l) = 0 :=
index_of_cons_eq _ rfl

@[simp, priority 990]
theorem index_of_cons_ne {a b : α} (l : list α) : a ≠ b → index_of a (b::l) = succ (index_of a l) :=
assume n, if_neg n

theorem index_of_eq_length {a : α} {l : list α} : index_of a l = length l ↔ a ∉ l :=
begin
  induction l with b l ih,
  { exact iff_of_true rfl (not_mem_nil _) },
  simp only [length, mem_cons_iff, index_of_cons], split_ifs,
  { exact iff_of_false (by rintro ⟨⟩) (λ H, H $ or.inl h) },
  { simp only [h, false_or], rw ← ih, exact succ_inj' }
end

@[simp, priority 980]
theorem index_of_of_not_mem {l : list α} {a : α} : a ∉ l → index_of a l = length l :=
index_of_eq_length.2

theorem index_of_le_length {a : α} {l : list α} : index_of a l ≤ length l :=
begin
  induction l with b l ih, {refl},
  simp only [length, index_of_cons],
  by_cases h : a = b, {rw if_pos h, exact nat.zero_le _},
  rw if_neg h, exact succ_le_succ ih
end

theorem index_of_lt_length {a} {l : list α} : index_of a l < length l ↔ a ∈ l :=
⟨λh, by_contradiction $ λ al, ne_of_lt h $ index_of_eq_length.2 al,
λal, lt_of_le_of_ne index_of_le_length $ λ h, index_of_eq_length.1 h al⟩

end index_of

/-! ### nth element -/

theorem nth_le_of_mem : ∀ {a} {l : list α}, a ∈ l → ∃ n h, nth_le l n h = a
| a (_ :: l) (or.inl rfl) := ⟨0, succ_pos _, rfl⟩
| a (b :: l) (or.inr m)   :=
  let ⟨n, h, e⟩ := nth_le_of_mem m in ⟨n+1, succ_lt_succ h, e⟩

theorem nth_le_nth : ∀ {l : list α} {n} h, nth l n = some (nth_le l n h)
| (a :: l) 0     h := rfl
| (a :: l) (n+1) h := @nth_le_nth l n _

theorem nth_len_le : ∀ {l : list α} {n}, length l ≤ n → nth l n = none
| []       n     h := rfl
| (a :: l) (n+1) h := nth_len_le (le_of_succ_le_succ h)

theorem nth_eq_some {l : list α} {n a} : nth l n = some a ↔ ∃ h, nth_le l n h = a :=
⟨λ e,
  have h : n < length l, from lt_of_not_ge $ λ hn,
    by rw nth_len_le hn at e; contradiction,
  ⟨h, by rw nth_le_nth h at e;
    injection e with e; apply nth_le_mem⟩,
λ ⟨h, e⟩, e ▸ nth_le_nth _⟩

@[simp]
theorem nth_eq_none_iff : ∀ {l : list α} {n}, nth l n = none ↔ length l ≤ n :=
begin
  intros, split,
  { intro h, by_contradiction h',
    have h₂ : ∃ h, l.nth_le n h = l.nth_le n (lt_of_not_ge h') := ⟨lt_of_not_ge h', rfl⟩,
    rw [← nth_eq_some, h] at h₂, cases h₂ },
  { solve_by_elim [nth_len_le] },
end

theorem nth_of_mem {a} {l : list α} (h : a ∈ l) : ∃ n, nth l n = some a :=
let ⟨n, h, e⟩ := nth_le_of_mem h in ⟨n, by rw [nth_le_nth, e]⟩

theorem nth_le_mem : ∀ (l : list α) n h, nth_le l n h ∈ l
| (a :: l) 0     h := mem_cons_self _ _
| (a :: l) (n+1) h := mem_cons_of_mem _ (nth_le_mem l _ _)

theorem nth_mem {l : list α} {n a} (e : nth l n = some a) : a ∈ l :=
let ⟨h, e⟩ := nth_eq_some.1 e in e ▸ nth_le_mem _ _ _

theorem mem_iff_nth_le {a} {l : list α} : a ∈ l ↔ ∃ n h, nth_le l n h = a :=
⟨nth_le_of_mem, λ ⟨n, h, e⟩, e ▸ nth_le_mem _ _ _⟩

theorem mem_iff_nth {a} {l : list α} : a ∈ l ↔ ∃ n, nth l n = some a :=
mem_iff_nth_le.trans $ exists_congr $ λ n, nth_eq_some.symm

lemma nth_zero (l : list α) : l.nth 0 = l.head' := by cases l; refl

lemma nth_injective {α : Type u} {xs : list α} {i j : ℕ}
  (h₀ : i < xs.length)
  (h₁ : nodup xs)
  (h₂ : xs.nth i = xs.nth j) : i = j :=
begin
  induction xs with x xs generalizing i j,
  { cases h₀ },
  { cases i; cases j,
    case nat.zero nat.zero
    { refl },
    case nat.succ nat.succ
    { congr, cases h₁,
      apply xs_ih;
      solve_by_elim [lt_of_succ_lt_succ] },
    iterate 2
    { dsimp at h₂,
      cases h₁ with _ _ h h',
      cases h x _ rfl,
      rw mem_iff_nth,
      exact ⟨_, h₂.symm⟩ <|>
        exact ⟨_, h₂⟩ } },
end

@[simp] theorem nth_map (f : α → β) : ∀ l n, nth (map f l) n = (nth l n).map f
| []       n     := rfl
| (a :: l) 0     := rfl
| (a :: l) (n+1) := nth_map l n

theorem nth_le_map (f : α → β) {l n} (H1 H2) : nth_le (map f l) n H1 = f (nth_le l n H2) :=
option.some.inj $ by rw [← nth_le_nth, nth_map, nth_le_nth]; refl

/-- A version of `nth_le_map` that can be used for rewriting. -/
theorem nth_le_map_rev (f : α → β) {l n} (H) :
  f (nth_le l n H) = nth_le (map f l) n ((length_map f l).symm ▸ H) :=
(nth_le_map f _ _).symm

@[simp] theorem nth_le_map' (f : α → β) {l n} (H) :
  nth_le (map f l) n H = f (nth_le l n (length_map f l ▸ H)) :=
nth_le_map f _ _

/-- If one has `nth_le L i hi` in a formula and `h : L = L'`, one can not `rw h` in the formula as
`hi` gives `i < L.length` and not `i < L'.length`. The lemma `nth_le_of_eq` can be used to make
such a rewrite, with `rw (nth_le_of_eq h)`. -/
lemma nth_le_of_eq {L L' : list α} (h : L = L') {i : ℕ} (hi : i < L.length) :
  nth_le L i hi = nth_le L' i (h ▸ hi) :=
by { congr, exact h}

@[simp] lemma nth_le_singleton (a : α) {n : ℕ} (hn : n < 1) :
  nth_le [a] n hn = a :=
have hn0 : n = 0 := le_zero_iff.1 (le_of_lt_succ hn),
by subst hn0; refl

lemma nth_le_zero [inhabited α] {L : list α} (h : 0 < L.length) :
  L.nth_le 0 h = L.head :=
by { cases L, cases h, simp, }

lemma nth_le_append : ∀ {l₁ l₂ : list α} {n : ℕ} (hn₁) (hn₂),
  (l₁ ++ l₂).nth_le n hn₁ = l₁.nth_le n hn₂
| []     _ n     hn₁ hn₂  := (not_lt_zero _ hn₂).elim
| (a::l) _ 0     hn₁ hn₂ := rfl
| (a::l) _ (n+1) hn₁ hn₂ := by simp only [nth_le, cons_append];
                         exact nth_le_append _ _

lemma nth_le_append_right_aux {l₁ l₂ : list α} {n : ℕ}
  (h₁ : l₁.length ≤ n) (h₂ : n < (l₁ ++ l₂).length) : n - l₁.length < l₂.length :=
begin
  rw list.length_append at h₂,
  convert (nat.sub_lt_sub_right_iff h₁).mpr h₂,
  simp,
end

lemma nth_le_append_right : ∀ {l₁ l₂ : list α} {n : ℕ} (h₁ : l₁.length ≤ n) (h₂),
  (l₁ ++ l₂).nth_le n h₂ = l₂.nth_le (n - l₁.length) (nth_le_append_right_aux h₁ h₂)
| []       _ n     h₁ h₂ := rfl
| (a :: l) _ (n+1) h₁ h₂ :=
  begin
    dsimp,
    conv { to_rhs, congr, skip, rw [←nat.sub_sub, nat.sub.right_comm, nat.add_sub_cancel], },
    rw nth_le_append_right (nat.lt_succ_iff.mp h₁),
  end

@[simp] lemma nth_le_repeat (a : α) {n m : ℕ} (h : m < (list.repeat a n).length) :
  (list.repeat a n).nth_le m h = a :=
eq_of_mem_repeat (nth_le_mem _ _ _)

lemma nth_append {l₁ l₂ : list α} {n : ℕ} (hn : n < l₁.length) :
  (l₁ ++ l₂).nth n = l₁.nth n :=
have hn' : n < (l₁ ++ l₂).length := lt_of_lt_of_le hn
  (by rw length_append; exact le_add_right _ _),
by rw [nth_le_nth hn, nth_le_nth hn', nth_le_append]

lemma nth_append_right {l₁ l₂ : list α} {n : ℕ} (hn : l₁.length ≤ n) :
  (l₁ ++ l₂).nth n = l₂.nth (n - l₁.length) :=
begin
  by_cases hl : n < (l₁ ++ l₂).length,
  { rw [nth_le_nth hl, nth_le_nth, nth_le_append_right hn] },
  { rw [nth_len_le (le_of_not_lt hl), nth_len_le],
    rw [not_lt, length_append] at hl,
    exact nat.le_sub_left_of_add_le hl }
end

lemma last_eq_nth_le : ∀ (l : list α) (h : l ≠ []),
  last l h = l.nth_le (l.length - 1) (sub_lt (length_pos_of_ne_nil h) one_pos)
| [] h := rfl
| [a] h := by rw [last_singleton, nth_le_singleton]
| (a :: b :: l) h := by { rw [last_cons, last_eq_nth_le (b :: l)],
                          refl, exact cons_ne_nil b l }

@[simp] lemma nth_concat_length : ∀ (l : list α) (a : α), (l ++ [a]).nth l.length = some a
| []     a := rfl
| (b::l) a := by rw [cons_append, length_cons, nth, nth_concat_length]

@[ext]
theorem ext : ∀ {l₁ l₂ : list α}, (∀n, nth l₁ n = nth l₂ n) → l₁ = l₂
| []      []       h := rfl
| (a::l₁) []       h := by have h0 := h 0; contradiction
| []      (a'::l₂) h := by have h0 := h 0; contradiction
| (a::l₁) (a'::l₂) h := by have h0 : some a = some a' := h 0; injection h0 with aa;
    simp only [aa, ext (λn, h (n+1))]; split; refl

theorem ext_le {l₁ l₂ : list α} (hl : length l₁ = length l₂)
  (h : ∀n h₁ h₂, nth_le l₁ n h₁ = nth_le l₂ n h₂) : l₁ = l₂ :=
ext $ λn, if h₁ : n < length l₁
  then by rw [nth_le_nth, nth_le_nth, h n h₁ (by rwa [← hl])]
  else let h₁ := le_of_not_gt h₁ in by { rw [nth_len_le h₁, nth_len_le], rwa [←hl], }

@[simp] theorem index_of_nth_le [decidable_eq α] {a : α} :
  ∀ {l : list α} h, nth_le l (index_of a l) h = a
| (b::l) h := by by_cases h' : a = b;
  simp only [h', if_pos, if_false, index_of_cons, nth_le, @index_of_nth_le l]

@[simp] theorem index_of_nth [decidable_eq α] {a : α} {l : list α} (h : a ∈ l) :
  nth l (index_of a l) = some a :=
by rw [nth_le_nth, index_of_nth_le (index_of_lt_length.2 h)]

theorem nth_le_reverse_aux1 :
  ∀ (l r : list α) (i h1 h2), nth_le (reverse_core l r) (i + length l) h1 = nth_le r i h2
| []       r i := λh1 h2, rfl
| (a :: l) r i :=
  by rw (show i + length (a :: l) = i + 1 + length l, from add_right_comm i (length l) 1);
    exact λh1 h2, nth_le_reverse_aux1 l (a :: r) (i+1) h1 (succ_lt_succ h2)

lemma index_of_inj [decidable_eq α] {l : list α} {x y : α}
  (hx : x ∈ l) (hy : y ∈ l) : index_of x l = index_of y l ↔ x = y :=
⟨λ h, have nth_le l (index_of x l) (index_of_lt_length.2 hx) =
        nth_le l (index_of y l) (index_of_lt_length.2 hy),
      by simp only [h],
    by simpa only [index_of_nth_le],
  λ h, by subst h⟩

theorem nth_le_reverse_aux2 : ∀ (l r : list α) (i : nat) (h1) (h2),
  nth_le (reverse_core l r) (length l - 1 - i) h1 = nth_le l i h2
| []       r i     h1 h2 := absurd h2 (not_lt_zero _)
| (a :: l) r 0     h1 h2 := begin
    have aux := nth_le_reverse_aux1 l (a :: r) 0,
    rw zero_add at aux,
    exact aux _ (zero_lt_succ _)
  end
| (a :: l) r (i+1) h1 h2 := begin
    have aux := nth_le_reverse_aux2 l (a :: r) i,
    have heq := calc length (a :: l) - 1 - (i + 1)
          = length l - (1 + i) : by rw add_comm; refl
      ... = length l - 1 - i   : by rw nat.sub_sub,
    rw [← heq] at aux,
    apply aux
  end

@[simp] theorem nth_le_reverse (l : list α) (i : nat) (h1 h2) :
  nth_le (reverse l) (length l - 1 - i) h1 = nth_le l i h2 :=
nth_le_reverse_aux2 _ _ _ _ _

lemma eq_cons_of_length_one {l : list α} (h : l.length = 1) :
  l = [l.nth_le 0 (h.symm ▸ zero_lt_one)] :=
begin
  refine ext_le (by convert h) (λ n h₁ h₂, _),
  simp only [nth_le_singleton],
  congr,
  exact eq_bot_iff.mpr (nat.lt_succ_iff.mp h₂)
end

lemma modify_nth_tail_modify_nth_tail {f g : list α → list α} (m : ℕ) :
  ∀n (l:list α), (l.modify_nth_tail f n).modify_nth_tail g (m + n) =
    l.modify_nth_tail (λl, (f l).modify_nth_tail g m) n
| 0     l      := rfl
| (n+1) []     := rfl
| (n+1) (a::l) := congr_arg (list.cons a) (modify_nth_tail_modify_nth_tail n l)

lemma modify_nth_tail_modify_nth_tail_le
  {f g : list α → list α} (m n : ℕ) (l : list α) (h : n ≤ m) :
  (l.modify_nth_tail f n).modify_nth_tail g m =
    l.modify_nth_tail (λl, (f l).modify_nth_tail g (m - n)) n :=
begin
  rcases le_iff_exists_add.1 h with ⟨m, rfl⟩,
  rw [nat.add_sub_cancel_left, add_comm, modify_nth_tail_modify_nth_tail]
end

lemma modify_nth_tail_modify_nth_tail_same {f g : list α → list α} (n : ℕ) (l:list α) :
  (l.modify_nth_tail f n).modify_nth_tail g n = l.modify_nth_tail (g ∘ f) n :=
by rw [modify_nth_tail_modify_nth_tail_le n n l (le_refl n), nat.sub_self]; refl

lemma modify_nth_tail_id :
  ∀n (l:list α), l.modify_nth_tail id n = l
| 0     l      := rfl
| (n+1) []     := rfl
| (n+1) (a::l) := congr_arg (list.cons a) (modify_nth_tail_id n l)

theorem remove_nth_eq_nth_tail : ∀ n (l : list α), remove_nth l n = modify_nth_tail tail n l
| 0     l      := by cases l; refl
| (n+1) []     := rfl
| (n+1) (a::l) := congr_arg (cons _) (remove_nth_eq_nth_tail _ _)

theorem update_nth_eq_modify_nth (a : α) : ∀ n (l : list α),
  update_nth l n a = modify_nth (λ _, a) n l
| 0     l      := by cases l; refl
| (n+1) []     := rfl
| (n+1) (b::l) := congr_arg (cons _) (update_nth_eq_modify_nth _ _)

theorem modify_nth_eq_update_nth (f : α → α) : ∀ n (l : list α),
  modify_nth f n l = ((λ a, update_nth l n (f a)) <$> nth l n).get_or_else l
| 0     l      := by cases l; refl
| (n+1) []     := rfl
| (n+1) (b::l) := (congr_arg (cons b)
  (modify_nth_eq_update_nth n l)).trans $ by cases nth l n; refl

theorem nth_modify_nth (f : α → α) : ∀ n (l : list α) m,
  nth (modify_nth f n l) m = (λ a, if n = m then f a else a) <$> nth l m
| n     l      0     := by cases l; cases n; refl
| n     []     (m+1) := by cases n; refl
| 0     (a::l) (m+1) := by cases nth l m; refl
| (n+1) (a::l) (m+1) := (nth_modify_nth n l m).trans $
  by cases nth l m with b; by_cases n = m;
  simp only [h, if_pos, if_true, if_false, option.map_none, option.map_some, mt succ.inj,
    not_false_iff]

theorem modify_nth_tail_length (f : list α → list α) (H : ∀ l, length (f l) = length l) :
  ∀ n l, length (modify_nth_tail f n l) = length l
| 0     l      := H _
| (n+1) []     := rfl
| (n+1) (a::l) := @congr_arg _ _ _ _ (+1) (modify_nth_tail_length _ _)

@[simp] theorem modify_nth_length (f : α → α) :
  ∀ n l, length (modify_nth f n l) = length l :=
modify_nth_tail_length _ (λ l, by cases l; refl)

@[simp] theorem update_nth_length (l : list α) (n) (a : α) :
  length (update_nth l n a) = length l :=
by simp only [update_nth_eq_modify_nth, modify_nth_length]

@[simp] theorem nth_modify_nth_eq (f : α → α) (n) (l : list α) :
  nth (modify_nth f n l) n = f <$> nth l n :=
by simp only [nth_modify_nth, if_pos]

@[simp] theorem nth_modify_nth_ne (f : α → α) {m n} (l : list α) (h : m ≠ n) :
  nth (modify_nth f m l) n = nth l n :=
by simp only [nth_modify_nth, if_neg h, id_map']

theorem nth_update_nth_eq (a : α) (n) (l : list α) :
  nth (update_nth l n a) n = (λ _, a) <$> nth l n :=
by simp only [update_nth_eq_modify_nth, nth_modify_nth_eq]

theorem nth_update_nth_of_lt (a : α) {n} {l : list α} (h : n < length l) :
  nth (update_nth l n a) n = some a :=
by rw [nth_update_nth_eq, nth_le_nth h]; refl

theorem nth_update_nth_ne (a : α) {m n} (l : list α) (h : m ≠ n) :
  nth (update_nth l m a) n = nth l n :=
by simp only [update_nth_eq_modify_nth, nth_modify_nth_ne _ _ h]

@[simp] lemma update_nth_nil (n : ℕ) (a : α) : [].update_nth n a = [] := rfl

@[simp] lemma update_nth_succ (x : α) (xs : list α) (n : ℕ) (a : α) :
  (x :: xs).update_nth n.succ a = x :: xs.update_nth n a := rfl

lemma update_nth_comm (a b : α) : Π {n m : ℕ} (l : list α) (h : n ≠ m),
  (l.update_nth n a).update_nth m b = (l.update_nth m b).update_nth n a
| _ _ [] _ := by simp
| 0 0 (x :: t) h := absurd rfl h
| (n + 1) 0 (x :: t) h := by simp [list.update_nth]
| 0 (m + 1) (x :: t) h := by simp [list.update_nth]
| (n + 1) (m + 1) (x :: t) h := by { simp only [update_nth, true_and, eq_self_iff_true],
  exact update_nth_comm t (λ h', h $ nat.succ_inj'.mpr h'), }

@[simp] lemma nth_le_update_nth_eq (l : list α) (i : ℕ) (a : α)
  (h : i < (l.update_nth i a).length) : (l.update_nth i a).nth_le i h = a :=
by rw [← option.some_inj, ← nth_le_nth, nth_update_nth_eq, nth_le_nth]; simp * at *

@[simp] lemma nth_le_update_nth_of_ne {l : list α} {i j : ℕ} (h : i ≠ j) (a : α)
  (hj : j < (l.update_nth i a).length) :
  (l.update_nth i a).nth_le j hj = l.nth_le j (by simpa using hj) :=
by rw [← option.some_inj, ← list.nth_le_nth, list.nth_update_nth_ne _ _ h, list.nth_le_nth]

lemma mem_or_eq_of_mem_update_nth : ∀ {l : list α} {n : ℕ} {a b : α}
  (h : a ∈ l.update_nth n b), a ∈ l ∨ a = b
| []     n     a b h := false.elim h
| (c::l) 0     a b h := ((mem_cons_iff _ _ _).1 h).elim
  or.inr (or.inl ∘ mem_cons_of_mem _)
| (c::l) (n+1) a b h := ((mem_cons_iff _ _ _).1 h).elim
  (λ h, h ▸ or.inl (mem_cons_self _ _))
  (λ h, (mem_or_eq_of_mem_update_nth h).elim
    (or.inl ∘ mem_cons_of_mem _) or.inr)

section insert_nth
variable {a : α}

@[simp] lemma insert_nth_nil (a : α) : insert_nth 0 a [] = [a] := rfl

@[simp] lemma insert_nth_succ_nil (n : ℕ) (a : α) : insert_nth (n + 1) a [] = [] := rfl

lemma length_insert_nth : ∀n as, n ≤ length as → length (insert_nth n a as) = length as + 1
| 0     as       h := rfl
| (n+1) []       h := (nat.not_succ_le_zero _ h).elim
| (n+1) (a'::as) h := congr_arg nat.succ $ length_insert_nth n as (nat.le_of_succ_le_succ h)

lemma remove_nth_insert_nth (n:ℕ) (l : list α) : (l.insert_nth n a).remove_nth n = l :=
by rw [remove_nth_eq_nth_tail, insert_nth, modify_nth_tail_modify_nth_tail_same];
from modify_nth_tail_id _ _

lemma insert_nth_remove_nth_of_ge : ∀n m as, n < length as → n ≤ m →
  insert_nth m a (as.remove_nth n) = (as.insert_nth (m + 1) a).remove_nth n
| 0     0     []      has _   := (lt_irrefl _ has).elim
| 0     0     (a::as) has hmn := by simp [remove_nth, insert_nth]
| 0     (m+1) (a::as) has hmn := rfl
| (n+1) (m+1) (a::as) has hmn :=
  congr_arg (cons a) $
    insert_nth_remove_nth_of_ge n m as (nat.lt_of_succ_lt_succ has) (nat.le_of_succ_le_succ hmn)

lemma insert_nth_remove_nth_of_le : ∀n m as, n < length as → m ≤ n →
  insert_nth m a (as.remove_nth n) = (as.insert_nth m a).remove_nth (n + 1)
| n       0       (a :: as) has hmn := rfl
| (n + 1) (m + 1) (a :: as) has hmn :=
  congr_arg (cons a) $
    insert_nth_remove_nth_of_le n m as (nat.lt_of_succ_lt_succ has) (nat.le_of_succ_le_succ hmn)

lemma insert_nth_comm (a b : α) :
  ∀(i j : ℕ) (l : list α) (h : i ≤ j) (hj : j ≤ length l),
    (l.insert_nth i a).insert_nth (j + 1) b = (l.insert_nth j b).insert_nth i a
| 0       j     l      := by simp [insert_nth]
| (i + 1) 0     l      := assume h, (nat.not_lt_zero _ h).elim
| (i + 1) (j+1) []     := by simp
| (i + 1) (j+1) (c::l) :=
  assume h₀ h₁,
  by simp [insert_nth];
    exact insert_nth_comm i j l (nat.le_of_succ_le_succ h₀) (nat.le_of_succ_le_succ h₁)

lemma mem_insert_nth {a b : α} : ∀ {n : ℕ} {l : list α} (hi : n ≤ l.length),
  a ∈ l.insert_nth n b ↔ a = b ∨ a ∈ l
| 0     as       h := iff.rfl
| (n+1) []       h := (nat.not_succ_le_zero _ h).elim
| (n+1) (a'::as) h := begin
  dsimp [list.insert_nth],
  erw [list.mem_cons_iff, mem_insert_nth (nat.le_of_succ_le_succ h), list.mem_cons_iff,
    ← or.assoc, or_comm (a = a'), or.assoc]
end

end insert_nth

/-! ### map -/

@[simp] lemma map_nil (f : α → β) : map f [] = [] := rfl

theorem map_eq_foldr (f : α → β) (l : list α) :
  map f l = foldr (λ a bs, f a :: bs) [] l :=
by induction l; simp *

lemma map_congr {f g : α → β} : ∀ {l : list α}, (∀ x ∈ l, f x = g x) → map f l = map g l
| []     _ := rfl
| (a::l) h := let ⟨h₁, h₂⟩ := forall_mem_cons.1 h in
  by rw [map, map, h₁, map_congr h₂]

lemma map_eq_map_iff {f g : α → β} {l : list α} : map f l = map g l ↔ (∀ x ∈ l, f x = g x) :=
begin
  refine ⟨_, map_congr⟩, intros h x hx,
  rw [mem_iff_nth_le] at hx, rcases hx with ⟨n, hn, rfl⟩,
  rw [nth_le_map_rev f, nth_le_map_rev g], congr, exact h
end

theorem map_concat (f : α → β) (a : α) (l : list α) : map f (concat l a) = concat (map f l) (f a) :=
by induction l; [refl, simp only [*, concat_eq_append, cons_append, map, map_append]]; split; refl

theorem map_id' {f : α → α} (h : ∀ x, f x = x) (l : list α) : map f l = l :=
by induction l; [refl, simp only [*, map]]; split; refl

theorem eq_nil_of_map_eq_nil {f : α → β} {l : list α} (h : map f l = nil) : l = nil :=
eq_nil_of_length_eq_zero $ by rw [← length_map f l, h]; refl

@[simp] theorem map_join (f : α → β) (L : list (list α)) :
  map f (join L) = join (map (map f) L) :=
by induction L; [refl, simp only [*, join, map, map_append]]

theorem bind_ret_eq_map (f : α → β) (l : list α) :
  l.bind (list.ret ∘ f) = map f l :=
by unfold list.bind; induction l; simp only [map, join, list.ret, cons_append, nil_append, *];
  split; refl

@[simp] theorem map_eq_map {α β} (f : α → β) (l : list α) : f <$> l = map f l := rfl

@[simp] theorem map_tail (f : α → β) (l) : map f (tail l) = tail (map f l) :=
by cases l; refl

@[simp] theorem map_injective_iff {f : α → β} : injective (map f) ↔ injective f :=
begin
  split; intros h x y hxy,
  { suffices : [x] = [y], { simpa using this }, apply h, simp [hxy] },
  { induction y generalizing x, simpa using hxy,
    cases x, simpa using hxy, simp at hxy, simp [y_ih hxy.2, h hxy.1] }
end

/--
A single `list.map` of a composition of functions is equal to
composing a `list.map` with another `list.map`, fully applied.
This is the reverse direction of `list.map_map`.
-/
lemma comp_map (h : β → γ) (g : α → β) (l : list α) :
  map (h ∘ g) l = map h (map g l) := (map_map _ _ _).symm

/--
Composing a `list.map` with another `list.map` is equal to
a single `list.map` of composed functions.
-/
@[simp] lemma map_comp_map (g : β → γ) (f : α → β) :
  map g ∘ map f = map (g ∘ f) :=
by { ext l, rw comp_map }

theorem map_filter_eq_foldr (f : α → β) (p : α → Prop) [decidable_pred p] (as : list α) :
  map f (filter p as) = foldr (λ a bs, if p a then f a :: bs else bs) [] as :=
by { induction as, { refl }, { simp! [*, apply_ite (map f)] } }

lemma last_map (f : α → β) {l : list α} (hl : l ≠ []) :
  (l.map f).last (mt eq_nil_of_map_eq_nil hl) = f (l.last hl) :=
begin
  induction l with l_ih l_tl l_ih,
  { apply (hl rfl).elim },
  { cases l_tl,
    { simp },
    { simpa using l_ih } }
end

/-! ### map₂ -/

theorem nil_map₂ (f : α → β → γ) (l : list β) : map₂ f [] l = [] :=
by cases l; refl

theorem map₂_nil (f : α → β → γ) (l : list α) : map₂ f l [] = [] :=
by cases l; refl

@[simp] theorem map₂_flip (f : α → β → γ) :
  ∀ as bs, map₂ (flip f) bs as = map₂ f as bs
| [] [] := rfl
| [] (b :: bs) := rfl
| (a :: as) [] := rfl
| (a :: as) (b :: bs) := by { simp! [map₂_flip], refl }

/-! ### take, drop -/
@[simp] theorem take_zero (l : list α) : take 0 l = [] := rfl

@[simp] theorem take_nil : ∀ n, take n [] = ([] : list α)
| 0     := rfl
| (n+1) := rfl

theorem take_cons (n) (a : α) (l : list α) : take (succ n) (a::l) = a :: take n l := rfl

@[simp] theorem take_length : ∀ (l : list α), take (length l) l = l
| []     := rfl
| (a::l) := begin change a :: (take (length l) l) = a :: l, rw take_length end

theorem take_all_of_le : ∀ {n} {l : list α}, length l ≤ n → take n l = l
| 0     []     h := rfl
| 0     (a::l) h := absurd h (not_le_of_gt (zero_lt_succ _))
| (n+1) []     h := rfl
| (n+1) (a::l) h :=
  begin
    change a :: take n l = a :: l,
    rw [take_all_of_le (le_of_succ_le_succ h)]
  end

@[simp] theorem take_left : ∀ l₁ l₂ : list α, take (length l₁) (l₁ ++ l₂) = l₁
| []      l₂ := rfl
| (a::l₁) l₂ := congr_arg (cons a) (take_left l₁ l₂)

theorem take_left' {l₁ l₂ : list α} {n} (h : length l₁ = n) :
  take n (l₁ ++ l₂) = l₁ :=
by rw ← h; apply take_left

theorem take_take : ∀ (n m) (l : list α), take n (take m l) = take (min n m) l
| n         0        l      := by rw [min_zero, take_zero, take_nil]
| 0         m        l      := by rw [zero_min, take_zero, take_zero]
| (succ n)  (succ m) nil    := by simp only [take_nil]
| (succ n)  (succ m) (a::l) := by simp only [take, min_succ_succ, take_take n m l]; split; refl

theorem take_repeat (a : α) : ∀ (n m : ℕ), take n (repeat a m) = repeat a (min n m)
| n        0        := by simp
| 0        m        := by simp
| (succ n) (succ m) := by simp [min_succ_succ, take_repeat]

lemma map_take {α β : Type*} (f : α → β) :
  ∀ (L : list α) (i : ℕ), (L.take i).map f = (L.map f).take i
| [] i := by simp
| L 0 := by simp
| (h :: t) (n+1) := by { dsimp, rw [map_take], }

lemma take_append_of_le_length : ∀ {l₁ l₂ : list α} {n : ℕ},
  n ≤ l₁.length → (l₁ ++ l₂).take n = l₁.take n
| l₁      l₂ 0     hn := by simp
| []      l₂ (n+1) hn := absurd hn dec_trivial
| (a::l₁) l₂ (n+1) hn :=
by rw [list.take, list.cons_append, list.take, take_append_of_le_length (le_of_succ_le_succ hn)]

/-- Taking the first `l₁.length + i` elements in `l₁ ++ l₂` is the same as appending the first
`i` elements of `l₂` to `l₁`. -/
lemma take_append {l₁ l₂ : list α} (i : ℕ) :
  take (l₁.length + i) (l₁ ++ l₂) = l₁ ++ (take i l₂) :=
begin
  induction l₁, { simp },
  have : length l₁_tl + 1 + i = (length l₁_tl + i).succ,
    by { rw nat.succ_eq_add_one, exact succ_add _ _ },
  simp only [cons_append, length, this, take_cons, l₁_ih, eq_self_iff_true, and_self]
end

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the big list to the small list. -/
lemma nth_le_take (L : list α) {i j : ℕ} (hi : i < L.length) (hj : i < j) :
  nth_le L i hi = nth_le (L.take j) i (by { rw length_take, exact lt_min hj hi }) :=
by { rw nth_le_of_eq (take_append_drop j L).symm hi, exact nth_le_append _ _ }

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the small list to the big list. -/
lemma nth_le_take' (L : list α) {i j : ℕ} (hi : i < (L.take j).length) :
  nth_le (L.take j) i hi = nth_le L i (lt_of_lt_of_le hi (by simp [le_refl])) :=
by { simp at hi, rw nth_le_take L _ hi.1 }

lemma nth_take {l : list α} {n m : ℕ} (h : m < n) :
  (l.take n).nth m = l.nth m :=
begin
  induction n with n hn generalizing l m,
  { simp only [nat.nat_zero_eq_zero] at h,
    exact absurd h (not_lt_of_le m.zero_le) },
  { cases l with hd tl,
    { simp only [take_nil] },
    { cases m,
      { simp only [nth, take] },
      { simpa only using hn (nat.lt_of_succ_lt_succ h) } } },
end

@[simp] lemma nth_take_of_succ {l : list α} {n : ℕ} :
  (l.take (n + 1)).nth n = l.nth n :=
nth_take (nat.lt_succ_self n)

lemma take_succ {l : list α} {n : ℕ} :
  l.take (n + 1) = l.take n ++ (l.nth n).to_list :=
begin
  induction l with hd tl hl generalizing n,
  { simp only [option.to_list, nth, take_nil, append_nil]},
  { cases n,
    { simp only [option.to_list, nth, eq_self_iff_true, and_self, take, nil_append] },
    { simp only [hl, cons_append, nth, eq_self_iff_true, and_self, take] } }
end

@[simp] lemma take_eq_nil_iff {l : list α} {k : ℕ} :
  l.take k = [] ↔ l = [] ∨ k = 0 :=
by { cases l; cases k; simp [nat.succ_ne_zero] }

lemma init_eq_take (l : list α) : l.init = l.take l.length.pred :=
begin
  cases l with x l,
  { simp [init] },
  { induction l with hd tl hl generalizing x,
    { simp [init], },
    { simp [init, hl] } }
end

lemma init_take {n : ℕ} {l : list α} (h : n < l.length) :
  (l.take n).init = l.take n.pred :=
by simp [init_eq_take, min_eq_left_of_lt h, take_take, pred_le]

@[simp] lemma drop_eq_nil_of_le {l : list α} {k : ℕ} (h : l.length ≤ k) :
  l.drop k = [] :=
by simpa [←length_eq_zero] using nat.sub_eq_zero_of_le h

lemma drop_eq_nil_iff_le {l : list α} {k : ℕ} :
  l.drop k = [] ↔ l.length ≤ k :=
begin
  refine ⟨λ h, _, drop_eq_nil_of_le⟩,
  induction k with k hk generalizing l,
  { simp only [drop] at h,
    simp [h] },
  { cases l,
    { simp },
    { simp only [drop] at h,
      simpa [nat.succ_le_succ_iff] using hk h } }
end

lemma tail_drop (l : list α) (n : ℕ) : (l.drop n).tail = l.drop (n + 1) :=
begin
  induction l with hd tl hl generalizing n,
  { simp },
  { cases n,
    { simp },
    { simp [hl] } }
end

lemma cons_nth_le_drop_succ {l : list α} {n : ℕ} (hn : n < l.length) :
  l.nth_le n hn :: l.drop (n + 1) = l.drop n :=
begin
  induction l with hd tl hl generalizing n,
  { exact absurd n.zero_le (not_le_of_lt (by simpa using hn)) },
  { cases n,
    { simp },
    { simp only [nat.succ_lt_succ_iff, list.length] at hn,
      simpa [list.nth_le, list.drop] using hl hn } }
end

theorem drop_nil : ∀ n, drop n [] = ([] : list α) :=
λ _, drop_eq_nil_of_le (nat.zero_le _)

lemma mem_of_mem_drop {α} {n : ℕ} {l : list α} {x : α}
  (h : x ∈ l.drop n) :
  x ∈ l :=
begin
  induction l generalizing n,
  case list.nil : n h
  { simpa using h },
  case list.cons : l_hd l_tl l_ih n h
  { cases n; simp only [mem_cons_iff, drop] at h ⊢,
    { exact h },
    right, apply l_ih h },
end

@[simp] theorem drop_one : ∀ l : list α, drop 1 l = tail l
| []       := rfl
| (a :: l) := rfl

theorem drop_add : ∀ m n (l : list α), drop (m + n) l = drop m (drop n l)
| m 0     l      := rfl
| m (n+1) []     := (drop_nil _).symm
| m (n+1) (a::l) := drop_add m n _

@[simp] theorem drop_left : ∀ l₁ l₂ : list α, drop (length l₁) (l₁ ++ l₂) = l₂
| []      l₂ := rfl
| (a::l₁) l₂ := drop_left l₁ l₂

theorem drop_left' {l₁ l₂ : list α} {n} (h : length l₁ = n) :
  drop n (l₁ ++ l₂) = l₂ :=
by rw ← h; apply drop_left

theorem drop_eq_nth_le_cons : ∀ {n} {l : list α} h,
  drop n l = nth_le l n h :: drop (n+1) l
| 0     (a::l) h := rfl
| (n+1) (a::l) h := @drop_eq_nth_le_cons n _ _

@[simp] lemma drop_length (l : list α) : l.drop l.length = [] :=
calc l.drop l.length = (l ++ []).drop l.length : by simp
                 ... = [] : drop_left _ _

lemma drop_append_of_le_length : ∀ {l₁ l₂ : list α} {n : ℕ}, n ≤ l₁.length →
  (l₁ ++ l₂).drop n = l₁.drop n ++ l₂
| l₁      l₂ 0     hn := by simp
| []      l₂ (n+1) hn := absurd hn dec_trivial
| (a::l₁) l₂ (n+1) hn :=
by rw [drop, cons_append, drop, drop_append_of_le_length (le_of_succ_le_succ hn)]

/-- Dropping the elements up to `l₁.length + i` in `l₁ + l₂` is the same as dropping the elements
up to `i` in `l₂`. -/
lemma drop_append {l₁ l₂ : list α} (i : ℕ) :
  drop (l₁.length + i) (l₁ ++ l₂) = drop i l₂ :=
begin
  induction l₁, { simp },
  have : length l₁_tl + 1 + i = (length l₁_tl + i).succ,
    by { rw nat.succ_eq_add_one, exact succ_add _ _ },
  simp only [cons_append, length, this, drop, l₁_ih]
end

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the big list to the small list. -/
lemma nth_le_drop (L : list α) {i j : ℕ} (h : i + j < L.length) :
  nth_le L (i + j) h = nth_le (L.drop i) j
begin
  have A : i < L.length := lt_of_le_of_lt (nat.le.intro rfl) h,
  rw (take_append_drop i L).symm at h,
  simpa only [le_of_lt A, min_eq_left, add_lt_add_iff_left, length_take, length_append] using h
end :=
begin
  have A : length (take i L) = i, by simp [le_of_lt (lt_of_le_of_lt (nat.le.intro rfl) h)],
  rw [nth_le_of_eq (take_append_drop i L).symm h, nth_le_append_right];
  simp [A]
end

/--  The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the small list to the big list. -/
lemma nth_le_drop' (L : list α) {i j : ℕ} (h : j < (L.drop i).length) :
  nth_le (L.drop i) j h = nth_le L (i + j) (nat.add_lt_of_lt_sub_left ((length_drop i L) ▸ h)) :=
by rw nth_le_drop

lemma nth_drop (L : list α) (i j : ℕ) :
  nth (L.drop i) j = nth L (i + j) :=
begin
  ext,
  simp only [nth_eq_some, nth_le_drop', option.mem_def],
  split;
  exact λ ⟨h, ha⟩, ⟨by simpa [nat.lt_sub_left_iff_add_lt] using h, ha⟩
end

@[simp] theorem drop_drop (n : ℕ) : ∀ (m) (l : list α), drop n (drop m l) = drop (n + m) l
| m     []     := by simp
| 0     l      := by simp
| (m+1) (a::l) :=
  calc drop n (drop (m + 1) (a :: l)) = drop n (drop m l) : rfl
    ... = drop (n + m) l : drop_drop m l
    ... = drop (n + (m + 1)) (a :: l) : rfl

theorem drop_take : ∀ (m : ℕ) (n : ℕ) (l : list α),
  drop m (take (m + n) l) = take n (drop m l)
| 0     n _      := by simp
| (m+1) n nil    := by simp
| (m+1) n (_::l) :=
  have h: m + 1 + n = (m+n) + 1, by ac_refl,
  by simpa [take_cons, h] using drop_take m n l

lemma map_drop {α β : Type*} (f : α → β) :
  ∀ (L : list α) (i : ℕ), (L.drop i).map f = (L.map f).drop i
| [] i := by simp
| L 0 := by simp
| (h :: t) (n+1) := by { dsimp, rw [map_drop], }

theorem modify_nth_tail_eq_take_drop (f : list α → list α) (H : f [] = []) :
  ∀ n l, modify_nth_tail f n l = take n l ++ f (drop n l)
| 0     l      := rfl
| (n+1) []     := H.symm
| (n+1) (b::l) := congr_arg (cons b) (modify_nth_tail_eq_take_drop n l)

theorem modify_nth_eq_take_drop (f : α → α) :
  ∀ n l, modify_nth f n l = take n l ++ modify_head f (drop n l) :=
modify_nth_tail_eq_take_drop _ rfl

theorem modify_nth_eq_take_cons_drop (f : α → α) {n l} (h) :
  modify_nth f n l = take n l ++ f (nth_le l n h) :: drop (n+1) l :=
by rw [modify_nth_eq_take_drop, drop_eq_nth_le_cons h]; refl

theorem update_nth_eq_take_cons_drop (a : α) {n l} (h : n < length l) :
  update_nth l n a = take n l ++ a :: drop (n+1) l :=
by rw [update_nth_eq_modify_nth, modify_nth_eq_take_cons_drop _ h]

lemma reverse_take {α} {xs : list α} (n : ℕ)
  (h : n ≤ xs.length) :
  xs.reverse.take n = (xs.drop (xs.length - n)).reverse :=
begin
  induction xs generalizing n;
    simp only [reverse_cons, drop, reverse_nil, nat.zero_sub, length, take_nil],
  cases decidable.lt_or_eq_of_le h with h' h',
  { replace h' := le_of_succ_le_succ h',
    rwa [take_append_of_le_length, xs_ih _ h'],
    rw [show xs_tl.length + 1 - n = succ (xs_tl.length - n), from _, drop],
    { rwa [succ_eq_add_one, nat.sub_add_comm] },
    { rwa length_reverse } },
  { subst h', rw [length, nat.sub_self, drop],
    suffices : xs_tl.length + 1 = (xs_tl.reverse ++ [xs_hd]).length,
      by rw [this, take_length, reverse_cons],
    rw [length_append, length_reverse], refl }
end

@[simp] lemma update_nth_eq_nil (l : list α) (n : ℕ) (a : α) : l.update_nth n a = [] ↔ l = [] :=
by cases l; cases n; simp only [update_nth]

section take'
variable [inhabited α]

@[simp] theorem take'_length : ∀ n l, length (@take' α _ n l) = n
| 0     l := rfl
| (n+1) l := congr_arg succ (take'_length _ _)

@[simp] theorem take'_nil : ∀ n, take' n (@nil α) = repeat (default _) n
| 0     := rfl
| (n+1) := congr_arg (cons _) (take'_nil _)

theorem take'_eq_take : ∀ {n} {l : list α},
  n ≤ length l → take' n l = take n l
| 0     l      h := rfl
| (n+1) (a::l) h := congr_arg (cons _) $
  take'_eq_take $ le_of_succ_le_succ h

@[simp] theorem take'_left (l₁ l₂ : list α) : take' (length l₁) (l₁ ++ l₂) = l₁ :=
(take'_eq_take (by simp only [length_append, nat.le_add_right])).trans (take_left _ _)

theorem take'_left' {l₁ l₂ : list α} {n} (h : length l₁ = n) :
  take' n (l₁ ++ l₂) = l₁ :=
by rw ← h; apply take'_left

end take'

/-! ### foldl, foldr -/

lemma foldl_ext (f g : α → β → α) (a : α)
  {l : list β} (H : ∀ a : α, ∀ b ∈ l, f a b = g a b) :
  foldl f a l = foldl g a l :=
begin
  induction l with hd tl ih generalizing a, {refl},
  unfold foldl,
  rw [ih (λ a b bin, H a b $ mem_cons_of_mem _ bin), H a hd (mem_cons_self _ _)]
end

lemma foldr_ext (f g : α → β → β) (b : β)
  {l : list α} (H : ∀ a ∈ l, ∀ b : β, f a b = g a b) :
  foldr f b l = foldr g b l :=
begin
  induction l with hd tl ih, {refl},
  simp only [mem_cons_iff, or_imp_distrib, forall_and_distrib, forall_eq] at H,
  simp only [foldr, ih H.2, H.1]
end

@[simp] theorem foldl_nil (f : α → β → α) (a : α) : foldl f a [] = a := rfl

@[simp] theorem foldl_cons (f : α → β → α) (a : α) (b : β) (l : list β) :
  foldl f a (b::l) = foldl f (f a b) l := rfl

@[simp] theorem foldr_nil (f : α → β → β) (b : β) : foldr f b [] = b := rfl

@[simp] theorem foldr_cons (f : α → β → β) (b : β) (a : α) (l : list α) :
  foldr f b (a::l) = f a (foldr f b l) := rfl

@[simp] theorem foldl_append (f : α → β → α) :
  ∀ (a : α) (l₁ l₂ : list β), foldl f a (l₁++l₂) = foldl f (foldl f a l₁) l₂
| a []      l₂ := rfl
| a (b::l₁) l₂ := by simp only [cons_append, foldl_cons, foldl_append (f a b) l₁ l₂]

@[simp] theorem foldr_append (f : α → β → β) :
  ∀ (b : β) (l₁ l₂ : list α), foldr f b (l₁++l₂) = foldr f (foldr f b l₂) l₁
| b []      l₂ := rfl
| b (a::l₁) l₂ := by simp only [cons_append, foldr_cons, foldr_append b l₁ l₂]

@[simp] theorem foldl_join (f : α → β → α) :
  ∀ (a : α) (L : list (list β)), foldl f a (join L) = foldl (foldl f) a L
| a []     := rfl
| a (l::L) := by simp only [join, foldl_append, foldl_cons, foldl_join (foldl f a l) L]

@[simp] theorem foldr_join (f : α → β → β) :
  ∀ (b : β) (L : list (list α)), foldr f b (join L) = foldr (λ l b, foldr f b l) b L
| a []     := rfl
| a (l::L) := by simp only [join, foldr_append, foldr_join a L, foldr_cons]

theorem foldl_reverse (f : α → β → α) (a : α) (l : list β) :
  foldl f a (reverse l) = foldr (λx y, f y x) a l :=
by induction l; [refl, simp only [*, reverse_cons, foldl_append, foldl_cons, foldl_nil, foldr]]

theorem foldr_reverse (f : α → β → β) (a : β) (l : list α) :
  foldr f a (reverse l) = foldl (λx y, f y x) a l :=
let t := foldl_reverse (λx y, f y x) a (reverse l) in
by rw reverse_reverse l at t; rwa t

@[simp] theorem foldr_eta : ∀ (l : list α), foldr cons [] l = l
| []     := rfl
| (x::l) := by simp only [foldr_cons, foldr_eta l]; split; refl

@[simp] theorem reverse_foldl {l : list α} : reverse (foldl (λ t h, h :: t) [] l) = l :=
by rw ←foldr_reverse; simp

@[simp] theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : list β) :
  foldl f a (map g l) = foldl (λx y, f x (g y)) a l :=
by revert a; induction l; intros; [refl, simp only [*, map, foldl]]

@[simp] theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : list β) :
  foldr f a (map g l) = foldr (f ∘ g) a l :=
by revert a; induction l; intros; [refl, simp only [*, map, foldr]]

theorem foldl_map' {α β: Type u} (g : α → β) (f : α → α → α) (f' : β → β → β)
  (a : α) (l : list α) (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
  list.foldl f' (g a) (l.map g) = g (list.foldl f a l) :=
begin
  induction l generalizing a,
  { simp }, { simp [l_ih, h] }
end

theorem foldr_map' {α β: Type u} (g : α → β) (f : α → α → α) (f' : β → β → β)
  (a : α) (l : list α) (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
  list.foldr f' (g a) (l.map g) = g (list.foldr f a l) :=
begin
  induction l generalizing a,
  { simp }, { simp [l_ih, h] }
end

theorem foldl_hom (l : list γ) (f : α → β) (op : α → γ → α) (op' : β → γ → β) (a : α)
  (h : ∀a x, f (op a x) = op' (f a) x) : foldl op' (f a) l = f (foldl op a l) :=
eq.symm $ by { revert a, induction l; intros; [refl, simp only [*, foldl]] }

theorem foldr_hom (l : list γ) (f : α → β) (op : γ → α → α) (op' : γ → β → β) (a : α)
  (h : ∀x a, f (op x a) = op' x (f a)) : foldr op' (f a) l = f (foldr op a l) :=
by { revert a, induction l; intros; [refl, simp only [*, foldr]] }

lemma injective_foldl_comp {α : Type*} {l : list (α → α)} {f : α → α}
  (hl : ∀ f ∈ l, function.injective f) (hf : function.injective f):
  function.injective (@list.foldl (α → α) (α → α) function.comp f l) :=
begin
  induction l generalizing f,
  { exact hf },
  { apply l_ih (λ _ h, hl _ (list.mem_cons_of_mem _ h)),
    apply function.injective.comp hf,
    apply hl _ (list.mem_cons_self _ _) }
end

/- scanl -/

section scanl

variables {f : β → α → β} {b : β} {a : α} {l : list α}

lemma length_scanl :
  ∀ a l, length (scanl f a l) = l.length + 1
| a [] := rfl
| a (x :: l) := by erw [length_cons, length_cons, length_scanl]

@[simp] lemma scanl_nil (b : β) : scanl f b nil = [b] := rfl

@[simp] lemma scanl_cons :
  scanl f b (a :: l) = [b] ++ scanl f (f b a) l :=
by simp only [scanl, eq_self_iff_true, singleton_append, and_self]

@[simp] lemma nth_zero_scanl : (scanl f b l).nth 0 = some b :=
begin
  cases l,
  { simp only [nth, scanl_nil] },
  { simp only [nth, scanl_cons, singleton_append] }
end

@[simp] lemma nth_le_zero_scanl {h : 0 < (scanl f b l).length} :
  (scanl f b l).nth_le 0 h = b :=
begin
  cases l,
  { simp only [nth_le, scanl_nil] },
  { simp only [nth_le, scanl_cons, singleton_append] }
end

lemma nth_succ_scanl {i : ℕ} :
  (scanl f b l).nth (i + 1) = ((scanl f b l).nth i).bind (λ x, (l.nth i).map (λ y, f x y)) :=
begin
  induction l with hd tl hl generalizing b i,
  { symmetry,
    simp only [option.bind_eq_none', nth, forall_2_true_iff, not_false_iff, option.map_none',
               scanl_nil, option.not_mem_none, forall_true_iff] },
  { simp only [nth, scanl_cons, singleton_append],
    cases i,
    { simp only [option.map_some', nth_zero_scanl, nth, option.some_bind'] },
    { simp only [hl, nth] } }
end

lemma nth_le_succ_scanl {i : ℕ} {h : i + 1 < (scanl f b l).length} :
  (scanl f b l).nth_le (i + 1) h =
  f ((scanl f b l).nth_le i (nat.lt_of_succ_lt h))
    (l.nth_le i (nat.lt_of_succ_lt_succ (lt_of_lt_of_le h (le_of_eq (length_scanl b l))))) :=
begin
  induction i with i hi generalizing b l,
  { cases l,
    { simp only [length, zero_add, scanl_nil] at h,
      exact absurd h (lt_irrefl 1) },
    { simp only [scanl_cons, singleton_append, nth_le_zero_scanl, nth_le] } },
  { cases l,
    { simp only [length, add_lt_iff_neg_right, scanl_nil] at h,
      exact absurd h (not_lt_of_lt nat.succ_pos') },
    { simp_rw scanl_cons,
      rw nth_le_append_right _,
      { simpa only [hi, length, succ_add_sub_one] },
      { simp only [length, nat.zero_le, le_add_iff_nonneg_left] } } }
end

end scanl

/- scanr -/

@[simp] theorem scanr_nil (f : α → β → β) (b : β) : scanr f b [] = [b] := rfl

@[simp] theorem scanr_aux_cons (f : α → β → β) (b : β) : ∀ (a : α) (l : list α),
  scanr_aux f b (a::l) = (foldr f b (a::l), scanr f b l)
| a []     := rfl
| a (x::l) := let t := scanr_aux_cons x l in
  by simp only [scanr, scanr_aux, t, foldr_cons]

@[simp] theorem scanr_cons (f : α → β → β) (b : β) (a : α) (l : list α) :
  scanr f b (a::l) = foldr f b (a::l) :: scanr f b l :=
by simp only [scanr, scanr_aux_cons, foldr_cons]; split; refl

section foldl_eq_foldr
-- foldl and foldr coincide when f is commutative and associative
variables {f : α → α → α} (hcomm : commutative f) (hassoc : associative f)

include hassoc
theorem foldl1_eq_foldr1 : ∀ a b l, foldl f a (l++[b]) = foldr f b (a::l)
| a b nil      := rfl
| a b (c :: l) :=
  by simp only [cons_append, foldl_cons, foldr_cons, foldl1_eq_foldr1 _ _ l]; rw hassoc

include hcomm
theorem foldl_eq_of_comm_of_assoc : ∀ a b l, foldl f a (b::l) = f b (foldl f a l)
| a b  nil    := hcomm a b
| a b  (c::l) := by simp only [foldl_cons];
  rw [← foldl_eq_of_comm_of_assoc, right_comm _ hcomm hassoc]; refl

theorem foldl_eq_foldr : ∀ a l, foldl f a l = foldr f a l
| a nil      := rfl
| a (b :: l) :=
  by simp only [foldr_cons, foldl_eq_of_comm_of_assoc hcomm hassoc]; rw (foldl_eq_foldr a l)

end foldl_eq_foldr

section foldl_eq_foldlr'

variables {f : α → β → α}
variables hf : ∀ a b c, f (f a b) c = f (f a c) b
include hf

theorem foldl_eq_of_comm' : ∀ a b l, foldl f a (b::l) = f (foldl f a l) b
| a b [] := rfl
| a b (c :: l) := by rw [foldl,foldl,foldl,← foldl_eq_of_comm',foldl,hf]

theorem foldl_eq_foldr' : ∀ a l, foldl f a l = foldr (flip f) a l
| a [] := rfl
| a (b :: l) := by rw [foldl_eq_of_comm' hf,foldr,foldl_eq_foldr']; refl

end foldl_eq_foldlr'

section foldl_eq_foldlr'

variables {f : α → β → β}
variables hf : ∀ a b c, f a (f b c) = f b (f a c)
include hf

theorem foldr_eq_of_comm' : ∀ a b l, foldr f a (b::l) = foldr f (f b a) l
| a b [] := rfl
| a b (c :: l) := by rw [foldr,foldr,foldr,hf,← foldr_eq_of_comm']; refl

end foldl_eq_foldlr'

section
variables {op : α → α → α} [ha : is_associative α op] [hc : is_commutative α op]
local notation a * b := op a b
local notation l <*> a := foldl op a l

include ha

lemma foldl_assoc : ∀ {l : list α} {a₁ a₂}, l <*> (a₁ * a₂) = a₁ * (l <*> a₂)
| [] a₁ a₂ := rfl
| (a :: l) a₁ a₂ :=
  calc a::l <*> (a₁ * a₂) = l <*> (a₁ * (a₂ * a)) : by simp only [foldl_cons, ha.assoc]
    ... = a₁ * (a::l <*> a₂) : by rw [foldl_assoc, foldl_cons]

lemma foldl_op_eq_op_foldr_assoc : ∀{l : list α} {a₁ a₂}, (l <*> a₁) * a₂ = a₁ * l.foldr (*) a₂
| [] a₁ a₂ := rfl
| (a :: l) a₁ a₂ := by simp only [foldl_cons, foldr_cons, foldl_assoc, ha.assoc];
  rw [foldl_op_eq_op_foldr_assoc]

include hc

lemma foldl_assoc_comm_cons {l : list α} {a₁ a₂} : (a₁ :: l) <*> a₂ = a₁ * (l <*> a₂) :=
by rw [foldl_cons, hc.comm, foldl_assoc]

end

/-! ### mfoldl, mfoldr, mmap -/

section mfoldl_mfoldr
variables {m : Type v → Type w} [monad m]

@[simp] theorem mfoldl_nil (f : β → α → m β) {b} : mfoldl f b [] = pure b := rfl

@[simp] theorem mfoldr_nil (f : α → β → m β) {b} : mfoldr f b [] = pure b := rfl

@[simp] theorem mfoldl_cons {f : β → α → m β} {b a l} :
  mfoldl f b (a :: l) = f b a >>= λ b', mfoldl f b' l := rfl

@[simp] theorem mfoldr_cons {f : α → β → m β} {b a l} :
  mfoldr f b (a :: l) = mfoldr f b l >>= f a := rfl

theorem mfoldr_eq_foldr (f : α → β → m β) (b l) :
  mfoldr f b l = foldr (λ a mb, mb >>= f a) (pure b) l :=
by induction l; simp *

attribute [simp] mmap mmap'

variables [is_lawful_monad m]

theorem mfoldl_eq_foldl (f : β → α → m β) (b l) :
  mfoldl f b l = foldl (λ mb a, mb >>= λ b, f b a) (pure b) l :=
begin
  suffices h : ∀ (mb : m β),
    (mb >>= λ b, mfoldl f b l) = foldl (λ mb a, mb >>= λ b, f b a) mb l,
  by simp [←h (pure b)],
  induction l; intro,
  { simp },
  { simp only [mfoldl, foldl, ←l_ih] with monad_norm }
end

@[simp] theorem mfoldl_append {f : β → α → m β} : ∀ {b l₁ l₂},
  mfoldl f b (l₁ ++ l₂) = mfoldl f b l₁ >>= λ x, mfoldl f x l₂
| _ []     _ := by simp only [nil_append, mfoldl_nil, pure_bind]
| _ (_::_) _ := by simp only [cons_append, mfoldl_cons, mfoldl_append, bind_assoc]

@[simp] theorem mfoldr_append {f : α → β → m β} : ∀ {b l₁ l₂},
  mfoldr f b (l₁ ++ l₂) = mfoldr f b l₂ >>= λ x, mfoldr f x l₁
| _ []     _ := by simp only [nil_append, mfoldr_nil, bind_pure]
| _ (_::_) _ := by simp only [mfoldr_cons, cons_append, mfoldr_append, bind_assoc]

end mfoldl_mfoldr

/-! ### prod and sum -/

-- list.sum was already defined in defs.lean, but we couldn't tag it with `to_additive` yet.
attribute [to_additive] list.prod

section monoid
variables [monoid α] {l l₁ l₂ : list α} {a : α}

@[simp, to_additive]
theorem prod_nil : ([] : list α).prod = 1 := rfl

@[to_additive]
theorem prod_singleton : [a].prod = a := one_mul a

@[simp, to_additive]
theorem prod_cons : (a::l).prod = a * l.prod :=
calc (a::l).prod = foldl (*) (a * 1) l : by simp only [list.prod, foldl_cons, one_mul, mul_one]
  ... = _ : foldl_assoc

@[simp, to_additive]
theorem prod_append : (l₁ ++ l₂).prod = l₁.prod * l₂.prod :=
calc (l₁ ++ l₂).prod = foldl (*) (foldl (*) 1 l₁ * 1) l₂ : by simp [list.prod]
  ... = l₁.prod * l₂.prod : foldl_assoc

@[simp, to_additive]
theorem prod_join {l : list (list α)} : l.join.prod = (l.map list.prod).prod :=
by induction l; [refl, simp only [*, list.join, map, prod_append, prod_cons]]

/-- If zero is an element of a list `L`, then `list.prod L = 0`. If the domain is a nontrivial
monoid with zero with no divisors, then this implication becomes an `iff`, see
`list.prod_eq_zero_iff`. -/
theorem prod_eq_zero {M₀ : Type*} [monoid_with_zero M₀] {L : list M₀} (h : (0 : M₀) ∈ L) :
  L.prod = 0 :=
begin
  induction L with a L ihL,
  { exact absurd h (not_mem_nil _) },
  { rw prod_cons,
    cases (mem_cons_iff _ _ _).1 h with ha hL,
    exacts [mul_eq_zero_of_left ha.symm _, mul_eq_zero_of_right _ (ihL hL)] }
end

/-- Product of elements of a list `L` equals zero if and only if `0 ∈ L`. See also
`list.prod_eq_zero` for an implication that needs weaker typeclass assumptions. -/
@[simp] theorem prod_eq_zero_iff {M₀ : Type*} [monoid_with_zero M₀] [nontrivial M₀]
  [no_zero_divisors M₀] {L : list M₀} :
  L.prod = 0 ↔ (0 : M₀) ∈ L :=
begin
  induction L with a L ihL,
  { simp },
  { rw [prod_cons, mul_eq_zero, ihL, mem_cons_iff, eq_comm] }
end

theorem prod_ne_zero {M₀ : Type*} [monoid_with_zero M₀] [nontrivial M₀] [no_zero_divisors M₀]
  {L : list M₀} (hL : (0 : M₀) ∉ L) : L.prod ≠ 0 :=
mt prod_eq_zero_iff.1 hL

@[to_additive]
theorem prod_eq_foldr : l.prod = foldr (*) 1 l :=
list.rec_on l rfl $ λ a l ihl, by rw [prod_cons, foldr_cons, ihl]

@[to_additive]
theorem prod_hom_rel {α β γ : Type*} [monoid β] [monoid γ] (l : list α) {r : β → γ → Prop}
  {f : α → β} {g : α → γ} (h₁ : r 1 1) (h₂ : ∀⦃a b c⦄, r b c → r (f a * b) (g a * c)) :
  r (l.map f).prod (l.map g).prod :=
list.rec_on l h₁ (λ a l hl, by simp only [map_cons, prod_cons, h₂ hl])

@[to_additive]
theorem prod_hom [monoid β] (l : list α) (f : α →* β) :
  (l.map f).prod = f l.prod :=
by { simp only [prod, foldl_map, f.map_one.symm],
  exact l.foldl_hom _ _ _ 1 f.map_mul }

-- `to_additive` chokes on the next few lemmas, so we do them by hand below
@[simp]
lemma prod_take_mul_prod_drop :
  ∀ (L : list α) (i : ℕ), (L.take i).prod * (L.drop i).prod = L.prod
| [] i := by simp
| L 0 := by simp
| (h :: t) (n+1) := by { dsimp, rw [prod_cons, prod_cons, mul_assoc, prod_take_mul_prod_drop], }

@[simp]
lemma prod_take_succ :
  ∀ (L : list α) (i : ℕ) (p), (L.take (i + 1)).prod = (L.take i).prod * L.nth_le i p
| [] i p := by cases p
| (h :: t) 0 _ := by simp
| (h :: t) (n+1) _ := by { dsimp, rw [prod_cons, prod_cons, prod_take_succ, mul_assoc], }

/-- A list with product not one must have positive length. -/
lemma length_pos_of_prod_ne_one (L : list α) (h : L.prod ≠ 1) : 0 < L.length :=
by { cases L, { simp at h, cases h, }, { simp, }, }

lemma prod_update_nth : ∀ (L : list α) (n : ℕ) (a : α),
  (L.update_nth n a).prod =
    (L.take n).prod * (if n < L.length then a else 1) * (L.drop (n + 1)).prod
| (x::xs) 0     a := by simp [update_nth]
| (x::xs) (i+1) a := by simp [update_nth, prod_update_nth xs i a, mul_assoc]
| []      _     _ := by simp [update_nth, (nat.zero_le _).not_lt]

end monoid

lemma to_add_prod [add_monoid α] {l : list (multiplicative α)} :
  multiplicative.to_add l.prod = (l.map multiplicative.to_add).sum :=
by induction l; simp *

lemma to_mul_sum [monoid α] {l : list (additive α)} :
  additive.to_mul l.sum = (l.map additive.to_mul).prod :=
by induction l; simp *

section group
variables [group α]

/-- This is the `list.prod` version of `mul_inv_rev` -/
@[to_additive "This is the `list.sum` version of `add_neg_rev`"]
lemma prod_inv_reverse : ∀ (L : list α), L.prod⁻¹ = (L.map (λ x, x⁻¹)).reverse.prod
| [] := by simp
| (x :: xs) := by simp [prod_inv_reverse xs]

/-- A non-commutative variant of `list.prod_reverse` -/
@[to_additive "A non-commutative variant of `list.sum_reverse`"]
lemma prod_reverse_noncomm : ∀ (L : list α), L.reverse.prod = (L.map (λ x, x⁻¹)).prod⁻¹ :=
by simp [prod_inv_reverse]

end group

section comm_group
variables [comm_group α]

/-- This is the `list.prod` version of `mul_inv` -/
@[to_additive "This is the `list.sum` version of `add_neg`"]
lemma prod_inv : ∀ (L : list α), L.prod⁻¹ = (L.map (λ x, x⁻¹)).prod
| [] := by simp
| (x :: xs) := by simp [mul_comm, prod_inv xs]

end comm_group

@[simp]
lemma sum_take_add_sum_drop [add_monoid α] :
  ∀ (L : list α) (i : ℕ), (L.take i).sum + (L.drop i).sum = L.sum
| [] i := by simp
| L 0 := by simp
| (h :: t) (n+1) := by { dsimp, rw [sum_cons, sum_cons, add_assoc, sum_take_add_sum_drop], }

@[simp]
lemma sum_take_succ [add_monoid α] :
  ∀ (L : list α) (i : ℕ) (p), (L.take (i + 1)).sum = (L.take i).sum + L.nth_le i p
| [] i p := by cases p
| (h :: t) 0 _ := by simp
| (h :: t) (n+1) _ := by { dsimp, rw [sum_cons, sum_cons, sum_take_succ, add_assoc], }

lemma eq_of_sum_take_eq [add_left_cancel_monoid α] {L L' : list α} (h : L.length = L'.length)
  (h' : ∀ i ≤ L.length, (L.take i).sum = (L'.take i).sum) : L = L' :=
begin
  apply ext_le h (λ i h₁ h₂, _),
  have : (L.take (i + 1)).sum = (L'.take (i + 1)).sum := h' _ (nat.succ_le_of_lt h₁),
  rw [sum_take_succ L i h₁, sum_take_succ L' i h₂, h' i (le_of_lt h₁)] at this,
  exact add_left_cancel this
end

lemma monotone_sum_take [canonically_ordered_add_monoid α] (L : list α) :
  monotone (λ i, (L.take i).sum) :=
begin
  apply monotone_of_monotone_nat (λ n, _),
  by_cases h : n < L.length,
  { rw sum_take_succ _ _ h,
    exact le_add_right (le_refl _) },
  { push_neg at h,
    simp [take_all_of_le h, take_all_of_le (le_trans h (nat.le_succ _))] }
end

@[to_additive sum_nonneg]
lemma one_le_prod_of_one_le [ordered_comm_monoid α] {l : list α} (hl₁ : ∀ x ∈ l, (1 : α) ≤ x) :
  1 ≤ l.prod :=
begin
  induction l with hd tl ih,
  { simp },
  rw prod_cons,
  exact one_le_mul (hl₁ hd (mem_cons_self hd tl)) (ih (λ x h, hl₁ x (mem_cons_of_mem hd h))),
end

@[to_additive]
lemma single_le_prod [ordered_comm_monoid α] {l : list α} (hl₁ : ∀ x ∈ l, (1 : α) ≤ x) :
  ∀ x ∈ l, x ≤ l.prod :=
begin
  induction l,
  { simp },
  simp_rw [prod_cons, forall_mem_cons] at ⊢ hl₁,
  split,
  { exact le_mul_of_one_le_right' (one_le_prod_of_one_le hl₁.2) },
  { exact λ x H, le_mul_of_one_le_of_le hl₁.1 (l_ih hl₁.right x H) },
end

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
lemma all_one_of_le_one_le_of_prod_eq_one [ordered_comm_monoid α]
  {l : list α} (hl₁ : ∀ x ∈ l, (1 : α) ≤ x) (hl₂ : l.prod = 1) :
  ∀ x ∈ l, x = (1 : α) :=
λ x hx, le_antisymm (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)

lemma sum_eq_zero_iff [canonically_ordered_add_monoid α] (l : list α) :
  l.sum = 0 ↔ ∀ x ∈ l, x = (0 : α) :=
⟨all_zero_of_le_zero_le_of_sum_eq_zero (λ _ _, zero_le _),
begin
  induction l,
  { simp },
  { intro h,
    rw [sum_cons, add_eq_zero_iff],
    rw forall_mem_cons at h,
    exact ⟨h.1, l_ih h.2⟩ },
end⟩

/-- A list with sum not zero must have positive length. -/
lemma length_pos_of_sum_ne_zero [add_monoid α] (L : list α) (h : L.sum ≠ 0) : 0 < L.length :=
by { cases L, { simp at h, cases h, }, { simp, }, }

/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
lemma length_le_sum_of_one_le (L : list ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.sum :=
begin
  induction L with j L IH h, { simp },
  rw [sum_cons, length, add_comm],
  exact add_le_add (h _ (set.mem_insert _ _)) (IH (λ i hi, h i (set.mem_union_right _ hi)))
end

-- Now we tie those lemmas back to their multiplicative versions.
attribute [to_additive] prod_take_mul_prod_drop prod_take_succ length_pos_of_prod_ne_one

/-- A list with positive sum must have positive length. -/
-- This is an easy consequence of `length_pos_of_sum_ne_zero`, but often useful in applications.
lemma length_pos_of_sum_pos [ordered_cancel_add_comm_monoid α] (L : list α) (h : 0 < L.sum) :
  0 < L.length :=
length_pos_of_sum_ne_zero L (ne_of_gt h)

@[simp, to_additive]
theorem prod_erase [decidable_eq α] [comm_monoid α] {a} :
  Π {l : list α}, a ∈ l → a * (l.erase a).prod = l.prod
| (b::l) h :=
  begin
    rcases eq_or_ne_mem_of_mem h with rfl | ⟨ne, h⟩,
    { simp only [list.erase, if_pos, prod_cons] },
    { simp only [list.erase, if_neg (mt eq.symm ne), prod_cons, prod_erase h, mul_left_comm a b] }
  end

lemma dvd_prod [comm_monoid α] {a} {l : list α} (ha : a ∈ l) : a ∣ l.prod :=
let ⟨s, t, h⟩ := mem_split ha in
by rw [h, prod_append, prod_cons, mul_left_comm]; exact dvd_mul_right _ _

@[simp] theorem sum_const_nat (m n : ℕ) : sum (list.repeat m n) = m * n :=
by induction n; [refl, simp only [*, repeat_succ, sum_cons, nat.mul_succ, add_comm]]

theorem dvd_sum [comm_semiring α] {a} {l : list α} (h : ∀ x ∈ l, a ∣ x) : a ∣ l.sum :=
begin
  induction l with x l ih,
  { exact dvd_zero _ },
  { rw [list.sum_cons],
    exact dvd_add (h _ (mem_cons_self _ _)) (ih (λ x hx, h x (mem_cons_of_mem _ hx))) }
end

@[simp] theorem length_join (L : list (list α)) : length (join L) = sum (map length L) :=
by induction L; [refl, simp only [*, join, map, sum_cons, length_append]]

@[simp] theorem length_bind (l : list α) (f : α → list β) :
  length (list.bind l f) = sum (map (length ∘ f) l) :=
by rw [list.bind, length_join, map_map]

lemma exists_lt_of_sum_lt [linear_ordered_cancel_add_comm_monoid β] {l : list α}
  (f g : α → β) (h : (l.map f).sum < (l.map g).sum) : ∃ x ∈ l, f x < g x :=
begin
  induction l with x l,
  { exfalso, exact lt_irrefl _ h },
  { by_cases h' : f x < g x, exact ⟨x, mem_cons_self _ _, h'⟩,
    rcases l_ih _ with ⟨y, h1y, h2y⟩, refine ⟨y, mem_cons_of_mem x h1y, h2y⟩, simp at h,
    exact lt_of_add_lt_add_left (lt_of_lt_of_le h $ add_le_add_right (le_of_not_gt h') _) }
end

lemma exists_le_of_sum_le [linear_ordered_cancel_add_comm_monoid β] {l : list α}
  (hl : l ≠ []) (f g : α → β) (h : (l.map f).sum ≤ (l.map g).sum) : ∃ x ∈ l, f x ≤ g x :=
begin
  cases l with x l,
  { contradiction },
  { by_cases h' : f x ≤ g x, exact ⟨x, mem_cons_self _ _, h'⟩,
    rcases exists_lt_of_sum_lt f g _ with ⟨y, h1y, h2y⟩,
    exact ⟨y, mem_cons_of_mem x h1y, le_of_lt h2y⟩, simp at h,
    exact lt_of_add_lt_add_left (lt_of_le_of_lt h $ add_lt_add_right (lt_of_not_ge h') _) }
end

-- Several lemmas about sum/head/tail for `list ℕ`.
-- These are hard to generalize well, as they rely on the fact that `default ℕ = 0`.

-- We'd like to state this as `L.head * L.tail.prod = L.prod`,
-- but because `L.head` relies on an inhabited instances and
-- returns a garbage value for the empty list, this is not possible.
-- Instead we write the statement in terms of `(L.nth 0).get_or_else 1`,
-- and below, restate the lemma just for `ℕ`.
@[to_additive]
lemma head_mul_tail_prod' [monoid α] (L : list α) :
  (L.nth 0).get_or_else 1 * L.tail.prod = L.prod :=
by { cases L, { simp, refl, }, { simp, }, }

lemma head_add_tail_sum (L : list ℕ) : L.head + L.tail.sum = L.sum :=
by { cases L, { simp, refl, }, { simp, }, }

lemma head_le_sum (L : list ℕ) : L.head ≤ L.sum :=
nat.le.intro (head_add_tail_sum L)

lemma tail_sum (L : list ℕ) : L.tail.sum = L.sum - L.head :=
by rw [← head_add_tail_sum L, add_comm, nat.add_sub_cancel]

section
variables {G : Type*} [comm_group G]

attribute [to_additive] alternating_prod

@[simp, to_additive] lemma alternating_prod_nil :
  alternating_prod ([] : list G) = 1 := rfl

@[simp, to_additive] lemma alternating_prod_singleton (g : G) :
  alternating_prod [g] = g := rfl

@[simp, to_additive alternating_sum_cons_cons']
lemma alternating_prod_cons_cons (g h : G) (l : list G) :
  alternating_prod (g :: h :: l) = g * h⁻¹ * alternating_prod l := rfl

lemma alternating_sum_cons_cons {G : Type*} [add_comm_group G] (g h : G) (l : list G) :
  alternating_sum (g :: h :: l) = g - h + alternating_sum l :=
by rw [sub_eq_add_neg, alternating_sum]

end

/-! ### join -/

attribute [simp] join

theorem join_eq_nil : ∀ {L : list (list α)}, join L = [] ↔ ∀ l ∈ L, l = []
| []     := iff_of_true rfl (forall_mem_nil _)
| (l::L) := by simp only [join, append_eq_nil, join_eq_nil, forall_mem_cons]

@[simp] theorem join_append (L₁ L₂ : list (list α)) : join (L₁ ++ L₂) = join L₁ ++ join L₂ :=
by induction L₁; [refl, simp only [*, join, cons_append, append_assoc]]

lemma join_join (l : list (list (list α))) : l.join.join = (l.map join).join :=
by { induction l, simp, simp [l_ih] }

/-- In a join, taking the first elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join of the first `i` sublists. -/
lemma take_sum_join (L : list (list α)) (i : ℕ) :
  L.join.take ((L.map length).take i).sum = (L.take i).join :=
begin
  induction L generalizing i, { simp },
  cases i, { simp },
  simp [take_append, L_ih]
end

/-- In a join, dropping all the elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join after dropping the first `i` sublists. -/
lemma drop_sum_join (L : list (list α)) (i : ℕ) :
  L.join.drop ((L.map length).take i).sum = (L.drop i).join :=
begin
  induction L generalizing i, { simp },
  cases i, { simp },
  simp [drop_append, L_ih],
end

/-- Taking only the first `i+1` elements in a list, and then dropping the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
lemma drop_take_succ_eq_cons_nth_le (L : list α) {i : ℕ} (hi : i < L.length) :
  (L.take (i+1)).drop i = [nth_le L i hi] :=
begin
  induction L generalizing i,
  { simp only [length] at hi, exact (nat.not_succ_le_zero i hi).elim },
  cases i, { simp },
  have : i < L_tl.length,
  { simp at hi,
    exact nat.lt_of_succ_lt_succ hi },
  simp [L_ih this],
  refl
end

/-- In a join of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lenghts of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`. -/
lemma drop_take_succ_join_eq_nth_le (L : list (list α)) {i : ℕ} (hi : i < L.length) :
  (L.join.take ((L.map length).take (i+1)).sum).drop ((L.map length).take i).sum = nth_le L i hi :=
begin
  have : (L.map length).take i = ((L.take (i+1)).map length).take i, by simp [map_take, take_take],
  simp [take_sum_join, this, drop_sum_join, drop_take_succ_eq_cons_nth_le _ hi]
end

/-- Auxiliary lemma to control elements in a join. -/
lemma sum_take_map_length_lt1 (L : list (list α)) {i j : ℕ}
  (hi : i < L.length) (hj : j < (nth_le L i hi).length) :
  ((L.map length).take i).sum + j < ((L.map length).take (i+1)).sum :=
by simp [hi, sum_take_succ, hj]

/-- Auxiliary lemma to control elements in a join. -/
lemma sum_take_map_length_lt2 (L : list (list α)) {i j : ℕ}
  (hi : i < L.length) (hj : j < (nth_le L i hi).length) :
  ((L.map length).take i).sum + j < L.join.length :=
begin
  convert lt_of_lt_of_le (sum_take_map_length_lt1 L hi hj) (monotone_sum_take _ hi),
  have : L.length = (L.map length).length, by simp,
  simp [this, -length_map]
end

/-- The `n`-th element in a join of sublists is the `j`-th element of the `i`th sublist,
where `n` can be obtained in terms of `i` and `j` by adding the lengths of all the sublists
of index `< i`, and adding `j`. -/
lemma nth_le_join (L : list (list α)) {i j : ℕ}
  (hi : i < L.length) (hj : j < (nth_le L i hi).length) :
  nth_le L.join (((L.map length).take i).sum + j) (sum_take_map_length_lt2 L hi hj) =
  nth_le (nth_le L i hi) j hj :=
by rw [nth_le_take L.join (sum_take_map_length_lt2 L hi hj) (sum_take_map_length_lt1 L hi hj),
  nth_le_drop, nth_le_of_eq (drop_take_succ_join_eq_nth_le L hi)]

/-- Two lists of sublists are equal iff their joins coincide, as well as the lengths of the
sublists. -/
theorem eq_iff_join_eq (L L' : list (list α)) :
  L = L' ↔ L.join = L'.join ∧ map length L = map length L' :=
begin
  refine ⟨λ H, by simp [H], _⟩,
  rintros ⟨join_eq, length_eq⟩,
  apply ext_le,
  { have : length (map length L) = length (map length L'), by rw length_eq,
    simpa using this },
  { assume n h₁ h₂,
    rw [← drop_take_succ_join_eq_nth_le, ← drop_take_succ_join_eq_nth_le, join_eq, length_eq] }
end

/-! ### lexicographic ordering -/

/-- Given a strict order `<` on `α`, the lexicographic strict order on `list α`, for which
`[a0, ..., an] < [b0, ..., b_k]` if `a0 < b0` or `a0 = b0` and `[a1, ..., an] < [b1, ..., bk]`.
The definition is given for any relation `r`, not only strict orders. -/
inductive lex (r : α → α → Prop) : list α → list α → Prop
| nil {a l} : lex [] (a :: l)
| cons {a l₁ l₂} (h : lex l₁ l₂) : lex (a :: l₁) (a :: l₂)
| rel {a₁ l₁ a₂ l₂} (h : r a₁ a₂) : lex (a₁ :: l₁) (a₂ :: l₂)

namespace lex
theorem cons_iff {r : α → α → Prop} [is_irrefl α r] {a l₁ l₂} :
  lex r (a :: l₁) (a :: l₂) ↔ lex r l₁ l₂ :=
⟨λ h, by cases h with _ _ _ _ _ h _ _ _ _ h;
  [exact h, exact (irrefl_of r a h).elim], lex.cons⟩

@[simp] theorem not_nil_right (r : α → α → Prop) (l : list α) : ¬ lex r l [].

instance is_order_connected (r : α → α → Prop)
  [is_order_connected α r] [is_trichotomous α r] :
  is_order_connected (list α) (lex r) :=
⟨λ l₁, match l₁ with
| _,     [],    c::l₃, nil    := or.inr nil
| _,     [],    c::l₃, rel _ := or.inr nil
| _,     [],    c::l₃, cons _ := or.inr nil
| _,     b::l₂, c::l₃, nil := or.inl nil
| a::l₁, b::l₂, c::l₃, rel h :=
  (is_order_connected.conn _ b _ h).imp rel rel
| a::l₁, b::l₂, _::l₃, cons h := begin
    rcases trichotomous_of r a b with ab | rfl | ab,
    { exact or.inl (rel ab) },
    { exact (_match _ l₂ _ h).imp cons cons },
    { exact or.inr (rel ab) }
  end
end⟩

instance is_trichotomous (r : α → α → Prop) [is_trichotomous α r] :
  is_trichotomous (list α) (lex r) :=
⟨λ l₁, match l₁ with
| [], [] := or.inr (or.inl rfl)
| [], b::l₂ := or.inl nil
| a::l₁, [] := or.inr (or.inr nil)
| a::l₁, b::l₂ := begin
    rcases trichotomous_of r a b with ab | rfl | ab,
    { exact or.inl (rel ab) },
    { exact (_match l₁ l₂).imp cons
      (or.imp (congr_arg _) cons) },
    { exact or.inr (or.inr (rel ab)) }
  end
end⟩

instance is_asymm (r : α → α → Prop)
  [is_asymm α r] : is_asymm (list α) (lex r) :=
⟨λ l₁, match l₁ with
| a::l₁, b::l₂, lex.rel h₁, lex.rel h₂ := asymm h₁ h₂
| a::l₁, b::l₂, lex.rel h₁, lex.cons h₂ := asymm h₁ h₁
| a::l₁, b::l₂, lex.cons h₁, lex.rel h₂ := asymm h₂ h₂
| a::l₁, b::l₂, lex.cons h₁, lex.cons h₂ :=
  by exact _match _ _ h₁ h₂
end⟩

instance is_strict_total_order (r : α → α → Prop)
  [is_strict_total_order' α r] : is_strict_total_order' (list α) (lex r) :=
{..is_strict_weak_order_of_is_order_connected}

instance decidable_rel [decidable_eq α] (r : α → α → Prop)
  [decidable_rel r] : decidable_rel (lex r)
| l₁ [] := is_false $ λ h, by cases h
| [] (b::l₂) := is_true lex.nil
| (a::l₁) (b::l₂) := begin
  haveI := decidable_rel l₁ l₂,
  refine decidable_of_iff (r a b ∨ a = b ∧ lex r l₁ l₂) ⟨λ h, _, λ h, _⟩,
  { rcases h with h | ⟨rfl, h⟩,
    { exact lex.rel h },
    { exact lex.cons h } },
  { rcases h with _|⟨_,_,_,h⟩|⟨_,_,_,_,h⟩,
    { exact or.inr ⟨rfl, h⟩ },
    { exact or.inl h } }
end

theorem append_right (r : α → α → Prop) :
  ∀ {s₁ s₂} t, lex r s₁ s₂ → lex r s₁ (s₂ ++ t)
| _ _ t nil      := nil
| _ _ t (cons h) := cons (append_right _ h)
| _ _ t (rel r)  := rel r

theorem append_left (R : α → α → Prop) {t₁ t₂} (h : lex R t₁ t₂) :
  ∀ s, lex R (s ++ t₁) (s ++ t₂)
| []      := h
| (a::l) := cons (append_left l)

theorem imp {r s : α → α → Prop} (H : ∀ a b, r a b → s a b) :
  ∀ l₁ l₂, lex r l₁ l₂ → lex s l₁ l₂
| _ _ nil      := nil
| _ _ (cons h) := cons (imp _ _ h)
| _ _ (rel r)  := rel (H _ _ r)

theorem to_ne : ∀ {l₁ l₂ : list α}, lex (≠) l₁ l₂ → l₁ ≠ l₂
| _ _ (cons h) e := to_ne h (list.cons.inj e).2
| _ _ (rel r)  e := r (list.cons.inj e).1

theorem ne_iff {l₁ l₂ : list α} (H : length l₁ ≤ length l₂) :
  lex (≠) l₁ l₂ ↔ l₁ ≠ l₂ :=
⟨to_ne, λ h, begin
  induction l₁ with a l₁ IH generalizing l₂; cases l₂ with b l₂,
  { contradiction },
  { apply nil },
  { exact (not_lt_of_ge H).elim (succ_pos _) },
  { cases classical.em (a = b) with ab ab,
    { subst b, apply cons,
      exact IH (le_of_succ_le_succ H) (mt (congr_arg _) h) },
    { exact rel ab } }
end⟩

end lex

--Note: this overrides an instance in core lean
instance has_lt' [has_lt α] : has_lt (list α) := ⟨lex (<)⟩

theorem nil_lt_cons [has_lt α] (a : α) (l : list α) : [] < a :: l :=
lex.nil

instance [linear_order α] : linear_order (list α) :=
linear_order_of_STO' (lex (<))

--Note: this overrides an instance in core lean
instance has_le' [linear_order α] : has_le (list α) :=
preorder.to_has_le _

/-! ### all & any -/

@[simp] theorem all_nil (p : α → bool) : all [] p = tt := rfl

@[simp] theorem all_cons (p : α → bool) (a : α) (l : list α) :
  all (a::l) p = (p a && all l p) := rfl

theorem all_iff_forall {p : α → bool} {l : list α} : all l p ↔ ∀ a ∈ l, p a :=
begin
  induction l with a l ih,
  { exact iff_of_true rfl (forall_mem_nil _) },
  simp only [all_cons, band_coe_iff, ih, forall_mem_cons]
end

theorem all_iff_forall_prop {p : α → Prop} [decidable_pred p]
  {l : list α} : all l (λ a, p a) ↔ ∀ a ∈ l, p a :=
by simp only [all_iff_forall, bool.of_to_bool_iff]

@[simp] theorem any_nil (p : α → bool) : any [] p = ff := rfl

@[simp] theorem any_cons (p : α → bool) (a : α) (l : list α) :
  any (a::l) p = (p a || any l p) := rfl

theorem any_iff_exists {p : α → bool} {l : list α} : any l p ↔ ∃ a ∈ l, p a :=
begin
  induction l with a l ih,
  { exact iff_of_false bool.not_ff (not_exists_mem_nil _) },
  simp only [any_cons, bor_coe_iff, ih, exists_mem_cons_iff]
end

theorem any_iff_exists_prop {p : α → Prop} [decidable_pred p]
  {l : list α} : any l (λ a, p a) ↔ ∃ a ∈ l, p a :=
by simp [any_iff_exists]

theorem any_of_mem {p : α → bool} {a : α} {l : list α} (h₁ : a ∈ l) (h₂ : p a) : any l p :=
any_iff_exists.2 ⟨_, h₁, h₂⟩

@[priority 500] instance decidable_forall_mem {p : α → Prop} [decidable_pred p] (l : list α) :
  decidable (∀ x ∈ l, p x) :=
decidable_of_iff _ all_iff_forall_prop

instance decidable_exists_mem {p : α → Prop} [decidable_pred p] (l : list α) :
  decidable (∃ x ∈ l, p x) :=
decidable_of_iff _ any_iff_exists_prop

/-! ### map for partial functions -/

/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp] def pmap {p : α → Prop} (f : Π a, p a → β) : Π l : list α, (∀ a ∈ l, p a) → list β
| []     H := []
| (a::l) H := f a (forall_mem_cons.1 H).1 :: pmap l (forall_mem_cons.1 H).2

/-- "Attach" the proof that the elements of `l` are in `l` to produce a new list
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach (l : list α) : list {x // x ∈ l} := pmap subtype.mk l (λ a, id)

theorem sizeof_lt_sizeof_of_mem [has_sizeof α] {x : α} {l : list α} (hx : x ∈ l) :
  sizeof x < sizeof l :=
begin
  induction l with h t ih; cases hx,
  { rw hx, exact lt_add_of_lt_of_nonneg (lt_one_add _) (nat.zero_le _) },
  { exact lt_add_of_pos_of_le (zero_lt_one_add _) (le_of_lt (ih hx)) }
end

theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : list α) (H) :
  @pmap _ _ p (λ a _, f a) l H = map f l :=
by induction l; [refl, simp only [*, pmap, map]]; split; refl

theorem pmap_congr {p q : α → Prop} {f : Π a, p a → β} {g : Π a, q a → β}
  (l : list α) {H₁ H₂} (h : ∀ a h₁ h₂, f a h₁ = g a h₂) :
  pmap f l H₁ = pmap g l H₂ :=
by induction l with _ _ ih; [refl, rw [pmap, pmap, h, ih]]

theorem map_pmap {p : α → Prop} (g : β → γ) (f : Π a, p a → β)
  (l H) : map g (pmap f l H) = pmap (λ a h, g (f a h)) l H :=
by induction l; [refl, simp only [*, pmap, map]]; split; refl

theorem pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β)
  (l H) : pmap g (map f l) H = pmap (λ a h, g (f a) h) l (λ a h, H _ (mem_map_of_mem _ h)) :=
by induction l; [refl, simp only [*, pmap, map]]; split; refl

theorem pmap_eq_map_attach {p : α → Prop} (f : Π a, p a → β)
  (l H) : pmap f l H = l.attach.map (λ x, f x.1 (H _ x.2)) :=
by rw [attach, map_pmap]; exact pmap_congr l (λ a h₁ h₂, rfl)

theorem attach_map_val (l : list α) : l.attach.map subtype.val = l :=
by rw [attach, map_pmap]; exact (pmap_eq_map _ _ _ _).trans (map_id l)

@[simp] theorem mem_attach (l : list α) : ∀ x, x ∈ l.attach | ⟨a, h⟩ :=
by have := mem_map.1 (by rw [attach_map_val]; exact h);
   { rcases this with ⟨⟨_, _⟩, m, rfl⟩, exact m }

@[simp] theorem mem_pmap {p : α → Prop} {f : Π a, p a → β}
  {l H b} : b ∈ pmap f l H ↔ ∃ a (h : a ∈ l), f a (H a h) = b :=
by simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and, subtype.exists]

@[simp] theorem length_pmap {p : α → Prop} {f : Π a, p a → β}
  {l H} : length (pmap f l H) = length l :=
by induction l; [refl, simp only [*, pmap, length]]

@[simp] lemma length_attach (L : list α) : L.attach.length = L.length := length_pmap

@[simp] lemma pmap_eq_nil {p : α → Prop} {f : Π a, p a → β}
  {l H} : pmap f l H = [] ↔ l = [] :=
by rw [← length_eq_zero, length_pmap, length_eq_zero]

@[simp] lemma attach_eq_nil (l : list α) : l.attach = [] ↔ l = [] := pmap_eq_nil

lemma last_pmap {α β : Type*} (p : α → Prop) (f : Π a, p a → β)
  (l : list α) (hl₁ : ∀ a ∈ l, p a) (hl₂ : l ≠ []) :
  (l.pmap f hl₁).last (mt list.pmap_eq_nil.1 hl₂) = f (l.last hl₂) (hl₁ _ (list.last_mem hl₂)) :=
begin
  induction l with l_hd l_tl l_ih,
  { apply (hl₂ rfl).elim },
  { cases l_tl,
    { simp },
    { apply l_ih } }
end

lemma nth_pmap {p : α → Prop} (f : Π a, p a → β) {l : list α} (h : ∀ a ∈ l, p a) (n : ℕ) :
  nth (pmap f l h) n = option.pmap f (nth l n) (λ x H, h x (nth_mem H)) :=
begin
  induction l with hd tl hl generalizing n,
  { simp },
  { cases n; simp [hl] }
end

lemma nth_le_pmap {p : α → Prop} (f : Π a, p a → β) {l : list α} (h : ∀ a ∈ l, p a) {n : ℕ}
  (hn : n < (pmap f l h).length) :
  nth_le (pmap f l h) n hn = f (nth_le l n (@length_pmap _ _ p f l h ▸ hn))
    (h _ (nth_le_mem l n (@length_pmap _ _ p f l h ▸ hn))) :=
begin
  induction l with hd tl hl generalizing n,
  { simp only [length, pmap] at hn,
    exact absurd hn (not_lt_of_le n.zero_le) },
  { cases n,
    { simp },
    { simpa [hl] } }
end

/-! ### find -/

section find
variables {p : α → Prop} [decidable_pred p] {l : list α} {a : α}

@[simp] theorem find_nil (p : α → Prop) [decidable_pred p] : find p [] = none :=
rfl

@[simp] theorem find_cons_of_pos (l) (h : p a) : find p (a::l) = some a :=
if_pos h

@[simp] theorem find_cons_of_neg (l) (h : ¬ p a) : find p (a::l) = find p l :=
if_neg h

@[simp] theorem find_eq_none : find p l = none ↔ ∀ x ∈ l, ¬ p x :=
begin
  induction l with a l IH,
  { exact iff_of_true rfl (forall_mem_nil _) },
  rw forall_mem_cons, by_cases h : p a,
  { simp only [find_cons_of_pos _ h, h, not_true, false_and] },
  { rwa [find_cons_of_neg _ h, iff_true_intro h, true_and] }
end

theorem find_some (H : find p l = some a) : p a :=
begin
  induction l with b l IH, {contradiction},
  by_cases h : p b,
  { rw find_cons_of_pos _ h at H, cases H, exact h },
  { rw find_cons_of_neg _ h at H, exact IH H }
end

@[simp] theorem find_mem (H : find p l = some a) : a ∈ l :=
begin
  induction l with b l IH, {contradiction},
  by_cases h : p b,
  { rw find_cons_of_pos _ h at H, cases H, apply mem_cons_self },
  { rw find_cons_of_neg _ h at H, exact mem_cons_of_mem _ (IH H) }
end

end find

/-! ### lookmap -/
section lookmap
variables (f : α → option α)

@[simp] theorem lookmap_nil : [].lookmap f = [] := rfl

@[simp] theorem lookmap_cons_none {a : α} (l : list α) (h : f a = none) :
  (a :: l).lookmap f = a :: l.lookmap f :=
by simp [lookmap, h]

@[simp] theorem lookmap_cons_some {a b : α} (l : list α) (h : f a = some b) :
  (a :: l).lookmap f = b :: l :=
by simp [lookmap, h]

theorem lookmap_some : ∀ l : list α, l.lookmap some = l
| []     := rfl
| (a::l) := rfl

theorem lookmap_none : ∀ l : list α, l.lookmap (λ _, none) = l
| []     := rfl
| (a::l) := congr_arg (cons a) (lookmap_none l)

theorem lookmap_congr {f g : α → option α} :
  ∀ {l : list α}, (∀ a ∈ l, f a = g a) → l.lookmap f = l.lookmap g
| []     H := rfl
| (a::l) H := begin
  cases forall_mem_cons.1 H with H₁ H₂,
  cases h : g a with b,
  { simp [h, H₁.trans h, lookmap_congr H₂] },
  { simp [lookmap_cons_some _ _ h, lookmap_cons_some _ _ (H₁.trans h)] }
end

theorem lookmap_of_forall_not {l : list α} (H : ∀ a ∈ l, f a = none) : l.lookmap f = l :=
(lookmap_congr H).trans (lookmap_none l)

theorem lookmap_map_eq (g : α → β) (h : ∀ a (b ∈ f a), g a = g b) :
  ∀ l : list α, map g (l.lookmap f) = map g l
| []     := rfl
| (a::l) := begin
  cases h' : f a with b,
  { simp [h', lookmap_map_eq] },
  { simp [lookmap_cons_some _ _ h', h _ _ h'] }
end

theorem lookmap_id' (h : ∀ a (b ∈ f a), a = b) (l : list α) : l.lookmap f = l :=
by rw [← map_id (l.lookmap f), lookmap_map_eq, map_id]; exact h

theorem length_lookmap (l : list α) : length (l.lookmap f) = length l :=
by rw [← length_map, lookmap_map_eq _ (λ _, ()), length_map]; simp

end lookmap

/-! ### filter_map -/

@[simp] theorem filter_map_nil (f : α → option β) : filter_map f [] = [] := rfl

@[simp] theorem filter_map_cons_none {f : α → option β} (a : α) (l : list α) (h : f a = none) :
  filter_map f (a :: l) = filter_map f l :=
by simp only [filter_map, h]

@[simp] theorem filter_map_cons_some (f : α → option β)
  (a : α) (l : list α) {b : β} (h : f a = some b) :
  filter_map f (a :: l) = b :: filter_map f l :=
by simp only [filter_map, h]; split; refl

lemma filter_map_append {α β : Type*} (l l' : list α) (f : α → option β) :
  filter_map f (l ++ l') = filter_map f l ++ filter_map f l' :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { rw [cons_append, filter_map, filter_map],
    cases f hd;
    simp only [filter_map, hl, cons_append, eq_self_iff_true, and_self] }
end

theorem filter_map_eq_map (f : α → β) : filter_map (some ∘ f) = map f :=
begin
  funext l,
  induction l with a l IH, {refl},
  simp only [filter_map_cons_some (some ∘ f) _ _ rfl, IH, map_cons], split; refl
end

theorem filter_map_eq_filter (p : α → Prop) [decidable_pred p] :
  filter_map (option.guard p) = filter p :=
begin
  funext l,
  induction l with a l IH, {refl},
  by_cases pa : p a,
  { simp only [filter_map, option.guard, IH, if_pos pa, filter_cons_of_pos _ pa], split; refl },
  { simp only [filter_map, option.guard, IH, if_neg pa, filter_cons_of_neg _ pa] }
end

theorem filter_map_filter_map (f : α → option β) (g : β → option γ) (l : list α) :
  filter_map g (filter_map f l) = filter_map (λ x, (f x).bind g) l :=
begin
  induction l with a l IH, {refl},
  cases h : f a with b,
  { rw [filter_map_cons_none _ _ h, filter_map_cons_none, IH],
    simp only [h, option.none_bind'] },
  rw filter_map_cons_some _ _ _ h,
  cases h' : g b with c;
  [ rw [filter_map_cons_none _ _ h', filter_map_cons_none, IH],
    rw [filter_map_cons_some _ _ _ h', filter_map_cons_some, IH] ];
  simp only [h, h', option.some_bind']
end

theorem map_filter_map (f : α → option β) (g : β → γ) (l : list α) :
  map g (filter_map f l) = filter_map (λ x, (f x).map g) l :=
by rw [← filter_map_eq_map, filter_map_filter_map]; refl

theorem filter_map_map (f : α → β) (g : β → option γ) (l : list α) :
  filter_map g (map f l) = filter_map (g ∘ f) l :=
by rw [← filter_map_eq_map, filter_map_filter_map]; refl

theorem filter_filter_map (f : α → option β) (p : β → Prop) [decidable_pred p] (l : list α) :
  filter p (filter_map f l) = filter_map (λ x, (f x).filter p) l :=
by rw [← filter_map_eq_filter, filter_map_filter_map]; refl

theorem filter_map_filter (p : α → Prop) [decidable_pred p] (f : α → option β) (l : list α) :
  filter_map f (filter p l) = filter_map (λ x, if p x then f x else none) l :=
begin
  rw [← filter_map_eq_filter, filter_map_filter_map], congr,
  funext x,
  show (option.guard p x).bind f = ite (p x) (f x) none,
  by_cases h : p x,
  { simp only [option.guard, if_pos h, option.some_bind'] },
  { simp only [option.guard, if_neg h, option.none_bind'] }
end

@[simp] theorem filter_map_some (l : list α) : filter_map some l = l :=
by rw filter_map_eq_map; apply map_id

@[simp] theorem mem_filter_map (f : α → option β) (l : list α) {b : β} :
  b ∈ filter_map f l ↔ ∃ a, a ∈ l ∧ f a = some b :=
begin
  induction l with a l IH,
  { split, { intro H, cases H }, { rintro ⟨_, H, _⟩, cases H } },
  cases h : f a with b',
  { have : f a ≠ some b, {rw h, intro, contradiction},
    simp only [filter_map_cons_none _ _ h, IH, mem_cons_iff,
      or_and_distrib_right, exists_or_distrib, exists_eq_left, this, false_or] },
  { have : f a = some b ↔ b = b',
    { split; intro t, {rw t at h; injection h}, {exact t.symm ▸ h} },
      simp only [filter_map_cons_some _ _ _ h, IH, mem_cons_iff,
        or_and_distrib_right, exists_or_distrib, this, exists_eq_left] }
end

theorem map_filter_map_of_inv (f : α → option β) (g : β → α)
  (H : ∀ x : α, (f x).map g = some x) (l : list α) :
  map g (filter_map f l) = l :=
by simp only [map_filter_map, H, filter_map_some]

theorem sublist.filter_map (f : α → option β) {l₁ l₂ : list α}
  (s : l₁ <+ l₂) : filter_map f l₁ <+ filter_map f l₂ :=
by induction s with l₁ l₂ a s IH l₁ l₂ a s IH;
   simp only [filter_map]; cases f a with b;
   simp only [filter_map, IH, sublist.cons, sublist.cons2]

theorem sublist.map (f : α → β) {l₁ l₂ : list α}
  (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ :=
filter_map_eq_map f ▸ s.filter_map _

/-! ### reduce_option -/

@[simp] lemma reduce_option_cons_of_some (x : α) (l : list (option α)) :
  reduce_option (some x :: l) = x :: l.reduce_option :=
by simp only [reduce_option, filter_map, id.def, eq_self_iff_true, and_self]

@[simp] lemma reduce_option_cons_of_none (l : list (option α)) :
  reduce_option (none :: l) = l.reduce_option :=
by simp only [reduce_option, filter_map, id.def]

@[simp] lemma reduce_option_nil : @reduce_option α [] = [] := rfl

@[simp] lemma reduce_option_map {l : list (option α)} {f : α → β} :
  reduce_option (map (option.map f) l) = map f (reduce_option l) :=
begin
  induction l with hd tl hl,
  { simp only [reduce_option_nil, map_nil] },
  { cases hd;
    simpa only [true_and, option.map_some', map, eq_self_iff_true,
                reduce_option_cons_of_some] using hl },
end

lemma reduce_option_append (l l' : list (option α)) :
  (l ++ l').reduce_option = l.reduce_option ++ l'.reduce_option :=
filter_map_append l l' id

lemma reduce_option_length_le (l : list (option α)) :
  l.reduce_option.length ≤ l.length :=
begin
  induction l with hd tl hl,
  { simp only [reduce_option_nil, length] },
  { cases hd,
    { exact nat.le_succ_of_le hl },
    { simpa only [length, add_le_add_iff_right, reduce_option_cons_of_some] using hl} }
end

lemma reduce_option_length_eq_iff {l : list (option α)} :
  l.reduce_option.length = l.length ↔ ∀ x ∈ l, option.is_some x :=
begin
  induction l with hd tl hl,
  { simp only [forall_const, reduce_option_nil, not_mem_nil,
               forall_prop_of_false, eq_self_iff_true, length, not_false_iff] },
  { cases hd,
    { simp only [mem_cons_iff, forall_eq_or_imp, bool.coe_sort_ff, false_and,
                 reduce_option_cons_of_none, length, option.is_some_none, iff_false],
      intro H,
      have := reduce_option_length_le tl,
      rw H at this,
      exact absurd (nat.lt_succ_self _) (not_lt_of_le this) },
    { simp only [hl, true_and, mem_cons_iff, forall_eq_or_imp, add_left_inj,
                 bool.coe_sort_tt, length, option.is_some_some, reduce_option_cons_of_some] } }
end

lemma reduce_option_length_lt_iff {l : list (option α)} :
  l.reduce_option.length < l.length ↔ none ∈ l :=
begin
  convert not_iff_not.mpr reduce_option_length_eq_iff;
  simp [lt_iff_le_and_ne, reduce_option_length_le l, option.is_none_iff_eq_none]
end

lemma reduce_option_singleton (x : option α) :
  [x].reduce_option = x.to_list :=
by cases x; refl

lemma reduce_option_concat (l : list (option α)) (x : option α) :
  (l.concat x).reduce_option = l.reduce_option ++ x.to_list :=
begin
  induction l with hd tl hl generalizing x,
  { cases x;
    simp [option.to_list] },
  { simp only [concat_eq_append, reduce_option_append] at hl,
    cases hd;
    simp [hl, reduce_option_append] }
end

lemma reduce_option_concat_of_some (l : list (option α)) (x : α) :
  (l.concat (some x)).reduce_option = l.reduce_option.concat x :=
by simp only [reduce_option_nil, concat_eq_append, reduce_option_append, reduce_option_cons_of_some]

lemma reduce_option_mem_iff {l : list (option α)} {x : α} :
  x ∈ l.reduce_option ↔ (some x) ∈ l :=
by simp only [reduce_option, id.def, mem_filter_map, exists_eq_right]


lemma reduce_option_nth_iff {l : list (option α)} {x : α} :
  (∃ i, l.nth i = some (some x)) ↔ ∃ i, l.reduce_option.nth i = some x :=
by rw [←mem_iff_nth, ←mem_iff_nth, reduce_option_mem_iff]

/-! ### filter -/

section filter
variables {p : α → Prop} [decidable_pred p]

theorem filter_eq_foldr (p : α → Prop) [decidable_pred p] (l : list α) :
  filter p l = foldr (λ a out, if p a then a :: out else out) [] l :=
by induction l; simp [*, filter]

lemma filter_congr {p q : α → Prop} [decidable_pred p] [decidable_pred q]
  : ∀ {l : list α}, (∀ x ∈ l, p x ↔ q x) → filter p l = filter q l
| [] _     := rfl
| (a::l) h := by rw forall_mem_cons at h; by_cases pa : p a;
  [simp only [filter_cons_of_pos _ pa, filter_cons_of_pos _ (h.1.1 pa), filter_congr h.2],
   simp only [filter_cons_of_neg _ pa, filter_cons_of_neg _ (mt h.1.2 pa), filter_congr h.2]];
     split; refl

@[simp] theorem filter_subset (l : list α) : filter p l ⊆ l :=
(filter_sublist l).subset

theorem of_mem_filter {a : α} : ∀ {l}, a ∈ filter p l → p a
| (b::l) ain :=
  if pb : p b then
    have a ∈ b :: filter p l, by simpa only [filter_cons_of_pos _ pb] using ain,
    or.elim (eq_or_mem_of_mem_cons this)
      (assume : a = b, begin rw [← this] at pb, exact pb end)
      (assume : a ∈ filter p l, of_mem_filter this)
  else
    begin simp only [filter_cons_of_neg _ pb] at ain, exact (of_mem_filter ain) end

theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
filter_subset l h

theorem mem_filter_of_mem {a : α} : ∀ {l}, a ∈ l → p a → a ∈ filter p l
| (_::l) (or.inl rfl) pa := by rw filter_cons_of_pos _ pa; apply mem_cons_self
| (b::l) (or.inr ain) pa := if pb : p b
    then by rw [filter_cons_of_pos _ pb]; apply mem_cons_of_mem; apply mem_filter_of_mem ain pa
    else by rw [filter_cons_of_neg _ pb]; apply mem_filter_of_mem ain pa

@[simp] theorem mem_filter {a : α} {l} : a ∈ filter p l ↔ a ∈ l ∧ p a :=
⟨λ h, ⟨mem_of_mem_filter h, of_mem_filter h⟩, λ ⟨h₁, h₂⟩, mem_filter_of_mem h₁ h₂⟩

theorem filter_eq_self {l} : filter p l = l ↔ ∀ a ∈ l, p a :=
begin
  induction l with a l ih,
  { exact iff_of_true rfl (forall_mem_nil _) },
  rw forall_mem_cons, by_cases p a,
  { rw [filter_cons_of_pos _ h, cons_inj, ih, and_iff_right h] },
  { rw [filter_cons_of_neg _ h],
    refine iff_of_false _ (mt and.left h), intro e,
    have := filter_sublist l, rw e at this,
    exact not_lt_of_ge (length_le_of_sublist this) (lt_succ_self _) }
end

theorem filter_eq_nil {l} : filter p l = [] ↔ ∀ a ∈ l, ¬p a :=
by simp only [eq_nil_iff_forall_not_mem, mem_filter, not_and]

variable (p)
theorem filter_sublist_filter {l₁ l₂} (s : l₁ <+ l₂) : filter p l₁ <+ filter p l₂ :=
filter_map_eq_filter p ▸ s.filter_map _

theorem map_filter (f : β → α) (l : list β) :
  filter p (map f l) = map f (filter (p ∘ f) l) :=
by rw [← filter_map_eq_map, filter_filter_map, filter_map_filter]; refl

@[simp] theorem filter_filter (q) [decidable_pred q] : ∀ l,
  filter p (filter q l) = filter (λ a, p a ∧ q a) l
| [] := rfl
| (a :: l) := by by_cases hp : p a; by_cases hq : q a; simp only [hp, hq, filter, if_true, if_false,
    true_and, false_and, filter_filter l, eq_self_iff_true]

@[simp] lemma filter_true {h : decidable_pred (λ a : α, true)} (l : list α) :
  @filter α (λ _, true) h l = l :=
by convert filter_eq_self.2 (λ _ _, trivial)

@[simp] lemma filter_false {h : decidable_pred (λ a : α, false)} (l : list α) :
  @filter α (λ _, false) h l = [] :=
by convert filter_eq_nil.2 (λ _ _, id)

@[simp] theorem span_eq_take_drop : ∀ (l : list α), span p l = (take_while p l, drop_while p l)
| []     := rfl
| (a::l) :=
    if pa : p a then by simp only [span, if_pos pa, span_eq_take_drop l, take_while, drop_while]
    else by simp only [span, take_while, drop_while, if_neg pa]

@[simp] theorem take_while_append_drop : ∀ (l : list α), take_while p l ++ drop_while p l = l
| []     := rfl
| (a::l) := if pa : p a then by rw [take_while, drop_while, if_pos pa, if_pos pa, cons_append,
      take_while_append_drop l]
    else by rw [take_while, drop_while, if_neg pa, if_neg pa, nil_append]

@[simp] theorem countp_nil : countp p [] = 0 := rfl

@[simp] theorem countp_cons_of_pos {a : α} (l) (pa : p a) : countp p (a::l) = countp p l + 1 :=
if_pos pa

@[simp] theorem countp_cons_of_neg {a : α} (l) (pa : ¬ p a) : countp p (a::l) = countp p l :=
if_neg pa

theorem countp_eq_length_filter (l) : countp p l = length (filter p l) :=
by induction l with x l ih; [refl, by_cases (p x)];
  [simp only [filter_cons_of_pos _ h, countp, ih, if_pos h],
   simp only [countp_cons_of_neg _ _ h, ih, filter_cons_of_neg _ h]]; refl

local attribute [simp] countp_eq_length_filter

@[simp] theorem countp_append (l₁ l₂) : countp p (l₁ ++ l₂) = countp p l₁ + countp p l₂ :=
by simp only [countp_eq_length_filter, filter_append, length_append]

theorem countp_pos {l} : 0 < countp p l ↔ ∃ a ∈ l, p a :=
by simp only [countp_eq_length_filter, length_pos_iff_exists_mem, mem_filter, exists_prop]

theorem countp_le_of_sublist {l₁ l₂} (s : l₁ <+ l₂) : countp p l₁ ≤ countp p l₂ :=
by simpa only [countp_eq_length_filter] using length_le_of_sublist (filter_sublist_filter p s)

@[simp] theorem countp_filter {q} [decidable_pred q] (l : list α) :
  countp p (filter q l) = countp (λ a, p a ∧ q a) l :=
by simp only [countp_eq_length_filter, filter_filter]

end filter

/-! ### count -/

section count
variable [decidable_eq α]

@[simp] theorem count_nil (a : α) : count a [] = 0 := rfl

theorem count_cons (a b : α) (l : list α) :
  count a (b :: l) = if a = b then succ (count a l) else count a l := rfl

theorem count_cons' (a b : α) (l : list α) :
  count a (b :: l) = count a l + (if a = b then 1 else 0) :=
begin rw count_cons, split_ifs; refl end

@[simp] theorem count_cons_self (a : α) (l : list α) : count a (a::l) = succ (count a l) :=
if_pos rfl

@[simp, priority 990]
theorem count_cons_of_ne {a b : α} (h : a ≠ b) (l : list α) : count a (b::l) = count a l :=
if_neg h

theorem count_tail : Π (l : list α) (a : α) (h : 0 < l.length),
  l.tail.count a = l.count a - ite (a = list.nth_le l 0 h) 1 0
| (_ :: _) a h := by { rw [count_cons], split_ifs; simp }

theorem count_le_of_sublist (a : α) {l₁ l₂} : l₁ <+ l₂ → count a l₁ ≤ count a l₂ :=
countp_le_of_sublist _

theorem count_le_count_cons (a b : α) (l : list α) : count a l ≤ count a (b :: l) :=
count_le_of_sublist _ (sublist_cons _ _)

theorem count_singleton (a : α) : count a [a] = 1 := if_pos rfl

@[simp] theorem count_append (a : α) : ∀ l₁ l₂, count a (l₁ ++ l₂) = count a l₁ + count a l₂ :=
countp_append _

theorem count_concat (a : α) (l : list α) : count a (concat l a) = succ (count a l) :=
by simp [-add_comm]

theorem count_pos {a : α} {l : list α} : 0 < count a l ↔ a ∈ l :=
by simp only [count, countp_pos, exists_prop, exists_eq_right']

@[simp, priority 980]
theorem count_eq_zero_of_not_mem {a : α} {l : list α} (h : a ∉ l) : count a l = 0 :=
by_contradiction $ λ h', h $ count_pos.1 (nat.pos_of_ne_zero h')

theorem not_mem_of_count_eq_zero {a : α} {l : list α} (h : count a l = 0) : a ∉ l :=
λ h', ne_of_gt (count_pos.2 h') h

@[simp] theorem count_repeat (a : α) (n : ℕ) : count a (repeat a n) = n :=
by rw [count, countp_eq_length_filter, filter_eq_self.2, length_repeat];
   exact λ b m, (eq_of_mem_repeat m).symm

theorem le_count_iff_repeat_sublist {a : α} {l : list α} {n : ℕ} :
  n ≤ count a l ↔ repeat a n <+ l :=
⟨λ h, ((repeat_sublist_repeat a).2 h).trans $
  have filter (eq a) l = repeat a (count a l), from eq_repeat.2
    ⟨by simp only [count, countp_eq_length_filter], λ b m, (of_mem_filter m).symm⟩,
  by rw ← this; apply filter_sublist,
 λ h, by simpa only [count_repeat] using count_le_of_sublist a h⟩

theorem repeat_count_eq_of_count_eq_length  {a : α} {l : list α} (h : count a l = length l)  :
  repeat a (count a l) = l :=
eq_of_sublist_of_length_eq (le_count_iff_repeat_sublist.mp (le_refl (count a l)))
    (eq.trans (length_repeat a (count a l)) h)

@[simp] theorem count_filter {p} [decidable_pred p]
  {a} {l : list α} (h : p a) : count a (filter p l) = count a l :=
by simp only [count, countp_filter]; congr; exact
set.ext (λ b, and_iff_left_of_imp (λ e, e ▸ h))

end count

/-! ### prefix, suffix, infix -/

@[simp] theorem prefix_append (l₁ l₂ : list α) : l₁ <+: l₁ ++ l₂ := ⟨l₂, rfl⟩

@[simp] theorem suffix_append (l₁ l₂ : list α) : l₂ <:+ l₁ ++ l₂ := ⟨l₁, rfl⟩

theorem infix_append (l₁ l₂ l₃ : list α) : l₂ <:+: l₁ ++ l₂ ++ l₃ := ⟨l₁, l₃, rfl⟩

@[simp] theorem infix_append' (l₁ l₂ l₃ : list α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) :=
by rw ← list.append_assoc; apply infix_append

theorem nil_prefix (l : list α) : [] <+: l := ⟨l, rfl⟩

theorem nil_suffix (l : list α) : [] <:+ l := ⟨l, append_nil _⟩

@[refl] theorem prefix_refl (l : list α) : l <+: l := ⟨[], append_nil _⟩

@[refl] theorem suffix_refl (l : list α) : l <:+ l := ⟨[], rfl⟩

@[simp] theorem suffix_cons (a : α) : ∀ l, l <:+ a :: l := suffix_append [a]

theorem prefix_concat (a : α) (l) : l <+: concat l a := by simp

theorem infix_of_prefix {l₁ l₂ : list α} : l₁ <+: l₂ → l₁ <:+: l₂ :=
λ⟨t, h⟩, ⟨[], t, h⟩

theorem infix_of_suffix {l₁ l₂ : list α} : l₁ <:+ l₂ → l₁ <:+: l₂ :=
λ⟨t, h⟩, ⟨t, [], by simp only [h, append_nil]⟩

@[refl] theorem infix_refl (l : list α) : l <:+: l := infix_of_prefix $ prefix_refl l

theorem nil_infix (l : list α) : [] <:+: l := infix_of_prefix $ nil_prefix l

theorem infix_cons {L₁ L₂ : list α} {x : α} : L₁ <:+: L₂ → L₁ <:+: x :: L₂ :=
λ⟨LP, LS, H⟩, ⟨x :: LP, LS, H ▸ rfl⟩

@[trans] theorem is_prefix.trans : ∀ {l₁ l₂ l₃ : list α}, l₁ <+: l₂ → l₂ <+: l₃ → l₁ <+: l₃
| l ._ ._ ⟨r₁, rfl⟩ ⟨r₂, rfl⟩ := ⟨r₁ ++ r₂, (append_assoc _ _ _).symm⟩

@[trans] theorem is_suffix.trans : ∀ {l₁ l₂ l₃ : list α}, l₁ <:+ l₂ → l₂ <:+ l₃ → l₁ <:+ l₃
| l ._ ._ ⟨l₁, rfl⟩ ⟨l₂, rfl⟩ := ⟨l₂ ++ l₁, append_assoc _ _ _⟩

@[trans] theorem is_infix.trans : ∀ {l₁ l₂ l₃ : list α}, l₁ <:+: l₂ → l₂ <:+: l₃ → l₁ <:+: l₃
| l ._ ._ ⟨l₁, r₁, rfl⟩ ⟨l₂, r₂, rfl⟩ := ⟨l₂ ++ l₁, r₁ ++ r₂, by simp only [append_assoc]⟩

theorem sublist_of_infix {l₁ l₂ : list α} : l₁ <:+: l₂ → l₁ <+ l₂ :=
λ⟨s, t, h⟩, by rw [← h]; exact (sublist_append_right _ _).trans (sublist_append_left _ _)

theorem sublist_of_prefix {l₁ l₂ : list α} : l₁ <+: l₂ → l₁ <+ l₂ :=
sublist_of_infix ∘ infix_of_prefix

theorem sublist_of_suffix {l₁ l₂ : list α} : l₁ <:+ l₂ → l₁ <+ l₂ :=
sublist_of_infix ∘ infix_of_suffix

theorem reverse_suffix {l₁ l₂ : list α} : reverse l₁ <:+ reverse l₂ ↔ l₁ <+: l₂ :=
⟨λ ⟨r, e⟩, ⟨reverse r,
  by rw [← reverse_reverse l₁, ← reverse_append, e, reverse_reverse]⟩,
 λ ⟨r, e⟩, ⟨reverse r, by rw [← reverse_append, e]⟩⟩

theorem reverse_prefix {l₁ l₂ : list α} : reverse l₁ <+: reverse l₂ ↔ l₁ <:+ l₂ :=
by rw ← reverse_suffix; simp only [reverse_reverse]

theorem length_le_of_infix {l₁ l₂ : list α} (s : l₁ <:+: l₂) : length l₁ ≤ length l₂ :=
length_le_of_sublist $ sublist_of_infix s

theorem eq_nil_of_infix_nil {l : list α} (s : l <:+: []) : l = [] :=
eq_nil_of_sublist_nil $ sublist_of_infix s

@[simp] theorem eq_nil_iff_infix_nil {l : list α} : l <:+: [] ↔ l = [] :=
⟨eq_nil_of_infix_nil, λ h, h ▸ infix_refl _⟩

theorem eq_nil_of_prefix_nil {l : list α} (s : l <+: []) : l = [] :=
eq_nil_of_infix_nil $ infix_of_prefix s

@[simp] theorem eq_nil_iff_prefix_nil {l : list α} : l <+: [] ↔ l = [] :=
⟨eq_nil_of_prefix_nil, λ h, h ▸ prefix_refl _⟩

theorem eq_nil_of_suffix_nil {l : list α} (s : l <:+ []) : l = [] :=
eq_nil_of_infix_nil $ infix_of_suffix s

@[simp] theorem eq_nil_iff_suffix_nil {l : list α} : l <:+ [] ↔ l = [] :=
⟨eq_nil_of_suffix_nil, λ h, h ▸ suffix_refl _⟩

theorem infix_iff_prefix_suffix (l₁ l₂ : list α) : l₁ <:+: l₂ ↔ ∃ t, l₁ <+: t ∧ t <:+ l₂ :=
⟨λ⟨s, t, e⟩, ⟨l₁ ++ t, ⟨_, rfl⟩, by rw [← e, append_assoc]; exact ⟨_, rfl⟩⟩,
λ⟨._, ⟨t, rfl⟩, ⟨s, e⟩⟩, ⟨s, t, by rw append_assoc; exact e⟩⟩

theorem eq_of_infix_of_length_eq {l₁ l₂ : list α} (s : l₁ <:+: l₂) :
  length l₁ = length l₂ → l₁ = l₂ :=
eq_of_sublist_of_length_eq $ sublist_of_infix s

theorem eq_of_prefix_of_length_eq {l₁ l₂ : list α} (s : l₁ <+: l₂) :
  length l₁ = length l₂ → l₁ = l₂ :=
eq_of_sublist_of_length_eq $ sublist_of_prefix s

theorem eq_of_suffix_of_length_eq {l₁ l₂ : list α} (s : l₁ <:+ l₂) :
  length l₁ = length l₂ → l₁ = l₂ :=
eq_of_sublist_of_length_eq $ sublist_of_suffix s

theorem prefix_of_prefix_length_le : ∀ {l₁ l₂ l₃ : list α},
 l₁ <+: l₃ → l₂ <+: l₃ → length l₁ ≤ length l₂ → l₁ <+: l₂
| []      l₂ l₃ h₁ h₂ _ := nil_prefix _
| (a::l₁) (b::l₂) _ ⟨r₁, rfl⟩ ⟨r₂, e⟩ ll := begin
  injection e with _ e', subst b,
  rcases prefix_of_prefix_length_le ⟨_, rfl⟩ ⟨_, e'⟩
    (le_of_succ_le_succ ll) with ⟨r₃, rfl⟩,
  exact ⟨r₃, rfl⟩
end

theorem prefix_or_prefix_of_prefix {l₁ l₂ l₃ : list α}
 (h₁ : l₁ <+: l₃) (h₂ : l₂ <+: l₃) : l₁ <+: l₂ ∨ l₂ <+: l₁ :=
(le_total (length l₁) (length l₂)).imp
  (prefix_of_prefix_length_le h₁ h₂)
  (prefix_of_prefix_length_le h₂ h₁)

theorem suffix_of_suffix_length_le {l₁ l₂ l₃ : list α}
 (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) (ll : length l₁ ≤ length l₂) : l₁ <:+ l₂ :=
reverse_prefix.1 $ prefix_of_prefix_length_le
  (reverse_prefix.2 h₁) (reverse_prefix.2 h₂) (by simp [ll])

theorem suffix_or_suffix_of_suffix {l₁ l₂ l₃ : list α}
 (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) : l₁ <:+ l₂ ∨ l₂ <:+ l₁ :=
(prefix_or_prefix_of_prefix (reverse_prefix.2 h₁) (reverse_prefix.2 h₂)).imp
  reverse_prefix.1 reverse_prefix.1

theorem infix_of_mem_join : ∀ {L : list (list α)} {l}, l ∈ L → l <:+: join L
| (_  :: L) l (or.inl rfl) := infix_append [] _ _
| (l' :: L) l (or.inr h)   :=
  is_infix.trans (infix_of_mem_join h) $ infix_of_suffix $ suffix_append _ _

theorem prefix_append_right_inj {l₁ l₂ : list α} (l) : l ++ l₁ <+: l ++ l₂ ↔ l₁ <+: l₂ :=
exists_congr $ λ r, by rw [append_assoc, append_right_inj]

theorem prefix_cons_inj {l₁ l₂ : list α} (a) : a :: l₁ <+: a :: l₂ ↔ l₁ <+: l₂ :=
prefix_append_right_inj [a]

theorem take_prefix (n) (l : list α) : take n l <+: l := ⟨_, take_append_drop _ _⟩

theorem drop_suffix (n) (l : list α) : drop n l <:+ l := ⟨_, take_append_drop _ _⟩

theorem tail_suffix (l : list α) : tail l <:+ l := by rw ← drop_one; apply drop_suffix

theorem tail_subset (l : list α) : tail l ⊆ l := (sublist_of_suffix (tail_suffix l)).subset

theorem prefix_iff_eq_append {l₁ l₂ : list α} : l₁ <+: l₂ ↔ l₁ ++ drop (length l₁) l₂ = l₂ :=
⟨by rintros ⟨r, rfl⟩; rw drop_left, λ e, ⟨_, e⟩⟩

theorem suffix_iff_eq_append {l₁ l₂ : list α} :
  l₁ <:+ l₂ ↔ take (length l₂ - length l₁) l₂ ++ l₁ = l₂ :=
⟨by rintros ⟨r, rfl⟩; simp only [length_append, nat.add_sub_cancel, take_left], λ e, ⟨_, e⟩⟩

theorem prefix_iff_eq_take {l₁ l₂ : list α} : l₁ <+: l₂ ↔ l₁ = take (length l₁) l₂ :=
⟨λ h, append_right_cancel $
  (prefix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
 λ e, e.symm ▸ take_prefix _ _⟩

theorem suffix_iff_eq_drop {l₁ l₂ : list α} : l₁ <:+ l₂ ↔ l₁ = drop (length l₂ - length l₁) l₂ :=
⟨λ h, append_left_cancel $
  (suffix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
 λ e, e.symm ▸ drop_suffix _ _⟩

instance decidable_prefix [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <+: l₂)
| []      l₂ := is_true ⟨l₂, rfl⟩
| (a::l₁) [] := is_false $ λ ⟨t, te⟩, list.no_confusion te
| (a::l₁) (b::l₂) :=
  if h : a = b then
    @decidable_of_iff _ _ (by rw [← h, prefix_cons_inj])
      (decidable_prefix l₁ l₂)
  else
    is_false $ λ ⟨t, te⟩, h $ by injection te

-- Alternatively, use mem_tails
instance decidable_suffix [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <:+ l₂)
| []      l₂ := is_true ⟨l₂, append_nil _⟩
| (a::l₁) [] := is_false $ mt (length_le_of_sublist ∘ sublist_of_suffix) dec_trivial
| l₁      l₂ := let len1 := length l₁, len2 := length l₂ in
  if hl : len1 ≤ len2 then
    decidable_of_iff' (l₁ = drop (len2-len1) l₂) suffix_iff_eq_drop
  else is_false $ λ h, hl $ length_le_of_sublist $ sublist_of_suffix h

lemma prefix_take_le_iff {L : list (list (option α))} {m n : ℕ} (hm : m < L.length) :
  (take m L) <+: (take n L) ↔ m ≤ n :=
begin
  simp only [prefix_iff_eq_take, length_take],
  induction m with m IH generalizing L n,
  { simp only [min_eq_left, eq_self_iff_true, nat.zero_le, take] },
  { cases n,
    { simp only [nat.nat_zero_eq_zero, nonpos_iff_eq_zero, take, take_nil],
      split,
      { cases L,
        { exact absurd hm (not_lt_of_le m.succ.zero_le) },
        { simp only [forall_prop_of_false, not_false_iff, take] } },
      { intro h,
        contradiction } },
    { cases L with l ls,
      { exact absurd hm (not_lt_of_le m.succ.zero_le) },
      { simp only [length] at hm,
        specialize @IH ls n (nat.lt_of_succ_lt_succ hm),
        simp only [le_of_lt (nat.lt_of_succ_lt_succ hm), min_eq_left] at IH,
        simp only [le_of_lt hm, IH, true_and, min_eq_left, eq_self_iff_true, length, take],
        exact ⟨nat.succ_le_succ, nat.le_of_succ_le_succ⟩ } } },
end

lemma cons_prefix_iff {l l' : list α} {x y : α} :
  x :: l <+: y :: l' ↔ x = y ∧ l <+: l' :=
begin
  split,
  { rintro ⟨L, hL⟩,
    simp only [cons_append] at hL,
    exact ⟨hL.left, ⟨L, hL.right⟩⟩ },
  { rintro ⟨rfl, h⟩,
    rwa [prefix_cons_inj] },
end

lemma map_prefix {l l' : list α} (f : α → β) (h : l <+: l') :
  l.map f <+: l'.map f :=
begin
  induction l with hd tl hl generalizing l',
  { simp only [nil_prefix, map_nil] },
  { cases l' with hd' tl',
    { simpa only using eq_nil_of_prefix_nil h },
    { rw cons_prefix_iff at h,
      simp only [h, prefix_cons_inj, hl, map] } },
end

lemma is_prefix.filter_map {l l' : list α} (h : l <+: l') (f : α → option β) :
  l.filter_map f <+: l'.filter_map f :=
begin
  induction l with hd tl hl generalizing l',
  { simp only [nil_prefix, filter_map_nil] },
  { cases l' with hd' tl',
    { simpa only using eq_nil_of_prefix_nil h },
    { rw cons_prefix_iff at h,
      rw [←@singleton_append _ hd _, ←@singleton_append _ hd' _, filter_map_append,
         filter_map_append, h.left, prefix_append_right_inj],
      exact hl h.right } },
end

lemma is_prefix.reduce_option {l l' : list (option α)} (h : l <+: l') :
  l.reduce_option <+: l'.reduce_option :=
h.filter_map id

@[simp] theorem mem_inits : ∀ (s t : list α), s ∈ inits t ↔ s <+: t
| s []     := suffices s = nil ↔ s <+: nil, by simpa only [inits, mem_singleton],
  ⟨λh, h.symm ▸ prefix_refl [], eq_nil_of_prefix_nil⟩
| s (a::t) :=
  suffices (s = nil ∨ ∃ l ∈ inits t, a :: l = s) ↔ s <+: a :: t, by simpa,
  ⟨λo, match s, o with
  | ._, or.inl rfl := ⟨_, rfl⟩
  | s, or.inr ⟨r, hr, hs⟩ := let ⟨s, ht⟩ := (mem_inits _ _).1 hr in
    by rw [← hs, ← ht]; exact ⟨s, rfl⟩
  end, λmi, match s, mi with
  | [], ⟨._, rfl⟩ := or.inl rfl
  | (b::s), ⟨r, hr⟩ := list.no_confusion hr $ λba (st : s++r = t), or.inr $
    by rw ba; exact ⟨_, (mem_inits _ _).2 ⟨_, st⟩, rfl⟩
  end⟩

@[simp] theorem mem_tails : ∀ (s t : list α), s ∈ tails t ↔ s <:+ t
| s []     := by simp only [tails, mem_singleton];
  exact ⟨λh, by rw h; exact suffix_refl [], eq_nil_of_suffix_nil⟩
| s (a::t) := by simp only [tails, mem_cons_iff, mem_tails s t];
  exact show s = a :: t ∨ s <:+ t ↔ s <:+ a :: t, from
  ⟨λo, match s, t, o with
  | ._, t, or.inl rfl := suffix_refl _
  | s, ._, or.inr ⟨l, rfl⟩ := ⟨a::l, rfl⟩
  end, λe, match s, t, e with
  | ._, t, ⟨[], rfl⟩ := or.inl rfl
  | s, t, ⟨b::l, he⟩ := list.no_confusion he (λab lt, or.inr ⟨l, lt⟩)
  end⟩

lemma inits_cons (a : α) (l : list α) : inits (a :: l) = [] :: l.inits.map (λ t, a :: t) :=
by simp

lemma tails_cons (a : α) (l : list α) : tails (a :: l) = (a :: l) :: l.tails :=
by simp

@[simp]
lemma inits_append : ∀ (s t : list α), inits (s ++ t) = s.inits ++ t.inits.tail.map (λ l, s ++ l)
| [] [] := by simp
| [] (a::t) := by simp
| (a::s) t := by simp [inits_append s t]

@[simp]
lemma tails_append : ∀ (s t : list α), tails (s ++ t) = s.tails.map (λ l, l ++ t) ++ t.tails.tail
| [] [] := by simp
| [] (a::t) := by simp
| (a::s) t := by simp [tails_append s t]

-- the lemma names `inits_eq_tails` and `tails_eq_inits` are like `sublists_eq_sublists'`
lemma inits_eq_tails :
  ∀ (l : list α), l.inits = (reverse $ map reverse $ tails $ reverse l)
| [] := by simp
| (a :: l) := by simp [inits_eq_tails l, map_eq_map_iff]

lemma tails_eq_inits :
  ∀ (l : list α), l.tails = (reverse $ map reverse $ inits $ reverse l)
| [] := by simp
| (a :: l) := by simp [tails_eq_inits l, append_left_inj]

lemma inits_reverse (l : list α) : inits (reverse l) = reverse (map reverse l.tails) :=
by { rw tails_eq_inits l, simp [reverse_involutive.comp_self], }

lemma tails_reverse (l : list α) : tails (reverse l) = reverse (map reverse l.inits) :=
by { rw inits_eq_tails l, simp [reverse_involutive.comp_self], }

lemma map_reverse_inits (l : list α) : map reverse l.inits = (reverse $ tails $ reverse l) :=
by { rw inits_eq_tails l, simp [reverse_involutive.comp_self], }

lemma map_reverse_tails (l : list α) : map reverse l.tails = (reverse $ inits $ reverse l) :=
by { rw tails_eq_inits l, simp [reverse_involutive.comp_self], }

instance decidable_infix [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <:+: l₂)
| []      l₂ := is_true ⟨[], l₂, rfl⟩
| (a::l₁) [] := is_false $ λ⟨s, t, te⟩, absurd te $ append_ne_nil_of_ne_nil_left _ _ $
                append_ne_nil_of_ne_nil_right _ _ $ λh, list.no_confusion h
| l₁      l₂ := decidable_of_decidable_of_iff (list.decidable_bex (λt, l₁ <+: t) (tails l₂)) $
  by refine (exists_congr (λt, _)).trans (infix_iff_prefix_suffix _ _).symm;
     exact ⟨λ⟨h1, h2⟩, ⟨h2, (mem_tails _ _).1 h1⟩, λ⟨h2, h1⟩, ⟨(mem_tails _ _).2 h1, h2⟩⟩

/-! ### sublists -/

@[simp] theorem sublists'_nil : sublists' (@nil α) = [[]] := rfl

@[simp, priority 1100] theorem sublists'_singleton (a : α) : sublists' [a] = [[], [a]] := rfl

theorem map_sublists'_aux (g : list β → list γ) (l : list α) (f r) :
  map g (sublists'_aux l f r) = sublists'_aux l (g ∘ f) (map g r) :=
by induction l generalizing f r; [refl, simp only [*, sublists'_aux]]

theorem sublists'_aux_append (r' : list (list β)) (l : list α) (f r) :
  sublists'_aux l f (r ++ r') = sublists'_aux l f r ++ r' :=
by induction l generalizing f r; [refl, simp only [*, sublists'_aux]]

theorem sublists'_aux_eq_sublists' (l f r) :
  @sublists'_aux α β l f r = map f (sublists' l) ++ r :=
by rw [sublists', map_sublists'_aux, ← sublists'_aux_append]; refl

@[simp] theorem sublists'_cons (a : α) (l : list α) :
  sublists' (a :: l) = sublists' l ++ map (cons a) (sublists' l) :=
by rw [sublists', sublists'_aux]; simp only [sublists'_aux_eq_sublists', map_id, append_nil]; refl

@[simp] theorem mem_sublists' {s t : list α} : s ∈ sublists' t ↔ s <+ t :=
begin
  induction t with a t IH generalizing s,
  { simp only [sublists'_nil, mem_singleton],
    exact ⟨λ h, by rw h, eq_nil_of_sublist_nil⟩ },
  simp only [sublists'_cons, mem_append, IH, mem_map],
  split; intro h, rcases h with h | ⟨s, h, rfl⟩,
  { exact sublist_cons_of_sublist _ h },
  { exact cons_sublist_cons _ h },
  { cases h with _ _ _ h s _ _ h,
    { exact or.inl h },
    { exact or.inr ⟨s, h, rfl⟩ } }
end

@[simp] theorem length_sublists' : ∀ l : list α, length (sublists' l) = 2 ^ length l
| []     := rfl
| (a::l) := by simp only [sublists'_cons, length_append, length_sublists' l, length_map,
    length, pow_succ', mul_succ, mul_zero, zero_add]

@[simp] theorem sublists_nil : sublists (@nil α) = [[]] := rfl

@[simp] theorem sublists_singleton (a : α) : sublists [a] = [[], [a]] := rfl

theorem sublists_aux₁_eq_sublists_aux : ∀ l (f : list α → list β),
  sublists_aux₁ l f = sublists_aux l (λ ys r, f ys ++ r)
| []     f := rfl
| (a::l) f := by rw [sublists_aux₁, sublists_aux]; simp only [*, append_assoc]

theorem sublists_aux_cons_eq_sublists_aux₁ (l : list α) :
  sublists_aux l cons = sublists_aux₁ l (λ x, [x]) :=
by rw [sublists_aux₁_eq_sublists_aux]; refl

theorem sublists_aux_eq_foldr.aux {a : α} {l : list α}
  (IH₁ : ∀ (f : list α → list β → list β), sublists_aux l f = foldr f [] (sublists_aux l cons))
  (IH₂ : ∀ (f : list α → list (list α) → list (list α)),
      sublists_aux l f = foldr f [] (sublists_aux l cons))
  (f : list α → list β → list β) : sublists_aux (a::l) f = foldr f [] (sublists_aux (a::l) cons) :=
begin
  simp only [sublists_aux, foldr_cons], rw [IH₂, IH₁], congr' 1,
  induction sublists_aux l cons with _ _ ih, {refl},
  simp only [ih, foldr_cons]
end

theorem sublists_aux_eq_foldr (l : list α) : ∀ (f : list α → list β → list β),
  sublists_aux l f = foldr f [] (sublists_aux l cons) :=
suffices _ ∧ ∀ f : list α → list (list α) → list (list α),
    sublists_aux l f = foldr f [] (sublists_aux l cons),
  from this.1,
begin
  induction l with a l IH, {split; intro; refl},
  exact ⟨sublists_aux_eq_foldr.aux IH.1 IH.2,
         sublists_aux_eq_foldr.aux IH.2 IH.2⟩
end

theorem sublists_aux_cons_cons (l : list α) (a : α) :
  sublists_aux (a::l) cons = [a] :: foldr (λys r, ys :: (a :: ys) :: r) [] (sublists_aux l cons) :=
by rw [← sublists_aux_eq_foldr]; refl

theorem sublists_aux₁_append : ∀ (l₁ l₂ : list α) (f : list α → list β),
  sublists_aux₁ (l₁ ++ l₂) f = sublists_aux₁ l₁ f ++
    sublists_aux₁ l₂ (λ x, f x ++ sublists_aux₁ l₁ (f ∘ (++ x)))
| []      l₂ f := by simp only [sublists_aux₁, nil_append, append_nil]
| (a::l₁) l₂ f := by simp only [sublists_aux₁, cons_append, sublists_aux₁_append l₁, append_assoc];
  refl

theorem sublists_aux₁_concat (l : list α) (a : α) (f : list α → list β) :
  sublists_aux₁ (l ++ [a]) f = sublists_aux₁ l f ++
    f [a] ++ sublists_aux₁ l (λ x, f (x ++ [a])) :=
by simp only [sublists_aux₁_append, sublists_aux₁, append_assoc, append_nil]

theorem sublists_aux₁_bind : ∀ (l : list α)
  (f : list α → list β) (g : β → list γ),
  (sublists_aux₁ l f).bind g = sublists_aux₁ l (λ x, (f x).bind g)
| []     f g := rfl
| (a::l) f g := by simp only [sublists_aux₁, bind_append, sublists_aux₁_bind l]

theorem sublists_aux_cons_append (l₁ l₂ : list α) :
  sublists_aux (l₁ ++ l₂) cons = sublists_aux l₁ cons ++
    (do x ← sublists_aux l₂ cons, (++ x) <$> sublists l₁) :=
begin
  simp only [sublists, sublists_aux_cons_eq_sublists_aux₁, sublists_aux₁_append, bind_eq_bind,
    sublists_aux₁_bind],
  congr, funext x, apply congr_arg _,
  rw [← bind_ret_eq_map, sublists_aux₁_bind], exact (append_nil _).symm
end

theorem sublists_append (l₁ l₂ : list α) :
  sublists (l₁ ++ l₂) = (do x ← sublists l₂, (++ x) <$> sublists l₁) :=
by simp only [map, sublists, sublists_aux_cons_append, map_eq_map, bind_eq_bind,
  cons_bind, map_id', append_nil, cons_append, map_id' (λ _, rfl)]; split; refl

@[simp] theorem sublists_concat (l : list α) (a : α) :
  sublists (l ++ [a]) = sublists l ++ map (λ x, x ++ [a]) (sublists l) :=
by rw [sublists_append, sublists_singleton, bind_eq_bind, cons_bind, cons_bind, nil_bind,
  map_eq_map, map_eq_map, map_id' (append_nil), append_nil]

theorem sublists_reverse (l : list α) : sublists (reverse l) = map reverse (sublists' l) :=
by induction l with hd tl ih; [refl,
simp only [reverse_cons, sublists_append, sublists'_cons, map_append, ih, sublists_singleton,
  map_eq_map, bind_eq_bind, map_map, cons_bind, append_nil, nil_bind, (∘)]]

theorem sublists_eq_sublists' (l : list α) : sublists l = map reverse (sublists' (reverse l)) :=
by rw [← sublists_reverse, reverse_reverse]

theorem sublists'_reverse (l : list α) : sublists' (reverse l) = map reverse (sublists l) :=
by simp only [sublists_eq_sublists', map_map, map_id' (reverse_reverse)]

theorem sublists'_eq_sublists (l : list α) : sublists' l = map reverse (sublists (reverse l)) :=
by rw [← sublists'_reverse, reverse_reverse]

theorem sublists_aux_ne_nil : ∀ (l : list α), [] ∉ sublists_aux l cons
| [] := id
| (a::l) := begin
  rw [sublists_aux_cons_cons],
  refine not_mem_cons_of_ne_of_not_mem (cons_ne_nil _ _).symm _,
  have := sublists_aux_ne_nil l, revert this,
  induction sublists_aux l cons; intro, {rwa foldr},
  simp only [foldr, mem_cons_iff, false_or, not_or_distrib],
  exact ⟨ne_of_not_mem_cons this, ih (not_mem_of_not_mem_cons this)⟩
end

@[simp] theorem mem_sublists {s t : list α} : s ∈ sublists t ↔ s <+ t :=
by rw [← reverse_sublist_iff, ← mem_sublists',
       sublists'_reverse, mem_map_of_injective reverse_injective]

@[simp] theorem length_sublists (l : list α) : length (sublists l) = 2 ^ length l :=
by simp only [sublists_eq_sublists', length_map, length_sublists', length_reverse]

theorem map_ret_sublist_sublists (l : list α) : map list.ret l <+ sublists l :=
reverse_rec_on l (nil_sublist _) $
λ l a IH, by simp only [map, map_append, sublists_concat]; exact
((append_sublist_append_left _).2 $ singleton_sublist.2 $
  mem_map.2 ⟨[], mem_sublists.2 (nil_sublist _), by refl⟩).trans
((append_sublist_append_right _).2 IH)

/-! ### sublists_len -/

/-- Auxiliary function to construct the list of all sublists of a given length. Given an
integer `n`, a list `l`, a function `f` and an auxiliary list `L`, it returns the list made of
of `f` applied to all sublists of `l` of length `n`, concatenated with `L`. -/
def sublists_len_aux {α β : Type*} : ℕ → list α → (list α → β) → list β → list β
| 0     l      f r := f [] :: r
| (n+1) []     f r := r
| (n+1) (a::l) f r := sublists_len_aux (n + 1) l f
  (sublists_len_aux n l (f ∘ list.cons a) r)

/-- The list of all sublists of a list `l` that are of length `n`. For instance, for
`l = [0, 1, 2, 3]` and `n = 2`, one gets
`[[2, 3], [1, 3], [1, 2], [0, 3], [0, 2], [0, 1]]`. -/
def sublists_len {α : Type*} (n : ℕ) (l : list α) : list (list α) :=
sublists_len_aux n l id []

lemma sublists_len_aux_append {α β γ : Type*} :
  ∀ (n : ℕ) (l : list α) (f : list α → β) (g : β → γ) (r : list β) (s : list γ),
  sublists_len_aux n l (g ∘ f) (r.map g ++ s) =
  (sublists_len_aux n l f r).map g ++ s
| 0     l      f g r s := rfl
| (n+1) []     f g r s := rfl
| (n+1) (a::l) f g r s := begin
  unfold sublists_len_aux,
  rw [show ((g ∘ f) ∘ list.cons a) = (g ∘ f ∘ list.cons a), by refl,
    sublists_len_aux_append, sublists_len_aux_append]
end

lemma sublists_len_aux_eq {α β : Type*} (l : list α) (n) (f : list α → β) (r) :
  sublists_len_aux n l f r = (sublists_len n l).map f ++ r :=
by rw [sublists_len, ← sublists_len_aux_append]; refl

lemma sublists_len_aux_zero {α : Type*} (l : list α) (f : list α → β) (r) :
  sublists_len_aux 0 l f r = f [] :: r := by cases l; refl

@[simp] lemma sublists_len_zero {α : Type*} (l : list α) :
  sublists_len 0 l = [[]] := sublists_len_aux_zero _ _ _

@[simp] lemma sublists_len_succ_nil {α : Type*} (n) :
  sublists_len (n+1) (@nil α) = [] := rfl

@[simp] lemma sublists_len_succ_cons {α : Type*} (n) (a : α) (l) :
  sublists_len (n + 1) (a::l) =
  sublists_len (n + 1) l ++ (sublists_len n l).map (cons a) :=
by rw [sublists_len, sublists_len_aux, sublists_len_aux_eq,
  sublists_len_aux_eq, map_id, append_nil]; refl

@[simp] lemma length_sublists_len {α : Type*} : ∀ n (l : list α),
  length (sublists_len n l) = nat.choose (length l) n
| 0     l      := by simp
| (n+1) []     := by simp
| (n+1) (a::l) := by simp [-add_comm, nat.choose, *]; apply add_comm

lemma sublists_len_sublist_sublists' {α : Type*} : ∀ n (l : list α),
  sublists_len n l <+ sublists' l
| 0     l      := singleton_sublist.2 (mem_sublists'.2 (nil_sublist _))
| (n+1) []     := nil_sublist _
| (n+1) (a::l) := begin
  rw [sublists_len_succ_cons, sublists'_cons],
  exact (sublists_len_sublist_sublists' _ _).append
    ((sublists_len_sublist_sublists' _ _).map _)
end

lemma sublists_len_sublist_of_sublist
  {α : Type*} (n) {l₁ l₂ : list α} (h : l₁ <+ l₂) : sublists_len n l₁ <+ sublists_len n l₂ :=
begin
  induction n with n IHn generalizing l₁ l₂, {simp},
  induction h with l₁ l₂ a s IH l₁ l₂ a s IH, {refl},
  { refine IH.trans _,
    rw sublists_len_succ_cons,
    apply sublist_append_left },
  { simp [sublists_len_succ_cons],
    exact IH.append ((IHn s).map _) }
end

lemma length_of_sublists_len {α : Type*} : ∀ {n} {l l' : list α},
  l' ∈ sublists_len n l → length l' = n
| 0     l      l' (or.inl rfl) := rfl
| (n+1) (a::l) l' h := begin
  rw [sublists_len_succ_cons, mem_append, mem_map] at h,
  rcases h with h | ⟨l', h, rfl⟩,
  { exact length_of_sublists_len h },
  { exact congr_arg (+1) (length_of_sublists_len h) },
end

lemma mem_sublists_len_self {α : Type*} {l l' : list α}
  (h : l' <+ l) : l' ∈ sublists_len (length l') l :=
begin
  induction h with l₁ l₂ a s IH l₁ l₂ a s IH,
  { exact or.inl rfl },
  { cases l₁ with b l₁,
    { exact or.inl rfl },
    { rw [length, sublists_len_succ_cons],
      exact mem_append_left _ IH } },
  { rw [length, sublists_len_succ_cons],
    exact mem_append_right _ (mem_map.2 ⟨_, IH, rfl⟩) }
end

@[simp] lemma mem_sublists_len {α : Type*} {n} {l l' : list α} :
  l' ∈ sublists_len n l ↔ l' <+ l ∧ length l' = n :=
⟨λ h, ⟨mem_sublists'.1
    ((sublists_len_sublist_sublists' _ _).subset h),
  length_of_sublists_len h⟩,
λ ⟨h₁, h₂⟩, h₂ ▸ mem_sublists_len_self h₁⟩

/-! ### permutations -/

section permutations

@[simp] theorem permutations_aux_nil (is : list α) : permutations_aux [] is = [] :=
by rw [permutations_aux, permutations_aux.rec]

@[simp] theorem permutations_aux_cons (t : α) (ts is : list α) :
  permutations_aux (t :: ts) is = foldr (λy r, (permutations_aux2 t ts r y id).2)
    (permutations_aux ts (t::is)) (permutations is) :=
by rw [permutations_aux, permutations_aux.rec]; refl

end permutations

/-! ### insert -/
section insert
variable [decidable_eq α]

@[simp] theorem insert_nil (a : α) : insert a nil = [a] := rfl

theorem insert.def (a : α) (l : list α) : insert a l = if a ∈ l then l else a :: l := rfl

@[simp, priority 980]
theorem insert_of_mem {a : α} {l : list α} (h : a ∈ l) : insert a l = l :=
by simp only [insert.def, if_pos h]

@[simp, priority 970]
theorem insert_of_not_mem {a : α} {l : list α} (h : a ∉ l) : insert a l = a :: l :=
by simp only [insert.def, if_neg h]; split; refl

@[simp] theorem mem_insert_iff {a b : α} {l : list α} : a ∈ insert b l ↔ a = b ∨ a ∈ l :=
begin
  by_cases h' : b ∈ l,
  { simp only [insert_of_mem h'],
    apply (or_iff_right_of_imp _).symm,
    exact λ e, e.symm ▸ h' },
  simp only [insert_of_not_mem h', mem_cons_iff]
end

@[simp] theorem suffix_insert (a : α) (l : list α) : l <:+ insert a l :=
by by_cases a ∈ l; [simp only [insert_of_mem h], simp only [insert_of_not_mem h, suffix_cons]]

@[simp] theorem mem_insert_self (a : α) (l : list α) : a ∈ insert a l :=
mem_insert_iff.2 (or.inl rfl)

theorem mem_insert_of_mem {a b : α} {l : list α} (h : a ∈ l) : a ∈ insert b l :=
mem_insert_iff.2 (or.inr h)

theorem eq_or_mem_of_mem_insert {a b : α} {l : list α} (h : a ∈ insert b l) : a = b ∨ a ∈ l :=
mem_insert_iff.1 h

@[simp] theorem length_insert_of_mem {a : α} {l : list α} (h : a ∈ l) :
  length (insert a l) = length l :=
by rw insert_of_mem h

@[simp] theorem length_insert_of_not_mem {a : α} {l : list α} (h : a ∉ l) :
  length (insert a l) = length l + 1 :=
by rw insert_of_not_mem h; refl

end insert

/-! ### erasep -/
section erasep
variables {p : α → Prop} [decidable_pred p]

@[simp] theorem erasep_nil : [].erasep p = [] := rfl

theorem erasep_cons (a : α) (l : list α) :
  (a :: l).erasep p = if p a then l else a :: l.erasep p := rfl

@[simp] theorem erasep_cons_of_pos {a : α} {l : list α} (h : p a) : (a :: l).erasep p = l :=
by simp [erasep_cons, h]

@[simp] theorem erasep_cons_of_neg {a : α} {l : list α} (h : ¬ p a) :
  (a::l).erasep p = a :: l.erasep p :=
by simp [erasep_cons, h]

theorem erasep_of_forall_not {l : list α}
  (h : ∀ a ∈ l, ¬ p a) : l.erasep p = l :=
by induction l with _ _ ih; [refl,
  simp [h _ (or.inl rfl), ih (forall_mem_of_forall_mem_cons h)]]

theorem exists_of_erasep {l : list α} {a} (al : a ∈ l) (pa : p a) :
  ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ :=
begin
  induction l with b l IH, {cases al},
  by_cases pb : p b,
  { exact ⟨b, [], l, forall_mem_nil _, pb, by simp [pb]⟩ },
  { rcases al with rfl | al, {exact pb.elim pa},
    rcases IH al with ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩,
    exact ⟨c, b::l₁, l₂, forall_mem_cons.2 ⟨pb, h₁⟩,
      h₂, by rw h₃; refl, by simp [pb, h₄]⟩ }
end

theorem exists_or_eq_self_of_erasep (p : α → Prop) [decidable_pred p] (l : list α) :
  l.erasep p = l ∨ ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ :=
begin
  by_cases h : ∃ a ∈ l, p a,
  { rcases h with ⟨a, ha, pa⟩,
    exact or.inr (exists_of_erasep ha pa) },
  { simp at h, exact or.inl (erasep_of_forall_not h) }
end

@[simp] theorem length_erasep_of_mem {l : list α} {a} (al : a ∈ l) (pa : p a) :
 length (l.erasep p) = pred (length l) :=
by rcases exists_of_erasep al pa with ⟨_, l₁, l₂, _, _, e₁, e₂⟩;
   rw e₂; simp [-add_comm, e₁]; refl

theorem erasep_append_left {a : α} (pa : p a) :
  ∀ {l₁ : list α} (l₂), a ∈ l₁ → (l₁++l₂).erasep p = l₁.erasep p ++ l₂
| (x::xs) l₂ h := begin
  by_cases h' : p x; simp [h'],
  rw erasep_append_left l₂ (mem_of_ne_of_mem (mt _ h') h),
  rintro rfl, exact pa
end

theorem erasep_append_right :
  ∀ {l₁ : list α} (l₂), (∀ b ∈ l₁, ¬ p b) → (l₁++l₂).erasep p = l₁ ++ l₂.erasep p
| []      l₂ h := rfl
| (x::xs) l₂ h := by simp [(forall_mem_cons.1 h).1,
  erasep_append_right _ (forall_mem_cons.1 h).2]

theorem erasep_sublist (l : list α) : l.erasep p <+ l :=
by rcases exists_or_eq_self_of_erasep p l with h | ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩;
   [rw h, {rw [h₄, h₃], simp}]

theorem erasep_subset (l : list α) : l.erasep p ⊆ l :=
(erasep_sublist l).subset

theorem sublist.erasep {l₁ l₂ : list α} (s : l₁ <+ l₂) : l₁.erasep p <+ l₂.erasep p :=
begin
  induction s,
  case list.sublist.slnil { refl },
  case list.sublist.cons : l₁ l₂ a s IH {
    by_cases h : p a; simp [h],
    exacts [IH.trans (erasep_sublist _), IH.cons _ _ _] },
  case list.sublist.cons2 : l₁ l₂ a s IH {
    by_cases h : p a; simp [h],
    exacts [s, IH.cons2 _ _ _] }
end

theorem mem_of_mem_erasep {a : α} {l : list α} : a ∈ l.erasep p → a ∈ l :=
@erasep_subset _ _ _ _ _

@[simp] theorem mem_erasep_of_neg {a : α} {l : list α} (pa : ¬ p a) : a ∈ l.erasep p ↔ a ∈ l :=
⟨mem_of_mem_erasep, λ al, begin
  rcases exists_or_eq_self_of_erasep p l with h | ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩,
  { rwa h },
  { rw h₄, rw h₃ at al,
    have : a ≠ c, {rintro rfl, exact pa.elim h₂},
    simpa [this] using al }
end⟩

theorem erasep_map (f : β → α) :
  ∀ (l : list β), (map f l).erasep p = map f (l.erasep (p ∘ f))
| []     := rfl
| (b::l) := by by_cases p (f b); simp [h, erasep_map l]

@[simp] theorem extractp_eq_find_erasep :
  ∀ l : list α, extractp p l = (find p l, erasep p l)
| []     := rfl
| (a::l) := by by_cases pa : p a; simp [extractp, pa, extractp_eq_find_erasep l]

end erasep

/-! ### erase -/
section erase
variable [decidable_eq α]

@[simp] theorem erase_nil (a : α) : [].erase a = [] := rfl

theorem erase_cons (a b : α) (l : list α) :
  (b :: l).erase a = if b = a then l else b :: l.erase a := rfl

@[simp] theorem erase_cons_head (a : α) (l : list α) : (a :: l).erase a = l :=
by simp only [erase_cons, if_pos rfl]

@[simp] theorem erase_cons_tail {a b : α} (l : list α) (h : b ≠ a) :
  (b::l).erase a = b :: l.erase a :=
by simp only [erase_cons, if_neg h]; split; refl

theorem erase_eq_erasep (a : α) (l : list α) : l.erase a = l.erasep (eq a) :=
by { induction l with b l, {refl},
  by_cases a = b; [simp [h], simp [h, ne.symm h, *]] }

@[simp, priority 980]
theorem erase_of_not_mem {a : α} {l : list α} (h : a ∉ l) : l.erase a = l :=
by rw [erase_eq_erasep, erasep_of_forall_not]; rintro b h' rfl; exact h h'

theorem exists_erase_eq {a : α} {l : list α} (h : a ∈ l) :
  ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l.erase a = l₁ ++ l₂ :=
by rcases exists_of_erasep h rfl with ⟨_, l₁, l₂, h₁, rfl, h₂, h₃⟩;
   rw erase_eq_erasep; exact ⟨l₁, l₂, λ h, h₁ _ h rfl, h₂, h₃⟩

@[simp] theorem length_erase_of_mem {a : α} {l : list α} (h : a ∈ l) :
  length (l.erase a) = pred (length l) :=
by rw erase_eq_erasep; exact length_erasep_of_mem h rfl

theorem erase_append_left {a : α} {l₁ : list α} (l₂) (h : a ∈ l₁) :
  (l₁++l₂).erase a = l₁.erase a ++ l₂ :=
by simp [erase_eq_erasep]; exact erasep_append_left (by refl) l₂ h

theorem erase_append_right {a : α} {l₁ : list α} (l₂) (h : a ∉ l₁) :
  (l₁++l₂).erase a = l₁ ++ l₂.erase a :=
by rw [erase_eq_erasep, erase_eq_erasep, erasep_append_right];
   rintro b h' rfl; exact h h'

theorem erase_sublist (a : α) (l : list α) : l.erase a <+ l :=
by rw erase_eq_erasep; apply erasep_sublist

theorem erase_subset (a : α) (l : list α) : l.erase a ⊆ l :=
(erase_sublist a l).subset

theorem sublist.erase (a : α) {l₁ l₂ : list α} (h : l₁ <+ l₂) : l₁.erase a <+ l₂.erase a :=
by simp [erase_eq_erasep]; exact sublist.erasep h

theorem mem_of_mem_erase {a b : α} {l : list α} : a ∈ l.erase b → a ∈ l :=
@erase_subset _ _ _ _ _

@[simp] theorem mem_erase_of_ne {a b : α} {l : list α} (ab : a ≠ b) : a ∈ l.erase b ↔ a ∈ l :=
by rw erase_eq_erasep; exact mem_erasep_of_neg ab.symm

theorem erase_comm (a b : α) (l : list α) : (l.erase a).erase b = (l.erase b).erase a :=
if ab : a = b then by rw ab else
if ha : a ∈ l then
if hb : b ∈ l then match l, l.erase a, exists_erase_eq ha, hb with
| ._, ._, ⟨l₁, l₂, ha', rfl, rfl⟩, hb :=
  if h₁ : b ∈ l₁ then
    by rw [erase_append_left _ h₁, erase_append_left _ h₁,
           erase_append_right _ (mt mem_of_mem_erase ha'), erase_cons_head]
  else
    by rw [erase_append_right _ h₁, erase_append_right _ h₁, erase_append_right _ ha',
           erase_cons_tail _ ab, erase_cons_head]
end
else by simp only [erase_of_not_mem hb, erase_of_not_mem (mt mem_of_mem_erase hb)]
else by simp only [erase_of_not_mem ha, erase_of_not_mem (mt mem_of_mem_erase ha)]

theorem map_erase [decidable_eq β] {f : α → β} (finj : injective f) {a : α}
  (l : list α) : map f (l.erase a) = (map f l).erase (f a) :=
by rw [erase_eq_erasep, erase_eq_erasep, erasep_map]; congr;
   ext b; simp [finj.eq_iff]

theorem map_foldl_erase [decidable_eq β] {f : α → β} (finj : injective f) {l₁ l₂ : list α} :
  map f (foldl list.erase l₁ l₂) = foldl (λ l a, l.erase (f a)) (map f l₁) l₂ :=
by induction l₂ generalizing l₁; [refl,
simp only [foldl_cons, map_erase finj, *]]

@[simp] theorem count_erase_self (a : α) :
  ∀ (s : list α), count a (list.erase s a) = pred (count a s)
| [] := by simp
| (h :: t) :=
begin
  rw erase_cons,
  by_cases p : h = a,
  { rw [if_pos p, count_cons', if_pos p.symm], simp },
  { rw [if_neg p, count_cons', count_cons', if_neg (λ x : a = h, p x.symm), count_erase_self],
    simp, }
end

@[simp] theorem count_erase_of_ne {a b : α} (ab : a ≠ b) :
  ∀ (s : list α), count a (list.erase s b) = count a s
| [] := by simp
| (x :: xs) :=
begin
  rw erase_cons,
  split_ifs with h,
  { rw [count_cons', h, if_neg ab], simp },
  { rw [count_cons', count_cons', count_erase_of_ne] }
end

end erase

/-! ### diff -/
section diff
variable [decidable_eq α]

@[simp] theorem diff_nil (l : list α) : l.diff [] = l := rfl

@[simp] theorem diff_cons (l₁ l₂ : list α) (a : α) : l₁.diff (a::l₂) = (l₁.erase a).diff l₂ :=
if h : a ∈ l₁ then by simp only [list.diff, if_pos h]
else by simp only [list.diff, if_neg h, erase_of_not_mem h]

lemma diff_cons_right (l₁ l₂ : list α) (a : α) : l₁.diff (a::l₂) = (l₁.diff l₂).erase a :=
begin
  induction l₂ with b l₂ ih generalizing l₁ a,
  { simp_rw [diff_cons, diff_nil] },
  { rw [diff_cons, diff_cons, erase_comm, ← diff_cons, ih, ← diff_cons] }
end

lemma diff_erase (l₁ l₂ : list α) (a : α) : (l₁.diff l₂).erase a = (l₁.erase a).diff l₂ :=
by rw [← diff_cons_right, diff_cons]

@[simp] theorem nil_diff (l : list α) : [].diff l = [] :=
by induction l; [refl, simp only [*, diff_cons, erase_of_not_mem (not_mem_nil _)]]

theorem diff_eq_foldl : ∀ (l₁ l₂ : list α), l₁.diff l₂ = foldl list.erase l₁ l₂
| l₁ []      := rfl
| l₁ (a::l₂) := (diff_cons l₁ l₂ a).trans (diff_eq_foldl _ _)

@[simp] theorem diff_append (l₁ l₂ l₃ : list α) : l₁.diff (l₂ ++ l₃) = (l₁.diff l₂).diff l₃ :=
by simp only [diff_eq_foldl, foldl_append]

@[simp] theorem map_diff [decidable_eq β] {f : α → β} (finj : injective f) {l₁ l₂ : list α} :
  map f (l₁.diff l₂) = (map f l₁).diff (map f l₂) :=
by simp only [diff_eq_foldl, foldl_map, map_foldl_erase finj]

theorem diff_sublist : ∀ l₁ l₂ : list α, l₁.diff l₂ <+ l₁
| l₁ []      := sublist.refl _
| l₁ (a::l₂) := calc l₁.diff (a :: l₂) = (l₁.erase a).diff l₂ : diff_cons _ _ _
  ... <+ l₁.erase a : diff_sublist _ _
  ... <+ l₁ : list.erase_sublist _ _

theorem diff_subset (l₁ l₂ : list α) : l₁.diff l₂ ⊆ l₁ :=
(diff_sublist _ _).subset

theorem mem_diff_of_mem {a : α} : ∀ {l₁ l₂ : list α}, a ∈ l₁ → a ∉ l₂ → a ∈ l₁.diff l₂
| l₁ []      h₁ h₂ := h₁
| l₁ (b::l₂) h₁ h₂ := by rw diff_cons; exact
  mem_diff_of_mem ((mem_erase_of_ne (ne_of_not_mem_cons h₂)).2 h₁) (not_mem_of_not_mem_cons h₂)

theorem sublist.diff_right : ∀ {l₁ l₂ l₃: list α}, l₁ <+ l₂ → l₁.diff l₃ <+ l₂.diff l₃
| l₁ l₂ [] h      := h
| l₁ l₂ (a::l₃) h := by simp only
  [diff_cons, (h.erase _).diff_right]

theorem erase_diff_erase_sublist_of_sublist {a : α} : ∀ {l₁ l₂ : list α},
  l₁ <+ l₂ → (l₂.erase a).diff (l₁.erase a) <+ l₂.diff l₁
| []      l₂ h := erase_sublist _ _
| (b::l₁) l₂ h := if heq : b = a then by simp only [heq, erase_cons_head, diff_cons]
                  else by simpa only [erase_cons_head, erase_cons_tail _ heq, diff_cons,
                    erase_comm a b l₂]
                  using erase_diff_erase_sublist_of_sublist (h.erase b)

end diff

/-! ### enum -/

theorem length_enum_from : ∀ n (l : list α), length (enum_from n l) = length l
| n []     := rfl
| n (a::l) := congr_arg nat.succ (length_enum_from _ _)

theorem length_enum : ∀ (l : list α), length (enum l) = length l := length_enum_from _

@[simp] theorem enum_from_nth : ∀ n (l : list α) m,
  nth (enum_from n l) m = (λ a, (n + m, a)) <$> nth l m
| n []       m     := rfl
| n (a :: l) 0     := rfl
| n (a :: l) (m+1) := (enum_from_nth (n+1) l m).trans $
  by rw [add_right_comm]; refl

@[simp] theorem enum_nth : ∀ (l : list α) n,
  nth (enum l) n = (λ a, (n, a)) <$> nth l n :=
by simp only [enum, enum_from_nth, zero_add]; intros; refl

@[simp] theorem enum_from_map_snd : ∀ n (l : list α),
  map prod.snd (enum_from n l) = l
| n []       := rfl
| n (a :: l) := congr_arg (cons _) (enum_from_map_snd _ _)

@[simp] theorem enum_map_snd : ∀ (l : list α),
  map prod.snd (enum l) = l := enum_from_map_snd _

theorem mem_enum_from {x : α} {i : ℕ} :
   ∀ {j : ℕ} (xs : list α), (i, x) ∈ xs.enum_from j → j ≤ i ∧ i < j + xs.length ∧ x ∈ xs
| j [] := by simp [enum_from]
| j (y :: ys) :=
suffices i = j ∧ x = y ∨ (i, x) ∈ enum_from (j + 1) ys →
    j ≤ i ∧ i < j + (length ys + 1) ∧ (x = y ∨ x ∈ ys),
  by simpa [enum_from, mem_enum_from ys],
begin
  rintro (h|h),
  { refine ⟨le_of_eq h.1.symm,h.1 ▸ _,or.inl h.2⟩,
    apply nat.lt_add_of_pos_right; simp },
  { obtain ⟨hji, hijlen, hmem⟩ := mem_enum_from _ h,
    refine ⟨_, _, _⟩,
    { exact le_trans (nat.le_succ _) hji },
    { convert hijlen using 1, ac_refl },
    { simp [hmem] } }
end

/-! ### product -/

@[simp] theorem nil_product (l : list β) : product (@nil α) l = [] := rfl

@[simp] theorem product_cons (a : α) (l₁ : list α) (l₂ : list β)
        : product (a::l₁) l₂ = map (λ b, (a, b)) l₂ ++ product l₁ l₂ := rfl

@[simp] theorem product_nil : ∀ (l : list α), product l (@nil β) = []
| []     := rfl
| (a::l) := by rw [product_cons, product_nil]; refl

@[simp] theorem mem_product {l₁ : list α} {l₂ : list β} {a : α} {b : β} :
  (a, b) ∈ product l₁ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ :=
by simp only [product, mem_bind, mem_map, prod.ext_iff, exists_prop,
  and.left_comm, exists_and_distrib_left, exists_eq_left, exists_eq_right]

theorem length_product (l₁ : list α) (l₂ : list β) :
  length (product l₁ l₂) = length l₁ * length l₂ :=
by induction l₁ with x l₁ IH; [exact (zero_mul _).symm,
  simp only [length, product_cons, length_append, IH,
    right_distrib, one_mul, length_map, add_comm]]


/-! ### sigma -/
section
variable {σ : α → Type*}

@[simp] theorem nil_sigma (l : Π a, list (σ a)) : (@nil α).sigma l = [] := rfl

@[simp] theorem sigma_cons (a : α) (l₁ : list α) (l₂ : Π a, list (σ a))
        : (a::l₁).sigma l₂ = map (sigma.mk a) (l₂ a) ++ l₁.sigma l₂ := rfl

@[simp] theorem sigma_nil : ∀ (l : list α), l.sigma (λ a, @nil (σ a)) = []
| []     := rfl
| (a::l) := by rw [sigma_cons, sigma_nil]; refl

@[simp] theorem mem_sigma {l₁ : list α} {l₂ : Π a, list (σ a)} {a : α} {b : σ a} :
  sigma.mk a b ∈ l₁.sigma l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ a :=
by simp only [list.sigma, mem_bind, mem_map, exists_prop, exists_and_distrib_left,
  and.left_comm, exists_eq_left, heq_iff_eq, exists_eq_right]

theorem length_sigma (l₁ : list α) (l₂ : Π a, list (σ a)) :
  length (l₁.sigma l₂) = (l₁.map (λ a, length (l₂ a))).sum :=
by induction l₁ with x l₁ IH; [refl,
simp only [map, sigma_cons, length_append, length_map, IH, sum_cons]]
end

/-! ### disjoint -/
section disjoint

theorem disjoint.symm {l₁ l₂ : list α} (d : disjoint l₁ l₂) : disjoint l₂ l₁
| a i₂ i₁ := d i₁ i₂

theorem disjoint_comm {l₁ l₂ : list α} : disjoint l₁ l₂ ↔ disjoint l₂ l₁ :=
⟨disjoint.symm, disjoint.symm⟩

theorem disjoint_left {l₁ l₂ : list α} : disjoint l₁ l₂ ↔ ∀ {a}, a ∈ l₁ → a ∉ l₂ := iff.rfl

theorem disjoint_right {l₁ l₂ : list α} : disjoint l₁ l₂ ↔ ∀ {a}, a ∈ l₂ → a ∉ l₁ :=
disjoint_comm

theorem disjoint_iff_ne {l₁ l₂ : list α} : disjoint l₁ l₂ ↔ ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b :=
by simp only [disjoint_left, imp_not_comm, forall_eq']

theorem disjoint_of_subset_left {l₁ l₂ l : list α} (ss : l₁ ⊆ l) (d : disjoint l l₂) :
  disjoint l₁ l₂
| x m₁ := d (ss m₁)

theorem disjoint_of_subset_right {l₁ l₂ l : list α} (ss : l₂ ⊆ l) (d : disjoint l₁ l) :
  disjoint l₁ l₂
| x m m₁ := d m (ss m₁)

theorem disjoint_of_disjoint_cons_left {a : α} {l₁ l₂} : disjoint (a::l₁) l₂ → disjoint l₁ l₂ :=
disjoint_of_subset_left (list.subset_cons _ _)

theorem disjoint_of_disjoint_cons_right {a : α} {l₁ l₂} : disjoint l₁ (a::l₂) → disjoint l₁ l₂ :=
disjoint_of_subset_right (list.subset_cons _ _)

@[simp] theorem disjoint_nil_left (l : list α) : disjoint [] l
| a := (not_mem_nil a).elim

@[simp] theorem disjoint_nil_right (l : list α) : disjoint l [] :=
by rw disjoint_comm; exact disjoint_nil_left _

@[simp, priority 1100] theorem singleton_disjoint {l : list α} {a : α} : disjoint [a] l ↔ a ∉ l :=
by simp only [disjoint, mem_singleton, forall_eq]; refl

@[simp, priority 1100] theorem disjoint_singleton {l : list α} {a : α} : disjoint l [a] ↔ a ∉ l :=
by rw disjoint_comm; simp only [singleton_disjoint]

@[simp] theorem disjoint_append_left {l₁ l₂ l : list α} :
  disjoint (l₁++l₂) l ↔ disjoint l₁ l ∧ disjoint l₂ l :=
by simp only [disjoint, mem_append, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_append_right {l₁ l₂ l : list α} :
  disjoint l (l₁++l₂) ↔ disjoint l l₁ ∧ disjoint l l₂ :=
disjoint_comm.trans $ by simp only [disjoint_comm, disjoint_append_left]

@[simp] theorem disjoint_cons_left {a : α} {l₁ l₂ : list α} :
  disjoint (a::l₁) l₂ ↔ a ∉ l₂ ∧ disjoint l₁ l₂ :=
(@disjoint_append_left _ [a] l₁ l₂).trans $ by simp only [singleton_disjoint]

@[simp] theorem disjoint_cons_right {a : α} {l₁ l₂ : list α} :
  disjoint l₁ (a::l₂) ↔ a ∉ l₁ ∧ disjoint l₁ l₂ :=
disjoint_comm.trans $ by simp only [disjoint_comm, disjoint_cons_left]

theorem disjoint_of_disjoint_append_left_left {l₁ l₂ l : list α} (d : disjoint (l₁++l₂) l) :
  disjoint l₁ l :=
(disjoint_append_left.1 d).1

theorem disjoint_of_disjoint_append_left_right {l₁ l₂ l : list α} (d : disjoint (l₁++l₂) l) :
  disjoint l₂ l :=
(disjoint_append_left.1 d).2

theorem disjoint_of_disjoint_append_right_left {l₁ l₂ l : list α} (d : disjoint l (l₁++l₂)) :
  disjoint l l₁ :=
(disjoint_append_right.1 d).1

theorem disjoint_of_disjoint_append_right_right {l₁ l₂ l : list α} (d : disjoint l (l₁++l₂)) :
  disjoint l l₂ :=
(disjoint_append_right.1 d).2

theorem disjoint_take_drop {l : list α} {m n : ℕ} (hl : l.nodup) (h : m ≤ n) :
  disjoint (l.take m) (l.drop n) :=
begin
  induction l generalizing m n,
  case list.nil : m n
  { simp },
  case list.cons : x xs xs_ih m n
  { cases m; cases n; simp only [disjoint_cons_left, mem_cons_iff, disjoint_cons_right, drop,
                                 true_or, eq_self_iff_true, not_true, false_and,
                                 disjoint_nil_left, take],
    { cases h },
    cases hl with _ _ h₀ h₁, split,
    { intro h, exact h₀ _ (mem_of_mem_drop h) rfl, },
    solve_by_elim [le_of_succ_le_succ] { max_depth := 4 } },
end

end disjoint

/-! ### union -/
section union
variable [decidable_eq α]

@[simp] theorem nil_union (l : list α) : [] ∪ l = l := rfl

@[simp] theorem cons_union (l₁ l₂ : list α) (a : α) : a :: l₁ ∪ l₂ = insert a (l₁ ∪ l₂) := rfl

@[simp] theorem mem_union {l₁ l₂ : list α} {a : α} : a ∈ l₁ ∪ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ :=
by induction l₁; simp only [nil_union, not_mem_nil, false_or, cons_union, mem_insert_iff,
  mem_cons_iff, or_assoc, *]

theorem mem_union_left {a : α} {l₁ : list α} (h : a ∈ l₁) (l₂ : list α) : a ∈ l₁ ∪ l₂ :=
mem_union.2 (or.inl h)

theorem mem_union_right {a : α} (l₁ : list α) {l₂ : list α} (h : a ∈ l₂) : a ∈ l₁ ∪ l₂ :=
mem_union.2 (or.inr h)

theorem sublist_suffix_of_union : ∀ l₁ l₂ : list α, ∃ t, t <+ l₁ ∧ t ++ l₂ = l₁ ∪ l₂
| [] l₂ := ⟨[], by refl, rfl⟩
| (a::l₁) l₂ := let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂ in
  if h : a ∈ l₁ ∪ l₂
  then ⟨t, sublist_cons_of_sublist _ s, by simp only [e, cons_union, insert_of_mem h]⟩
  else ⟨a::t, cons_sublist_cons _ s, by simp only [cons_append, cons_union, e, insert_of_not_mem h];
    split; refl⟩

theorem suffix_union_right (l₁ l₂ : list α) : l₂ <:+ l₁ ∪ l₂ :=
(sublist_suffix_of_union l₁ l₂).imp (λ a, and.right)

theorem union_sublist_append (l₁ l₂ : list α) : l₁ ∪ l₂ <+ l₁ ++ l₂ :=
let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂ in
e ▸ (append_sublist_append_right _).2 s

theorem forall_mem_union {p : α → Prop} {l₁ l₂ : list α} :
  (∀ x ∈ l₁ ∪ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ (∀ x ∈ l₂, p x) :=
by simp only [mem_union, or_imp_distrib, forall_and_distrib]

theorem forall_mem_of_forall_mem_union_left {p : α → Prop} {l₁ l₂ : list α}
   (h : ∀ x ∈ l₁ ∪ l₂, p x) : ∀ x ∈ l₁, p x :=
(forall_mem_union.1 h).1

theorem forall_mem_of_forall_mem_union_right {p : α → Prop} {l₁ l₂ : list α}
   (h : ∀ x ∈ l₁ ∪ l₂, p x) : ∀ x ∈ l₂, p x :=
(forall_mem_union.1 h).2

end union

/-! ### inter -/
section inter
variable [decidable_eq α]

@[simp] theorem inter_nil (l : list α) : [] ∩ l = [] := rfl

@[simp] theorem inter_cons_of_mem {a : α} (l₁ : list α) {l₂ : list α} (h : a ∈ l₂) :
  (a::l₁) ∩ l₂ = a :: (l₁ ∩ l₂) :=
if_pos h

@[simp] theorem inter_cons_of_not_mem {a : α} (l₁ : list α) {l₂ : list α} (h : a ∉ l₂) :
  (a::l₁) ∩ l₂ = l₁ ∩ l₂ :=
if_neg h

theorem mem_of_mem_inter_left {l₁ l₂ : list α} {a : α} : a ∈ l₁ ∩ l₂ → a ∈ l₁ :=
mem_of_mem_filter

theorem mem_of_mem_inter_right {l₁ l₂ : list α} {a : α} : a ∈ l₁ ∩ l₂ → a ∈ l₂ :=
of_mem_filter

theorem mem_inter_of_mem_of_mem {l₁ l₂ : list α} {a : α} : a ∈ l₁ → a ∈ l₂ → a ∈ l₁ ∩ l₂ :=
mem_filter_of_mem

@[simp] theorem mem_inter {a : α} {l₁ l₂ : list α} : a ∈ l₁ ∩ l₂ ↔ a ∈ l₁ ∧ a ∈ l₂ :=
mem_filter

theorem inter_subset_left (l₁ l₂ : list α) : l₁ ∩ l₂ ⊆ l₁ :=
filter_subset _

theorem inter_subset_right (l₁ l₂ : list α) : l₁ ∩ l₂ ⊆ l₂ :=
λ a, mem_of_mem_inter_right

theorem subset_inter {l l₁ l₂ : list α} (h₁ : l ⊆ l₁) (h₂ : l ⊆ l₂) : l ⊆ l₁ ∩ l₂ :=
λ a h, mem_inter.2 ⟨h₁ h, h₂ h⟩

theorem inter_eq_nil_iff_disjoint {l₁ l₂ : list α} : l₁ ∩ l₂ = [] ↔ disjoint l₁ l₂ :=
by simp only [eq_nil_iff_forall_not_mem, mem_inter, not_and]; refl

theorem forall_mem_inter_of_forall_left {p : α → Prop} {l₁ : list α} (h : ∀ x ∈ l₁, p x)
     (l₂ : list α) :
  ∀ x, x ∈ l₁ ∩ l₂ → p x :=
ball.imp_left (λ x, mem_of_mem_inter_left) h

theorem forall_mem_inter_of_forall_right {p : α → Prop} (l₁ : list α) {l₂ : list α}
    (h : ∀ x ∈ l₂, p x) :
  ∀ x, x ∈ l₁ ∩ l₂ → p x :=
ball.imp_left (λ x, mem_of_mem_inter_right) h

@[simp] lemma inter_reverse {xs ys : list α} :
  xs.inter ys.reverse = xs.inter ys :=
by simp only [list.inter, mem_reverse]; congr

end inter

section choose
variables (p : α → Prop) [decidable_pred p] (l : list α)

lemma choose_spec (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
(choose_x p l hp).property

lemma choose_mem (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l := (choose_spec _ _ _).1

lemma choose_property (hp : ∃ a, a ∈ l ∧ p a) : p (choose p l hp) := (choose_spec _ _ _).2

end choose

/-! ### map₂_left' -/

section map₂_left'

-- The definitional equalities for `map₂_left'` can already be used by the
-- simplifie because `map₂_left'` is marked `@[simp]`.

@[simp] theorem map₂_left'_nil_right (f : α → option β → γ) (as) :
  map₂_left' f as [] = (as.map (λ a, f a none), []) :=
by cases as; refl

end map₂_left'

/-! ### map₂_right' -/

section map₂_right'

variables (f : option α → β → γ) (a : α) (as : list α) (b : β) (bs : list β)

@[simp] theorem map₂_right'_nil_left :
  map₂_right' f [] bs = (bs.map (f none), []) :=
by cases bs; refl

@[simp] theorem map₂_right'_nil_right  :
  map₂_right' f as [] = ([], as) :=
rfl

@[simp] theorem map₂_right'_nil_cons :
  map₂_right' f [] (b :: bs) = (f none b :: bs.map (f none), []) :=
rfl

@[simp] theorem map₂_right'_cons_cons :
  map₂_right' f (a :: as) (b :: bs) =
    let rec := map₂_right' f as bs in
    (f (some a) b :: rec.fst, rec.snd) :=
rfl

end map₂_right'

/-! ### zip_left' -/

section zip_left'

variables (a : α) (as : list α) (b : β) (bs : list β)

@[simp] theorem zip_left'_nil_right :
  zip_left' as ([] : list β) = (as.map (λ a, (a, none)), []) :=
by cases as; refl

@[simp] theorem zip_left'_nil_left :
  zip_left' ([] : list α) bs = ([], bs) :=
rfl

@[simp] theorem zip_left'_cons_nil :
  zip_left' (a :: as) ([] : list β) = ((a, none) :: as.map (λ a, (a, none)), []) :=
rfl

@[simp] theorem zip_left'_cons_cons :
  zip_left' (a :: as) (b :: bs) =
    let rec := zip_left' as bs in
    ((a, some b) :: rec.fst, rec.snd) :=
rfl

end zip_left'

/-! ### zip_right' -/

section zip_right'

variables (a : α) (as : list α) (b : β) (bs : list β)

@[simp] theorem zip_right'_nil_left :
  zip_right' ([] : list α) bs = (bs.map (λ b, (none, b)), []) :=
by cases bs; refl

@[simp] theorem zip_right'_nil_right :
  zip_right' as ([] : list β) = ([], as) :=
rfl

@[simp] theorem zip_right'_nil_cons :
  zip_right' ([] : list α) (b :: bs) = ((none, b) :: bs.map (λ b, (none, b)), []) :=
rfl

@[simp] theorem zip_right'_cons_cons :
  zip_right' (a :: as) (b :: bs) =
    let rec := zip_right' as bs in
    ((some a, b) :: rec.fst, rec.snd) :=
rfl

end zip_right'

/-! ### map₂_left -/

section map₂_left

variables (f : α → option β → γ) (as : list α)

-- The definitional equalities for `map₂_left` can already be used by the
-- simplifier because `map₂_left` is marked `@[simp]`.

@[simp] theorem map₂_left_nil_right :
  map₂_left f as [] = as.map (λ a, f a none) :=
by cases as; refl

theorem map₂_left_eq_map₂_left' : ∀ as bs,
  map₂_left f as bs = (map₂_left' f as bs).fst
| [] bs := by simp!
| (a :: as) [] := by simp!
| (a :: as) (b :: bs) := by simp! [*]

theorem map₂_left_eq_map₂ : ∀ as bs,
  length as ≤ length bs →
  map₂_left f as bs = map₂ (λ a b, f a (some b)) as bs
| [] [] h := by simp!
| [] (b :: bs) h := by simp!
| (a :: as) [] h := by { simp at h, contradiction }
| (a :: as) (b :: bs) h := by { simp at h, simp! [*] }

end map₂_left

/-! ### map₂_right -/

section map₂_right

variables (f : option α → β → γ) (a : α) (as : list α) (b : β) (bs : list β)

@[simp] theorem map₂_right_nil_left :
  map₂_right f [] bs = bs.map (f none) :=
by cases bs; refl

@[simp] theorem map₂_right_nil_right :
  map₂_right f as [] = [] :=
rfl

@[simp] theorem map₂_right_nil_cons :
  map₂_right f [] (b :: bs) = f none b :: bs.map (f none) :=
rfl

@[simp] theorem map₂_right_cons_cons :
  map₂_right f (a :: as) (b :: bs) = f (some a) b :: map₂_right f as bs :=
rfl

theorem map₂_right_eq_map₂_right' :
  map₂_right f as bs = (map₂_right' f as bs).fst :=
by simp only [map₂_right, map₂_right', map₂_left_eq_map₂_left']

theorem map₂_right_eq_map₂ (h : length bs ≤ length as) :
  map₂_right f as bs = map₂ (λ a b, f (some a) b) as bs :=
begin
  have : (λ a b, flip f a (some b)) = (flip (λ a b, f (some a) b)) := rfl,
  simp only [map₂_right, map₂_left_eq_map₂, map₂_flip, *]
end

end map₂_right

/-! ### zip_left -/

section zip_left

variables (a : α) (as : list α) (b : β) (bs : list β)

@[simp] theorem zip_left_nil_right :
  zip_left as ([] : list β) = as.map (λ a, (a, none)) :=
by cases as; refl

@[simp] theorem zip_left_nil_left :
  zip_left ([] : list α) bs = [] :=
rfl

@[simp] theorem zip_left_cons_nil :
  zip_left (a :: as) ([] : list β) = (a, none) :: as.map (λ a, (a, none)) :=
rfl

@[simp] theorem zip_left_cons_cons :
  zip_left (a :: as) (b :: bs) = (a, some b) :: zip_left as bs :=
rfl

theorem zip_left_eq_zip_left' :
  zip_left as bs = (zip_left' as bs).fst :=
by simp only [zip_left, zip_left', map₂_left_eq_map₂_left']

end zip_left

/-! ### zip_right -/

section zip_right

variables (a : α) (as : list α) (b : β) (bs : list β)

@[simp] theorem zip_right_nil_left :
  zip_right ([] : list α) bs = bs.map (λ b, (none, b)) :=
by cases bs; refl

@[simp] theorem zip_right_nil_right :
  zip_right as ([] : list β) = [] :=
rfl

@[simp] theorem zip_right_nil_cons :
  zip_right ([] : list α) (b :: bs) = (none, b) :: bs.map (λ b, (none, b)) :=
rfl

@[simp] theorem zip_right_cons_cons :
  zip_right (a :: as) (b :: bs) = (some a, b) :: zip_right as bs :=
rfl

theorem zip_right_eq_zip_right' :
  zip_right as bs = (zip_right' as bs).fst :=
by simp only [zip_right, zip_right', map₂_right_eq_map₂_right']

end zip_right

/-! ### Miscellaneous lemmas -/

theorem ilast'_mem : ∀ a l, @ilast' α a l ∈ a :: l
| a []     := or.inl rfl
| a (b::l) := or.inr (ilast'_mem b l)

@[simp] lemma nth_le_attach (L : list α) (i) (H : i < L.attach.length) :
  (L.attach.nth_le i H).1 = L.nth_le i (length_attach L ▸ H) :=
calc  (L.attach.nth_le i H).1
    = (L.attach.map subtype.val).nth_le i (by simpa using H) : by rw nth_le_map'
... = L.nth_le i _ : by congr; apply attach_map_val

end list

@[to_additive]
theorem monoid_hom.map_list_prod {α β : Type*} [monoid α] [monoid β] (f : α →* β) (l : list α) :
  f l.prod = (l.map f).prod :=
(l.prod_hom f).symm

namespace list

@[to_additive]
theorem prod_map_hom {α β γ : Type*} [monoid β] [monoid γ] (L : list α) (f : α → β) (g : β →* γ) :
  (L.map (g ∘ f)).prod = g ((L.map f).prod) :=
by {rw g.map_list_prod, exact congr_arg _ (map_map _ _ _).symm}

theorem sum_map_mul_left {α : Type*} [semiring α] {β : Type*} (L : list β)
  (f : β → α) (r : α) :
  (L.map (λ b, r * f b)).sum = r * (L.map f).sum :=
sum_map_hom L f $ add_monoid_hom.mul_left r

theorem sum_map_mul_right {α : Type*} [semiring α] {β : Type*} (L : list β)
  (f : β → α) (r : α) :
  (L.map (λ b, f b * r)).sum = (L.map f).sum * r :=
sum_map_hom L f $ add_monoid_hom.mul_right r

universes u v

@[simp]
theorem mem_map_swap {α : Type u} {β : Type v} (x : α) (y : β) (xs : list (α × β)) :
  (y, x) ∈ map prod.swap xs ↔ (x, y) ∈ xs :=
begin
  induction xs with x xs,
  { simp only [not_mem_nil, map_nil] },
  { cases x with a b,
    simp only [mem_cons_iff, prod.mk.inj_iff, map, prod.swap_prod_mk, prod.exists, xs_ih],
    tauto! },
end

lemma slice_eq {α} (xs : list α) (n m : ℕ) :
  slice n m xs = xs.take n ++ xs.drop (n+m) :=
begin
  induction n generalizing xs,
  { simp [slice] },
  { cases xs; simp [slice, *, nat.succ_add], }
end

lemma sizeof_slice_lt {α} [has_sizeof α] (i j : ℕ) (hj : 0 < j) (xs : list α) (hi : i < xs.length) :
  sizeof (list.slice i j xs) < sizeof xs :=
begin
  induction xs generalizing i j,
  case list.nil : i j h
  { cases hi },
  case list.cons : x xs xs_ih i j h
  { cases i; simp only [-slice_eq, list.slice],
    { cases j, cases h,
      dsimp only [drop], unfold_wf,
      apply @lt_of_le_of_lt _ _ _ xs.sizeof,
      { clear_except,
        induction xs generalizing j; unfold_wf,
        case list.nil : j
        { refl },
        case list.cons : xs_hd xs_tl xs_ih j
        { cases j; unfold_wf, refl,
          transitivity, apply xs_ih,
          simp }, },
      unfold_wf, apply zero_lt_one_add, },
    { unfold_wf, apply xs_ih _ _ h,
      apply lt_of_succ_lt_succ hi, } },
end

end list
