/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Multisets.
-/
import data.list.sort
import data.list.intervals
import data.list.antidiagonal
import data.string.basic
import algebra.group_power
import algebra.ordered_group
import control.traversable.lemmas
import control.traversable.instances

open list subtype nat

variables {α : Type*} {β : Type*} {γ : Type*}

/-- `multiset α` is the quotient of `list α` by list permutation. The result
  is a type of finite sets with duplicates allowed.  -/
def {u} multiset (α : Type u) : Type u :=
quotient (list.is_setoid α)

namespace multiset

instance : has_coe (list α) (multiset α) := ⟨quot.mk _⟩

@[simp] theorem quot_mk_to_coe (l : list α) : @eq (multiset α) ⟦l⟧ l := rfl

@[simp] theorem quot_mk_to_coe' (l : list α) : @eq (multiset α) (quot.mk (≈) l) l := rfl

@[simp] theorem quot_mk_to_coe'' (l : list α) : @eq (multiset α) (quot.mk setoid.r l) l := rfl

@[simp] theorem coe_eq_coe {l₁ l₂ : list α} : (l₁ : multiset α) = l₂ ↔ l₁ ~ l₂ := quotient.eq

instance has_decidable_eq [decidable_eq α] : decidable_eq (multiset α)
| s₁ s₂ := quotient.rec_on_subsingleton₂ s₁ s₂ $ λ l₁ l₂,
  decidable_of_iff' _ quotient.eq

/- empty multiset -/

/-- `0 : multiset α` is the empty set -/
protected def zero : multiset α := @nil α

instance : has_zero (multiset α)   := ⟨multiset.zero⟩
instance : has_emptyc (multiset α) := ⟨0⟩
instance : inhabited (multiset α)  := ⟨0⟩

@[simp] theorem coe_nil_eq_zero : (@nil α : multiset α) = 0 := rfl
@[simp] theorem empty_eq_zero : (∅ : multiset α) = 0 := rfl

theorem coe_eq_zero (l : list α) : (l : multiset α) = 0 ↔ l = [] :=
iff.trans coe_eq_coe perm_nil

/- cons -/

/-- `cons a s` is the multiset which contains `s` plus one more
  instance of `a`. -/
def cons (a : α) (s : multiset α) : multiset α :=
quot.lift_on s (λ l, (a :: l : multiset α))
  (λ l₁ l₂ p, quot.sound (p.cons a))

notation a :: b := cons a b

instance : has_insert α (multiset α) := ⟨cons⟩

@[simp] theorem insert_eq_cons (a : α) (s : multiset α) :
  insert a s = a::s := rfl

@[simp] theorem cons_coe (a : α) (l : list α) :
  (a::l : multiset α) = (a::l : list α) := rfl

theorem singleton_coe (a : α) : (a::0 : multiset α) = ([a] : list α) := rfl

@[simp] theorem cons_inj_left {a b : α} (s : multiset α) :
  a::s = b::s ↔ a = b :=
⟨quot.induction_on s $ λ l e,
  have [a] ++ l ~ [b] ++ l, from quotient.exact e,
  singleton_perm_singleton.1 $ (perm_append_right_iff _).1 this, congr_arg _⟩

@[simp] theorem cons_inj_right (a : α) : ∀{s t : multiset α}, a::s = a::t ↔ s = t :=
by rintros ⟨l₁⟩ ⟨l₂⟩; simp

@[recursor 5] protected theorem induction {p : multiset α → Prop}
  (h₁ : p 0) (h₂ : ∀ ⦃a : α⦄ {s : multiset α}, p s → p (a :: s)) : ∀s, p s :=
by rintros ⟨l⟩; induction l with _ _ ih; [exact h₁, exact h₂ ih]

@[elab_as_eliminator] protected theorem induction_on {p : multiset α → Prop}
  (s : multiset α) (h₁ : p 0) (h₂ : ∀ ⦃a : α⦄ {s : multiset α}, p s → p (a :: s)) : p s :=
multiset.induction h₁ h₂ s

theorem cons_swap (a b : α) (s : multiset α) : a :: b :: s = b :: a :: s :=
quot.induction_on s $ λ l, quotient.sound $ perm.swap _ _ _

section rec
variables {C : multiset α → Sort*}

/-- Dependent recursor on multisets.

TODO: should be @[recursor 6], but then the definition of `multiset.pi` fails with a stack
overflow in `whnf`.
-/
protected def rec
  (C_0 : C 0)
  (C_cons : Πa m, C m → C (a::m))
  (C_cons_heq : ∀a a' m b, C_cons a (a'::m) (C_cons a' m b) == C_cons a' (a::m) (C_cons a m b))
  (m : multiset α) : C m :=
quotient.hrec_on m (@list.rec α (λl, C ⟦l⟧) C_0 (λa l b, C_cons a ⟦l⟧ b)) $
  assume l l' h,
  h.rec_heq
    (assume a l l' b b' hl, have ⟦l⟧ = ⟦l'⟧, from quot.sound hl, by cc)
    (assume a a' l, C_cons_heq a a' ⟦l⟧)

@[elab_as_eliminator]
protected def rec_on (m : multiset α)
  (C_0 : C 0)
  (C_cons : Πa m, C m → C (a::m))
  (C_cons_heq : ∀a a' m b, C_cons a (a'::m) (C_cons a' m b) == C_cons a' (a::m) (C_cons a m b)) :
  C m :=
multiset.rec C_0 C_cons C_cons_heq m

variables {C_0 : C 0} {C_cons : Πa m, C m → C (a::m)}
  {C_cons_heq : ∀a a' m b, C_cons a (a'::m) (C_cons a' m b) == C_cons a' (a::m) (C_cons a m b)}

@[simp] lemma rec_on_0 : @multiset.rec_on α C (0:multiset α) C_0 C_cons C_cons_heq = C_0 :=
rfl

@[simp] lemma rec_on_cons (a : α) (m : multiset α) :
  (a :: m).rec_on C_0 C_cons C_cons_heq = C_cons a m (m.rec_on C_0 C_cons C_cons_heq) :=
quotient.induction_on m $ assume l, rfl

end rec

section mem

/-- `a ∈ s` means that `a` has nonzero multiplicity in `s`. -/
def mem (a : α) (s : multiset α) : Prop :=
quot.lift_on s (λ l, a ∈ l) (λ l₁ l₂ (e : l₁ ~ l₂), propext $ e.mem_iff)

instance : has_mem α (multiset α) := ⟨mem⟩

@[simp] lemma mem_coe {a : α} {l : list α} : a ∈ (l : multiset α) ↔ a ∈ l := iff.rfl

instance decidable_mem [decidable_eq α] (a : α) (s : multiset α) : decidable (a ∈ s) :=
quot.rec_on_subsingleton s $ list.decidable_mem a

@[simp] theorem mem_cons {a b : α} {s : multiset α} : a ∈ b :: s ↔ a = b ∨ a ∈ s :=
quot.induction_on s $ λ l, iff.rfl

lemma mem_cons_of_mem {a b : α} {s : multiset α} (h : a ∈ s) : a ∈ b :: s :=
mem_cons.2 $ or.inr h

@[simp] theorem mem_cons_self (a : α) (s : multiset α) : a ∈ a :: s :=
mem_cons.2 (or.inl rfl)

theorem exists_cons_of_mem {s : multiset α} {a : α} : a ∈ s → ∃ t, s = a :: t :=
quot.induction_on s $ λ l (h : a ∈ l),
let ⟨l₁, l₂, e⟩ := mem_split h in
e.symm ▸ ⟨(l₁++l₂ : list α), quot.sound perm_middle⟩

@[simp] theorem not_mem_zero (a : α) : a ∉ (0 : multiset α) := id

theorem eq_zero_of_forall_not_mem {s : multiset α} : (∀x, x ∉ s) → s = 0 :=
quot.induction_on s $ λ l H, by rw eq_nil_iff_forall_not_mem.mpr H; refl

theorem eq_zero_iff_forall_not_mem {s : multiset α} : s = 0 ↔ ∀ a, a ∉ s :=
⟨λ h, h.symm ▸ λ _, not_false, eq_zero_of_forall_not_mem⟩

theorem exists_mem_of_ne_zero {s : multiset α} : s ≠ 0 → ∃ a : α, a ∈ s :=
quot.induction_on s $ assume l hl,
  match l, hl with
  | [] := assume h, false.elim $ h rfl
  | (a :: l) := assume _, ⟨a, by simp⟩
  end

@[simp] lemma zero_ne_cons {a : α} {m : multiset α} : 0 ≠ a :: m :=
assume h, have a ∈ (0:multiset α), from h.symm ▸ mem_cons_self _ _, not_mem_zero _ this

@[simp] lemma cons_ne_zero {a : α} {m : multiset α} : a :: m ≠ 0 := zero_ne_cons.symm

lemma cons_eq_cons {a b : α} {as bs : multiset α} :
  a :: as = b :: bs ↔ ((a = b ∧ as = bs) ∨ (a ≠ b ∧ ∃cs, as = b :: cs ∧ bs = a :: cs)) :=
begin
  haveI : decidable_eq α := classical.dec_eq α,
  split,
  { assume eq,
    by_cases a = b,
    { subst h, simp * at * },
    { have : a ∈ b :: bs, from eq ▸ mem_cons_self _ _,
      have : a ∈ bs, by simpa [h],
      rcases exists_cons_of_mem this with ⟨cs, hcs⟩,
      simp [h, hcs],
      have : a :: as = b :: a :: cs, by simp [eq, hcs],
      have : a :: as = a :: b :: cs, by rwa [cons_swap],
      simpa using this } },
  { assume h,
    rcases h with ⟨eq₁, eq₂⟩ | ⟨h, cs, eq₁, eq₂⟩,
    { simp * },
    { simp [*, cons_swap a b] } }
end

end mem

/- subset -/
section subset

/-- `s ⊆ t` is the lift of the list subset relation. It means that any
  element with nonzero multiplicity in `s` has nonzero multiplicity in `t`,
  but it does not imply that the multiplicity of `a` in `s` is less or equal than in `t`;
  see `s ≤ t` for this relation. -/
protected def subset (s t : multiset α) : Prop := ∀ ⦃a : α⦄, a ∈ s → a ∈ t

instance : has_subset (multiset α) := ⟨multiset.subset⟩

@[simp] theorem coe_subset {l₁ l₂ : list α} : (l₁ : multiset α) ⊆ l₂ ↔ l₁ ⊆ l₂ := iff.rfl

@[simp] theorem subset.refl (s : multiset α) : s ⊆ s := λ a h, h

theorem subset.trans {s t u : multiset α} : s ⊆ t → t ⊆ u → s ⊆ u :=
λ h₁ h₂ a m, h₂ (h₁ m)

theorem subset_iff {s t : multiset α} : s ⊆ t ↔ (∀⦃x⦄, x ∈ s → x ∈ t) := iff.rfl

theorem mem_of_subset {s t : multiset α} {a : α} (h : s ⊆ t) : a ∈ s → a ∈ t := @h _

@[simp] theorem zero_subset (s : multiset α) : 0 ⊆ s :=
λ a, (not_mem_nil a).elim

@[simp] theorem cons_subset {a : α} {s t : multiset α} : (a :: s) ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
by simp [subset_iff, or_imp_distrib, forall_and_distrib]

theorem eq_zero_of_subset_zero {s : multiset α} (h : s ⊆ 0) : s = 0 :=
eq_zero_of_forall_not_mem h

theorem subset_zero {s : multiset α} : s ⊆ 0 ↔ s = 0 :=
⟨eq_zero_of_subset_zero, λ xeq, xeq.symm ▸ subset.refl 0⟩

end subset

/- multiset order -/

/-- `s ≤ t` means that `s` is a sublist of `t` (up to permutation).
  Equivalently, `s ≤ t` means that `count a s ≤ count a t` for all `a`. -/
protected def le (s t : multiset α) : Prop :=
quotient.lift_on₂ s t (<+~) $ λ v₁ v₂ w₁ w₂ p₁ p₂,
  propext (p₂.subperm_left.trans p₁.subperm_right)

instance : partial_order (multiset α) :=
{ le          := multiset.le,
  le_refl     := by rintros ⟨l⟩; exact subperm.refl _,
  le_trans    := by rintros ⟨l₁⟩ ⟨l₂⟩ ⟨l₃⟩; exact @subperm.trans _ _ _ _,
  le_antisymm := by rintros ⟨l₁⟩ ⟨l₂⟩ h₁ h₂; exact quot.sound (subperm.antisymm h₁ h₂) }

theorem subset_of_le {s t : multiset α} : s ≤ t → s ⊆ t :=
quotient.induction_on₂ s t $ λ l₁ l₂, subperm.subset

theorem mem_of_le {s t : multiset α} {a : α} (h : s ≤ t) : a ∈ s → a ∈ t :=
mem_of_subset (subset_of_le h)

@[simp] theorem coe_le {l₁ l₂ : list α} : (l₁ : multiset α) ≤ l₂ ↔ l₁ <+~ l₂ := iff.rfl

@[elab_as_eliminator] theorem le_induction_on {C : multiset α → multiset α → Prop}
  {s t : multiset α} (h : s ≤ t)
  (H : ∀ {l₁ l₂ : list α}, l₁ <+ l₂ → C l₁ l₂) : C s t :=
quotient.induction_on₂ s t (λ l₁ l₂ ⟨l, p, s⟩,
  (show ⟦l⟧ = ⟦l₁⟧, from quot.sound p) ▸ H s) h

theorem zero_le (s : multiset α) : 0 ≤ s :=
quot.induction_on s $ λ l, (nil_sublist l).subperm

theorem le_zero {s : multiset α} : s ≤ 0 ↔ s = 0 :=
⟨λ h, le_antisymm h (zero_le _), le_of_eq⟩

theorem lt_cons_self (s : multiset α) (a : α) : s < a :: s :=
quot.induction_on s $ λ l,
suffices l <+~ a :: l ∧ (¬l ~ a :: l),
  by simpa [lt_iff_le_and_ne],
⟨(sublist_cons _ _).subperm,
 λ p, ne_of_lt (lt_succ_self (length l)) p.length_eq⟩

theorem le_cons_self (s : multiset α) (a : α) : s ≤ a :: s :=
le_of_lt $ lt_cons_self _ _

theorem cons_le_cons_iff (a : α) {s t : multiset α} : a :: s ≤ a :: t ↔ s ≤ t :=
quotient.induction_on₂ s t $ λ l₁ l₂, subperm_cons a

theorem cons_le_cons (a : α) {s t : multiset α} : s ≤ t → a :: s ≤ a :: t :=
(cons_le_cons_iff a).2

theorem le_cons_of_not_mem {a : α} {s t : multiset α} (m : a ∉ s) : s ≤ a :: t ↔ s ≤ t :=
begin
  refine ⟨_, λ h, le_trans h $ le_cons_self _ _⟩,
  suffices : ∀ {t'} (_ : s ≤ t') (_ : a ∈ t'), a :: s ≤ t',
  { exact λ h, (cons_le_cons_iff a).1 (this h (mem_cons_self _ _)) },
  introv h, revert m, refine le_induction_on h _,
  introv s m₁ m₂,
  rcases mem_split m₂ with ⟨r₁, r₂, rfl⟩,
  exact perm_middle.subperm_left.2 ((subperm_cons _).2 $
    ((sublist_or_mem_of_sublist s).resolve_right m₁).subperm)
end

/- cardinality -/

/-- The cardinality of a multiset is the sum of the multiplicities
  of all its elements, or simply the length of the underlying list. -/
def card (s : multiset α) : ℕ :=
quot.lift_on s length $ λ l₁ l₂, perm.length_eq

@[simp] theorem coe_card (l : list α) : card (l : multiset α) = length l := rfl

@[simp] theorem card_zero : @card α 0 = 0 := rfl

@[simp] theorem card_cons (a : α) (s : multiset α) : card (a :: s) = card s + 1 :=
quot.induction_on s $ λ l, rfl

@[simp] theorem card_singleton (a : α) : card (a::0) = 1 := by simp

theorem card_le_of_le {s t : multiset α} (h : s ≤ t) : card s ≤ card t :=
le_induction_on h $ λ l₁ l₂, length_le_of_sublist

theorem eq_of_le_of_card_le {s t : multiset α} (h : s ≤ t) : card t ≤ card s → s = t :=
le_induction_on h $ λ l₁ l₂ s h₂, congr_arg coe $ eq_of_sublist_of_length_le s h₂

theorem card_lt_of_lt {s t : multiset α} (h : s < t) : card s < card t :=
lt_of_not_ge $ λ h₂, ne_of_lt h $ eq_of_le_of_card_le (le_of_lt h) h₂

theorem lt_iff_cons_le {s t : multiset α} : s < t ↔ ∃ a, a :: s ≤ t :=
⟨quotient.induction_on₂ s t $ λ l₁ l₂ h,
  subperm.exists_of_length_lt (le_of_lt h) (card_lt_of_lt h),
λ ⟨a, h⟩, lt_of_lt_of_le (lt_cons_self _ _) h⟩

@[simp] theorem card_eq_zero {s : multiset α} : card s = 0 ↔ s = 0 :=
⟨λ h, (eq_of_le_of_card_le (zero_le _) (le_of_eq h)).symm, λ e, by simp [e]⟩

theorem card_pos {s : multiset α} : 0 < card s ↔ s ≠ 0 :=
pos_iff_ne_zero.trans $ not_congr card_eq_zero

theorem card_pos_iff_exists_mem {s : multiset α} : 0 < card s ↔ ∃ a, a ∈ s :=
quot.induction_on s $ λ l, length_pos_iff_exists_mem

@[elab_as_eliminator] def strong_induction_on {p : multiset α → Sort*} :
  ∀ (s : multiset α), (∀ s, (∀t < s, p t) → p s) → p s
| s := λ ih, ih s $ λ t h,
  have card t < card s, from card_lt_of_lt h,
  strong_induction_on t ih
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf card⟩]}

theorem strong_induction_eq {p : multiset α → Sort*}
  (s : multiset α) (H) : @strong_induction_on _ p s H =
    H s (λ t h, @strong_induction_on _ p t H) :=
by rw [strong_induction_on]

@[elab_as_eliminator] lemma case_strong_induction_on {p : multiset α → Prop}
  (s : multiset α) (h₀ : p 0) (h₁ : ∀ a s, (∀t ≤ s, p t) → p (a :: s)) : p s :=
multiset.strong_induction_on s $ assume s,
multiset.induction_on s (λ _, h₀) $ λ a s _ ih, h₁ _ _ $
λ t h, ih _ $ lt_of_le_of_lt h $ lt_cons_self _ _

/- singleton -/
instance : has_singleton α (multiset α) := ⟨λ a, a::0⟩

instance : is_lawful_singleton α (multiset α) := ⟨λ a, rfl⟩

@[simp] theorem singleton_eq_singleton (a : α) : singleton a = a::0 := rfl

@[simp] theorem mem_singleton {a b : α} : b ∈ a::0 ↔ b = a := by simp

theorem mem_singleton_self (a : α) : a ∈ (a::0 : multiset α) := mem_cons_self _ _

theorem singleton_inj {a b : α} : a::0 = b::0 ↔ a = b := cons_inj_left _

@[simp] theorem singleton_ne_zero (a : α) : a::0 ≠ 0 :=
ne_of_gt (lt_cons_self _ _)

@[simp] theorem singleton_le {a : α} {s : multiset α} : a::0 ≤ s ↔ a ∈ s :=
⟨λ h, mem_of_le h (mem_singleton_self _),
 λ h, let ⟨t, e⟩ := exists_cons_of_mem h in e.symm ▸ cons_le_cons _ (zero_le _)⟩

theorem card_eq_one {s : multiset α} : card s = 1 ↔ ∃ a, s = a::0 :=
⟨quot.induction_on s $ λ l h,
  (list.length_eq_one.1 h).imp $ λ a, congr_arg coe,
 λ ⟨a, e⟩, e.symm ▸ rfl⟩

/- add -/

/-- The sum of two multisets is the lift of the list append operation.
  This adds the multiplicities of each element,
  i.e. `count a (s + t) = count a s + count a t`. -/
protected def add (s₁ s₂ : multiset α) : multiset α :=
quotient.lift_on₂ s₁ s₂ (λ l₁ l₂, ((l₁ ++ l₂ : list α) : multiset α)) $
  λ v₁ v₂ w₁ w₂ p₁ p₂, quot.sound $ p₁.append p₂

instance : has_add (multiset α) := ⟨multiset.add⟩

@[simp] theorem coe_add (s t : list α) : (s + t : multiset α) = (s ++ t : list α) := rfl

protected theorem add_comm (s t : multiset α) : s + t = t + s :=
quotient.induction_on₂ s t $ λ l₁ l₂, quot.sound perm_append_comm

protected theorem zero_add (s : multiset α) : 0 + s = s :=
quot.induction_on s $ λ l, rfl

theorem singleton_add (a : α) (s : multiset α) : ↑[a] + s = a::s := rfl

protected theorem add_le_add_left (s) {t u : multiset α} : s + t ≤ s + u ↔ t ≤ u :=
quotient.induction_on₃ s t u $ λ l₁ l₂ l₃, subperm_append_left _

protected theorem add_left_cancel (s) {t u : multiset α} (h : s + t = s + u) : t = u :=
le_antisymm ((multiset.add_le_add_left _).1 (le_of_eq h))
  ((multiset.add_le_add_left _).1 (le_of_eq h.symm))

instance : ordered_cancel_add_comm_monoid (multiset α) :=
{ zero                  := 0,
  add                   := (+),
  add_comm              := multiset.add_comm,
  add_assoc             := λ s₁ s₂ s₃, quotient.induction_on₃ s₁ s₂ s₃ $ λ l₁ l₂ l₃,
    congr_arg coe $ append_assoc l₁ l₂ l₃,
  zero_add              := multiset.zero_add,
  add_zero              := λ s, by rw [multiset.add_comm, multiset.zero_add],
  add_left_cancel       := multiset.add_left_cancel,
  add_right_cancel      := λ s₁ s₂ s₃ h, multiset.add_left_cancel s₂ $
    by simpa [multiset.add_comm] using h,
  add_le_add_left       := λ s₁ s₂ h s₃, (multiset.add_le_add_left _).2 h,
  le_of_add_le_add_left := λ s₁ s₂ s₃, (multiset.add_le_add_left _).1,
  ..@multiset.partial_order α }

@[simp] theorem cons_add (a : α) (s t : multiset α) : a :: s + t = a :: (s + t) :=
by rw [← singleton_add, ← singleton_add, add_assoc]

@[simp] theorem add_cons (a : α) (s t : multiset α) : s + a :: t = a :: (s + t) :=
by rw [add_comm, cons_add, add_comm]

theorem le_add_right (s t : multiset α) : s ≤ s + t :=
by simpa using add_le_add_left (zero_le t) s

theorem le_add_left (s t : multiset α) : s ≤ t + s :=
by simpa using add_le_add_right (zero_le t) s

@[simp] theorem card_add (s t : multiset α) : card (s + t) = card s + card t :=
quotient.induction_on₂ s t length_append

lemma card_smul (s : multiset α) (n : ℕ) :
  (n •ℕ s).card = n * s.card :=
by induction n; simp [succ_nsmul, *, nat.succ_mul]; cc

@[simp] theorem mem_add {a : α} {s t : multiset α} : a ∈ s + t ↔ a ∈ s ∨ a ∈ t :=
quotient.induction_on₂ s t $ λ l₁ l₂, mem_append

theorem le_iff_exists_add {s t : multiset α} : s ≤ t ↔ ∃ u, t = s + u :=
⟨λ h, le_induction_on h $ λ l₁ l₂ s,
  let ⟨l, p⟩ := s.exists_perm_append in ⟨l, quot.sound p⟩,
λ⟨u, e⟩, e.symm ▸ le_add_right s u⟩

instance : canonically_ordered_add_monoid (multiset α) :=
{ lt_of_add_lt_add_left := @lt_of_add_lt_add_left _ _,
  le_iff_exists_add     := @le_iff_exists_add _,
  bot                   := 0,
  bot_le                := multiset.zero_le,
  ..multiset.ordered_cancel_add_comm_monoid }

/- repeat -/

/-- `repeat a n` is the multiset containing only `a` with multiplicity `n`. -/
def repeat (a : α) (n : ℕ) : multiset α := repeat a n

@[simp] lemma repeat_zero (a : α) : repeat a 0 = 0 := rfl

@[simp] lemma repeat_succ (a : α) (n) : repeat a (n+1) = a :: repeat a n := by simp [repeat]

@[simp] lemma repeat_one (a : α) : repeat a 1 = a :: 0 := by simp

@[simp] lemma card_repeat : ∀ (a : α) n, card (repeat a n) = n := length_repeat

theorem eq_of_mem_repeat {a b : α} {n} : b ∈ repeat a n → b = a := eq_of_mem_repeat

theorem eq_repeat' {a : α} {s : multiset α} : s = repeat a s.card ↔ ∀ b ∈ s, b = a :=
quot.induction_on s $ λ l, iff.trans ⟨λ h,
  (perm_repeat.1 $ (quotient.exact h)), congr_arg coe⟩ eq_repeat'

theorem eq_repeat_of_mem {a : α} {s : multiset α} : (∀ b ∈ s, b = a) → s = repeat a s.card :=
eq_repeat'.2

theorem eq_repeat {a : α} {n} {s : multiset α} : s = repeat a n ↔ card s = n ∧ ∀ b ∈ s, b = a :=
⟨λ h, h.symm ▸ ⟨card_repeat _ _, λ b, eq_of_mem_repeat⟩,
 λ ⟨e, al⟩, e ▸ eq_repeat_of_mem al⟩

theorem repeat_subset_singleton : ∀ (a : α) n, repeat a n ⊆ a::0 := repeat_subset_singleton

theorem repeat_le_coe {a : α} {n} {l : list α} : repeat a n ≤ l ↔ list.repeat a n <+ l :=
⟨λ ⟨l', p, s⟩, (perm_repeat.1 p) ▸ s, sublist.subperm⟩

/- range -/

/-- `range n` is the multiset lifted from the list `range n`,
  that is, the set `{0, 1, ..., n-1}`. -/
def range (n : ℕ) : multiset ℕ := range n

@[simp] theorem range_zero : range 0 = 0 := rfl

@[simp] theorem range_succ (n : ℕ) : range (succ n) = n :: range n :=
by rw [range, range_concat, ← coe_add, add_comm]; refl

@[simp] theorem card_range (n : ℕ) : card (range n) = n := length_range _

theorem range_subset {m n : ℕ} : range m ⊆ range n ↔ m ≤ n := range_subset

@[simp] theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n := mem_range

@[simp] theorem not_mem_range_self {n : ℕ} : n ∉ range n := not_mem_range_self

theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) := list.self_mem_range_succ n

/- erase -/
section erase
variables [decidable_eq α] {s t : multiset α} {a b : α}

/-- `erase s a` is the multiset that subtracts 1 from the
  multiplicity of `a`. -/
def erase (s : multiset α) (a : α) : multiset α :=
quot.lift_on s (λ l, (l.erase a : multiset α))
  (λ l₁ l₂ p, quot.sound (p.erase a))

@[simp] theorem coe_erase (l : list α) (a : α) :
  erase (l : multiset α) a = l.erase a := rfl

@[simp] theorem erase_zero (a : α) : (0 : multiset α).erase a = 0 := rfl

@[simp] theorem erase_cons_head (a : α) (s : multiset α) : (a :: s).erase a = s :=
quot.induction_on s $ λ l, congr_arg coe $ erase_cons_head a l

@[simp, priority 990]
theorem erase_cons_tail {a b : α} (s : multiset α) (h : b ≠ a) : (b::s).erase a = b :: s.erase a :=
quot.induction_on s $ λ l, congr_arg coe $ erase_cons_tail l h

@[simp, priority 980]
theorem erase_of_not_mem {a : α} {s : multiset α} : a ∉ s → s.erase a = s :=
quot.induction_on s $ λ l h, congr_arg coe $ erase_of_not_mem h

@[simp, priority 980]
theorem cons_erase {s : multiset α} {a : α} : a ∈ s → a :: s.erase a = s :=
quot.induction_on s $ λ l h, quot.sound (perm_cons_erase h).symm

theorem le_cons_erase (s : multiset α) (a : α) : s ≤ a :: s.erase a :=
if h : a ∈ s then le_of_eq (cons_erase h).symm
else by rw erase_of_not_mem h; apply le_cons_self

theorem erase_add_left_pos {a : α} {s : multiset α} (t) : a ∈ s → (s + t).erase a = s.erase a + t :=
quotient.induction_on₂ s t $ λ l₁ l₂ h, congr_arg coe $ erase_append_left l₂ h

theorem erase_add_right_pos {a : α} (s) {t : multiset α} (h : a ∈ t) :
  (s + t).erase a = s + t.erase a :=
by rw [add_comm, erase_add_left_pos s h, add_comm]

theorem erase_add_right_neg {a : α} {s : multiset α} (t) :
  a ∉ s → (s + t).erase a = s + t.erase a :=
quotient.induction_on₂ s t $ λ l₁ l₂ h, congr_arg coe $ erase_append_right l₂ h

theorem erase_add_left_neg {a : α} (s) {t : multiset α} (h : a ∉ t) :
  (s + t).erase a = s.erase a + t :=
by rw [add_comm, erase_add_right_neg s h, add_comm]

theorem erase_le (a : α) (s : multiset α) : s.erase a ≤ s :=
quot.induction_on s $ λ l, (erase_sublist a l).subperm

@[simp] theorem erase_lt {a : α} {s : multiset α} : s.erase a < s ↔ a ∈ s :=
⟨λ h, not_imp_comm.1 erase_of_not_mem (ne_of_lt h),
 λ h, by simpa [h] using lt_cons_self (s.erase a) a⟩

theorem erase_subset (a : α) (s : multiset α) : s.erase a ⊆ s :=
subset_of_le (erase_le a s)

theorem mem_erase_of_ne {a b : α} {s : multiset α} (ab : a ≠ b) : a ∈ s.erase b ↔ a ∈ s :=
quot.induction_on s $ λ l, list.mem_erase_of_ne ab

theorem mem_of_mem_erase {a b : α} {s : multiset α} : a ∈ s.erase b → a ∈ s :=
mem_of_subset (erase_subset _ _)

theorem erase_comm (s : multiset α) (a b : α) : (s.erase a).erase b = (s.erase b).erase a :=
quot.induction_on s $ λ l, congr_arg coe $ l.erase_comm a b

theorem erase_le_erase {s t : multiset α} (a : α) (h : s ≤ t) : s.erase a ≤ t.erase a :=
le_induction_on h $ λ l₁ l₂ h, (h.erase _).subperm

theorem erase_le_iff_le_cons {s t : multiset α} {a : α} : s.erase a ≤ t ↔ s ≤ a :: t :=
⟨λ h, le_trans (le_cons_erase _ _) (cons_le_cons _ h),
 λ h, if m : a ∈ s
  then by rw ← cons_erase m at h; exact (cons_le_cons_iff _).1 h
  else le_trans (erase_le _ _) ((le_cons_of_not_mem m).1 h)⟩

@[simp] theorem card_erase_of_mem {a : α} {s : multiset α} :
  a ∈ s → card (s.erase a) = pred (card s) :=
quot.induction_on s $ λ l, length_erase_of_mem

theorem card_erase_lt_of_mem {a : α} {s : multiset α} : a ∈ s → card (s.erase a) < card s :=
λ h, card_lt_of_lt (erase_lt.mpr h)

theorem card_erase_le {a : α} {s : multiset α} : card (s.erase a) ≤ card s :=
card_le_of_le (erase_le a s)

end erase

@[simp] theorem coe_reverse (l : list α) : (reverse l : multiset α) = l :=
quot.sound $ reverse_perm _

/- map -/

/-- `map f s` is the lift of the list `map` operation. The multiplicity
  of `b` in `map f s` is the number of `a ∈ s` (counting multiplicity)
  such that `f a = b`. -/
def map (f : α → β) (s : multiset α) : multiset β :=
quot.lift_on s (λ l : list α, (l.map f : multiset β))
  (λ l₁ l₂ p, quot.sound (p.map f))

@[simp] theorem coe_map (f : α → β) (l : list α) : map f ↑l = l.map f := rfl

@[simp] theorem map_zero (f : α → β) : map f 0 = 0 := rfl

@[simp] theorem map_cons (f : α → β) (a s) : map f (a::s) = f a :: map f s :=
quot.induction_on s $ λ l, rfl

lemma map_singleton (f : α → β) (a : α) : ({a} : multiset α).map f = {f a} := rfl

@[simp] theorem map_add (f : α → β) (s t) : map f (s + t) = map f s + map f t :=
quotient.induction_on₂ s t $ λ l₁ l₂, congr_arg coe $ map_append _ _ _

instance (f : α → β) : is_add_monoid_hom (map f) :=
{ map_add := map_add _, map_zero := map_zero _ }

@[simp] theorem mem_map {f : α → β} {b : β} {s : multiset α} :
  b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b :=
quot.induction_on s $ λ l, mem_map

@[simp] theorem card_map (f : α → β) (s) : card (map f s) = card s :=
quot.induction_on s $ λ l, length_map _ _

@[simp] theorem map_eq_zero {s : multiset α} {f : α → β} : s.map f = 0 ↔ s = 0 :=
by rw [← multiset.card_eq_zero, multiset.card_map, multiset.card_eq_zero]

theorem mem_map_of_mem (f : α → β) {a : α} {s : multiset α} (h : a ∈ s) : f a ∈ map f s :=
mem_map.2 ⟨_, h, rfl⟩

theorem mem_map_of_inj {f : α → β} (H : function.injective f) {a : α} {s : multiset α} :
  f a ∈ map f s ↔ a ∈ s :=
quot.induction_on s $ λ l, mem_map_of_inj H

@[simp] theorem map_map (g : β → γ) (f : α → β) (s : multiset α) : map g (map f s) = map (g ∘ f) s :=
quot.induction_on s $ λ l, congr_arg coe $ list.map_map _ _ _

theorem map_id (s : multiset α) : map id s = s :=
quot.induction_on s $ λ l, congr_arg coe $ map_id _

@[simp] lemma map_id' (s : multiset α) : map (λx, x) s = s := map_id s

@[simp] theorem map_const (s : multiset α) (b : β) : map (function.const α b) s = repeat b s.card :=
quot.induction_on s $ λ l, congr_arg coe $ map_const _ _

@[congr] theorem map_congr {f g : α → β} {s : multiset α} : (∀ x ∈ s, f x = g x) → map f s = map g s :=
quot.induction_on s $ λ l H, congr_arg coe $ map_congr H

lemma map_hcongr {β' : Type*} {m : multiset α} {f : α → β} {f' : α → β'}
  (h : β = β') (hf : ∀a∈m, f a == f' a) : map f m == map f' m :=
begin subst h, simp at hf, simp [map_congr hf] end

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : list α} (h : b₁ ∈ map (function.const α b₂) l) : b₁ = b₂ :=
eq_of_mem_repeat $ by rwa map_const at h

@[simp] theorem map_le_map {f : α → β} {s t : multiset α} (h : s ≤ t) : map f s ≤ map f t :=
le_induction_on h $ λ l₁ l₂ h, (h.map f).subperm

@[simp] theorem map_subset_map {f : α → β} {s t : multiset α} (H : s ⊆ t) : map f s ⊆ map f t :=
λ b m, let ⟨a, h, e⟩ := mem_map.1 m in mem_map.2 ⟨a, H h, e⟩

/- fold -/

/-- `foldl f H b s` is the lift of the list operation `foldl f b l`,
  which folds `f` over the multiset. It is well defined when `f` is right-commutative,
  that is, `f (f b a₁) a₂ = f (f b a₂) a₁`. -/
def foldl (f : β → α → β) (H : right_commutative f) (b : β) (s : multiset α) : β :=
quot.lift_on s (λ l, foldl f b l)
  (λ l₁ l₂ p, p.foldl_eq H b)

@[simp] theorem foldl_zero (f : β → α → β) (H b) : foldl f H b 0 = b := rfl

@[simp] theorem foldl_cons (f : β → α → β) (H b a s) : foldl f H b (a :: s) = foldl f H (f b a) s :=
quot.induction_on s $ λ l, rfl

@[simp] theorem foldl_add (f : β → α → β) (H b s t) : foldl f H b (s + t) = foldl f H (foldl f H b s) t :=
quotient.induction_on₂ s t $ λ l₁ l₂, foldl_append _ _ _ _

/-- `foldr f H b s` is the lift of the list operation `foldr f b l`,
  which folds `f` over the multiset. It is well defined when `f` is left-commutative,
  that is, `f a₁ (f a₂ b) = f a₂ (f a₁ b)`. -/
def foldr (f : α → β → β) (H : left_commutative f) (b : β) (s : multiset α) : β :=
quot.lift_on s (λ l, foldr f b l)
  (λ l₁ l₂ p, p.foldr_eq H b)

@[simp] theorem foldr_zero (f : α → β → β) (H b) : foldr f H b 0 = b := rfl

@[simp] theorem foldr_cons (f : α → β → β) (H b a s) : foldr f H b (a :: s) = f a (foldr f H b s) :=
quot.induction_on s $ λ l, rfl

@[simp] theorem foldr_add (f : α → β → β) (H b s t) : foldr f H b (s + t) = foldr f H (foldr f H b t) s :=
quotient.induction_on₂ s t $ λ l₁ l₂, foldr_append _ _ _ _

@[simp] theorem coe_foldr (f : α → β → β) (H : left_commutative f) (b : β) (l : list α) :
  foldr f H b l = l.foldr f b := rfl

@[simp] theorem coe_foldl (f : β → α → β) (H : right_commutative f) (b : β) (l : list α) :
  foldl f H b l = l.foldl f b := rfl

theorem coe_foldr_swap (f : α → β → β) (H : left_commutative f) (b : β) (l : list α) :
  foldr f H b l = l.foldl (λ x y, f y x) b :=
(congr_arg (foldr f H b) (coe_reverse l)).symm.trans $ foldr_reverse _ _ _

theorem foldr_swap (f : α → β → β) (H : left_commutative f) (b : β) (s : multiset α) :
  foldr f H b s = foldl (λ x y, f y x) (λ x y z, (H _ _ _).symm) b s :=
quot.induction_on s $ λ l, coe_foldr_swap _ _ _ _

theorem foldl_swap (f : β → α → β) (H : right_commutative f) (b : β) (s : multiset α) :
  foldl f H b s = foldr (λ x y, f y x) (λ x y z, (H _ _ _).symm) b s :=
(foldr_swap _ _ _ _).symm

/-- Product of a multiset given a commutative monoid structure on `α`.
  `prod {a, b, c} = a * b * c` -/
@[to_additive]
def prod [comm_monoid α] : multiset α → α :=
foldr (*) (λ x y z, by simp [mul_left_comm]) 1

@[to_additive]
theorem prod_eq_foldr [comm_monoid α] (s : multiset α) :
  prod s = foldr (*) (λ x y z, by simp [mul_left_comm]) 1 s := rfl

@[to_additive]
theorem prod_eq_foldl [comm_monoid α] (s : multiset α) :
  prod s = foldl (*) (λ x y z, by simp [mul_right_comm]) 1 s :=
(foldr_swap _ _ _ _).trans (by simp [mul_comm])

@[simp, to_additive]
theorem coe_prod [comm_monoid α] (l : list α) : prod ↑l = l.prod :=
prod_eq_foldl _

@[simp, to_additive]
theorem prod_zero [comm_monoid α] : @prod α _ 0 = 1 := rfl

@[simp, to_additive]
theorem prod_cons [comm_monoid α] (a : α) (s) : prod (a :: s) = a * prod s :=
foldr_cons _ _ _ _ _

@[to_additive]
theorem prod_singleton [comm_monoid α] (a : α) : prod (a :: 0) = a := by simp

@[simp, to_additive]
theorem prod_add [comm_monoid α] (s t : multiset α) : prod (s + t) = prod s * prod t :=
quotient.induction_on₂ s t $ λ l₁ l₂, by simp

instance sum.is_add_monoid_hom [add_comm_monoid α] : is_add_monoid_hom (sum : multiset α → α) :=
{ map_add := sum_add, map_zero := sum_zero }

lemma prod_smul {α : Type*} [comm_monoid α] (m : multiset α) :
  ∀n, (n •ℕ m).prod = m.prod ^ n
| 0       := rfl
| (n + 1) :=
  by rw [add_nsmul, one_nsmul, _root_.pow_add, _root_.pow_one, prod_add, prod_smul n]

@[simp] theorem prod_repeat [comm_monoid α] (a : α) (n : ℕ) : prod (multiset.repeat a n) = a ^ n :=
by simp [repeat, list.prod_repeat]
@[simp] theorem sum_repeat [add_comm_monoid α] :
  ∀ (a : α) (n : ℕ), sum (multiset.repeat a n) = n •ℕ a :=
@prod_repeat (multiplicative α) _
attribute [to_additive] prod_repeat

lemma prod_map_one [comm_monoid γ] {m : multiset α} :
  prod (m.map (λa, (1 : γ))) = (1 : γ) :=
by simp
lemma sum_map_zero [add_comm_monoid γ] {m : multiset α} :
  sum (m.map (λa, (0 : γ))) = (0 : γ) :=
by simp
attribute [to_additive] prod_map_one

@[simp, to_additive]
lemma prod_map_mul [comm_monoid γ] {m : multiset α} {f g : α → γ} :
  prod (m.map $ λa, f a * g a) = prod (m.map f) * prod (m.map g) :=
multiset.induction_on m (by simp) (assume a m ih, by simp [ih]; cc)

lemma prod_map_prod_map [comm_monoid γ] (m : multiset α) (n : multiset β) {f : α → β → γ} :
  prod (m.map $ λa, prod $ n.map $ λb, f a b) = prod (n.map $ λb, prod $ m.map $ λa, f a b) :=
multiset.induction_on m (by simp) (assume a m ih, by simp [ih])

lemma sum_map_sum_map [add_comm_monoid γ] : ∀ (m : multiset α) (n : multiset β) {f : α → β → γ},
  sum (m.map $ λa, sum $ n.map $ λb, f a b) = sum (n.map $ λb, sum $ m.map $ λa, f a b) :=
@prod_map_prod_map _ _ (multiplicative γ) _
attribute [to_additive] prod_map_prod_map

lemma sum_map_mul_left [semiring β] {b : β} {s : multiset α} {f : α → β} :
  sum (s.map (λa, b * f a)) = b * sum (s.map f) :=
multiset.induction_on s (by simp) (assume a s ih, by simp [ih, mul_add])

lemma sum_map_mul_right [semiring β] {b : β} {s : multiset α} {f : α → β} :
  sum (s.map (λa, f a * b)) = sum (s.map f) * b :=
multiset.induction_on s (by simp) (assume a s ih, by simp [ih, add_mul])

@[to_additive]
lemma prod_hom [comm_monoid α] [comm_monoid β] (s : multiset α) (f : α → β) [is_monoid_hom f] :
  (s.map f).prod = f s.prod :=
quotient.induction_on s $ λ l, by simp only [l.prod_hom f, quot_mk_to_coe, coe_map, coe_prod]

@[to_additive]
theorem prod_hom_rel [comm_monoid β] [comm_monoid γ] (s : multiset α) {r : β → γ → Prop}
  {f : α → β} {g : α → γ} (h₁ : r 1 1) (h₂ : ∀⦃a b c⦄, r b c → r (f a * b) (g a * c)) :
  r (s.map f).prod (s.map g).prod :=
quotient.induction_on s $ λ l,
  by simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, coe_map, coe_prod]

lemma dvd_prod [comm_semiring α] {a : α} {s : multiset α} : a ∈ s → a ∣ s.prod :=
quotient.induction_on s (λ l a h, by simpa using list.dvd_prod h) a

lemma le_sum_of_subadditive [add_comm_monoid α] [ordered_add_comm_monoid β]
  (f : α → β) (h_zero : f 0 = 0) (h_add : ∀x y, f (x + y) ≤ f x + f y) (s : multiset α) :
  f s.sum ≤ (s.map f).sum :=
multiset.induction_on s (le_of_eq h_zero) $
  assume a s ih, by rw [sum_cons, map_cons, sum_cons];
    from le_trans (h_add a s.sum) (add_le_add_left' ih)

lemma abs_sum_le_sum_abs [discrete_linear_ordered_field α] {s : multiset α} :
  abs s.sum ≤ (s.map abs).sum :=
le_sum_of_subadditive _ abs_zero abs_add s

theorem dvd_sum [comm_semiring α] {a : α} {s : multiset α} : (∀ x ∈ s, a ∣ x) → a ∣ s.sum :=
multiset.induction_on s (λ _, dvd_zero _)
  (λ x s ih h, by rw sum_cons; exact dvd_add
    (h _ (mem_cons_self _ _)) (ih (λ y hy, h _ (mem_cons.2 (or.inr hy)))))

/- join -/

/-- `join S`, where `S` is a multiset of multisets, is the lift of the list join
  operation, that is, the union of all the sets.

     join {{1, 2}, {1, 2}, {0, 1}} = {0, 1, 1, 1, 2, 2} -/
def join : multiset (multiset α) → multiset α := sum

theorem coe_join : ∀ L : list (list α),
  join (L.map (@coe _ (multiset α) _) : multiset (multiset α)) = L.join
| []       := rfl
| (l :: L) := congr_arg (λ s : multiset α, ↑l + s) (coe_join L)

@[simp] theorem join_zero : @join α 0 = 0 := rfl

@[simp] theorem join_cons (s S) : @join α (s :: S) = s + join S :=
sum_cons _ _

@[simp] theorem join_add (S T) : @join α (S + T) = join S + join T :=
sum_add _ _

@[simp] theorem mem_join {a S} : a ∈ @join α S ↔ ∃ s ∈ S, a ∈ s :=
multiset.induction_on S (by simp) $
  by simp [or_and_distrib_right, exists_or_distrib] {contextual := tt}

@[simp] theorem card_join (S) : card (@join α S) = sum (map card S) :=
multiset.induction_on S (by simp) (by simp)

/- bind -/

/-- `bind s f` is the monad bind operation, defined as `join (map f s)`.
  It is the union of `f a` as `a` ranges over `s`. -/
def bind (s : multiset α) (f : α → multiset β) : multiset β :=
join (map f s)

@[simp] theorem coe_bind (l : list α) (f : α → list β) :
  @bind α β l (λ a, f a) = l.bind f :=
by rw [list.bind, ← coe_join, list.map_map]; refl

@[simp] theorem zero_bind (f : α → multiset β) : bind 0 f = 0 := rfl

@[simp] theorem cons_bind (a s) (f : α → multiset β) : bind (a::s) f = f a + bind s f :=
by simp [bind]

@[simp] theorem add_bind (s t) (f : α → multiset β) : bind (s + t) f = bind s f + bind t f :=
by simp [bind]

@[simp] theorem bind_zero (s : multiset α) : bind s (λa, 0 : α → multiset β) = 0 :=
by simp [bind, join]

@[simp] theorem bind_add (s : multiset α) (f g : α → multiset β) :
  bind s (λa, f a + g a) = bind s f + bind s g :=
by simp [bind, join]

@[simp] theorem bind_cons (s : multiset α) (f : α → β) (g : α → multiset β) :
  bind s (λa, f a :: g a) = map f s + bind s g :=
multiset.induction_on s (by simp) (by simp [add_comm, add_left_comm] {contextual := tt})

@[simp] theorem mem_bind {b s} {f : α → multiset β} : b ∈ bind s f ↔ ∃ a ∈ s, b ∈ f a :=
by simp [bind]; simp [-exists_and_distrib_right, exists_and_distrib_right.symm];
   rw exists_swap; simp [and_assoc]

@[simp] theorem card_bind (s) (f : α → multiset β) : card (bind s f) = sum (map (card ∘ f) s) :=
by simp [bind]

lemma bind_congr {f g : α → multiset β} {m : multiset α} : (∀a∈m, f a = g a) → bind m f = bind m g :=
by simp [bind] {contextual := tt}

lemma bind_hcongr {β' : Type*} {m : multiset α} {f : α → multiset β} {f' : α → multiset β'}
  (h : β = β') (hf : ∀a∈m, f a == f' a) : bind m f == bind m f' :=
begin subst h, simp at hf, simp [bind_congr hf] end

lemma map_bind (m : multiset α) (n : α → multiset β) (f : β → γ) :
  map f (bind m n) = bind m (λa, map f (n a)) :=
multiset.induction_on m (by simp) (by simp {contextual := tt})

lemma bind_map (m : multiset α) (n : β → multiset γ) (f : α → β) :
  bind (map f m) n = bind m (λa, n (f a)) :=
multiset.induction_on m (by simp) (by simp {contextual := tt})

lemma bind_assoc {s : multiset α} {f : α → multiset β} {g : β → multiset γ} :
  (s.bind f).bind g = s.bind (λa, (f a).bind g) :=
multiset.induction_on s (by simp) (by simp {contextual := tt})

lemma bind_bind (m : multiset α) (n : multiset β) {f : α → β → multiset γ} :
  (bind m $ λa, bind n $ λb, f a b) = (bind n $ λb, bind m $ λa, f a b) :=
multiset.induction_on m (by simp) (by simp {contextual := tt})

lemma bind_map_comm (m : multiset α) (n : multiset β) {f : α → β → γ} :
  (bind m $ λa, n.map $ λb, f a b) = (bind n $ λb, m.map $ λa, f a b) :=
multiset.induction_on m (by simp) (by simp {contextual := tt})

@[simp, to_additive]
lemma prod_bind [comm_monoid β] (s : multiset α) (t : α → multiset β) :
  prod (bind s t) = prod (s.map $ λa, prod (t a)) :=
multiset.induction_on s (by simp) (assume a s ih, by simp [ih, cons_bind])

/- product -/

/-- The multiplicity of `(a, b)` in `product s t` is
  the product of the multiplicity of `a` in `s` and `b` in `t`. -/
def product (s : multiset α) (t : multiset β) : multiset (α × β) :=
s.bind $ λ a, t.map $ prod.mk a

@[simp] theorem coe_product (l₁ : list α) (l₂ : list β) :
  @product α β l₁ l₂ = l₁.product l₂ :=
by rw [product, list.product, ← coe_bind]; simp

@[simp] theorem zero_product (t) : @product α β 0 t = 0 := rfl

@[simp] theorem cons_product (a : α) (s : multiset α) (t : multiset β) :
  product (a :: s) t = map (prod.mk a) t + product s t :=
by simp [product]

@[simp] theorem product_singleton (a : α) (b : β) : product (a::0) (b::0) = (a,b)::0 := rfl

@[simp] theorem add_product (s t : multiset α) (u : multiset β) :
  product (s + t) u = product s u + product t u :=
by simp [product]

@[simp] theorem product_add (s : multiset α) : ∀ t u : multiset β,
  product s (t + u) = product s t + product s u :=
multiset.induction_on s (λ t u, rfl) $ λ a s IH t u,
  by rw [cons_product, IH]; simp; cc

@[simp] theorem mem_product {s t} : ∀ {p : α × β}, p ∈ @product α β s t ↔ p.1 ∈ s ∧ p.2 ∈ t
| (a, b) := by simp [product, and.left_comm]

@[simp] theorem card_product (s : multiset α) (t : multiset β) : card (product s t) = card s * card t :=
by simp [product, repeat, (∘), mul_comm]

/- sigma -/
section
variable {σ : α → Type*}

/-- `sigma s t` is the dependent version of `product`. It is the sum of
  `(a, b)` as `a` ranges over `s` and `b` ranges over `t a`. -/
protected def sigma (s : multiset α) (t : Π a, multiset (σ a)) : multiset (Σ a, σ a) :=
s.bind $ λ a, (t a).map $ sigma.mk a

@[simp] theorem coe_sigma (l₁ : list α) (l₂ : Π a, list (σ a)) :
  @multiset.sigma α σ l₁ (λ a, l₂ a) = l₁.sigma l₂ :=
by rw [multiset.sigma, list.sigma, ← coe_bind]; simp

@[simp] theorem zero_sigma (t) : @multiset.sigma α σ 0 t = 0 := rfl

@[simp] theorem cons_sigma (a : α) (s : multiset α) (t : Π a, multiset (σ a)) :
  (a :: s).sigma t = map (sigma.mk a) (t a) + s.sigma t :=
by simp [multiset.sigma]

@[simp] theorem sigma_singleton (a : α) (b : α → β) :
  (a::0).sigma (λ a, b a::0) = ⟨a, b a⟩::0 := rfl

@[simp] theorem add_sigma (s t : multiset α) (u : Π a, multiset (σ a)) :
  (s + t).sigma u = s.sigma u + t.sigma u :=
by simp [multiset.sigma]

@[simp] theorem sigma_add (s : multiset α) : ∀ t u : Π a, multiset (σ a),
  s.sigma (λ a, t a + u a) = s.sigma t + s.sigma u :=
multiset.induction_on s (λ t u, rfl) $ λ a s IH t u,
  by rw [cons_sigma, IH]; simp; cc

@[simp] theorem mem_sigma {s t} : ∀ {p : Σ a, σ a},
  p ∈ @multiset.sigma α σ s t ↔ p.1 ∈ s ∧ p.2 ∈ t p.1
| ⟨a, b⟩ := by simp [multiset.sigma, and_assoc, and.left_comm]

@[simp] theorem card_sigma (s : multiset α) (t : Π a, multiset (σ a)) :
  card (s.sigma t) = sum (map (λ a, card (t a)) s) :=
by simp [multiset.sigma, (∘)]

end

/- map for partial functions -/

/-- Lift of the list `pmap` operation. Map a partial function `f` over a multiset
  `s` whose elements are all in the domain of `f`. -/
def pmap {p : α → Prop} (f : Π a, p a → β) (s : multiset α) : (∀ a ∈ s, p a) → multiset β :=
quot.rec_on s (λ l H, ↑(pmap f l H)) $ λ l₁ l₂ (pp : l₁ ~ l₂),
funext $ λ (H₂ : ∀ a ∈ l₂, p a),
have H₁ : ∀ a ∈ l₁, p a, from λ a h, H₂ a (pp.subset h),
have ∀ {s₂ e H}, @eq.rec (multiset α) l₁
  (λ s, (∀ a ∈ s, p a) → multiset β) (λ _, ↑(pmap f l₁ H₁))
  s₂ e H = ↑(pmap f l₁ H₁), by intros s₂ e _; subst e,
this.trans $ quot.sound $ pp.pmap f

@[simp] theorem coe_pmap {p : α → Prop} (f : Π a, p a → β)
  (l : list α) (H : ∀ a ∈ l, p a) : pmap f l H = l.pmap f H := rfl

@[simp] lemma pmap_zero {p : α → Prop} (f : Π a, p a → β) (h : ∀a∈(0:multiset α), p a) :
  pmap f 0 h = 0 := rfl

@[simp] lemma pmap_cons {p : α → Prop} (f : Π a, p a → β) (a : α) (m : multiset α) :
  ∀(h : ∀b∈a::m, p b), pmap f (a :: m) h =
    f a (h a (mem_cons_self a m)) :: pmap f m (λa ha, h a $ mem_cons_of_mem ha) :=
quotient.induction_on m $ assume l h, rfl

/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
  a multiset on `{x // x ∈ s}`. -/
def attach (s : multiset α) : multiset {x // x ∈ s} := pmap subtype.mk s (λ a, id)

@[simp] theorem coe_attach (l : list α) :
 @eq (multiset {x // x ∈ l}) (@attach α l) l.attach := rfl

theorem pmap_eq_map (p : α → Prop) (f : α → β) (s : multiset α) :
  ∀ H, @pmap _ _ p (λ a _, f a) s H = map f s :=
quot.induction_on s $ λ l H, congr_arg coe $ pmap_eq_map p f l H

theorem pmap_congr {p q : α → Prop} {f : Π a, p a → β} {g : Π a, q a → β}
  (s : multiset α) {H₁ H₂} (h : ∀ a h₁ h₂, f a h₁ = g a h₂) :
  pmap f s H₁ = pmap g s H₂ :=
quot.induction_on s (λ l H₁ H₂, congr_arg coe $ pmap_congr l h) H₁ H₂

theorem map_pmap {p : α → Prop} (g : β → γ) (f : Π a, p a → β)
  (s) : ∀ H, map g (pmap f s H) = pmap (λ a h, g (f a h)) s H :=
quot.induction_on s $ λ l H, congr_arg coe $ map_pmap g f l H

theorem pmap_eq_map_attach {p : α → Prop} (f : Π a, p a → β)
  (s) : ∀ H, pmap f s H = s.attach.map (λ x, f x.1 (H _ x.2)) :=
quot.induction_on s $ λ l H, congr_arg coe $ pmap_eq_map_attach f l H

theorem attach_map_val (s : multiset α) : s.attach.map subtype.val = s :=
quot.induction_on s $ λ l, congr_arg coe $ attach_map_val l

@[simp] theorem mem_attach (s : multiset α) : ∀ x, x ∈ s.attach :=
quot.induction_on s $ λ l, mem_attach _

@[simp] theorem mem_pmap {p : α → Prop} {f : Π a, p a → β}
  {s H b} : b ∈ pmap f s H ↔ ∃ a (h : a ∈ s), f a (H a h) = b :=
quot.induction_on s (λ l H, mem_pmap) H

@[simp] theorem card_pmap {p : α → Prop} (f : Π a, p a → β)
  (s H) : card (pmap f s H) = card s :=
quot.induction_on s (λ l H, length_pmap) H

@[simp] theorem card_attach {m : multiset α} : card (attach m) = card m := card_pmap _ _ _

@[simp] lemma attach_zero : (0 : multiset α).attach = 0 := rfl

lemma attach_cons (a : α) (m : multiset α) :
  (a :: m).attach = ⟨a, mem_cons_self a m⟩ :: (m.attach.map $ λp, ⟨p.1, mem_cons_of_mem p.2⟩) :=
quotient.induction_on m $ assume l, congr_arg coe $ congr_arg (list.cons _) $
  by rw [list.map_pmap]; exact list.pmap_congr _ (assume a' h₁ h₂, subtype.eq rfl)

section decidable_pi_exists
variables {m : multiset α}

protected def decidable_forall_multiset {p : α → Prop} [hp : ∀a, decidable (p a)] :
  decidable (∀a∈m, p a) :=
quotient.rec_on_subsingleton m (λl, decidable_of_iff (∀a∈l, p a) $ by simp)

instance decidable_dforall_multiset {p : Πa∈m, Prop} [hp : ∀a (h : a ∈ m), decidable (p a h)] :
  decidable (∀a (h : a ∈ m), p a h) :=
decidable_of_decidable_of_iff
  (@multiset.decidable_forall_multiset {a // a ∈ m} m.attach (λa, p a.1 a.2) _)
  (iff.intro (assume h a ha, h ⟨a, ha⟩ (mem_attach _ _)) (assume h ⟨a, ha⟩ _, h _ _))

/-- decidable equality for functions whose domain is bounded by multisets -/
instance decidable_eq_pi_multiset {β : α → Type*} [h : ∀a, decidable_eq (β a)] :
  decidable_eq (Πa∈m, β a) :=
assume f g, decidable_of_iff (∀a (h : a ∈ m), f a h = g a h) (by simp [function.funext_iff])

def decidable_exists_multiset {p : α → Prop} [decidable_pred p] :
  decidable (∃ x ∈ m, p x) :=
quotient.rec_on_subsingleton m list.decidable_exists_mem

instance decidable_dexists_multiset {p : Πa∈m, Prop} [hp : ∀a (h : a ∈ m), decidable (p a h)] :
  decidable (∃a (h : a ∈ m), p a h) :=
decidable_of_decidable_of_iff
  (@multiset.decidable_exists_multiset {a // a ∈ m} m.attach (λa, p a.1 a.2) _)
  (iff.intro (λ ⟨⟨a, ha₁⟩, _, ha₂⟩, ⟨a, ha₁, ha₂⟩)
    (λ ⟨a, ha₁, ha₂⟩, ⟨⟨a, ha₁⟩, mem_attach _ _, ha₂⟩))

end decidable_pi_exists

/- subtraction -/
section
variables [decidable_eq α] {s t u : multiset α} {a b : α}

/-- `s - t` is the multiset such that
  `count a (s - t) = count a s - count a t` for all `a`. -/
protected def sub (s t : multiset α) : multiset α :=
quotient.lift_on₂ s t (λ l₁ l₂, (l₁.diff l₂ : multiset α)) $ λ v₁ v₂ w₁ w₂ p₁ p₂,
  quot.sound $ p₁.diff p₂

instance : has_sub (multiset α) := ⟨multiset.sub⟩

@[simp] theorem coe_sub (s t : list α) : (s - t : multiset α) = (s.diff t : list α) := rfl

theorem sub_eq_fold_erase (s t : multiset α) : s - t = foldl erase erase_comm s t :=
quotient.induction_on₂ s t $ λ l₁ l₂,
show ↑(l₁.diff l₂) = foldl erase erase_comm ↑l₁ ↑l₂,
by { rw diff_eq_foldl l₁ l₂, symmetry, exact foldl_hom _ _ _ _ _ (λ x y, rfl) }

@[simp] theorem sub_zero (s : multiset α) : s - 0 = s :=
quot.induction_on s $ λ l, rfl

@[simp] theorem sub_cons (a : α) (s t : multiset α) : s - a::t = s.erase a - t :=
quotient.induction_on₂ s t $ λ l₁ l₂, congr_arg coe $ diff_cons _ _ _

theorem add_sub_of_le (h : s ≤ t) : s + (t - s) = t :=
begin
  revert t,
  refine multiset.induction_on s (by simp) (λ a s IH t h, _),
  have := cons_erase (mem_of_le h (mem_cons_self _ _)),
  rw [cons_add, sub_cons, IH, this],
  exact (cons_le_cons_iff a).1 (this.symm ▸ h)
end

theorem sub_add' : s - (t + u) = s - t - u :=
quotient.induction_on₃ s t u $
λ l₁ l₂ l₃, congr_arg coe $ diff_append _ _ _

theorem sub_add_cancel (h : t ≤ s) : s - t + t = s :=
by rw [add_comm, add_sub_of_le h]

@[simp] theorem add_sub_cancel_left (s : multiset α) : ∀ t, s + t - s = t :=
multiset.induction_on s (by simp)
  (λ a s IH t, by rw [cons_add, sub_cons, erase_cons_head, IH])

@[simp] theorem add_sub_cancel (s t : multiset α) : s + t - t = s :=
by rw [add_comm, add_sub_cancel_left]

theorem sub_le_sub_right (h : s ≤ t) (u) : s - u ≤ t - u :=
by revert s t h; exact
multiset.induction_on u (by simp {contextual := tt})
  (λ a u IH s t h, by simp [IH, erase_le_erase a h])

theorem sub_le_sub_left (h : s ≤ t) : ∀ u, u - t ≤ u - s :=
le_induction_on h $ λ l₁ l₂ h, begin
  induction h with l₁ l₂ a s IH l₁ l₂ a s IH; intro u,
  { refl },
  { rw [← cons_coe, sub_cons],
    exact le_trans (sub_le_sub_right (erase_le _ _) _) (IH u) },
  { rw [← cons_coe, sub_cons, ← cons_coe, sub_cons],
    exact IH _ }
end

theorem sub_le_iff_le_add : s - t ≤ u ↔ s ≤ u + t :=
by revert s; exact
multiset.induction_on t (by simp)
  (λ a t IH s, by simp [IH, erase_le_iff_le_cons])

theorem le_sub_add (s t : multiset α) : s ≤ s - t + t :=
sub_le_iff_le_add.1 (le_refl _)

theorem sub_le_self (s t : multiset α) : s - t ≤ s :=
sub_le_iff_le_add.2 (le_add_right _ _)

@[simp] theorem card_sub {s t : multiset α} (h : t ≤ s) : card (s - t) = card s - card t :=
(nat.sub_eq_of_eq_add $ by rw [add_comm, ← card_add, sub_add_cancel h]).symm

/- union -/

/-- `s ∪ t` is the lattice join operation with respect to the
  multiset `≤`. The multiplicity of `a` in `s ∪ t` is the maximum
  of the multiplicities in `s` and `t`. -/
def union (s t : multiset α) : multiset α := s - t + t

instance : has_union (multiset α) := ⟨union⟩

theorem union_def (s t : multiset α) : s ∪ t = s - t + t := rfl

theorem le_union_left (s t : multiset α) : s ≤ s ∪ t := le_sub_add _ _

theorem le_union_right (s t : multiset α) : t ≤ s ∪ t := le_add_left _ _

theorem eq_union_left : t ≤ s → s ∪ t = s := sub_add_cancel

theorem union_le_union_right (h : s ≤ t) (u) : s ∪ u ≤ t ∪ u :=
add_le_add_right (sub_le_sub_right h _) u

theorem union_le (h₁ : s ≤ u) (h₂ : t ≤ u) : s ∪ t ≤ u :=
by rw ← eq_union_left h₂; exact union_le_union_right h₁ t

@[simp] theorem mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
⟨λ h, (mem_add.1 h).imp_left (mem_of_le $ sub_le_self _ _),
 or.rec (mem_of_le $ le_union_left _ _) (mem_of_le $ le_union_right _ _)⟩

@[simp] theorem map_union [decidable_eq β] {f : α → β} (finj : function.injective f) {s t : multiset α} :
  map f (s ∪ t) = map f s ∪ map f t :=
quotient.induction_on₂ s t $ λ l₁ l₂,
congr_arg coe (by rw [list.map_append f, list.map_diff finj])

/- inter -/

/-- `s ∩ t` is the lattice meet operation with respect to the
  multiset `≤`. The multiplicity of `a` in `s ∩ t` is the minimum
  of the multiplicities in `s` and `t`. -/
def inter (s t : multiset α) : multiset α :=
quotient.lift_on₂ s t (λ l₁ l₂, (l₁.bag_inter l₂ : multiset α)) $ λ v₁ v₂ w₁ w₂ p₁ p₂,
  quot.sound $ p₁.bag_inter p₂

instance : has_inter (multiset α) := ⟨inter⟩

@[simp] theorem inter_zero (s : multiset α) : s ∩ 0 = 0 :=
quot.induction_on s $ λ l, congr_arg coe l.bag_inter_nil

@[simp] theorem zero_inter (s : multiset α) : 0 ∩ s = 0 :=
quot.induction_on s $ λ l, congr_arg coe l.nil_bag_inter

@[simp] theorem cons_inter_of_pos {a} (s : multiset α) {t} :
  a ∈ t → (a :: s) ∩ t = a :: s ∩ t.erase a :=
quotient.induction_on₂ s t $ λ l₁ l₂ h,
congr_arg coe $ cons_bag_inter_of_pos _ h

@[simp] theorem cons_inter_of_neg {a} (s : multiset α) {t} :
  a ∉ t → (a :: s) ∩ t = s ∩ t :=
quotient.induction_on₂ s t $ λ l₁ l₂ h,
congr_arg coe $ cons_bag_inter_of_neg _ h

theorem inter_le_left (s t : multiset α) : s ∩ t ≤ s :=
quotient.induction_on₂ s t $ λ l₁ l₂,
(bag_inter_sublist_left _ _).subperm

theorem inter_le_right (s : multiset α) : ∀ t, s ∩ t ≤ t :=
multiset.induction_on s (λ t, (zero_inter t).symm ▸ zero_le _) $
λ a s IH t, if h : a ∈ t
  then by simpa [h] using cons_le_cons a (IH (t.erase a))
  else by simp [h, IH]

theorem le_inter (h₁ : s ≤ t) (h₂ : s ≤ u) : s ≤ t ∩ u :=
begin
  revert s u, refine multiset.induction_on t _ (λ a t IH, _); intros,
  { simp [h₁] },
  by_cases a ∈ u,
  { rw [cons_inter_of_pos _ h, ← erase_le_iff_le_cons],
    exact IH (erase_le_iff_le_cons.2 h₁) (erase_le_erase _ h₂) },
  { rw cons_inter_of_neg _ h,
    exact IH ((le_cons_of_not_mem $ mt (mem_of_le h₂) h).1 h₁) h₂ }
end

@[simp] theorem mem_inter : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t :=
⟨λ h, ⟨mem_of_le (inter_le_left _ _) h, mem_of_le (inter_le_right _ _) h⟩,
 λ ⟨h₁, h₂⟩, by rw [← cons_erase h₁, cons_inter_of_pos _ h₂]; apply mem_cons_self⟩

instance : lattice (multiset α) :=
{ sup          := (∪),
  sup_le       := @union_le _ _,
  le_sup_left  := le_union_left,
  le_sup_right := le_union_right,
  inf          := (∩),
  le_inf       := @le_inter _ _,
  inf_le_left  := inter_le_left,
  inf_le_right := inter_le_right,
  ..@multiset.partial_order α }

@[simp] theorem sup_eq_union (s t : multiset α) : s ⊔ t = s ∪ t := rfl
@[simp] theorem inf_eq_inter (s t : multiset α) : s ⊓ t = s ∩ t := rfl

@[simp] theorem le_inter_iff : s ≤ t ∩ u ↔ s ≤ t ∧ s ≤ u := le_inf_iff
@[simp] theorem union_le_iff : s ∪ t ≤ u ↔ s ≤ u ∧ t ≤ u := sup_le_iff

instance : semilattice_inf_bot (multiset α) :=
{ bot := 0, bot_le := zero_le, ..multiset.lattice }

theorem union_comm (s t : multiset α) : s ∪ t = t ∪ s := sup_comm
theorem inter_comm (s t : multiset α) : s ∩ t = t ∩ s := inf_comm

theorem eq_union_right (h : s ≤ t) : s ∪ t = t :=
by rw [union_comm, eq_union_left h]

theorem union_le_union_left (h : s ≤ t) (u) : u ∪ s ≤ u ∪ t :=
sup_le_sup_left h _

theorem union_le_add (s t : multiset α) : s ∪ t ≤ s + t :=
union_le (le_add_right _ _) (le_add_left _ _)

theorem union_add_distrib (s t u : multiset α) : (s ∪ t) + u = (s + u) ∪ (t + u) :=
by simpa [(∪), union, eq_comm, add_assoc] using show s + u - (t + u) = s - t,
by rw [add_comm t, sub_add', add_sub_cancel]

theorem add_union_distrib (s t u : multiset α) : s + (t ∪ u) = (s + t) ∪ (s + u) :=
by rw [add_comm, union_add_distrib, add_comm s, add_comm s]

theorem cons_union_distrib (a : α) (s t : multiset α) : a :: (s ∪ t) = (a :: s) ∪ (a :: t) :=
by simpa using add_union_distrib (a::0) s t

theorem inter_add_distrib (s t u : multiset α) : (s ∩ t) + u = (s + u) ∩ (t + u) :=
begin
  by_contra h,
  cases lt_iff_cons_le.1 (lt_of_le_of_ne (le_inter
    (add_le_add_right (inter_le_left s t) u)
    (add_le_add_right (inter_le_right s t) u)) h) with a hl,
  rw ← cons_add at hl,
  exact not_le_of_lt (lt_cons_self (s ∩ t) a) (le_inter
    (le_of_add_le_add_right (le_trans hl (inter_le_left _ _)))
    (le_of_add_le_add_right (le_trans hl (inter_le_right _ _))))
end

theorem add_inter_distrib (s t u : multiset α) : s + (t ∩ u) = (s + t) ∩ (s + u) :=
by rw [add_comm, inter_add_distrib, add_comm s, add_comm s]

theorem cons_inter_distrib (a : α) (s t : multiset α) : a :: (s ∩ t) = (a :: s) ∩ (a :: t) :=
by simp

theorem union_add_inter (s t : multiset α) : s ∪ t + s ∩ t = s + t :=
begin
  apply le_antisymm,
  { rw union_add_distrib,
    refine union_le (add_le_add_left (inter_le_right _ _) _) _,
    rw add_comm, exact add_le_add_right (inter_le_left _ _) _ },
  { rw [add_comm, add_inter_distrib],
    refine le_inter (add_le_add_right (le_union_right _ _) _) _,
    rw add_comm, exact add_le_add_right (le_union_left _ _) _ }
end

theorem sub_add_inter (s t : multiset α) : s - t + s ∩ t = s :=
begin
  rw [inter_comm],
  revert s, refine multiset.induction_on t (by simp) (λ a t IH s, _),
  by_cases a ∈ s,
  { rw [cons_inter_of_pos _ h, sub_cons, add_cons, IH, cons_erase h] },
  { rw [cons_inter_of_neg _ h, sub_cons, erase_of_not_mem h, IH] }
end

theorem sub_inter (s t : multiset α) : s - (s ∩ t) = s - t :=
add_right_cancel $
by rw [sub_add_inter s t, sub_add_cancel (inter_le_left _ _)]

end


/- filter -/
section
variables {p : α → Prop} [decidable_pred p]

/-- `filter p s` returns the elements in `s` (with the same multiplicities)
  which satisfy `p`, and removes the rest. -/
def filter (p : α → Prop) [h : decidable_pred p] (s : multiset α) : multiset α :=
quot.lift_on s (λ l, (filter p l : multiset α))
  (λ l₁ l₂ h, quot.sound $ h.filter p)

@[simp] theorem coe_filter (p : α → Prop) [h : decidable_pred p]
  (l : list α) : filter p (↑l) = l.filter p := rfl

@[simp] theorem filter_zero (p : α → Prop) [h : decidable_pred p] : filter p 0 = 0 := rfl

@[simp] theorem filter_cons_of_pos {a : α} (s) : p a → filter p (a::s) = a :: filter p s :=
quot.induction_on s $ λ l h, congr_arg coe $ filter_cons_of_pos l h

@[simp] theorem filter_cons_of_neg {a : α} (s) : ¬ p a → filter p (a::s) = filter p s :=
quot.induction_on s $ λ l h, @congr_arg _ _ _ _ coe $ filter_cons_of_neg l h

lemma filter_congr {p q : α → Prop} [decidable_pred p] [decidable_pred q]
  {s : multiset α} : (∀ x ∈ s, p x ↔ q x) → filter p s = filter q s :=
quot.induction_on s $ λ l h, congr_arg coe $ filter_congr h

@[simp] theorem filter_add (s t : multiset α) :
  filter p (s + t) = filter p s + filter p t :=
quotient.induction_on₂ s t $ λ l₁ l₂, congr_arg coe $ filter_append _ _

@[simp] theorem filter_le (s : multiset α) : filter p s ≤ s :=
quot.induction_on s $ λ l, (filter_sublist _).subperm

@[simp] theorem filter_subset (s : multiset α) : filter p s ⊆ s :=
subset_of_le $ filter_le _

@[simp] theorem mem_filter {a : α} {s} : a ∈ filter p s ↔ a ∈ s ∧ p a :=
quot.induction_on s $ λ l, mem_filter

theorem of_mem_filter {a : α} {s} (h : a ∈ filter p s) : p a :=
(mem_filter.1 h).2

theorem mem_of_mem_filter {a : α} {s} (h : a ∈ filter p s) : a ∈ s :=
(mem_filter.1 h).1

theorem mem_filter_of_mem {a : α} {l} (m : a ∈ l) (h : p a) : a ∈ filter p l :=
mem_filter.2 ⟨m, h⟩

theorem filter_eq_self {s} : filter p s = s ↔ ∀ a ∈ s, p a :=
quot.induction_on s $ λ l, iff.trans ⟨λ h,
  eq_of_sublist_of_length_eq (filter_sublist _) (@congr_arg _ _ _ _ card h),
  congr_arg coe⟩ filter_eq_self

theorem filter_eq_nil {s} : filter p s = 0 ↔ ∀ a ∈ s, ¬p a :=
quot.induction_on s $ λ l, iff.trans ⟨λ h,
  eq_nil_of_length_eq_zero (@congr_arg _ _ _ _ card h),
  congr_arg coe⟩ filter_eq_nil

theorem filter_le_filter {s t} (h : s ≤ t) : filter p s ≤ filter p t :=
le_induction_on h $ λ l₁ l₂ h, (filter_sublist_filter h).subperm

theorem le_filter {s t} : s ≤ filter p t ↔ s ≤ t ∧ ∀ a ∈ s, p a :=
⟨λ h, ⟨le_trans h (filter_le _), λ a m, of_mem_filter (mem_of_le h m)⟩,
 λ ⟨h, al⟩, filter_eq_self.2 al ▸ filter_le_filter h⟩

@[simp] theorem filter_sub [decidable_eq α] (s t : multiset α) :
  filter p (s - t) = filter p s - filter p t :=
begin
  revert s, refine multiset.induction_on t (by simp) (λ a t IH s, _),
  rw [sub_cons, IH],
  by_cases p a,
  { rw [filter_cons_of_pos _ h, sub_cons], congr,
    by_cases m : a ∈ s,
    { rw [← cons_inj_right a, ← filter_cons_of_pos _ h,
          cons_erase (mem_filter_of_mem m h), cons_erase m] },
    { rw [erase_of_not_mem m, erase_of_not_mem (mt mem_of_mem_filter m)] } },
  { rw [filter_cons_of_neg _ h],
    by_cases m : a ∈ s,
    { rw [(by rw filter_cons_of_neg _ h : filter p (erase s a) = filter p (a :: erase s a)),
          cons_erase m] },
    { rw [erase_of_not_mem m] } }
end

@[simp] theorem filter_union [decidable_eq α] (s t : multiset α) :
  filter p (s ∪ t) = filter p s ∪ filter p t :=
by simp [(∪), union]

@[simp] theorem filter_inter [decidable_eq α] (s t : multiset α) :
  filter p (s ∩ t) = filter p s ∩ filter p t :=
le_antisymm (le_inter
    (filter_le_filter $ inter_le_left _ _)
    (filter_le_filter $ inter_le_right _ _)) $ le_filter.2
⟨inf_le_inf (filter_le _) (filter_le _),
  λ a h, of_mem_filter (mem_of_le (inter_le_left _ _) h)⟩

@[simp] theorem filter_filter {q} [decidable_pred q] (s : multiset α) :
  filter p (filter q s) = filter (λ a, p a ∧ q a) s :=
quot.induction_on s $ λ l, congr_arg coe $ filter_filter l

theorem filter_add_filter {q} [decidable_pred q] (s : multiset α) :
  filter p s + filter q s = filter (λ a, p a ∨ q a) s + filter (λ a, p a ∧ q a) s :=
multiset.induction_on s rfl $ λ a s IH,
by by_cases p a; by_cases q a; simp *

theorem filter_add_not (s : multiset α) :
  filter p s + filter (λ a, ¬ p a) s = s :=
by rw [filter_add_filter, filter_eq_self.2, filter_eq_nil.2]; simp [decidable.em]

/- filter_map -/

/-- `filter_map f s` is a combination filter/map operation on `s`.
  The function `f : α → option β` is applied to each element of `s`;
  if `f a` is `some b` then `b` is added to the result, otherwise
  `a` is removed from the resulting multiset. -/
def filter_map (f : α → option β) (s : multiset α) : multiset β :=
quot.lift_on s (λ l, (filter_map f l : multiset β))
  (λ l₁ l₂ h, quot.sound $ h.filter_map f)

@[simp] theorem coe_filter_map (f : α → option β) (l : list α) :
  filter_map f l = l.filter_map f := rfl

@[simp] theorem filter_map_zero (f : α → option β) : filter_map f 0 = 0 := rfl

@[simp] theorem filter_map_cons_none {f : α → option β} (a : α) (s : multiset α) (h : f a = none) :
  filter_map f (a :: s) = filter_map f s :=
quot.induction_on s $ λ l, @congr_arg _ _ _ _ coe $ filter_map_cons_none a l h

@[simp] theorem filter_map_cons_some (f : α → option β)
  (a : α) (s : multiset α) {b : β} (h : f a = some b) :
  filter_map f (a :: s) = b :: filter_map f s :=
quot.induction_on s $ λ l, @congr_arg _ _ _ _ coe $ filter_map_cons_some f a l h

theorem filter_map_eq_map (f : α → β) : filter_map (some ∘ f) = map f :=
funext $ λ s, quot.induction_on s $ λ l,
@congr_arg _ _ _ _ coe $ congr_fun (filter_map_eq_map f) l

theorem filter_map_eq_filter (p : α → Prop) [decidable_pred p] :
  filter_map (option.guard p) = filter p :=
funext $ λ s, quot.induction_on s $ λ l,
@congr_arg _ _ _ _ coe $ congr_fun (filter_map_eq_filter p) l

theorem filter_map_filter_map (f : α → option β) (g : β → option γ) (s : multiset α) :
  filter_map g (filter_map f s) = filter_map (λ x, (f x).bind g) s :=
quot.induction_on s $ λ l, congr_arg coe $ filter_map_filter_map f g l

theorem map_filter_map (f : α → option β) (g : β → γ) (s : multiset α) :
  map g (filter_map f s) = filter_map (λ x, (f x).map g) s :=
quot.induction_on s $ λ l, congr_arg coe $ map_filter_map f g l

theorem filter_map_map (f : α → β) (g : β → option γ) (s : multiset α) :
  filter_map g (map f s) = filter_map (g ∘ f) s :=
quot.induction_on s $ λ l, congr_arg coe $ filter_map_map f g l

theorem filter_filter_map (f : α → option β) (p : β → Prop) [decidable_pred p] (s : multiset α) :
  filter p (filter_map f s) = filter_map (λ x, (f x).filter p) s :=
quot.induction_on s $ λ l, congr_arg coe $ filter_filter_map f p l

theorem filter_map_filter (p : α → Prop) [decidable_pred p] (f : α → option β) (s : multiset α) :
  filter_map f (filter p s) = filter_map (λ x, if p x then f x else none) s :=
quot.induction_on s $ λ l, congr_arg coe $ filter_map_filter p f l

@[simp] theorem filter_map_some (s : multiset α) : filter_map some s = s :=
quot.induction_on s $ λ l, congr_arg coe $ filter_map_some l

@[simp] theorem mem_filter_map (f : α → option β) (s : multiset α) {b : β} :
  b ∈ filter_map f s ↔ ∃ a, a ∈ s ∧ f a = some b :=
quot.induction_on s $ λ l, mem_filter_map f l

theorem map_filter_map_of_inv (f : α → option β) (g : β → α)
  (H : ∀ x : α, (f x).map g = some x) (s : multiset α) :
  map g (filter_map f s) = s :=
quot.induction_on s $ λ l, congr_arg coe $ map_filter_map_of_inv f g H l

theorem filter_map_le_filter_map (f : α → option β) {s t : multiset α}
  (h : s ≤ t) : filter_map f s ≤ filter_map f t :=
le_induction_on h $ λ l₁ l₂ h, (h.filter_map _).subperm

/- powerset -/

def powerset_aux (l : list α) : list (multiset α) :=
0 :: sublists_aux l (λ x y, x :: y)

theorem powerset_aux_eq_map_coe {l : list α} :
  powerset_aux l = (sublists l).map coe :=
by simp [powerset_aux, sublists];
   rw [← show @sublists_aux₁ α (multiset α) l (λ x, [↑x]) =
              sublists_aux l (λ x, list.cons ↑x),
         from sublists_aux₁_eq_sublists_aux _ _,
       sublists_aux_cons_eq_sublists_aux₁,
       ← bind_ret_eq_map, sublists_aux₁_bind]; refl

@[simp] theorem mem_powerset_aux {l : list α} {s} :
  s ∈ powerset_aux l ↔ s ≤ ↑l :=
quotient.induction_on s $
by simp [powerset_aux_eq_map_coe, subperm, and.comm]

def powerset_aux' (l : list α) : list (multiset α) := (sublists' l).map coe

theorem powerset_aux_perm_powerset_aux' {l : list α} :
  powerset_aux l ~ powerset_aux' l :=
by rw powerset_aux_eq_map_coe; exact (sublists_perm_sublists' _).map _

@[simp] theorem powerset_aux'_nil : powerset_aux' (@nil α) = [0] := rfl

@[simp] theorem powerset_aux'_cons (a : α) (l : list α) :
  powerset_aux' (a::l) = powerset_aux' l ++ list.map (cons a) (powerset_aux' l) :=
by simp [powerset_aux']; refl

theorem powerset_aux'_perm {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  powerset_aux' l₁ ~ powerset_aux' l₂ :=
begin
  induction p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂, {simp},
  { simp, exact IH.append (IH.map _) },
  { simp, apply perm.append_left,
    rw [← append_assoc, ← append_assoc,
        (by funext s; simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)],
    exact perm_append_comm.append_right _ },
  { exact IH₁.trans IH₂ }
end

theorem powerset_aux_perm {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  powerset_aux l₁ ~ powerset_aux l₂ :=
powerset_aux_perm_powerset_aux'.trans $
(powerset_aux'_perm p).trans powerset_aux_perm_powerset_aux'.symm

def powerset (s : multiset α) : multiset (multiset α) :=
quot.lift_on s
  (λ l, (powerset_aux l : multiset (multiset α)))
  (λ l₁ l₂ h, quot.sound (powerset_aux_perm h))

theorem powerset_coe (l : list α) :
  @powerset α l = ((sublists l).map coe : list (multiset α)) :=
congr_arg coe powerset_aux_eq_map_coe

@[simp] theorem powerset_coe' (l : list α) :
  @powerset α l = ((sublists' l).map coe : list (multiset α)) :=
quot.sound powerset_aux_perm_powerset_aux'

@[simp] theorem powerset_zero : @powerset α 0 = 0::0 := rfl

@[simp] theorem powerset_cons (a : α) (s) :
  powerset (a::s) = powerset s + map (cons a) (powerset s) :=
quotient.induction_on s $ λ l, by simp; refl

@[simp] theorem mem_powerset {s t : multiset α} :
  s ∈ powerset t ↔ s ≤ t :=
quotient.induction_on₂ s t $ by simp [subperm, and.comm]

theorem map_single_le_powerset (s : multiset α) :
  s.map (λ a, a::0) ≤ powerset s :=
quotient.induction_on s $ λ l, begin
  simp [powerset_coe],
  show l.map (coe ∘ list.ret) <+~ (sublists l).map coe,
  rw ← list.map_map,
  exact ((map_ret_sublist_sublists _).map _).subperm
end

@[simp] theorem card_powerset (s : multiset α) :
  card (powerset s) = 2 ^ card s :=
quotient.induction_on s $ by simp

/- antidiagonal -/

theorem revzip_powerset_aux {l : list α} ⦃x⦄
  (h : x ∈ revzip (powerset_aux l)) : x.1 + x.2 = ↑l :=
begin
  rw [revzip, powerset_aux_eq_map_coe, ← map_reverse, zip_map, ← revzip] at h,
  simp at h, rcases h with ⟨l₁, l₂, h, rfl, rfl⟩,
  exact quot.sound (revzip_sublists _ _ _ h)
end

theorem revzip_powerset_aux' {l : list α} ⦃x⦄
  (h : x ∈ revzip (powerset_aux' l)) : x.1 + x.2 = ↑l :=
begin
  rw [revzip, powerset_aux', ← map_reverse, zip_map, ← revzip] at h,
  simp at h, rcases h with ⟨l₁, l₂, h, rfl, rfl⟩,
  exact quot.sound (revzip_sublists' _ _ _ h)
end

theorem revzip_powerset_aux_lemma [decidable_eq α] (l : list α)
  {l' : list (multiset α)} (H : ∀ ⦃x : _ × _⦄, x ∈ revzip l' → x.1 + x.2 = ↑l) :
  revzip l' = l'.map (λ x, (x, ↑l - x)) :=
begin
  have : forall₂ (λ (p : multiset α × multiset α) (s : multiset α), p = (s, ↑l - s))
    (revzip l') ((revzip l').map prod.fst),
  { rw forall₂_map_right_iff,
    apply forall₂_same, rintro ⟨s, t⟩ h,
    dsimp, rw [← H h, add_sub_cancel_left] },
  rw [← forall₂_eq_eq_eq, forall₂_map_right_iff], simpa
end

theorem revzip_powerset_aux_perm_aux' {l : list α} :
  revzip (powerset_aux l) ~ revzip (powerset_aux' l) :=
begin
  haveI := classical.dec_eq α,
  rw [revzip_powerset_aux_lemma l revzip_powerset_aux,
      revzip_powerset_aux_lemma l revzip_powerset_aux'],
  exact powerset_aux_perm_powerset_aux'.map _
end

theorem revzip_powerset_aux_perm {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  revzip (powerset_aux l₁) ~ revzip (powerset_aux l₂) :=
begin
  haveI := classical.dec_eq α,
  simp [λ l:list α, revzip_powerset_aux_lemma l revzip_powerset_aux, coe_eq_coe.2 p],
  exact (powerset_aux_perm p).map _
end

/-- The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
    such that `t₁ + t₂ = s`. These pairs are counted with multiplicities. -/
def antidiagonal (s : multiset α) : multiset (multiset α × multiset α) :=
quot.lift_on s
  (λ l, (revzip (powerset_aux l) : multiset (multiset α × multiset α)))
  (λ l₁ l₂ h, quot.sound (revzip_powerset_aux_perm h))

theorem antidiagonal_coe (l : list α) :
  @antidiagonal α l = revzip (powerset_aux l) := rfl

@[simp] theorem antidiagonal_coe' (l : list α) :
  @antidiagonal α l = revzip (powerset_aux' l) :=
quot.sound revzip_powerset_aux_perm_aux'

/-- A pair `(t₁, t₂)` of multisets is contained in `antidiagonal s`
    if and only if `t₁ + t₂ = s`. -/
@[simp] theorem mem_antidiagonal {s : multiset α} {x : multiset α × multiset α} :
  x ∈ antidiagonal s ↔ x.1 + x.2 = s :=
quotient.induction_on s $ λ l, begin
  simp [antidiagonal_coe], refine ⟨λ h, revzip_powerset_aux h, λ h, _⟩,
  haveI := classical.dec_eq α,
  simp [revzip_powerset_aux_lemma l revzip_powerset_aux, h.symm],
  cases x with x₁ x₂,
  exact ⟨_, le_add_right _ _, by rw add_sub_cancel_left _ _⟩
end

@[simp] theorem antidiagonal_map_fst (s : multiset α) :
  (antidiagonal s).map prod.fst = powerset s :=
quotient.induction_on s $ λ l,
by simp [powerset_aux']

@[simp] theorem antidiagonal_map_snd (s : multiset α) :
  (antidiagonal s).map prod.snd = powerset s :=
quotient.induction_on s $ λ l,
by simp [powerset_aux']

@[simp] theorem antidiagonal_zero : @antidiagonal α 0 = (0, 0)::0 := rfl

@[simp] theorem antidiagonal_cons (a : α) (s) : antidiagonal (a::s) =
  map (prod.map id (cons a)) (antidiagonal s) +
  map (prod.map (cons a) id) (antidiagonal s) :=
quotient.induction_on s $ λ l, begin
  simp only [revzip, reverse_append, quot_mk_to_coe, coe_eq_coe, powerset_aux'_cons, cons_coe,
    coe_map, antidiagonal_coe', coe_add],
  rw [← zip_map, ← zip_map, zip_append, (_ : _++_=_)],
  {congr; simp}, {simp}
end

@[simp] theorem card_antidiagonal (s : multiset α) :
  card (antidiagonal s) = 2 ^ card s :=
by have := card_powerset s;
   rwa [← antidiagonal_map_fst, card_map] at this

lemma prod_map_add [comm_semiring β] {s : multiset α} {f g : α → β} :
  prod (s.map (λa, f a + g a)) =
  sum ((antidiagonal s).map (λp, (p.1.map f).prod * (p.2.map g).prod)) :=
begin
  refine s.induction_on _ _,
  { simp },
  { assume a s ih,
    simp [ih, add_mul, mul_comm, mul_left_comm, mul_assoc, sum_map_mul_left.symm],
    cc },
end

/- powerset_len -/

def powerset_len_aux (n : ℕ) (l : list α) : list (multiset α) :=
sublists_len_aux n l coe []

theorem powerset_len_aux_eq_map_coe {n} {l : list α} :
  powerset_len_aux n l = (sublists_len n l).map coe :=
by rw [powerset_len_aux, sublists_len_aux_eq, append_nil]

@[simp] theorem mem_powerset_len_aux {n} {l : list α} {s} :
  s ∈ powerset_len_aux n l ↔ s ≤ ↑l ∧ card s = n :=
quotient.induction_on s $
by simp [powerset_len_aux_eq_map_coe, subperm]; exact
  λ l₁, ⟨λ ⟨l₂, ⟨s, e⟩, p⟩, ⟨⟨_, p, s⟩, p.symm.length_eq.trans e⟩,
    λ ⟨⟨l₂, p, s⟩, e⟩, ⟨_, ⟨s, p.length_eq.trans e⟩, p⟩⟩

@[simp] theorem powerset_len_aux_zero (l : list α) :
  powerset_len_aux 0 l = [0] :=
by simp [powerset_len_aux_eq_map_coe]

@[simp] theorem powerset_len_aux_nil (n : ℕ) :
  powerset_len_aux (n+1) (@nil α) = [] := rfl

@[simp] theorem powerset_len_aux_cons (n : ℕ) (a : α) (l : list α) :
  powerset_len_aux (n+1) (a::l) =
  powerset_len_aux (n+1) l ++ list.map (cons a) (powerset_len_aux n l) :=
by simp [powerset_len_aux_eq_map_coe]; refl

theorem powerset_len_aux_perm {n} {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  powerset_len_aux n l₁ ~ powerset_len_aux n l₂ :=
begin
  induction n with n IHn generalizing l₁ l₂, {simp},
  induction p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂, {refl},
  { simp, exact IH.append ((IHn p).map _) },
  { simp, apply perm.append_left,
    cases n, {simp, apply perm.swap},
    simp,
    rw [← append_assoc, ← append_assoc,
        (by funext s; simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)],
    exact perm_append_comm.append_right _ },
  { exact IH₁.trans IH₂ }
end

def powerset_len (n : ℕ) (s : multiset α) : multiset (multiset α) :=
quot.lift_on s
  (λ l, (powerset_len_aux n l : multiset (multiset α)))
  (λ l₁ l₂ h, quot.sound (powerset_len_aux_perm h))

theorem powerset_len_coe' (n) (l : list α) :
  @powerset_len α n l = powerset_len_aux n l := rfl

theorem powerset_len_coe (n) (l : list α) :
  @powerset_len α n l = ((sublists_len n l).map coe : list (multiset α)) :=
congr_arg coe powerset_len_aux_eq_map_coe

@[simp] theorem powerset_len_zero_left (s : multiset α) :
  powerset_len 0 s = 0::0 :=
quotient.induction_on s $ λ l, by simp [powerset_len_coe']; refl

@[simp] theorem powerset_len_zero_right (n : ℕ) :
  @powerset_len α (n + 1) 0 = 0 := rfl

@[simp] theorem powerset_len_cons (n : ℕ) (a : α) (s) :
  powerset_len (n + 1) (a::s) =
  powerset_len (n + 1) s + map (cons a) (powerset_len n s) :=
quotient.induction_on s $ λ l, by simp [powerset_len_coe']; refl

@[simp] theorem mem_powerset_len {n : ℕ} {s t : multiset α} :
  s ∈ powerset_len n t ↔ s ≤ t ∧ card s = n :=
quotient.induction_on t $ λ l, by simp [powerset_len_coe']

@[simp] theorem card_powerset_len (n : ℕ) (s : multiset α) :
  card (powerset_len n s) = nat.choose (card s) n :=
quotient.induction_on s $ by simp [powerset_len_coe]

theorem powerset_len_le_powerset (n : ℕ) (s : multiset α) :
  powerset_len n s ≤ powerset s :=
quotient.induction_on s $ λ l, by simp [powerset_len_coe]; exact
  ((sublists_len_sublist_sublists' _ _).map _).subperm

theorem powerset_len_mono (n : ℕ) {s t : multiset α} (h : s ≤ t) :
  powerset_len n s ≤ powerset_len n t :=
le_induction_on h $ λ l₁ l₂ h, by simp [powerset_len_coe]; exact
  ((sublists_len_sublist_of_sublist _ h).map _).subperm

/- countp -/

/-- `countp p s` counts the number of elements of `s` (with multiplicity) that
  satisfy `p`. -/
def countp (p : α → Prop) [decidable_pred p] (s : multiset α) : ℕ :=
quot.lift_on s (countp p) (λ l₁ l₂, perm.countp_eq p)

@[simp] theorem coe_countp (l : list α) : countp p l = l.countp p := rfl

@[simp] theorem countp_zero (p : α → Prop) [decidable_pred p] : countp p 0 = 0 := rfl

@[simp] theorem countp_cons_of_pos {a : α} (s) : p a → countp p (a::s) = countp p s + 1 :=
quot.induction_on s countp_cons_of_pos

@[simp] theorem countp_cons_of_neg {a : α} (s) : ¬ p a → countp p (a::s) = countp p s :=
quot.induction_on s countp_cons_of_neg

theorem countp_eq_card_filter (s) : countp p s = card (filter p s) :=
quot.induction_on s $ λ l, countp_eq_length_filter _

@[simp] theorem countp_add (s t) : countp p (s + t) = countp p s + countp p t :=
by simp [countp_eq_card_filter]

instance countp.is_add_monoid_hom : is_add_monoid_hom (countp p : multiset α → ℕ) :=
{ map_add := countp_add, map_zero := countp_zero _ }

theorem countp_pos {s} : 0 < countp p s ↔ ∃ a ∈ s, p a :=
by simp [countp_eq_card_filter, card_pos_iff_exists_mem]

@[simp] theorem countp_sub [decidable_eq α] {s t : multiset α} (h : t ≤ s) :
  countp p (s - t) = countp p s - countp p t :=
by simp [countp_eq_card_filter, h, filter_le_filter]

theorem countp_pos_of_mem {s a} (h : a ∈ s) (pa : p a) : 0 < countp p s :=
countp_pos.2 ⟨_, h, pa⟩

theorem countp_le_of_le {s t} (h : s ≤ t) : countp p s ≤ countp p t :=
by simpa [countp_eq_card_filter] using card_le_of_le (filter_le_filter h)

@[simp] theorem countp_filter {q} [decidable_pred q] (s : multiset α) :
  countp p (filter q s) = countp (λ a, p a ∧ q a) s :=
by simp [countp_eq_card_filter]

end

/- count -/

section
variable [decidable_eq α]

/-- `count a s` is the multiplicity of `a` in `s`. -/
def count (a : α) : multiset α → ℕ := countp (eq a)

@[simp] theorem coe_count (a : α) (l : list α) : count a (↑l) = l.count a := coe_countp _

@[simp] theorem count_zero (a : α) : count a 0 = 0 := rfl

@[simp] theorem count_cons_self (a : α) (s : multiset α) : count a (a::s) = succ (count a s) :=
countp_cons_of_pos _ rfl

@[simp, priority 990]
theorem count_cons_of_ne {a b : α} (h : a ≠ b) (s : multiset α) : count a (b::s) = count a s :=
countp_cons_of_neg _ h

theorem count_le_of_le (a : α) {s t} : s ≤ t → count a s ≤ count a t :=
countp_le_of_le

theorem count_le_count_cons (a b : α) (s : multiset α) : count a s ≤ count a (b :: s) :=
count_le_of_le _ (le_cons_self _ _)

theorem count_singleton (a : α) : count a (a::0) = 1 :=
by simp

@[simp] theorem count_add (a : α) : ∀ s t, count a (s + t) = count a s + count a t :=
countp_add

instance count.is_add_monoid_hom (a : α) : is_add_monoid_hom (count a : multiset α → ℕ) :=
countp.is_add_monoid_hom

@[simp] theorem count_smul (a : α) (n s) : count a (n •ℕ s) = n * count a s :=
by induction n; simp [*, succ_nsmul', succ_mul]

theorem count_pos {a : α} {s : multiset α} : 0 < count a s ↔ a ∈ s :=
by simp [count, countp_pos]

@[simp, priority 980]
theorem count_eq_zero_of_not_mem {a : α} {s : multiset α} (h : a ∉ s) : count a s = 0 :=
by_contradiction $ λ h', h $ count_pos.1 (nat.pos_of_ne_zero h')

theorem count_eq_zero {a : α} {s : multiset α} : count a s = 0 ↔ a ∉ s :=
iff_not_comm.1 $ count_pos.symm.trans pos_iff_ne_zero

@[simp] theorem count_repeat (a : α) (n : ℕ) : count a (repeat a n) = n :=
by simp [repeat]

@[simp] theorem count_erase_self (a : α) (s : multiset α) : count a (erase s a) = pred (count a s) :=
begin
  by_cases a ∈ s,
  { rw [(by rw cons_erase h : count a s = count a (a::erase s a)),
        count_cons_self]; refl },
  { rw [erase_of_not_mem h, count_eq_zero.2 h]; refl }
end

@[simp, priority 980]
theorem count_erase_of_ne {a b : α} (ab : a ≠ b) (s : multiset α) : count a (erase s b) = count a s :=
begin
  by_cases b ∈ s,
  { rw [← count_cons_of_ne ab, cons_erase h] },
  { rw [erase_of_not_mem h] }
end

@[simp] theorem count_sub (a : α) (s t : multiset α) : count a (s - t) = count a s - count a t :=
begin
  revert s, refine multiset.induction_on t (by simp) (λ b t IH s, _),
  rw [sub_cons, IH],
  by_cases ab : a = b,
  { subst b, rw [count_erase_self, count_cons_self, sub_succ, pred_sub] },
  { rw [count_erase_of_ne ab, count_cons_of_ne ab] }
end

@[simp] theorem count_union (a : α) (s t : multiset α) : count a (s ∪ t) = max (count a s) (count a t) :=
by simp [(∪), union, sub_add_eq_max, -add_comm]

@[simp] theorem count_inter (a : α) (s t : multiset α) : count a (s ∩ t) = min (count a s) (count a t) :=
begin
  apply @nat.add_left_cancel (count a (s - t)),
  rw [← count_add, sub_add_inter, count_sub, sub_add_min],
end

lemma count_bind {m : multiset β} {f : β → multiset α} {a : α} :
  count a (bind m f) = sum (m.map $ λb, count a $ f b) :=
multiset.induction_on m (by simp) (by simp)

theorem le_count_iff_repeat_le {a : α} {s : multiset α} {n : ℕ} : n ≤ count a s ↔ repeat a n ≤ s :=
quot.induction_on s $ λ l, le_count_iff_repeat_sublist.trans repeat_le_coe.symm

@[simp] theorem count_filter {p} [decidable_pred p]
  {a} {s : multiset α} (h : p a) : count a (filter p s) = count a s :=
quot.induction_on s $ λ l, count_filter h

theorem ext {s t : multiset α} : s = t ↔ ∀ a, count a s = count a t :=
quotient.induction_on₂ s t $ λ l₁ l₂, quotient.eq.trans perm_iff_count

@[ext]
theorem ext' {s t : multiset α} : (∀ a, count a s = count a t) → s = t :=
ext.2

@[simp] theorem coe_inter (s t : list α) : (s ∩ t : multiset α) = (s.bag_inter t : list α) :=
by ext; simp

theorem le_iff_count {s t : multiset α} : s ≤ t ↔ ∀ a, count a s ≤ count a t :=
⟨λ h a, count_le_of_le a h, λ al,
 by rw ← (ext.2 (λ a, by simp [max_eq_right (al a)]) : s ∪ t = t);
    apply le_union_left⟩

instance : distrib_lattice (multiset α) :=
{ le_sup_inf := λ s t u, le_of_eq $ eq.symm $
    ext.2 $ λ a, by simp only [max_min_distrib_left,
      multiset.count_inter, multiset.sup_eq_union, multiset.count_union, multiset.inf_eq_inter],
  ..multiset.lattice }

instance : semilattice_sup_bot (multiset α) :=
{ bot := 0,
  bot_le := zero_le,
  ..multiset.lattice }

end

/- relator -/

section rel

/-- `rel r s t` -- lift the relation `r` between two elements to a relation between `s` and `t`,
s.t. there is a one-to-one mapping betweem elements in `s` and `t` following `r`. -/
inductive rel (r : α → β → Prop) : multiset α → multiset β → Prop
| zero : rel 0 0
| cons {a b as bs} : r a b → rel as bs → rel (a :: as) (b :: bs)

mk_iff_of_inductive_prop multiset.rel multiset.rel_iff

variables {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

private lemma rel_flip_aux {s t} (h : rel r s t) : rel (flip r) t s :=
rel.rec_on h rel.zero (assume _ _ _ _ h₀ h₁ ih, rel.cons h₀ ih)

lemma rel_flip {s t} : rel (flip r) s t ↔ rel r t s :=
⟨rel_flip_aux, rel_flip_aux⟩

lemma rel_eq_refl {s : multiset α} : rel (=) s s :=
multiset.induction_on s rel.zero (assume a s, rel.cons rfl)

lemma rel_eq {s t : multiset α} : rel (=) s t ↔ s = t :=
begin
  split,
  { assume h, induction h; simp * },
  { assume h, subst h, exact rel_eq_refl }
end

lemma rel.mono {p : α → β → Prop} {s t} (h : ∀a b, r a b → p a b) (hst : rel r s t) : rel p s t :=
begin
  induction hst,
  case rel.zero { exact rel.zero },
  case rel.cons : a b s t hab hst ih { exact ih.cons (h a b hab) }
end

lemma rel.add {s t u v} (hst : rel r s t) (huv : rel r u v) : rel r (s + u) (t + v) :=
begin
  induction hst,
  case rel.zero { simpa using huv },
  case rel.cons : a b s t hab hst ih { simpa using ih.cons hab }
end

lemma rel_flip_eq  {s t : multiset α} : rel (λa b, b = a) s t ↔ s = t :=
show rel (flip (=)) s t ↔ s = t, by rw [rel_flip, rel_eq, eq_comm]

@[simp] lemma rel_zero_left {b : multiset β} : rel r 0 b ↔ b = 0 :=
by rw [rel_iff]; simp

@[simp] lemma rel_zero_right {a : multiset α} : rel r a 0 ↔ a = 0 :=
by rw [rel_iff]; simp

lemma rel_cons_left {a as bs} :
  rel r (a :: as) bs ↔ (∃b bs', r a b ∧ rel r as bs' ∧ bs = b :: bs') :=
begin
  split,
  { generalize hm : a :: as = m,
    assume h,
    induction h generalizing as,
    case rel.zero { simp at hm, contradiction },
    case rel.cons : a' b as' bs ha'b h ih {
      rcases cons_eq_cons.1 hm with ⟨eq₁, eq₂⟩ | ⟨h, cs, eq₁, eq₂⟩,
      { subst eq₁, subst eq₂, exact ⟨b, bs, ha'b, h, rfl⟩ },
      { rcases ih eq₂.symm with ⟨b', bs', h₁, h₂, eq⟩,
        exact ⟨b', b::bs', h₁, eq₁.symm ▸ rel.cons ha'b h₂, eq.symm ▸ cons_swap _ _ _⟩  }
    } },
  { exact assume ⟨b, bs', hab, h, eq⟩, eq.symm ▸ rel.cons hab h }
end

lemma rel_cons_right {as b bs} :
  rel r as (b :: bs) ↔ (∃a as', r a b ∧ rel r as' bs ∧ as = a :: as') :=
begin
  rw [← rel_flip, rel_cons_left],
  apply exists_congr, assume a,
  apply exists_congr, assume as',
  rw [rel_flip, flip]
end

lemma rel_add_left {as₀ as₁} :
  ∀{bs}, rel r (as₀ + as₁) bs ↔ (∃bs₀ bs₁, rel r as₀ bs₀ ∧ rel r as₁ bs₁ ∧ bs = bs₀ + bs₁) :=
multiset.induction_on as₀ (by simp)
  begin
    assume a s ih bs,
    simp only [ih, cons_add, rel_cons_left],
    split,
    { assume h,
      rcases h with ⟨b, bs', hab, h, rfl⟩,
      rcases h with ⟨bs₀, bs₁, h₀, h₁, rfl⟩,
      exact ⟨b :: bs₀, bs₁, ⟨b, bs₀, hab, h₀, rfl⟩, h₁, by simp⟩ },
    { assume h,
      rcases h with ⟨bs₀, bs₁, h, h₁, rfl⟩,
      rcases h with ⟨b, bs, hab, h₀, rfl⟩,
      exact ⟨b, bs + bs₁, hab, ⟨bs, bs₁, h₀, h₁, rfl⟩, by simp⟩ }
  end

lemma rel_add_right {as bs₀ bs₁} :
  rel r as (bs₀ + bs₁) ↔ (∃as₀ as₁, rel r as₀ bs₀ ∧ rel r as₁ bs₁ ∧ as = as₀ + as₁) :=
by rw [← rel_flip, rel_add_left]; simp [rel_flip]

lemma rel_map_left {s : multiset γ} {f : γ → α} :
  ∀{t}, rel r (s.map f) t ↔ rel (λa b, r (f a) b) s t :=
multiset.induction_on s (by simp) (by simp [rel_cons_left] {contextual := tt})

lemma rel_map_right {s : multiset α} {t : multiset γ} {f : γ → β} :
  rel r s (t.map f) ↔ rel (λa b, r a (f b)) s t :=
by rw [← rel_flip, rel_map_left, ← rel_flip]; refl

lemma rel_join {s t} (h : rel (rel r) s t) : rel r s.join t.join :=
begin
  induction h,
  case rel.zero { simp },
  case rel.cons : a b s t hab hst ih { simpa using hab.add ih }
end

lemma rel_map {p : γ → δ → Prop} {s t} {f : α → γ} {g : β → δ} (h : (r ⇒ p) f g) (hst : rel r s t) :
  rel p (s.map f) (t.map g) :=
by rw [rel_map_left, rel_map_right]; exact hst.mono h

lemma rel_bind {p : γ → δ → Prop} {s t} {f : α → multiset γ} {g : β → multiset δ}
  (h : (r ⇒ rel p) f g) (hst : rel r s t) :
  rel p (s.bind f) (t.bind g) :=
by apply rel_join; apply rel_map; assumption

lemma card_eq_card_of_rel {r : α → β → Prop} {s : multiset α} {t : multiset β} (h : rel r s t) :
  card s = card t :=
by induction h; simp [*]

lemma exists_mem_of_rel_of_mem {r : α → β → Prop} {s : multiset α} {t : multiset β} (h : rel r s t) :
  ∀ {a : α} (ha : a ∈ s), ∃ b ∈ t, r a b :=
begin
  induction h with x y s t hxy hst ih,
  { simp },
  { assume a ha,
    cases mem_cons.1 ha with ha ha,
    { exact ⟨y, mem_cons_self _ _, ha.symm ▸ hxy⟩ },
    { rcases ih ha with ⟨b, hbt, hab⟩,
      exact ⟨b, mem_cons.2 (or.inr hbt), hab⟩ } }
end

end rel

section map

theorem map_eq_map {f : α → β} (hf : function.injective f) {s t : multiset α} :
  s.map f = t.map f ↔ s = t :=
by rw [← rel_eq, ← rel_eq, rel_map_left, rel_map_right]; simp [hf.eq_iff]

theorem injective_map {f : α → β} (hf : function.injective f) :
  function.injective (multiset.map f) :=
assume x y, (map_eq_map hf).1

end map

section quot

theorem map_mk_eq_map_mk_of_rel {r : α → α → Prop} {s t : multiset α} (hst : s.rel r t) :
 s.map (quot.mk r) = t.map (quot.mk r) :=
rel.rec_on hst rfl $ assume a b s t hab hst ih, by simp [ih, quot.sound hab]

theorem exists_multiset_eq_map_quot_mk {r : α → α → Prop} (s : multiset (quot r)) :
  ∃t:multiset α, s = t.map (quot.mk r) :=
multiset.induction_on s ⟨0, rfl⟩ $
  assume a s ⟨t, ht⟩, quot.induction_on a $ assume a, ht.symm ▸ ⟨a::t, (map_cons _ _ _).symm⟩

theorem induction_on_multiset_quot
  {r : α → α → Prop} {p : multiset (quot r) → Prop} (s : multiset (quot r)) :
  (∀s:multiset α, p (s.map (quot.mk r))) → p s :=
match s, exists_multiset_eq_map_quot_mk s with _, ⟨t, rfl⟩ := assume h, h _ end

end quot

/- disjoint -/

/-- `disjoint s t` means that `s` and `t` have no elements in common. -/
def disjoint (s t : multiset α) : Prop := ∀ ⦃a⦄, a ∈ s → a ∈ t → false

@[simp] theorem coe_disjoint (l₁ l₂ : list α) : @disjoint α l₁ l₂ ↔ l₁.disjoint l₂ := iff.rfl

theorem disjoint.symm {s t : multiset α} (d : disjoint s t) : disjoint t s
| a i₂ i₁ := d i₁ i₂

theorem disjoint_comm {s t : multiset α} : disjoint s t ↔ disjoint t s :=
⟨disjoint.symm, disjoint.symm⟩

theorem disjoint_left {s t : multiset α} : disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t := iff.rfl

theorem disjoint_right {s t : multiset α} : disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
disjoint_comm

theorem disjoint_iff_ne {s t : multiset α} : disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b :=
by simp [disjoint_left, imp_not_comm]

theorem disjoint_of_subset_left {s t u : multiset α} (h : s ⊆ u) (d : disjoint u t) : disjoint s t
| x m₁ := d (h m₁)

theorem disjoint_of_subset_right {s t u : multiset α} (h : t ⊆ u) (d : disjoint s u) : disjoint s t
| x m m₁ := d m (h m₁)

theorem disjoint_of_le_left {s t u : multiset α} (h : s ≤ u) : disjoint u t → disjoint s t :=
disjoint_of_subset_left (subset_of_le h)

theorem disjoint_of_le_right {s t u : multiset α} (h : t ≤ u) : disjoint s u → disjoint s t :=
disjoint_of_subset_right (subset_of_le h)

@[simp] theorem zero_disjoint (l : multiset α) : disjoint 0 l
| a := (not_mem_nil a).elim

@[simp, priority 1100]
theorem singleton_disjoint {l : multiset α} {a : α} : disjoint (a::0) l ↔ a ∉ l :=
by simp [disjoint]; refl

@[simp, priority 1100]
theorem disjoint_singleton {l : multiset α} {a : α} : disjoint l (a::0) ↔ a ∉ l :=
by rw disjoint_comm; simp

@[simp] theorem disjoint_add_left {s t u : multiset α} :
  disjoint (s + t) u ↔ disjoint s u ∧ disjoint t u :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_add_right {s t u : multiset α} :
  disjoint s (t + u) ↔ disjoint s t ∧ disjoint s u :=
by rw [disjoint_comm, disjoint_add_left]; tauto

@[simp] theorem disjoint_cons_left {a : α} {s t : multiset α} :
  disjoint (a::s) t ↔ a ∉ t ∧ disjoint s t :=
(@disjoint_add_left _ (a::0) s t).trans $ by simp

@[simp] theorem disjoint_cons_right {a : α} {s t : multiset α} :
  disjoint s (a::t) ↔ a ∉ s ∧ disjoint s t :=
by rw [disjoint_comm, disjoint_cons_left]; tauto

theorem inter_eq_zero_iff_disjoint [decidable_eq α] {s t : multiset α} : s ∩ t = 0 ↔ disjoint s t :=
by rw ← subset_zero; simp [subset_iff, disjoint]

@[simp] theorem disjoint_union_left [decidable_eq α] {s t u : multiset α} :
  disjoint (s ∪ t) u ↔ disjoint s u ∧ disjoint t u :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_union_right [decidable_eq α] {s t u : multiset α} :
  disjoint s (t ∪ u) ↔ disjoint s t ∧ disjoint s u :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]

lemma disjoint_map_map {f : α → γ} {g : β → γ} {s : multiset α} {t : multiset β} :
  disjoint (s.map f) (t.map g) ↔ (∀a∈s, ∀b∈t, f a ≠ g b) :=
begin
  simp [disjoint],
  split,
  from assume h a ha b hb eq, h _ ha rfl _ hb eq.symm,
  from assume h c a ha eq₁ b hb eq₂, h _ ha _ hb (eq₂.symm ▸ eq₁)
end

/-- `pairwise r m` states that there exists a list of the elements s.t. `r` holds pairwise on this list. -/
def pairwise (r : α → α → Prop) (m : multiset α) : Prop :=
∃l:list α, m = l ∧ l.pairwise r

lemma pairwise_coe_iff_pairwise {r : α → α → Prop} (hr : symmetric r) {l : list α} :
  multiset.pairwise r l ↔ l.pairwise r :=
iff.intro
  (assume ⟨l', eq, h⟩, ((quotient.exact eq).pairwise_iff hr).2 h)
  (assume h, ⟨l, rfl, h⟩)

/- nodup -/

/-- `nodup s` means that `s` has no duplicates, i.e. the multiplicity of
  any element is at most 1. -/
def nodup (s : multiset α) : Prop :=
quot.lift_on s nodup (λ s t p, propext p.nodup_iff)

@[simp] theorem coe_nodup {l : list α} : @nodup α l ↔ l.nodup := iff.rfl

@[simp] theorem nodup_zero : @nodup α 0 := pairwise.nil

@[simp] theorem nodup_cons {a : α} {s : multiset α} : nodup (a::s) ↔ a ∉ s ∧ nodup s :=
quot.induction_on s $ λ l, nodup_cons

theorem nodup_cons_of_nodup {a : α} {s : multiset α} (m : a ∉ s) (n : nodup s) : nodup (a::s) :=
nodup_cons.2 ⟨m, n⟩

theorem nodup_singleton : ∀ a : α, nodup (a::0) := nodup_singleton

theorem nodup_of_nodup_cons {a : α} {s : multiset α} (h : nodup (a::s)) : nodup s :=
(nodup_cons.1 h).2

theorem not_mem_of_nodup_cons {a : α} {s : multiset α} (h : nodup (a::s)) : a ∉ s :=
(nodup_cons.1 h).1

theorem nodup_of_le {s t : multiset α} (h : s ≤ t) : nodup t → nodup s :=
le_induction_on h $ λ l₁ l₂, nodup_of_sublist

theorem not_nodup_pair : ∀ a : α, ¬ nodup (a::a::0) := not_nodup_pair

theorem nodup_iff_le {s : multiset α} : nodup s ↔ ∀ a : α, ¬ a::a::0 ≤ s :=
quot.induction_on s $ λ l, nodup_iff_sublist.trans $ forall_congr $ λ a,
not_congr (@repeat_le_coe _ a 2 _).symm

theorem nodup_iff_count_le_one [decidable_eq α] {s : multiset α} : nodup s ↔ ∀ a, count a s ≤ 1 :=
quot.induction_on s $ λ l, nodup_iff_count_le_one

@[simp] theorem count_eq_one_of_mem [decidable_eq α] {a : α} {s : multiset α}
  (d : nodup s) (h : a ∈ s) : count a s = 1 :=
le_antisymm (nodup_iff_count_le_one.1 d a) (count_pos.2 h)

lemma pairwise_of_nodup {r : α → α → Prop} {s : multiset α} :
  (∀a∈s, ∀b∈s, a ≠ b → r a b) → nodup s → pairwise r s :=
quotient.induction_on s $ assume l h hl, ⟨l, rfl, hl.imp_of_mem $ assume a b ha hb, h a ha b hb⟩

lemma forall_of_pairwise {r : α → α → Prop} (H : symmetric r) {s : multiset α}
   (hs : pairwise r s) : (∀a∈s, ∀b∈s, a ≠ b → r a b) :=
let ⟨l, hl₁, hl₂⟩ := hs in hl₁.symm ▸ list.forall_of_pairwise H hl₂

theorem nodup_add {s t : multiset α} : nodup (s + t) ↔ nodup s ∧ nodup t ∧ disjoint s t :=
quotient.induction_on₂ s t $ λ l₁ l₂, nodup_append

theorem disjoint_of_nodup_add {s t : multiset α} (d : nodup (s + t)) : disjoint s t :=
(nodup_add.1 d).2.2

theorem nodup_add_of_nodup {s t : multiset α} (d₁ : nodup s) (d₂ : nodup t) : nodup (s + t) ↔ disjoint s t :=
by simp [nodup_add, d₁, d₂]

theorem nodup_of_nodup_map (f : α → β) {s : multiset α} : nodup (map f s) → nodup s :=
quot.induction_on s $ λ l, nodup_of_nodup_map f

theorem nodup_map_on {f : α → β} {s : multiset α} : (∀x∈s, ∀y∈s, f x = f y → x = y) →
  nodup s → nodup (map f s) :=
quot.induction_on s $ λ l, nodup_map_on

theorem nodup_map {f : α → β} {s : multiset α} (hf : function.injective f) : nodup s → nodup (map f s) :=
nodup_map_on (λ x _ y _ h, hf h)

theorem nodup_filter (p : α → Prop) [decidable_pred p] {s} : nodup s → nodup (filter p s) :=
quot.induction_on s $ λ l, nodup_filter p

@[simp] theorem nodup_attach {s : multiset α} : nodup (attach s) ↔ nodup s :=
quot.induction_on s $ λ l, nodup_attach

theorem nodup_pmap {p : α → Prop} {f : Π a, p a → β} {s : multiset α} {H}
  (hf : ∀ a ha b hb, f a ha = f b hb → a = b) : nodup s → nodup (pmap f s H) :=
quot.induction_on s (λ l H, nodup_pmap hf) H

instance nodup_decidable [decidable_eq α] (s : multiset α) : decidable (nodup s) :=
quotient.rec_on_subsingleton s $ λ l, l.nodup_decidable

theorem nodup_erase_eq_filter [decidable_eq α] (a : α) {s} : nodup s → s.erase a = filter (≠ a) s :=
quot.induction_on s $ λ l d, congr_arg coe $ nodup_erase_eq_filter a d

theorem nodup_erase_of_nodup [decidable_eq α] (a : α) {l} : nodup l → nodup (l.erase a) :=
nodup_of_le (erase_le _ _)

theorem mem_erase_iff_of_nodup [decidable_eq α] {a b : α} {l} (d : nodup l) :
  a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l :=
by rw nodup_erase_eq_filter b d; simp [and_comm]

theorem mem_erase_of_nodup [decidable_eq α] {a : α} {l} (h : nodup l) : a ∉ l.erase a :=
by rw mem_erase_iff_of_nodup h; simp

theorem nodup_product {s : multiset α} {t : multiset β} : nodup s → nodup t → nodup (product s t) :=
quotient.induction_on₂ s t $ λ l₁ l₂ d₁ d₂, by simp [nodup_product d₁ d₂]

theorem nodup_sigma {σ : α → Type*} {s : multiset α} {t : Π a, multiset (σ a)} :
  nodup s → (∀ a, nodup (t a)) → nodup (s.sigma t) :=
quot.induction_on s $ assume l₁,
begin
  choose f hf using assume a, quotient.exists_rep (t a),
  rw show t = λ a, f a, from (eq.symm $ funext $ λ a, hf a),
  simpa using nodup_sigma
end

theorem nodup_filter_map (f : α → option β) {s : multiset α}
  (H : ∀ (a a' : α) (b : β), b ∈ f a → b ∈ f a' → a = a') :
  nodup s → nodup (filter_map f s) :=
quot.induction_on s $ λ l, nodup_filter_map H

theorem nodup_range (n : ℕ) : nodup (range n) := nodup_range _

theorem nodup_inter_left [decidable_eq α] {s : multiset α} (t) : nodup s → nodup (s ∩ t) :=
nodup_of_le $ inter_le_left _ _

theorem nodup_inter_right [decidable_eq α] (s) {t : multiset α} : nodup t → nodup (s ∩ t) :=
nodup_of_le $ inter_le_right _ _

@[simp] theorem nodup_union [decidable_eq α] {s t : multiset α} : nodup (s ∪ t) ↔ nodup s ∧ nodup t :=
⟨λ h, ⟨nodup_of_le (le_union_left _ _) h, nodup_of_le (le_union_right _ _) h⟩,
 λ ⟨h₁, h₂⟩, nodup_iff_count_le_one.2 $ λ a, by rw [count_union]; exact
   max_le (nodup_iff_count_le_one.1 h₁ a) (nodup_iff_count_le_one.1 h₂ a)⟩

@[simp] theorem nodup_powerset {s : multiset α} : nodup (powerset s) ↔ nodup s :=
⟨λ h, nodup_of_nodup_map _ (nodup_of_le (map_single_le_powerset _) h),
  quotient.induction_on s $ λ l h,
  by simp; refine list.nodup_map_on _ (nodup_sublists'.2 h); exact
  λ x sx y sy e,
    (h.sublist_ext (mem_sublists'.1 sx) (mem_sublists'.1 sy)).1
      (quotient.exact e)⟩

theorem nodup_powerset_len {n : ℕ} {s : multiset α}
  (h : nodup s) : nodup (powerset_len n s) :=
nodup_of_le (powerset_len_le_powerset _ _) (nodup_powerset.2 h)

@[simp] lemma nodup_bind {s : multiset α} {t : α → multiset β} :
  nodup (bind s t) ↔ ((∀a∈s, nodup (t a)) ∧ (s.pairwise (λa b, disjoint (t a) (t b)))) :=
have h₁ : ∀a, ∃l:list β, t a = l, from
  assume a, quot.induction_on (t a) $ assume l, ⟨l, rfl⟩,
let ⟨t', h'⟩ := classical.axiom_of_choice h₁ in
have t = λa, t' a, from funext h',
have hd : symmetric (λa b, list.disjoint (t' a) (t' b)), from assume a b h, h.symm,
quot.induction_on s $ by simp [this, list.nodup_bind, pairwise_coe_iff_pairwise hd]

theorem nodup_ext {s t : multiset α} : nodup s → nodup t → (s = t ↔ ∀ a, a ∈ s ↔ a ∈ t) :=
quotient.induction_on₂ s t $ λ l₁ l₂ d₁ d₂, quotient.eq.trans $ perm_ext d₁ d₂

theorem le_iff_subset {s t : multiset α} : nodup s → (s ≤ t ↔ s ⊆ t) :=
quotient.induction_on₂ s t $ λ l₁ l₂ d, ⟨subset_of_le, subperm_of_subset_nodup d⟩

theorem range_le {m n : ℕ} : range m ≤ range n ↔ m ≤ n :=
(le_iff_subset (nodup_range _)).trans range_subset

theorem mem_sub_of_nodup [decidable_eq α] {a : α} {s t : multiset α} (d : nodup s) :
  a ∈ s - t ↔ a ∈ s ∧ a ∉ t :=
⟨λ h, ⟨mem_of_le (sub_le_self _ _) h, λ h',
  by refine count_eq_zero.1 _ h; rw [count_sub a s t, nat.sub_eq_zero_iff_le];
     exact le_trans (nodup_iff_count_le_one.1 d _) (count_pos.2 h')⟩,
 λ ⟨h₁, h₂⟩, or.resolve_right (mem_add.1 $ mem_of_le (le_sub_add _ _) h₁) h₂⟩

lemma map_eq_map_of_bij_of_nodup (f : α → γ) (g : β → γ) {s : multiset α} {t : multiset β}
  (hs : s.nodup) (ht : t.nodup) (i : Πa∈s, β)
  (hi : ∀a ha, i a ha ∈ t) (h : ∀a ha, f a = g (i a ha))
  (i_inj : ∀a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
  (i_surj : ∀b∈t, ∃a ha, b = i a ha) :
  s.map f = t.map g :=
have t = s.attach.map (λ x, i x.1 x.2),
  from (nodup_ext ht (nodup_map
      (show function.injective (λ x : {x // x ∈ s}, i x.1 x.2), from λ x y hxy,
        subtype.eq (i_inj x.1 y.1 x.2 y.2 hxy))
      (nodup_attach.2 hs))).2
    (λ x, by simp only [mem_map, true_and, subtype.exists, eq_comm, mem_attach];
      exact ⟨i_surj _, λ ⟨y, hy⟩, hy.snd.symm ▸ hi _ _⟩),
calc s.map f = s.pmap  (λ x _, f x) (λ _, id) : by rw [pmap_eq_map]
... = s.attach.map (λ x, f x.1) : by rw [pmap_eq_map_attach]
... = t.map g : by rw [this, multiset.map_map]; exact map_congr (λ x _, h _ _)

section
variable [decidable_eq α]

/- erase_dup -/

/-- `erase_dup s` removes duplicates from `s`, yielding a `nodup` multiset. -/
def erase_dup (s : multiset α) : multiset α :=
quot.lift_on s (λ l, (l.erase_dup : multiset α))
  (λ s t p, quot.sound p.erase_dup)

@[simp] theorem coe_erase_dup (l : list α) : @erase_dup α _ l = l.erase_dup := rfl

@[simp] theorem erase_dup_zero : @erase_dup α _ 0 = 0 := rfl

@[simp] theorem mem_erase_dup {a : α} {s : multiset α} : a ∈ erase_dup s ↔ a ∈ s :=
quot.induction_on s $ λ l, mem_erase_dup

@[simp] theorem erase_dup_cons_of_mem {a : α} {s : multiset α} : a ∈ s →
  erase_dup (a::s) = erase_dup s :=
quot.induction_on s $ λ l m, @congr_arg _ _ _ _ coe $ erase_dup_cons_of_mem m

@[simp] theorem erase_dup_cons_of_not_mem {a : α} {s : multiset α} : a ∉ s →
  erase_dup (a::s) = a :: erase_dup s :=
quot.induction_on s $ λ l m, congr_arg coe $ erase_dup_cons_of_not_mem m

theorem erase_dup_le (s : multiset α) : erase_dup s ≤ s :=
quot.induction_on s $ λ l, (erase_dup_sublist _).subperm

theorem erase_dup_subset (s : multiset α) : erase_dup s ⊆ s :=
subset_of_le $ erase_dup_le _

theorem subset_erase_dup (s : multiset α) : s ⊆ erase_dup s :=
λ a, mem_erase_dup.2

@[simp] theorem erase_dup_subset' {s t : multiset α} : erase_dup s ⊆ t ↔ s ⊆ t :=
⟨subset.trans (subset_erase_dup _), subset.trans (erase_dup_subset _)⟩

@[simp] theorem subset_erase_dup' {s t : multiset α} : s ⊆ erase_dup t ↔ s ⊆ t :=
⟨λ h, subset.trans h (erase_dup_subset _), λ h, subset.trans h (subset_erase_dup _)⟩

@[simp] theorem nodup_erase_dup (s : multiset α) : nodup (erase_dup s) :=
quot.induction_on s nodup_erase_dup

theorem erase_dup_eq_self {s : multiset α} : erase_dup s = s ↔ nodup s :=
⟨λ e, e ▸ nodup_erase_dup s,
 quot.induction_on s $ λ l h, congr_arg coe $ erase_dup_eq_self.2 h⟩

theorem erase_dup_eq_zero {s : multiset α} : erase_dup s = 0 ↔ s = 0 :=
⟨λ h, eq_zero_of_subset_zero $ h ▸ subset_erase_dup _,
 λ h, h.symm ▸ erase_dup_zero⟩

@[simp] theorem erase_dup_singleton {a : α} : erase_dup (a :: 0) = a :: 0 :=
erase_dup_eq_self.2 $ nodup_singleton _

theorem le_erase_dup {s t : multiset α} : s ≤ erase_dup t ↔ s ≤ t ∧ nodup s :=
⟨λ h, ⟨le_trans h (erase_dup_le _), nodup_of_le h (nodup_erase_dup _)⟩,
 λ ⟨l, d⟩, (le_iff_subset d).2 $ subset.trans (subset_of_le l) (subset_erase_dup _)⟩

theorem erase_dup_ext {s t : multiset α} : erase_dup s = erase_dup t ↔ ∀ a, a ∈ s ↔ a ∈ t :=
by simp [nodup_ext]

theorem erase_dup_map_erase_dup_eq [decidable_eq β] (f : α → β) (s : multiset α) :
  erase_dup (map f (erase_dup s)) = erase_dup (map f s) := by simp [erase_dup_ext]

/- finset insert -/

/-- `ndinsert a s` is the lift of the list `insert` operation. This operation
  does not respect multiplicities, unlike `cons`, but it is suitable as
  an insert operation on `finset`. -/
def ndinsert (a : α) (s : multiset α) : multiset α :=
quot.lift_on s (λ l, (l.insert a : multiset α))
  (λ s t p, quot.sound (p.insert a))

@[simp] theorem coe_ndinsert (a : α) (l : list α) : ndinsert a l = (insert a l : list α) := rfl

@[simp] theorem ndinsert_zero (a : α) : ndinsert a 0 = a::0 := rfl

@[simp, priority 980]
theorem ndinsert_of_mem {a : α} {s : multiset α} : a ∈ s → ndinsert a s = s :=
quot.induction_on s $ λ l h, congr_arg coe $ insert_of_mem h

@[simp, priority 980]
theorem ndinsert_of_not_mem {a : α} {s : multiset α} : a ∉ s → ndinsert a s = a :: s :=
quot.induction_on s $ λ l h, congr_arg coe $ insert_of_not_mem h

@[simp] theorem mem_ndinsert {a b : α} {s : multiset α} : a ∈ ndinsert b s ↔ a = b ∨ a ∈ s :=
quot.induction_on s $ λ l, mem_insert_iff

@[simp] theorem le_ndinsert_self (a : α) (s : multiset α) : s ≤ ndinsert a s :=
quot.induction_on s $ λ l, (sublist_of_suffix $ suffix_insert _ _).subperm

@[simp] theorem mem_ndinsert_self (a : α) (s : multiset α) : a ∈ ndinsert a s :=
mem_ndinsert.2 (or.inl rfl)

theorem mem_ndinsert_of_mem {a b : α} {s : multiset α} (h : a ∈ s) : a ∈ ndinsert b s :=
mem_ndinsert.2 (or.inr h)

@[simp, priority 980]
theorem length_ndinsert_of_mem {a : α} {s : multiset α} (h : a ∈ s) :
  card (ndinsert a s) = card s :=
by simp [h]

@[simp, priority 980]
theorem length_ndinsert_of_not_mem {a : α} {s : multiset α} (h : a ∉ s) :
  card (ndinsert a s) = card s + 1 :=
by simp [h]

theorem erase_dup_cons {a : α} {s : multiset α} :
  erase_dup (a::s) = ndinsert a (erase_dup s) :=
by by_cases a ∈ s; simp [h]

theorem nodup_ndinsert (a : α) {s : multiset α} : nodup s → nodup (ndinsert a s) :=
quot.induction_on s $ λ l, nodup_insert

theorem ndinsert_le {a : α} {s t : multiset α} : ndinsert a s ≤ t ↔ s ≤ t ∧ a ∈ t :=
⟨λ h, ⟨le_trans (le_ndinsert_self _ _) h, mem_of_le h (mem_ndinsert_self _ _)⟩,
 λ ⟨l, m⟩, if h : a ∈ s then by simp [h, l] else
   by rw [ndinsert_of_not_mem h, ← cons_erase m, cons_le_cons_iff,
          ← le_cons_of_not_mem h, cons_erase m]; exact l⟩

lemma attach_ndinsert (a : α) (s : multiset α) :
  (s.ndinsert a).attach =
    ndinsert ⟨a, mem_ndinsert_self a s⟩ (s.attach.map $ λp, ⟨p.1, mem_ndinsert_of_mem p.2⟩) :=
have eq : ∀h : ∀(p : {x // x ∈ s}), p.1 ∈ s,
    (λ (p : {x // x ∈ s}), ⟨p.val, h p⟩ : {x // x ∈ s} → {x // x ∈ s}) = id, from
  assume h, funext $ assume p, subtype.eq rfl,
have ∀t (eq : s.ndinsert a = t), t.attach = ndinsert ⟨a, eq ▸ mem_ndinsert_self a s⟩
  (s.attach.map $ λp, ⟨p.1, eq ▸ mem_ndinsert_of_mem p.2⟩),
begin
  intros t ht,
  by_cases a ∈ s,
  { rw [ndinsert_of_mem h] at ht,
    subst ht,
    rw [eq, map_id, ndinsert_of_mem (mem_attach _ _)] },
  { rw [ndinsert_of_not_mem h] at ht,
    subst ht,
    simp [attach_cons, h] }
end,
this _ rfl

@[simp] theorem disjoint_ndinsert_left {a : α} {s t : multiset α} :
  disjoint (ndinsert a s) t ↔ a ∉ t ∧ disjoint s t :=
iff.trans (by simp [disjoint]) disjoint_cons_left

@[simp] theorem disjoint_ndinsert_right {a : α} {s t : multiset α} :
  disjoint s (ndinsert a t) ↔ a ∉ s ∧ disjoint s t :=
by rw [disjoint_comm, disjoint_ndinsert_left]; tauto

/- finset union -/

/-- `ndunion s t` is the lift of the list `union` operation. This operation
  does not respect multiplicities, unlike `s ∪ t`, but it is suitable as
  a union operation on `finset`. (`s ∪ t` would also work as a union operation
  on finset, but this is more efficient.) -/
def ndunion (s t : multiset α) : multiset α :=
quotient.lift_on₂ s t (λ l₁ l₂, (l₁.union l₂ : multiset α)) $ λ v₁ v₂ w₁ w₂ p₁ p₂,
  quot.sound $ p₁.union p₂

@[simp] theorem coe_ndunion (l₁ l₂ : list α) : @ndunion α _ l₁ l₂ = (l₁ ∪ l₂ : list α) := rfl

@[simp] theorem zero_ndunion (s : multiset α) : ndunion 0 s = s :=
quot.induction_on s $ λ l, rfl

@[simp] theorem cons_ndunion (s t : multiset α) (a : α) :
  ndunion (a :: s) t = ndinsert a (ndunion s t) :=
quotient.induction_on₂ s t $ λ l₁ l₂, rfl

@[simp] theorem mem_ndunion {s t : multiset α} {a : α} : a ∈ ndunion s t ↔ a ∈ s ∨ a ∈ t :=
quotient.induction_on₂ s t $ λ l₁ l₂, list.mem_union

theorem le_ndunion_right (s t : multiset α) : t ≤ ndunion s t :=
quotient.induction_on₂ s t $ λ l₁ l₂,
(sublist_of_suffix $ suffix_union_right _ _).subperm

theorem subset_ndunion_right (s t : multiset α) : t ⊆ ndunion s t :=
subset_of_le (le_ndunion_right s t)

theorem ndunion_le_add (s t : multiset α) : ndunion s t ≤ s + t :=
quotient.induction_on₂ s t $ λ l₁ l₂, (union_sublist_append _ _).subperm

theorem ndunion_le {s t u : multiset α} : ndunion s t ≤ u ↔ s ⊆ u ∧ t ≤ u :=
multiset.induction_on s (by simp)
  (by simp [ndinsert_le, and_comm, and.left_comm] {contextual := tt})

theorem subset_ndunion_left (s t : multiset α) : s ⊆ ndunion s t :=
λ a h, mem_ndunion.2 $ or.inl h

theorem le_ndunion_left {s} (t : multiset α) (d : nodup s) : s ≤ ndunion s t :=
(le_iff_subset d).2 $ subset_ndunion_left _ _

theorem ndunion_le_union (s t : multiset α) : ndunion s t ≤ s ∪ t :=
ndunion_le.2 ⟨subset_of_le (le_union_left _ _), le_union_right _ _⟩

theorem nodup_ndunion (s : multiset α) {t : multiset α} : nodup t → nodup (ndunion s t) :=
quotient.induction_on₂ s t $ λ l₁ l₂, list.nodup_union _

@[simp, priority 980]
theorem ndunion_eq_union {s t : multiset α} (d : nodup s) : ndunion s t = s ∪ t :=
le_antisymm (ndunion_le_union _ _) $ union_le (le_ndunion_left _ d) (le_ndunion_right _ _)

theorem erase_dup_add (s t : multiset α) : erase_dup (s + t) = ndunion s (erase_dup t) :=
quotient.induction_on₂ s t $ λ l₁ l₂, congr_arg coe $ erase_dup_append _ _

/- finset inter -/

/-- `ndinter s t` is the lift of the list `∩` operation. This operation
  does not respect multiplicities, unlike `s ∩ t`, but it is suitable as
  an intersection operation on `finset`. (`s ∩ t` would also work as a union operation
  on finset, but this is more efficient.) -/
def ndinter (s t : multiset α) : multiset α := filter (∈ t) s

@[simp] theorem coe_ndinter (l₁ l₂ : list α) : @ndinter α _ l₁ l₂ = (l₁ ∩ l₂ : list α) := rfl

@[simp] theorem zero_ndinter (s : multiset α) : ndinter 0 s = 0 := rfl

@[simp, priority 980]
theorem cons_ndinter_of_mem {a : α} (s : multiset α) {t : multiset α} (h : a ∈ t) :
  ndinter (a::s) t = a :: (ndinter s t) := by simp [ndinter, h]

@[simp, priority 980]
theorem ndinter_cons_of_not_mem {a : α} (s : multiset α) {t : multiset α} (h : a ∉ t) :
  ndinter (a::s) t = ndinter s t := by simp [ndinter, h]

@[simp] theorem mem_ndinter {s t : multiset α} {a : α} : a ∈ ndinter s t ↔ a ∈ s ∧ a ∈ t :=
mem_filter

@[simp]
theorem nodup_ndinter {s : multiset α} (t : multiset α) : nodup s → nodup (ndinter s t) :=
nodup_filter _

theorem le_ndinter {s t u : multiset α} : s ≤ ndinter t u ↔ s ≤ t ∧ s ⊆ u :=
by simp [ndinter, le_filter, subset_iff]

theorem ndinter_le_left (s t : multiset α) : ndinter s t ≤ s :=
(le_ndinter.1 (le_refl _)).1

theorem ndinter_subset_left (s t : multiset α) : ndinter s t ⊆ s :=
subset_of_le (ndinter_le_left s t)

theorem ndinter_subset_right (s t : multiset α) : ndinter s t ⊆ t :=
(le_ndinter.1 (le_refl _)).2

theorem ndinter_le_right {s} (t : multiset α) (d : nodup s) : ndinter s t ≤ t :=
(le_iff_subset $ nodup_ndinter _ d).2 (ndinter_subset_right _ _)

theorem inter_le_ndinter (s t : multiset α) : s ∩ t ≤ ndinter s t :=
le_ndinter.2 ⟨inter_le_left _ _, subset_of_le $ inter_le_right _ _⟩

@[simp, priority 980]
theorem ndinter_eq_inter {s t : multiset α} (d : nodup s) : ndinter s t = s ∩ t :=
le_antisymm (le_inter (ndinter_le_left _ _) (ndinter_le_right _ d)) (inter_le_ndinter _ _)

theorem ndinter_eq_zero_iff_disjoint {s t : multiset α} : ndinter s t = 0 ↔ disjoint s t :=
by rw ← subset_zero; simp [subset_iff, disjoint]

end

/- fold -/
section fold
variables (op : α → α → α) [hc : is_commutative α op] [ha : is_associative α op]
local notation a * b := op a b
include hc ha

/-- `fold op b s` folds a commutative associative operation `op` over
  the multiset `s`. -/
def fold : α → multiset α → α := foldr op (left_comm _ hc.comm ha.assoc)

theorem fold_eq_foldr (b : α) (s : multiset α) : fold op b s = foldr op (left_comm _ hc.comm ha.assoc) b s := rfl

@[simp] theorem coe_fold_r (b : α) (l : list α) : fold op b l = l.foldr op b := rfl

theorem coe_fold_l (b : α) (l : list α) : fold op b l = l.foldl op b :=
(coe_foldr_swap op _ b l).trans $ by simp [hc.comm]

theorem fold_eq_foldl (b : α) (s : multiset α) : fold op b s = foldl op (right_comm _ hc.comm ha.assoc) b s :=
quot.induction_on s $ λ l, coe_fold_l _ _ _

@[simp] theorem fold_zero (b : α) : (0 : multiset α).fold op b = b := rfl

@[simp] theorem fold_cons_left : ∀ (b a : α) (s : multiset α),
  (a :: s).fold op b = a * s.fold op b := foldr_cons _ _

theorem fold_cons_right (b a : α) (s : multiset α) : (a :: s).fold op b = s.fold op b * a :=
by simp [hc.comm]

theorem fold_cons'_right (b a : α) (s : multiset α) : (a :: s).fold op b = s.fold op (b * a) :=
by rw [fold_eq_foldl, foldl_cons, ← fold_eq_foldl]

theorem fold_cons'_left (b a : α) (s : multiset α) : (a :: s).fold op b = s.fold op (a * b) :=
by rw [fold_cons'_right, hc.comm]

theorem fold_add (b₁ b₂ : α) (s₁ s₂ : multiset α) : (s₁ + s₂).fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂ :=
multiset.induction_on s₂
  (by rw [add_zero, fold_zero, ← fold_cons'_right, ← fold_cons_right op])
  (by simp {contextual := tt}; cc)

theorem fold_singleton (b a : α) : (a::0 : multiset α).fold op b = a * b := by simp

theorem fold_distrib {f g : β → α} (u₁ u₂ : α) (s : multiset β) :
  (s.map (λx, f x * g x)).fold op (u₁ * u₂) = (s.map f).fold op u₁ * (s.map g).fold op u₂ :=
multiset.induction_on s (by simp) (by simp {contextual := tt}; cc)

theorem fold_hom {op' : β → β → β} [is_commutative β op'] [is_associative β op']
  {m : α → β} (hm : ∀x y, m (op x y) = op' (m x) (m y)) (b : α) (s : multiset α) :
  (s.map m).fold op' (m b) = m (s.fold op b) :=
multiset.induction_on s (by simp) (by simp [hm] {contextual := tt})

theorem fold_union_inter [decidable_eq α] (s₁ s₂ : multiset α) (b₁ b₂ : α) :
  (s₁ ∪ s₂).fold op b₁ * (s₁ ∩ s₂).fold op b₂ = s₁.fold op b₁ * s₂.fold op b₂ :=
by rw [← fold_add op, union_add_inter, fold_add op]

@[simp] theorem fold_erase_dup_idem [decidable_eq α] [hi : is_idempotent α op] (s : multiset α) (b : α) :
  (erase_dup s).fold op b = s.fold op b :=
multiset.induction_on s (by simp) $ λ a s IH, begin
  by_cases a ∈ s; simp [IH, h],
  show fold op b s = op a (fold op b s),
  rw [← cons_erase h, fold_cons_left, ← ha.assoc, hi.idempotent],
end

end fold

theorem le_smul_erase_dup [decidable_eq α] (s : multiset α) :
  ∃ n : ℕ, s ≤ n •ℕ erase_dup s :=
⟨(s.map (λ a, count a s)).fold max 0, le_iff_count.2 $ λ a, begin
  rw count_smul, by_cases a ∈ s,
  { refine le_trans _ (mul_le_mul_left _ $ count_pos.2 $ mem_erase_dup.2 h),
    have : count a s ≤ fold max 0 (map (λ a, count a s) (a :: erase s a));
    [simp [le_max_left], simpa [cons_erase h]] },
  { simp [count_eq_zero.2 h, nat.zero_le] }
end⟩

section sup
variables [semilattice_sup_bot α]

/-- Supremum of a multiset: `sup {a, b, c} = a ⊔ b ⊔ c` -/
def sup (s : multiset α) : α := s.fold (⊔) ⊥

@[simp] lemma sup_zero : (0 : multiset α).sup = ⊥ :=
fold_zero _ _

@[simp] lemma sup_cons (a : α) (s : multiset α) :
  (a :: s).sup = a ⊔ s.sup :=
fold_cons_left _ _ _ _

@[simp] lemma sup_singleton {a : α} : (a::0).sup = a := by simp

@[simp] lemma sup_add (s₁ s₂ : multiset α) : (s₁ + s₂).sup = s₁.sup ⊔ s₂.sup :=
eq.trans (by simp [sup]) (fold_add _ _ _ _ _)

lemma sup_le {s : multiset α} {a : α} : s.sup ≤ a ↔ (∀b ∈ s, b ≤ a) :=
multiset.induction_on s (by simp)
  (by simp [or_imp_distrib, forall_and_distrib] {contextual := tt})

lemma le_sup {s : multiset α} {a : α} (h : a ∈ s) : a ≤ s.sup :=
sup_le.1 (le_refl _) _ h

lemma sup_mono {s₁ s₂ : multiset α} (h : s₁ ⊆ s₂) : s₁.sup ≤ s₂.sup :=
sup_le.2 $ assume b hb, le_sup (h hb)

variables [decidable_eq α]

@[simp] lemma sup_erase_dup (s : multiset α) : (erase_dup s).sup = s.sup :=
fold_erase_dup_idem _ _ _

@[simp] lemma sup_ndunion (s₁ s₂ : multiset α) :
  (ndunion s₁ s₂).sup = s₁.sup ⊔ s₂.sup :=
by rw [← sup_erase_dup, erase_dup_ext.2, sup_erase_dup, sup_add]; simp

@[simp] lemma sup_union (s₁ s₂ : multiset α) :
  (s₁ ∪ s₂).sup = s₁.sup ⊔ s₂.sup :=
by rw [← sup_erase_dup, erase_dup_ext.2, sup_erase_dup, sup_add]; simp

@[simp] lemma sup_ndinsert (a : α) (s : multiset α) :
  (ndinsert a s).sup = a ⊔ s.sup :=
by rw [← sup_erase_dup, erase_dup_ext.2, sup_erase_dup, sup_cons]; simp

end sup

section inf
variables [semilattice_inf_top α]

/-- Infimum of a multiset: `inf {a, b, c} = a ⊓ b ⊓ c` -/
def inf (s : multiset α) : α := s.fold (⊓) ⊤

@[simp] lemma inf_zero : (0 : multiset α).inf = ⊤ :=
fold_zero _ _

@[simp] lemma inf_cons (a : α) (s : multiset α) :
  (a :: s).inf = a ⊓ s.inf :=
fold_cons_left _ _ _ _

@[simp] lemma inf_singleton {a : α} : (a::0).inf = a := by simp

@[simp] lemma inf_add (s₁ s₂ : multiset α) : (s₁ + s₂).inf = s₁.inf ⊓ s₂.inf :=
eq.trans (by simp [inf]) (fold_add _ _ _ _ _)

lemma le_inf {s : multiset α} {a : α} : a ≤ s.inf ↔ (∀b ∈ s, a ≤ b) :=
multiset.induction_on s (by simp)
  (by simp [or_imp_distrib, forall_and_distrib] {contextual := tt})

lemma inf_le {s : multiset α} {a : α} (h : a ∈ s) : s.inf ≤ a :=
le_inf.1 (le_refl _) _ h

lemma inf_mono {s₁ s₂ : multiset α} (h : s₁ ⊆ s₂) : s₂.inf ≤ s₁.inf :=
le_inf.2 $ assume b hb, inf_le (h hb)

variables [decidable_eq α]

@[simp] lemma inf_erase_dup (s : multiset α) : (erase_dup s).inf = s.inf :=
fold_erase_dup_idem _ _ _

@[simp] lemma inf_ndunion (s₁ s₂ : multiset α) :
  (ndunion s₁ s₂).inf = s₁.inf ⊓ s₂.inf :=
by rw [← inf_erase_dup, erase_dup_ext.2, inf_erase_dup, inf_add]; simp

@[simp] lemma inf_union (s₁ s₂ : multiset α) :
  (s₁ ∪ s₂).inf = s₁.inf ⊓ s₂.inf :=
by rw [← inf_erase_dup, erase_dup_ext.2, inf_erase_dup, inf_add]; simp

@[simp] lemma inf_ndinsert (a : α) (s : multiset α) :
  (ndinsert a s).inf = a ⊓ s.inf :=
by rw [← inf_erase_dup, erase_dup_ext.2, inf_erase_dup, inf_cons]; simp

end inf

section sort
variables (r : α → α → Prop) [decidable_rel r]
  [is_trans α r] [is_antisymm α r] [is_total α r]

/-- `sort s` constructs a sorted list from the multiset `s`.
  (Uses merge sort algorithm.) -/
def sort (s : multiset α) : list α :=
quot.lift_on s (merge_sort r) $ λ a b h,
eq_of_sorted_of_perm
  ((perm_merge_sort _ _).trans $ h.trans (perm_merge_sort _ _).symm)
  (sorted_merge_sort r _)
  (sorted_merge_sort r _)

@[simp] theorem coe_sort (l : list α) : sort r l = merge_sort r l := rfl

@[simp] theorem sort_sorted (s : multiset α) : sorted r (sort r s) :=
quot.induction_on s $ λ l, sorted_merge_sort r _

@[simp] theorem sort_eq (s : multiset α) : ↑(sort r s) = s :=
quot.induction_on s $ λ l, quot.sound $ perm_merge_sort _ _

@[simp] theorem mem_sort {s : multiset α} {a : α} : a ∈ sort r s ↔ a ∈ s :=
by rw [← mem_coe, sort_eq]

@[simp] theorem length_sort {s : multiset α} : (sort r s).length = s.card :=
quot.induction_on s $ length_merge_sort _

end sort

instance [has_repr α] : has_repr (multiset α) :=
⟨λ s, "{" ++ string.intercalate ", " ((s.map repr).sort (≤)) ++ "}"⟩

section sections

def sections (s : multiset (multiset α)) : multiset (multiset α) :=
multiset.rec_on s {0} (λs _ c, s.bind $ λa, c.map ((::) a))
  (assume a₀ a₁ s pi, by simp [map_bind, bind_bind a₀ a₁, cons_swap])

@[simp] lemma sections_zero : sections (0 : multiset (multiset α)) = 0::0 :=
rfl

@[simp] lemma sections_cons (s : multiset (multiset α)) (m : multiset α) :
  sections (m :: s) = m.bind (λa, (sections s).map ((::) a)) :=
rec_on_cons m s

lemma coe_sections : ∀(l : list (list α)),
  sections ((l.map (λl:list α, (l : multiset α))) : multiset (multiset α)) =
    ((l.sections.map (λl:list α, (l : multiset α))) : multiset (multiset α))
| [] := rfl
| (a :: l) :=
  begin
    simp,
    rw [← cons_coe, sections_cons, bind_map_comm, coe_sections l],
    simp [list.sections, (∘), list.bind]
  end

@[simp] lemma sections_add (s t : multiset (multiset α)) :
  sections (s + t) = (sections s).bind (λm, (sections t).map ((+) m)) :=
multiset.induction_on s (by simp)
  (assume a s ih, by simp [ih, bind_assoc, map_bind, bind_map, -add_comm])

lemma mem_sections {s : multiset (multiset α)} :
  ∀{a}, a ∈ sections s ↔ s.rel (λs a, a ∈ s) a :=
multiset.induction_on s (by simp)
  (assume a s ih a',
    by simp [ih, rel_cons_left, -exists_and_distrib_left, exists_and_distrib_left.symm, eq_comm])

lemma card_sections {s : multiset (multiset α)} : card (sections s) = prod (s.map card) :=
multiset.induction_on s (by simp) (by simp {contextual := tt})

lemma prod_map_sum [comm_semiring α] {s : multiset (multiset α)} :
  prod (s.map sum) = sum ((sections s).map prod) :=
multiset.induction_on s (by simp)
  (assume a s ih, by simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right])

end sections

section pi
variables [decidable_eq α] {δ : α → Type*}
open function

def pi.cons (m : multiset α) (a : α) (b : δ a) (f : Πa∈m, δ a) : Πa'∈a::m, δ a' :=
λa' ha', if h : a' = a then eq.rec b h.symm else f a' $ (mem_cons.1 ha').resolve_left h

def pi.empty (δ : α → Type*) : (Πa∈(0:multiset α), δ a) .

lemma pi.cons_same {m : multiset α} {a : α} {b : δ a} {f : Πa∈m, δ a} (h : a ∈ a :: m) :
  pi.cons m a b f a h = b :=
dif_pos rfl

lemma pi.cons_ne {m : multiset α} {a a' : α} {b : δ a} {f : Πa∈m, δ a} (h' : a' ∈ a :: m) (h : a' ≠ a) :
  pi.cons m a b f a' h' = f a' ((mem_cons.1 h').resolve_left h) :=
dif_neg h

lemma pi.cons_swap {a a' : α} {b : δ a} {b' : δ a'} {m : multiset α} {f : Πa∈m, δ a} (h : a ≠ a') :
  pi.cons (a' :: m) a b (pi.cons m a' b' f) == pi.cons (a :: m) a' b' (pi.cons m a b f) :=
begin
  apply hfunext, { refl }, intros a'' _ h, subst h,
  apply hfunext, { rw [cons_swap] }, intros ha₁ ha₂ h,
  by_cases h₁ : a'' = a; by_cases h₂ : a'' = a';
    simp [*, pi.cons_same, pi.cons_ne] at *,
  { subst h₁, rw [pi.cons_same, pi.cons_same] },
  { subst h₂, rw [pi.cons_same, pi.cons_same] }
end

/-- `pi m t` constructs the Cartesian product over `t` indexed by `m`. -/
def pi (m : multiset α) (t : Πa, multiset (δ a)) : multiset (Πa∈m, δ a) :=
m.rec_on {pi.empty δ} (λa m (p : multiset (Πa∈m, δ a)), (t a).bind $ λb, p.map $ pi.cons m a b)
begin
  intros a a' m n,
  by_cases eq : a = a',
  { subst eq },
  { simp [map_bind, bind_bind (t a') (t a)],
    apply bind_hcongr, { rw [cons_swap a a'] },
    intros b hb,
    apply bind_hcongr, { rw [cons_swap a a'] },
    intros b' hb',
    apply map_hcongr, { rw [cons_swap a a'] },
    intros f hf,
    exact pi.cons_swap eq }
end

@[simp] lemma pi_zero (t : Πa, multiset (δ a)) : pi 0 t = pi.empty δ :: 0 := rfl

@[simp] lemma pi_cons (m : multiset α) (t : Πa, multiset (δ a)) (a : α) :
  pi (a :: m) t = ((t a).bind $ λb, (pi m t).map $ pi.cons m a b) :=
rec_on_cons a m

lemma injective_pi_cons {a : α} {b : δ a} {s : multiset α} (hs : a ∉ s) :
  function.injective (pi.cons s a b) :=
assume f₁ f₂ eq, funext $ assume a', funext $ assume h',
have ne : a ≠ a', from assume h, hs $ h.symm ▸ h',
have a' ∈ a :: s, from mem_cons_of_mem h',
calc f₁ a' h' = pi.cons s a b f₁ a' this : by rw [pi.cons_ne this ne.symm]
  ... = pi.cons s a b f₂ a' this : by rw [eq]
  ... = f₂ a' h' : by rw [pi.cons_ne this ne.symm]

lemma card_pi (m : multiset α) (t : Πa, multiset (δ a)) :
  card (pi m t) = prod (m.map $ λa, card (t a)) :=
multiset.induction_on m (by simp) (by simp [mul_comm] {contextual := tt})

lemma nodup_pi {s : multiset α} {t : Πa, multiset (δ a)} :
  nodup s → (∀a∈s, nodup (t a)) → nodup (pi s t) :=
multiset.induction_on s (assume _ _, nodup_singleton _)
begin
  assume a s ih hs ht,
  have has : a ∉ s, by simp at hs; exact hs.1,
  have hs : nodup s, by simp at hs; exact hs.2,
  simp,
  split,
  { assume b hb,
    from nodup_map (injective_pi_cons has) (ih hs $ assume a' h', ht a' $ mem_cons_of_mem h') },
  { apply pairwise_of_nodup _ (ht a $ mem_cons_self _ _),
    from assume b₁ hb₁ b₂ hb₂ neb, disjoint_map_map.2 (assume f hf g hg eq,
      have pi.cons s a b₁ f a (mem_cons_self _ _) = pi.cons s a b₂ g a (mem_cons_self _ _),
        by rw [eq],
      neb $ show b₁ = b₂, by rwa [pi.cons_same, pi.cons_same] at this) }
end

lemma mem_pi (m : multiset α) (t : Πa, multiset (δ a)) :
  ∀f:Πa∈m, δ a, (f ∈ pi m t) ↔ (∀a (h : a ∈ m), f a h ∈ t a) :=
begin
  refine multiset.induction_on m (λ f, _) (λ a m ih f, _),
  { simpa using show f = pi.empty δ, by funext a ha; exact ha.elim },
  simp, split,
  { rintro ⟨b, hb, f', hf', rfl⟩ a' ha',
    rw [ih] at hf',
    by_cases a' = a,
    { subst h, rwa [pi.cons_same] },
    { rw [pi.cons_ne _ h], apply hf' } },
  { intro hf,
    refine ⟨_, hf a (mem_cons_self a _), λa ha, f a (mem_cons_of_mem ha),
      (ih _).2 (λ a' h', hf _ _), _⟩,
    funext a' h',
    by_cases a' = a,
    { subst h, rw [pi.cons_same] },
    { rw [pi.cons_ne _ h] } }
end

end pi
end multiset

namespace multiset

instance : functor multiset :=
{ map := @map }

@[simp] lemma fmap_def {α' β'} {s : multiset α'} (f : α' → β') : f <$> s = s.map f := rfl

instance : is_lawful_functor multiset :=
by refine { .. }; intros; simp

open is_lawful_traversable is_comm_applicative

variables {F : Type u_1 → Type u_1} [applicative F] [is_comm_applicative F]
variables {α' β' : Type u_1} (f : α' → F β')

def traverse : multiset α' → F (multiset β') :=
quotient.lift (functor.map coe ∘ traversable.traverse f)
begin
  introv p, unfold function.comp,
  induction p,
  case perm.nil { refl },
  case perm.cons {
    have : multiset.cons <$> f p_x <*> (coe <$> traverse f p_l₁) =
      multiset.cons <$> f p_x <*> (coe <$> traverse f p_l₂),
    { rw [p_ih] },
    simpa with functor_norm },
  case perm.swap {
    have : (λa b (l:list β'), (↑(a :: b :: l) : multiset β')) <$> f p_y <*> f p_x =
      (λa b l, ↑(a :: b :: l)) <$> f p_x <*> f p_y,
    { rw [is_comm_applicative.commutative_map],
      congr, funext a b l, simpa [flip] using perm.swap b a l },
    simp [(∘), this] with functor_norm },
  case perm.trans { simp [*] }
end

instance : monad multiset :=
{ pure := λ α x, x::0,
  bind := @bind,
  .. multiset.functor }

@[simp] lemma pure_def {α} : (pure : α → multiset α) = (λ x, x::0) := rfl
@[simp] lemma bind_def {α β} : (>>=) = @bind α β := rfl

instance : is_lawful_monad multiset :=
{ bind_pure_comp_eq_map := λ α β f s, multiset.induction_on s rfl $ λ a s ih, by simp,
  pure_bind := λ α β x f, by simp,
  bind_assoc := @bind_assoc }

open functor
open traversable is_lawful_traversable

@[simp]
lemma lift_beta {α β : Type*} (x : list α) (f : list α → β)
  (h : ∀ a b : list α, a ≈ b → f a = f b) :
  quotient.lift f h (x : multiset α) = f x :=
quotient.lift_beta _ _ _

@[simp]
lemma map_comp_coe {α β} (h : α → β) :
  functor.map h ∘ coe = (coe ∘ functor.map h : list α → multiset β) :=
by funext; simp [functor.map]

lemma id_traverse {α : Type*} (x : multiset α) :
  traverse id.mk x = x :=
quotient.induction_on x begin intro, simp [traverse], refl end

lemma comp_traverse {G H : Type* → Type*}
               [applicative G] [applicative H]
               [is_comm_applicative G] [is_comm_applicative H]
               {α β γ : Type*}
               (g : α → G β) (h : β → H γ) (x : multiset α) :
  traverse (comp.mk ∘ functor.map h ∘ g) x =
  comp.mk (functor.map (traverse h) (traverse g x)) :=
quotient.induction_on x
(by intro;
    simp [traverse,comp_traverse] with functor_norm;
    simp [(<$>),(∘)] with functor_norm)

lemma map_traverse {G : Type* → Type*}
               [applicative G] [is_comm_applicative G]
               {α β γ : Type*}
               (g : α → G β) (h : β → γ)
               (x : multiset α) :
  functor.map (functor.map h) (traverse g x) =
  traverse (functor.map h ∘ g) x :=
quotient.induction_on x
(by intro; simp [traverse] with functor_norm;
    rw [comp_map,map_traverse])

lemma traverse_map {G : Type* → Type*}
               [applicative G] [is_comm_applicative G]
               {α β γ : Type*}
               (g : α → β) (h : β → G γ)
               (x : multiset α) :
  traverse h (map g x) =
  traverse (h ∘ g) x :=
quotient.induction_on x
(by intro; simp [traverse];
    rw [← traversable.traverse_map h g];
    [ refl, apply_instance ])

lemma naturality {G H : Type* → Type*}
                [applicative G] [applicative H]
                [is_comm_applicative G] [is_comm_applicative H]
                (eta : applicative_transformation G H)
                {α β : Type*} (f : α → G β) (x : multiset α) :
  eta (traverse f x) = traverse (@eta _ ∘ f) x :=
quotient.induction_on x
(by intro; simp [traverse,is_lawful_traversable.naturality] with functor_norm)

section choose
variables (p : α → Prop) [decidable_pred p] (l : multiset α)

def choose_x : Π hp : (∃! a, a ∈ l ∧ p a), { a // a ∈ l ∧ p a } :=
quotient.rec_on l (λ l' ex_unique, list.choose_x p l' (exists_of_exists_unique ex_unique)) begin
  intros,
  funext hp,
  suffices all_equal : ∀ x y : { t // t ∈ b ∧ p t }, x = y,
  { apply all_equal },
  { rintros ⟨x, px⟩ ⟨y, py⟩,
    rcases hp with ⟨z, ⟨z_mem_l, pz⟩, z_unique⟩,
    congr,
    calc x = z : z_unique x px
    ...    = y : (z_unique y py).symm }
end

def choose (hp : ∃! a, a ∈ l ∧ p a) : α := choose_x p l hp

lemma choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
(choose_x p l hp).property

lemma choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l := (choose_spec _ _ _).1

lemma choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) := (choose_spec _ _ _).2

end choose

/- Ico -/

/-- `Ico n m` is the multiset lifted from the list `Ico n m`, e.g. the set `{n, n+1, ..., m-1}`. -/
def Ico (n m : ℕ) : multiset ℕ := Ico n m

namespace Ico

theorem map_add (n m k : ℕ) : (Ico n m).map ((+) k) = Ico (n + k) (m + k) :=
congr_arg coe $ list.Ico.map_add _ _ _

theorem map_sub (n m k : ℕ) (h : k ≤ n) : (Ico n m).map (λ x, x - k) = Ico (n - k) (m - k) :=
congr_arg coe $ list.Ico.map_sub _ _ _ h

theorem zero_bot (n : ℕ) : Ico 0 n = range n :=
congr_arg coe $ list.Ico.zero_bot _

@[simp] theorem card (n m : ℕ) : (Ico n m).card = m - n :=
list.Ico.length _ _

theorem nodup (n m : ℕ) : nodup (Ico n m) := Ico.nodup _ _

@[simp] theorem mem {n m l : ℕ} : l ∈ Ico n m ↔ n ≤ l ∧ l < m :=
list.Ico.mem

theorem eq_zero_of_le {n m : ℕ} (h : m ≤ n) : Ico n m = 0 :=
congr_arg coe $ list.Ico.eq_nil_of_le h

@[simp] theorem self_eq_zero {n : ℕ} : Ico n n = 0 :=
eq_zero_of_le $ le_refl n

@[simp] theorem eq_zero_iff {n m : ℕ} : Ico n m = 0 ↔ m ≤ n :=
iff.trans (coe_eq_zero _) list.Ico.eq_empty_iff

lemma add_consecutive {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
  Ico n m + Ico m l = Ico n l :=
congr_arg coe $ list.Ico.append_consecutive hnm hml

@[simp] lemma inter_consecutive (n m l : ℕ) : Ico n m ∩ Ico m l = 0 :=
congr_arg coe $ list.Ico.bag_inter_consecutive n m l

@[simp] theorem succ_singleton {n : ℕ} : Ico n (n+1) = {n} :=
congr_arg coe $ list.Ico.succ_singleton

theorem succ_top {n m : ℕ} (h : n ≤ m) : Ico n (m + 1) = m :: Ico n m :=
by rw [Ico, list.Ico.succ_top h, ← coe_add, add_comm]; refl

theorem eq_cons {n m : ℕ} (h : n < m) : Ico n m = n :: Ico (n + 1) m :=
congr_arg coe $ list.Ico.eq_cons h

@[simp] theorem pred_singleton {m : ℕ} (h : 0 < m) : Ico (m - 1) m = {m - 1} :=
congr_arg coe $ list.Ico.pred_singleton h

@[simp] theorem not_mem_top {n m : ℕ} : m ∉ Ico n m :=
list.Ico.not_mem_top

lemma filter_lt_of_top_le {n m l : ℕ} (hml : m ≤ l) : (Ico n m).filter (λ x, x < l) = Ico n m :=
congr_arg coe $ list.Ico.filter_lt_of_top_le hml

lemma filter_lt_of_le_bot {n m l : ℕ} (hln : l ≤ n) : (Ico n m).filter (λ x, x < l) = ∅ :=
congr_arg coe $ list.Ico.filter_lt_of_le_bot hln

lemma filter_lt_of_ge {n m l : ℕ} (hlm : l ≤ m) : (Ico n m).filter (λ x, x < l) = Ico n l :=
congr_arg coe $ list.Ico.filter_lt_of_ge hlm

@[simp] lemma filter_lt (n m l : ℕ) : (Ico n m).filter (λ x, x < l) = Ico n (min m l) :=
congr_arg coe $ list.Ico.filter_lt n m l

lemma filter_le_of_le_bot {n m l : ℕ} (hln : l ≤ n) : (Ico n m).filter (λ x, l ≤ x) = Ico n m :=
congr_arg coe $ list.Ico.filter_le_of_le_bot hln

lemma filter_le_of_top_le {n m l : ℕ} (hml : m ≤ l) : (Ico n m).filter (λ x, l ≤ x) = ∅ :=
congr_arg coe $ list.Ico.filter_le_of_top_le hml

lemma filter_le_of_le {n m l : ℕ} (hnl : n ≤ l) : (Ico n m).filter (λ x, l ≤ x) = Ico l m :=
congr_arg coe $ list.Ico.filter_le_of_le hnl

@[simp] lemma filter_le (n m l : ℕ) : (Ico n m).filter (λ x, l ≤ x) = Ico (max n l) m :=
congr_arg coe $ list.Ico.filter_le n m l

end Ico

variable (α)

def subsingleton_equiv [subsingleton α] : list α ≃ multiset α :=
{ to_fun := coe,
  inv_fun := quot.lift id $ λ (a b : list α) (h : a ~ b),
    list.ext_le h.length_eq $ λ n h₁ h₂, subsingleton.elim _ _,
  left_inv := λ l, rfl,
  right_inv := λ m, quot.induction_on m $ λ l, rfl }

namespace nat

/-- The antidiagonal of a natural number `n` is
    the multiset of pairs `(i,j)` such that `i+j = n`. -/
def antidiagonal (n : ℕ) : multiset (ℕ × ℕ) :=
list.nat.antidiagonal n

/-- A pair (i,j) is contained in the antidiagonal of `n` if and only if `i+j=n`. -/
@[simp] lemma mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} :
  x ∈ antidiagonal n ↔ x.1 + x.2 = n :=
by rw [antidiagonal, mem_coe, list.nat.mem_antidiagonal]

/-- The cardinality of the antidiagonal of `n` is `n+1`. -/
@[simp] lemma card_antidiagonal (n : ℕ) : (antidiagonal n).card = n+1 :=
by rw [antidiagonal, coe_card, list.nat.length_antidiagonal]

/-- The antidiagonal of `0` is the list `[(0,0)]` -/
@[simp] lemma antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
by { rw [antidiagonal, list.nat.antidiagonal_zero], refl }

/-- The antidiagonal of `n` does not contain duplicate entries. -/
@[simp] lemma nodup_antidiagonal (n : ℕ) : nodup (antidiagonal n) :=
coe_nodup.2 $ list.nat.nodup_antidiagonal n

end nat

end multiset

@[to_additive]
theorem monoid_hom.map_multiset_prod [comm_monoid α] [comm_monoid β] (f : α →* β) (s : multiset α) :
  f s.prod = (s.map f).prod :=
(s.prod_hom f).symm
