/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.list.perm
import algebra.group_power

/-!
# Multisets

These are implemented as the quotient of a list by permutations.

## Notation

We define the global infix notation `::ₘ` for `multiset.cons`.
-/

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

/-- defines a size for a multiset by referring to the size of the underlying list -/
protected def sizeof [has_sizeof α] (s : multiset α) : ℕ :=
quot.lift_on s sizeof $ λ l₁ l₂, perm.sizeof_eq_sizeof

instance has_sizeof [has_sizeof α] : has_sizeof (multiset α) := ⟨multiset.sizeof⟩

/-! ### Empty multiset -/

/-- `0 : multiset α` is the empty set -/
protected def zero : multiset α := @nil α

instance : has_zero (multiset α)   := ⟨multiset.zero⟩
instance : has_emptyc (multiset α) := ⟨0⟩
instance : inhabited (multiset α)  := ⟨0⟩

@[simp] theorem coe_nil_eq_zero : (@nil α : multiset α) = 0 := rfl
@[simp] theorem empty_eq_zero : (∅ : multiset α) = 0 := rfl

theorem coe_eq_zero (l : list α) : (l : multiset α) = 0 ↔ l = [] :=
iff.trans coe_eq_coe perm_nil

/-! ### `multiset.cons` -/

/-- `cons a s` is the multiset which contains `s` plus one more
  instance of `a`. -/
def cons (a : α) (s : multiset α) : multiset α :=
quot.lift_on s (λ l, (a :: l : multiset α))
  (λ l₁ l₂ p, quot.sound (p.cons a))

infixr ` ::ₘ `:67  := multiset.cons

instance : has_insert α (multiset α) := ⟨cons⟩

@[simp] theorem insert_eq_cons (a : α) (s : multiset α) :
  insert a s = a ::ₘ s := rfl

@[simp] theorem cons_coe (a : α) (l : list α) :
  (a ::ₘ l : multiset α) = (a::l : list α) := rfl

theorem singleton_coe (a : α) : (a ::ₘ 0 : multiset α) = ([a] : list α) := rfl

@[simp] theorem cons_inj_left {a b : α} (s : multiset α) :
  a ::ₘ s = b ::ₘ s ↔ a = b :=
⟨quot.induction_on s $ λ l e,
  have [a] ++ l ~ [b] ++ l, from quotient.exact e,
  singleton_perm_singleton.1 $ (perm_append_right_iff _).1 this, congr_arg _⟩

@[simp] theorem cons_inj_right (a : α) : ∀{s t : multiset α}, a ::ₘ s = a ::ₘ t ↔ s = t :=
by rintros ⟨l₁⟩ ⟨l₂⟩; simp

@[recursor 5] protected theorem induction {p : multiset α → Prop}
  (h₁ : p 0) (h₂ : ∀ ⦃a : α⦄ {s : multiset α}, p s → p (a ::ₘ s)) : ∀s, p s :=
by rintros ⟨l⟩; induction l with _ _ ih; [exact h₁, exact h₂ ih]

@[elab_as_eliminator] protected theorem induction_on {p : multiset α → Prop}
  (s : multiset α) (h₁ : p 0) (h₂ : ∀ ⦃a : α⦄ {s : multiset α}, p s → p (a ::ₘ s)) : p s :=
multiset.induction h₁ h₂ s

theorem cons_swap (a b : α) (s : multiset α) : a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s :=
quot.induction_on s $ λ l, quotient.sound $ perm.swap _ _ _

section rec
variables {C : multiset α → Sort*}

/-- Dependent recursor on multisets.

TODO: should be @[recursor 6], but then the definition of `multiset.pi` fails with a stack
overflow in `whnf`.
-/
protected def rec
  (C_0 : C 0)
  (C_cons : Πa m, C m → C (a ::ₘ m))
  (C_cons_heq : ∀ a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ==
    C_cons a' (a ::ₘ m) (C_cons a m b))
  (m : multiset α) : C m :=
quotient.hrec_on m (@list.rec α (λl, C ⟦l⟧) C_0 (λa l b, C_cons a ⟦l⟧ b)) $
  assume l l' h,
  h.rec_heq
    (assume a l l' b b' hl, have ⟦l⟧ = ⟦l'⟧, from quot.sound hl, by cc)
    (assume a a' l, C_cons_heq a a' ⟦l⟧)

@[elab_as_eliminator]
protected def rec_on (m : multiset α)
  (C_0 : C 0)
  (C_cons : Πa m, C m → C (a ::ₘ m))
  (C_cons_heq : ∀a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ==
      C_cons a' (a ::ₘ m) (C_cons a m b)) :
  C m :=
multiset.rec C_0 C_cons C_cons_heq m

variables {C_0 : C 0} {C_cons : Πa m, C m → C (a ::ₘ m)}
  {C_cons_heq : ∀a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ==
    C_cons a' (a ::ₘ m) (C_cons a m b)}

@[simp] lemma rec_on_0 : @multiset.rec_on α C (0:multiset α) C_0 C_cons C_cons_heq = C_0 :=
rfl

@[simp] lemma rec_on_cons (a : α) (m : multiset α) :
  (a ::ₘ m).rec_on C_0 C_cons C_cons_heq = C_cons a m (m.rec_on C_0 C_cons C_cons_heq) :=
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

@[simp] theorem mem_cons {a b : α} {s : multiset α} : a ∈ b ::ₘ s ↔ a = b ∨ a ∈ s :=
quot.induction_on s $ λ l, iff.rfl

lemma mem_cons_of_mem {a b : α} {s : multiset α} (h : a ∈ s) : a ∈ b ::ₘ s :=
mem_cons.2 $ or.inr h

@[simp] theorem mem_cons_self (a : α) (s : multiset α) : a ∈ a ::ₘ s :=
mem_cons.2 (or.inl rfl)

theorem forall_mem_cons {p : α → Prop} {a : α} {s : multiset α} :
  (∀ x ∈ (a ::ₘ s), p x) ↔ p a ∧ ∀ x ∈ s, p x :=
quotient.induction_on' s $ λ L, list.forall_mem_cons

theorem exists_cons_of_mem {s : multiset α} {a : α} : a ∈ s → ∃ t, s = a ::ₘ t :=
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

@[simp] lemma zero_ne_cons {a : α} {m : multiset α} : 0 ≠ a ::ₘ m :=
assume h, have a ∈ (0:multiset α), from h.symm ▸ mem_cons_self _ _, not_mem_zero _ this

@[simp] lemma cons_ne_zero {a : α} {m : multiset α} : a ::ₘ m ≠ 0 := zero_ne_cons.symm

lemma cons_eq_cons {a b : α} {as bs : multiset α} :
  a ::ₘ as = b ::ₘ bs ↔ ((a = b ∧ as = bs) ∨ (a ≠ b ∧ ∃cs, as = b ::ₘ cs ∧ bs = a ::ₘ cs)) :=
begin
  haveI : decidable_eq α := classical.dec_eq α,
  split,
  { assume eq,
    by_cases a = b,
    { subst h, simp * at * },
    { have : a ∈ b ::ₘ bs, from eq ▸ mem_cons_self _ _,
      have : a ∈ bs, by simpa [h],
      rcases exists_cons_of_mem this with ⟨cs, hcs⟩,
      simp [h, hcs],
      have : a ::ₘ as = b ::ₘ a ::ₘ cs, by simp [eq, hcs],
      have : a ::ₘ as = a ::ₘ b ::ₘ cs, by rwa [cons_swap],
      simpa using this } },
  { assume h,
    rcases h with ⟨eq₁, eq₂⟩ | ⟨h, cs, eq₁, eq₂⟩,
    { simp * },
    { simp [*, cons_swap a b] } }
end

end mem

/-! ### `multiset.subset` -/
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

@[simp] theorem cons_subset {a : α} {s t : multiset α} : (a ::ₘ s) ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
by simp [subset_iff, or_imp_distrib, forall_and_distrib]

theorem eq_zero_of_subset_zero {s : multiset α} (h : s ⊆ 0) : s = 0 :=
eq_zero_of_forall_not_mem h

theorem subset_zero {s : multiset α} : s ⊆ 0 ↔ s = 0 :=
⟨eq_zero_of_subset_zero, λ xeq, xeq.symm ▸ subset.refl 0⟩

lemma induction_on' {p : multiset α → Prop} (S : multiset α)
  (h₁ : p ∅) (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → p s → p (insert a s)) : p S :=
@multiset.induction_on α (λ T, T ⊆ S → p T) S (λ _, h₁) (λ a s hps hs,
  let ⟨hS, sS⟩ := cons_subset.1 hs in h₂ hS sS (hps sS)) (subset.refl S)

end subset

section to_list

/-- Produces a list of the elements in the multiset using choice. -/
@[reducible] noncomputable def to_list {α : Type*} (s : multiset α) :=
classical.some (quotient.exists_rep s)

@[simp] lemma to_list_zero {α : Type*} : (multiset.to_list 0 : list α) = [] :=
(multiset.coe_eq_zero _).1 (classical.some_spec (quotient.exists_rep multiset.zero))

lemma coe_to_list {α : Type*} (s : multiset α) : (s.to_list : multiset α) = s :=
classical.some_spec (quotient.exists_rep _)

lemma mem_to_list {α : Type*} (a : α) (s : multiset α) : a ∈ s.to_list ↔ a ∈ s :=
by rw [←multiset.mem_coe, multiset.coe_to_list]

end to_list

/-! ### Partial order on `multiset`s -/

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

theorem lt_cons_self (s : multiset α) (a : α) : s < a ::ₘ s :=
quot.induction_on s $ λ l,
suffices l <+~ a :: l ∧ (¬l ~ a :: l),
  by simpa [lt_iff_le_and_ne],
⟨(sublist_cons _ _).subperm,
 λ p, ne_of_lt (lt_succ_self (length l)) p.length_eq⟩

theorem le_cons_self (s : multiset α) (a : α) : s ≤ a ::ₘ s :=
le_of_lt $ lt_cons_self _ _

theorem cons_le_cons_iff (a : α) {s t : multiset α} : a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t :=
quotient.induction_on₂ s t $ λ l₁ l₂, subperm_cons a

theorem cons_le_cons (a : α) {s t : multiset α} : s ≤ t → a ::ₘ s ≤ a ::ₘ t :=
(cons_le_cons_iff a).2

theorem le_cons_of_not_mem {a : α} {s t : multiset α} (m : a ∉ s) : s ≤ a ::ₘ t ↔ s ≤ t :=
begin
  refine ⟨_, λ h, le_trans h $ le_cons_self _ _⟩,
  suffices : ∀ {t'} (_ : s ≤ t') (_ : a ∈ t'), a ::ₘ s ≤ t',
  { exact λ h, (cons_le_cons_iff a).1 (this h (mem_cons_self _ _)) },
  introv h, revert m, refine le_induction_on h _,
  introv s m₁ m₂,
  rcases mem_split m₂ with ⟨r₁, r₂, rfl⟩,
  exact perm_middle.subperm_left.2 ((subperm_cons _).2 $
    ((sublist_or_mem_of_sublist s).resolve_right m₁).subperm)
end

/-! ### Additive monoid -/

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

theorem singleton_add (a : α) (s : multiset α) : ↑[a] + s = a ::ₘ s := rfl

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

theorem le_add_right (s t : multiset α) : s ≤ s + t :=
by simpa using add_le_add_left (zero_le t) s

theorem le_add_left (s t : multiset α) : s ≤ t + s :=
by simpa using add_le_add_right (zero_le t) s
theorem le_iff_exists_add {s t : multiset α} : s ≤ t ↔ ∃ u, t = s + u :=
⟨λ h, le_induction_on h $ λ l₁ l₂ s,
  let ⟨l, p⟩ := s.exists_perm_append in ⟨l, quot.sound p⟩,
 λ ⟨u, e⟩, e.symm ▸ le_add_right _ _⟩

instance : canonically_ordered_add_monoid (multiset α) :=
{ lt_of_add_lt_add_left := @lt_of_add_lt_add_left _ _,
  le_iff_exists_add     := @le_iff_exists_add _,
  bot                   := 0,
  bot_le                := multiset.zero_le,
  ..multiset.ordered_cancel_add_comm_monoid }

@[simp] theorem cons_add (a : α) (s t : multiset α) : a ::ₘ s + t = a ::ₘ (s + t) :=
by rw [← singleton_add, ← singleton_add, add_assoc]

@[simp] theorem add_cons (a : α) (s t : multiset α) : s + a ::ₘ t = a ::ₘ (s + t) :=
by rw [add_comm, cons_add, add_comm]

@[simp] theorem mem_add {a : α} {s t : multiset α} : a ∈ s + t ↔ a ∈ s ∨ a ∈ t :=
quotient.induction_on₂ s t $ λ l₁ l₂, mem_append

/-! ### Cardinality -/

/-- The cardinality of a multiset is the sum of the multiplicities
  of all its elements, or simply the length of the underlying list. -/
def card : multiset α →+ ℕ :=
{ to_fun := λ s, quot.lift_on s length $ λ l₁ l₂, perm.length_eq,
  map_zero' := rfl,
  map_add' := λ s t, quotient.induction_on₂ s t length_append }

@[simp] theorem coe_card (l : list α) : card (l : multiset α) = length l := rfl

@[simp] theorem card_zero : @card α 0 = 0 := rfl

theorem card_add (s t : multiset α) : card (s + t) = card s + card t :=
card.map_add s t

lemma card_smul (s : multiset α) (n : ℕ) :
  (n •ℕ s).card = n * s.card :=
by rw [card.map_nsmul s n, nat.nsmul_eq_mul]

@[simp] theorem card_cons (a : α) (s : multiset α) : card (a ::ₘ s) = card s + 1 :=
quot.induction_on s $ λ l, rfl

@[simp] theorem card_singleton (a : α) : card (a ::ₘ 0) = 1 := by simp

theorem card_le_of_le {s t : multiset α} (h : s ≤ t) : card s ≤ card t :=
le_induction_on h $ λ l₁ l₂, length_le_of_sublist

theorem eq_of_le_of_card_le {s t : multiset α} (h : s ≤ t) : card t ≤ card s → s = t :=
le_induction_on h $ λ l₁ l₂ s h₂, congr_arg coe $ eq_of_sublist_of_length_le s h₂

theorem card_lt_of_lt {s t : multiset α} (h : s < t) : card s < card t :=
lt_of_not_ge $ λ h₂, ne_of_lt h $ eq_of_le_of_card_le (le_of_lt h) h₂

theorem lt_iff_cons_le {s t : multiset α} : s < t ↔ ∃ a, a ::ₘ s ≤ t :=
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
  (s : multiset α) (h₀ : p 0) (h₁ : ∀ a s, (∀t ≤ s, p t) → p (a ::ₘ s)) : p s :=
multiset.strong_induction_on s $ assume s,
multiset.induction_on s (λ _, h₀) $ λ a s _ ih, h₁ _ _ $
λ t h, ih _ $ lt_of_le_of_lt h $ lt_cons_self _ _

/-! ### Singleton -/
instance : has_singleton α (multiset α) := ⟨λ a, a ::ₘ 0⟩

instance : is_lawful_singleton α (multiset α) := ⟨λ a, rfl⟩

@[simp] theorem singleton_eq_singleton (a : α) : singleton a = a ::ₘ 0 := rfl

@[simp] theorem mem_singleton {a b : α} : b ∈ a ::ₘ 0 ↔ b = a := by simp

theorem mem_singleton_self (a : α) : a ∈ (a ::ₘ 0 : multiset α) := mem_cons_self _ _

theorem singleton_inj {a b : α} : a ::ₘ 0 = b ::ₘ 0 ↔ a = b := cons_inj_left _

@[simp] theorem singleton_ne_zero (a : α) : a ::ₘ 0 ≠ 0 :=
ne_of_gt (lt_cons_self _ _)

@[simp] theorem singleton_le {a : α} {s : multiset α} : a ::ₘ 0 ≤ s ↔ a ∈ s :=
⟨λ h, mem_of_le h (mem_singleton_self _),
 λ h, let ⟨t, e⟩ := exists_cons_of_mem h in e.symm ▸ cons_le_cons _ (zero_le _)⟩

theorem card_eq_one {s : multiset α} : card s = 1 ↔ ∃ a, s = a ::ₘ 0 :=
⟨quot.induction_on s $ λ l h,
  (list.length_eq_one.1 h).imp $ λ a, congr_arg coe,
 λ ⟨a, e⟩, e.symm ▸ rfl⟩

/-! ### `multiset.repeat` -/

/-- `repeat a n` is the multiset containing only `a` with multiplicity `n`. -/
def repeat (a : α) (n : ℕ) : multiset α := repeat a n

@[simp] lemma repeat_zero (a : α) : repeat a 0 = 0 := rfl

@[simp] lemma repeat_succ (a : α) (n) : repeat a (n+1) = a ::ₘ repeat a n := by simp [repeat]

@[simp] lemma repeat_one (a : α) : repeat a 1 = a ::ₘ 0 := by simp

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

theorem repeat_subset_singleton : ∀ (a : α) n, repeat a n ⊆ a ::ₘ 0 := repeat_subset_singleton

theorem repeat_le_coe {a : α} {n} {l : list α} : repeat a n ≤ l ↔ list.repeat a n <+ l :=
⟨λ ⟨l', p, s⟩, (perm_repeat.1 p) ▸ s, sublist.subperm⟩

/-! ### Erasing one copy of an element -/
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

@[simp] theorem erase_cons_head (a : α) (s : multiset α) : (a ::ₘ s).erase a = s :=
quot.induction_on s $ λ l, congr_arg coe $ erase_cons_head a l

@[simp, priority 990]
theorem erase_cons_tail {a b : α} (s : multiset α) (h : b ≠ a) :
  (b ::ₘ s).erase a = b ::ₘ s.erase a :=
quot.induction_on s $ λ l, congr_arg coe $ erase_cons_tail l h

@[simp, priority 980]
theorem erase_of_not_mem {a : α} {s : multiset α} : a ∉ s → s.erase a = s :=
quot.induction_on s $ λ l h, congr_arg coe $ erase_of_not_mem h

@[simp, priority 980]
theorem cons_erase {s : multiset α} {a : α} : a ∈ s → a ::ₘ s.erase a = s :=
quot.induction_on s $ λ l h, quot.sound (perm_cons_erase h).symm

theorem le_cons_erase (s : multiset α) (a : α) : s ≤ a ::ₘ s.erase a :=
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

theorem erase_le_iff_le_cons {s t : multiset α} {a : α} : s.erase a ≤ t ↔ s ≤ a ::ₘ t :=
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

/-! ### `multiset.map` -/

/-- `map f s` is the lift of the list `map` operation. The multiplicity
  of `b` in `map f s` is the number of `a ∈ s` (counting multiplicity)
  such that `f a = b`. -/
def map (f : α → β) (s : multiset α) : multiset β :=
quot.lift_on s (λ l : list α, (l.map f : multiset β))
  (λ l₁ l₂ p, quot.sound (p.map f))

theorem forall_mem_map_iff {f : α → β} {p : β → Prop} {s : multiset α} :
  (∀ y ∈ s.map f, p y) ↔ (∀ x ∈ s, p (f x)) :=
quotient.induction_on' s $ λ L, list.forall_mem_map_iff

@[simp] theorem coe_map (f : α → β) (l : list α) : map f ↑l = l.map f := rfl

@[simp] theorem map_zero (f : α → β) : map f 0 = 0 := rfl

@[simp] theorem map_cons (f : α → β) (a s) : map f (a ::ₘ s) = f a ::ₘ map f s :=
quot.induction_on s $ λ l, rfl

lemma map_singleton (f : α → β) (a : α) : ({a} : multiset α).map f = {f a} := rfl

theorem map_repeat (f : α → β) (a : α) (k : ℕ) : (repeat a k).map f = repeat (f a) k := by
{ induction k, simp, simpa }

@[simp] theorem map_add (f : α → β) (s t) : map f (s + t) = map f s + map f t :=
quotient.induction_on₂ s t $ λ l₁ l₂, congr_arg coe $ map_append _ _ _

instance (f : α → β) : is_add_monoid_hom (map f) :=
{ map_add := map_add _, map_zero := map_zero _ }

theorem map_nsmul (f : α → β) (n s) : map f (n •ℕ s) = n •ℕ map f s :=
(add_monoid_hom.of (map f)).map_nsmul _ _

@[simp] theorem mem_map {f : α → β} {b : β} {s : multiset α} :
  b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b :=
quot.induction_on s $ λ l, mem_map

@[simp] theorem card_map (f : α → β) (s) : card (map f s) = card s :=
quot.induction_on s $ λ l, length_map _ _

@[simp] theorem map_eq_zero {s : multiset α} {f : α → β} : s.map f = 0 ↔ s = 0 :=
by rw [← multiset.card_eq_zero, multiset.card_map, multiset.card_eq_zero]

theorem mem_map_of_mem (f : α → β) {a : α} {s : multiset α} (h : a ∈ s) : f a ∈ map f s :=
mem_map.2 ⟨_, h, rfl⟩

theorem mem_map_of_injective {f : α → β} (H : function.injective f) {a : α} {s : multiset α} :
  f a ∈ map f s ↔ a ∈ s :=
quot.induction_on s $ λ l, mem_map_of_injective H

@[simp] theorem map_map (g : β → γ) (f : α → β) (s : multiset α) :
  map g (map f s) = map (g ∘ f) s :=
quot.induction_on s $ λ l, congr_arg coe $ list.map_map _ _ _

theorem map_id (s : multiset α) : map id s = s :=
quot.induction_on s $ λ l, congr_arg coe $ map_id _

@[simp] lemma map_id' (s : multiset α) : map (λx, x) s = s := map_id s

@[simp] theorem map_const (s : multiset α) (b : β) : map (function.const α b) s = repeat b s.card :=
quot.induction_on s $ λ l, congr_arg coe $ map_const _ _

@[congr] theorem map_congr {f g : α → β} {s : multiset α} :
  (∀ x ∈ s, f x = g x) → map f s = map g s :=
quot.induction_on s $ λ l H, congr_arg coe $ map_congr H

lemma map_hcongr {β' : Type*} {m : multiset α} {f : α → β} {f' : α → β'}
  (h : β = β') (hf : ∀a∈m, f a == f' a) : map f m == map f' m :=
begin subst h, simp at hf, simp [map_congr hf] end

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : list α} (h : b₁ ∈ map (function.const α b₂) l) :
  b₁ = b₂ :=
eq_of_mem_repeat $ by rwa map_const at h

@[simp] theorem map_le_map {f : α → β} {s t : multiset α} (h : s ≤ t) : map f s ≤ map f t :=
le_induction_on h $ λ l₁ l₂ h, (h.map f).subperm

@[simp] theorem map_subset_map {f : α → β} {s t : multiset α} (H : s ⊆ t) : map f s ⊆ map f t :=
λ b m, let ⟨a, h, e⟩ := mem_map.1 m in mem_map.2 ⟨a, H h, e⟩

/-! ### `multiset.fold` -/

/-- `foldl f H b s` is the lift of the list operation `foldl f b l`,
  which folds `f` over the multiset. It is well defined when `f` is right-commutative,
  that is, `f (f b a₁) a₂ = f (f b a₂) a₁`. -/
def foldl (f : β → α → β) (H : right_commutative f) (b : β) (s : multiset α) : β :=
quot.lift_on s (λ l, foldl f b l)
  (λ l₁ l₂ p, p.foldl_eq H b)

@[simp] theorem foldl_zero (f : β → α → β) (H b) : foldl f H b 0 = b := rfl

@[simp] theorem foldl_cons (f : β → α → β) (H b a s) :
  foldl f H b (a ::ₘ s) = foldl f H (f b a) s :=
quot.induction_on s $ λ l, rfl

@[simp] theorem foldl_add (f : β → α → β) (H b s t) :
  foldl f H b (s + t) = foldl f H (foldl f H b s) t :=
quotient.induction_on₂ s t $ λ l₁ l₂, foldl_append _ _ _ _

/-- `foldr f H b s` is the lift of the list operation `foldr f b l`,
  which folds `f` over the multiset. It is well defined when `f` is left-commutative,
  that is, `f a₁ (f a₂ b) = f a₂ (f a₁ b)`. -/
def foldr (f : α → β → β) (H : left_commutative f) (b : β) (s : multiset α) : β :=
quot.lift_on s (λ l, foldr f b l)
  (λ l₁ l₂ p, p.foldr_eq H b)

@[simp] theorem foldr_zero (f : α → β → β) (H b) : foldr f H b 0 = b := rfl

@[simp] theorem foldr_cons (f : α → β → β) (H b a s) :
  foldr f H b (a ::ₘ s) = f a (foldr f H b s) :=
quot.induction_on s $ λ l, rfl

@[simp] theorem foldr_add (f : α → β → β) (H b s t) :
  foldr f H b (s + t) = foldr f H (foldr f H b t) s :=
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

lemma foldr_induction' (f : α → β → β) (H : left_commutative f) (x : β) (q : α → Prop)
  (p : β → Prop) (s : multiset α) (hpqf : ∀ a b, q a → p b → p (f a b)) (px : p x)
  (q_s : ∀ a ∈ s, q a) :
  p (foldr f H x s) :=
begin
  revert s,
  refine multiset.induction (by simp [px]) _,
  intros a s hs hsa,
  rw foldr_cons,
  have hps : ∀ (x : α), x ∈ s → q x, from λ x hxs, hsa x (mem_cons_of_mem hxs),
  exact hpqf a (foldr f H x s) (hsa a (mem_cons_self a s)) (hs hps),
end

lemma foldr_induction (f : α → α → α) (H : left_commutative f) (x : α) (p : α → Prop)
  (s : multiset α) (p_f : ∀ a b, p a → p b → p (f a b)) (px : p x) (p_s : ∀ a ∈ s, p a) :
  p (foldr f H x s) :=
foldr_induction' f H x p p s p_f px p_s

lemma foldl_induction' (f : β → α → β) (H : right_commutative f) (x : β) (q : α → Prop)
  (p : β → Prop) (s : multiset α) (hpqf : ∀ a b, q a → p b → p (f b a)) (px : p x)
  (q_s : ∀ a ∈ s, q a) :
  p (foldl f H x s) :=
begin
  rw foldl_swap,
  exact foldr_induction' (λ x y, f y x) (λ x y z, (H _ _ _).symm) x q p s hpqf px q_s,
end

lemma foldl_induction (f : α → α → α) (H : right_commutative f) (x : α) (p : α → Prop)
  (s : multiset α) (p_f : ∀ a b, p a → p b → p (f b a)) (px : p x) (p_s : ∀ a ∈ s, p a) :
  p (foldl f H x s) :=
foldl_induction' f H x p p s p_f px p_s

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

attribute [norm_cast] coe_prod coe_sum

@[simp, to_additive]
theorem prod_zero [comm_monoid α] : @prod α _ 0 = 1 := rfl

@[simp, to_additive]
theorem prod_cons [comm_monoid α] (a : α) (s) : prod (a ::ₘ s) = a * prod s :=
foldr_cons _ _ _ _ _

@[to_additive]
theorem prod_singleton [comm_monoid α] (a : α) : prod (a ::ₘ 0) = a := by simp

@[simp, to_additive]
theorem prod_add [comm_monoid α] (s t : multiset α) : prod (s + t) = prod s * prod t :=
quotient.induction_on₂ s t $ λ l₁ l₂, by simp

instance sum.is_add_monoid_hom [add_comm_monoid α] : is_add_monoid_hom (sum : multiset α → α) :=
{ map_add := sum_add, map_zero := sum_zero }

lemma to_mul_sum [comm_monoid α] (s : multiset (additive α)) :
  additive.to_mul (sum s) = (s.map additive.to_mul).prod :=
multiset.induction (by simp) (by intros; simp *) s

lemma of_mul_prod [comm_monoid α] (s : multiset α) :
  additive.of_mul (prod s) = (s.map additive.of_mul).sum :=
multiset.induction (by simp) (by intros; simp *) s

lemma to_add_prod [add_comm_monoid α] (s : multiset (multiplicative α)) :
  multiplicative.to_add (prod s) = (s.map multiplicative.to_add).sum :=
multiset.induction (by simp) (by intros; simp *) s

lemma of_add_sum [add_comm_monoid α] (s : multiset α) :
  multiplicative.of_add (sum s) = (s.map multiplicative.of_add).prod :=
multiset.induction (by simp) (by intros; simp *) s

lemma prod_smul {α : Type*} [comm_monoid α] (m : multiset α) :
  ∀n, (n •ℕ m).prod = m.prod ^ n
| 0       := rfl
| (n + 1) :=
  by rw [add_nsmul, one_nsmul, pow_add, pow_one, prod_add, prod_smul n]

@[simp] theorem prod_repeat [comm_monoid α] (a : α) (n : ℕ) : prod (multiset.repeat a n) = a ^ n :=
by simp [repeat, list.prod_repeat]
@[simp] theorem sum_repeat [add_comm_monoid α] :
  ∀ (a : α) (n : ℕ), sum (multiset.repeat a n) = n •ℕ a :=
by simp [repeat, list.sum_repeat]
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

lemma sum_map_sum_map [add_comm_monoid γ] (m : multiset α) (n : multiset β) {f : α → β → γ} :
  sum (m.map $ λa, sum $ n.map $ λb, f a b) = sum (n.map $ λb, sum $ m.map $ λa, f a b) :=
multiset.induction_on m (by simp) (assume a m ih, by simp [ih])
attribute [to_additive] prod_map_prod_map

lemma sum_map_mul_left [semiring β] {b : β} {s : multiset α} {f : α → β} :
  sum (s.map (λa, b * f a)) = b * sum (s.map f) :=
multiset.induction_on s (by simp) (assume a s ih, by simp [ih, mul_add])

lemma sum_map_mul_right [semiring β] {b : β} {s : multiset α} {f : α → β} :
  sum (s.map (λa, f a * b)) = sum (s.map f) * b :=
multiset.induction_on s (by simp) (assume a s ih, by simp [ih, add_mul])

lemma prod_eq_zero {M₀ : Type*} [comm_monoid_with_zero M₀] {s : multiset M₀} (h : (0 : M₀) ∈ s) :
  multiset.prod s = 0 :=
begin
  rcases multiset.exists_cons_of_mem h with ⟨s', hs'⟩,
  simp [hs', multiset.prod_cons]
end

lemma prod_eq_zero_iff {M₀ : Type*} [comm_monoid_with_zero M₀] [no_zero_divisors M₀] [nontrivial M₀]
  {s : multiset M₀} :
  multiset.prod s = 0 ↔ (0 : M₀) ∈ s :=
by { rcases s with ⟨l⟩, simp }

theorem prod_ne_zero {M₀ : Type*} [comm_monoid_with_zero M₀] [no_zero_divisors M₀] [nontrivial M₀]
  {m : multiset M₀} (h : (0 : M₀) ∉ m) : m.prod ≠ 0 :=
mt prod_eq_zero_iff.1 h

@[to_additive]
lemma prod_hom [comm_monoid α] [comm_monoid β] (s : multiset α) (f : α →* β) :
  (s.map f).prod = f s.prod :=
quotient.induction_on s $ λ l, by simp only [l.prod_hom f, quot_mk_to_coe, coe_map, coe_prod]

@[to_additive]
theorem prod_hom_rel [comm_monoid β] [comm_monoid γ] (s : multiset α) {r : β → γ → Prop}
  {f : α → β} {g : α → γ} (h₁ : r 1 1) (h₂ : ∀⦃a b c⦄, r b c → r (f a * b) (g a * c)) :
  r (s.map f).prod (s.map g).prod :=
quotient.induction_on s $ λ l,
  by simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, coe_map, coe_prod]

lemma dvd_prod [comm_monoid α] {a : α} {s : multiset α} : a ∈ s → a ∣ s.prod :=
quotient.induction_on s (λ l a h, by simpa using list.dvd_prod h) a

lemma prod_dvd_prod [comm_monoid α] {s t : multiset α} (h : s ≤ t) :
  s.prod ∣ t.prod :=
begin
  rcases multiset.le_iff_exists_add.1 h with ⟨z, rfl⟩,
  simp,
end

@[to_additive sum_nonneg]
lemma one_le_prod_of_one_le [ordered_comm_monoid α] {m : multiset α} :
  (∀ x ∈ m, (1 : α) ≤ x) → 1 ≤ m.prod :=
quotient.induction_on m $ λ l hl, by simpa using list.one_le_prod_of_one_le hl

@[to_additive]
lemma single_le_prod [ordered_comm_monoid α] {m : multiset α} :
  (∀ x ∈ m, (1 : α) ≤ x) → ∀ x ∈ m, x ≤ m.prod :=
quotient.induction_on m $ λ l hl x hx, by simpa using list.single_le_prod hl x hx

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
lemma all_one_of_le_one_le_of_prod_eq_one [ordered_comm_monoid α] {m : multiset α} :
  (∀ x ∈ m, (1 : α) ≤ x) → m.prod = 1 → (∀ x ∈ m, x = (1 : α)) :=
begin
  apply quotient.induction_on m,
  simp only [quot_mk_to_coe, coe_prod, mem_coe],
  intros l hl₁ hl₂ x hx,
  apply all_one_of_le_one_le_of_prod_eq_one hl₁ hl₂ _ hx,
end

lemma sum_eq_zero_iff [canonically_ordered_add_monoid α] {m : multiset α} :
  m.sum = 0 ↔ ∀ x ∈ m, x = (0 : α) :=
quotient.induction_on m $ λ l, by simpa using list.sum_eq_zero_iff l

@[to_additive]
lemma prod_induction {M : Type*} [comm_monoid M] (p : M → Prop) (s : multiset M)
  (p_mul : ∀ a b, p a → p b → p (a * b)) (p_one : p 1) (p_s : ∀ a ∈ s, p a) :
  p s.prod :=
begin
  rw prod_eq_foldr,
  exact foldr_induction (*) (λ x y z, by simp [mul_left_comm]) 1 p s p_mul p_one p_s,
end

@[to_additive le_sum_of_subadditive_on_pred]
lemma le_prod_of_submultiplicative_on_pred [comm_monoid α] [ordered_comm_monoid β]
  (f : α → β) (p : α → Prop) (h_one : f 1 = 1) (hp_one : p 1)
  (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b)
  (hp_mul : ∀ a b, p a → p b → p (a * b)) (s : multiset α) (hps : ∀ a, a ∈ s → p a) :
  f s.prod ≤ (s.map f).prod :=
begin
  revert s,
  refine multiset.induction _ _,
  { simp [le_of_eq h_one], },
  intros a s hs hpsa,
  have hps : ∀ x, x ∈ s → p x, from λ x hx, hpsa x (mem_cons_of_mem hx),
  have hp_prod : p s.prod, from prod_induction p s hp_mul hp_one hps,
  rw [prod_cons, map_cons, prod_cons],
  exact (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans (mul_le_mul_left' (hs hps) _),
end

@[to_additive le_sum_of_subadditive]
lemma le_prod_of_submultiplicative [comm_monoid α] [ordered_comm_monoid β]
  (f : α → β) (h_one : f 1 = 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : multiset α) :
  f s.prod ≤ (s.map f).prod :=
le_prod_of_submultiplicative_on_pred f (λ i, true) h_one trivial (λ x y _ _ , h_mul x y) (by simp)
  s (by simp)

@[to_additive]
lemma prod_induction_nonempty {M : Type*} [comm_monoid M] (p : M → Prop)
  (p_mul : ∀ a b, p a → p b → p (a * b)) {s : multiset M} (hs_nonempty : s ≠ ∅)
  (p_s : ∀ a ∈ s, p a) :
  p s.prod :=
begin
  revert s,
  refine multiset.induction _ _,
  { intro h,
    exfalso,
    simpa using h, },
  intros a s hs hsa hpsa,
  rw prod_cons,
  by_cases hs_empty : s = ∅,
  { simp [hs_empty, hpsa a], },
  have hps : ∀ (x : M), x ∈ s → p x, from λ x hxs, hpsa x (mem_cons_of_mem hxs),
  exact p_mul a s.prod (hpsa a (mem_cons_self a s)) (hs hs_empty hps),
end

@[to_additive le_sum_nonempty_of_subadditive_on_pred]
lemma le_prod_nonempty_of_submultiplicative_on_pred [comm_monoid α] [ordered_comm_monoid β]
  (f : α → β) (p : α → Prop) (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b)
  (hp_mul : ∀ a b, p a → p b → p (a * b)) (s : multiset α) (hs_nonempty : s ≠ ∅)
  (hs : ∀ a, a ∈ s → p a) :
  f s.prod ≤ (s.map f).prod :=
begin
  revert s,
  refine multiset.induction _ _,
  { intro h,
    exfalso,
    exact h rfl, },
  rintros a s hs hsa_nonempty hsa_prop,
  rw [prod_cons, map_cons, prod_cons],
  by_cases hs_empty : s = ∅,
  { simp [hs_empty], },
  have hsa_restrict : (∀ x, x ∈ s → p x), from λ x hx, hsa_prop x (mem_cons_of_mem hx),
  have hp_sup : p s.prod,
    from prod_induction_nonempty p hp_mul hs_empty hsa_restrict,
  have hp_a : p a, from hsa_prop a (mem_cons_self a s),
  exact (h_mul a _ hp_a hp_sup).trans (mul_le_mul_left' (hs hs_empty hsa_restrict) _),
end

@[to_additive le_sum_nonempty_of_subadditive]
lemma le_prod_nonempty_of_submultiplicative [comm_monoid α] [ordered_comm_monoid β]
  (f : α → β) (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : multiset α) (hs_nonempty : s ≠ ∅) :
  f s.prod ≤ (s.map f).prod :=
le_prod_nonempty_of_submultiplicative_on_pred f (λ i, true) (by simp [h_mul]) (by simp) s
  hs_nonempty (by simp)

lemma abs_sum_le_sum_abs [linear_ordered_field α] {s : multiset α} :
  abs s.sum ≤ (s.map abs).sum :=
le_sum_of_subadditive _ abs_zero abs_add s

theorem dvd_sum [comm_semiring α] {a : α} {s : multiset α} : (∀ x ∈ s, a ∣ x) → a ∣ s.sum :=
multiset.induction_on s (λ _, dvd_zero _)
  (λ x s ih h, by rw sum_cons; exact dvd_add
    (h _ (mem_cons_self _ _)) (ih (λ y hy, h _ (mem_cons.2 (or.inr hy)))))

@[simp] theorem sum_map_singleton (s : multiset α) : (s.map (λ a, a ::ₘ 0)).sum = s :=
multiset.induction_on s (by simp) (by simp)

/-! ### Join -/

/-- `join S`, where `S` is a multiset of multisets, is the lift of the list join
  operation, that is, the union of all the sets.

     join {{1, 2}, {1, 2}, {0, 1}} = {0, 1, 1, 1, 2, 2} -/
def join : multiset (multiset α) → multiset α := sum

theorem coe_join : ∀ L : list (list α),
  join (L.map (@coe _ (multiset α) _) : multiset (multiset α)) = L.join
| []       := rfl
| (l :: L) := congr_arg (λ s : multiset α, ↑l + s) (coe_join L)

@[simp] theorem join_zero : @join α 0 = 0 := rfl

@[simp] theorem join_cons (s S) : @join α (s ::ₘ S) = s + join S :=
sum_cons _ _

@[simp] theorem join_add (S T) : @join α (S + T) = join S + join T :=
sum_add _ _

@[simp] theorem mem_join {a S} : a ∈ @join α S ↔ ∃ s ∈ S, a ∈ s :=
multiset.induction_on S (by simp) $
  by simp [or_and_distrib_right, exists_or_distrib] {contextual := tt}

@[simp] theorem card_join (S) : card (@join α S) = sum (map card S) :=
multiset.induction_on S (by simp) (by simp)

/-! ### `multiset.bind` -/

/-- `bind s f` is the monad bind operation, defined as `join (map f s)`.
  It is the union of `f a` as `a` ranges over `s`. -/
def bind (s : multiset α) (f : α → multiset β) : multiset β :=
join (map f s)

@[simp] theorem coe_bind (l : list α) (f : α → list β) :
  @bind α β l (λ a, f a) = l.bind f :=
by rw [list.bind, ← coe_join, list.map_map]; refl

@[simp] theorem zero_bind (f : α → multiset β) : bind 0 f = 0 := rfl

@[simp] theorem cons_bind (a s) (f : α → multiset β) : bind (a ::ₘ s) f = f a + bind s f :=
by simp [bind]

@[simp] theorem add_bind (s t) (f : α → multiset β) : bind (s + t) f = bind s f + bind t f :=
by simp [bind]

@[simp] theorem bind_zero (s : multiset α) : bind s (λa, 0 : α → multiset β) = 0 :=
by simp [bind, join]

@[simp] theorem bind_add (s : multiset α) (f g : α → multiset β) :
  bind s (λa, f a + g a) = bind s f + bind s g :=
by simp [bind, join]

@[simp] theorem bind_cons (s : multiset α) (f : α → β) (g : α → multiset β) :
  bind s (λa, f a ::ₘ g a) = map f s + bind s g :=
multiset.induction_on s (by simp) (by simp [add_comm, add_left_comm] {contextual := tt})

@[simp] theorem mem_bind {b s} {f : α → multiset β} : b ∈ bind s f ↔ ∃ a ∈ s, b ∈ f a :=
by simp [bind]; simp [-exists_and_distrib_right, exists_and_distrib_right.symm];
   rw exists_swap; simp [and_assoc]

@[simp] theorem card_bind (s) (f : α → multiset β) : card (bind s f) = sum (map (card ∘ f) s) :=
by simp [bind]

lemma bind_congr {f g : α → multiset β} {m : multiset α} :
  (∀a∈m, f a = g a) → bind m f = bind m g :=
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

/-! ### Product of two `multiset`s -/

/-- The multiplicity of `(a, b)` in `product s t` is
  the product of the multiplicity of `a` in `s` and `b` in `t`. -/
def product (s : multiset α) (t : multiset β) : multiset (α × β) :=
s.bind $ λ a, t.map $ prod.mk a

@[simp] theorem coe_product (l₁ : list α) (l₂ : list β) :
  @product α β l₁ l₂ = l₁.product l₂ :=
by rw [product, list.product, ← coe_bind]; simp

@[simp] theorem zero_product (t) : @product α β 0 t = 0 := rfl

@[simp] theorem cons_product (a : α) (s : multiset α) (t : multiset β) :
  product (a ::ₘ s) t = map (prod.mk a) t + product s t :=
by simp [product]

@[simp] theorem product_singleton (a : α) (b : β) : product (a ::ₘ 0) (b ::ₘ 0) = (a,b) ::ₘ 0 := rfl

@[simp] theorem add_product (s t : multiset α) (u : multiset β) :
  product (s + t) u = product s u + product t u :=
by simp [product]

@[simp] theorem product_add (s : multiset α) : ∀ t u : multiset β,
  product s (t + u) = product s t + product s u :=
multiset.induction_on s (λ t u, rfl) $ λ a s IH t u,
  by rw [cons_product, IH]; simp; cc

@[simp] theorem mem_product {s t} : ∀ {p : α × β}, p ∈ @product α β s t ↔ p.1 ∈ s ∧ p.2 ∈ t
| (a, b) := by simp [product, and.left_comm]

@[simp] theorem card_product (s : multiset α) (t : multiset β) :
  card (product s t) = card s * card t :=
by simp [product, repeat, (∘), mul_comm]

/-! ### Sigma multiset -/
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
  (a ::ₘ s).sigma t = map (sigma.mk a) (t a) + s.sigma t :=
by simp [multiset.sigma]

@[simp] theorem sigma_singleton (a : α) (b : α → β) :
  (a ::ₘ 0).sigma (λ a, b a ::ₘ 0) = ⟨a, b a⟩ ::ₘ 0 := rfl

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

/-! ### Map for partial functions -/

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
  ∀(h : ∀b∈a ::ₘ m, p b), pmap f (a ::ₘ m) h =
    f a (h a (mem_cons_self a m)) ::ₘ pmap f m (λa ha, h a $ mem_cons_of_mem ha) :=
quotient.induction_on m $ assume l h, rfl

/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
  a multiset on `{x // x ∈ s}`. -/
def attach (s : multiset α) : multiset {x // x ∈ s} := pmap subtype.mk s (λ a, id)

@[simp] theorem coe_attach (l : list α) :
 @eq (multiset {x // x ∈ l}) (@attach α l) l.attach := rfl

theorem sizeof_lt_sizeof_of_mem [has_sizeof α] {x : α} {s : multiset α} (hx : x ∈ s) :
  sizeof x < sizeof s := by
{ induction s with l a b, exact list.sizeof_lt_sizeof_of_mem hx, refl }

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
  (a ::ₘ m).attach = ⟨a, mem_cons_self a m⟩ ::ₘ (m.attach.map $ λp, ⟨p.1, mem_cons_of_mem p.2⟩) :=
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

/-! ### Subtraction -/
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

@[simp] theorem sub_cons (a : α) (s t : multiset α) : s - a ::ₘ t = s.erase a - t :=
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

/-! ### Union -/

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

@[simp] theorem map_union [decidable_eq β] {f : α → β} (finj : function.injective f)
  {s t : multiset α} :
  map f (s ∪ t) = map f s ∪ map f t :=
quotient.induction_on₂ s t $ λ l₁ l₂,
congr_arg coe (by rw [list.map_append f, list.map_diff finj])

/-! ### Intersection -/

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
  a ∈ t → (a ::ₘ s) ∩ t = a ::ₘ s ∩ t.erase a :=
quotient.induction_on₂ s t $ λ l₁ l₂ h,
congr_arg coe $ cons_bag_inter_of_pos _ h

@[simp] theorem cons_inter_of_neg {a} (s : multiset α) {t} :
  a ∉ t → (a ::ₘ s) ∩ t = s ∩ t :=
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

theorem cons_union_distrib (a : α) (s t : multiset α) : a ::ₘ (s ∪ t) = (a ::ₘ s) ∪ (a ::ₘ t) :=
by simpa using add_union_distrib (a ::ₘ 0) s t

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

theorem cons_inter_distrib (a : α) (s t : multiset α) : a ::ₘ (s ∩ t) = (a ::ₘ s) ∩ (a ::ₘ t) :=
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

/-! ### `multiset.filter` -/
section
variables (p : α → Prop) [decidable_pred p]

/-- `filter p s` returns the elements in `s` (with the same multiplicities)
  which satisfy `p`, and removes the rest. -/
def filter (s : multiset α) : multiset α :=
quot.lift_on s (λ l, (filter p l : multiset α))
  (λ l₁ l₂ h, quot.sound $ h.filter p)

@[simp] theorem coe_filter (l : list α) : filter p (↑l) = l.filter p := rfl

@[simp] theorem filter_zero : filter p 0 = 0 := rfl

lemma filter_congr {p q : α → Prop} [decidable_pred p] [decidable_pred q]
  {s : multiset α} : (∀ x ∈ s, p x ↔ q x) → filter p s = filter q s :=
quot.induction_on s $ λ l h, congr_arg coe $ filter_congr h

@[simp] theorem filter_add (s t : multiset α) : filter p (s + t) = filter p s + filter p t :=
quotient.induction_on₂ s t $ λ l₁ l₂, congr_arg coe $ filter_append _ _

@[simp] theorem filter_le (s : multiset α) : filter p s ≤ s :=
quot.induction_on s $ λ l, (filter_sublist _).subperm

@[simp] theorem filter_subset (s : multiset α) : filter p s ⊆ s :=
subset_of_le $ filter_le _ _

theorem filter_le_filter {s t} (h : s ≤ t) : filter p s ≤ filter p t :=
le_induction_on h $ λ l₁ l₂ h, (filter_sublist_filter p h).subperm

variable {p}

@[simp] theorem filter_cons_of_pos {a : α} (s) : p a → filter p (a ::ₘ s) = a ::ₘ filter p s :=
quot.induction_on s $ λ l h, congr_arg coe $ filter_cons_of_pos l h

@[simp] theorem filter_cons_of_neg {a : α} (s) : ¬ p a → filter p (a ::ₘ s) = filter p s :=
quot.induction_on s $ λ l h, @congr_arg _ _ _ _ coe $ filter_cons_of_neg l h

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

theorem le_filter {s t} : s ≤ filter p t ↔ s ≤ t ∧ ∀ a ∈ s, p a :=
⟨λ h, ⟨le_trans h (filter_le _ _), λ a m, of_mem_filter (mem_of_le h m)⟩,
 λ ⟨h, al⟩, filter_eq_self.2 al ▸ filter_le_filter p h⟩

variable (p)

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
    { rw [(by rw filter_cons_of_neg _ h : filter p (erase s a) = filter p (a ::ₘ erase s a)),
          cons_erase m] },
    { rw [erase_of_not_mem m] } }
end

@[simp] theorem filter_union [decidable_eq α] (s t : multiset α) :
  filter p (s ∪ t) = filter p s ∪ filter p t :=
by simp [(∪), union]

@[simp] theorem filter_inter [decidable_eq α] (s t : multiset α) :
  filter p (s ∩ t) = filter p s ∩ filter p t :=
le_antisymm (le_inter
    (filter_le_filter _ $ inter_le_left _ _)
    (filter_le_filter _ $ inter_le_right _ _)) $ le_filter.2
⟨inf_le_inf (filter_le _ _) (filter_le _ _),
  λ a h, of_mem_filter (mem_of_le (inter_le_left _ _) h)⟩

@[simp] theorem filter_filter (q) [decidable_pred q] (s : multiset α) :
  filter p (filter q s) = filter (λ a, p a ∧ q a) s :=
quot.induction_on s $ λ l, congr_arg coe $ filter_filter p q l

theorem filter_add_filter (q) [decidable_pred q] (s : multiset α) :
  filter p s + filter q s = filter (λ a, p a ∨ q a) s + filter (λ a, p a ∧ q a) s :=
multiset.induction_on s rfl $ λ a s IH,
by by_cases p a; by_cases q a; simp *

theorem filter_add_not (s : multiset α) :
  filter p s + filter (λ a, ¬ p a) s = s :=
by rw [filter_add_filter, filter_eq_self.2, filter_eq_nil.2]; simp [decidable.em]

theorem map_filter (f : β → α) (s : multiset β) :
  filter p (map f s) = map f (filter (p ∘ f) s) :=
quot.induction_on s (λ l, by simp [map_filter])

/-! ### Simultaneously filter and map elements of a multiset -/

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
  filter_map f (a ::ₘ s) = filter_map f s :=
quot.induction_on s $ λ l, @congr_arg _ _ _ _ coe $ filter_map_cons_none a l h

@[simp] theorem filter_map_cons_some (f : α → option β)
  (a : α) (s : multiset α) {b : β} (h : f a = some b) :
  filter_map f (a ::ₘ s) = b ::ₘ filter_map f s :=
quot.induction_on s $ λ l, @congr_arg _ _ _ _ coe $ filter_map_cons_some f a l h

theorem filter_map_eq_map (f : α → β) : filter_map (some ∘ f) = map f :=
funext $ λ s, quot.induction_on s $ λ l,
@congr_arg _ _ _ _ coe $ congr_fun (filter_map_eq_map f) l

theorem filter_map_eq_filter : filter_map (option.guard p) = filter p :=
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

theorem filter_map_filter (f : α → option β) (s : multiset α) :
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

/-! ### countp -/

/-- `countp p s` counts the number of elements of `s` (with multiplicity) that
  satisfy `p`. -/
def countp (s : multiset α) : ℕ :=
quot.lift_on s (countp p) (λ l₁ l₂, perm.countp_eq p)

@[simp] theorem coe_countp (l : list α) : countp p l = l.countp p := rfl

@[simp] theorem countp_zero : countp p 0 = 0 := rfl

variable {p}

@[simp] theorem countp_cons_of_pos {a : α} (s) : p a → countp p (a ::ₘ s) = countp p s + 1 :=
quot.induction_on s $ countp_cons_of_pos p

@[simp] theorem countp_cons_of_neg {a : α} (s) : ¬ p a → countp p (a ::ₘ s) = countp p s :=
quot.induction_on s $ countp_cons_of_neg p

variable (p)

theorem countp_eq_card_filter (s) : countp p s = card (filter p s) :=
quot.induction_on s $ λ l, countp_eq_length_filter _ _

@[simp] theorem countp_add (s t) : countp p (s + t) = countp p s + countp p t :=
by simp [countp_eq_card_filter]

instance countp.is_add_monoid_hom : is_add_monoid_hom (countp p : multiset α → ℕ) :=
{ map_add := countp_add _, map_zero := countp_zero _ }

@[simp] theorem countp_sub [decidable_eq α] {s t : multiset α} (h : t ≤ s) :
  countp p (s - t) = countp p s - countp p t :=
by simp [countp_eq_card_filter, h, filter_le_filter]

theorem countp_le_of_le {s t} (h : s ≤ t) : countp p s ≤ countp p t :=
by simpa [countp_eq_card_filter] using card_le_of_le (filter_le_filter p h)

@[simp] theorem countp_filter (q) [decidable_pred q] (s : multiset α) :
  countp p (filter q s) = countp (λ a, p a ∧ q a) s :=
by simp [countp_eq_card_filter]

variable {p}

theorem countp_pos {s} : 0 < countp p s ↔ ∃ a ∈ s, p a :=
by simp [countp_eq_card_filter, card_pos_iff_exists_mem]

theorem countp_pos_of_mem {s a} (h : a ∈ s) (pa : p a) : 0 < countp p s :=
countp_pos.2 ⟨_, h, pa⟩

end

/-! ### Multiplicity of an element -/

section
variable [decidable_eq α]

/-- `count a s` is the multiplicity of `a` in `s`. -/
def count (a : α) : multiset α → ℕ := countp (eq a)

@[simp] theorem coe_count (a : α) (l : list α) : count a (↑l) = l.count a := coe_countp _ _

@[simp] theorem count_zero (a : α) : count a 0 = 0 := rfl

@[simp] theorem count_cons_self (a : α) (s : multiset α) : count a (a ::ₘ s) = succ (count a s) :=
countp_cons_of_pos _ rfl

@[simp, priority 990]
theorem count_cons_of_ne {a b : α} (h : a ≠ b) (s : multiset α) : count a (b ::ₘ s) = count a s :=
countp_cons_of_neg _ h

theorem count_le_of_le (a : α) {s t} : s ≤ t → count a s ≤ count a t :=
countp_le_of_le _

theorem count_le_count_cons (a b : α) (s : multiset α) : count a s ≤ count a (b ::ₘ s) :=
count_le_of_le _ (le_cons_self _ _)

theorem count_cons (a b : α) (s : multiset α) :
  count a (b ::ₘ s) = count a s + (if a = b then 1 else 0) :=
by by_cases h : a = b; simp [h]

theorem count_singleton (a : α) : count a (a ::ₘ 0) = 1 :=
by simp

@[simp] theorem count_add (a : α) : ∀ s t, count a (s + t) = count a s + count a t :=
countp_add _

instance count.is_add_monoid_hom (a : α) : is_add_monoid_hom (count a : multiset α → ℕ) :=
countp.is_add_monoid_hom _

@[simp] theorem count_smul (a : α) (n s) : count a (n •ℕ s) = n * count a s :=
by induction n; simp [*, succ_nsmul', succ_mul]

theorem count_pos {a : α} {s : multiset α} : 0 < count a s ↔ a ∈ s :=
by simp [count, countp_pos]

@[simp, priority 980]
theorem count_eq_zero_of_not_mem {a : α} {s : multiset α} (h : a ∉ s) : count a s = 0 :=
by_contradiction $ λ h', h $ count_pos.1 (nat.pos_of_ne_zero h')

@[simp] theorem count_eq_zero {a : α} {s : multiset α} : count a s = 0 ↔ a ∉ s :=
iff_not_comm.1 $ count_pos.symm.trans pos_iff_ne_zero

theorem count_ne_zero {a : α} {s : multiset α} : count a s ≠ 0 ↔ a ∈ s :=
by simp [ne.def, count_eq_zero]

@[simp] theorem count_repeat_self (a : α) (n : ℕ) : count a (repeat a n) = n :=
by simp [repeat]

theorem count_repeat (a b : α) (n : ℕ)  :
  count a (repeat b n) = if (a = b) then n else 0 :=
begin
  split_ifs with h₁,
  { rw [h₁, count_repeat_self] },
  { rw [count_eq_zero],
    apply mt eq_of_mem_repeat h₁ },
end

@[simp] theorem count_erase_self (a : α) (s : multiset α) :
  count a (erase s a) = pred (count a s) :=
begin
  by_cases a ∈ s,
  { rw [(by rw cons_erase h : count a s = count a (a ::ₘ erase s a)),
        count_cons_self]; refl },
  { rw [erase_of_not_mem h, count_eq_zero.2 h]; refl }
end

@[simp, priority 980] theorem count_erase_of_ne {a b : α} (ab : a ≠ b) (s : multiset α) :
  count a (erase s b) = count a s :=
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

@[simp] theorem count_union (a : α) (s t : multiset α) :
  count a (s ∪ t) = max (count a s) (count a t) :=
by simp [(∪), union, sub_add_eq_max, -add_comm]

@[simp] theorem count_inter (a : α) (s t : multiset α) :
  count a (s ∩ t) = min (count a s) (count a t) :=
begin
  apply @nat.add_left_cancel (count a (s - t)),
  rw [← count_add, sub_add_inter, count_sub, sub_add_min],
end

lemma count_sum {m : multiset β} {f : β → multiset α} {a : α} :
  count a (map f m).sum = sum (m.map $ λb, count a $ f b) :=
multiset.induction_on m (by simp) ( by simp)

lemma count_bind {m : multiset β} {f : β → multiset α} {a : α} :
  count a (bind m f) = sum (m.map $ λb, count a $ f b) := count_sum

@[simp] lemma count_map_equiv [decidable_eq β] {m : multiset α} {f : α ≃ β} {b : β} :
  count b (m.map f) = count (f.symm b) m :=
multiset.induction_on m (by simp) (λ a s h, by simp [h, map_cons, count_cons, f.symm_apply_eq])

theorem le_count_iff_repeat_le {a : α} {s : multiset α} {n : ℕ} : n ≤ count a s ↔ repeat a n ≤ s :=
quot.induction_on s $ λ l, le_count_iff_repeat_sublist.trans repeat_le_coe.symm

@[simp] theorem count_filter_of_pos {p} [decidable_pred p]
  {a} {s : multiset α} (h : p a) : count a (filter p s) = count a s :=
quot.induction_on s $ λ l, count_filter h

@[simp] theorem count_filter_of_neg {p} [decidable_pred p]
  {a} {s : multiset α} (h : ¬ p a) : count a (filter p s) = 0 :=
multiset.count_eq_zero_of_not_mem (λ t, h (of_mem_filter t))

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

@[simp]
lemma mem_nsmul {a : α} {s : multiset α} {n : ℕ} (h0 : n ≠ 0) :
  a ∈ n •ℕ s ↔ a ∈ s :=
begin
  classical,
  cases n,
  { exfalso, apply h0 rfl },
  rw [← not_iff_not, ← count_eq_zero, ← count_eq_zero],
  simp [h0],
end

/-! ### Lift a relation to `multiset`s -/

section rel

/-- `rel r s t` -- lift the relation `r` between two elements to a relation between `s` and `t`,
s.t. there is a one-to-one mapping betweem elements in `s` and `t` following `r`. -/
@[mk_iff] inductive rel (r : α → β → Prop) : multiset α → multiset β → Prop
| zero : rel 0 0
| cons {a b as bs} : r a b → rel as bs → rel (a ::ₘ as) (b ::ₘ bs)

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
  rel r (a ::ₘ as) bs ↔ (∃b bs', r a b ∧ rel r as bs' ∧ bs = b ::ₘ bs') :=
begin
  split,
  { generalize hm : a ::ₘ as = m,
    assume h,
    induction h generalizing as,
    case rel.zero { simp at hm, contradiction },
    case rel.cons : a' b as' bs ha'b h ih {
      rcases cons_eq_cons.1 hm with ⟨eq₁, eq₂⟩ | ⟨h, cs, eq₁, eq₂⟩,
      { subst eq₁, subst eq₂, exact ⟨b, bs, ha'b, h, rfl⟩ },
      { rcases ih eq₂.symm with ⟨b', bs', h₁, h₂, eq⟩,
        exact ⟨b', b ::ₘ bs', h₁, eq₁.symm ▸ rel.cons ha'b h₂, eq.symm ▸ cons_swap _ _ _⟩  }
    } },
  { exact assume ⟨b, bs', hab, h, eq⟩, eq.symm ▸ rel.cons hab h }
end

lemma rel_cons_right {as b bs} :
  rel r as (b ::ₘ bs) ↔ (∃a as', r a b ∧ rel r as' bs ∧ as = a ::ₘ as') :=
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
      exact ⟨b ::ₘ bs₀, bs₁, ⟨b, bs₀, hab, h₀, rfl⟩, h₁, by simp⟩ },
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

lemma exists_mem_of_rel_of_mem {r : α → β → Prop} {s : multiset α} {t : multiset β}
  (h : rel r s t) :
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

theorem map_injective {f : α → β} (hf : function.injective f) :
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
  assume a s ⟨t, ht⟩, quot.induction_on a $ assume a, ht.symm ▸ ⟨a ::ₘ t, (map_cons _ _ _).symm⟩

theorem induction_on_multiset_quot
  {r : α → α → Prop} {p : multiset (quot r) → Prop} (s : multiset (quot r)) :
  (∀s:multiset α, p (s.map (quot.mk r))) → p s :=
match s, exists_multiset_eq_map_quot_mk s with _, ⟨t, rfl⟩ := assume h, h _ end

end quot

/-! ### Disjoint multisets -/

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
theorem singleton_disjoint {l : multiset α} {a : α} : disjoint (a ::ₘ 0) l ↔ a ∉ l :=
by simp [disjoint]; refl

@[simp, priority 1100]
theorem disjoint_singleton {l : multiset α} {a : α} : disjoint l (a ::ₘ 0) ↔ a ∉ l :=
by rw disjoint_comm; simp

@[simp] theorem disjoint_add_left {s t u : multiset α} :
  disjoint (s + t) u ↔ disjoint s u ∧ disjoint t u :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_add_right {s t u : multiset α} :
  disjoint s (t + u) ↔ disjoint s t ∧ disjoint s u :=
by rw [disjoint_comm, disjoint_add_left]; tauto

@[simp] theorem disjoint_cons_left {a : α} {s t : multiset α} :
  disjoint (a ::ₘ s) t ↔ a ∉ t ∧ disjoint s t :=
(@disjoint_add_left _ (a ::ₘ 0) s t).trans $ by simp

@[simp] theorem disjoint_cons_right {a : α} {s t : multiset α} :
  disjoint s (a ::ₘ t) ↔ a ∉ s ∧ disjoint s t :=
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
by { simp [disjoint, @eq_comm _ (f _) (g _)], refl }

/-- `pairwise r m` states that there exists a list of the elements s.t. `r` holds pairwise on this
list. -/
def pairwise (r : α → α → Prop) (m : multiset α) : Prop :=
∃l:list α, m = l ∧ l.pairwise r

lemma pairwise_coe_iff_pairwise {r : α → α → Prop} (hr : symmetric r) {l : list α} :
  multiset.pairwise r l ↔ l.pairwise r :=
iff.intro
  (assume ⟨l', eq, h⟩, ((quotient.exact eq).pairwise_iff hr).2 h)
  (assume h, ⟨l, rfl, h⟩)

end multiset

namespace multiset

section choose
variables (p : α → Prop) [decidable_pred p] (l : multiset α)

/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `choose_x p l hp` returns
that `a` together with proofs of `a ∈ l` and `p a`. -/
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

/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `choose p l hp` returns
that `a`. -/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α := choose_x p l hp

lemma choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
(choose_x p l hp).property

lemma choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l := (choose_spec _ _ _).1

lemma choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) := (choose_spec _ _ _).2

end choose

variable (α)

/-- The equivalence between lists and multisets of a subsingleton type. -/
def subsingleton_equiv [subsingleton α] : list α ≃ multiset α :=
{ to_fun := coe,
  inv_fun := quot.lift id $ λ (a b : list α) (h : a ~ b),
    list.ext_le h.length_eq $ λ n h₁ h₂, subsingleton.elim _ _,
  left_inv := λ l, rfl,
  right_inv := λ m, quot.induction_on m $ λ l, rfl }

variable {α}

@[simp]
lemma coe_subsingleton_equiv [subsingleton α] :
  (subsingleton_equiv α : list α → multiset α) = coe :=
rfl

end multiset

@[to_additive]
theorem monoid_hom.map_multiset_prod [comm_monoid α] [comm_monoid β] (f : α →* β) (s : multiset α) :
  f s.prod = (s.map f).prod :=
(s.prod_hom f).symm
