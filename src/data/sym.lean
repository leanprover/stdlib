/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/

import data.multiset.basic
import data.vector2

/-!
# Symmetric powers

This file defines symmetric powers of a type.  The nth symmetric power
consists of homogeneous n-tuples modulo permutations by the symmetric
group.

The special case of 2-tuples is called the symmetric square, which is
addressed in more detail in `data.sym2`.

TODO: This was created as supporting material for `data.sym2`; it
needs a fleshed-out interface.

## Tags

symmetric powers

-/

universes u

/--
The nth symmetric power is n-tuples up to permutation.  We define it
as a subtype of `multiset` since these are well developed in the
library.  We also give a definition `sym.sym'` in terms of vectors, and we
show these are equivalent in `sym.sym_equiv_sym'`.
-/
def sym (α : Type u) (n : ℕ) := {s : multiset α // s.card = n}

/--
This is the `list.perm` setoid lifted to `vector`.
-/
def vector.perm.is_setoid (α : Type u) (n : ℕ) : setoid (vector α n) :=
{ r := λ a b, list.perm a.1 b.1,
  iseqv := by { rcases list.perm.eqv α with ⟨hr, hs, ht⟩, tidy, } }

local attribute [instance] vector.perm.is_setoid

namespace sym

variables {α : Type u} {n : ℕ}

/--
This is the quotient map that takes a list of n elements as an n-tuple and produces an nth
symmetric power.
-/
def of_vector (x : vector α n) : sym α n :=
⟨↑x.val, by { rw multiset.coe_card, exact x.2 }⟩

instance : has_lift (vector α n) (sym α n) :=
{ lift := of_vector }

/--
The unique element in `sym α 0`.
-/
@[pattern] def nil : sym α 0 := ⟨0, by tidy⟩

/--
Inserts an element into the term of `sym α n`, increasing the length by one.
-/
@[pattern] def cons : α → sym α n → sym α (nat.succ n)
| a ⟨s, h⟩ := ⟨a ::ₘ s, by rw [multiset.card_cons, h]⟩

notation a :: b := cons a b

@[simp]
lemma cons_inj_right (a : α) (s s' : sym α n) : a :: s = a :: s' ↔ s = s' :=
by { cases s, cases s', delta cons, simp, }

@[simp]
lemma cons_inj_left (a a' : α) (s : sym α n) : a :: s = a' :: s ↔ a = a' :=
by { cases s, delta cons, simp, }

lemma cons_swap (a b : α) (s : sym α n) : a :: b :: s = b :: a :: s :=
by { cases s, ext, delta cons, rw subtype.coe_mk, dsimp, exact multiset.cons_swap a b s_val }

/--
`α ∈ s` means that `a` appears as one of the factors in `s`.
-/
def mem (a : α) (s : sym α n) : Prop := a ∈ s.1

instance : has_mem α (sym α n) := ⟨mem⟩

instance decidable_mem [decidable_eq α] (a : α) (s : sym α n) : decidable (a ∈ s) :=
by { cases s, change decidable (a ∈ s_val), apply_instance }

@[simp] lemma mem_cons {a b : α} {s : sym α n} : a ∈ b :: s ↔ a = b ∨ a ∈ s :=
begin cases s, change a ∈ b ::ₘ s_val ↔ a = b ∨ a ∈ s_val, simp, end

lemma mem_cons_of_mem {a b : α} {s : sym α n} (h : a ∈ s) : a ∈ b :: s :=
mem_cons.2 (or.inr h)

@[simp] lemma mem_cons_self (a : α) (s : sym α n) : a ∈ a :: s :=
mem_cons.2 (or.inl rfl)

lemma cons_of_coe_eq (a : α) (v : vector α n) : a :: (↑v : sym α n) = ↑(a ::ᵥ v) :=
by { unfold_coes, delta of_vector, delta cons, delta vector.cons, tidy }

lemma sound {a b : vector α n} (h : a.val ~ b.val) : (↑a : sym α n) = ↑b :=
begin
  cases a, cases b, unfold_coes, dunfold of_vector,
  simp only [subtype.mk_eq_mk, multiset.coe_eq_coe],
  exact h,
end

/--
Another definition of the nth symmetric power, using vectors modulo permutations. (See `sym`.)
-/
def sym' (α : Type u) (n : ℕ) := quotient (vector.perm.is_setoid α n)

/--
This is `cons` but for the alternative `sym'` definition.
-/
def cons' {α : Type u} {n : ℕ} : α → sym' α n → sym' α (nat.succ n) :=
λ a, quotient.map (vector.cons a) (λ ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h, list.perm.cons _ h)

notation a :: b := cons' a b

/--
Multisets of cardinality n are equivalent to length-n vectors up to permutations.
-/
def sym_equiv_sym' {α : Type u} {n : ℕ} : sym α n ≃ sym' α n :=
equiv.subtype_quotient_equiv_quotient_subtype _ _ (λ _, by refl) (λ _ _, by refl)

lemma cons_equiv_eq_equiv_cons (α : Type u) (n : ℕ) (a : α) (s : sym α n) :
  a :: sym_equiv_sym' s = sym_equiv_sym' (a :: s) :=
by tidy

section inhabited
-- Instances to make the linter happy

instance inhabited_sym [inhabited α] (n : ℕ) : inhabited (sym α n) :=
⟨⟨multiset.repeat (default α) n, multiset.card_repeat _ _⟩⟩

instance inhabited_sym' [inhabited α] (n : ℕ) : inhabited (sym' α n) :=
⟨quotient.mk' (vector.repeat (default α) n)⟩

end inhabited

end sym
