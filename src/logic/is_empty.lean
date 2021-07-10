/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import logic.basic
import tactic.protected
/-!
# Types that are empty

In this file we define a typeclass `is_empty`, which expresses that a type has no elements.

## Main declaration

* `is_empty`: a typeclass that expresses that a type is empty.
-/

variables {α β γ : Sort*}

/-- `is_empty α` expresses that `α` is empty. -/
@[protect_proj]
class is_empty (α : Sort*) : Prop :=
(false : α → false)

instance : is_empty empty   := ⟨empty.elim⟩
instance : is_empty pempty  := ⟨pempty.elim⟩
instance : is_empty false   := ⟨id⟩
instance : is_empty (fin 0) := ⟨λ n, nat.not_lt_zero n.1 n.2⟩

protected lemma function.is_empty [is_empty β] (f : α → β) : is_empty α :=
⟨λ x, is_empty.false (f x)⟩

instance {p : α → Sort*} [h : nonempty α] [∀ x, is_empty (p x)] : is_empty (Π x, p x) :=
h.elim $ λ x, function.is_empty $ function.eval x
instance pprod.is_empty_left [is_empty α] : is_empty (pprod α β) :=
function.is_empty pprod.fst
instance pprod.is_empty_right [is_empty β] : is_empty (pprod α β) :=
function.is_empty pprod.snd
instance prod.is_empty_left {α β} [is_empty α] : is_empty (α × β) :=
function.is_empty prod.fst
instance prod.is_empty_right {α β} [is_empty β] : is_empty (α × β) :=
function.is_empty prod.snd
instance [is_empty α] [is_empty β] : is_empty (psum α β) :=
⟨λ x, psum.rec is_empty.false is_empty.false x⟩
instance {α β} [is_empty α] [is_empty β] : is_empty (α ⊕ β) :=
⟨λ x, sum.rec is_empty.false is_empty.false x⟩
/-- subtypes of an empty type are empty -/
instance [is_empty α] (p : α → Prop) : is_empty (subtype p) :=
⟨λ x, is_empty.false x.1⟩
/-- subtypes by an all-false predicate are false. -/
lemma subtype.is_empty_of_false {p : α → Prop} (hp : ∀ a, ¬(p a)) : is_empty (subtype p) :=
⟨λ x, hp _ x.2⟩
/-- subtypes by false are false. -/
instance subtype.is_empty_false : is_empty {a : α // false} :=
subtype.is_empty_of_false (λ a, id)

/- Test that `pi.is_empty` finds this instance. -/
example [h : nonempty α] [is_empty β] : is_empty (α → β) := by apply_instance

/-- Eliminate out of a type that `is_empty` (without using projection notation). -/
@[elab_as_eliminator]
def is_empty_elim [is_empty α] {p : α → Sort*} (a : α) : p a :=
(is_empty.false a).elim

lemma is_empty_iff : is_empty α ↔ α → false :=
⟨@is_empty.false α, is_empty.mk⟩

namespace is_empty
open function
/-- Eliminate out of a type that `is_empty` (using projection notation). -/
protected def elim (h : is_empty α) {p : α → Sort*} (a : α) : p a :=
is_empty_elim a

/-- Non-dependent version of `is_empty.elim`. Helpful if the elaborator cannot elaborate `h.elim a`
  correctly. -/
protected def elim' {β : Sort*} (h : is_empty α) (a : α) : β :=
h.elim a

protected lemma prop_iff {p : Prop} : is_empty p ↔ ¬ p :=
is_empty_iff

variables [is_empty α]

lemma forall_iff {p : α → Prop} : (∀ a, p a) ↔ true :=
iff_true_intro is_empty_elim

lemma exists_iff {p : α → Prop} : (∃ a, p a) ↔ false :=
iff_false_intro $ λ ⟨x, hx⟩, is_empty.false x

@[priority 100] -- see Note [lower instance priority]
instance : subsingleton α := ⟨is_empty_elim⟩

end is_empty

@[simp] lemma not_nonempty_iff : ¬ nonempty α ↔ is_empty α :=
⟨λ h, ⟨λ x, h ⟨x⟩⟩, λ h1 h2, h2.elim h1.elim⟩

@[simp] lemma not_is_empty_iff : ¬ is_empty α ↔ nonempty α :=
not_iff_comm.mp not_nonempty_iff

variables (α)

lemma is_empty_or_nonempty : is_empty α ∨ nonempty α :=
(em $ is_empty α).elim or.inl $ or.inr ∘ not_is_empty_iff.mp

@[simp] lemma not_is_empty_of_nonempty [h : nonempty α] : ¬ is_empty α :=
not_is_empty_iff.mpr h
