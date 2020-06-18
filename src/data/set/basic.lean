/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import tactic.basic
import tactic.finish
import data.subtype
import logic.unique
import data.prod

/-!
# Basic properties of sets

Sets in Lean are homogeneous; all their elements have the same type. Sets whose elements
have type `X` are thus defined as `set X := X → Prop`. Note that this function need not
be decidable. The definition is in the core library.

This file provides some basic definitions related to sets and functions not present in the core
library, as well as extra lemmas for functions in the core library (empty set, univ, union,
intersection, insert, singleton, set-theoretic difference, complement, and powerset).

Note that a set is a term, not a type. There is a coersion from `set α` to `Type*` sending
`s` to the corresponding subtype `↑s`.

See also the file `set_theory/zfc.lean`, which contains an encoding of ZFC set theory in Lean.

## Main definitions

Notation used here:

-  `f : α → β` is a function,

-  `s : set α` and `s₁ s₂ : set α` are subsets of `α`

-  `t : set β` is a subset of `β`.

Definitions in the file:

* `strict_subset s₁ s₂ : Prop` : the predicate `s₁ ⊆ s₂` but `s₁ ≠ s₂`.

* `nonempty s : Prop` : the predicate `s ≠ ∅`. Note that this is the preferred way to express the
  fact that `s` has an element (see the Implementation Notes).

* `preimage f t : set α` : the preimage f⁻¹(t) (written `f ⁻¹' t` in Lean) of a subset of β.

* `subsingleton s : Prop` : the predicate saying that `s` has at most one element.

* `range f : set β` : the image of `univ` under `f`.
  Also works for `{p : Prop} (f : p → α)` (unlike `image`)

* `prod s t : set (α × β)` : the subset `s × t`.

* `inclusion s₁ s₂ : ↑s₁ → ↑s₂` : the map `↑s₁ → ↑s₂` induced by an inclusion `s₁ ⊆ s₂`.

## Notation

* `f ⁻¹' t` for `preimage f t`

* `f '' s` for `image f s`

## Implementation notes

`s.nonempty` is to be preferred to `s ≠ ∅` or `∃ x, x ∈ s`. It has the advantage that
the `s.nonempty` dot notation can be used.

## Tags

set, sets, subset, subsets, image, preimage, pre-image, range, union, intersection, insert,
singleton, complement, powerset

-/

/-! ### Set coercion to a type -/

open function

namespace set

/-- Coercion from a set to the corresponding subtype. -/
instance {α : Type*} : has_coe_to_sort (set α) := ⟨_, λ s, {x // x ∈ s}⟩

end set

section set_coe

universe u

variables {α : Type u}

theorem set.set_coe_eq_subtype (s : set α) :
  coe_sort.{(u+1) (u+2)} s = {x // x ∈ s} := rfl

@[simp] theorem set_coe.forall {s : set α} {p : s → Prop} :
  (∀ x : s, p x) ↔ (∀ x (h : x ∈ s), p ⟨x, h⟩) :=
subtype.forall

@[simp] theorem set_coe.exists {s : set α} {p : s → Prop} :
  (∃ x : s, p x) ↔ (∃ x (h : x ∈ s), p ⟨x, h⟩) :=
subtype.exists

theorem set_coe.exists' {s : set α} {p : Π x, x ∈ s → Prop} :
  (∃ x (h : x ∈ s), p x h) ↔ (∃ x : s, p x.1 x.2)  :=
(@set_coe.exists _ _ $ λ x, p x.1 x.2).symm

@[simp] theorem set_coe_cast : ∀ {s t : set α} (H' : s = t) (H : @eq (Type u) s t) (x : s),
  cast H x = ⟨x.1, H' ▸ x.2⟩
| s _ rfl _ ⟨x, h⟩ := rfl

theorem set_coe.ext {s : set α} {a b : s} : (↑a : α) = ↑b → a = b :=
subtype.eq

theorem set_coe.ext_iff {s : set α} {a b : s} : (↑a : α) = ↑b ↔ a = b :=
iff.intro set_coe.ext (assume h, h ▸ rfl)

end set_coe

lemma subtype.mem {α : Type*} {s : set α} (p : s) : (p : α) ∈ s := p.property

namespace set

universes u v w x

variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {a : α} {s t : set α}

instance : inhabited (set α) := ⟨∅⟩

@[ext]
theorem ext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
funext (assume x, propext (h x))

theorem ext_iff {s t : set α} : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t :=
⟨λ h x, by rw h, ext⟩

@[trans] theorem mem_of_mem_of_subset {x : α} {s t : set α} (hx : x ∈ s) (h : s ⊆ t) : x ∈ t := h hx

/-! ### Lemmas about `mem` and `set_of` -/

@[simp] theorem mem_set_of_eq {a : α} {p : α → Prop} : a ∈ {a | p a} = p a := rfl

theorem nmem_set_of_eq {a : α} {P : α → Prop} : a ∉ {a : α | P a} = ¬ P a := rfl

@[simp] theorem set_of_mem_eq {s : set α} : {x | x ∈ s} = s := rfl

lemma set_of_app_iff {p : α → Prop} {x : α} : { x | p x } x ↔ p x := iff.rfl

theorem mem_def {a : α} {s : set α} : a ∈ s ↔ s a := iff.rfl

instance decidable_mem (s : set α) [H : decidable_pred s] : ∀ a, decidable (a ∈ s) := H

instance decidable_set_of (p : α → Prop) [H : decidable_pred p] : decidable_pred {a | p a} := H

@[simp] theorem set_of_subset_set_of {p q : α → Prop} :
  {a | p a} ⊆ {a | q a} ↔ (∀a, p a → q a) := iff.rfl

@[simp] lemma sep_set_of {α} {p q : α → Prop} : {a ∈ {a | p a } | q a} = {a | p a ∧ q a} := rfl

/-! ### Lemmas about subsets -/

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
theorem subset_def {s t : set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := rfl

@[refl] theorem subset.refl (a : set α) : a ⊆ a := assume x, id

@[trans] theorem subset.trans {a b c : set α} (ab : a ⊆ b) (bc : b ⊆ c) : a ⊆ c :=
assume x h, bc (ab h)

@[trans] theorem mem_of_eq_of_mem {x y : α} {s : set α} (hx : x = y) (h : y ∈ s) : x ∈ s :=
hx.symm ▸ h

theorem subset.antisymm {a b : set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
ext (λ x, iff.intro (λ ina, h₁ ina) (λ inb, h₂ inb))

theorem subset.antisymm_iff {a b : set α} : a = b ↔ a ⊆ b ∧ b ⊆ a :=
⟨λ e, e ▸ ⟨subset.refl _, subset.refl _⟩,
 λ ⟨h₁, h₂⟩, subset.antisymm h₁ h₂⟩

-- an alternative name
theorem eq_of_subset_of_subset {a b : set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
subset.antisymm h₁ h₂

theorem mem_of_subset_of_mem {s₁ s₂ : set α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
assume h₁ h₂, h₁ h₂

theorem not_subset : (¬ s ⊆ t) ↔ ∃a ∈ s, a ∉ t :=
by simp [subset_def, classical.not_forall]

/-! ### Definition of strict subsets `s ⊂ t` and basic properties. -/

/-- `s ⊂ t` means that `s` is a strict subset of `t`, that is, `s ⊆ t` but `s ≠ t`. -/
def strict_subset (s t : set α) := s ⊆ t ∧ ¬ (t ⊆ s)

instance : has_ssubset (set α) := ⟨strict_subset⟩

theorem ssubset_def : (s ⊂ t) = (s ⊆ t ∧ ¬ (t ⊆ s)) := rfl

theorem eq_or_ssubset_of_subset (h : s ⊆ t) : s = t ∨ s ⊂ t :=
classical.by_cases
  (λ H : t ⊆ s, or.inl $ subset.antisymm h H)
  (λ H, or.inr ⟨h, H⟩)

lemma exists_of_ssubset {s t : set α} (h : s ⊂ t) : (∃x∈t, x ∉ s) :=
not_subset.1 h.2

lemma ssubset_iff_subset_ne {s t : set α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
by split; simp [set.ssubset_def, ne.def, set.subset.antisymm_iff] {contextual := tt}

lemma ssubset_iff_of_subset {s t : set α} (h : s ⊆ t) : s ⊂ t ↔ ∃ x ∈ t, x ∉ s :=
⟨exists_of_ssubset, λ ⟨x, hxt, hxs⟩, ⟨h, λ h, hxs $ h hxt⟩⟩

theorem not_mem_empty (x : α) : ¬ (x ∈ (∅ : set α)) :=
assume h : x ∈ ∅, h

@[simp] theorem not_not_mem : ¬ (a ∉ s) ↔ a ∈ s :=
by { classical, exact not_not }

/-! ### Non-empty sets -/

/-- The property `s.nonempty` expresses the fact that the set `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def nonempty (s : set α) : Prop := ∃ x, x ∈ s

lemma nonempty_of_mem {x} (h : x ∈ s) : s.nonempty := ⟨x, h⟩

theorem nonempty.not_subset_empty : s.nonempty  → ¬(s ⊆ ∅)
| ⟨x, hx⟩ hs := hs hx

theorem nonempty.ne_empty : s.nonempty → s ≠ ∅
| ⟨x, hx⟩ hs := by { rw hs at hx, exact hx }

/-- Extract a witness from `s.nonempty`. This function might be used instead of case analysis
on the argument. Note that it makes a proof depend on the `classical.choice` axiom. -/
protected noncomputable def nonempty.some (h : s.nonempty) : α := classical.some h

protected lemma nonempty.some_mem (h : s.nonempty) : h.some ∈ s := classical.some_spec h

lemma nonempty.mono (ht : s ⊆ t) (hs : s.nonempty) : t.nonempty := hs.imp ht

lemma nonempty_of_ssubset (ht : s ⊂ t) : (t \ s).nonempty :=
let ⟨x, xt, xs⟩ := exists_of_ssubset ht in ⟨x, xt, xs⟩

lemma nonempty.of_diff (h : (s \ t).nonempty) : s.nonempty := h.imp $ λ _, and.left

lemma nonempty_of_ssubset' (ht : s ⊂ t) : t.nonempty := (nonempty_of_ssubset ht).of_diff

lemma nonempty.inl (hs : s.nonempty) : (s ∪ t).nonempty := hs.imp $ λ _, or.inl

lemma nonempty.inr (ht : t.nonempty) : (s ∪ t).nonempty := ht.imp $ λ _, or.inr

@[simp] lemma union_nonempty : (s ∪ t).nonempty ↔ s.nonempty ∨ t.nonempty := exists_or_distrib

lemma nonempty.left (h : (s ∩ t).nonempty) : s.nonempty := h.imp $ λ _, and.left

lemma nonempty.right (h : (s ∩ t).nonempty) : t.nonempty := h.imp $ λ _, and.right

lemma nonempty_iff_univ_nonempty : nonempty α ↔ (univ : set α).nonempty :=
⟨λ ⟨x⟩, ⟨x, trivial⟩, λ ⟨x, _⟩, ⟨x⟩⟩

@[simp] lemma univ_nonempty : ∀ [h : nonempty α], (univ : set α).nonempty
| ⟨x⟩ := ⟨x, trivial⟩

lemma nonempty.to_subtype (h : s.nonempty) : nonempty s :=
nonempty_subtype.2 h

/-! ### Lemmas about the empty set -/

theorem empty_def : (∅ : set α) = {x | false} := rfl

@[simp] theorem mem_empty_eq (x : α) : x ∈ (∅ : set α) = false := rfl

@[simp] theorem set_of_false : {a : α | false} = ∅ := rfl

theorem eq_empty_iff_forall_not_mem {s : set α} : s = ∅ ↔ ∀ x, x ∉ s :=
by simp [ext_iff]

@[simp] theorem empty_subset (s : set α) : ∅ ⊆ s :=
assume x, assume h, false.elim h

theorem subset_empty_iff {s : set α} : s ⊆ ∅ ↔ s = ∅ :=
by simp [subset.antisymm_iff]

theorem eq_empty_of_subset_empty {s : set α} : s ⊆ ∅ → s = ∅ :=
subset_empty_iff.1

lemma not_nonempty_iff_eq_empty {s : set α} : ¬s.nonempty ↔ s = ∅ :=
by simp only [set.nonempty, eq_empty_iff_forall_not_mem, not_exists]

lemma empty_not_nonempty : ¬(∅ : set α).nonempty :=
not_nonempty_iff_eq_empty.2 rfl

lemma eq_empty_or_nonempty (s : set α) : s = ∅ ∨ s.nonempty :=
classical.by_cases or.inr (λ h, or.inl $ not_nonempty_iff_eq_empty.1 h)

theorem ne_empty_iff_nonempty : s ≠ ∅ ↔ s.nonempty :=
(not_congr not_nonempty_iff_eq_empty.symm).trans classical.not_not

theorem subset_eq_empty {s t : set α} (h : t ⊆ s) (e : s = ∅) : t = ∅ :=
subset_empty_iff.1 $ e ▸ h

theorem ball_empty_iff {p : α → Prop} :
  (∀ x ∈ (∅ : set α), p x) ↔ true :=
by simp [iff_def]

/-!

### Universal set.

In Lean `@univ α` (or `univ : set α`) is the set that contains all elements of type `α`.
Mathematically it is the same as `α` but it has a different type.

-/

theorem univ_def : @univ α = {x | true} := rfl

@[simp] theorem mem_univ (x : α) : x ∈ @univ α := trivial

theorem empty_ne_univ [h : nonempty α] : (∅ : set α) ≠ univ :=
by simp [ext_iff]

@[simp] theorem subset_univ (s : set α) : s ⊆ univ := λ x H, trivial

theorem univ_subset_iff {s : set α} : univ ⊆ s ↔ s = univ :=
by simp [subset.antisymm_iff]

theorem eq_univ_of_univ_subset {s : set α} : univ ⊆ s → s = univ :=
univ_subset_iff.1

theorem eq_univ_iff_forall {s : set α} : s = univ ↔ ∀ x, x ∈ s :=
by simp [ext_iff]

theorem eq_univ_of_forall {s : set α} : (∀ x, x ∈ s) → s = univ := eq_univ_iff_forall.2

@[simp] lemma univ_eq_empty_iff : (univ : set α) = ∅ ↔ ¬ nonempty α :=
eq_empty_iff_forall_not_mem.trans ⟨λ H ⟨x⟩, H x trivial, λ H x _, H ⟨x⟩⟩

lemma exists_mem_of_nonempty (α) : ∀ [nonempty α], ∃x:α, x ∈ (univ : set α)
| ⟨x⟩ := ⟨x, trivial⟩

instance univ_decidable : decidable_pred (@set.univ α) :=
λ x, is_true trivial

/-! ### Lemmas about union -/

theorem union_def {s₁ s₂ : set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂} := rfl

theorem mem_union_left {x : α} {a : set α} (b : set α) : x ∈ a → x ∈ a ∪ b := or.inl

theorem mem_union_right {x : α} {b : set α} (a : set α) : x ∈ b → x ∈ a ∪ b := or.inr

theorem mem_or_mem_of_mem_union {x : α} {a b : set α} (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b := H

theorem mem_union.elim {x : α} {a b : set α} {P : Prop}
    (H₁ : x ∈ a ∪ b) (H₂ : x ∈ a → P) (H₃ : x ∈ b → P) : P :=
or.elim H₁ H₂ H₃

theorem mem_union (x : α) (a b : set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := iff.rfl

@[simp] theorem mem_union_eq (x : α) (a b : set α) : x ∈ a ∪ b = (x ∈ a ∨ x ∈ b) := rfl

@[simp] theorem union_self (a : set α) : a ∪ a = a :=
ext (assume x, or_self _)

@[simp] theorem union_empty (a : set α) : a ∪ ∅ = a :=
ext (assume x, or_false _)

@[simp] theorem empty_union (a : set α) : ∅ ∪ a = a :=
ext (assume x, false_or _)

theorem union_comm (a b : set α) : a ∪ b = b ∪ a :=
ext (assume x, or.comm)

theorem union_assoc (a b c : set α) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
ext (assume x, or.assoc)

instance union_is_assoc : is_associative (set α) (∪) :=
⟨union_assoc⟩

instance union_is_comm : is_commutative (set α) (∪) :=
⟨union_comm⟩

theorem union_left_comm (s₁ s₂ s₃ : set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
by finish

theorem union_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
by finish

theorem union_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∪ t = t :=
by finish [subset_def, ext_iff, iff_def]

theorem union_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∪ t = s :=
by finish [subset_def, ext_iff, iff_def]

@[simp] theorem subset_union_left (s t : set α) : s ⊆ s ∪ t := λ x, or.inl

@[simp] theorem subset_union_right (s t : set α) : t ⊆ s ∪ t := λ x, or.inr

theorem union_subset {s t r : set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
by finish [subset_def, union_def]

@[simp] theorem union_subset_iff {s t u : set α} : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
by finish [iff_def, subset_def]

theorem union_subset_union {s₁ s₂ t₁ t₂ : set α} (h₁ : s₁ ⊆ s₂) (h₂ : t₁ ⊆ t₂) : s₁ ∪ t₁ ⊆ s₂ ∪ t₂ :=
by finish [subset_def]

theorem union_subset_union_left {s₁ s₂ : set α} (t) (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
union_subset_union h (by refl)

theorem union_subset_union_right (s) {t₁ t₂ : set α} (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
union_subset_union (by refl) h

lemma subset_union_of_subset_left {s t : set α} (h : s ⊆ t) (u : set α) : s ⊆ t ∪ u :=
subset.trans h (subset_union_left t u)

lemma subset_union_of_subset_right {s u : set α} (h : s ⊆ u) (t : set α) : s ⊆ t ∪ u :=
subset.trans h (subset_union_right t u)

@[simp] theorem union_empty_iff {s t : set α} : s ∪ t = ∅ ↔ s = ∅ ∧ t = ∅ :=
⟨by finish [ext_iff], by finish [ext_iff]⟩

/-! ### Lemmas about intersection -/

theorem inter_def {s₁ s₂ : set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂} := rfl

theorem mem_inter_iff (x : α) (a b : set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := iff.rfl

@[simp] theorem mem_inter_eq (x : α) (a b : set α) : x ∈ a ∩ b = (x ∈ a ∧ x ∈ b) := rfl

theorem mem_inter {x : α} {a b : set α} (ha : x ∈ a) (hb : x ∈ b) : x ∈ a ∩ b :=
⟨ha, hb⟩

theorem mem_of_mem_inter_left {x : α} {a b : set α} (h : x ∈ a ∩ b) : x ∈ a :=
h.left

theorem mem_of_mem_inter_right {x : α} {a b : set α} (h : x ∈ a ∩ b) : x ∈ b :=
h.right

@[simp] theorem inter_self (a : set α) : a ∩ a = a :=
ext (assume x, and_self _)

@[simp] theorem inter_empty (a : set α) : a ∩ ∅ = ∅ :=
ext (assume x, and_false _)

@[simp] theorem empty_inter (a : set α) : ∅ ∩ a = ∅ :=
ext (assume x, false_and _)

theorem inter_comm (a b : set α) : a ∩ b = b ∩ a :=
ext (assume x, and.comm)

theorem inter_assoc (a b c : set α) : (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
ext (assume x, and.assoc)

instance inter_is_assoc : is_associative (set α) (∩) :=
⟨inter_assoc⟩

instance inter_is_comm : is_commutative (set α) (∩) :=
⟨inter_comm⟩

theorem inter_left_comm (s₁ s₂ s₃ : set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
by finish

theorem inter_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
by finish

@[simp] theorem inter_subset_left (s t : set α) : s ∩ t ⊆ s := λ x H, and.left H

@[simp] theorem inter_subset_right (s t : set α) : s ∩ t ⊆ t := λ x H, and.right H

theorem subset_inter {s t r : set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
by finish [subset_def, inter_def]

@[simp] theorem subset_inter_iff {s t r : set α} : r ⊆ s ∩ t ↔ r ⊆ s ∧ r ⊆ t :=
⟨λ h, ⟨subset.trans h (inter_subset_left _ _), subset.trans h (inter_subset_right _ _)⟩,
 λ ⟨h₁, h₂⟩, subset_inter h₁ h₂⟩

@[simp] theorem inter_univ (a : set α) : a ∩ univ = a :=
ext (assume x, and_true _)

@[simp] theorem univ_inter (a : set α) : univ ∩ a = a :=
ext (assume x, true_and _)

theorem inter_subset_inter_left {s t : set α} (u : set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
by finish [subset_def]

theorem inter_subset_inter_right {s t : set α} (u : set α) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
by finish [subset_def]

theorem inter_subset_inter {s₁ s₂ t₁ t₂ : set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ ∩ s₂ ⊆ t₁ ∩ t₂ :=
by finish [subset_def]

theorem inter_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∩ t = s :=
by finish [subset_def, ext_iff, iff_def]

theorem inter_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∩ t = t :=
by finish [subset_def, ext_iff, iff_def]

theorem union_inter_cancel_left {s t : set α} : (s ∪ t) ∩ s = s :=
by finish [ext_iff, iff_def]

theorem union_inter_cancel_right {s t : set α} : (s ∪ t) ∩ t = t :=
by finish [ext_iff, iff_def]

/-! ### Distributivity laws -/

theorem inter_distrib_left (s t u : set α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
ext (assume x, and_or_distrib_left)

theorem inter_distrib_right (s t u : set α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
ext (assume x, or_and_distrib_right)

theorem union_distrib_left (s t u : set α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
ext (assume x, or_and_distrib_left)

theorem union_distrib_right (s t u : set α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
ext (assume x, and_or_distrib_right)

/-!
### Lemmas about `insert`

`insert α s` is the set `{α} ∪ s`.
-/

theorem insert_def (x : α) (s : set α) : insert x s = { y | y = x ∨ y ∈ s } := rfl

@[simp] theorem subset_insert (x : α) (s : set α) : s ⊆ insert x s :=
assume y ys, or.inr ys

theorem mem_insert (x : α) (s : set α) : x ∈ insert x s :=
or.inl rfl

theorem mem_insert_of_mem {x : α} {s : set α} (y : α) : x ∈ s → x ∈ insert y s := or.inr

theorem eq_or_mem_of_mem_insert {x a : α} {s : set α} : x ∈ insert a s → x = a ∨ x ∈ s := id

theorem mem_of_mem_insert_of_ne {x a : α} {s : set α} (xin : x ∈ insert a s) : x ≠ a → x ∈ s :=
by finish [insert_def]

@[simp] theorem mem_insert_iff {x a : α} {s : set α} : x ∈ insert a s ↔ (x = a ∨ x ∈ s) := iff.rfl

@[simp] theorem insert_eq_of_mem {a : α} {s : set α} (h : a ∈ s) : insert a s = s :=
by finish [ext_iff, iff_def]

lemma ne_insert_of_not_mem {s : set α} (t : set α) {a : α} (h : a ∉ s) :
  s ≠ insert a t :=
by { contrapose! h, simp [h] }

theorem insert_subset : insert a s ⊆ t ↔ (a ∈ t ∧ s ⊆ t) :=
by simp [subset_def, or_imp_distrib, forall_and_distrib]

theorem insert_subset_insert (h : s ⊆ t) : insert a s ⊆ insert a t :=
assume a', or.imp_right (@h a')

theorem ssubset_iff_insert {s t : set α} : s ⊂ t ↔ ∃ a ∉ s, insert a s ⊆ t :=
begin
  simp only [insert_subset, exists_and_distrib_right, ssubset_def, not_subset],
  simp only [exists_prop, and_comm]
end

theorem ssubset_insert {s : set α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
ssubset_iff_insert.2 ⟨a, h, subset.refl _⟩

theorem insert_comm (a b : α) (s : set α) : insert a (insert b s) = insert b (insert a s) :=
ext $ by simp [or.left_comm]

theorem insert_union : insert a s ∪ t = insert a (s ∪ t) :=
ext $ assume a, by simp [or.comm, or.left_comm]

@[simp] theorem union_insert : s ∪ insert a t = insert a (s ∪ t) :=
ext $ assume a, by simp [or.comm, or.left_comm]

theorem insert_nonempty (a : α) (s : set α) : (insert a s).nonempty :=
⟨a, mem_insert a s⟩

-- useful in proofs by induction
theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : set α} (h : ∀ x, x ∈ insert a s → P x) :
  ∀ x, x ∈ s → P x :=
by finish

theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : set α} (h : ∀ x, x ∈ s → P x) (ha : P a) :
  ∀ x, x ∈ insert a s → P x :=
by finish

theorem bex_insert_iff {P : α → Prop} {a : α} {s : set α} :
  (∃ x ∈ insert a s, P x) ↔ (∃ x ∈ s, P x) ∨ P a :=
by finish [iff_def]

theorem ball_insert_iff {P : α → Prop} {a : α} {s : set α} :
  (∀ x ∈ insert a s, P x) ↔ P a ∧ (∀x ∈ s, P x) :=
by finish [iff_def]

/-! ### Lemmas about singletons -/

theorem singleton_def (a : α) : ({a} : set α) = insert a ∅ :=
(insert_emptyc_eq _).symm

@[simp] theorem mem_singleton_iff {a b : α} : a ∈ ({b} : set α) ↔ a = b :=
iff.rfl

@[simp]
lemma set_of_eq_eq_singleton {a : α} : {n | n = a} = {a} := set.ext $ λ n, (set.mem_singleton_iff).symm

-- TODO: again, annotation needed
@[simp] theorem mem_singleton (a : α) : a ∈ ({a} : set α) := by finish

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : set α)) : x = y :=
by finish

@[simp] theorem singleton_eq_singleton_iff {x y : α} : {x} = ({y} : set α) ↔ x = y :=
by finish [ext_iff, iff_def]

theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : set α) :=
by finish

theorem insert_eq (x : α) (s : set α) : insert x s = ({x} : set α) ∪ s :=
by finish [ext_iff, or_comm]

@[simp] theorem pair_eq_singleton (a : α) : ({a, a} : set α) = {a} :=
by finish

@[simp] theorem singleton_nonempty (a : α) : ({a} : set α).nonempty :=
⟨a, rfl⟩

@[simp] theorem singleton_subset_iff {a : α} {s : set α} : {a} ⊆ s ↔ a ∈ s :=
⟨λh, h (by simp), λh b e, by simp at e; simp [*]⟩

theorem set_compr_eq_eq_singleton {a : α} : {b | b = a} = {a} :=
ext $ by simp

@[simp] theorem singleton_union : {a} ∪ s = insert a s :=
rfl

@[simp] theorem union_singleton : s ∪ {a} = insert a s :=
by rw [union_comm, singleton_union]

theorem singleton_inter_eq_empty : {a} ∩ s = ∅ ↔ a ∉ s :=
by simp [eq_empty_iff_forall_not_mem]

theorem inter_singleton_eq_empty : s ∩ {a} = ∅ ↔ a ∉ s :=
by rw [inter_comm, singleton_inter_eq_empty]

lemma nmem_singleton_empty {s : set α} : s ∉ ({∅} : set (set α)) ↔ s.nonempty :=
by rw [mem_singleton_iff, ← ne.def, ne_empty_iff_nonempty]

instance unique_singleton (a : α) : unique ↥({a} : set α) :=
{ default := ⟨a, mem_singleton a⟩,
  uniq :=
  begin
    intros x,
    apply subtype.coe_ext.2,
    apply eq_of_mem_singleton (subtype.mem x),
  end}

/-! ### Lemmas about sets defined as `{x ∈ s | p x}`. -/

theorem mem_sep {s : set α} {p : α → Prop} {x : α} (xs : x ∈ s) (px : p x) : x ∈ {x ∈ s | p x} :=
⟨xs, px⟩

@[simp] theorem mem_sep_eq {s : set α} {p : α → Prop} {x : α} : x ∈ {x ∈ s | p x} = (x ∈ s ∧ p x) := rfl

theorem mem_sep_iff {s : set α} {p : α → Prop} {x : α} : x ∈ {x ∈ s | p x} ↔ x ∈ s ∧ p x :=
iff.rfl

theorem eq_sep_of_subset {s t : set α} (ssubt : s ⊆ t) : s = {x ∈ t | x ∈ s} :=
by finish [ext_iff, iff_def, subset_def]

theorem sep_subset (s : set α) (p : α → Prop) : {x ∈ s | p x} ⊆ s :=
assume x, and.left

theorem forall_not_of_sep_empty {s : set α} {p : α → Prop} (h : {x ∈ s | p x} = ∅) :
  ∀ x ∈ s, ¬ p x :=
by finish [ext_iff]

@[simp] lemma sep_univ {α} {p : α → Prop} : {a ∈ (univ : set α) | p a} = {a | p a} :=
set.ext $ by simp

/-! ### Lemmas about complement -/

theorem mem_compl {s : set α} {x : α} (h : x ∉ s) : x ∈ -s := h

lemma compl_set_of {α} (p : α → Prop) : - {a | p a} = { a | ¬ p a } := rfl

theorem not_mem_of_mem_compl {s : set α} {x : α} (h : x ∈ -s) : x ∉ s := h

@[simp] theorem mem_compl_eq (s : set α) (x : α) : x ∈ -s = (x ∉ s) := rfl

theorem mem_compl_iff (s : set α) (x : α) : x ∈ -s ↔ x ∉ s := iff.rfl

@[simp] theorem inter_compl_self (s : set α) : s ∩ -s = ∅ :=
by finish [ext_iff]

@[simp] theorem compl_inter_self (s : set α) : -s ∩ s = ∅ :=
by finish [ext_iff]

@[simp] theorem compl_empty : -(∅ : set α) = univ :=
by finish [ext_iff]

@[simp] theorem compl_union (s t : set α) : -(s ∪ t) = -s ∩ -t :=
by finish [ext_iff]

local attribute [simp] -- Will be generalized to lattices in `compl_compl'`
theorem compl_compl (s : set α) : -(-s) = s :=
by finish [ext_iff]

-- ditto
theorem compl_inter (s t : set α) : -(s ∩ t) = -s ∪ -t :=
by finish [ext_iff]

@[simp] theorem compl_univ : -(univ : set α) = ∅ :=
by finish [ext_iff]

lemma compl_empty_iff {s : set α} : -s = ∅ ↔ s = univ :=
by { split, intro h, rw [←compl_compl s, h, compl_empty], intro h, rw [h, compl_univ] }

lemma compl_univ_iff {s : set α} : -s = univ ↔ s = ∅ :=
by rw [←compl_empty_iff, compl_compl]

lemma nonempty_compl {s : set α} : (-s : set α).nonempty ↔ s ≠ univ :=
ne_empty_iff_nonempty.symm.trans $ not_congr $ compl_empty_iff

lemma mem_compl_singleton_iff {a x : α} : x ∈ -({a} : set α) ↔ x ≠ a :=
not_iff_not_of_iff mem_singleton_iff

lemma compl_singleton_eq (a : α) : -({a} : set α) = {x | x ≠ a} :=
ext $ λ x,  mem_compl_singleton_iff

theorem union_eq_compl_compl_inter_compl (s t : set α) : s ∪ t = -(-s ∩ -t) :=
by simp [compl_inter, compl_compl]

theorem inter_eq_compl_compl_union_compl (s t : set α) : s ∩ t = -(-s ∪ -t) :=
by simp [compl_compl]

@[simp] theorem union_compl_self (s : set α) : s ∪ -s = univ :=
by finish [ext_iff]

@[simp] theorem compl_union_self (s : set α) : -s ∪ s = univ :=
by finish [ext_iff]

theorem compl_comp_compl : compl ∘ compl = @id (set α) :=
funext compl_compl

theorem compl_subset_comm {s t : set α} : -s ⊆ t ↔ -t ⊆ s :=
by haveI := classical.prop_decidable; exact
forall_congr (λ a, not_imp_comm)

lemma compl_subset_compl {s t : set α} : -s ⊆ -t ↔ t ⊆ s :=
by rw [compl_subset_comm, compl_compl]

theorem compl_subset_iff_union {s t : set α} : -s ⊆ t ↔ s ∪ t = univ :=
iff.symm $ eq_univ_iff_forall.trans $ forall_congr $ λ a,
by haveI := classical.prop_decidable; exact or_iff_not_imp_left

theorem subset_compl_comm {s t : set α} : s ⊆ -t ↔ t ⊆ -s :=
forall_congr $ λ a, imp_not_comm

theorem subset_compl_iff_disjoint {s t : set α} : s ⊆ -t ↔ s ∩ t = ∅ :=
iff.trans (forall_congr $ λ a, and_imp.symm) subset_empty_iff

lemma subset_compl_singleton_iff {a : α} {s : set α} : s ⊆ -({a} : set α) ↔ a ∉ s :=
by { rw subset_compl_comm, simp }

theorem inter_subset (a b c : set α) : a ∩ b ⊆ c ↔ a ⊆ -b ∪ c :=
begin
  classical,
  split,
  { intros h x xa, by_cases h' : x ∈ b, simp [h ⟨xa, h'⟩], simp [h'] },
  intros h x, rintro ⟨xa, xb⟩, cases h xa, contradiction, assumption
end

/-! ### Lemmas about set difference -/

theorem diff_eq (s t : set α) : s \ t = s ∩ -t := rfl

@[simp] theorem mem_diff {s t : set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := iff.rfl

theorem mem_diff_of_mem {s t : set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t :=
⟨h1, h2⟩

theorem mem_of_mem_diff {s t : set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
h.left

theorem not_mem_of_mem_diff {s t : set α} {x : α} (h : x ∈ s \ t) : x ∉ t :=
h.right

theorem nonempty_diff {s t : set α} : (s \ t).nonempty ↔ ¬ (s ⊆ t) :=
⟨λ ⟨x, xs, xt⟩, not_subset.2 ⟨x, xs, xt⟩,
  λ h, let ⟨x, xs, xt⟩ := not_subset.1 h in ⟨x, xs, xt⟩⟩

theorem union_diff_cancel {s t : set α} (h : s ⊆ t) : s ∪ (t \ s) = t :=
by finish [ext_iff, iff_def, subset_def]

theorem union_diff_cancel_left {s t : set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ s = t :=
by finish [ext_iff, iff_def, subset_def]

theorem union_diff_cancel_right {s t : set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ t = s :=
by finish [ext_iff, iff_def, subset_def]

theorem union_diff_left {s t : set α} : (s ∪ t) \ s = t \ s :=
by finish [ext_iff, iff_def]

theorem union_diff_right {s t : set α} : (s ∪ t) \ t = s \ t :=
by finish [ext_iff, iff_def]

theorem union_diff_distrib {s t u : set α} : (s ∪ t) \ u = s \ u ∪ t \ u :=
inter_distrib_right _ _ _

theorem inter_union_distrib_left {s t u : set α} : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
set.ext $ λ _, and_or_distrib_left

theorem inter_union_distrib_right {s t u : set α} : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
set.ext $ λ _, and_or_distrib_right

theorem union_inter_distrib_left {s t u : set α} : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
set.ext $ λ _, or_and_distrib_left

theorem union_inter_distrib_right {s t u : set α} : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
set.ext $ λ _, or_and_distrib_right

theorem inter_diff_assoc (a b c : set α) : (a ∩ b) \ c = a ∩ (b \ c) :=
inter_assoc _ _ _

theorem inter_diff_self (a b : set α) : a ∩ (b \ a) = ∅ :=
by finish [ext_iff]

theorem inter_union_diff (s t : set α) : (s ∩ t) ∪ (s \ t) = s :=
by finish [ext_iff, iff_def]

theorem diff_subset (s t : set α) : s \ t ⊆ s :=
by finish [subset_def]

theorem diff_subset_diff {s₁ s₂ t₁ t₂ : set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
by finish [subset_def]

theorem diff_subset_diff_left {s₁ s₂ t : set α} (h : s₁ ⊆ s₂) : s₁ \ t ⊆ s₂ \ t :=
diff_subset_diff h (by refl)

theorem diff_subset_diff_right {s t u : set α} (h : t ⊆ u) : s \ u ⊆ s \ t :=
diff_subset_diff (subset.refl s) h

theorem compl_eq_univ_diff (s : set α) : -s = univ \ s :=
by finish [ext_iff]

@[simp] lemma empty_diff (s : set α) : (∅ \ s : set α) = ∅ :=
eq_empty_of_subset_empty $ assume x ⟨hx, _⟩, hx

theorem diff_eq_empty {s t : set α} : s \ t = ∅ ↔ s ⊆ t :=
⟨assume h x hx, classical.by_contradiction $ assume : x ∉ t, show x ∈ (∅ : set α), from h ▸ ⟨hx, this⟩,
  assume h, eq_empty_of_subset_empty $ assume x ⟨hx, hnx⟩, hnx $ h hx⟩

@[simp] theorem diff_empty {s : set α} : s \ ∅ = s :=
ext $ assume x, ⟨assume ⟨hx, _⟩, hx, assume h, ⟨h, not_false⟩⟩

theorem diff_diff {u : set α} : s \ t \ u = s \ (t ∪ u) :=
ext $ by simp [not_or_distrib, and.comm, and.left_comm]

lemma diff_subset_iff {s t u : set α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
⟨assume h x xs, classical.by_cases or.inl (assume nxt, or.inr (h ⟨xs, nxt⟩)),
 assume h x ⟨xs, nxt⟩, or.resolve_left (h xs) nxt⟩

lemma subset_diff_union (s t : set α) : s ⊆ (s \ t) ∪ t :=
by rw [union_comm, ←diff_subset_iff]

@[simp] lemma diff_singleton_subset_iff {x : α} {s t : set α} : s \ {x} ⊆ t ↔ s ⊆ insert x t :=
by { rw [←union_singleton, union_comm], apply diff_subset_iff }

lemma subset_diff_singleton {x : α} {s t : set α} (h : s ⊆ t) (hx : x ∉ s) : s ⊆ t \ {x} :=
subset_inter h $ subset_compl_comm.1 $ singleton_subset_iff.2 hx

lemma subset_insert_diff_singleton (x : α) (s : set α) : s ⊆ insert x (s \ {x}) :=
by rw [←diff_singleton_subset_iff]

lemma diff_subset_comm {s t u : set α} : s \ t ⊆ u ↔ s \ u ⊆ t :=
by rw [diff_subset_iff, diff_subset_iff, union_comm]

lemma diff_inter {s t u : set α} : s \ (t ∩ u) = (s \ t) ∪ (s \ u) :=
ext $ λ x, by simp [classical.not_and_distrib, and_or_distrib_left]

lemma diff_compl : s \ -t = s ∩ t := by rw [diff_eq, compl_compl]

lemma diff_diff_right {s t u : set α} : s \ (t \ u) = (s \ t) ∪ (s ∩ u) :=
by rw [diff_eq t u, diff_inter, diff_compl]

@[simp] theorem insert_diff_of_mem (s) (h : a ∈ t) : insert a s \ t = s \ t :=
ext $ by intro; constructor; simp [or_imp_distrib, h] {contextual := tt}

theorem insert_diff_of_not_mem (s) (h : a ∉ t) : insert a s \ t = insert a (s \ t) :=
begin
  classical,
  ext x,
  by_cases h' : x ∈ t,
  { have : x ≠ a,
    { assume H,
      rw H at h',
      exact h h' },
    simp [h, h', this] },
  { simp [h, h'] }
end

theorem union_diff_self {s t : set α} : s ∪ (t \ s) = s ∪ t :=
by finish [ext_iff, iff_def]

theorem diff_union_self {s t : set α} : (s \ t) ∪ t = s ∪ t :=
by rw [union_comm, union_diff_self, union_comm]

theorem diff_inter_self {a b : set α} : (b \ a) ∩ a = ∅ :=
ext $ by simp [iff_def] {contextual:=tt}

theorem diff_eq_self {s t : set α} : s \ t = s ↔ t ∩ s ⊆ ∅ :=
by finish [ext_iff, iff_def, subset_def]

@[simp] theorem diff_singleton_eq_self {a : α} {s : set α} (h : a ∉ s) : s \ {a} = s :=
diff_eq_self.2 $ by simp [singleton_inter_eq_empty.2 h]

@[simp] theorem insert_diff_singleton {a : α} {s : set α} :
  insert a (s \ {a}) = insert a s :=
by simp [insert_eq, union_diff_self, -union_singleton, -singleton_union]

@[simp] lemma diff_self {s : set α} : s \ s = ∅ := ext $ by simp

lemma diff_diff_cancel_left {s t : set α} (h : s ⊆ t) : t \ (t \ s) = s :=
by simp only [diff_diff_right, diff_self, inter_eq_self_of_subset_right h, empty_union]

lemma mem_diff_singleton {x y : α} {s : set α} : x ∈ s \ {y} ↔ (x ∈ s ∧ x ≠ y) :=
iff.rfl

lemma mem_diff_singleton_empty {s : set α} {t : set (set α)} :
  s ∈ t \ {∅} ↔ (s ∈ t ∧ s.nonempty) :=
mem_diff_singleton.trans $ and_congr iff.rfl ne_empty_iff_nonempty

/-! ### Powerset -/

theorem mem_powerset {x s : set α} (h : x ⊆ s) : x ∈ powerset s := h

theorem subset_of_mem_powerset {x s : set α} (h : x ∈ powerset s) : x ⊆ s := h

theorem mem_powerset_iff (x s : set α) : x ∈ powerset s ↔ x ⊆ s := iff.rfl

/-! ### Inverse image -/

/-- The preimage of `s : set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
def preimage {α : Type u} {β : Type v} (f : α → β) (s : set β) : set α := {x | f x ∈ s}

infix ` ⁻¹' `:80 := preimage

section preimage
variables {f : α → β} {g : β → γ}

@[simp] theorem preimage_empty : f ⁻¹' ∅ = ∅ := rfl

@[simp] theorem mem_preimage {s : set β} {a : α} : (a ∈ f ⁻¹' s) ↔ (f a ∈ s) := iff.rfl

theorem preimage_mono {s t : set β} (h : s ⊆ t) : f ⁻¹' s ⊆ f ⁻¹' t :=
assume x hx, h hx

@[simp] theorem preimage_univ : f ⁻¹' univ = univ := rfl

theorem subset_preimage_univ {s : set α} : s ⊆ f ⁻¹' univ := subset_univ _

@[simp] theorem preimage_inter {s t : set β} : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := rfl

@[simp] theorem preimage_union {s t : set β} : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t := rfl

@[simp] theorem preimage_compl {s : set β} : f ⁻¹' (- s) = - (f ⁻¹' s) := rfl

@[simp] theorem preimage_diff (f : α → β) (s t : set β) :
  f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t := rfl

@[simp] theorem preimage_set_of_eq {p : α → Prop} {f : β → α} : f ⁻¹' {a | p a} = {a | p (f a)} :=
rfl

@[simp] theorem preimage_id {s : set α} : id ⁻¹' s = s := rfl

theorem preimage_comp {s : set γ} : (g ∘ f) ⁻¹' s = f ⁻¹' (g ⁻¹' s) := rfl

theorem eq_preimage_subtype_val_iff {p : α → Prop} {s : set (subtype p)} {t : set α} :
  s = subtype.val ⁻¹' t ↔ (∀x (h : p x), (⟨x, h⟩ : subtype p) ∈ s ↔ x ∈ t) :=
⟨assume s_eq x h, by rw [s_eq]; simp,
 assume h, ext $ assume ⟨x, hx⟩, by simp [h]⟩

lemma if_preimage (s : set α) [decidable_pred s] (f g : α → β) (t : set β) :
  (λa, if a ∈ s then f a else g a)⁻¹' t = (s ∩ f ⁻¹' t) ∪ (-s ∩ g ⁻¹' t) :=
begin
  ext,
  simp only [mem_inter_eq, mem_union_eq, mem_preimage],
  split_ifs;
  simp [mem_def, h]
end

end preimage

/-! ### Image of a set under a function -/

section image

infix ` '' `:80 := image

-- TODO(Jeremy): use bounded exists in image

theorem mem_image_iff_bex {f : α → β} {s : set α} {y : β} :
  y ∈ f '' s ↔ ∃ x (_ : x ∈ s), f x = y := bex_def.symm

theorem mem_image_eq (f : α → β) (s : set α) (y: β) : y ∈ f '' s = ∃ x, x ∈ s ∧ f x = y := rfl

@[simp] theorem mem_image (f : α → β) (s : set α) (y : β) :
  y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y := iff.rfl

theorem mem_image_of_mem (f : α → β) {x : α} {a : set α} (h : x ∈ a) : f x ∈ f '' a :=
⟨_, h, rfl⟩

theorem mem_image_of_injective {f : α → β} {a : α} {s : set α} (hf : injective f) :
  f a ∈ f '' s ↔ a ∈ s :=
iff.intro
  (assume ⟨b, hb, eq⟩, (hf eq) ▸ hb)
  (assume h, mem_image_of_mem _ h)

theorem ball_image_of_ball {f : α → β} {s : set α} {p : β → Prop}
  (h : ∀ x ∈ s, p (f x)) : ∀ y ∈ f '' s, p y :=
by finish [mem_image_eq]

theorem ball_image_iff {f : α → β} {s : set α} {p : β → Prop} :
  (∀ y ∈ f '' s, p y) ↔ (∀ x ∈ s, p (f x)) :=
iff.intro
  (assume h a ha, h _ $ mem_image_of_mem _ ha)
  (assume h b ⟨a, ha, eq⟩, eq ▸ h a ha)

theorem bex_image_iff {f : α → β} {s : set α} {p : β → Prop} :
  (∃ y ∈ f '' s, p y) ↔ (∃ x ∈ s, p (f x)) :=
by simp

theorem mem_image_elim {f : α → β} {s : set α} {C : β → Prop} (h : ∀ (x : α), x ∈ s → C (f x)) :
 ∀{y : β}, y ∈ f '' s → C y
| ._ ⟨a, a_in, rfl⟩ := h a a_in

theorem mem_image_elim_on {f : α → β} {s : set α} {C : β → Prop} {y : β} (h_y : y ∈ f '' s)
  (h : ∀ (x : α), x ∈ s → C (f x)) : C y :=
mem_image_elim h h_y

@[congr] lemma image_congr {f g : α → β} {s : set α}
  (h : ∀a∈s, f a = g a) : f '' s = g '' s :=
by safe [ext_iff, iff_def]

/-- A common special case of `image_congr` -/
lemma image_congr' {f g : α → β} {s : set α} (h : ∀ (x : α), f x = g x) : f '' s = g '' s :=
image_congr (λx _, h x)

theorem image_comp (f : β → γ) (g : α → β) (a : set α) : (f ∘ g) '' a = f '' (g '' a) :=
subset.antisymm
  (ball_image_of_ball $ assume a ha, mem_image_of_mem _ $ mem_image_of_mem _ ha)
  (ball_image_of_ball $ ball_image_of_ball $ assume a ha, mem_image_of_mem _ ha)
/- Proof is removed as it uses generated names
TODO(Jeremy): make automatic,
begin
  safe [ext_iff, iff_def, mem_image, (∘)],
  have h' := h_2 (g a_2),
  finish
end -/

/-- A variant of `image_comp`, useful for rewriting -/
lemma image_image (g : β → γ) (f : α → β) (s : set α) : g '' (f '' s) = (λ x, g (f x)) '' s :=
(image_comp g f s).symm

/-- Image is monotone with respect to `⊆`. See `set.monotone_image` for the statement in
terms of `≤`. -/
theorem image_subset {a b : set α} (f : α → β) (h : a ⊆ b) : f '' a ⊆ f '' b :=
by finish [subset_def, mem_image_eq]

theorem image_union (f : α → β) (s t : set α) :
  f '' (s ∪ t) = f '' s ∪ f '' t :=
by finish [ext_iff, iff_def, mem_image_eq]

@[simp] theorem image_empty (f : α → β) : f '' ∅ = ∅ := ext $ by simp

lemma image_inter_subset (f : α → β) (s t : set α) :
  f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
subset_inter (image_subset _ $ inter_subset_left _ _) (image_subset _ $ inter_subset_right _ _)

theorem image_inter_on {f : α → β} {s t : set α} (h : ∀x∈t, ∀y∈s, f x = f y → x = y) :
  f '' s ∩ f '' t = f '' (s ∩ t) :=
subset.antisymm
  (assume b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩,
    have a₂ = a₁, from h _ ha₂ _ ha₁ (by simp *),
    ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩)
  (image_inter_subset _ _ _)

theorem image_inter {f : α → β} {s t : set α} (H : injective f) :
  f '' s ∩ f '' t = f '' (s ∩ t) :=
image_inter_on (assume x _ y _ h, H h)

theorem image_univ_of_surjective {ι : Type*} {f : ι → β} (H : surjective f) : f '' univ = univ :=
eq_univ_of_forall $ by simp [image]; exact H

@[simp] theorem image_singleton {f : α → β} {a : α} : f '' {a} = {f a} :=
ext $ λ x, by simp [image]; rw eq_comm

theorem nonempty.image_const {s : set α} (hs : s.nonempty) (a : β) : (λ _, a) '' s = {a} :=
ext $ λ x, ⟨λ ⟨y, _, h⟩, h ▸ mem_singleton _,
  λ h, (eq_of_mem_singleton h).symm ▸ hs.imp (λ y hy, ⟨hy, rfl⟩)⟩

@[simp] lemma image_eq_empty {α β} {f : α → β} {s : set α} : f '' s = ∅ ↔ s = ∅ :=
by simp only [eq_empty_iff_forall_not_mem]; exact
⟨λ H a ha, H _ ⟨_, ha, rfl⟩, λ H b ⟨_, ha, _⟩, H _ ha⟩

lemma inter_singleton_nonempty {s : set α} {a : α} : (s ∩ {a}).nonempty ↔ a ∈ s :=
by finish [set.nonempty]

theorem fix_set_compl (t : set α) : compl t = - t := rfl

-- TODO(Jeremy): there is an issue with - t unfolding to compl t
theorem mem_compl_image (t : set α) (S : set (set α)) :
  t ∈ compl '' S ↔ -t ∈ S :=
begin
  suffices : ∀ x, -x = t ↔ -t = x, {simp [fix_set_compl, this]},
  intro x, split; { intro e, subst e, simp }
end

/-- A variant of `image_id` -/
@[simp] lemma image_id' (s : set α) : (λx, x) '' s = s := ext $ by simp

theorem image_id (s : set α) : id '' s = s := by simp

theorem compl_compl_image (S : set (set α)) :
  compl '' (compl '' S) = S :=
by rw [← image_comp, compl_comp_compl, image_id]

theorem image_insert_eq {f : α → β} {a : α} {s : set α} :
  f '' (insert a s) = insert (f a) (f '' s) :=
ext $ by simp [and_or_distrib_left, exists_or_distrib, eq_comm, or_comm, and_comm]

theorem image_pair (f : α → β) (a b : α) : f '' {a, b} = {f a, f b} :=
by simp only [image_insert_eq, image_singleton]

theorem image_subset_preimage_of_inverse {f : α → β} {g : β → α}
  (I : left_inverse g f) (s : set α) : f '' s ⊆ g ⁻¹' s :=
λ b ⟨a, h, e⟩, e ▸ ((I a).symm ▸ h : g (f a) ∈ s)

theorem preimage_subset_image_of_inverse {f : α → β} {g : β → α}
  (I : left_inverse g f) (s : set β) : f ⁻¹' s ⊆ g '' s :=
λ b h, ⟨f b, h, I b⟩

theorem image_eq_preimage_of_inverse {f : α → β} {g : β → α}
  (h₁ : left_inverse g f) (h₂ : right_inverse g f) :
  image f = preimage g :=
funext $ λ s, subset.antisymm
  (image_subset_preimage_of_inverse h₁ s)
  (preimage_subset_image_of_inverse h₂ s)

theorem mem_image_iff_of_inverse {f : α → β} {g : β → α} {b : β} {s : set α}
  (h₁ : left_inverse g f) (h₂ : right_inverse g f) :
  b ∈ f '' s ↔ g b ∈ s :=
by rw image_eq_preimage_of_inverse h₁ h₂; refl

theorem image_compl_subset {f : α → β} {s : set α} (H : injective f) : f '' -s ⊆ -(f '' s) :=
subset_compl_iff_disjoint.2 $ by simp [image_inter H]

theorem subset_image_compl {f : α → β} {s : set α} (H : surjective f) : -(f '' s) ⊆ f '' -s :=
compl_subset_iff_union.2 $
by rw ← image_union; simp [image_univ_of_surjective H]

theorem image_compl_eq {f : α → β} {s : set α} (H : bijective f) : f '' -s = -(f '' s) :=
subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)

lemma nonempty.image (f : α → β) {s : set α} : s.nonempty → (f '' s).nonempty
| ⟨x, hx⟩ := ⟨f x, mem_image_of_mem f hx⟩

lemma nonempty.of_image {f : α → β} {s : set α} : (f '' s).nonempty → s.nonempty
| ⟨y, x, hx, _⟩ := ⟨x, hx⟩

@[simp] lemma nonempty_image_iff {f : α → β} {s : set α} :
  (f '' s).nonempty ↔ s.nonempty :=
⟨nonempty.of_image, λ h, h.image f⟩

/-- image and preimage are a Galois connection -/
theorem image_subset_iff {s : set α} {t : set β} {f : α → β} :
  f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
ball_image_iff

theorem image_preimage_subset (f : α → β) (s : set β) :
  f '' (f ⁻¹' s) ⊆ s :=
image_subset_iff.2 (subset.refl _)

theorem subset_preimage_image (f : α → β) (s : set α) :
  s ⊆ f ⁻¹' (f '' s) :=
λ x, mem_image_of_mem f

theorem preimage_image_eq {f : α → β} (s : set α) (h : injective f) : f ⁻¹' (f '' s) = s :=
subset.antisymm
  (λ x ⟨y, hy, e⟩, h e ▸ hy)
  (subset_preimage_image f s)

theorem image_preimage_eq {f : α → β} {s : set β} (h : surjective f) : f '' (f ⁻¹' s) = s :=
subset.antisymm
  (image_preimage_subset f s)
  (λ x hx, let ⟨y, e⟩ := h x in ⟨y, (e.symm ▸ hx : f y ∈ s), e⟩)

lemma preimage_eq_preimage {f : β → α} (hf : surjective f) : f ⁻¹' s = preimage f t ↔ s = t :=
iff.intro
  (assume eq, by rw [← @image_preimage_eq β α f s hf, ← @image_preimage_eq β α f t hf, eq])
  (assume eq, eq ▸ rfl)

protected lemma push_pull (f : α → β) (s : set α) (t : set β) :
  f '' (s ∩ f ⁻¹' t) = f '' s ∩ t :=
begin
  apply subset.antisymm,
  { calc f '' (s ∩ f ⁻¹' t) ⊆ f '' s ∩ (f '' (f⁻¹' t)) : image_inter_subset _ _ _
  ... ⊆ f '' s ∩ t : inter_subset_inter_right _ (image_preimage_subset f t) },
  { rintros _ ⟨⟨x, h', rfl⟩, h⟩,
    exact ⟨x, ⟨h', h⟩, rfl⟩ }
end

protected lemma push_pull' (f : α → β) (s : set α) (t : set β) :
  f '' (f ⁻¹' t ∩ s) = t ∩ f '' s :=
by simp only [inter_comm, set.push_pull]

theorem compl_image : image (@compl α) = preimage compl :=
image_eq_preimage_of_inverse compl_compl compl_compl

theorem compl_image_set_of {p : set α → Prop} :
  compl '' {s | p s} = {s | p (- s)} :=
congr_fun compl_image p

theorem inter_preimage_subset (s : set α) (t : set β) (f : α → β) :
  s ∩ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∩ t) :=
λ x h, ⟨mem_image_of_mem _ h.left, h.right⟩

theorem union_preimage_subset (s : set α) (t : set β) (f : α → β) :
  s ∪ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∪ t) :=
λ x h, or.elim h (λ l, or.inl $ mem_image_of_mem _ l) (λ r, or.inr r)

theorem subset_image_union (f : α → β) (s : set α) (t : set β) :
  f '' (s ∪ f ⁻¹' t) ⊆ f '' s ∪ t :=
image_subset_iff.2 (union_preimage_subset _ _ _)

lemma preimage_subset_iff {A : set α} {B : set β} {f : α → β} :
  f⁻¹' B ⊆ A ↔ (∀ a : α, f a ∈ B → a ∈ A) := iff.rfl

lemma image_eq_image {f : α → β} (hf : injective f) : f '' s = f '' t ↔ s = t :=
iff.symm $ iff.intro (assume eq, eq ▸ rfl) $ assume eq,
  by rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, eq]

lemma image_subset_image_iff {f : α → β} (hf : injective f) : f '' s ⊆ f '' t ↔ s ⊆ t :=
begin
  refine (iff.symm $ iff.intro (image_subset f) $ assume h, _),
  rw [← preimage_image_eq s hf, ← preimage_image_eq t hf],
  exact preimage_mono h
end

lemma injective_image {f : α → β} (hf : injective f) : injective (('') f) :=
assume s t, (image_eq_image hf).1

lemma prod_quotient_preimage_eq_image [s : setoid α] (g : quotient s → β) {h : α → β}
  (Hh : h = g ∘ quotient.mk) (r : set (β × β)) :
  {x : quotient s × quotient s | (g x.1, g x.2) ∈ r} =
  (λ a : α × α, (⟦a.1⟧, ⟦a.2⟧)) '' ((λ a : α × α, (h a.1, h a.2)) ⁻¹' r) :=
Hh.symm ▸ set.ext (λ ⟨a₁, a₂⟩, ⟨quotient.induction_on₂ a₁ a₂
  (λ a₁ a₂ h, ⟨(a₁, a₂), h, rfl⟩),
  λ ⟨⟨b₁, b₂⟩, h₁, h₂⟩, show (g a₁, g a₂) ∈ r, from
  have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := prod.ext_iff.1 h₂,
    h₃.1 ▸ h₃.2 ▸ h₁⟩)

/-- Restriction of `f` to `s` factors through `s.image_factorization f : s → f '' s`. -/
def image_factorization (f : α → β) (s : set α) : s → f '' s :=
λ p, ⟨f p.1, mem_image_of_mem f p.2⟩

lemma image_factorization_eq {f : α → β} {s : set α} :
  subtype.val ∘ image_factorization f s = f ∘ subtype.val :=
funext $ λ p, rfl

lemma surjective_onto_image {f : α → β} {s : set α} :
  surjective (image_factorization f s) :=
λ ⟨_, ⟨a, ha, rfl⟩⟩, ⟨⟨a, ha⟩, rfl⟩

end image

/-! ### Subsingleton -/

/-- A set `s` is a `subsingleton`, if it has at most one element. -/
protected def subsingleton (s : set α) : Prop :=
∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), x = y

lemma subsingleton.mono (ht : t.subsingleton) (hst : s ⊆ t) : s.subsingleton :=
λ x hx y hy, ht (hst hx) (hst hy)

lemma subsingleton.image (hs : s.subsingleton) (f : α → β) : (f '' s).subsingleton :=
λ _ ⟨x, hx, Hx⟩ _ ⟨y, hy, Hy⟩, Hx ▸ Hy ▸ congr_arg f (hs hx hy)

lemma subsingleton.eq_singleton_of_mem (hs : s.subsingleton) {x:α} (hx : x ∈ s) :
  s = {x} :=
ext $ λ y, ⟨λ hy, (hs hx hy) ▸ mem_singleton _, λ hy, (eq_of_mem_singleton hy).symm ▸ hx⟩

lemma subsingleton_empty : (∅ : set α).subsingleton := λ x, false.elim

lemma subsingleton_singleton {a} : ({a} : set α).subsingleton :=
λ x hx y hy, (eq_of_mem_singleton hx).symm ▸ (eq_of_mem_singleton hy).symm ▸ rfl

lemma subsingleton.eq_empty_or_singleton (hs : s.subsingleton) :
  s = ∅ ∨ ∃ x, s = {x} :=
s.eq_empty_or_nonempty.elim or.inl (λ ⟨x, hx⟩, or.inr ⟨x, hs.eq_singleton_of_mem hx⟩)

lemma subsingleton_univ [subsingleton α] : (univ : set α).subsingleton :=
λ x hx y hy, subsingleton.elim x y

theorem univ_eq_true_false : univ = ({true, false} : set Prop) :=
eq.symm $ eq_univ_of_forall $ classical.cases (by simp) (by simp)

/-! ### Lemmas about range of a function. -/
section range
variables {f : ι → α}
open function

/-- Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range (f : ι → α) : set α := {x | ∃y, f y = x}

@[simp] theorem mem_range {x : α} : x ∈ range f ↔ ∃ y, f y = x := iff.rfl

theorem mem_range_self (i : ι) : f i ∈ range f := ⟨i, rfl⟩

theorem forall_range_iff {p : α → Prop} : (∀ a ∈ range f, p a) ↔ (∀ i, p (f i)) :=
⟨assume h i, h (f i) (mem_range_self _), assume h a ⟨i, (hi : f i = a)⟩, hi ▸ h i⟩

theorem exists_range_iff {p : α → Prop} : (∃ a ∈ range f, p a) ↔ (∃ i, p (f i)) :=
by simp

lemma exists_range_iff' {p : α → Prop} :
  (∃ a, a ∈ range f ∧ p a) ↔ ∃ i, p (f i) :=
by simpa only [exists_prop] using exists_range_iff

theorem range_iff_surjective : range f = univ ↔ surjective f :=
eq_univ_iff_forall

@[simp] theorem range_id : range (@id α) = univ := range_iff_surjective.2 surjective_id

theorem range_inl_union_range_inr : range (@sum.inl α β) ∪ range sum.inr = univ :=
ext $ λ x, by cases x; simp

@[simp] theorem range_quot_mk (r : α → α → Prop) : range (quot.mk r) = univ :=
range_iff_surjective.2 quot.exists_rep

@[simp] theorem image_univ {ι : Type*} {f : ι → β} : f '' univ = range f :=
ext $ by simp [image, range]

theorem image_subset_range {ι : Type*} (f : ι → β) (s : set ι) : f '' s ⊆ range f :=
by rw ← image_univ; exact image_subset _ (subset_univ _)

theorem range_comp {g : α → β} : range (g ∘ f) = g '' range f :=
subset.antisymm
  (forall_range_iff.mpr $ assume i, mem_image_of_mem g (mem_range_self _))
  (ball_image_iff.mpr $ forall_range_iff.mpr mem_range_self)

theorem range_subset_iff {s : set α} : range f ⊆ s ↔ ∀ y, f y ∈ s :=
forall_range_iff

lemma range_comp_subset_range (f : α → β) (g : β → γ) : range (g ∘ f) ⊆ range g :=
by rw range_comp; apply image_subset_range

lemma range_nonempty_iff_nonempty : (range f).nonempty ↔ nonempty ι :=
⟨λ ⟨y, x, hxy⟩, ⟨x⟩, λ ⟨x⟩, ⟨f x, mem_range_self x⟩⟩

lemma range_nonempty [h : nonempty ι] (f : ι → α) : (range f).nonempty :=
range_nonempty_iff_nonempty.2 h

@[simp] lemma range_eq_empty {f : ι → α} : range f = ∅ ↔ ¬ nonempty ι :=
not_nonempty_iff_eq_empty.symm.trans $ not_congr range_nonempty_iff_nonempty

theorem image_preimage_eq_inter_range {f : α → β} {t : set β} :
  f '' (f ⁻¹' t) = t ∩ range f :=
ext $ assume x, ⟨assume ⟨x, hx, heq⟩, heq ▸ ⟨hx, mem_range_self _⟩,
  assume ⟨hx, ⟨y, h_eq⟩⟩, h_eq ▸ mem_image_of_mem f $
    show y ∈ f ⁻¹' t, by simp [preimage, h_eq, hx]⟩

lemma image_preimage_eq_of_subset {f : α → β} {s : set β} (hs : s ⊆ range f) :
  f '' (f ⁻¹' s) = s :=
by rw [image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]

lemma preimage_subset_preimage_iff {s t : set α} {f : β → α} (hs : s ⊆ range f) :
  f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t :=
begin
  split,
  { intros h x hx, rcases hs hx with ⟨y, rfl⟩, exact h hx },
  intros h x, apply h
end

lemma preimage_eq_preimage' {s t : set α} {f : β → α} (hs : s ⊆ range f) (ht : t ⊆ range f) :
  f ⁻¹' s = f ⁻¹' t ↔ s = t :=
begin
  split,
  { intro h, apply subset.antisymm, rw [←preimage_subset_preimage_iff hs, h],
    rw [←preimage_subset_preimage_iff ht, h] },
  rintro rfl, refl
end

theorem preimage_inter_range {f : α → β} {s : set β} : f ⁻¹' (s ∩ range f) = f ⁻¹' s :=
set.ext $ λ x, and_iff_left ⟨x, rfl⟩

theorem preimage_image_preimage {f : α → β} {s : set β} :
  f ⁻¹' (f '' (f ⁻¹' s)) = f ⁻¹' s :=
by rw [image_preimage_eq_inter_range, preimage_inter_range]

@[simp] theorem quot_mk_range_eq [setoid α] : range (λx : α, ⟦x⟧) = univ :=
range_iff_surjective.2 quot.exists_rep

lemma range_const_subset {c : α} : range (λx:ι, c) ⊆ {c} :=
range_subset_iff.2 $ λ x, rfl

@[simp] lemma range_const : ∀ [nonempty ι] {c : α}, range (λx:ι, c) = {c}
| ⟨x⟩ c := subset.antisymm range_const_subset $
  assume y hy, (mem_singleton_iff.1 hy).symm ▸ mem_range_self x

/-- Any map `f : ι → β` factors through a map `range_factorization f : ι → range f`. -/
def range_factorization (f : ι → β) : ι → range f :=
λ i, ⟨f i, mem_range_self i⟩

lemma range_factorization_eq {f : ι → β} :
  subtype.val ∘ range_factorization f = f :=
funext $ λ i, rfl

lemma surjective_onto_range : surjective (range_factorization f) :=
λ ⟨_, ⟨i, rfl⟩⟩, ⟨i, rfl⟩

lemma image_eq_range (f : α → β) (s : set α) : f '' s = range (λ(x : s), f x.1) :=
by { ext, split, rintro ⟨x, h1, h2⟩, exact ⟨⟨x, h1⟩, h2⟩, rintro ⟨⟨x, h1⟩, h2⟩, exact ⟨x, h1, h2⟩ }

@[simp] lemma sum.elim_range {α β γ : Type*} (f : α → γ) (g : β → γ) :
  range (sum.elim f g) = range f ∪ range g :=
by simp [set.ext_iff, mem_range]

lemma range_ite_subset' {p : Prop} [decidable p] {f g : α → β} :
  range (if p then f else g) ⊆ range f ∪ range g :=
begin
  by_cases h : p, {rw if_pos h, exact subset_union_left _ _},
  {rw if_neg h, exact subset_union_right _ _}
end

lemma range_ite_subset {p : α → Prop} [decidable_pred p] {f g : α → β} :
  range (λ x, if p x then f x else g x) ⊆ range f ∪ range g :=
begin
  rw range_subset_iff, intro x, by_cases h : p x,
  simp [if_pos h, mem_union, mem_range_self],
  simp [if_neg h, mem_union, mem_range_self]
end

end range

/-- The set `s` is pairwise `r` if `r x y` for all *distinct* `x y ∈ s`. -/
def pairwise_on (s : set α) (r : α → α → Prop) := ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r x y

theorem pairwise_on.mono {s t : set α} {r}
  (h : t ⊆ s) (hp : pairwise_on s r) : pairwise_on t r :=
λ x xt y yt, hp x (h xt) y (h yt)

theorem pairwise_on.mono' {s : set α} {r r' : α → α → Prop}
  (H : ∀ a b, r a b → r' a b) (hp : pairwise_on s r) : pairwise_on s r' :=
λ x xs y ys h, H _ _ (hp x xs y ys h)

end set
open set

/-! ### Image and preimage on subtypes -/

namespace subtype

variable {α : Type*}

lemma val_image {p : α → Prop} {s : set (subtype p)} :
  subtype.val '' s = {x | ∃h : p x, (⟨x, h⟩ : subtype p) ∈ s} :=
set.ext $ assume a,
⟨assume ⟨⟨a', ha'⟩, in_s, h_eq⟩, h_eq ▸ ⟨ha', in_s⟩,
  assume ⟨ha, in_s⟩, ⟨⟨a, ha⟩, in_s, rfl⟩⟩

@[simp] lemma val_range {p : α → Prop} :
  set.range (@subtype.val _ p) = {x | p x} :=
by rw ← set.image_univ; simp [-set.image_univ, val_image]

lemma range_val (s : set α) : range (subtype.val : s → α) = s :=
val_range

theorem val_image_subset (s : set α) (t : set (subtype s)) : t.image val ⊆ s :=
λ x ⟨y, yt, yvaleq⟩, by rw ←yvaleq; exact y.property

theorem val_image_univ (s : set α) : @val _ s '' set.univ = s :=
set.eq_of_subset_of_subset (val_image_subset _ _) (λ x xs, ⟨⟨x, xs⟩, ⟨set.mem_univ _, rfl⟩⟩)

theorem image_preimage_val (s t : set α) :
  (@subtype.val _ s) '' ((@subtype.val _ s) ⁻¹' t) = t ∩ s :=
begin
  ext x, simp, split,
  { rintros ⟨y, ys, yt, yx⟩, rw ←yx, exact ⟨yt, ys⟩ },
  rintros ⟨xt, xs⟩, exact ⟨x, xs, xt, rfl⟩
end

theorem preimage_val_eq_preimage_val_iff (s t u : set α) :
  ((@subtype.val _ s) ⁻¹' t = (@subtype.val _ s) ⁻¹' u) ↔ (t ∩ s = u ∩ s) :=
begin
  rw [←image_preimage_val, ←image_preimage_val],
  split, { intro h, rw h },
  intro h, exact set.injective_image (val_injective) h
end

lemma exists_set_subtype {t : set α} (p : set α → Prop) :
(∃(s : set t), p (subtype.val '' s)) ↔ ∃(s : set α), s ⊆ t ∧ p s :=
begin
  split,
  { rintro ⟨s, hs⟩, refine ⟨subtype.val '' s, _, hs⟩,
    convert image_subset_range _ _, rw [range_val] },
  rintro ⟨s, hs₁, hs₂⟩, refine ⟨subtype.val ⁻¹' s, _⟩,
  rw [image_preimage_eq_of_subset], exact hs₂, rw [range_val], exact hs₁
end
end subtype

namespace set

section range

variable {α : Type*}

@[simp] lemma range_coe_subtype (s : set α) : range (coe : s → α) = s :=
subtype.val_range

theorem preimage_coe_eq_preimage_coe_iff {s t u : set α} :
  ((coe : s → α) ⁻¹' t = coe ⁻¹' u) ↔ t ∩ s = u ∩ s :=
subtype.preimage_val_eq_preimage_val_iff _ _ _

end range

/-! ### Lemmas about cartesian product of sets -/

section prod

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables {s s₁ s₂ : set α} {t t₁ t₂ : set β}

/-- The cartesian product `prod s t` is the set of `(a, b)`
  such that `a ∈ s` and `b ∈ t`. -/
protected def prod (s : set α) (t : set β) : set (α × β) :=
{p | p.1 ∈ s ∧ p.2 ∈ t}

lemma prod_eq (s : set α) (t : set β) : set.prod s t = prod.fst ⁻¹' s ∩ prod.snd ⁻¹' t := rfl

theorem mem_prod_eq {p : α × β} : p ∈ set.prod s t = (p.1 ∈ s ∧ p.2 ∈ t) := rfl

@[simp] theorem mem_prod {p : α × β} : p ∈ set.prod s t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

lemma mk_mem_prod {a : α} {b : β} (a_in : a ∈ s) (b_in : b ∈ t) : (a, b) ∈ set.prod s t := ⟨a_in, b_in⟩

lemma prod_subset_iff {P : set (α × β)} :
  (set.prod s t ⊆ P) ↔ ∀ (x ∈ s) (y ∈ t), (x, y) ∈ P :=
⟨λ h _ xin _ yin, h (mk_mem_prod xin yin),
 λ h _ pin, by { cases mem_prod.1 pin with hs ht, simpa using h _ hs _ ht }⟩

@[simp] theorem prod_empty : set.prod s ∅ = (∅ : set (α × β)) :=
ext $ by simp [set.prod]

@[simp] theorem empty_prod : set.prod ∅ t = (∅ : set (α × β)) :=
ext $ by simp [set.prod]

theorem insert_prod {a : α} {s : set α} {t : set β} :
  set.prod (insert a s) t = (prod.mk a '' t) ∪ set.prod s t :=
ext begin simp [set.prod, image, iff_def, or_imp_distrib] {contextual := tt}; cc end

theorem prod_insert {b : β} {s : set α} {t : set β} :
  set.prod s (insert b t) = ((λa, (a, b)) '' s) ∪ set.prod s t :=
ext begin simp [set.prod, image, iff_def, or_imp_distrib] {contextual := tt}; cc end

theorem prod_preimage_eq {f : γ → α} {g : δ → β} :
  set.prod (preimage f s) (preimage g t) = preimage (λp, (f p.1, g p.2)) (set.prod s t) := rfl

theorem prod_mono {s₁ s₂ : set α} {t₁ t₂ : set β} (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) :
  set.prod s₁ t₁ ⊆ set.prod s₂ t₂ :=
assume x ⟨h₁, h₂⟩, ⟨hs h₁, ht h₂⟩

theorem prod_inter_prod : set.prod s₁ t₁ ∩ set.prod s₂ t₂ = set.prod (s₁ ∩ s₂) (t₁ ∩ t₂) :=
subset.antisymm
  (assume ⟨a, b⟩ ⟨⟨ha₁, hb₁⟩, ⟨ha₂, hb₂⟩⟩, ⟨⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩⟩)
  (subset_inter
    (prod_mono (inter_subset_left _ _) (inter_subset_left _ _))
    (prod_mono (inter_subset_right _ _) (inter_subset_right _ _)))

theorem image_swap_prod : (λp:β×α, (p.2, p.1)) '' set.prod t s = set.prod s t :=
ext $ assume ⟨a, b⟩, by simp [mem_image_eq, set.prod, and_comm]; exact
⟨ assume ⟨b', a', ⟨h_a, h_b⟩, h⟩, by subst a'; subst b'; assumption,
  assume h, ⟨b, a, ⟨rfl, rfl⟩, h⟩⟩

theorem image_swap_eq_preimage_swap : image (@prod.swap α β) = preimage prod.swap :=
image_eq_preimage_of_inverse prod.swap_left_inverse prod.swap_right_inverse

theorem prod_image_image_eq {m₁ : α → γ} {m₂ : β → δ} :
  set.prod (image m₁ s) (image m₂ t) = image (λp:α×β, (m₁ p.1, m₂ p.2)) (set.prod s t) :=
ext $ by simp [-exists_and_distrib_right, exists_and_distrib_right.symm, and.left_comm, and.assoc, and.comm]

theorem prod_range_range_eq {α β γ δ} {m₁ : α → γ} {m₂ : β → δ} :
  set.prod (range m₁) (range m₂) = range (λp:α×β, (m₁ p.1, m₂ p.2)) :=
ext $ by simp [range]

theorem prod_range_univ_eq {α β γ} {m₁ : α → γ} :
  set.prod (range m₁) (univ : set β) = range (λp:α×β, (m₁ p.1, p.2)) :=
ext $ by simp [range]

theorem prod_univ_range_eq {α β δ} {m₂ : β → δ} :
  set.prod (univ : set α) (range m₂) = range (λp:α×β, (p.1, m₂ p.2)) :=
ext $ by simp [range]

@[simp] theorem prod_singleton_singleton {a : α} {b : β} :
  set.prod {a} {b} = ({(a, b)} : set (α×β)) :=
ext $ by simp [set.prod]

theorem nonempty.prod : s.nonempty → t.nonempty → (s.prod t).nonempty
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨(x, y), ⟨hx, hy⟩⟩

theorem nonempty.fst : (s.prod t).nonempty → s.nonempty
| ⟨p, hp⟩ := ⟨p.1, hp.1⟩

theorem nonempty.snd : (s.prod t).nonempty → t.nonempty
| ⟨p, hp⟩ := ⟨p.2, hp.2⟩

theorem prod_nonempty_iff : (s.prod t).nonempty ↔ s.nonempty ∧ t.nonempty :=
⟨λ h, ⟨h.fst, h.snd⟩, λ h, nonempty.prod h.1 h.2⟩

theorem prod_eq_empty_iff {s : set α} {t : set β} :
  set.prod s t = ∅ ↔ (s = ∅ ∨ t = ∅) :=
by simp only [not_nonempty_iff_eq_empty.symm, prod_nonempty_iff, classical.not_and_distrib]

@[simp] theorem prod_mk_mem_set_prod_eq {a : α} {b : β} {s : set α} {t : set β} :
  (a, b) ∈ set.prod s t = (a ∈ s ∧ b ∈ t) := rfl

@[simp] theorem univ_prod_univ : set.prod (@univ α) (@univ β) = univ :=
ext $ assume ⟨a, b⟩, by simp

lemma prod_sub_preimage_iff {W : set γ} {f : α × β → γ} :
  set.prod s t ⊆ f ⁻¹' W ↔ ∀ a b, a ∈ s → b ∈ t → f (a, b) ∈ W :=
by simp [subset_def]

lemma fst_image_prod_subset (s : set α) (t : set β) :
  prod.fst '' (set.prod s t) ⊆ s :=
λ _ h, let ⟨_, ⟨h₂, _⟩, h₁⟩ := (set.mem_image _ _ _).1 h in h₁ ▸ h₂

lemma prod_subset_preimage_fst (s : set α) (t : set β) :
  set.prod s t ⊆ prod.fst ⁻¹' s :=
image_subset_iff.1 (fst_image_prod_subset s t)

lemma fst_image_prod (s : set β) {t : set α} (ht : t.nonempty) :
  prod.fst '' (set.prod s t) = s :=
set.subset.antisymm (fst_image_prod_subset _ _)
  $ λ y y_in, let ⟨x, x_in⟩ := ht in
    ⟨(y, x), ⟨y_in, x_in⟩, rfl⟩

lemma snd_image_prod_subset (s : set α) (t : set β) :
  prod.snd '' (set.prod s t) ⊆ t :=
λ _ h, let ⟨_, ⟨_, h₂⟩, h₁⟩ := (set.mem_image _ _ _).1 h in h₁ ▸ h₂

lemma prod_subset_preimage_snd (s : set α) (t : set β) :
  set.prod s t ⊆ prod.snd ⁻¹' t :=
image_subset_iff.1 (snd_image_prod_subset s t)

lemma snd_image_prod {s : set α} (hs : s.nonempty) (t : set β) :
  prod.snd '' (set.prod s t) = t :=
set.subset.antisymm (snd_image_prod_subset _ _)
  $ λ y y_in, let ⟨x, x_in⟩ := hs in
    ⟨(x, y), ⟨x_in, y_in⟩, rfl⟩

/-- A product set is included in a product set if and only factors are included, or a factor of the
first set is empty. -/
lemma prod_subset_prod_iff :
  (set.prod s t ⊆ set.prod s₁ t₁) ↔ (s ⊆ s₁ ∧ t ⊆ t₁) ∨ (s = ∅) ∨ (t = ∅) :=
begin
  classical,
  cases (set.prod s t).eq_empty_or_nonempty with h h,
  { simp [h, prod_eq_empty_iff.1 h] },
  { have st : s.nonempty ∧ t.nonempty, by rwa [prod_nonempty_iff] at h,
    split,
    { assume H : set.prod s t ⊆ set.prod s₁ t₁,
      have h' : s₁.nonempty ∧ t₁.nonempty := prod_nonempty_iff.1 (h.mono H),
      refine or.inl ⟨_, _⟩,
      show s ⊆ s₁,
      { have := image_subset (prod.fst : α × β → α) H,
        rwa [fst_image_prod _ st.2, fst_image_prod _ h'.2] at this },
      show t ⊆ t₁,
      { have := image_subset (prod.snd : α × β → β) H,
        rwa [snd_image_prod st.1, snd_image_prod h'.1] at this } },
    { assume H,
      simp only [st.1.ne_empty, st.2.ne_empty, or_false] at H,
      exact prod_mono H.1 H.2 } }
end

end prod

/-! ### Lemmas about set-indexed products of sets -/

section pi
variables {α : Type*} {π : α → Type*}

/-- Given an index set `i` and a family of sets `s : Πa, set (π a)`, `pi i s`
is the set of dependent functions `f : Πa, π a` such that `f a` belongs to `π a`
whenever `a ∈ i`. -/
def pi (i : set α) (s : Πa, set (π a)) : set (Πa, π a) := { f | ∀a∈i, f a ∈ s a }

@[simp] lemma pi_empty_index (s : Πa, set (π a)) : pi ∅ s = univ := by ext; simp [pi]

@[simp] lemma pi_insert_index (a : α) (i : set α) (s : Πa, set (π a)) :
  pi (insert a i) s = ((λf, f a) ⁻¹' s a) ∩ pi i s :=
by ext; simp [pi, or_imp_distrib, forall_and_distrib]

@[simp] lemma pi_singleton_index (a : α) (s : Πa, set (π a)) :
  pi {a} s = ((λf:(Πa, π a), f a) ⁻¹' s a) :=
by ext; simp [pi]

lemma pi_if {p : α → Prop} [h : decidable_pred p] (i : set α) (s t : Πa, set (π a)) :
  pi i (λa, if p a then s a else t a) = pi {a ∈ i | p a} s ∩ pi {a ∈ i | ¬ p a} t :=
begin
  ext f,
  split,
  { assume h, split; { rintros a ⟨hai, hpa⟩, simpa [*] using h a } },
  { rintros ⟨hs, ht⟩ a hai,
    by_cases p a; simp [*, pi] at * }
end

end pi

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

section inclusion
variable {α : Type*}

/-- `inclusion` is the "identity" function between two subsets `s` and `t`, where `s ⊆ t` -/
def inclusion {s t : set α} (h : s ⊆ t) : s → t :=
λ x : s, (⟨x, h x.2⟩ : t)

@[simp] lemma inclusion_self {s : set α} (x : s) :
  inclusion (set.subset.refl _) x = x := by cases x; refl

@[simp] lemma inclusion_inclusion {s t u : set α} (hst : s ⊆ t) (htu : t ⊆ u)
  (x : s) : inclusion htu (inclusion hst x) = inclusion (set.subset.trans hst htu) x :=
by cases x; refl

@[simp] lemma coe_inclusion {s t : set α} (h : s ⊆ t) (x : s) :
  (inclusion h x : α) = (x : α) := rfl

lemma inclusion_injective {s t : set α} (h : s ⊆ t) :
  function.injective (inclusion h)
| ⟨_, _⟩ ⟨_, _⟩ := subtype.ext.2 ∘ subtype.ext.1

lemma range_inclusion {s t : set α} (h : s ⊆ t) : range (inclusion h) = {x : t | (x:α) ∈ s} :=
ext $ λ ⟨x, hx⟩ , by simp [inclusion]

end inclusion

end set

namespace subsingleton

variables {α : Type*} [subsingleton α]

lemma eq_univ_of_nonempty {s : set α} : s.nonempty → s = univ :=
λ ⟨x, hx⟩, eq_univ_of_forall $ λ y, subsingleton.elim x y ▸ hx

@[elab_as_eliminator]
lemma set_cases {p : set α → Prop} (h0 : p ∅) (h1 : p univ) (s) : p s :=
s.eq_empty_or_nonempty.elim (λ h, h.symm ▸ h0) $ λ h, (eq_univ_of_nonempty h).symm ▸ h1

end subsingleton

namespace function

variables {ι : Sort*} {α : Type*} {β : Type*}

lemma surjective.injective_preimage {f : β → α} (hf : surjective f) : injective (preimage f) :=
assume s t, (preimage_eq_preimage hf).1

lemma surjective.range_eq {f : ι → α} (hf : surjective f) : range f = univ :=
range_iff_surjective.2 hf

lemma surjective.range_comp (g : α → β) {f : ι → α} (hf : surjective f) :
  range (g ∘ f) = range g :=
by rw [range_comp, hf.range_eq, image_univ]

end function
