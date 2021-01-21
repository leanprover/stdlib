/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import order.boolean_algebra

/-!
# Basic properties of sets

Sets in Lean are homogeneous; all their elements have the same type. Sets whose elements
have type `X` are thus defined as `set X := X → Prop`. Note that this function need not
be decidable. The definition is in the core library.

This file provides some basic definitions related to sets and functions not present in the core
library, as well as extra lemmas for functions in the core library (empty set, univ, union,
intersection, insert, singleton, set-theoretic difference, complement, and powerset).

Note that a set is a term, not a type. There is a coersion from `set α` to `Type*` sending
`s` to the corresponding subtype `↥s`.

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

* `s.prod t : set (α × β)` : the subset `s × t`.

* `inclusion s₁ s₂ : ↥s₁ → ↥s₂` : the map `↥s₁ → ↥s₂` induced by an inclusion `s₁ ⊆ s₂`.

## Notation

* `f ⁻¹' t` for `preimage f t`

* `f '' s` for `image f s`

* `sᶜ` for the complement of `s`

## Implementation notes

* `s.nonempty` is to be preferred to `s ≠ ∅` or `∃ x, x ∈ s`. It has the advantage that
the `s.nonempty` dot notation can be used.

* For `s : set α`, do not use `subtype s`. Instead use `↥s` or `(s : Type*)` or `s`.

## Tags

set, sets, subset, subsets, image, preimage, pre-image, range, union, intersection, insert,
singleton, complement, powerset

-/

/-! ### Set coercion to a type -/

open function

universe variables u v w x

run_cmd do e ← tactic.get_env,
  tactic.set_env $ e.mk_protected `set.compl

namespace set

variable {α : Type*}

instance : has_le (set α) := ⟨(⊆)⟩
instance : has_lt (set α) := ⟨λ s t, s ≤ t ∧ ¬t ≤ s⟩  -- `⊂` is not defined until further down

instance {α : Type*} : boolean_algebra (set α) :=
{ sup := (∪),
  le  := (≤),
  lt  := (<),
  inf := (∩),
  bot := ∅,
  compl := set.compl,
  top := univ,
  sdiff := (\),
  .. (infer_instance : boolean_algebra (α → Prop)) }

@[simp] lemma top_eq_univ : (⊤ : set α) = univ := rfl
@[simp] lemma bot_eq_empty : (⊥ : set α) = ∅ := rfl
@[simp] lemma sup_eq_union (s t : set α) : s ⊔ t = s ∪ t := rfl
@[simp] lemma inf_eq_inter (s t : set α) : s ⊓ t = s ∩ t := rfl
@[simp] lemma le_eq_subset (s t : set α) : s ≤ t = (s ⊆ t) := rfl
/-! `set.lt_eq_ssubset` is defined further down -/

/-- Coercion from a set to the corresponding subtype. -/
instance {α : Type*} : has_coe_to_sort (set α) := ⟨_, λ s, {x // x ∈ s}⟩

end set

section set_coe

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
  (∃ x (h : x ∈ s), p x h) ↔ (∃ x : s, p x x.2)  :=
(@set_coe.exists _ _ $ λ x, p x.1 x.2).symm

theorem set_coe.forall' {s : set α} {p : Π x, x ∈ s → Prop} :
  (∀ x (h : x ∈ s), p x h) ↔ (∀ x : s, p x x.2)  :=
(@set_coe.forall _ _ $ λ x, p x.1 x.2).symm

@[simp] theorem set_coe_cast : ∀ {s t : set α} (H' : s = t) (H : @eq (Type u) s t) (x : s),
  cast H x = ⟨x.1, H' ▸ x.2⟩
| s _ rfl _ ⟨x, h⟩ := rfl

theorem set_coe.ext {s : set α} {a b : s} : (↑a : α) = ↑b → a = b :=
subtype.eq

theorem set_coe.ext_iff {s : set α} {a b : s} : (↑a : α) = ↑b ↔ a = b :=
iff.intro set_coe.ext (assume h, h ▸ rfl)

end set_coe

/-- See also `subtype.prop` -/
lemma subtype.mem {α : Type*} {s : set α} (p : s) : (p : α) ∈ s := p.prop

lemma eq.subset {α} {s t : set α} : s = t → s ⊆ t :=
by { rintro rfl x hx, exact hx }

namespace set

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

theorem set_of_set {s : set α} : set_of s = s := rfl

lemma set_of_app_iff {p : α → Prop} {x : α} : { x | p x } x ↔ p x := iff.rfl

theorem mem_def {a : α} {s : set α} : a ∈ s ↔ s a := iff.rfl

instance decidable_mem (s : set α) [H : decidable_pred s] : ∀ a, decidable (a ∈ s) := H

instance decidable_set_of (p : α → Prop) [H : decidable_pred p] : decidable_pred {a | p a} := H

@[simp] theorem set_of_subset_set_of {p q : α → Prop} :
  {a | p a} ⊆ {a | q a} ↔ (∀a, p a → q a) := iff.rfl

@[simp] lemma sep_set_of {p q : α → Prop} : {a ∈ {a | p a } | q a} = {a | p a ∧ q a} := rfl

lemma set_of_and {p q : α → Prop} : {a | p a ∧ q a} = {a | p a} ∩ {a | q a} := rfl

lemma set_of_or {p q : α → Prop} : {a | p a ∨ q a} = {a | p a} ∪ {a | q a} := rfl

/-! ### Lemmas about subsets -/

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
theorem subset_def {s t : set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := rfl

@[refl] theorem subset.refl (a : set α) : a ⊆ a := assume x, id
theorem subset.rfl {s : set α} : s ⊆ s := subset.refl s

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
by simp [subset_def, not_forall]

/-! ### Definition of strict subsets `s ⊂ t` and basic properties. -/

instance : has_ssubset (set α) := ⟨(<)⟩

@[simp] lemma lt_eq_ssubset (s t : set α) : s < t = (s ⊂ t) := rfl

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

lemma nonempty_def : s.nonempty ↔ ∃ x, x ∈ s := iff.rfl

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

lemma nonempty_of_not_subset (h : ¬s ⊆ t) : (s \ t).nonempty :=
let ⟨x, xs, xt⟩ := not_subset.1 h in ⟨x, xs, xt⟩

lemma nonempty_of_ssubset (ht : s ⊂ t) : (t \ s).nonempty :=
nonempty_of_not_subset ht.2

lemma nonempty.of_diff (h : (s \ t).nonempty) : s.nonempty := h.imp $ λ _, and.left

lemma nonempty_of_ssubset' (ht : s ⊂ t) : t.nonempty := (nonempty_of_ssubset ht).of_diff

lemma nonempty.inl (hs : s.nonempty) : (s ∪ t).nonempty := hs.imp $ λ _, or.inl

lemma nonempty.inr (ht : t.nonempty) : (s ∪ t).nonempty := ht.imp $ λ _, or.inr

@[simp] lemma union_nonempty : (s ∪ t).nonempty ↔ s.nonempty ∨ t.nonempty := exists_or_distrib

lemma nonempty.left (h : (s ∩ t).nonempty) : s.nonempty := h.imp $ λ _, and.left

lemma nonempty.right (h : (s ∩ t).nonempty) : t.nonempty := h.imp $ λ _, and.right

lemma nonempty_inter_iff_exists_right : (s ∩ t).nonempty ↔ ∃ x : t, ↑x ∈ s :=
⟨λ ⟨x, xs, xt⟩, ⟨⟨x, xt⟩, xs⟩, λ ⟨⟨x, xt⟩, xs⟩, ⟨x, xs, xt⟩⟩

lemma nonempty_inter_iff_exists_left : (s ∩ t).nonempty ↔ ∃ x : s, ↑x ∈ t :=
⟨λ ⟨x, xs, xt⟩, ⟨⟨x, xs⟩, xt⟩, λ ⟨⟨x, xt⟩, xs⟩, ⟨x, xt, xs⟩⟩

lemma nonempty_iff_univ_nonempty : nonempty α ↔ (univ : set α).nonempty :=
⟨λ ⟨x⟩, ⟨x, trivial⟩, λ ⟨x, _⟩, ⟨x⟩⟩

@[simp] lemma univ_nonempty : ∀ [h : nonempty α], (univ : set α).nonempty
| ⟨x⟩ := ⟨x, trivial⟩

lemma nonempty.to_subtype (h : s.nonempty) : nonempty s :=
nonempty_subtype.2 h

instance [nonempty α] : nonempty (set.univ : set α) := set.univ_nonempty.to_subtype

@[simp] lemma nonempty_insert (a : α) (s : set α) : (insert a s).nonempty := ⟨a, or.inl rfl⟩

lemma nonempty_of_nonempty_subtype [nonempty s] : s.nonempty :=
nonempty_subtype.mp ‹_›

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

theorem eq_empty_of_not_nonempty (h : ¬nonempty α) (s : set α) : s = ∅ :=
eq_empty_of_subset_empty $ λ x hx, h ⟨x⟩

lemma not_nonempty_iff_eq_empty {s : set α} : ¬s.nonempty ↔ s = ∅ :=
by simp only [set.nonempty, eq_empty_iff_forall_not_mem, not_exists]

lemma empty_not_nonempty : ¬(∅ : set α).nonempty :=
not_nonempty_iff_eq_empty.2 rfl

lemma eq_empty_or_nonempty (s : set α) : s = ∅ ∨ s.nonempty :=
classical.by_cases or.inr (λ h, or.inl $ not_nonempty_iff_eq_empty.1 h)

theorem ne_empty_iff_nonempty : s ≠ ∅ ↔ s.nonempty :=
(not_congr not_nonempty_iff_eq_empty.symm).trans not_not

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

@[simp] theorem set_of_true : {x : α | true} = univ := rfl

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

lemma eq_univ_of_subset {s t : set α} (h : s ⊆ t) (hs : s = univ) : t = univ :=
eq_univ_of_univ_subset $ hs ▸ h

@[simp] lemma univ_eq_empty_iff : (univ : set α) = ∅ ↔ ¬ nonempty α :=
eq_empty_iff_forall_not_mem.trans ⟨λ H ⟨x⟩, H x trivial, λ H x _, H ⟨x⟩⟩

lemma exists_mem_of_nonempty (α) : ∀ [nonempty α], ∃x:α, x ∈ (univ : set α)
| ⟨x⟩ := ⟨x, trivial⟩

instance univ_decidable : decidable_pred (@set.univ α) :=
λ x, is_true trivial

/-- `diagonal α` is the subset of `α × α` consisting of all pairs of the form `(a, a)`. -/
def diagonal (α : Type*) : set (α × α) := {p | p.1 = p.2}

@[simp]
lemma mem_diagonal {α : Type*} (x : α) : (x, x) ∈ diagonal α :=
by simp [diagonal]

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

theorem subset_iff_inter_eq_self {s t : set α} : s ⊆ t ↔ s ∩ t = s :=
⟨λ h, inter_eq_self_of_subset_left h, λ h x h1, set.mem_of_mem_inter_right (by {rw h, exact h1})⟩

lemma inter_compl_nonempty_iff {s t : set α} : (s ∩ tᶜ).nonempty ↔ ¬ s ⊆ t :=
begin
  split,
  { rintros ⟨x ,xs, xt⟩ sub,
    exact xt (sub xs) },
  { intros h,
    rcases not_subset.mp h with ⟨x, xs, xt⟩,
    exact ⟨x, xs, xt⟩ }
end

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
by { ext, simp [or.left_comm] }

theorem insert_union : insert a s ∪ t = insert a (s ∪ t) :=
by { ext, simp [or.comm, or.left_comm] }

@[simp] theorem union_insert : s ∪ insert a t = insert a (s ∪ t) :=
by { ext, simp [or.comm, or.left_comm] }

theorem insert_nonempty (a : α) (s : set α) : (insert a s).nonempty :=
⟨a, mem_insert a s⟩

instance (a : α) (s : set α) : nonempty (insert a s : set α) := (insert_nonempty a s).to_subtype

lemma insert_inter (x : α) (s t : set α) : insert x (s ∩ t) = insert x s ∩ insert x t :=
by { ext y, simp [←or_and_distrib_left] }

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
lemma set_of_eq_eq_singleton {a : α} : {n | n = a} = {a} :=
set.ext $ λ n, (set.mem_singleton_iff).symm

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

theorem pair_comm (a b : α) : ({a, b} : set α) = {b, a} :=
ext $ λ x, or_comm _ _

@[simp] theorem singleton_nonempty (a : α) : ({a} : set α).nonempty :=
⟨a, rfl⟩

@[simp] theorem singleton_subset_iff {a : α} {s : set α} : {a} ⊆ s ↔ a ∈ s :=
⟨λh, h (by simp), λh b e, by { rw [mem_singleton_iff] at e, simp [*] }⟩

theorem set_compr_eq_eq_singleton {a : α} : {b | b = a} = {a} :=
by { ext, simp }

@[simp] theorem singleton_union : {a} ∪ s = insert a s :=
rfl

@[simp] theorem union_singleton : s ∪ {a} = insert a s :=
by rw [union_comm, singleton_union]

@[simp] theorem singleton_inter_eq_empty : {a} ∩ s = ∅ ↔ a ∉ s :=
by simp [eq_empty_iff_forall_not_mem]

@[simp] theorem inter_singleton_eq_empty : s ∩ {a} = ∅ ↔ a ∉ s :=
by rw [inter_comm, singleton_inter_eq_empty]

@[simp] theorem singleton_inter_nonempty : ({a} ∩ s).nonempty ↔ a ∈ s :=
by rw [← ne_empty_iff_nonempty, ne.def, singleton_inter_eq_empty, not_not]

@[simp] theorem inter_singleton_nonempty : (s ∩ {a}).nonempty ↔ a ∈ s :=
by rw [inter_comm, singleton_inter_nonempty]

lemma nmem_singleton_empty {s : set α} : s ∉ ({∅} : set (set α)) ↔ s.nonempty :=
by rw [mem_singleton_iff, ← ne.def, ne_empty_iff_nonempty]

instance unique_singleton (a : α) : unique ↥({a} : set α) :=
{ default := ⟨a, mem_singleton a⟩,
  uniq :=
  begin
    intros x,
    apply subtype.ext,
    apply eq_of_mem_singleton (subtype.mem x),
  end}

lemma eq_singleton_iff_unique_mem {s : set α} {a : α} :
  s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
by simp [ext_iff, @iff_def (_ ∈ s), forall_and_distrib, and_comm]

lemma eq_singleton_iff_nonempty_unique_mem {s : set α} {a : α} :
  s = {a} ↔ s.nonempty ∧ ∀ x ∈ s, x = a :=
begin
  split,
  { intros h, subst h, simp, },
  { rintros ⟨hne, h_uniq⟩, rw eq_singleton_iff_unique_mem, refine ⟨_, h_uniq⟩,
    rw ← h_uniq hne.some hne.some_spec, apply hne.some_spec, },
end

/-! ### Lemmas about sets defined as `{x ∈ s | p x}`. -/

theorem mem_sep {s : set α} {p : α → Prop} {x : α} (xs : x ∈ s) (px : p x) : x ∈ {x ∈ s | p x} :=
⟨xs, px⟩

@[simp] theorem sep_mem_eq {s t : set α} : {x ∈ s | x ∈ t} = s ∩ t := rfl

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
by { ext, simp }

@[simp] lemma subset_singleton_iff {α : Type*} {s : set α} {x : α} : s ⊆ {x} ↔ ∀ y ∈ s, y = x :=
iff.rfl

/-! ### Lemmas about complement -/

theorem mem_compl {s : set α} {x : α} (h : x ∉ s) : x ∈ sᶜ := h

lemma compl_set_of {α} (p : α → Prop) : {a | p a}ᶜ = { a | ¬ p a } := rfl

theorem not_mem_of_mem_compl {s : set α} {x : α} (h : x ∈ sᶜ) : x ∉ s := h

@[simp] theorem mem_compl_eq (s : set α) (x : α) : x ∈ sᶜ = (x ∉ s) := rfl

theorem mem_compl_iff (s : set α) (x : α) : x ∈ sᶜ ↔ x ∉ s := iff.rfl

@[simp] theorem inter_compl_self (s : set α) : s ∩ sᶜ = ∅ := inf_compl_eq_bot

@[simp] theorem compl_inter_self (s : set α) : sᶜ ∩ s = ∅ := compl_inf_eq_bot

@[simp] theorem compl_empty : (∅ : set α)ᶜ = univ := compl_bot

@[simp] theorem compl_union (s t : set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := compl_sup

theorem compl_inter (s t : set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := compl_inf

@[simp] theorem compl_univ : (univ : set α)ᶜ = ∅ := compl_top

@[simp] lemma compl_empty_iff {s : set α} : sᶜ = ∅ ↔ s = univ := compl_eq_bot

@[simp] lemma compl_univ_iff {s : set α} : sᶜ = univ ↔ s = ∅ := compl_eq_top

lemma nonempty_compl {s : set α} : sᶜ.nonempty ↔ s ≠ univ :=
ne_empty_iff_nonempty.symm.trans $ not_congr $ compl_empty_iff

lemma mem_compl_singleton_iff {a x : α} : x ∈ ({a} : set α)ᶜ ↔ x ≠ a :=
not_congr mem_singleton_iff

lemma compl_singleton_eq (a : α) : ({a} : set α)ᶜ = {x | x ≠ a} :=
ext $ λ x, mem_compl_singleton_iff

theorem union_eq_compl_compl_inter_compl (s t : set α) : s ∪ t = (sᶜ ∩ tᶜ)ᶜ :=
by simp [compl_inter, compl_compl]

theorem inter_eq_compl_compl_union_compl (s t : set α) : s ∩ t = (sᶜ ∪ tᶜ)ᶜ :=
by simp [compl_compl]

@[simp] theorem union_compl_self (s : set α) : s ∪ sᶜ = univ :=
by finish [ext_iff]

@[simp] theorem compl_union_self (s : set α) : sᶜ ∪ s = univ :=
by finish [ext_iff]

theorem compl_comp_compl : compl ∘ compl = @id (set α) :=
funext compl_compl

theorem compl_subset_comm {s t : set α} : sᶜ ⊆ t ↔ tᶜ ⊆ s :=
@compl_le_iff_compl_le _ s t _

lemma compl_subset_compl {s t : set α} : sᶜ ⊆ tᶜ ↔ t ⊆ s :=
@compl_le_compl_iff_le _ t s _

theorem compl_subset_iff_union {s t : set α} : sᶜ ⊆ t ↔ s ∪ t = univ :=
iff.symm $ eq_univ_iff_forall.trans $ forall_congr $ λ a,
by haveI := classical.prop_decidable; exact or_iff_not_imp_left

theorem subset_compl_comm {s t : set α} : s ⊆ tᶜ ↔ t ⊆ sᶜ :=
forall_congr $ λ a, imp_not_comm

theorem subset_compl_iff_disjoint {s t : set α} : s ⊆ tᶜ ↔ s ∩ t = ∅ :=
iff.trans (forall_congr $ λ a, and_imp.symm) subset_empty_iff

lemma subset_compl_singleton_iff {a : α} {s : set α} : s ⊆ {a}ᶜ ↔ a ∉ s :=
by { rw subset_compl_comm, simp }

theorem inter_subset (a b c : set α) : a ∩ b ⊆ c ↔ a ⊆ bᶜ ∪ c :=
begin
  classical,
  split,
  { intros h x xa, by_cases h' : x ∈ b, simp [h ⟨xa, h'⟩], simp [h'] },
  intros h x, rintro ⟨xa, xb⟩, cases h xa, contradiction, assumption
end

/-! ### Lemmas about set difference -/

theorem diff_eq (s t : set α) : s \ t = s ∩ tᶜ := rfl

@[simp] theorem mem_diff {s t : set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := iff.rfl

theorem mem_diff_of_mem {s t : set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t :=
⟨h1, h2⟩

theorem mem_of_mem_diff {s t : set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
h.left

theorem not_mem_of_mem_diff {s t : set α} {x : α} (h : x ∈ s \ t) : x ∉ t :=
h.right

theorem diff_eq_compl_inter {s t : set α} : s \ t = tᶜ ∩ s :=
by rw [diff_eq, inter_comm]

theorem nonempty_diff {s t : set α} : (s \ t).nonempty ↔ ¬ (s ⊆ t) :=
⟨λ ⟨x, xs, xt⟩, not_subset.2 ⟨x, xs, xt⟩,
  λ h, let ⟨x, xs, xt⟩ := not_subset.1 h in ⟨x, xs, xt⟩⟩

theorem union_diff_cancel' {s t u : set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : t ∪ (u \ s) = u :=
by finish [ext_iff, iff_def, subset_def]

theorem union_diff_cancel {s t : set α} (h : s ⊆ t) : s ∪ (t \ s) = t :=
union_diff_cancel' (subset.refl s) h

theorem union_diff_cancel_left {s t : set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ s = t :=
by finish [ext_iff, iff_def, subset_def]

theorem union_diff_cancel_right {s t : set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ t = s :=
by finish [ext_iff, iff_def, subset_def]

@[simp] theorem union_diff_left {s t : set α} : (s ∪ t) \ s = t \ s :=
by finish [ext_iff, iff_def]

@[simp] theorem union_diff_right {s t : set α} : (s ∪ t) \ t = s \ t :=
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

@[simp] theorem inter_diff_self (a b : set α) : a ∩ (b \ a) = ∅ :=
by finish [ext_iff]

@[simp] theorem inter_union_diff (s t : set α) : (s ∩ t) ∪ (s \ t) = s :=
by finish [ext_iff, iff_def]

@[simp] theorem inter_union_compl (s t : set α) : (s ∩ t) ∪ (s ∩ tᶜ) = s := inter_union_diff _ _

theorem diff_subset (s t : set α) : s \ t ⊆ s :=
by finish [subset_def]

theorem diff_subset_diff {s₁ s₂ t₁ t₂ : set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
by finish [subset_def]

theorem diff_subset_diff_left {s₁ s₂ t : set α} (h : s₁ ⊆ s₂) : s₁ \ t ⊆ s₂ \ t :=
diff_subset_diff h (by refl)

theorem diff_subset_diff_right {s t u : set α} (h : t ⊆ u) : s \ u ⊆ s \ t :=
diff_subset_diff (subset.refl s) h

theorem compl_eq_univ_diff (s : set α) : sᶜ = univ \ s :=
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

-- the following statement contains parentheses to help the reader
lemma diff_diff_comm {s t u : set α} : (s \ t) \ u = (s \ u) \ t :=
by simp_rw [diff_diff, union_comm]

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
ext $ λ x, by simp [not_and_distrib, and_or_distrib_left]

lemma diff_inter_diff {s t u : set α} : s \ t ∩ (s \ u) = s \ (t ∪ u) :=
by { ext x, simp only [mem_inter_eq, mem_union_eq, mem_diff, not_or_distrib, and.left_comm,
  and.assoc, and_self_left] }

lemma diff_compl : s \ tᶜ = s ∩ t := by rw [diff_eq, compl_compl]

lemma diff_diff_right {s t u : set α} : s \ (t \ u) = (s \ t) ∪ (s ∩ u) :=
by rw [diff_eq t u, diff_inter, diff_compl]

@[simp] theorem insert_diff_of_mem (s) (h : a ∈ t) : insert a s \ t = s \ t :=
by { ext, split; simp [or_imp_distrib, h] {contextual := tt} }

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

lemma insert_diff_self_of_not_mem {a : α} {s : set α} (h : a ∉ s) :
  insert a s \ {a} = s :=
by { ext, simp [and_iff_left_of_imp (λ hx : x ∈ s, show x ≠ a, from λ hxa, h $ hxa ▸ hx)] }

theorem union_diff_self {s t : set α} : s ∪ (t \ s) = s ∪ t :=
by finish [ext_iff, iff_def]

theorem diff_union_self {s t : set α} : (s \ t) ∪ t = s ∪ t :=
by rw [union_comm, union_diff_self, union_comm]

theorem diff_inter_self {a b : set α} : (b \ a) ∩ a = ∅ :=
by { ext, by simp [iff_def] {contextual:=tt} }

theorem diff_inter_self_eq_diff {s t : set α} : s \ (t ∩ s) = s \ t :=
by { ext, simp [iff_def] {contextual := tt} }

theorem diff_self_inter {s t : set α} : s \ (s ∩ t) = s \ t :=
by rw [inter_comm, diff_inter_self_eq_diff]

theorem diff_eq_self {s t : set α} : s \ t = s ↔ t ∩ s ⊆ ∅ :=
by finish [ext_iff, iff_def, subset_def]

@[simp] theorem diff_singleton_eq_self {a : α} {s : set α} (h : a ∉ s) : s \ {a} = s :=
diff_eq_self.2 $ by simp [singleton_inter_eq_empty.2 h]

@[simp] theorem insert_diff_singleton {a : α} {s : set α} :
  insert a (s \ {a}) = insert a s :=
by simp [insert_eq, union_diff_self, -union_singleton, -singleton_union]

@[simp] lemma diff_self {s : set α} : s \ s = ∅ := by { ext, simp }

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

@[simp] theorem mem_powerset_iff (x s : set α) : x ∈ powerset s ↔ x ⊆ s := iff.rfl

theorem powerset_inter (s t : set α) : 𝒫 (s ∩ t) = 𝒫 s ∩ 𝒫 t :=
ext $ λ u, subset_inter_iff

@[simp] theorem powerset_mono : 𝒫 s ⊆ 𝒫 t ↔ s ⊆ t :=
⟨λ h, h (subset.refl s), λ h u hu, subset.trans hu h⟩

theorem monotone_powerset : monotone (powerset : set α → set (set α)) :=
λ s t, powerset_mono.2

@[simp] theorem powerset_nonempty : (𝒫 s).nonempty :=
⟨∅, empty_subset s⟩

@[simp] theorem powerset_empty : 𝒫 (∅ : set α) = {∅} :=
ext $ λ s, subset_empty_iff

/-! ### Inverse image -/

/-- The preimage of `s : set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
def preimage {α : Type u} {β : Type v} (f : α → β) (s : set β) : set α := {x | f x ∈ s}

infix ` ⁻¹' `:80 := preimage

section preimage
variables {f : α → β} {g : β → γ}

@[simp] theorem preimage_empty : f ⁻¹' ∅ = ∅ := rfl

@[simp] theorem mem_preimage {s : set β} {a : α} : (a ∈ f ⁻¹' s) ↔ (f a ∈ s) := iff.rfl

lemma preimage_congr {f g : α → β} {s : set β} (h : ∀ (x : α), f x = g x) : f ⁻¹' s = g ⁻¹' s :=
by { congr' with x, apply_assumption }

theorem preimage_mono {s t : set β} (h : s ⊆ t) : f ⁻¹' s ⊆ f ⁻¹' t :=
assume x hx, h hx

@[simp] theorem preimage_univ : f ⁻¹' univ = univ := rfl

theorem subset_preimage_univ {s : set α} : s ⊆ f ⁻¹' univ := subset_univ _

@[simp] theorem preimage_inter {s t : set β} : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := rfl

@[simp] theorem preimage_union {s t : set β} : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t := rfl

@[simp] theorem preimage_compl {s : set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ := rfl

@[simp] theorem preimage_diff (f : α → β) (s t : set β) :
  f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t := rfl

@[simp] theorem preimage_set_of_eq {p : α → Prop} {f : β → α} : f ⁻¹' {a | p a} = {a | p (f a)} :=
rfl

@[simp] theorem preimage_id {s : set α} : id ⁻¹' s = s := rfl

@[simp] theorem preimage_id' {s : set α} : (λ x, x) ⁻¹' s = s := rfl

theorem preimage_const_of_mem {b : β} {s : set β} (h : b ∈ s) :
  (λ (x : α), b) ⁻¹' s = univ :=
eq_univ_of_forall $ λ x, h

theorem preimage_const_of_not_mem {b : β} {s : set β} (h : b ∉ s) :
  (λ (x : α), b) ⁻¹' s = ∅ :=
eq_empty_of_subset_empty $ λ x hx, h hx

theorem preimage_const (b : β) (s : set β) [decidable (b ∈ s)] :
  (λ (x : α), b) ⁻¹' s = if b ∈ s then univ else ∅ :=
by { split_ifs with hb hb, exacts [preimage_const_of_mem hb, preimage_const_of_not_mem hb] }

theorem preimage_comp {s : set γ} : (g ∘ f) ⁻¹' s = f ⁻¹' (g ⁻¹' s) := rfl

lemma preimage_preimage {g : β → γ} {f : α → β} {s : set γ} :
  f ⁻¹' (g ⁻¹' s) = (λ x, g (f x)) ⁻¹' s :=
preimage_comp.symm

theorem eq_preimage_subtype_val_iff {p : α → Prop} {s : set (subtype p)} {t : set α} :
  s = subtype.val ⁻¹' t ↔ (∀x (h : p x), (⟨x, h⟩ : subtype p) ∈ s ↔ x ∈ t) :=
⟨assume s_eq x h, by { rw [s_eq], simp },
 assume h, ext $ λ ⟨x, hx⟩, by simp [h]⟩

lemma preimage_coe_coe_diagonal {α : Type*} (s : set α) :
  (prod.map coe coe) ⁻¹' (diagonal α) = diagonal s :=
begin
  ext ⟨⟨x, x_in⟩, ⟨y, y_in⟩⟩,
  simp [set.diagonal],
end

end preimage

/-! ### Image of a set under a function -/

section image

infix ` '' `:80 := image

theorem mem_image_iff_bex {f : α → β} {s : set α} {y : β} :
  y ∈ f '' s ↔ ∃ x (_ : x ∈ s), f x = y := bex_def.symm

theorem mem_image_eq (f : α → β) (s : set α) (y: β) : y ∈ f '' s = ∃ x, x ∈ s ∧ f x = y := rfl

@[simp] theorem mem_image (f : α → β) (s : set α) (y : β) :
  y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y := iff.rfl

lemma image_eta (f : α → β) : f '' s = (λ x, f x) '' s := rfl

theorem mem_image_of_mem (f : α → β) {x : α} {a : set α} (h : x ∈ a) : f x ∈ f '' a :=
⟨_, h, rfl⟩

theorem mem_image_of_injective {f : α → β} {a : α} {s : set α} (hf : injective f) :
  f a ∈ f '' s ↔ a ∈ s :=
iff.intro
  (assume ⟨b, hb, eq⟩, (hf eq) ▸ hb)
  (assume h, mem_image_of_mem _ h)

theorem ball_image_iff {f : α → β} {s : set α} {p : β → Prop} :
  (∀ y ∈ f '' s, p y) ↔ (∀ x ∈ s, p (f x)) :=
by simp

theorem ball_image_of_ball {f : α → β} {s : set α} {p : β → Prop}
  (h : ∀ x ∈ s, p (f x)) : ∀ y ∈ f '' s, p y :=
ball_image_iff.2 h

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

@[simp] theorem image_empty (f : α → β) : f '' ∅ = ∅ := by { ext, simp }

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
eq_univ_of_forall $ by { simpa [image] }

@[simp] theorem image_singleton {f : α → β} {a : α} : f '' {a} = {f a} :=
by { ext, simp [image, eq_comm] }

@[simp] theorem nonempty.image_const {s : set α} (hs : s.nonempty) (a : β) : (λ _, a) '' s = {a} :=
ext $ λ x, ⟨λ ⟨y, _, h⟩, h ▸ mem_singleton _,
  λ h, (eq_of_mem_singleton h).symm ▸ hs.imp (λ y hy, ⟨hy, rfl⟩)⟩

@[simp] lemma image_eq_empty {α β} {f : α → β} {s : set α} : f '' s = ∅ ↔ s = ∅ :=
by { simp only [eq_empty_iff_forall_not_mem],
     exact ⟨λ H a ha, H _ ⟨_, ha, rfl⟩, λ H b ⟨_, ha, _⟩, H _ ha⟩ }

-- TODO(Jeremy): there is an issue with - t unfolding to compl t
theorem mem_compl_image (t : set α) (S : set (set α)) :
  t ∈ compl '' S ↔ tᶜ ∈ S :=
begin
  suffices : ∀ x, xᶜ = t ↔ tᶜ = x, { simp [this] },
  intro x, split; { intro e, subst e, simp }
end

/-- A variant of `image_id` -/
@[simp] lemma image_id' (s : set α) : (λx, x) '' s = s := by { ext, simp }

theorem image_id (s : set α) : id '' s = s := by simp

theorem compl_compl_image (S : set (set α)) :
  compl '' (compl '' S) = S :=
by rw [← image_comp, compl_comp_compl, image_id]

theorem image_insert_eq {f : α → β} {a : α} {s : set α} :
  f '' (insert a s) = insert (f a) (f '' s) :=
by { ext, simp [and_or_distrib_left, exists_or_distrib, eq_comm, or_comm, and_comm] }

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

theorem image_compl_subset {f : α → β} {s : set α} (H : injective f) : f '' sᶜ ⊆ (f '' s)ᶜ :=
subset_compl_iff_disjoint.2 $ by simp [image_inter H]

theorem subset_image_compl {f : α → β} {s : set α} (H : surjective f) : (f '' s)ᶜ ⊆ f '' sᶜ :=
compl_subset_iff_union.2 $
by { rw ← image_union, simp [image_univ_of_surjective H] }

theorem image_compl_eq {f : α → β} {s : set α} (H : bijective f) : f '' sᶜ = (f '' s)ᶜ :=
subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)

theorem subset_image_diff (f : α → β) (s t : set α) :
  f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  rw [diff_subset_iff, ← image_union, union_diff_self],
  exact image_subset f (subset_union_right t s)
end

theorem image_diff {f : α → β} (hf : injective f) (s t : set α) :
  f '' (s \ t) = f '' s \ f '' t :=
subset.antisymm
  (subset.trans (image_inter_subset _ _ _) $ inter_subset_inter_right _ $ image_compl_subset hf)
  (subset_image_diff f s t)

lemma nonempty.image (f : α → β) {s : set α} : s.nonempty → (f '' s).nonempty
| ⟨x, hx⟩ := ⟨f x, mem_image_of_mem f hx⟩

lemma nonempty.of_image {f : α → β} {s : set α} : (f '' s).nonempty → s.nonempty
| ⟨y, x, hx, _⟩ := ⟨x, hx⟩

@[simp] lemma nonempty_image_iff {f : α → β} {s : set α} :
  (f '' s).nonempty ↔ s.nonempty :=
⟨nonempty.of_image, λ h, h.image f⟩

instance (f : α → β) (s : set α) [nonempty s] : nonempty (f '' s) :=
(set.nonempty.image f nonempty_of_nonempty_subtype).to_subtype

/-- image and preimage are a Galois connection -/
@[simp] theorem image_subset_iff {s : set α} {t : set β} {f : α → β} :
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

theorem image_preimage_eq {f : α → β} (s : set β) (h : surjective f) : f '' (f ⁻¹' s) = s :=
subset.antisymm
  (image_preimage_subset f s)
  (λ x hx, let ⟨y, e⟩ := h x in ⟨y, (e.symm ▸ hx : f y ∈ s), e⟩)

lemma preimage_eq_preimage {f : β → α} (hf : surjective f) : f ⁻¹' s = f ⁻¹' t ↔ s = t :=
iff.intro
  (assume eq, by rw [← image_preimage_eq s hf, ← image_preimage_eq t hf, eq])
  (assume eq, eq ▸ rfl)

lemma image_inter_preimage (f : α → β) (s : set α) (t : set β) :
  f '' (s ∩ f ⁻¹' t) = f '' s ∩ t :=
begin
  apply subset.antisymm,
  { calc f '' (s ∩ f ⁻¹' t) ⊆ f '' s ∩ (f '' (f⁻¹' t)) : image_inter_subset _ _ _
  ... ⊆ f '' s ∩ t : inter_subset_inter_right _ (image_preimage_subset f t) },
  { rintros _ ⟨⟨x, h', rfl⟩, h⟩,
    exact ⟨x, ⟨h', h⟩, rfl⟩ }
end

lemma image_preimage_inter (f : α → β) (s : set α) (t : set β) :
  f '' (f ⁻¹' t ∩ s) = t ∩ f '' s :=
by simp only [inter_comm, image_inter_preimage]

@[simp] lemma image_inter_nonempty_iff {f : α → β} {s : set α} {t : set β} :
  (f '' s ∩ t).nonempty ↔ (s ∩ f ⁻¹' t).nonempty :=
by rw [←image_inter_preimage, nonempty_image_iff]

lemma image_diff_preimage {f : α → β} {s : set α} {t : set β} : f '' (s \ f ⁻¹' t) = f '' s \ t :=
by simp_rw [diff_eq, ← preimage_compl, image_inter_preimage]

theorem compl_image : image (compl : set α → set α) = preimage compl :=
image_eq_preimage_of_inverse compl_compl compl_compl

theorem compl_image_set_of {p : set α → Prop} :
  compl '' {s | p s} = {s | p sᶜ} :=
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

/-- `s`, coerced to a type, is a subsingleton type if and only if `s`
is a subsingleton set. -/
@[simp, norm_cast] lemma subsingleton_coe (s : set α) : subsingleton s ↔ s.subsingleton :=
begin
  split,
  { refine λ h, (λ a ha b hb, _),
    exact set_coe.ext_iff.2 (@subsingleton.elim s h ⟨a, ha⟩ ⟨b, hb⟩) },
  { exact λ h, subsingleton.intro (λ a b, set_coe.ext (h a.property b.property)) }
end

/-- `s` is a subsingleton, if its image of an injective function is. -/
theorem subsingleton_of_image {α β : Type*} {f : α → β} (hf : function.injective f)
  (s : set α) (hs : subsingleton (f '' s)) : subsingleton s :=
subsingleton.intro $ λ ⟨a, ha⟩ ⟨b, hb⟩, subtype.ext $ hf
  (by {simpa using @subsingleton.elim _ hs ⟨f a, ⟨a, ha, rfl⟩⟩ ⟨f b, ⟨b, hb, rfl⟩⟩})

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

@[simp] theorem mem_range_self (i : ι) : f i ∈ range f := ⟨i, rfl⟩

theorem forall_range_iff {p : α → Prop} : (∀ a ∈ range f, p a) ↔ (∀ i, p (f i)) :=
by simp

theorem exists_range_iff {p : α → Prop} : (∃ a ∈ range f, p a) ↔ (∃ i, p (f i)) :=
by simp

lemma exists_range_iff' {p : α → Prop} :
  (∃ a, a ∈ range f ∧ p a) ↔ ∃ i, p (f i) :=
by simpa only [exists_prop] using exists_range_iff

theorem range_iff_surjective : range f = univ ↔ surjective f :=
eq_univ_iff_forall

alias range_iff_surjective ↔ _ function.surjective.range_eq

@[simp] theorem range_id : range (@id α) = univ := range_iff_surjective.2 surjective_id

theorem is_compl_range_inl_range_inr : is_compl (range $ @sum.inl α β) (range sum.inr) :=
⟨by { rintro y ⟨⟨x₁, rfl⟩, ⟨x₂, _⟩⟩, cc },
  by { rintro (x|y) -; [left, right]; exact mem_range_self _ }⟩

@[simp] theorem range_inl_union_range_inr : range (sum.inl : α → α ⊕ β) ∪ range sum.inr = univ :=
is_compl_range_inl_range_inr.sup_eq_top

@[simp] theorem range_inl_inter_range_inr : range (sum.inl : α → α ⊕ β) ∩ range sum.inr = ∅ :=
is_compl_range_inl_range_inr.inf_eq_bot

@[simp] theorem range_inr_union_range_inl : range (sum.inr : β → α ⊕ β) ∪ range sum.inl = univ :=
is_compl_range_inl_range_inr.symm.sup_eq_top

@[simp] theorem range_inr_inter_range_inl : range (sum.inr : β → α ⊕ β) ∩ range sum.inl = ∅ :=
is_compl_range_inl_range_inr.symm.inf_eq_bot

@[simp] theorem preimage_inl_range_inr : sum.inl ⁻¹' range (sum.inr : β → α ⊕ β) = ∅ :=
by { ext, simp }

@[simp] theorem preimage_inr_range_inl : sum.inr ⁻¹' range (sum.inl : α → α ⊕ β) = ∅ :=
by { ext, simp }

@[simp] theorem range_quot_mk (r : α → α → Prop) : range (quot.mk r) = univ :=
(surjective_quot_mk r).range_eq

@[simp] theorem image_univ {ι : Type*} {f : ι → β} : f '' univ = range f :=
by { ext, simp [image, range] }

theorem image_subset_range {ι : Type*} (f : ι → β) (s : set ι) : f '' s ⊆ range f :=
by rw ← image_univ; exact image_subset _ (subset_univ _)

theorem range_comp (g : α → β) (f : ι → α) : range (g ∘ f) = g '' range f :=
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

instance [nonempty ι] (f : ι → α) : nonempty (range f) := (range_nonempty f).to_subtype

@[simp] lemma image_union_image_compl_eq_range (f : α → β) :
  (f '' s) ∪ (f '' sᶜ) = range f :=
by rw [← image_union, ← image_univ, ← union_compl_self]

theorem image_preimage_eq_inter_range {f : α → β} {t : set β} :
  f '' (f ⁻¹' t) = t ∩ range f :=
ext $ assume x, ⟨assume ⟨x, hx, heq⟩, heq ▸ ⟨hx, mem_range_self _⟩,
  assume ⟨hx, ⟨y, h_eq⟩⟩, h_eq ▸ mem_image_of_mem f $
    show y ∈ f ⁻¹' t, by simp [preimage, h_eq, hx]⟩

lemma image_preimage_eq_of_subset {f : α → β} {s : set β} (hs : s ⊆ range f) :
  f '' (f ⁻¹' s) = s :=
by rw [image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]

lemma image_preimage_eq_iff {f : α → β} {s : set β} : f '' (f ⁻¹' s) = s ↔ s ⊆ range f :=
⟨by { intro h, rw [← h], apply image_subset_range }, image_preimage_eq_of_subset⟩

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

@[simp] theorem preimage_inter_range {f : α → β} {s : set β} : f ⁻¹' (s ∩ range f) = f ⁻¹' s :=
set.ext $ λ x, and_iff_left ⟨x, rfl⟩

@[simp] theorem preimage_range_inter {f : α → β} {s : set β} : f ⁻¹' (range f ∩ s) = f ⁻¹' s :=
by rw [inter_comm, preimage_inter_range]

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

lemma diagonal_eq_range {α  : Type*} : diagonal α = range (λ x, (x, x)) :=
by { ext ⟨x, y⟩, simp [diagonal, eq_comm] }

theorem preimage_singleton_nonempty {f : α → β} {y : β} :
  (f ⁻¹' {y}).nonempty ↔ y ∈ range f :=
iff.rfl

theorem preimage_singleton_eq_empty {f : α → β} {y : β} :
  f ⁻¹' {y} = ∅ ↔ y ∉ range f :=
not_nonempty_iff_eq_empty.symm.trans $ not_congr preimage_singleton_nonempty

lemma range_subset_singleton {f : ι → α} {x : α} : range f ⊆ {x} ↔ f = const ι x :=
by simp [range_subset_iff, funext_iff, mem_singleton]

lemma image_compl_preimage {f : α → β} {s : set β} : f '' ((f ⁻¹' s)ᶜ) = range f \ s :=
by rw [compl_eq_univ_diff, image_diff_preimage, image_univ]

@[simp] theorem range_sigma_mk {β : α → Type*} (a : α) :
  range (sigma.mk a : β a → Σ a, β a) = sigma.fst ⁻¹' {a} :=
begin
  apply subset.antisymm,
  { rintros _ ⟨b, rfl⟩, simp },
  { rintros ⟨x, y⟩ (rfl|_),
    exact mem_range_self y }
end

/-- Any map `f : ι → β` factors through a map `range_factorization f : ι → range f`. -/
def range_factorization (f : ι → β) : ι → range f :=
λ i, ⟨f i, mem_range_self i⟩

lemma range_factorization_eq {f : ι → β} :
  subtype.val ∘ range_factorization f = f :=
funext $ λ i, rfl

lemma surjective_onto_range : surjective (range_factorization f) :=
λ ⟨_, ⟨i, rfl⟩⟩, ⟨i, rfl⟩

lemma image_eq_range (f : α → β) (s : set α) : f '' s = range (λ(x : s), f x) :=
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

@[simp] lemma preimage_range (f : α → β) : f ⁻¹' (range f) = univ :=
eq_univ_of_forall mem_range_self

/-- The range of a function from a `unique` type contains just the
function applied to its single value. -/
lemma range_unique [h : unique ι] : range f = {f $ default ι} :=
begin
  ext x,
  rw mem_range,
  split,
  { rintros ⟨i, hi⟩,
    rw h.uniq i at hi,
    exact hi ▸ mem_singleton _ },
  { exact λ h, ⟨default ι, h.symm⟩ }
end

lemma range_diff_image_subset (f : α → β) (s : set α) :
  range f \ f '' s ⊆ f '' sᶜ :=
λ y ⟨⟨x, h₁⟩, h₂⟩, ⟨x, λ h, h₂ ⟨x, h, h₁⟩, h₁⟩

lemma range_diff_image {f : α → β} (H : injective f) (s : set α) :
  range f \ f '' s = f '' sᶜ :=
subset.antisymm (range_diff_image_subset f s) $ λ y ⟨x, hx, hy⟩, hy ▸
  ⟨mem_range_self _, λ ⟨x', hx', eq⟩, hx $ H eq ▸ hx'⟩

end range

/-- The set `s` is pairwise `r` if `r x y` for all *distinct* `x y ∈ s`. -/
def pairwise_on (s : set α) (r : α → α → Prop) := ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r x y

theorem pairwise_on.mono {s t : set α} {r}
  (h : t ⊆ s) (hp : pairwise_on s r) : pairwise_on t r :=
λ x xt y yt, hp x (h xt) y (h yt)

theorem pairwise_on.mono' {s : set α} {r r' : α → α → Prop}
  (H : ∀ a b, r a b → r' a b) (hp : pairwise_on s r) : pairwise_on s r' :=
λ x xs y ys h, H _ _ (hp x xs y ys h)

/-- If and only if `f` takes pairwise equal values on `s`, there is
some value it takes everywhere on `s`. -/
lemma pairwise_on_eq_iff_exists_eq [nonempty β] (s : set α) (f : α → β) :
  (pairwise_on s (λ x y, f x = f y)) ↔ ∃ z, ∀ x ∈ s, f x = z :=
begin
  split,
  { intro h,
    rcases eq_empty_or_nonempty s with rfl | ⟨x, hx⟩,
    { exact ⟨classical.arbitrary β, λ x hx, false.elim hx⟩ },
    { use f x,
      intros y hy,
      by_cases hyx : y = x,
      { rw hyx },
      { exact h y hy x hx hyx } } },
  { rintros ⟨z, hz⟩ x hx y hy hne,
    rw [hz x hx, hz y hy] }
end

end set
open set

namespace function

variables {ι : Sort*} {α : Type*} {β : Type*} {f : α → β}

lemma surjective.preimage_injective (hf : surjective f) : injective (preimage f) :=
assume s t, (preimage_eq_preimage hf).1

lemma injective.preimage_image (hf : injective f) (s : set α) : f ⁻¹' (f '' s) = s :=
preimage_image_eq s hf

lemma injective.preimage_surjective (hf : injective f) : surjective (preimage f) :=
by { intro s, use f '' s, rw hf.preimage_image }

lemma surjective.image_preimage (hf : surjective f) (s : set β) : f '' (f ⁻¹' s) = s :=
image_preimage_eq s hf

lemma surjective.image_surjective (hf : surjective f) : surjective (image f) :=
by { intro s, use f ⁻¹' s, rw hf.image_preimage }

lemma injective.image_injective (hf : injective f) : injective (image f) :=
by { intros s t h, rw [←preimage_image_eq s hf, ←preimage_image_eq t hf, h] }

lemma surjective.preimage_subset_preimage_iff {s t : set β} (hf : surjective f) :
  f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t :=
by { apply preimage_subset_preimage_iff, rw [hf.range_eq], apply subset_univ }

lemma surjective.range_comp {ι' : Sort*} {f : ι → ι'} (hf : surjective f) (g : ι' → α) :
  range (g ∘ f) = range g :=
ext $ λ y, (@surjective.exists _ _ _ hf (λ x, g x = y)).symm

lemma injective.nonempty_apply_iff {f : set α → set β} (hf : injective f)
  (h2 : f ∅ = ∅) {s : set α} : (f s).nonempty ↔ s.nonempty :=
by rw [← ne_empty_iff_nonempty, ← h2, ← ne_empty_iff_nonempty, hf.ne_iff]

end function
open function

/-! ### Image and preimage on subtypes -/

namespace subtype

variable {α : Type*}

lemma coe_image {p : α → Prop} {s : set (subtype p)} :
  coe '' s = {x | ∃h : p x, (⟨x, h⟩ : subtype p) ∈ s} :=
set.ext $ assume a,
⟨assume ⟨⟨a', ha'⟩, in_s, h_eq⟩, h_eq ▸ ⟨ha', in_s⟩,
  assume ⟨ha, in_s⟩, ⟨⟨a, ha⟩, in_s, rfl⟩⟩

lemma range_coe {s : set α} :
  range (coe : s → α) = s :=
by { rw ← set.image_univ, simp [-set.image_univ, coe_image] }

/-- A variant of `range_coe`. Try to use `range_coe` if possible.
  This version is useful when defining a new type that is defined as the subtype of something.
  In that case, the coercion doesn't fire anymore. -/
lemma range_val {s : set α} :
  range (subtype.val : s → α) = s :=
range_coe

/-- We make this the simp lemma instead of `range_coe`. The reason is that if we write
  for `s : set α` the function `coe : s → α`, then the inferred implicit arguments of `coe` are
  `coe α (λ x, x ∈ s)`. -/
@[simp] lemma range_coe_subtype {p : α → Prop} :
  range (coe : subtype p → α) = {x | p x} :=
range_coe

@[simp] lemma coe_preimage_self (s : set α) : (coe : s → α) ⁻¹' s = univ :=
by rw [← preimage_range (coe : s → α), range_coe]

lemma range_val_subtype {p : α → Prop} :
  range (subtype.val : subtype p → α) = {x | p x} :=
range_coe

theorem coe_image_subset (s : set α) (t : set s) : coe '' t ⊆ s :=
λ x ⟨y, yt, yvaleq⟩, by rw ←yvaleq; exact y.property

theorem coe_image_univ (s : set α) : (coe : s → α) '' set.univ = s :=
image_univ.trans range_coe

@[simp] theorem image_preimage_coe (s t : set α) :
  (coe : s → α) '' (coe ⁻¹' t) = t ∩ s :=
image_preimage_eq_inter_range.trans $ congr_arg _ range_coe

theorem image_preimage_val (s t : set α) :
  (subtype.val : s → α) '' (subtype.val ⁻¹' t) = t ∩ s :=
image_preimage_coe s t

theorem preimage_coe_eq_preimage_coe_iff {s t u : set α} :
  ((coe : s → α) ⁻¹' t = coe ⁻¹' u) ↔ t ∩ s = u ∩ s :=
begin
  rw [←image_preimage_coe, ←image_preimage_coe],
  split, { intro h, rw h },
  intro h, exact coe_injective.image_injective h
end

theorem preimage_val_eq_preimage_val_iff (s t u : set α) :
  ((subtype.val : s → α) ⁻¹' t = subtype.val ⁻¹' u) ↔ (t ∩ s = u ∩ s) :=
preimage_coe_eq_preimage_coe_iff

lemma exists_set_subtype {t : set α} (p : set α → Prop) :
  (∃(s : set t), p (coe '' s)) ↔ ∃(s : set α), s ⊆ t ∧ p s :=
begin
  split,
  { rintro ⟨s, hs⟩, refine ⟨coe '' s, _, hs⟩,
    convert image_subset_range _ _, rw [range_coe] },
  rintro ⟨s, hs₁, hs₂⟩, refine ⟨coe ⁻¹' s, _⟩,
  rw [image_preimage_eq_of_subset], exact hs₂, rw [range_coe], exact hs₁
end

lemma preimage_coe_nonempty {s t : set α} : ((coe : s → α) ⁻¹' t).nonempty ↔ (s ∩ t).nonempty :=
by rw [inter_comm, ← image_preimage_coe, nonempty_image_iff]

lemma preimage_coe_eq_empty {s t : set α} : (coe : s → α) ⁻¹' t = ∅ ↔ s ∩ t = ∅ :=
by simp only [← not_nonempty_iff_eq_empty, preimage_coe_nonempty]

@[simp] lemma preimage_coe_compl (s : set α) : (coe : s → α) ⁻¹' sᶜ = ∅ :=
preimage_coe_eq_empty.2 (inter_compl_self s)

@[simp] lemma preimage_coe_compl' (s : set α) : (coe : sᶜ → α) ⁻¹' s = ∅ :=
preimage_coe_eq_empty.2 (compl_inter_self s)

end subtype

namespace set

/-! ### Lemmas about cartesian product of sets -/

section prod

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables {s s₁ s₂ : set α} {t t₁ t₂ : set β}

/-- The cartesian product `prod s t` is the set of `(a, b)`
  such that `a ∈ s` and `b ∈ t`. -/
protected def prod (s : set α) (t : set β) : set (α × β) :=
{p | p.1 ∈ s ∧ p.2 ∈ t}

lemma prod_eq (s : set α) (t : set β) : s.prod t = prod.fst ⁻¹' s ∩ prod.snd ⁻¹' t := rfl

theorem mem_prod_eq {p : α × β} : p ∈ s.prod t = (p.1 ∈ s ∧ p.2 ∈ t) := rfl

@[simp] theorem mem_prod {p : α × β} : p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

@[simp] theorem prod_mk_mem_set_prod_eq {a : α} {b : β} :
  (a, b) ∈ s.prod t = (a ∈ s ∧ b ∈ t) := rfl

lemma mk_mem_prod {a : α} {b : β} (a_in : a ∈ s) (b_in : b ∈ t) : (a, b) ∈ s.prod t :=
⟨a_in, b_in⟩

theorem prod_mono {s₁ s₂ : set α} {t₁ t₂ : set β} (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) :
  s₁.prod t₁ ⊆ s₂.prod t₂ :=
assume x ⟨h₁, h₂⟩, ⟨hs h₁, ht h₂⟩

lemma prod_subset_iff {P : set (α × β)} :
  (s.prod t ⊆ P) ↔ ∀ (x ∈ s) (y ∈ t), (x, y) ∈ P :=
⟨λ h _ xin _ yin, h (mk_mem_prod xin yin), λ h ⟨_, _⟩ pin, h _ pin.1 _ pin.2⟩

lemma forall_prod_set {p : α × β → Prop} :
  (∀ x ∈ s.prod t, p x) ↔ ∀ (x ∈ s) (y ∈ t), p (x, y) :=
prod_subset_iff

lemma exists_prod_set {p : α × β → Prop} :
  (∃ x ∈ s.prod t, p x) ↔ ∃ (x ∈ s) (y ∈ t), p (x, y) :=
by simp [and_assoc]

@[simp] theorem prod_empty : s.prod ∅ = (∅ : set (α × β)) :=
by { ext, simp }

@[simp] theorem empty_prod : set.prod ∅ t = (∅ : set (α × β)) :=
by { ext, simp }

@[simp] theorem univ_prod_univ : (@univ α).prod (@univ β) = univ :=
by { ext ⟨x, y⟩, simp }

lemma univ_prod {t : set β} : set.prod (univ : set α) t = prod.snd ⁻¹' t :=
by simp [prod_eq]

lemma prod_univ {s : set α} : set.prod s (univ : set β) = prod.fst ⁻¹' s :=
by simp [prod_eq]

@[simp] theorem singleton_prod {a : α} : set.prod {a} t = prod.mk a '' t :=
by { ext ⟨x, y⟩, simp [and.left_comm, eq_comm] }

@[simp] theorem prod_singleton {b : β} : s.prod {b} = (λ a, (a, b)) '' s :=
by { ext ⟨x, y⟩, simp [and.left_comm, eq_comm] }

theorem singleton_prod_singleton {a : α} {b : β} : set.prod {a} {b} = ({(a, b)} : set (α × β)) :=
by simp

@[simp] theorem union_prod : (s₁ ∪ s₂).prod t = s₁.prod t ∪ s₂.prod t :=
by { ext ⟨x, y⟩, simp [or_and_distrib_right] }

@[simp] theorem prod_union : s.prod (t₁ ∪ t₂) = s.prod t₁ ∪ s.prod t₂ :=
by { ext ⟨x, y⟩, simp [and_or_distrib_left] }

theorem prod_inter_prod : s₁.prod t₁ ∩ s₂.prod t₂ = (s₁ ∩ s₂).prod (t₁ ∩ t₂) :=
by { ext ⟨x, y⟩, simp [and_assoc, and.left_comm] }

theorem insert_prod {a : α} : (insert a s).prod t = (prod.mk a '' t) ∪ s.prod t :=
by { ext ⟨x, y⟩, simp [image, iff_def, or_imp_distrib, imp.swap] {contextual := tt} }

theorem prod_insert {b : β} : s.prod (insert b t) = ((λa, (a, b)) '' s) ∪ s.prod t :=
by { ext ⟨x, y⟩, simp [image, iff_def, or_imp_distrib, imp.swap] {contextual := tt} }

theorem prod_preimage_eq {f : γ → α} {g : δ → β} :
  (f ⁻¹' s).prod (g ⁻¹' t) = (λ p, (f p.1, g p.2)) ⁻¹' s.prod t := rfl

lemma prod_preimage_left {f : γ → α} : (f ⁻¹' s).prod t = (λp, (f p.1, p.2)) ⁻¹' (s.prod t) := rfl

lemma prod_preimage_right {g : δ → β} : s.prod (g ⁻¹' t) = (λp, (p.1, g p.2)) ⁻¹' (s.prod t) := rfl

lemma mk_preimage_prod (f : γ → α) (g : γ → β) :
  (λ x, (f x, g x)) ⁻¹' s.prod t = f ⁻¹' s ∩ g ⁻¹' t := rfl

@[simp] lemma mk_preimage_prod_left {y : β} (h : y ∈ t) : (λ x, (x, y)) ⁻¹' s.prod t = s :=
by { ext x, simp [h] }

@[simp] lemma mk_preimage_prod_right {x : α} (h : x ∈ s) : prod.mk x ⁻¹' s.prod t = t :=
by { ext y, simp [h] }

@[simp] lemma mk_preimage_prod_left_eq_empty {y : β} (hy : y ∉ t) :
  (λ x, (x, y)) ⁻¹' s.prod t = ∅ :=
by { ext z, simp [hy] }

@[simp] lemma mk_preimage_prod_right_eq_empty {x : α} (hx : x ∉ s) :
  prod.mk x ⁻¹' s.prod t = ∅ :=
by { ext z, simp [hx] }

lemma mk_preimage_prod_left_eq_if {y : β} [decidable_pred (∈ t)] :
  (λ x, (x, y)) ⁻¹' s.prod t = if y ∈ t then s else ∅ :=
by { split_ifs; simp [h] }

lemma mk_preimage_prod_right_eq_if {x : α} [decidable_pred (∈ s)] :
  prod.mk x ⁻¹' s.prod t = if x ∈ s then t else ∅ :=
by { split_ifs; simp [h] }

lemma mk_preimage_prod_left_fn_eq_if {y : β} [decidable_pred (∈ t)] (f : γ → α) :
  (λ x, (f x, y)) ⁻¹' s.prod t = if y ∈ t then f ⁻¹' s else ∅ :=
by rw [← mk_preimage_prod_left_eq_if, prod_preimage_left, preimage_preimage]

lemma mk_preimage_prod_right_fn_eq_if {x : α} [decidable_pred (∈ s)] (g : δ → β) :
  (λ y, (x, g y)) ⁻¹' s.prod t = if x ∈ s then g ⁻¹' t else ∅ :=
by rw [← mk_preimage_prod_right_eq_if, prod_preimage_right, preimage_preimage]

theorem image_swap_eq_preimage_swap : image (@prod.swap α β) = preimage prod.swap :=
image_eq_preimage_of_inverse prod.swap_left_inverse prod.swap_right_inverse

theorem preimage_swap_prod {s : set α} {t : set β} : prod.swap ⁻¹' t.prod s = s.prod t :=
by { ext ⟨x, y⟩, simp [and_comm] }

theorem image_swap_prod : prod.swap '' t.prod s = s.prod t :=
by rw [image_swap_eq_preimage_swap, preimage_swap_prod]

theorem prod_image_image_eq {m₁ : α → γ} {m₂ : β → δ} :
  (image m₁ s).prod (image m₂ t) = image (λp:α×β, (m₁ p.1, m₂ p.2)) (s.prod t) :=
ext $ by simp [-exists_and_distrib_right, exists_and_distrib_right.symm, and.left_comm,
  and.assoc, and.comm]

theorem prod_range_range_eq {α β γ δ} {m₁ : α → γ} {m₂ : β → δ} :
  (range m₁).prod (range m₂) = range (λp:α×β, (m₁ p.1, m₂ p.2)) :=
ext $ by simp [range]

theorem prod_range_univ_eq {α β γ} {m₁ : α → γ} :
  (range m₁).prod (univ : set β) = range (λp:α×β, (m₁ p.1, p.2)) :=
ext $ by simp [range]

theorem prod_univ_range_eq {α β δ} {m₂ : β → δ} :
  (univ : set α).prod (range m₂) = range (λp:α×β, (p.1, m₂ p.2)) :=
ext $ by simp [range]

theorem nonempty.prod : s.nonempty → t.nonempty → (s.prod t).nonempty
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨(x, y), ⟨hx, hy⟩⟩

theorem nonempty.fst : (s.prod t).nonempty → s.nonempty
| ⟨p, hp⟩ := ⟨p.1, hp.1⟩

theorem nonempty.snd : (s.prod t).nonempty → t.nonempty
| ⟨p, hp⟩ := ⟨p.2, hp.2⟩

theorem prod_nonempty_iff : (s.prod t).nonempty ↔ s.nonempty ∧ t.nonempty :=
⟨λ h, ⟨h.fst, h.snd⟩, λ h, nonempty.prod h.1 h.2⟩

theorem prod_eq_empty_iff :
  s.prod t = ∅ ↔ (s = ∅ ∨ t = ∅) :=
by simp only [not_nonempty_iff_eq_empty.symm, prod_nonempty_iff, not_and_distrib]

lemma prod_sub_preimage_iff {W : set γ} {f : α × β → γ} :
  s.prod t ⊆ f ⁻¹' W ↔ ∀ a b, a ∈ s → b ∈ t → f (a, b) ∈ W :=
by simp [subset_def]

lemma fst_image_prod_subset (s : set α) (t : set β) :
  prod.fst '' (s.prod t) ⊆ s :=
λ _ h, let ⟨_, ⟨h₂, _⟩, h₁⟩ := (set.mem_image _ _ _).1 h in h₁ ▸ h₂

lemma prod_subset_preimage_fst (s : set α) (t : set β) :
  s.prod t ⊆ prod.fst ⁻¹' s :=
image_subset_iff.1 (fst_image_prod_subset s t)

lemma fst_image_prod (s : set β) {t : set α} (ht : t.nonempty) :
  prod.fst '' (s.prod t) = s :=
set.subset.antisymm (fst_image_prod_subset _ _)
  $ λ y y_in, let ⟨x, x_in⟩ := ht in
    ⟨(y, x), ⟨y_in, x_in⟩, rfl⟩

lemma snd_image_prod_subset (s : set α) (t : set β) :
  prod.snd '' (s.prod t) ⊆ t :=
λ _ h, let ⟨_, ⟨_, h₂⟩, h₁⟩ := (set.mem_image _ _ _).1 h in h₁ ▸ h₂

lemma prod_subset_preimage_snd (s : set α) (t : set β) :
  s.prod t ⊆ prod.snd ⁻¹' t :=
image_subset_iff.1 (snd_image_prod_subset s t)

lemma snd_image_prod {s : set α} (hs : s.nonempty) (t : set β) :
  prod.snd '' (s.prod t) = t :=
set.subset.antisymm (snd_image_prod_subset _ _)
  $ λ y y_in, let ⟨x, x_in⟩ := hs in
    ⟨(x, y), ⟨x_in, y_in⟩, rfl⟩

/-- A product set is included in a product set if and only factors are included, or a factor of the
first set is empty. -/
lemma prod_subset_prod_iff :
  (s.prod t ⊆ s₁.prod t₁) ↔ (s ⊆ s₁ ∧ t ⊆ t₁) ∨ (s = ∅) ∨ (t = ∅) :=
begin
  classical,
  cases (s.prod t).eq_empty_or_nonempty with h h,
  { simp [h, prod_eq_empty_iff.1 h] },
  { have st : s.nonempty ∧ t.nonempty, by rwa [prod_nonempty_iff] at h,
    split,
    { assume H : s.prod t ⊆ s₁.prod t₁,
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
variables {ι : Type*} {α : ι → Type*} {s s₁ : set ι} {t t₁ t₂ : Π i, set (α i)}

/-- Given an index set `i` and a family of sets `s : Π i, set (α i)`, `pi i s`
is the set of dependent functions `f : Πa, π a` such that `f a` belongs to `π a`
whenever `a ∈ i`. -/
def pi (s : set ι) (t : Π i, set (α i)) : set (Π i, α i) := { f | ∀i ∈ s, f i ∈ t i }

@[simp] lemma mem_pi {f : Π i, α i} : f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i :=
by refl

@[simp] lemma mem_univ_pi {f : Π i, α i} : f ∈ pi univ t ↔ ∀ i, f i ∈ t i :=
by simp

@[simp] lemma empty_pi (s : Π i, set (α i)) : pi ∅ s = univ := by { ext, simp [pi] }

@[simp] lemma pi_univ (s : set ι) : pi s (λ i, (univ : set (α i))) = univ :=
eq_univ_of_forall $ λ f i hi, mem_univ _

lemma pi_mono (h : ∀ i ∈ s, t₁ i ⊆ t₂ i) : pi s t₁ ⊆ pi s t₂ :=
λ x hx i hi, (h i hi $ hx i hi)

lemma pi_inter_distrib : s.pi (λ i, t i ∩ t₁ i) = s.pi t ∩ s.pi t₁ :=
ext $ λ x, by simp only [forall_and_distrib, mem_pi, mem_inter_eq]

lemma pi_congr (h : s = s₁) (h' : ∀ i ∈ s, t i = t₁ i) : pi s t = pi s₁ t₁ :=
h ▸ (ext $ λ x, forall_congr $ λ i, forall_congr $ λ hi, h' i hi ▸ iff.rfl)

lemma pi_eq_empty {i : ι} (hs : i ∈ s) (ht : t i = ∅) : s.pi t = ∅ :=
by { ext f, simp only [mem_empty_eq, not_forall, iff_false, mem_pi, not_imp],
     exact ⟨i, hs, by simp [ht]⟩ }

lemma univ_pi_eq_empty {i : ι} (ht : t i = ∅) : pi univ t = ∅ :=
pi_eq_empty (mem_univ i) ht

lemma pi_nonempty_iff : (s.pi t).nonempty ↔ ∀ i, ∃ x, i ∈ s → x ∈ t i :=
by simp [classical.skolem, set.nonempty]

lemma univ_pi_nonempty_iff : (pi univ t).nonempty ↔ ∀ i, (t i).nonempty :=
by simp [classical.skolem, set.nonempty]

lemma pi_eq_empty_iff : s.pi t = ∅ ↔ ∃ i, (α i → false) ∨ (i ∈ s ∧ t i = ∅) :=
begin
  rw [← not_nonempty_iff_eq_empty, pi_nonempty_iff], push_neg, apply exists_congr, intro i,
  split,
  { intro h, by_cases hα : nonempty (α i),
    { cases hα with x, refine or.inr ⟨(h x).1, by simp [eq_empty_iff_forall_not_mem, h]⟩ },
    { exact or.inl (λ x, hα ⟨x⟩) }},
  { rintro (h|h) x, exfalso, exact h x, simp [h] }
end

lemma univ_pi_eq_empty_iff : pi univ t = ∅ ↔ ∃ i, t i = ∅ :=
by simp [← not_nonempty_iff_eq_empty, univ_pi_nonempty_iff]

@[simp] lemma insert_pi (i : ι) (s : set ι) (t : Π i, set (α i)) :
  pi (insert i s) t = (eval i ⁻¹' t i) ∩ pi s t :=
by { ext, simp [pi, or_imp_distrib, forall_and_distrib] }

@[simp] lemma singleton_pi (i : ι) (t : Π i, set (α i)) :
  pi {i} t = (eval i ⁻¹' t i) :=
by { ext, simp [pi] }

lemma singleton_pi' (i : ι) (t : Π i, set (α i)) : pi {i} t = {x | x i ∈ t i} :=
singleton_pi i t

lemma pi_if {p : ι → Prop} [h : decidable_pred p] (s : set ι) (t₁ t₂ : Π i, set (α i)) :
  pi s (λ i, if p i then t₁ i else t₂ i) = pi {i ∈ s | p i} t₁ ∩ pi {i ∈ s | ¬ p i} t₂ :=
begin
  ext f,
  split,
  { assume h, split; { rintros i ⟨his, hpi⟩, simpa [*] using h i } },
  { rintros ⟨ht₁, ht₂⟩ i his,
    by_cases p i; simp * at * }
end

lemma union_pi : (s ∪ s₁).pi t = s.pi t ∩ s₁.pi t :=
by simp [pi, or_imp_distrib, forall_and_distrib, set_of_and]

@[simp] lemma pi_inter_compl (s : set ι) : pi s t ∩ pi sᶜ t = pi univ t :=
by rw [← union_pi, union_compl_self]

lemma pi_update_of_not_mem [decidable_eq ι] {β : Π i, Type*} {i : ι} (hi : i ∉ s) (f : Π j, α j)
  (a : α i) (t : Π j, α j → set (β j)) :
  s.pi (λ j, t j (update f i a j)) = s.pi (λ j, t j (f j)) :=
pi_congr rfl $ λ j hj, by { rw update_noteq, exact λ h, hi (h ▸ hj) }

lemma pi_update_of_mem [decidable_eq ι] {β : Π i, Type*} {i : ι} (hi : i ∈ s) (f : Π j, α j)
  (a : α i) (t : Π j, α j → set (β j)) :
  s.pi (λ j, t j (update f i a j)) = {x | x i ∈ t i a} ∩ (s \ {i}).pi (λ j, t j (f j)) :=
calc s.pi (λ j, t j (update f i a j)) = ({i} ∪ s \ {i}).pi (λ j, t j (update f i a j)) :
  by rw [union_diff_self, union_eq_self_of_subset_left (singleton_subset_iff.2 hi)]
... = {x | x i ∈ t i a} ∩ (s \ {i}).pi (λ j, t j (f j)) :
  by { rw [union_pi, singleton_pi', update_same, pi_update_of_not_mem], simp }

lemma univ_pi_update [decidable_eq ι] {β : Π i, Type*} (i : ι) (f : Π j, α j)
  (a : α i) (t : Π j, α j → set (β j)) :
  pi univ (λ j, t j (update f i a j)) = {x | x i ∈ t i a} ∩ pi {i}ᶜ (λ j, t j (f j)) :=
by rw [compl_eq_univ_diff, ← pi_update_of_mem (mem_univ _)]

lemma univ_pi_update_univ [decidable_eq ι] (i : ι) (s : set (α i)) :
  pi univ (update (λ j : ι, (univ : set (α j))) i s) = eval i ⁻¹' s :=
by rw [univ_pi_update i (λ j, (univ : set (α j))) s (λ j t, t), pi_univ, inter_univ, preimage]

open_locale classical

lemma eval_image_pi {i : ι} (hs : i ∈ s) (ht : (s.pi t).nonempty) : eval i '' s.pi t = t i :=
begin
  ext x, rcases ht with ⟨f, hf⟩, split,
  { rintro ⟨g, hg, rfl⟩, exact hg i hs },
  { intro hg, refine ⟨update f i x, _, by simp⟩,
    intros j hj, by_cases hji : j = i,
    { subst hji, simp [hg] },
    { rw [mem_pi] at hf, simp [hji, hf, hj] }},
end

@[simp] lemma eval_image_univ_pi {i : ι} (ht : (pi univ t).nonempty) :
  (λ f : Π i, α i, f i) '' pi univ t = t i :=
eval_image_pi (mem_univ i) ht

lemma update_preimage_pi {i : ι} {f : Π i, α i} (hi : i ∈ s)
  (hf : ∀ j ∈ s, j ≠ i → f j ∈ t j) : (update f i) ⁻¹' s.pi t = t i :=
begin
  ext x, split,
  { intro h, convert h i hi, simp },
  { intros hx j hj, by_cases h : j = i,
    { cases h, simpa },
    { rw [update_noteq h], exact hf j hj h }}
end

lemma update_preimage_univ_pi {i : ι} {f : Π i, α i} (hf : ∀ j ≠ i, f j ∈ t j) :
  (update f i) ⁻¹' pi univ t = t i :=
update_preimage_pi (mem_univ i) (λ j _, hf j)

lemma subset_pi_eval_image (s : set ι) (u : set (Π i, α i)) : u ⊆ pi s (λ i, eval i '' u) :=
λ f hf i hi, ⟨f, hf, rfl⟩

end pi

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

section inclusion
variable {α : Type*}

/-- `inclusion` is the "identity" function between two subsets `s` and `t`, where `s ⊆ t` -/
def inclusion {s t : set α} (h : s ⊆ t) : s → t :=
λ x : s, (⟨x, h x.2⟩ : t)

@[simp] lemma inclusion_self {s : set α} (x : s) :
  inclusion (set.subset.refl _) x = x :=
by { cases x, refl }

@[simp] lemma inclusion_right {s t : set α} (h : s ⊆ t) (x : t) (m : (x : α) ∈ s) :
  inclusion h ⟨x, m⟩ = x :=
by { cases x, refl }

@[simp] lemma inclusion_inclusion {s t u : set α} (hst : s ⊆ t) (htu : t ⊆ u)
  (x : s) : inclusion htu (inclusion hst x) = inclusion (set.subset.trans hst htu) x :=
by { cases x, refl }

@[simp] lemma coe_inclusion {s t : set α} (h : s ⊆ t) (x : s) :
  (inclusion h x : α) = (x : α) := rfl

lemma inclusion_injective {s t : set α} (h : s ⊆ t) :
  function.injective (inclusion h)
| ⟨_, _⟩ ⟨_, _⟩ := subtype.ext_iff_val.2 ∘ subtype.ext_iff_val.1

lemma eq_of_inclusion_surjective {s t : set α} {h : s ⊆ t}
  (h_surj : function.surjective (inclusion h)) : s = t :=
begin
  apply set.subset.antisymm h,
  intros x hx,
  cases h_surj ⟨x, hx⟩ with y key,
  rw [←subtype.coe_mk x hx, ←key, coe_inclusion],
  exact subtype.mem y,
end

lemma range_inclusion {s t : set α} (h : s ⊆ t) : range (inclusion h) = {x : t | (x:α) ∈ s} :=
by { ext ⟨x, hx⟩, simp [inclusion] }

end inclusion

/-! ### Injectivity and surjectivity lemmas for image and preimage -/
section image_preimage
variables {α : Type u} {β : Type v} {f : α → β}
@[simp]
lemma preimage_injective : injective (preimage f) ↔ surjective f :=
begin
  refine ⟨λ h y, _, surjective.preimage_injective⟩,
  obtain ⟨x, hx⟩ : (f ⁻¹' {y}).nonempty,
  { rw [h.nonempty_apply_iff preimage_empty], apply singleton_nonempty },
  exact ⟨x, hx⟩
end

@[simp]
lemma preimage_surjective : surjective (preimage f) ↔ injective f :=
begin
  refine ⟨λ h x x' hx, _, injective.preimage_surjective⟩,
  cases h {x} with s hs, have := mem_singleton x,
  rwa [← hs, mem_preimage, hx, ← mem_preimage, hs, mem_singleton_iff, eq_comm] at this
end

@[simp] lemma image_surjective : surjective (image f) ↔ surjective f :=
begin
  refine ⟨λ h y, _, surjective.image_surjective⟩,
  cases h {y} with s hs,
  have := mem_singleton y, rw [← hs] at this, rcases this with ⟨x, h1x, h2x⟩,
  exact ⟨x, h2x⟩
end

@[simp] lemma image_injective : injective (image f) ↔ injective f :=
begin
  refine ⟨λ h x x' hx, _, injective.image_injective⟩,
  rw [← singleton_eq_singleton_iff], apply h,
  rw [image_singleton, image_singleton, hx]
end
end image_preimage

/-! ### Lemmas about images of binary and ternary functions -/

section n_ary_image

variables {α β γ δ ε : Type*} {f f' : α → β → γ} {g g' : α → β → γ → δ}
variables {s s' : set α} {t t' : set β} {u u' : set γ} {a a' : α} {b b' : β} {c c' : γ} {d d' : δ}


/-- The image of a binary function `f : α → β → γ` as a function `set α → set β → set γ`.
  Mathematically this should be thought of as the image of the corresponding function `α × β → γ`.
-/
def image2 (f : α → β → γ) (s : set α) (t : set β) : set γ :=
{c | ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c }

lemma mem_image2_eq : c ∈ image2 f s t = ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c := rfl

@[simp] lemma mem_image2 : c ∈ image2 f s t ↔ ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c := iff.rfl

lemma mem_image2_of_mem (h1 : a ∈ s) (h2 : b ∈ t) : f a b ∈ image2 f s t :=
⟨a, b, h1, h2, rfl⟩

lemma mem_image2_iff (hf : injective2 f) : f a b ∈ image2 f s t ↔ a ∈ s ∧ b ∈ t :=
⟨ by { rintro ⟨a', b', ha', hb', h⟩, rcases hf h with ⟨rfl, rfl⟩, exact ⟨ha', hb'⟩ },
  λ ⟨ha, hb⟩, mem_image2_of_mem ha hb⟩

/-- image2 is monotone with respect to `⊆`. -/
lemma image2_subset (hs : s ⊆ s') (ht : t ⊆ t') : image2 f s t ⊆ image2 f s' t' :=
by { rintro _ ⟨a, b, ha, hb, rfl⟩, exact mem_image2_of_mem (hs ha) (ht hb) }

lemma forall_image2_iff {p : γ → Prop} :
  (∀ z ∈ image2 f s t, p z) ↔ ∀ (x ∈ s) (y ∈ t), p (f x y) :=
⟨λ h x hx y hy, h _ ⟨x, y, hx, hy, rfl⟩, λ h z ⟨x, y, hx, hy, hz⟩, hz ▸ h x hx y hy⟩

@[simp] lemma image2_subset_iff {u : set γ} :
  image2 f s t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), f x y ∈ u :=
forall_image2_iff

lemma image2_union_left : image2 f (s ∪ s') t = image2 f s t ∪ image2 f s' t :=
begin
  ext c, split,
  { rintros ⟨a, b, h1a|h2a, hb, rfl⟩;[left, right]; exact ⟨_, _, ‹_›, ‹_›, rfl⟩ },
  { rintro (⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩); refine ⟨_, _, _, ‹_›, rfl⟩; simp [mem_union, *] }
end

lemma image2_union_right : image2 f s (t ∪ t') = image2 f s t ∪ image2 f s t' :=
begin
  ext c, split,
  { rintros ⟨a, b, ha, h1b|h2b, rfl⟩;[left, right]; exact ⟨_, _, ‹_›, ‹_›, rfl⟩ },
  { rintro (⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩); refine ⟨_, _, ‹_›, _, rfl⟩; simp [mem_union, *] }
end

@[simp] lemma image2_empty_left : image2 f ∅ t = ∅ := ext $ by simp
@[simp] lemma image2_empty_right : image2 f s ∅ = ∅ := ext $ by simp

lemma image2_inter_subset_left : image2 f (s ∩ s') t ⊆ image2 f s t ∩ image2 f s' t :=
by { rintro _ ⟨a, b, ⟨h1a, h2a⟩, hb, rfl⟩, split; exact ⟨_, _, ‹_›, ‹_›, rfl⟩ }

lemma image2_inter_subset_right : image2 f s (t ∩ t') ⊆ image2 f s t ∩ image2 f s t' :=
by { rintro _ ⟨a, b, ha, ⟨h1b, h2b⟩, rfl⟩, split; exact ⟨_, _, ‹_›, ‹_›, rfl⟩ }

@[simp] lemma image2_singleton_left : image2 f {a} t = f a '' t :=
ext $ λ x, by simp

@[simp] lemma image2_singleton_right : image2 f s {b} = (λ a, f a b) '' s :=
ext $ λ x, by simp

lemma image2_singleton : image2 f {a} {b} = {f a b} := by simp

@[congr] lemma image2_congr (h : ∀ (a ∈ s) (b ∈ t), f a b = f' a b) :
  image2 f s t = image2 f' s t :=
by { ext, split; rintro ⟨a, b, ha, hb, rfl⟩; refine ⟨a, b, ha, hb, by rw h a ha b hb⟩ }

/-- A common special case of `image2_congr` -/
lemma image2_congr' (h : ∀ a b, f a b = f' a b) : image2 f s t = image2 f' s t :=
image2_congr (λ a _ b _, h a b)

/-- The image of a ternary function `f : α → β → γ → δ` as a function
  `set α → set β → set γ → set δ`. Mathematically this should be thought of as the image of the
  corresponding function `α × β × γ → δ`.
-/
def image3 (g : α → β → γ → δ) (s : set α) (t : set β) (u : set γ) : set δ :=
{d | ∃ a b c, a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d }

@[simp] lemma mem_image3 : d ∈ image3 g s t u ↔ ∃ a b c, a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d :=
iff.rfl

@[congr] lemma image3_congr (h : ∀ (a ∈ s) (b ∈ t) (c ∈ u), g a b c = g' a b c) :
  image3 g s t u = image3 g' s t u :=
by { ext x,
     split; rintro ⟨a, b, c, ha, hb, hc, rfl⟩; refine ⟨a, b, c, ha, hb, hc, by rw h a ha b hb c hc⟩ }

/-- A common special case of `image3_congr` -/
lemma image3_congr' (h : ∀ a b c, g a b c = g' a b c) : image3 g s t u = image3 g' s t u :=
image3_congr (λ a _ b _ c _, h a b c)

lemma image2_image2_left (f : δ → γ → ε) (g : α → β → δ) :
  image2 f (image2 g s t) u = image3 (λ a b c, f (g a b) c) s t u :=
begin
  ext, split,
  { rintro ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩, refine ⟨a, b, c, ha, hb, hc, rfl⟩ },
  { rintro ⟨a, b, c, ha, hb, hc, rfl⟩, refine ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩ }
end

lemma image2_image2_right (f : α → δ → ε) (g : β → γ → δ) :
  image2 f s (image2 g t u) = image3 (λ a b c, f a (g b c)) s t u :=
begin
  ext, split,
  { rintro ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩, refine ⟨a, b, c, ha, hb, hc, rfl⟩ },
  { rintro ⟨a, b, c, ha, hb, hc, rfl⟩, refine ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩ }
end

lemma image2_assoc {ε'} {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
  (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
  image2 f (image2 g s t) u = image2 f' s (image2 g' t u) :=
by simp only [image2_image2_left, image2_image2_right, h_assoc]

lemma image_image2 (f : α → β → γ) (g : γ → δ) :
  g '' image2 f s t = image2 (λ a b, g (f a b)) s t :=
begin
  ext, split,
  { rintro ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩, refine ⟨a, b, ha, hb, rfl⟩ },
  { rintro ⟨a, b, ha, hb, rfl⟩, refine ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩ }
end

lemma image2_image_left (f : γ → β → δ) (g : α → γ) :
  image2 f (g '' s) t = image2 (λ a b, f (g a) b) s t :=
begin
  ext, split,
  { rintro ⟨_, b, ⟨a, ha, rfl⟩, hb, rfl⟩, refine ⟨a, b, ha, hb, rfl⟩ },
  { rintro ⟨a, b, ha, hb, rfl⟩, refine ⟨_, b, ⟨a, ha, rfl⟩, hb, rfl⟩ }
end

lemma image2_image_right (f : α → γ → δ) (g : β → γ) :
  image2 f s (g '' t) = image2 (λ a b, f a (g b)) s t :=
begin
  ext, split,
  { rintro ⟨a, _, ha, ⟨b, hb, rfl⟩, rfl⟩, refine ⟨a, b, ha, hb, rfl⟩ },
  { rintro ⟨a, b, ha, hb, rfl⟩, refine ⟨a, _, ha, ⟨b, hb, rfl⟩, rfl⟩ }
end

lemma image2_swap (f : α → β → γ) (s : set α) (t : set β) :
  image2 f s t = image2 (λ a b, f b a) t s :=
by { ext, split; rintro ⟨a, b, ha, hb, rfl⟩; refine ⟨b, a, hb, ha, rfl⟩ }

@[simp] lemma image2_left (h : t.nonempty) : image2 (λ x y, x) s t = s :=
by simp [nonempty_def.mp h, ext_iff]

@[simp] lemma image2_right (h : s.nonempty) : image2 (λ x y, y) s t = t :=
by simp [nonempty_def.mp h, ext_iff]

@[simp] lemma image_prod (f : α → β → γ) : (λ x : α × β, f x.1 x.2) '' s.prod t = image2 f s t :=
set.ext $ λ a,
⟨ by { rintros ⟨_, _, rfl⟩, exact ⟨_, _, (mem_prod.mp ‹_›).1, (mem_prod.mp ‹_›).2, rfl⟩ },
  by { rintros ⟨_, _, _, _, rfl⟩, exact ⟨(_, _), mem_prod.mpr ⟨‹_›, ‹_›⟩, rfl⟩ }⟩

lemma nonempty.image2 (hs : s.nonempty) (ht : t.nonempty) : (image2 f s t).nonempty :=
by { cases hs with a ha, cases ht with b hb, exact ⟨f a b, ⟨a, b, ha, hb, rfl⟩⟩ }

end n_ary_image

end set

namespace subsingleton

variables {α : Type*} [subsingleton α]

lemma eq_univ_of_nonempty {s : set α} : s.nonempty → s = univ :=
λ ⟨x, hx⟩, eq_univ_of_forall $ λ y, subsingleton.elim x y ▸ hx

@[elab_as_eliminator]
lemma set_cases {p : set α → Prop} (h0 : p ∅) (h1 : p univ) (s) : p s :=
s.eq_empty_or_nonempty.elim (λ h, h.symm ▸ h0) $ λ h, (eq_univ_of_nonempty h).symm ▸ h1

end subsingleton
