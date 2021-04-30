/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import data.multiset.finset_ops
import tactic.monotonicity
import tactic.apply
import tactic.nth_rewrite

/-!
# Finite sets

Terms of type `finset α` are one way of talking about finite subsets of `α` in mathlib.
Below, `finset α` is defined as a structure with 2 fields:

  1. `val` is a `multiset α` of elements;
  2. `nodup` is a proof that `val` has no duplicates.

Finsets in Lean are constructive in that they have an underlying `list` that enumerates their
elements. In particular, any function that uses the data of the underlying list cannot depend on its
ordering. This is handled on the `multiset` level by multiset API, so in most cases one needn't
worry about it explicitly.

Finsets give a basic foundation for defining finite sums and products over types:

  1. `∑ i in (s : finset α), f i`;
  2. `∏ i in (s : finset α), f i`.

Lean refers to these operations as `big_operator`s.
More information can be found in `algebra.big_operators.basic`.

Finsets are directly used to define fintypes in Lean.
A `fintype α` instance for a type `α` consists of
a universal `finset α` containing every term of `α`, called `univ`. See `data.fintype.basic`.
There is also `univ'`, the noncomputable partner to `univ`,
which is defined to be `α` as a finset if `α` is finite,
and the empty finset otherwise. See `data.fintype.basic`.

## Main declarations

### Main definitions

* `finset`: Defines a type for the finite subsets of `α`.
  Constructing a `finset` requires two pieces of data: `val`, a `multiset α` of elements,
  and `nodup`, a proof that `val` has no duplicates.
* `finset.has_mem`: Defines membership `a ∈ (s : finset α)`.
* `finset.has_coe`: Provides a coercion `s : finset α` to `s : set α`.
* `finset.induction_on`: Induction on finsets. To prove a proposition about an arbitrary `finset α`,
  it suffices to prove it for the empty finset, and to show that if it holds for some `finset α`,
  then it holds for the finset obtained by inserting a new element.
* `finset.choose`: Given a proof `h` of existence and uniqueness of a certain element
  satisfying a predicate, `choose s h` returns the element of `s` satisfying that predicate.
* `finset.card`: `card s : ℕ` returns the cardinalilty of `s : finset α`.
  The API for `card`'s interaction with operations on finsets is extensive.
  TODO: The noncomputable sister `fincard` is about to be added into mathlib.

### Finset constructions

* `singleton`: Denoted by `{a}`; the finset consisting of one element.
* `finset.empty`: Denoted by `∅`. The finset associated to any type consisting of no elements.
* `finset.range`: For any `n : ℕ`, `range n` is equal to `{0, 1, ... , n - 1} ⊆ ℕ`.
  This convention is consistent with other languages and normalizes `card (range n) = n`.
  Beware, `n` is not in `range n`.
* `finset.diag`: Given `s`, `diag s` is the set of pairs `(a, a)` with `a ∈ s`. See also
  `finset.off_diag`: Given a finite set `s`, the off-diagonal,
  `s.off_diag` is the set of pairs `(a, b)` with `a ≠ b` for `a, b ∈ s`.
* `finset.attach`: Given `s : finset α`, `attach s` forms a finset of elements of the subtype
  `{a // a ∈ s}`; in other words, it attaches elements to a proof of membership in the set.

### Finsets from functions

* `finset.image`: Given a function `f : α → β`, `s.image f` is the image finset in `β`.
* `finset.map`: Given an embedding `f : α ↪ β`, `s.map f` is the image finset in `β`.
* `finset.filter`: Given a predicate `p : α → Prop`, `s.filter p` is
  the finset consisting of those elements in `s` satisfying the predicate `p`.

### The lattice structure on subsets of finsets

There is a natural lattice structure on the subsets of a set.
In Lean, we use lattice notation to talk about things involving unions and intersections. See
`order.lattice`. For the lattice structure on finsets, `⊥` is called `bot` with `⊥ = ∅` and `⊤` is
called `top` with `⊤ = univ`.

* `finset.subset`: Lots of API about lattices, otherwise behaves exactly as one would expect.
* `finset.union`: Defines `s ∪ t` (or `s ⊔ t`) as the union of `s` and `t`.
  See `finset.bUnion` for finite unions.
* `finset.inter`: Defines `s ∩ t` (or `s ⊓ t`) as the intersection of `s` and `t`.
  TODO: `finset.bInter` for finite intersections.
* `finset.disj_union`: Given a hypothesis `h` which states that finsets `s` and `t` are disjoint,
  `s.disj_union t h` is the set such that `a ∈ disj_union s t h` iff `a ∈ s` or `a ∈ t`; this does
  not require decidable equality on the type `α`.

### Operations on two or more finsets

* `finset.insert` and `finset.cons`: For any `a : α`, `insert s a` returns `s ∪ {a}`. `cons s a h`
  returns the same except that it requires a hypothesis stating that `a` is not already in `s`.
  This does not require decidable equality on the type `α`.
* `finset.union`: see "The lattice structure on subsets of finsets"
* `finset.inter`: see "The lattice structure on subsets of finsets"
* `finset.erase`: For any `a : α`, `erase s a` returns `s` with the element `a` removed.
* `finset.sdiff`: Defines the set difference `s \ t` for finsets `s` and `t`.
* `finset.prod`: Given finsets of `α` and `β`, defines finsets of `α × β`.
  For arbitrary dependent products, see `data.finset.pi`.
* `finset.sigma`: Given finsets of `α` and `β`, defines finsets of the dependent sum type `Σ α, β`
* `finset.bUnion`: Finite unions of finsets; given an indexing function `f : α → finset β` and a
  `s : finset α`, `s.bUnion f` is the union of all finsets of the form `f a` for `a ∈ s`.
* `finset.bInter`: TODO: Implemement finite intersections.

### Maps constructed using finsets

* `finset.piecewise`: Given two functions `f`, `g`, `s.piecewise f g` is a function which is equal
  to `f` on `s` and `g` on the complement.

### Predicates on finsets

* `disjoint`: defined via the lattice structure on finsets; two sets are disjoint if their
  intersection is empty.
* `finset.nonempty`: A finset is nonempty if it has elements.
  This is equivalent to saying `s ≠ ∅`. TODO: Decide on the simp normal form.

### Equivalences between finsets

* The `data.equiv` files describe a general type of equivalence, so look in there for any lemmas.
  There is some API for rewriting sums and products from `s` to `t` given that `s ≃ t`.
  TODO: examples

## Tags

finite sets, finset

-/

open multiset subtype nat function

variables {α : Type*} {β : Type*} {γ : Type*}

/-- `finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
structure finset (α : Type*) :=
(val : multiset α)
(nodup : nodup val)

namespace finset

theorem eq_of_veq : ∀ {s t : finset α}, s.1 = t.1 → s = t
| ⟨s, _⟩ ⟨t, _⟩ rfl := rfl

@[simp] theorem val_inj {s t : finset α} : s.1 = t.1 ↔ s = t :=
⟨eq_of_veq, congr_arg _⟩

@[simp] theorem erase_dup_eq_self [decidable_eq α] (s : finset α) : erase_dup s.1 = s.1 :=
erase_dup_eq_self.2 s.2

instance has_decidable_eq [decidable_eq α] : decidable_eq (finset α)
| s₁ s₂ := decidable_of_iff _ val_inj

/-! ### membership -/

instance : has_mem α (finset α) := ⟨λ a s, a ∈ s.1⟩

theorem mem_def {a : α} {s : finset α} : a ∈ s ↔ a ∈ s.1 := iff.rfl

@[simp] theorem mem_mk {a : α} {s nd} : a ∈ @finset.mk α s nd ↔ a ∈ s := iff.rfl

instance decidable_mem [h : decidable_eq α] (a : α) (s : finset α) : decidable (a ∈ s) :=
multiset.decidable_mem _ _

/-! ### set coercion -/

/-- Convert a finset to a set in the natural way. -/
instance : has_coe_t (finset α) (set α) := ⟨λ s, {x | x ∈ s}⟩

@[simp, norm_cast] lemma mem_coe {a : α} {s : finset α} : a ∈ (s : set α) ↔ a ∈ s := iff.rfl

@[simp] lemma set_of_mem {α} {s : finset α} : {a | a ∈ s} = s := rfl

@[simp] lemma coe_mem {s : finset α} (x : (s : set α)) : ↑x ∈ s := x.2

@[simp] lemma mk_coe {s : finset α} (x : (s : set α)) {h} :
  (⟨x, h⟩ : (s : set α)) = x :=
subtype.coe_eta _ _

instance decidable_mem' [decidable_eq α] (a : α) (s : finset α) :
  decidable (a ∈ (s : set α)) := s.decidable_mem _

/-! ### extensionality -/
theorem ext_iff {s₁ s₂ : finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
val_inj.symm.trans $ nodup_ext s₁.2 s₂.2

@[ext]
theorem ext {s₁ s₂ : finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
ext_iff.2

@[simp, norm_cast] theorem coe_inj {s₁ s₂ : finset α} : (s₁ : set α) = s₂ ↔ s₁ = s₂ :=
set.ext_iff.trans ext_iff.symm

lemma coe_injective {α} : injective (coe : finset α → set α) :=
λ s t, coe_inj.1

/-! ### subset -/

instance : has_subset (finset α) := ⟨λ s₁ s₂, ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂⟩

theorem subset_def {s₁ s₂ : finset α} : s₁ ⊆ s₂ ↔ s₁.1 ⊆ s₂.1 := iff.rfl

@[simp] theorem subset.refl (s : finset α) : s ⊆ s := subset.refl _

theorem subset_of_eq {s t : finset α} (h : s = t) : s ⊆ t := h ▸ subset.refl _

theorem subset.trans {s₁ s₂ s₃ : finset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ := subset.trans

theorem superset.trans {s₁ s₂ s₃ : finset α} : s₁ ⊇ s₂ → s₂ ⊇ s₃ → s₁ ⊇ s₃ :=
λ h' h, subset.trans h h'

-- TODO: these should be global attributes, but this will require fixing other files
local attribute [trans] subset.trans superset.trans

theorem mem_of_subset {s₁ s₂ : finset α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ := mem_of_subset

theorem subset.antisymm {s₁ s₂ : finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
ext $ λ a, ⟨@H₁ a, @H₂ a⟩

theorem subset_iff {s₁ s₂ : finset α} : s₁ ⊆ s₂ ↔ ∀ ⦃x⦄, x ∈ s₁ → x ∈ s₂ := iff.rfl

@[simp, norm_cast] theorem coe_subset {s₁ s₂ : finset α} :
  (s₁ : set α) ⊆ s₂ ↔ s₁ ⊆ s₂ := iff.rfl

@[simp] theorem val_le_iff {s₁ s₂ : finset α} : s₁.1 ≤ s₂.1 ↔ s₁ ⊆ s₂ := le_iff_subset s₁.2

instance : has_ssubset (finset α) := ⟨λa b, a ⊆ b ∧ ¬ b ⊆ a⟩

instance : partial_order (finset α) :=
{ le := (⊆),
  lt := (⊂),
  le_refl := subset.refl,
  le_trans := @subset.trans _,
  le_antisymm := @subset.antisymm _ }

theorem subset.antisymm_iff {s₁ s₂ : finset α} : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ :=
le_antisymm_iff

@[simp] theorem le_eq_subset : ((≤) : finset α → finset α → Prop) = (⊆) := rfl
@[simp] theorem lt_eq_subset : ((<) : finset α → finset α → Prop) = (⊂) := rfl

theorem le_iff_subset {s₁ s₂ : finset α} : s₁ ≤ s₂ ↔ s₁ ⊆ s₂ := iff.rfl
theorem lt_iff_ssubset {s₁ s₂ : finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂ := iff.rfl

@[simp, norm_cast] lemma coe_ssubset {s₁ s₂ : finset α} : (s₁ : set α) ⊂ s₂ ↔ s₁ ⊂ s₂ :=
show (s₁ : set α) ⊂ s₂ ↔ s₁ ⊆ s₂ ∧ ¬s₂ ⊆ s₁,
  by simp only [set.ssubset_def, finset.coe_subset]

@[simp] theorem val_lt_iff {s₁ s₂ : finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂ :=
and_congr val_le_iff $ not_congr val_le_iff

theorem ssubset_iff_of_subset {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : s₁ ⊂ s₂ ↔ ∃ x ∈ s₂, x ∉ s₁ :=
set.ssubset_iff_of_subset h

/-! ### Nonempty -/

/-- The property `s.nonempty` expresses the fact that the finset `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def nonempty (s : finset α) : Prop := ∃ x:α, x ∈ s

@[simp, norm_cast] lemma coe_nonempty {s : finset α} : (s:set α).nonempty ↔ s.nonempty := iff.rfl

lemma nonempty.bex {s : finset α} (h : s.nonempty) : ∃ x:α, x ∈ s := h

lemma nonempty.mono {s t : finset α} (hst : s ⊆ t) (hs : s.nonempty) : t.nonempty :=
set.nonempty.mono hst hs

lemma nonempty.forall_const {s : finset α} (h : s.nonempty) {p : Prop} : (∀ x ∈ s, p) ↔ p :=
let ⟨x, hx⟩ := h in ⟨λ h, h x hx, λ h x hx, h⟩

/-! ### empty -/

/-- The empty finset -/
protected def empty : finset α := ⟨0, nodup_zero⟩

instance : has_emptyc (finset α) := ⟨finset.empty⟩

instance inhabited_finset : inhabited (finset α) := ⟨∅⟩

@[simp] theorem empty_val : (∅ : finset α).1 = 0 := rfl

@[simp] theorem not_mem_empty (a : α) : a ∉ (∅ : finset α) := id

@[simp] theorem not_nonempty_empty : ¬(∅ : finset α).nonempty :=
λ ⟨x, hx⟩, not_mem_empty x hx

@[simp] theorem mk_zero : (⟨0, nodup_zero⟩ : finset α) = ∅ := rfl

theorem ne_empty_of_mem {a : α} {s : finset α} (h : a ∈ s) : s ≠ ∅ :=
λ e, not_mem_empty a $ e ▸ h

theorem nonempty.ne_empty {s : finset α} (h : s.nonempty) : s ≠ ∅ :=
exists.elim h $ λ a, ne_empty_of_mem

@[simp] theorem empty_subset (s : finset α) : ∅ ⊆ s := zero_subset _

theorem eq_empty_of_forall_not_mem {s : finset α} (H : ∀x, x ∉ s) : s = ∅ :=
eq_of_veq (eq_zero_of_forall_not_mem H)

lemma eq_empty_iff_forall_not_mem {s : finset α} : s = ∅ ↔ ∀ x, x ∉ s :=
⟨by rintro rfl x; exact id, λ h, eq_empty_of_forall_not_mem h⟩

@[simp] theorem val_eq_zero {s : finset α} : s.1 = 0 ↔ s = ∅ := @val_inj _ s ∅

theorem subset_empty {s : finset α} : s ⊆ ∅ ↔ s = ∅ := subset_zero.trans val_eq_zero

theorem nonempty_of_ne_empty {s : finset α} (h : s ≠ ∅) : s.nonempty :=
exists_mem_of_ne_zero (mt val_eq_zero.1 h)

theorem nonempty_iff_ne_empty {s : finset α} : s.nonempty ↔ s ≠ ∅ :=
⟨nonempty.ne_empty, nonempty_of_ne_empty⟩

@[simp] theorem not_nonempty_iff_eq_empty {s : finset α} : ¬s.nonempty ↔ s = ∅ :=
by { rw nonempty_iff_ne_empty, exact not_not, }

theorem eq_empty_or_nonempty (s : finset α) : s = ∅ ∨ s.nonempty :=
classical.by_cases or.inl (λ h, or.inr (nonempty_of_ne_empty h))

@[simp, norm_cast] lemma coe_empty : ((∅ : finset α) : set α) = ∅ := rfl

@[simp, norm_cast] lemma coe_eq_empty {s : finset α} :
  (s : set α) = ∅ ↔ s = ∅ :=
by rw [← coe_empty, coe_inj]

/-- A `finset` for an empty type is empty. -/
lemma eq_empty_of_not_nonempty (h : ¬ nonempty α) (s : finset α) : s = ∅ :=
finset.eq_empty_of_forall_not_mem $ λ x, false.elim $ not_nonempty_iff_imp_false.1 h x

/-! ### singleton -/
/--
`{a} : finset a` is the set `{a}` containing `a` and nothing else.

This differs from `insert a ∅` in that it does not require a `decidable_eq` instance for `α`.
-/
instance : has_singleton α (finset α) := ⟨λ a, ⟨{a}, nodup_singleton a⟩⟩

@[simp] theorem singleton_val (a : α) : ({a} : finset α).1 = a ::ₘ 0 := rfl

@[simp] theorem mem_singleton {a b : α} : b ∈ ({a} : finset α) ↔ b = a := mem_singleton

theorem not_mem_singleton {a b : α} : a ∉ ({b} : finset α) ↔ a ≠ b := not_congr mem_singleton

theorem mem_singleton_self (a : α) : a ∈ ({a} : finset α) := or.inl rfl

theorem singleton_inj {a b : α} : ({a} : finset α) = {b} ↔ a = b :=
⟨λ h, mem_singleton.1 (h ▸ mem_singleton_self _), congr_arg _⟩

@[simp] theorem singleton_nonempty (a : α) : ({a} : finset α).nonempty := ⟨a, mem_singleton_self a⟩

@[simp] theorem singleton_ne_empty (a : α) : ({a} : finset α) ≠ ∅ := (singleton_nonempty a).ne_empty

@[simp, norm_cast] lemma coe_singleton (a : α) : (({a} : finset α) : set α) = {a} :=
by { ext, simp }

lemma eq_singleton_iff_unique_mem {s : finset α} {a : α} :
  s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
begin
  split; intro t,
    rw t,
    refine ⟨finset.mem_singleton_self _, λ _, finset.mem_singleton.1⟩,
  ext, rw finset.mem_singleton,
  refine ⟨t.right _, λ r, r.symm ▸ t.left⟩
end

lemma eq_singleton_iff_nonempty_unique_mem {s : finset α} {a : α} :
  s = {a} ↔ s.nonempty ∧ ∀ x ∈ s, x = a :=
begin
  split,
  { intros h, subst h, simp, },
  { rintros ⟨hne, h_uniq⟩, rw eq_singleton_iff_unique_mem, refine ⟨_, h_uniq⟩,
    rw ← h_uniq hne.some hne.some_spec, apply hne.some_spec, },
end

lemma singleton_iff_unique_mem (s : finset α) : (∃ a, s = {a}) ↔ ∃! a, a ∈ s :=
by simp only [eq_singleton_iff_unique_mem, exists_unique]

lemma singleton_subset_set_iff {s : set α} {a : α} :
  ↑({a} : finset α) ⊆ s ↔ a ∈ s :=
by rw [coe_singleton, set.singleton_subset_iff]

@[simp] lemma singleton_subset_iff {s : finset α} {a : α} :
  {a} ⊆ s ↔ a ∈ s :=
singleton_subset_set_iff

/-! ### cons -/

/-- `cons a s h` is the set `{a} ∪ s` containing `a` and the elements of `s`. It is the same as
`insert a s` when it is defined, but unlike `insert a s` it does not require `decidable_eq α`,
and the union is guaranteed to be disjoint.  -/
def cons {α} (a : α) (s : finset α) (h : a ∉ s) : finset α :=
⟨a ::ₘ s.1, multiset.nodup_cons.2 ⟨h, s.2⟩⟩

@[simp] theorem mem_cons {α a s h b} : b ∈ @cons α a s h ↔ b = a ∨ b ∈ s :=
by rcases s with ⟨⟨s⟩⟩; apply list.mem_cons_iff

@[simp] theorem cons_val {a : α} {s : finset α} (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1 := rfl

@[simp] theorem mk_cons {a : α} {s : multiset α} (h : (a ::ₘ s).nodup) :
  (⟨a ::ₘ s, h⟩ : finset α) = cons a ⟨s, (multiset.nodup_cons.1 h).2⟩ (multiset.nodup_cons.1 h).1 :=
rfl

@[simp] theorem nonempty_cons {a : α} {s : finset α} (h : a ∉ s) : (cons a s h).nonempty :=
⟨a, mem_cons.2 (or.inl rfl)⟩

@[simp] lemma nonempty_mk_coe : ∀ {l : list α} {hl}, (⟨↑l, hl⟩ : finset α).nonempty ↔ l ≠ []
| [] hl := by simp
| (a::l) hl := by simp [← multiset.cons_coe]

/-! ### disjoint union -/

/-- `disj_union s t h` is the set such that `a ∈ disj_union s t h` iff `a ∈ s` or `a ∈ t`.
It is the same as `s ∪ t`, but it does not require decidable equality on the type. The hypothesis
ensures that the sets are disjoint. -/
def disj_union {α} (s t : finset α) (h : ∀ a ∈ s, a ∉ t) : finset α :=
⟨s.1 + t.1, multiset.nodup_add.2 ⟨s.2, t.2, h⟩⟩

@[simp] theorem mem_disj_union {α s t h a} :
  a ∈ @disj_union α s t h ↔ a ∈ s ∨ a ∈ t :=
by rcases s with ⟨⟨s⟩⟩; rcases t with ⟨⟨t⟩⟩; apply list.mem_append

/-! ### insert -/
section decidable_eq
variables [decidable_eq α]

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
instance : has_insert α (finset α) := ⟨λ a s, ⟨_, nodup_ndinsert a s.2⟩⟩

theorem insert_def (a : α) (s : finset α) : insert a s = ⟨_, nodup_ndinsert a s.2⟩ := rfl

@[simp] theorem insert_val (a : α) (s : finset α) : (insert a s).1 = ndinsert a s.1 := rfl

theorem insert_val' (a : α) (s : finset α) : (insert a s).1 = erase_dup (a ::ₘ s.1) :=
by rw [erase_dup_cons, erase_dup_eq_self]; refl

theorem insert_val_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1 :=
by rw [insert_val, ndinsert_of_not_mem h]

@[simp] theorem mem_insert {a b : α} {s : finset α} : a ∈ insert b s ↔ a = b ∨ a ∈ s := mem_ndinsert

theorem mem_insert_self (a : α) (s : finset α) : a ∈ insert a s := mem_ndinsert_self a s.1
theorem mem_insert_of_mem {a b : α} {s : finset α} (h : a ∈ s) : a ∈ insert b s :=
mem_ndinsert_of_mem h
theorem mem_of_mem_insert_of_ne {a b : α} {s : finset α} (h : b ∈ insert a s) : b ≠ a → b ∈ s :=
(mem_insert.1 h).resolve_left

@[simp] theorem cons_eq_insert {α} [decidable_eq α] (a s h) : @cons α a s h = insert a s :=
ext $ λ a, by simp

@[simp, norm_cast] lemma coe_insert (a : α) (s : finset α) :
  ↑(insert a s) = (insert a s : set α) :=
set.ext $ λ x, by simp only [mem_coe, mem_insert, set.mem_insert_iff]

lemma mem_insert_coe {s : finset α} {x y : α} : x ∈ insert y s ↔ x ∈ insert y (s : set α) :=
by simp

instance : is_lawful_singleton α (finset α) := ⟨λ a, by { ext, simp }⟩

@[simp] theorem insert_eq_of_mem {a : α} {s : finset α} (h : a ∈ s) : insert a s = s :=
eq_of_veq $ ndinsert_of_mem h

@[simp] theorem insert_singleton_self_eq (a : α) : ({a, a} : finset α) = {a} :=
insert_eq_of_mem $ mem_singleton_self _

theorem insert.comm (a b : α) (s : finset α) : insert a (insert b s) = insert b (insert a s) :=
ext $ λ x, by simp only [mem_insert, or.left_comm]

theorem insert_singleton_comm (a b : α) : ({a, b} : finset α) = {b, a} :=
begin
  ext,
  simp [or.comm]
end

@[simp] theorem insert_idem (a : α) (s : finset α) : insert a (insert a s) = insert a s :=
ext $ λ x, by simp only [mem_insert, or.assoc.symm, or_self]

@[simp] theorem insert_nonempty (a : α) (s : finset α) : (insert a s).nonempty :=
⟨a, mem_insert_self a s⟩

@[simp] theorem insert_ne_empty (a : α) (s : finset α) : insert a s ≠ ∅ :=
(insert_nonempty a s).ne_empty

section
universe u
/-!
The universe annotation is required for the following instance, possibly this is a bug in Lean. See
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/strange.20error.20(universe.20issue.3F)
-/

instance {α : Type u} [decidable_eq α] (i : α) (s : finset α) :
  nonempty.{u + 1} ((insert i s : finset α) : set α) :=
(finset.coe_nonempty.mpr (s.insert_nonempty i)).to_subtype

end

lemma ne_insert_of_not_mem (s t : finset α) {a : α} (h : a ∉ s) :
  s ≠ insert a t :=
by { contrapose! h, simp [h] }

theorem insert_subset {a : α} {s t : finset α} : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
by simp only [subset_iff, mem_insert, forall_eq, or_imp_distrib, forall_and_distrib]

theorem subset_insert (a : α) (s : finset α) : s ⊆ insert a s :=
λ b, mem_insert_of_mem

theorem insert_subset_insert (a : α) {s t : finset α} (h : s ⊆ t) : insert a s ⊆ insert a t :=
insert_subset.2 ⟨mem_insert_self _ _, subset.trans h (subset_insert _ _)⟩

lemma ssubset_iff {s t : finset α} : s ⊂ t ↔ (∃a ∉ s, insert a s ⊆ t) :=
by exact_mod_cast @set.ssubset_iff_insert α s t

lemma ssubset_insert {s : finset α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
ssubset_iff.mpr ⟨a, h, subset.refl _⟩

@[elab_as_eliminator]
lemma cons_induction {α : Type*} {p : finset α → Prop}
  (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α} (h : a ∉ s), p s → p (cons a s h)) : ∀ s, p s
| ⟨s, nd⟩ := multiset.induction_on s (λ _, h₁) (λ a s IH nd, begin
    cases nodup_cons.1 nd with m nd',
    rw [← (eq_of_veq _ : cons a (finset.mk s _) m = ⟨a ::ₘ s, nd⟩)],
    { exact h₂ (by exact m) (IH nd') },
    { rw [cons_val] }
  end) nd

@[elab_as_eliminator]
lemma cons_induction_on {α : Type*} {p : finset α → Prop} (s : finset α)
  (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α} (h : a ∉ s), p s → p (cons a s h)) : p s :=
cons_induction h₁ h₂ s

@[elab_as_eliminator]
protected theorem induction {α : Type*} {p : finset α → Prop} [decidable_eq α]
  (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α}, a ∉ s → p s → p (insert a s)) : ∀ s, p s :=
cons_induction h₁ $ λ a s ha, (s.cons_eq_insert a ha).symm ▸ h₂ ha

/--
To prove a proposition about an arbitrary `finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α`,
then it holds for the `finset` obtained by inserting a new element.
-/
@[elab_as_eliminator]
protected theorem induction_on {α : Type*} {p : finset α → Prop} [decidable_eq α]
  (s : finset α) (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α}, a ∉ s → p s → p (insert a s)) : p s :=
finset.induction h₁ h₂ s

/--
To prove a proposition about `S : finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α ⊆ S`,
then it holds for the `finset` obtained by inserting a new element of `S`.
-/
@[elab_as_eliminator]
theorem induction_on' {α : Type*} {p : finset α → Prop} [decidable_eq α]
  (S : finset α) (h₁ : p ∅) (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → a ∉ s → p s → p (insert a s)) : p S :=
@finset.induction_on α (λ T, T ⊆ S → p T) _ S (λ _, h₁) (λ a s has hqs hs,
  let ⟨hS, sS⟩ := finset.insert_subset.1 hs in h₂ hS sS has (hqs sS)) (finset.subset.refl S)

/-- Inserting an element to a finite set is equivalent to the option type. -/
def subtype_insert_equiv_option {t : finset α} {x : α} (h : x ∉ t) :
  {i // i ∈ insert x t} ≃ option {i // i ∈ t} :=
begin
  refine
  { to_fun := λ y, if h : ↑y = x then none else some ⟨y, (mem_insert.mp y.2).resolve_left h⟩,
    inv_fun := λ y, y.elim ⟨x, mem_insert_self _ _⟩ $ λ z, ⟨z, mem_insert_of_mem z.2⟩,
    .. },
  { intro y, by_cases h : ↑y = x,
    simp only [subtype.ext_iff, h, option.elim, dif_pos, subtype.coe_mk],
    simp only [h, option.elim, dif_neg, not_false_iff, subtype.coe_eta, subtype.coe_mk] },
  { rintro (_|y), simp only [option.elim, dif_pos, subtype.coe_mk],
    have : ↑y ≠ x, { rintro ⟨⟩, exact h y.2 },
    simp only [this, option.elim, subtype.eta, dif_neg, not_false_iff, subtype.coe_eta,
      subtype.coe_mk] },
end

/-! ### union -/

/-- `s ∪ t` is the set such that `a ∈ s ∪ t` iff `a ∈ s` or `a ∈ t`. -/
instance : has_union (finset α) := ⟨λ s₁ s₂, ⟨_, nodup_ndunion s₁.1 s₂.2⟩⟩

theorem union_val_nd (s₁ s₂ : finset α) : (s₁ ∪ s₂).1 = ndunion s₁.1 s₂.1 := rfl

@[simp] theorem union_val (s₁ s₂ : finset α) : (s₁ ∪ s₂).1 = s₁.1 ∪ s₂.1 :=
ndunion_eq_union s₁.2

@[simp] theorem mem_union {a : α} {s₁ s₂ : finset α} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ := mem_ndunion

@[simp] theorem disj_union_eq_union {α} [decidable_eq α] (s t h) : @disj_union α s t h = s ∪ t :=
ext $ λ a, by simp

theorem mem_union_left {a : α} {s₁ : finset α} (s₂ : finset α) (h : a ∈ s₁) : a ∈ s₁ ∪ s₂ :=
mem_union.2 $ or.inl h

theorem mem_union_right {a : α} {s₂ : finset α} (s₁ : finset α) (h : a ∈ s₂) : a ∈ s₁ ∪ s₂ :=
mem_union.2 $ or.inr h

theorem forall_mem_union {s₁ s₂ : finset α} {p : α → Prop} :
  (∀ ab ∈ (s₁ ∪ s₂), p ab) ↔ (∀ a ∈ s₁, p a) ∧ (∀ b ∈ s₂, p b) :=
⟨λ h, ⟨λ a, h a ∘ mem_union_left _, λ b, h b ∘ mem_union_right _⟩,
 λ h ab hab, (mem_union.mp hab).elim (h.1 _) (h.2 _)⟩

theorem not_mem_union {a : α} {s₁ s₂ : finset α} : a ∉ s₁ ∪ s₂ ↔ a ∉ s₁ ∧ a ∉ s₂ :=
by rw [mem_union, not_or_distrib]

@[simp, norm_cast]
lemma coe_union (s₁ s₂ : finset α) : ↑(s₁ ∪ s₂) = (s₁ ∪ s₂ : set α) := set.ext $ λ x, mem_union

theorem union_subset {s₁ s₂ s₃ : finset α} (h₁ : s₁ ⊆ s₃) (h₂ : s₂ ⊆ s₃) : s₁ ∪ s₂ ⊆ s₃ :=
val_le_iff.1 (ndunion_le.2 ⟨h₁, val_le_iff.2 h₂⟩)

theorem subset_union_left (s₁ s₂ : finset α) : s₁ ⊆ s₁ ∪ s₂ := λ x, mem_union_left _

theorem subset_union_right (s₁ s₂ : finset α) : s₂ ⊆ s₁ ∪ s₂ := λ x, mem_union_right _

theorem union_subset_iff {s₁ s₂ s₃ : finset α} : s₁ ∪ s₂ ⊆ s₃ ↔ s₁ ⊆ s₃ ∧ s₂ ⊆ s₃ :=
⟨λ h, ⟨subset.trans (subset_union_left _ _) h, subset.trans (subset_union_right _ _) h⟩,
  and.rec union_subset⟩

lemma union_subset_union {s1 t1 s2 t2 : finset α} (h1 : s1 ⊆ t1) (h2 : s2 ⊆ t2) :
  s1 ∪ s2 ⊆ t1 ∪ t2 :=
by { intros x hx, rw finset.mem_union at hx ⊢, tauto }

theorem union_comm (s₁ s₂ : finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
ext $ λ x, by simp only [mem_union, or_comm]

instance : is_commutative (finset α) (∪) := ⟨union_comm⟩

@[simp] theorem union_assoc (s₁ s₂ s₃ : finset α) : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
ext $ λ x, by simp only [mem_union, or_assoc]

instance : is_associative (finset α) (∪) := ⟨union_assoc⟩

@[simp] theorem union_idempotent (s : finset α) : s ∪ s = s :=
ext $ λ _, mem_union.trans $ or_self _

instance : is_idempotent (finset α) (∪) := ⟨union_idempotent⟩

theorem union_left_comm (s₁ s₂ s₃ : finset α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
ext $ λ _, by simp only [mem_union, or.left_comm]

theorem union_right_comm (s₁ s₂ s₃ : finset α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
ext $ λ x, by simp only [mem_union, or_assoc, or_comm (x ∈ s₂)]

theorem union_self (s : finset α) : s ∪ s = s := union_idempotent s

@[simp] theorem union_empty (s : finset α) : s ∪ ∅ = s :=
ext $ λ x, mem_union.trans $ or_false _

@[simp] theorem empty_union (s : finset α) : ∅ ∪ s = s :=
ext $ λ x, mem_union.trans $ false_or _

theorem insert_eq (a : α) (s : finset α) : insert a s = {a} ∪ s := rfl

@[simp] theorem insert_union (a : α) (s t : finset α) : insert a s ∪ t = insert a (s ∪ t) :=
by simp only [insert_eq, union_assoc]

@[simp] theorem union_insert (a : α) (s t : finset α) : s ∪ insert a t = insert a (s ∪ t) :=
by simp only [insert_eq, union_left_comm]

theorem insert_union_distrib (a : α) (s t : finset α) :
  insert a (s ∪ t) = insert a s ∪ insert a t :=
by simp only [insert_union, union_insert, insert_idem]

@[simp] lemma union_eq_left_iff_subset {s t : finset α} :
  s ∪ t = s ↔ t ⊆ s :=
begin
  split,
  { assume h,
    have : t ⊆ s ∪ t := subset_union_right _ _,
    rwa h at this },
  { assume h,
    exact subset.antisymm (union_subset (subset.refl _) h) (subset_union_left _ _) }
end

@[simp] lemma left_eq_union_iff_subset {s t : finset α} :
  s = s ∪ t ↔ t ⊆ s :=
by rw [← union_eq_left_iff_subset, eq_comm]

@[simp] lemma union_eq_right_iff_subset {s t : finset α} :
  t ∪ s = s ↔ t ⊆ s :=
by rw [union_comm, union_eq_left_iff_subset]

@[simp] lemma right_eq_union_iff_subset {s t : finset α} :
  s = t ∪ s ↔ t ⊆ s :=
by rw [← union_eq_right_iff_subset, eq_comm]

/--
To prove a relation on pairs of `finset X`, it suffices to show that it is
  * symmetric,
  * it holds when one of the `finset`s is empty,
  * it holds for pairs of singletons,
  * if it holds for `[a, c]` and for `[b, c]`, then it holds for `[a ∪ b, c]`.
-/
lemma induction_on_union (P : finset α → finset α → Prop)
  (symm : ∀ {a b}, P a b → P b a)
  (empty_right : ∀ {a}, P a ∅)
  (singletons : ∀ {a b}, P {a} {b})
  (union_of : ∀ {a b c}, P a c → P b c → P (a ∪ b) c) :
  ∀ a b, P a b :=
begin
  intros a b,
  refine finset.induction_on b empty_right (λ x s xs hi, symm _),
  rw finset.insert_eq,
  apply union_of _ (symm hi),
  refine finset.induction_on a empty_right (λ a t ta hi, symm _),
  rw finset.insert_eq,
  exact union_of singletons (symm hi),
end

lemma exists_mem_subset_of_subset_bUnion_of_directed_on {α ι : Type*}
  {f : ι → set α}  {c : set ι} {a : ι} (hac : a ∈ c) (hc : directed_on (λ i j, f i ⊆ f j) c)
  {s : finset α} (hs : (s : set α) ⊆ ⋃ i ∈ c, f i) : ∃ i ∈ c, (s : set α) ⊆ f i :=
begin
  classical,
  revert hs,
  apply s.induction_on,
  { intros,
    use [a, hac],
    simp },
  { intros b t hbt htc hbtc,
    obtain ⟨i : ι , hic : i ∈ c, hti : (t : set α) ⊆ f i⟩ :=
      htc (set.subset.trans (t.subset_insert b) hbtc),
    obtain ⟨j, hjc, hbj⟩ : ∃ j ∈ c, b ∈ f j,
      by simpa [set.mem_bUnion_iff] using hbtc (t.mem_insert_self b),
    rcases hc j hjc i hic with ⟨k, hkc, hk, hk'⟩,
    use [k, hkc],
    rw [coe_insert, set.insert_subset],
    exact ⟨hk hbj, trans hti hk'⟩ }
end

/-! ### inter -/

/-- `s ∩ t` is the set such that `a ∈ s ∩ t` iff `a ∈ s` and `a ∈ t`. -/
instance : has_inter (finset α) := ⟨λ s₁ s₂, ⟨_, nodup_ndinter s₂.1 s₁.2⟩⟩

-- TODO: some of these results may have simpler proofs, once there are enough results
-- to obtain the `lattice` instance.

theorem inter_val_nd (s₁ s₂ : finset α) : (s₁ ∩ s₂).1 = ndinter s₁.1 s₂.1 := rfl

@[simp] theorem inter_val (s₁ s₂ : finset α) : (s₁ ∩ s₂).1 = s₁.1 ∩ s₂.1 :=
ndinter_eq_inter s₁.2

@[simp] theorem mem_inter {a : α} {s₁ s₂ : finset α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ := mem_ndinter

theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : finset α} (h : a ∈ s₁ ∩ s₂) :
  a ∈ s₁ := (mem_inter.1 h).1

theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : finset α} (h : a ∈ s₁ ∩ s₂) :
  a ∈ s₂ := (mem_inter.1 h).2

theorem mem_inter_of_mem {a : α} {s₁ s₂ : finset α} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
and_imp.1 mem_inter.2

theorem inter_subset_left (s₁ s₂ : finset α) : s₁ ∩ s₂ ⊆ s₁ := λ a, mem_of_mem_inter_left

theorem inter_subset_right (s₁ s₂ : finset α) : s₁ ∩ s₂ ⊆ s₂ := λ a, mem_of_mem_inter_right

theorem subset_inter {s₁ s₂ s₃ : finset α} : s₁ ⊆ s₂ → s₁ ⊆ s₃ → s₁ ⊆ s₂ ∩ s₃ :=
by simp only [subset_iff, mem_inter] {contextual:=tt}; intros; split; trivial

@[simp, norm_cast]
lemma coe_inter (s₁ s₂ : finset α) : ↑(s₁ ∩ s₂) = (s₁ ∩ s₂ : set α) := set.ext $ λ _, mem_inter

@[simp] theorem union_inter_cancel_left {s t : finset α} : (s ∪ t) ∩ s = s :=
by rw [← coe_inj, coe_inter, coe_union, set.union_inter_cancel_left]

@[simp] theorem union_inter_cancel_right {s t : finset α} : (s ∪ t) ∩ t = t :=
by rw [← coe_inj, coe_inter, coe_union, set.union_inter_cancel_right]

theorem inter_comm (s₁ s₂ : finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
ext $ λ _, by simp only [mem_inter, and_comm]

@[simp] theorem inter_assoc (s₁ s₂ s₃ : finset α) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
ext $ λ _, by simp only [mem_inter, and_assoc]

theorem inter_left_comm (s₁ s₂ s₃ : finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
ext $ λ _, by simp only [mem_inter, and.left_comm]

theorem inter_right_comm (s₁ s₂ s₃ : finset α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
ext $ λ _, by simp only [mem_inter, and.right_comm]

@[simp] theorem inter_self (s : finset α) : s ∩ s = s :=
ext $ λ _, mem_inter.trans $ and_self _

@[simp] theorem inter_empty (s : finset α) : s ∩ ∅ = ∅ :=
ext $ λ _, mem_inter.trans $ and_false _

@[simp] theorem empty_inter (s : finset α) : ∅ ∩ s = ∅ :=
ext $ λ _, mem_inter.trans $ false_and _

@[simp] lemma inter_union_self (s t : finset α) : s ∩ (t ∪ s) = s :=
by rw [inter_comm, union_inter_cancel_right]

@[simp] theorem insert_inter_of_mem {s₁ s₂ : finset α} {a : α} (h : a ∈ s₂) :
  insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
ext $ λ x, have x = a ∨ x ∈ s₂ ↔ x ∈ s₂, from or_iff_right_of_imp $ by rintro rfl; exact h,
by simp only [mem_inter, mem_insert, or_and_distrib_left, this]

@[simp] theorem inter_insert_of_mem {s₁ s₂ : finset α} {a : α} (h : a ∈ s₁) :
  s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) :=
by rw [inter_comm, insert_inter_of_mem h, inter_comm]

@[simp] theorem insert_inter_of_not_mem {s₁ s₂ : finset α} {a : α} (h : a ∉ s₂) :
  insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
ext $ λ x, have ¬ (x = a ∧ x ∈ s₂), by rintro ⟨rfl, H⟩; exact h H,
by simp only [mem_inter, mem_insert, or_and_distrib_right, this, false_or]

@[simp] theorem inter_insert_of_not_mem {s₁ s₂ : finset α} {a : α} (h : a ∉ s₁) :
  s₁ ∩ insert a s₂ = s₁ ∩ s₂ :=
by rw [inter_comm, insert_inter_of_not_mem h, inter_comm]

@[simp] theorem singleton_inter_of_mem {a : α} {s : finset α} (H : a ∈ s) : {a} ∩ s = {a} :=
show insert a ∅ ∩ s = insert a ∅, by rw [insert_inter_of_mem H, empty_inter]

@[simp] theorem singleton_inter_of_not_mem {a : α} {s : finset α} (H : a ∉ s) : {a} ∩ s = ∅ :=
eq_empty_of_forall_not_mem $ by simp only [mem_inter, mem_singleton]; rintro x ⟨rfl, h⟩; exact H h

@[simp] theorem inter_singleton_of_mem {a : α} {s : finset α} (h : a ∈ s) : s ∩ {a} = {a} :=
by rw [inter_comm, singleton_inter_of_mem h]

@[simp] theorem inter_singleton_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : s ∩ {a} = ∅ :=
by rw [inter_comm, singleton_inter_of_not_mem h]

@[mono]
lemma inter_subset_inter {x y s t : finset α} (h : x ⊆ y) (h' : s ⊆ t) : x ∩ s ⊆ y ∩ t :=
begin
  intros a a_in,
  rw finset.mem_inter at a_in ⊢,
  exact ⟨h a_in.1, h' a_in.2⟩
end

lemma inter_subset_inter_right {x y s : finset α} (h : x ⊆ y) : x ∩ s ⊆ y ∩ s :=
finset.inter_subset_inter h (finset.subset.refl _)

lemma inter_subset_inter_left {x y s : finset α} (h : x ⊆ y) : s ∩ x ⊆ s ∩ y :=
finset.inter_subset_inter (finset.subset.refl _) h

/-! ### lattice laws -/

instance : lattice (finset α) :=
{ sup          := (∪),
  sup_le       := assume a b c, union_subset,
  le_sup_left  := subset_union_left,
  le_sup_right := subset_union_right,
  inf          := (∩),
  le_inf       := assume a b c, subset_inter,
  inf_le_left  := inter_subset_left,
  inf_le_right := inter_subset_right,
  ..finset.partial_order }

@[simp] theorem sup_eq_union : ((⊔) : finset α → finset α → finset α) = (∪) := rfl
@[simp] theorem inf_eq_inter : ((⊓) : finset α → finset α → finset α) = (∩) := rfl

instance : semilattice_inf_bot (finset α) :=
{ bot := ∅, bot_le := empty_subset, ..finset.lattice }

@[simp] lemma bot_eq_empty : (⊥ : finset α) = ∅ := rfl

instance {α : Type*} [decidable_eq α] : semilattice_sup_bot (finset α) :=
{ ..finset.semilattice_inf_bot, ..finset.lattice }

instance : distrib_lattice (finset α) :=
{ le_sup_inf := assume a b c, show (a ∪ b) ∩ (a ∪ c) ⊆ a ∪ b ∩ c,
    by simp only [subset_iff, mem_inter, mem_union, and_imp, or_imp_distrib] {contextual:=tt};
    simp only [true_or, imp_true_iff, true_and, or_true],
  ..finset.lattice }

@[simp] theorem union_left_idem (s t : finset α) : s ∪ (s ∪ t) = s ∪ t := sup_left_idem

@[simp] theorem union_right_idem (s t : finset α) : s ∪ t ∪ t = s ∪ t := sup_right_idem

@[simp] theorem inter_left_idem (s t : finset α) : s ∩ (s ∩ t) = s ∩ t := inf_left_idem

@[simp] theorem inter_right_idem (s t : finset α) : s ∩ t ∩ t = s ∩ t := inf_right_idem

theorem inter_distrib_left (s t u : finset α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := inf_sup_left

theorem inter_distrib_right (s t u : finset α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) := inf_sup_right

theorem union_distrib_left (s t u : finset α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) := sup_inf_left

theorem union_distrib_right (s t u : finset α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) := sup_inf_right

lemma union_eq_empty_iff (A B : finset α) : A ∪ B = ∅ ↔ A = ∅ ∧ B = ∅ := sup_eq_bot_iff

theorem inter_eq_left_iff_subset (s t : finset α) :
  s ∩ t = s ↔ s ⊆ t :=
(inf_eq_left : s ⊓ t = s ↔ s ≤ t)

theorem inter_eq_right_iff_subset (s t : finset α) :
  t ∩ s = s ↔ s ⊆ t :=
(inf_eq_right : t ⊓ s = s ↔ s ≤ t)

/-! ### erase -/

/-- `erase s a` is the set `s - {a}`, that is, the elements of `s` which are
  not equal to `a`. -/
def erase (s : finset α) (a : α) : finset α := ⟨_, nodup_erase_of_nodup a s.2⟩

@[simp] theorem erase_val (s : finset α) (a : α) : (erase s a).1 = s.1.erase a := rfl

@[simp] theorem mem_erase {a b : α} {s : finset α} : a ∈ erase s b ↔ a ≠ b ∧ a ∈ s :=
mem_erase_iff_of_nodup s.2

theorem not_mem_erase (a : α) (s : finset α) : a ∉ erase s a := mem_erase_of_nodup s.2

@[simp] theorem erase_empty (a : α) : erase ∅ a = ∅ := rfl

theorem ne_of_mem_erase {a b : α} {s : finset α} : b ∈ erase s a → b ≠ a :=
by simp only [mem_erase]; exact and.left

theorem mem_of_mem_erase {a b : α} {s : finset α} : b ∈ erase s a → b ∈ s := mem_of_mem_erase

theorem mem_erase_of_ne_of_mem {a b : α} {s : finset α} : a ≠ b → a ∈ s → a ∈ erase s b :=
by simp only [mem_erase]; exact and.intro

/-- An element of `s` that is not an element of `erase s a` must be
`a`. -/
lemma eq_of_mem_of_not_mem_erase {a b : α} {s : finset α} (hs : b ∈ s)
    (hsa : b ∉ s.erase a) : b = a :=
begin
  rw [mem_erase, not_and] at hsa,
  exact not_imp_not.mp hsa hs
end

theorem erase_insert {a : α} {s : finset α} (h : a ∉ s) : erase (insert a s) a = s :=
ext $ assume x, by simp only [mem_erase, mem_insert, and_or_distrib_left, not_and_self, false_or];
apply and_iff_right_of_imp; rintro H rfl; exact h H

theorem insert_erase {a : α} {s : finset α} (h : a ∈ s) : insert a (erase s a) = s :=
ext $ assume x, by simp only [mem_insert, mem_erase, or_and_distrib_left, dec_em, true_and];
apply or_iff_right_of_imp; rintro rfl; exact h

theorem erase_subset_erase (a : α) {s t : finset α} (h : s ⊆ t) : erase s a ⊆ erase t a :=
val_le_iff.1 $ erase_le_erase _ $ val_le_iff.2 h

theorem erase_subset (a : α) (s : finset α) : erase s a ⊆ s := erase_subset _ _

@[simp, norm_cast] lemma coe_erase (a : α) (s : finset α) : ↑(erase s a) = (s \ {a} : set α) :=
set.ext $ λ _, mem_erase.trans $ by rw [and_comm, set.mem_diff, set.mem_singleton_iff]; refl

lemma erase_ssubset {a : α} {s : finset α} (h : a ∈ s) : s.erase a ⊂ s :=
calc s.erase a ⊂ insert a (s.erase a) : ssubset_insert $ not_mem_erase _ _
  ... = _ : insert_erase h

theorem erase_eq_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : erase s a = s :=
eq_of_veq $ erase_of_not_mem h

theorem subset_insert_iff {a : α} {s t : finset α} : s ⊆ insert a t ↔ erase s a ⊆ t :=
by simp only [subset_iff, or_iff_not_imp_left, mem_erase, mem_insert, and_imp];
exact forall_congr (λ x, forall_swap)

theorem erase_insert_subset (a : α) (s : finset α) : erase (insert a s) a ⊆ s :=
subset_insert_iff.1 $ subset.refl _

theorem insert_erase_subset (a : α) (s : finset α) : s ⊆ insert a (erase s a) :=
subset_insert_iff.2 $ subset.refl _

lemma erase_inj {x y : α} (s : finset α) (hx : x ∈ s) :
  s.erase x = s.erase y ↔ x = y :=
begin
  refine ⟨λ h, _, congr_arg _⟩,
  rw eq_of_mem_of_not_mem_erase hx,
  rw ←h,
  simp,
end

lemma erase_inj_on (s : finset α) : set.inj_on s.erase s :=
λ _ _ _ _, (erase_inj s ‹_›).mp

/-! ### sdiff -/

/-- `s \ t` is the set consisting of the elements of `s` that are not in `t`. -/
instance : has_sdiff (finset α) := ⟨λs₁ s₂, ⟨s₁.1 - s₂.1, nodup_of_le (sub_le_self _ _) s₁.2⟩⟩

@[simp] theorem mem_sdiff {a : α} {s₁ s₂ : finset α} :
  a ∈ s₁ \ s₂ ↔ a ∈ s₁ ∧ a ∉ s₂ := mem_sub_of_nodup s₁.2

@[simp] theorem inter_sdiff_self (s₁ s₂ : finset α) : s₁ ∩ (s₂ \ s₁) = ∅ :=
eq_empty_of_forall_not_mem $
by simp only [mem_inter, mem_sdiff]; rintro x ⟨h, _, hn⟩; exact hn h

instance : generalized_boolean_algebra (finset α) :=
{ sup_inf_sdiff := λ x y, by { simp only [ext_iff, mem_union, mem_sdiff, inf_eq_inter, sup_eq_union,
      mem_inter], tauto },
  inf_inf_sdiff := λ x y, by { simp only [ext_iff, inter_sdiff_self, inter_empty, inter_assoc,
      false_iff, inf_eq_inter, not_mem_empty], tauto },
  ..finset.has_sdiff,
  ..finset.distrib_lattice,
  ..finset.semilattice_inf_bot }

lemma not_mem_sdiff_of_mem_right {a : α} {s t : finset α} (h : a ∈ t) : a ∉ s \ t :=
by simp only [mem_sdiff, h, not_true, not_false_iff, and_false]

theorem union_sdiff_of_subset {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : s₁ ∪ (s₂ \ s₁) = s₂ :=
sup_sdiff_of_le h

theorem sdiff_union_of_subset {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : (s₂ \ s₁) ∪ s₁ = s₂ :=
(union_comm _ _).trans (union_sdiff_of_subset h)

theorem inter_sdiff (s t u : finset α) : s ∩ (t \ u) = s ∩ t \ u :=
by { ext x, simp [and_assoc] }

@[simp] theorem sdiff_inter_self (s₁ s₂ : finset α) : (s₂ \ s₁) ∩ s₁ = ∅ :=
inf_sdiff_self_left

@[simp] theorem sdiff_self (s₁ : finset α) : s₁ \ s₁ = ∅ :=
sdiff_self

theorem sdiff_inter_distrib_right (s₁ s₂ s₃ : finset α) : s₁ \ (s₂ ∩ s₃) = (s₁ \ s₂) ∪ (s₁ \ s₃) :=
sdiff_inf

@[simp] theorem sdiff_inter_self_left (s₁ s₂ : finset α) : s₁ \ (s₁ ∩ s₂) = s₁ \ s₂ :=
sdiff_inf_self_left

@[simp] theorem sdiff_inter_self_right (s₁ s₂ : finset α) : s₁ \ (s₂ ∩ s₁) = s₁ \ s₂ :=
sdiff_inf_self_right

@[simp] theorem sdiff_empty {s₁ : finset α} : s₁ \ ∅ = s₁ :=
sdiff_bot

@[mono]
theorem sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : finset α} (h₁ : t₁ ⊆ t₂) (h₂ : s₂ ⊆ s₁) :
  t₁ \ s₁ ⊆ t₂ \ s₂ :=
sdiff_le_sdiff ‹t₁ ≤ t₂› ‹s₂ ≤ s₁›

@[simp, norm_cast] lemma coe_sdiff (s₁ s₂ : finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ : set α) :=
set.ext $ λ _, mem_sdiff

@[simp] theorem union_sdiff_self_eq_union {s t : finset α} : s ∪ (t \ s) = s ∪ t :=
sup_sdiff_self_right

@[simp] theorem sdiff_union_self_eq_union {s t : finset α} : (s \ t) ∪ t = s ∪ t :=
sup_sdiff_self_left

lemma union_sdiff_symm {s t : finset α} : s ∪ (t \ s) = t ∪ (s \ t) :=
sup_sdiff_symm

lemma sdiff_union_inter (s t : finset α) : (s \ t) ∪ (s ∩ t) = s :=
by { rw union_comm, exact sup_inf_sdiff _ _ }

@[simp] lemma sdiff_idem (s t : finset α) : s \ t \ t = s \ t :=
sdiff_idem

lemma sdiff_eq_empty_iff_subset {s t : finset α} : s \ t = ∅ ↔ s ⊆ t :=
sdiff_eq_bot_iff

@[simp] lemma empty_sdiff (s : finset α) : ∅ \ s = ∅ :=
bot_sdiff

lemma insert_sdiff_of_not_mem (s : finset α) {t : finset α} {x : α} (h : x ∉ t) :
  (insert x s) \ t = insert x (s \ t) :=
begin
  rw [← coe_inj, coe_insert, coe_sdiff, coe_sdiff, coe_insert],
  exact set.insert_diff_of_not_mem s h
end

lemma insert_sdiff_of_mem (s : finset α) {t : finset α} {x : α} (h : x ∈ t) :
  (insert x s) \ t = s \ t :=
begin
  rw [← coe_inj, coe_sdiff, coe_sdiff, coe_insert],
  exact set.insert_diff_of_mem s h
end

@[simp] lemma insert_sdiff_insert (s t : finset α) (x : α) :
  (insert x s) \ (insert x t) = s \ insert x t :=
insert_sdiff_of_mem _ (mem_insert_self _ _)

lemma sdiff_insert_of_not_mem {s : finset α} {x : α} (h : x ∉ s) (t : finset α) :
  s \ (insert x t) = s \ t :=
begin
  refine subset.antisymm (sdiff_subset_sdiff (subset.refl _) (subset_insert _ _)) (λ y hy, _),
  simp only [mem_sdiff, mem_insert, not_or_distrib] at hy ⊢,
  exact ⟨hy.1, λ hxy, h $ hxy ▸ hy.1, hy.2⟩
end

@[simp] lemma sdiff_subset (s t : finset α) : s \ t ⊆ s :=
show s \ t ≤ s, from sdiff_le

lemma union_sdiff_distrib (s₁ s₂ t : finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t :=
sup_sdiff

lemma sdiff_union_distrib (s t₁ t₂ : finset α) : s \ (t₁ ∪ t₂) = (s \ t₁) ∩ (s \ t₂) :=
sdiff_sup

lemma union_sdiff_self (s t : finset α) : (s ∪ t) \ t = s \ t :=
sup_sdiff_right_self

lemma sdiff_singleton_eq_erase (a : α) (s : finset α) : s \ singleton a = erase s a :=
by { ext, rw [mem_erase, mem_sdiff, mem_singleton], tauto }

lemma sdiff_sdiff_self_left (s t : finset α) : s \ (s \ t) = s ∩ t :=
sdiff_sdiff_right_self

lemma sdiff_eq_sdiff_iff_inter_eq_inter {s t₁ t₂ : finset α} : s \ t₁ = s \ t₂ ↔ s ∩ t₁ = s ∩ t₂ :=
sdiff_eq_sdiff_iff_inf_eq_inf

lemma union_eq_sdiff_union_sdiff_union_inter (s t : finset α) :
  s ∪ t = (s \ t) ∪ (t \ s) ∪ (s ∩ t) :=
sup_eq_sdiff_sup_sdiff_sup_inf

end decidable_eq

/-! ### attach -/

/-- `attach s` takes the elements of `s` and forms a new set of elements of the
  subtype `{x // x ∈ s}`. -/
def attach (s : finset α) : finset {x // x ∈ s} := ⟨attach s.1, nodup_attach.2 s.2⟩

theorem sizeof_lt_sizeof_of_mem [has_sizeof α] {x : α} {s : finset α} (hx : x ∈ s) :
  sizeof x < sizeof s := by
{ cases s, dsimp [sizeof, has_sizeof.sizeof, finset.sizeof],
  apply lt_add_left, exact multiset.sizeof_lt_sizeof_of_mem hx }

@[simp] theorem attach_val (s : finset α) : s.attach.1 = s.1.attach := rfl

@[simp] theorem mem_attach (s : finset α) : ∀ x, x ∈ s.attach := mem_attach _

@[simp] theorem attach_empty : attach (∅ : finset α) = ∅ := rfl

/-! ### piecewise -/
section piecewise

/-- `s.piecewise f g` is the function equal to `f` on the finset `s`, and to `g` on its
complement. -/
def piecewise {α : Type*} {δ : α → Sort*} (s : finset α) (f g : Πi, δ i) [∀j, decidable (j ∈ s)] :
  Πi, δ i :=
λi, if i ∈ s then f i else g i

variables {δ : α → Sort*} (s : finset α) (f g : Πi, δ i)

@[simp] lemma piecewise_insert_self [decidable_eq α] {j : α} [∀i, decidable (i ∈ insert j s)] :
  (insert j s).piecewise f g j = f j :=
by simp [piecewise]

@[simp] lemma piecewise_empty [∀i : α, decidable (i ∈ (∅ : finset α))] : piecewise ∅ f g = g :=
by { ext i, simp [piecewise] }

variable [∀j, decidable (j ∈ s)]

@[norm_cast] lemma piecewise_coe [∀j, decidable (j ∈ (s : set α))] :
  (s : set α).piecewise f g = s.piecewise f g :=
by { ext, congr }

@[simp, priority 980]
lemma piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i :=
by simp [piecewise, hi]

@[simp, priority 980]
lemma piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i :=
by simp [piecewise, hi]

lemma piecewise_congr {f f' g g' : Π i, δ i} (hf : ∀ i ∈ s, f i = f' i) (hg : ∀ i ∉ s, g i = g' i) :
  s.piecewise f g = s.piecewise f' g' :=
funext $ λ i, if_ctx_congr iff.rfl (hf i) (hg i)

@[simp, priority 990]
lemma piecewise_insert_of_ne [decidable_eq α] {i j : α} [∀i, decidable (i ∈ insert j s)]
  (h : i ≠ j) : (insert j s).piecewise f g i = s.piecewise f g i :=
by simp [piecewise, h]

lemma piecewise_insert [decidable_eq α] (j : α) [∀i, decidable (i ∈ insert j s)] :
  (insert j s).piecewise f g = update (s.piecewise f g) j (f j) :=
begin
  classical,
  rw [← piecewise_coe, ← piecewise_coe, ← set.piecewise_insert, ← coe_insert j s],
  congr
end

lemma piecewise_cases {i} (p : δ i → Prop) (hf : p (f i)) (hg : p (g i)) : p (s.piecewise f g i) :=
by by_cases hi : i ∈ s; simpa [hi]

lemma piecewise_mem_set_pi {δ : α → Type*} {t : set α} {t' : Π i, set (δ i)}
  {f g} (hf : f ∈ set.pi t t') (hg : g ∈ set.pi t t') : s.piecewise f g ∈ set.pi t t' :=
by { classical, rw ← piecewise_coe, exact set.piecewise_mem_pi ↑s hf hg }

lemma piecewise_singleton [decidable_eq α] (i : α) :
  piecewise {i} f g = update g i (f i) :=
by rw [← insert_emptyc_eq, piecewise_insert, piecewise_empty]

lemma piecewise_piecewise_of_subset_left {s t : finset α} [Π i, decidable (i ∈ s)]
  [Π i, decidable (i ∈ t)] (h : s ⊆ t) (f₁ f₂ g : Π a, δ a) :
  s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g :=
s.piecewise_congr (λ i hi, piecewise_eq_of_mem _ _ _ (h hi)) (λ _ _, rfl)

@[simp] lemma piecewise_idem_left (f₁ f₂ g : Π a, δ a) :
  s.piecewise (s.piecewise f₁ f₂) g = s.piecewise f₁ g :=
piecewise_piecewise_of_subset_left (subset.refl _) _ _ _

lemma piecewise_piecewise_of_subset_right {s t : finset α} [Π i, decidable (i ∈ s)]
  [Π i, decidable (i ∈ t)] (h : t ⊆ s) (f g₁ g₂ : Π a, δ a) :
  s.piecewise f (t.piecewise g₁ g₂) = s.piecewise f g₂ :=
s.piecewise_congr (λ _ _, rfl) (λ i hi, t.piecewise_eq_of_not_mem _ _ (mt (@h _) hi))

@[simp] lemma piecewise_idem_right (f g₁ g₂ : Π a, δ a) :
  s.piecewise f (s.piecewise g₁ g₂) = s.piecewise f g₂ :=
piecewise_piecewise_of_subset_right (subset.refl _) f g₁ g₂

lemma update_eq_piecewise {β : Type*} [decidable_eq α] (f : α → β) (i : α) (v : β) :
  update f i v = piecewise (singleton i) (λj, v) f :=
(piecewise_singleton _ _ _).symm

lemma update_piecewise [decidable_eq α] (i : α) (v : δ i) :
  update (s.piecewise f g) i v = s.piecewise (update f i v) (update g i v) :=
begin
  ext j,
  rcases em (j = i) with (rfl|hj); by_cases hs : j ∈ s; simp *
end

lemma update_piecewise_of_mem [decidable_eq α] {i : α} (hi : i ∈ s) (v : δ i) :
  update (s.piecewise f g) i v = s.piecewise (update f i v) g :=
begin
  rw update_piecewise,
  refine s.piecewise_congr (λ _ _, rfl) (λ j hj, update_noteq _ _ _),
  exact λ h, hj (h.symm ▸ hi)
end

lemma update_piecewise_of_not_mem [decidable_eq α] {i : α} (hi : i ∉ s) (v : δ i) :
  update (s.piecewise f g) i v = s.piecewise f (update g i v) :=
begin
  rw update_piecewise,
  refine s.piecewise_congr (λ j hj, update_noteq _ _ _)  (λ _ _, rfl),
  exact λ h, hi (h ▸ hj)
end

lemma piecewise_le_of_le_of_le {δ : α → Type*} [Π i, preorder (δ i)] {f g h : Π i, δ i}
  (Hf : f ≤ h) (Hg : g ≤ h) : s.piecewise f g ≤ h :=
λ x, piecewise_cases s f g (≤ h x) (Hf x) (Hg x)

lemma le_piecewise_of_le_of_le {δ : α → Type*} [Π i, preorder (δ i)] {f g h : Π i, δ i}
  (Hf : h ≤ f) (Hg : h ≤ g) : h ≤ s.piecewise f g :=
λ x, piecewise_cases s f g (λ y, h x ≤ y) (Hf x) (Hg x)

lemma piecewise_le_piecewise' {δ : α → Type*} [Π i, preorder (δ i)] {f g f' g' : Π i, δ i}
  (Hf : ∀ x ∈ s, f x ≤ f' x) (Hg : ∀ x ∉ s, g x ≤ g' x) : s.piecewise f g ≤ s.piecewise f' g' :=
λ x, by { by_cases hx : x ∈ s; simp [hx, *] }

lemma piecewise_le_piecewise {δ : α → Type*} [Π i, preorder (δ i)] {f g f' g' : Π i, δ i}
  (Hf : f ≤ f') (Hg : g ≤ g') : s.piecewise f g ≤ s.piecewise f' g' :=
s.piecewise_le_piecewise' (λ x _, Hf x) (λ x _, Hg x)

lemma piecewise_mem_Icc_of_mem_of_mem {δ : α → Type*} [Π i, preorder (δ i)] {f f₁ g g₁ : Π i, δ i}
  (hf : f ∈ set.Icc f₁ g₁) (hg : g ∈ set.Icc f₁ g₁) :
  s.piecewise f g ∈ set.Icc f₁ g₁ :=
⟨le_piecewise_of_le_of_le _ hf.1 hg.1, piecewise_le_of_le_of_le _ hf.2 hg.2⟩

lemma piecewise_mem_Icc {δ : α → Type*} [Π i, preorder (δ i)] {f g : Π i, δ i} (h : f ≤ g) :
  s.piecewise f g ∈ set.Icc f g :=
piecewise_mem_Icc_of_mem_of_mem _ (set.left_mem_Icc.2 h) (set.right_mem_Icc.2 h)

lemma piecewise_mem_Icc' {δ : α → Type*} [Π i, preorder (δ i)] {f g : Π i, δ i} (h : g ≤ f) :
  s.piecewise f g ∈ set.Icc g f :=
piecewise_mem_Icc_of_mem_of_mem _ (set.right_mem_Icc.2 h) (set.left_mem_Icc.2 h)

end piecewise

section decidable_pi_exists
variables {s : finset α}

instance decidable_dforall_finset {p : Πa∈s, Prop} [hp : ∀a (h : a ∈ s), decidable (p a h)] :
  decidable (∀a (h : a ∈ s), p a h) :=
multiset.decidable_dforall_multiset

/-- decidable equality for functions whose domain is bounded by finsets -/
instance decidable_eq_pi_finset {β : α → Type*} [h : ∀a, decidable_eq (β a)] :
  decidable_eq (Πa∈s, β a) :=
multiset.decidable_eq_pi_multiset

instance decidable_dexists_finset {p : Πa∈s, Prop} [hp : ∀a (h : a ∈ s), decidable (p a h)] :
  decidable (∃a (h : a ∈ s), p a h) :=
multiset.decidable_dexists_multiset

end decidable_pi_exists

/-! ### filter -/
section filter
variables (p q : α → Prop) [decidable_pred p] [decidable_pred q]

/-- `filter p s` is the set of elements of `s` that satisfy `p`. -/
def filter (s : finset α) : finset α :=
⟨_, nodup_filter p s.2⟩

@[simp] theorem filter_val (s : finset α) : (filter p s).1 = s.1.filter p := rfl

@[simp] theorem filter_subset (s : finset α) : s.filter p ⊆ s := filter_subset _ _

variable {p}

@[simp] theorem mem_filter {s : finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a := mem_filter

theorem filter_ssubset {s : finset α} : s.filter p ⊂ s ↔ ∃ x ∈ s, ¬ p x :=
⟨λ h, let ⟨x, hs, hp⟩ := set.exists_of_ssubset h in ⟨x, hs, mt (λ hp, mem_filter.2 ⟨hs, hp⟩) hp⟩,
  λ ⟨x, hs, hp⟩, ⟨s.filter_subset _, λ h, hp (mem_filter.1 (h hs)).2⟩⟩

variable (p)

theorem filter_filter (s : finset α) : (s.filter p).filter q = s.filter (λa, p a ∧ q a) :=
ext $ assume a, by simp only [mem_filter, and_comm, and.left_comm]

lemma filter_true {s : finset α} [h : decidable_pred (λ _, true)] :
  @finset.filter α (λ _, true) h s = s :=
by ext; simp

@[simp] theorem filter_false {h} (s : finset α) : @filter α (λa, false) h s = ∅ :=
ext $ assume a, by simp only [mem_filter, and_false]; refl

variables {p q}

/-- If all elements of a `finset` satisfy the predicate `p`, `s.filter p` is `s`. -/
@[simp] lemma filter_true_of_mem {s : finset α} (h : ∀ x ∈ s, p x) : s.filter p = s :=
ext $ λ x, ⟨λ h, (mem_filter.1 h).1, λ hx, mem_filter.2 ⟨hx, h x hx⟩⟩

/-- If all elements of a `finset` fail to satisfy the predicate `p`, `s.filter p` is `∅`. -/
lemma filter_false_of_mem {s : finset α} (h : ∀ x ∈ s, ¬ p x) : s.filter p = ∅ :=
eq_empty_of_forall_not_mem (by simpa)

lemma filter_congr {s : finset α} (H : ∀ x ∈ s, p x ↔ q x) : filter p s = filter q s :=
eq_of_veq $ filter_congr H

variables (p q)

lemma filter_empty : filter p ∅ = ∅ := subset_empty.1 $ filter_subset _ _

lemma filter_subset_filter {s t : finset α} (h : s ⊆ t) : s.filter p ⊆ t.filter p :=
assume a ha, mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩

@[simp, norm_cast] lemma coe_filter (s : finset α) : ↑(s.filter p) = ({x ∈ ↑s | p x} : set α) :=
set.ext $ λ _, mem_filter

theorem filter_singleton (a : α) : filter p (singleton a) = if p a then singleton a else ∅ :=
by { classical, ext x, simp, split_ifs with h; by_cases h' : x = a; simp [h, h'] }

variable [decidable_eq α]

theorem filter_union (s₁ s₂ : finset α) : (s₁ ∪ s₂).filter p = s₁.filter p ∪ s₂.filter p :=
ext $ λ _, by simp only [mem_filter, mem_union, or_and_distrib_right]

theorem filter_union_right (s : finset α) : s.filter p ∪ s.filter q = s.filter (λx, p x ∨ q x) :=
ext $ λ x, by simp only [mem_filter, mem_union, and_or_distrib_left.symm]

lemma filter_mem_eq_inter {s t : finset α} [Π i, decidable (i ∈ t)] :
  s.filter (λ i, i ∈ t) = s ∩ t :=
ext $ λ i, by rw [mem_filter, mem_inter]

theorem filter_inter (s t : finset α) : filter p s ∩ t = filter p (s ∩ t) :=
by { ext, simp only [mem_inter, mem_filter, and.right_comm] }

theorem inter_filter (s t : finset α) : s ∩ filter p t = filter p (s ∩ t) :=
by rw [inter_comm, filter_inter, inter_comm]

theorem filter_insert (a : α) (s : finset α) :
  filter p (insert a s) = if p a then insert a (filter p s) else filter p s :=
by { ext x, simp, split_ifs with h; by_cases h' : x = a; simp [h, h'] }

theorem filter_or [decidable_pred (λ a, p a ∨ q a)] (s : finset α) :
  s.filter (λ a, p a ∨ q a) = s.filter p ∪ s.filter q :=
ext $ λ _, by simp only [mem_filter, mem_union, and_or_distrib_left]

theorem filter_and [decidable_pred (λ a, p a ∧ q a)] (s : finset α) :
  s.filter (λ a, p a ∧ q a) = s.filter p ∩ s.filter q :=
ext $ λ _, by simp only [mem_filter, mem_inter, and_comm, and.left_comm, and_self]

theorem filter_not [decidable_pred (λ a, ¬ p a)] (s : finset α) :
  s.filter (λ a, ¬ p a) = s \ s.filter p :=
ext $ by simpa only [mem_filter, mem_sdiff, and_comm, not_and] using λ a, and_congr_right $
  λ h : a ∈ s, (imp_iff_right h).symm.trans imp_not_comm

theorem sdiff_eq_filter (s₁ s₂ : finset α) :
  s₁ \ s₂ = filter (∉ s₂) s₁ := ext $ λ _, by simp only [mem_sdiff, mem_filter]

theorem sdiff_eq_self (s₁ s₂ : finset α) :
  s₁ \ s₂ = s₁ ↔ s₁ ∩ s₂ ⊆ ∅ :=
by { simp [subset.antisymm_iff],
     split; intro h,
     { transitivity' ((s₁ \ s₂) ∩ s₂), mono, simp },
     { calc  s₁ \ s₂
           ⊇ s₁ \ (s₁ ∩ s₂) : by simp [(⊇)]
       ... ⊇ s₁ \ ∅         : by mono using [(⊇)]
       ... ⊇ s₁             : by simp [(⊇)] } }

theorem filter_union_filter_neg_eq [decidable_pred (λ a, ¬ p a)]
  (s : finset α) : s.filter p ∪ s.filter (λa, ¬ p a) = s :=
by simp only [filter_not, union_sdiff_of_subset (filter_subset p s)]

theorem filter_inter_filter_neg_eq (s : finset α) : s.filter p ∩ s.filter (λa, ¬ p a) = ∅ :=
by simp only [filter_not, inter_sdiff_self]

lemma subset_union_elim {s : finset α} {t₁ t₂ : set α} (h : ↑s ⊆ t₁ ∪ t₂) :
  ∃s₁ s₂ : finset α, s₁ ∪ s₂ = s ∧ ↑s₁ ⊆ t₁ ∧ ↑s₂ ⊆ t₂ \ t₁ :=
begin
  classical,
  refine ⟨s.filter (∈ t₁), s.filter (∉ t₁), _, _ , _⟩,
  { simp [filter_union_right, em] },
  { intro x, simp },
  { intro x, simp, intros hx hx₂, refine ⟨or.resolve_left (h hx) hx₂, hx₂⟩ }
end

/- We can simplify an application of filter where the decidability is inferred in "the wrong way" -/
@[simp] lemma filter_congr_decidable {α} (s : finset α) (p : α → Prop) (h : decidable_pred p)
  [decidable_pred p] : @filter α p h s = s.filter p :=
by congr

section classical
open_locale classical
/-- The following instance allows us to write `{x ∈ s | p x}` for `finset.filter p s`.
  Since the former notation requires us to define this for all propositions `p`, and `finset.filter`
  only works for decidable propositions, the notation `{x ∈ s | p x}` is only compatible with
  classical logic because it uses `classical.prop_decidable`.
  We don't want to redo all lemmas of `finset.filter` for `has_sep.sep`, so we make sure that `simp`
  unfolds the notation `{x ∈ s | p x}` to `finset.filter p s`. If `p` happens to be decidable, the
  simp-lemma `finset.filter_congr_decidable` will make sure that `finset.filter` uses the right
  instance for decidability.
-/
noncomputable instance {α : Type*} : has_sep α (finset α) := ⟨λ p x, x.filter p⟩

@[simp] lemma sep_def {α : Type*} (s : finset α) (p : α → Prop) : {x ∈ s | p x} = s.filter p := rfl

end classical

/--
  After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq'` with the equality the other way.
-/
-- This is not a good simp lemma, as it would prevent `finset.mem_filter` from firing
-- on, e.g. `x ∈ s.filter(eq b)`.
lemma filter_eq [decidable_eq β] (s : finset β) (b : β) :
  s.filter (eq b) = ite (b ∈ s) {b} ∅ :=
begin
  split_ifs,
  { ext,
    simp only [mem_filter, mem_singleton],
    exact ⟨λ h, h.2.symm, by { rintro ⟨h⟩, exact ⟨h, rfl⟩, }⟩ },
  { ext,
    simp only [mem_filter, not_and, iff_false, not_mem_empty],
    rintros m ⟨e⟩, exact h m, }
end

/--
  After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq` with the equality the other way.
-/
lemma filter_eq' [decidable_eq β] (s : finset β) (b : β) :
  s.filter (λ a, a = b) = ite (b ∈ s) {b} ∅ :=
trans (filter_congr (λ _ _, ⟨eq.symm, eq.symm⟩)) (filter_eq s b)

lemma filter_ne [decidable_eq β] (s : finset β) (b : β) :
  s.filter (λ a, b ≠ a) = s.erase b :=
by { ext, simp only [mem_filter, mem_erase, ne.def], tauto, }

lemma filter_ne' [decidable_eq β] (s : finset β) (b : β) :
  s.filter (λ a, a ≠ b) = s.erase b :=
trans (filter_congr (λ _ _, ⟨ne.symm, ne.symm⟩)) (filter_ne s b)

end filter

/-! ### range -/
section range
variables {n m l : ℕ}

/-- `range n` is the set of natural numbers less than `n`. -/
def range (n : ℕ) : finset ℕ := ⟨_, nodup_range n⟩

@[simp] theorem range_coe (n : ℕ) : (range n).1 = multiset.range n := rfl

@[simp] theorem mem_range : m ∈ range n ↔ m < n := mem_range

@[simp] theorem range_zero : range 0 = ∅ := rfl

@[simp] theorem range_one : range 1 = {0} := rfl

theorem range_succ : range (succ n) = insert n (range n) :=
eq_of_veq $ (range_succ n).trans $ (ndinsert_of_not_mem not_mem_range_self).symm

theorem range_add_one : range (n + 1) = insert n (range n) :=
range_succ

@[simp] theorem not_mem_range_self : n ∉ range n := not_mem_range_self

@[simp] theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) := multiset.self_mem_range_succ n

@[simp] theorem range_subset {n m} : range n ⊆ range m ↔ n ≤ m := range_subset

theorem range_mono : monotone range := λ _ _, range_subset.2

lemma mem_range_succ_iff {a b : ℕ} : a ∈ finset.range b.succ ↔ a ≤ b :=
finset.mem_range.trans nat.lt_succ_iff

lemma mem_range_le {n x : ℕ} (hx : x ∈ range n) : x ≤ n :=
(mem_range.1 hx).le

lemma mem_range_sub_ne_zero {n x : ℕ} (hx : x ∈ range n) : n - x ≠ 0 :=
ne_of_gt $ nat.sub_pos_of_lt $ mem_range.1 hx

end range

/- useful rules for calculations with quantifiers -/
theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : finset α) ∧ p x) ↔ false :=
by simp only [not_mem_empty, false_and, exists_false]

theorem exists_mem_insert [d : decidable_eq α]
    (a : α) (s : finset α) (p : α → Prop) :
  (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ (∃ x, x ∈ s ∧ p x) :=
by simp only [mem_insert, or_and_distrib_right, exists_or_distrib, exists_eq_left]

theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : finset α) → p x) ↔ true :=
iff_true_intro $ λ _, false.elim

theorem forall_mem_insert [d : decidable_eq α]
    (a : α) (s : finset α) (p : α → Prop) :
  (∀ x, x ∈ insert a s → p x) ↔ p a ∧ (∀ x, x ∈ s → p x) :=
by simp only [mem_insert, or_imp_distrib, forall_and_distrib, forall_eq]

end finset

/-- Equivalence between the set of natural numbers which are `≥ k` and `ℕ`, given by `n → n - k`. -/
def not_mem_range_equiv (k : ℕ) : {n // n ∉ range k} ≃ ℕ :=
{ to_fun := λ i, i.1 - k,
  inv_fun := λ j, ⟨j + k, by simp⟩,
  left_inv :=
  begin
    assume j,
    rw subtype.ext_iff_val,
    apply nat.sub_add_cancel,
    simpa using j.2
  end,
  right_inv := λ j, nat.add_sub_cancel _ _ }

@[simp] lemma coe_not_mem_range_equiv (k : ℕ) :
  (not_mem_range_equiv k : {n // n ∉ range k} → ℕ) = (λ i, i - k) := rfl

@[simp] lemma coe_not_mem_range_equiv_symm (k : ℕ) :
  ((not_mem_range_equiv k).symm : ℕ → {n // n ∉ range k}) = λ j, ⟨j + k, by simp⟩ := rfl

namespace option

/-- Construct an empty or singleton finset from an `option` -/
def to_finset (o : option α) : finset α :=
match o with
| none   := ∅
| some a := {a}
end

@[simp] theorem to_finset_none : none.to_finset = (∅ : finset α) := rfl

@[simp] theorem to_finset_some {a : α} : (some a).to_finset = {a} := rfl

@[simp] theorem mem_to_finset {a : α} {o : option α} : a ∈ o.to_finset ↔ a ∈ o :=
by cases o; simp only [to_finset, finset.mem_singleton, option.mem_def, eq_comm]; refl

end option

/-! ### erase_dup on list and multiset -/

namespace multiset
variable [decidable_eq α]

/-- `to_finset s` removes duplicates from the multiset `s` to produce a finset. -/
def to_finset (s : multiset α) : finset α := ⟨_, nodup_erase_dup s⟩

@[simp] theorem to_finset_val (s : multiset α) : s.to_finset.1 = s.erase_dup := rfl

theorem to_finset_eq {s : multiset α} (n : nodup s) : finset.mk s n = s.to_finset :=
finset.val_inj.1 (erase_dup_eq_self.2 n).symm

@[simp] theorem mem_to_finset {a : α} {s : multiset α} : a ∈ s.to_finset ↔ a ∈ s :=
mem_erase_dup

@[simp] lemma to_finset_zero :
  to_finset (0 : multiset α) = ∅ :=
rfl

@[simp] lemma to_finset_cons (a : α) (s : multiset α) :
  to_finset (a ::ₘ s) = insert a (to_finset s) :=
finset.eq_of_veq erase_dup_cons

@[simp] lemma to_finset_add (s t : multiset α) :
  to_finset (s + t) = to_finset s ∪ to_finset t :=
finset.ext $ by simp

@[simp] lemma to_finset_nsmul (s : multiset α) :
  ∀(n : ℕ) (hn : n ≠ 0), (n • s).to_finset = s.to_finset
| 0     h := by contradiction
| (n+1) h :=
  begin
    by_cases n = 0,
    { rw [h, zero_add, one_nsmul] },
    { rw [add_nsmul, to_finset_add, one_nsmul, to_finset_nsmul n h, finset.union_idempotent] }
  end

@[simp] lemma to_finset_inter (s t : multiset α) :
  to_finset (s ∩ t) = to_finset s ∩ to_finset t :=
finset.ext $ by simp

@[simp] lemma to_finset_union (s t : multiset α) :
  (s ∪ t).to_finset = s.to_finset ∪ t.to_finset :=
by ext; simp

theorem to_finset_eq_empty {m : multiset α} : m.to_finset = ∅ ↔ m = 0 :=
finset.val_inj.symm.trans multiset.erase_dup_eq_zero

@[simp] lemma to_finset_subset (m1 m2 : multiset α) :
  m1.to_finset ⊆ m2.to_finset ↔ m1 ⊆ m2 :=
by simp only [finset.subset_iff, multiset.subset_iff, multiset.mem_to_finset]

end multiset

namespace finset

@[simp] lemma val_to_finset [decidable_eq α] (s : finset α) : s.val.to_finset = s :=
by { ext, rw [multiset.mem_to_finset, ←mem_def] }

end finset

namespace list
variable [decidable_eq α]

/-- `to_finset l` removes duplicates from the list `l` to produce a finset. -/
def to_finset (l : list α) : finset α := multiset.to_finset l

@[simp] theorem to_finset_val (l : list α) : l.to_finset.1 = (l.erase_dup : multiset α) := rfl

theorem to_finset_eq {l : list α} (n : nodup l) : @finset.mk α l n = l.to_finset :=
multiset.to_finset_eq n

@[simp] theorem mem_to_finset {a : α} {l : list α} : a ∈ l.to_finset ↔ a ∈ l :=
mem_erase_dup

@[simp] theorem to_finset_nil : to_finset (@nil α) = ∅ :=
rfl

@[simp] theorem to_finset_cons {a : α} {l : list α} : to_finset (a :: l) = insert a (to_finset l) :=
finset.eq_of_veq $ by by_cases h : a ∈ l; simp [finset.insert_val', multiset.erase_dup_cons, h]

lemma to_finset_surj_on : set.surj_on to_finset {l : list α | l.nodup} set.univ :=
begin
  rintro s -,
  cases s with t hl, induction t using quot.ind with l,
  refine ⟨l, hl, (to_finset_eq hl).symm⟩
end

theorem to_finset_surjective : surjective (to_finset : list α → finset α) :=
by { intro s, rcases to_finset_surj_on (set.mem_univ s) with ⟨l, -, hls⟩, exact ⟨l, hls⟩ }

lemma to_finset_eq_iff_perm_erase_dup {l l' : list α} :
  l.to_finset = l'.to_finset ↔ l.erase_dup ~ l'.erase_dup :=
by simp [finset.ext_iff, perm_ext (nodup_erase_dup _) (nodup_erase_dup _)]

lemma to_finset_eq_of_perm (l l' : list α) (h : l ~ l') :
  l.to_finset = l'.to_finset :=
to_finset_eq_iff_perm_erase_dup.mpr h.erase_dup

@[simp] lemma to_finset_append {l l' : list α} :
  to_finset (l ++ l') = l.to_finset ∪ l'.to_finset :=
begin
  induction l with hd tl hl,
  { simp },
  { simp [hl] }
end

@[simp] lemma to_finset_reverse {l : list α} :
  to_finset l.reverse = l.to_finset :=
to_finset_eq_of_perm _ _ (reverse_perm l)

end list

namespace finset

/-! ### map -/
section map
open function

/-- When `f` is an embedding of `α` in `β` and `s` is a finset in `α`, then `s.map f` is the image
finset in `β`. The embedding condition guarantees that there are no duplicates in the image. -/
def map (f : α ↪ β) (s : finset α) : finset β :=
⟨s.1.map f, nodup_map f.2 s.2⟩

@[simp] theorem map_val (f : α ↪ β) (s : finset α) : (map f s).1 = s.1.map f := rfl

@[simp] theorem map_empty (f : α ↪ β) : (∅ : finset α).map f = ∅ := rfl

variables {f : α ↪ β} {s : finset α}

@[simp] theorem mem_map {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
mem_map.trans $ by simp only [exists_prop]; refl

@[simp] theorem mem_map_equiv {f : α ≃ β} {b : β} :
  b ∈ s.map f.to_embedding ↔ f.symm b ∈ s :=
by { rw mem_map, exact ⟨by { rintro ⟨a, H, rfl⟩, simpa }, λ h, ⟨_, h, by simp⟩⟩ }

theorem mem_map' (f : α ↪ β) {a} {s : finset α} : f a ∈ s.map f ↔ a ∈ s :=
mem_map_of_injective f.2

theorem mem_map_of_mem (f : α ↪ β) {a} {s : finset α} : a ∈ s → f a ∈ s.map f :=
(mem_map' _).2

@[simp, norm_cast] theorem coe_map (f : α ↪ β) (s : finset α) : (s.map f : set β) = f '' s :=
set.ext $ λ x, mem_map.trans set.mem_image_iff_bex.symm

theorem coe_map_subset_range (f : α ↪ β) (s : finset α) : (s.map f : set β) ⊆ set.range f :=
calc ↑(s.map f) = f '' s      : coe_map f s
            ... ⊆ set.range f : set.image_subset_range f ↑s

theorem map_to_finset [decidable_eq α] [decidable_eq β] {s : multiset α} :
  s.to_finset.map f = (s.map f).to_finset :=
ext $ λ _, by simp only [mem_map, multiset.mem_map, exists_prop, multiset.mem_to_finset]

@[simp] theorem map_refl : s.map (embedding.refl _) = s :=
ext $ λ _, by simpa only [mem_map, exists_prop] using exists_eq_right

@[simp] theorem map_cast_heq {α β} (h : α = β) (s : finset α) :
  s.map (equiv.cast h).to_embedding == s :=
by { subst h, simp }

theorem map_map {g : β ↪ γ} : (s.map f).map g = s.map (f.trans g) :=
eq_of_veq $ by simp only [map_val, multiset.map_map]; refl

theorem map_subset_map {s₁ s₂ : finset α} : s₁.map f ⊆ s₂.map f ↔ s₁ ⊆ s₂ :=
⟨λ h x xs, (mem_map' _).1 $ h $ (mem_map' f).2 xs,
 λ h, by simp [subset_def, map_subset_map h]⟩

theorem map_inj {s₁ s₂ : finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂ :=
by simp only [subset.antisymm_iff, map_subset_map]

/-- Associate to an embedding `f` from `α` to `β` the embedding that maps a finset to its image
under `f`. -/
def map_embedding (f : α ↪ β) : finset α ↪ finset β := ⟨map f, λ s₁ s₂, map_inj.1⟩

@[simp] theorem map_embedding_apply : map_embedding f s = map f s := rfl

theorem map_filter {p : β → Prop} [decidable_pred p] :
  (s.map f).filter p = (s.filter (p ∘ f)).map f :=
eq_of_veq (map_filter _ _ _)

theorem map_union [decidable_eq α] [decidable_eq β]
  {f : α ↪ β} (s₁ s₂ : finset α) : (s₁ ∪ s₂).map f = s₁.map f ∪ s₂.map f :=
ext $ λ _, by simp only [mem_map, mem_union, exists_prop, or_and_distrib_right, exists_or_distrib]

theorem map_inter [decidable_eq α] [decidable_eq β]
  {f : α ↪ β} (s₁ s₂ : finset α) : (s₁ ∩ s₂).map f = s₁.map f ∩ s₂.map f :=
ext $ λ b, by simp only [mem_map, mem_inter, exists_prop]; exact
⟨by rintro ⟨a, ⟨m₁, m₂⟩, rfl⟩; exact ⟨⟨a, m₁, rfl⟩, ⟨a, m₂, rfl⟩⟩,
by rintro ⟨⟨a, m₁, e⟩, ⟨a', m₂, rfl⟩⟩; cases f.2 e; exact ⟨_, ⟨m₁, m₂⟩, rfl⟩⟩

@[simp] theorem map_singleton (f : α ↪ β) (a : α) : map f {a} = {f a} :=
ext $ λ _, by simp only [mem_map, mem_singleton, exists_prop, exists_eq_left]; exact eq_comm

@[simp] theorem map_insert [decidable_eq α] [decidable_eq β]
  (f : α ↪ β) (a : α) (s : finset α) :
  (insert a s).map f = insert (f a) (s.map f) :=
by simp only [insert_eq, map_union, map_singleton]

@[simp] theorem map_eq_empty : s.map f = ∅ ↔ s = ∅ :=
⟨λ h, eq_empty_of_forall_not_mem $
 λ a m, ne_empty_of_mem (mem_map_of_mem _ m) h, λ e, e.symm ▸ rfl⟩

lemma attach_map_val {s : finset α} : s.attach.map (embedding.subtype _) = s :=
eq_of_veq $ by rw [map_val, attach_val]; exact attach_map_val _

lemma nonempty.map (h : s.nonempty) (f : α ↪ β) : (s.map f).nonempty :=
let ⟨a, ha⟩ := h in ⟨f a, (mem_map' f).mpr ha⟩

end map

lemma range_add_one' (n : ℕ) :
  range (n + 1) = insert 0 ((range n).map ⟨λi, i + 1, assume i j, nat.succ.inj⟩) :=
by ext (⟨⟩ | ⟨n⟩); simp [nat.succ_eq_add_one, nat.zero_lt_succ n]

/-! ### image -/
section image
variables [decidable_eq β]

/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : finset α) : finset β := (s.1.map f).to_finset

@[simp] theorem image_val (f : α → β) (s : finset α) : (image f s).1 = (s.1.map f).erase_dup := rfl

@[simp] theorem image_empty (f : α → β) : (∅ : finset α).image f = ∅ := rfl

variables {f : α → β} {s : finset α}

@[simp] theorem mem_image {b : β} : b ∈ s.image f ↔ ∃ a ∈ s, f a = b :=
by simp only [mem_def, image_val, mem_erase_dup, multiset.mem_map, exists_prop]

theorem mem_image_of_mem (f : α → β) {a} {s : finset α} (h : a ∈ s) : f a ∈ s.image f :=
mem_image.2 ⟨_, h, rfl⟩

lemma filter_mem_image_eq_image (f : α → β) (s : finset α) (t : finset β) (h : ∀ x ∈ s, f x ∈ t) :
  t.filter (λ y, y ∈ s.image f) = s.image f :=
by { ext, rw [mem_filter, mem_image],
     simp only [and_imp, exists_prop, and_iff_right_iff_imp, exists_imp_distrib],
     rintros x xel rfl, exact h _ xel }

lemma fiber_nonempty_iff_mem_image (f : α → β) (s : finset α) (y : β) :
  (s.filter (λ x, f x = y)).nonempty ↔ y ∈ s.image f :=
by simp [finset.nonempty]

@[simp, norm_cast] lemma coe_image {f : α → β} : ↑(s.image f) = f '' ↑s :=
set.ext $ λ _, mem_image.trans set.mem_image_iff_bex.symm

lemma nonempty.image (h : s.nonempty) (f : α → β) : (s.image f).nonempty :=
let ⟨a, ha⟩ := h in ⟨f a, mem_image_of_mem f ha⟩

@[simp]
lemma nonempty.image_iff (f : α → β) : (s.image f).nonempty ↔ s.nonempty :=
⟨λ ⟨y, hy⟩, let ⟨x, hx, _⟩ := mem_image.mp hy in ⟨x, hx⟩, λ h, h.image f⟩

theorem image_to_finset [decidable_eq α] {s : multiset α} :
  s.to_finset.image f = (s.map f).to_finset :=
ext $ λ _, by simp only [mem_image, multiset.mem_to_finset, exists_prop, multiset.mem_map]

theorem image_val_of_inj_on (H : set.inj_on f s) : (image f s).1 = s.1.map f :=
multiset.erase_dup_eq_self.2 (nodup_map_on H s.2)

@[simp]
theorem image_id [decidable_eq α] : s.image id = s :=
ext $ λ _, by simp only [mem_image, exists_prop, id, exists_eq_right]

theorem image_image [decidable_eq γ] {g : β → γ} : (s.image f).image g = s.image (g ∘ f) :=
eq_of_veq $ by simp only [image_val, erase_dup_map_erase_dup_eq, multiset.map_map]

theorem image_subset_image {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : s₁.image f ⊆ s₂.image f :=
by simp only [subset_def, image_val, subset_erase_dup', erase_dup_subset',
  multiset.map_subset_map h]

theorem image_subset_iff {s : finset α} {t : finset β} {f : α → β} :
  s.image f ⊆ t ↔ ∀ x ∈ s, f x ∈ t :=
calc s.image f ⊆ t ↔ f '' ↑s ⊆ ↑t : by norm_cast
               ... ↔ _ : set.image_subset_iff

theorem image_mono (f : α → β) : monotone (finset.image f) := λ _ _, image_subset_image

theorem coe_image_subset_range : ↑(s.image f) ⊆ set.range f :=
calc ↑(s.image f) = f '' ↑s     : coe_image
              ... ⊆ set.range f : set.image_subset_range f ↑s

theorem image_filter {p : β → Prop} [decidable_pred p] :
  (s.image f).filter p = (s.filter (p ∘ f)).image f :=
ext $ λ b, by simp only [mem_filter, mem_image, exists_prop]; exact
⟨by rintro ⟨⟨x, h1, rfl⟩, h2⟩; exact ⟨x, ⟨h1, h2⟩, rfl⟩,
 by rintro ⟨x, ⟨h1, h2⟩, rfl⟩; exact ⟨⟨x, h1, rfl⟩, h2⟩⟩

theorem image_union [decidable_eq α] {f : α → β} (s₁ s₂ : finset α) :
  (s₁ ∪ s₂).image f = s₁.image f ∪ s₂.image f :=
ext $ λ _, by simp only [mem_image, mem_union, exists_prop, or_and_distrib_right,
  exists_or_distrib]

theorem image_inter [decidable_eq α] (s₁ s₂ : finset α) (hf : ∀x y, f x = f y → x = y) :
  (s₁ ∩ s₂).image f = s₁.image f ∩ s₂.image f :=
ext $ by simp only [mem_image, exists_prop, mem_inter]; exact λ b,
⟨λ ⟨a, ⟨m₁, m₂⟩, e⟩, ⟨⟨a, m₁, e⟩, ⟨a, m₂, e⟩⟩,
 λ ⟨⟨a, m₁, e₁⟩, ⟨a', m₂, e₂⟩⟩, ⟨a, ⟨m₁, hf _ _ (e₂.trans e₁.symm) ▸ m₂⟩, e₁⟩⟩.

@[simp] theorem image_singleton (f : α → β) (a : α) : image f {a} = {f a} :=
ext $ λ x, by simpa only [mem_image, exists_prop, mem_singleton, exists_eq_left] using eq_comm

@[simp] theorem image_insert [decidable_eq α] (f : α → β) (a : α) (s : finset α) :
  (insert a s).image f = insert (f a) (s.image f) :=
by simp only [insert_eq, image_singleton, image_union]

@[simp] theorem image_eq_empty : s.image f = ∅ ↔ s = ∅ :=
⟨λ h, eq_empty_of_forall_not_mem $
 λ a m, ne_empty_of_mem (mem_image_of_mem _ m) h, λ e, e.symm ▸ rfl⟩

lemma mem_range_iff_mem_finset_range_of_mod_eq' [decidable_eq α] {f : ℕ → α} {a : α} {n : ℕ}
  (hn : 0 < n) (h : ∀i, f (i % n) = f i) :
  a ∈ set.range f ↔ a ∈ (finset.range n).image (λi, f i) :=
begin
  split,
  { rintros ⟨i, hi⟩,
    simp only [mem_image, exists_prop, mem_range],
    exact ⟨i % n, nat.mod_lt i hn, (rfl.congr hi).mp (h i)⟩ },
  { rintro h,
    simp only [mem_image, exists_prop, set.mem_range, mem_range] at *,
    rcases h with ⟨i, hi, ha⟩,
    use ⟨i, ha⟩ },
end

lemma mem_range_iff_mem_finset_range_of_mod_eq [decidable_eq α] {f : ℤ → α} {a : α} {n : ℕ}
  (hn : 0 < n) (h : ∀i, f (i % n) = f i) :
  a ∈ set.range f ↔ a ∈ (finset.range n).image (λi, f i) :=
suffices (∃i, f (i % n) = a) ↔ ∃i, i < n ∧ f ↑i = a, by simpa [h],
have hn' : 0 < (n : ℤ), from int.coe_nat_lt.mpr hn,
iff.intro
  (assume ⟨i, hi⟩,
    have 0 ≤ i % ↑n, from int.mod_nonneg _ (ne_of_gt hn'),
    ⟨int.to_nat (i % n),
      by rw [←int.coe_nat_lt, int.to_nat_of_nonneg this]; exact ⟨int.mod_lt_of_pos i hn', hi⟩⟩)
  (assume ⟨i, hi, ha⟩,
    ⟨i, by rw [int.mod_eq_of_lt (int.coe_zero_le _) (int.coe_nat_lt_coe_nat_of_lt hi), ha]⟩)


lemma attach_image_val [decidable_eq α] {s : finset α} : s.attach.image subtype.val = s :=
eq_of_veq $ by rw [image_val, attach_val, multiset.attach_map_val, erase_dup_eq_self]

@[simp] lemma attach_insert [decidable_eq α] {a : α} {s : finset α} :
  attach (insert a s) = insert (⟨a, mem_insert_self a s⟩ : {x // x ∈ insert a s})
    ((attach s).image (λx, ⟨x.1, mem_insert_of_mem x.2⟩)) :=
ext $ λ ⟨x, hx⟩, ⟨or.cases_on (mem_insert.1 hx)
  (λ h : x = a, λ _, mem_insert.2 $ or.inl $ subtype.eq h)
  (λ h : x ∈ s, λ _, mem_insert_of_mem $ mem_image.2 $ ⟨⟨x, h⟩, mem_attach _ _, subtype.eq rfl⟩),
λ _, finset.mem_attach _ _⟩

theorem map_eq_image (f : α ↪ β) (s : finset α) : s.map f = s.image f :=
eq_of_veq $ (multiset.erase_dup_eq_self.2 (s.map f).2).symm

lemma image_const {s : finset α} (h : s.nonempty) (b : β) : s.image (λa, b) = singleton b :=
ext $ assume b', by simp only [mem_image, exists_prop, exists_and_distrib_right,
  h.bex, true_and, mem_singleton, eq_comm]

/--
Because `finset.image` requires a `decidable_eq` instances for the target type,
we can only construct a `functor finset` when working classically.
-/
instance [Π P, decidable P] : functor finset :=
{ map := λ α β f s, s.image f, }

instance [Π P, decidable P] : is_lawful_functor finset :=
{ id_map := λ α x, image_id,
  comp_map := λ α β γ f g s, image_image.symm, }


/-- Given a finset `s` and a predicate `p`, `s.subtype p` is the finset of `subtype p` whose
elements belong to `s`.  -/
protected def subtype {α} (p : α → Prop) [decidable_pred p] (s : finset α) : finset (subtype p) :=
(s.filter p).attach.map ⟨λ x, ⟨x.1, (finset.mem_filter.1 x.2).2⟩,
λ x y H, subtype.eq $ subtype.mk.inj H⟩

@[simp] lemma mem_subtype {p : α → Prop} [decidable_pred p] {s : finset α} :
  ∀{a : subtype p}, a ∈ s.subtype p ↔ (a : α) ∈ s
| ⟨a, ha⟩ := by simp [finset.subtype, ha]

lemma subtype_eq_empty {p : α → Prop} [decidable_pred p] {s : finset α} :
  s.subtype p = ∅ ↔ ∀ x, p x → x ∉ s :=
by simp [ext_iff, subtype.forall, subtype.coe_mk]; refl

/-- `s.subtype p` converts back to `s.filter p` with
`embedding.subtype`. -/
@[simp] lemma subtype_map (p : α → Prop) [decidable_pred p] :
  (s.subtype p).map (embedding.subtype _) = s.filter p :=
begin
  ext x,
  rw mem_map,
  change (∃ a : {x // p x}, ∃ H, (a : α) = x) ↔ _,
  split,
  { rintros ⟨y, hy, hyval⟩,
    rw [mem_subtype, hyval] at hy,
    rw mem_filter,
    use hy,
    rw ← hyval,
    use y.property },
  { intro hx,
    rw mem_filter at hx,
    use ⟨⟨x, hx.2⟩, mem_subtype.2 hx.1, rfl⟩ }
end

/-- If all elements of a `finset` satisfy the predicate `p`,
`s.subtype p` converts back to `s` with `embedding.subtype`. -/
lemma subtype_map_of_mem {p : α → Prop} [decidable_pred p] (h : ∀ x ∈ s, p x) :
  (s.subtype p).map (embedding.subtype _) = s :=
by rw [subtype_map, filter_true_of_mem h]

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, all elements of the result have the property of
the subtype. -/
lemma property_of_mem_map_subtype {p : α → Prop} (s : finset {x // p x}) {a : α}
  (h : a ∈ s.map (embedding.subtype _)) : p a :=
begin
  rcases mem_map.1 h with ⟨x, hx, rfl⟩,
  exact x.2
end

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result does not contain any value that does
not satisfy the property of the subtype. -/
lemma not_mem_map_subtype_of_not_property {p : α → Prop} (s : finset {x // p x})
  {a : α} (h : ¬ p a) : a ∉ (s.map (embedding.subtype _)) :=
mt s.property_of_mem_map_subtype h

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result is a subset of the set giving the
subtype. -/
lemma map_subtype_subset {t : set α} (s : finset t) :
  ↑(s.map (embedding.subtype _)) ⊆ t :=
begin
  intros a ha,
  rw mem_coe at ha,
  convert property_of_mem_map_subtype s ha
end

lemma subset_image_iff {f : α → β}
  {s : finset β} {t : set α} : ↑s ⊆ f '' t ↔ ∃s' : finset α, ↑s' ⊆ t ∧ s'.image f = s :=
begin
  classical,
  split, swap,
  { rintro ⟨s, hs, rfl⟩, rw [coe_image], exact set.image_subset f hs },
  intro h, induction s using finset.induction with a s has ih h,
  { refine ⟨∅, set.empty_subset _, _⟩,
    convert finset.image_empty _ },
  rw [finset.coe_insert, set.insert_subset] at h,
  rcases ih h.2 with ⟨s', hst, hsi⟩,
  rcases h.1 with ⟨x, hxt, rfl⟩,
  refine ⟨insert x s', _, _⟩,
  { rw [finset.coe_insert, set.insert_subset], exact ⟨hxt, hst⟩ },
  rw [finset.image_insert, hsi],
  congr
end

end image
end finset

theorem multiset.to_finset_map [decidable_eq α] [decidable_eq β] (f : α → β) (m : multiset α) :
  (m.map f).to_finset = m.to_finset.image f :=
finset.val_inj.1 (multiset.erase_dup_map_erase_dup_eq _ _).symm

namespace finset

/-! ### card -/
section card

/-- `card s` is the cardinality (number of elements) of `s`. -/
def card (s : finset α) : nat := s.1.card

theorem card_def (s : finset α) : s.card = s.1.card := rfl

@[simp] lemma card_mk {m nodup} : (⟨m, nodup⟩ : finset α).card = m.card := rfl

@[simp] theorem card_empty : card (∅ : finset α) = 0 := rfl

@[simp] theorem card_eq_zero {s : finset α} : card s = 0 ↔ s = ∅ :=
card_eq_zero.trans val_eq_zero

theorem card_pos {s : finset α} : 0 < card s ↔ s.nonempty :=
pos_iff_ne_zero.trans $ (not_congr card_eq_zero).trans nonempty_iff_ne_empty.symm

theorem card_ne_zero_of_mem {s : finset α} {a : α} (h : a ∈ s) : card s ≠ 0 :=
(not_congr card_eq_zero).2 (ne_empty_of_mem h)

theorem card_eq_one {s : finset α} : s.card = 1 ↔ ∃ a, s = {a} :=
by cases s; simp only [multiset.card_eq_one, finset.card, ← val_inj, singleton_val]

theorem card_le_one {s : finset α} : s.card ≤ 1 ↔ ∀ (a ∈ s) (b ∈ s), a = b :=
begin
  rcases s.eq_empty_or_nonempty with rfl|⟨x, hx⟩, { simp },
  refine (nat.succ_le_of_lt (card_pos.2 ⟨x, hx⟩)).le_iff_eq.trans (card_eq_one.trans ⟨_, _⟩),
  { rintro ⟨y, rfl⟩, simp },
  { exact λ h, ⟨x, eq_singleton_iff_unique_mem.2 ⟨hx, λ y hy, h _ hy _ hx⟩⟩ }
end

theorem one_lt_card {s : finset α} : 1 < s.card ↔ ∃ (a ∈ s) (b ∈ s), a ≠ b :=
by { rw ← not_iff_not, push_neg, exact card_le_one }

@[simp] theorem card_insert_of_not_mem [decidable_eq α]
  {a : α} {s : finset α} (h : a ∉ s) : card (insert a s) = card s + 1 :=
by simpa only [card_cons, card, insert_val] using
congr_arg multiset.card (ndinsert_of_not_mem h)

theorem card_insert_of_mem [decidable_eq α] {a : α} {s : finset α}
  (h : a ∈ s) : card (insert a s) = card s := by rw insert_eq_of_mem h

theorem card_insert_le [decidable_eq α] (a : α) (s : finset α) : card (insert a s) ≤ card s + 1 :=
by by_cases a ∈ s; [{rw [insert_eq_of_mem h], apply nat.le_add_right},
rw [card_insert_of_not_mem h]]

@[simp] theorem card_singleton (a : α) : card ({a} : finset α) = 1 := card_singleton _

lemma card_singleton_inter [decidable_eq α] {x : α} {s : finset α} : ({x} ∩ s).card ≤ 1 :=
begin
  cases (finset.decidable_mem x s),
  { simp [finset.singleton_inter_of_not_mem h] },
  { simp [finset.singleton_inter_of_mem h] },
end

theorem card_erase_of_mem [decidable_eq α] {a : α} {s : finset α} :
  a ∈ s → card (erase s a) = pred (card s) := card_erase_of_mem

theorem card_erase_lt_of_mem [decidable_eq α] {a : α} {s : finset α} :
  a ∈ s → card (erase s a) < card s := card_erase_lt_of_mem

theorem card_erase_le [decidable_eq α] {a : α} {s : finset α} :
  card (erase s a) ≤ card s := card_erase_le

theorem pred_card_le_card_erase [decidable_eq α] {a : α} {s : finset α} :
  card s - 1 ≤ card (erase s a) :=
begin
  by_cases h : a ∈ s,
  { rw [card_erase_of_mem h], refl },
  { rw [erase_eq_of_not_mem h], apply nat.sub_le }
end

@[simp] theorem card_range (n : ℕ) : card (range n) = n := card_range n

@[simp] theorem card_attach {s : finset α} : card (attach s) = card s := multiset.card_attach

end card
end finset

theorem multiset.to_finset_card_le [decidable_eq α] (m : multiset α) : m.to_finset.card ≤ m.card :=
card_le_of_le (erase_dup_le _)

lemma list.card_to_finset [decidable_eq α] (l : list α) :
  finset.card l.to_finset = l.erase_dup.length := rfl

theorem list.to_finset_card_le [decidable_eq α] (l : list α) : l.to_finset.card ≤ l.length :=
multiset.to_finset_card_le ⟦l⟧

namespace finset
section card

theorem card_image_le [decidable_eq β] {f : α → β} {s : finset α} : card (image f s) ≤ card s :=
by simpa only [card_map] using (s.1.map f).to_finset_card_le

theorem card_image_of_inj_on [decidable_eq β] {f : α → β} {s : finset α}
  (H : set.inj_on f s) : card (image f s) = card s :=
by simp only [card, image_val_of_inj_on H, card_map]

theorem inj_on_of_card_image_eq [decidable_eq β] {f : α → β} {s : finset α}
  (H : card (image f s) = card s) :
  set.inj_on f s :=
begin
  change (s.1.map f).erase_dup.card = s.1.card at H,
  have : (s.1.map f).erase_dup = s.1.map f,
  { apply multiset.eq_of_le_of_card_le,
    { apply multiset.erase_dup_le },
    rw H,
    simp only [multiset.card_map] },
  rw multiset.erase_dup_eq_self at this,
  apply inj_on_of_nodup_map this,
end

theorem card_image_eq_iff_inj_on [decidable_eq β] {f : α → β} {s : finset α} :
  (s.image f).card = s.card ↔ set.inj_on f s :=
⟨inj_on_of_card_image_eq, card_image_of_inj_on⟩

theorem card_image_of_injective [decidable_eq β] {f : α → β} (s : finset α)
  (H : injective f) : card (image f s) = card s :=
card_image_of_inj_on $ λ x _ y _ h, H h

lemma fiber_card_ne_zero_iff_mem_image (s : finset α) (f : α → β) [decidable_eq β] (y : β) :
  (s.filter (λ x, f x = y)).card ≠ 0 ↔ y ∈ s.image f :=
by { rw [←pos_iff_ne_zero, card_pos, fiber_nonempty_iff_mem_image] }

@[simp] lemma card_map {α β} (f : α ↪ β) {s : finset α} : (s.map f).card = s.card :=
multiset.card_map _ _

@[simp] lemma card_subtype (p : α → Prop) [decidable_pred p] (s : finset α) :
  (s.subtype p).card = (s.filter p).card :=
by simp [finset.subtype]

lemma card_eq_of_bijective {s : finset α} {n : ℕ}
  (f : ∀i, i < n → α)
  (hf : ∀a∈s, ∃i, ∃h:i<n, f i h = a) (hf' : ∀i (h : i < n), f i h ∈ s)
  (f_inj : ∀i j (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) :
  card s = n :=
begin
  classical,
  have : ∀ (a : α), a ∈ s ↔ ∃i (hi : i ∈ range n), f i (mem_range.1 hi) = a,
    from assume a, ⟨assume ha, let ⟨i, hi, eq⟩ := hf a ha in ⟨i, mem_range.2 hi, eq⟩,
      assume ⟨i, hi, eq⟩, eq ▸ hf' i (mem_range.1 hi)⟩,
  have : s = ((range n).attach.image $ λi, f i.1 (mem_range.1 i.2)),
    by simpa only [ext_iff, mem_image, exists_prop, subtype.exists, mem_attach, true_and],
  calc card s = card ((range n).attach.image $ λi, f i.1 (mem_range.1 i.2)) :
      by rw [this]
    ... = card ((range n).attach) :
      card_image_of_injective _ $ assume ⟨i, hi⟩ ⟨j, hj⟩ eq,
        subtype.eq $ f_inj i j (mem_range.1 hi) (mem_range.1 hj) eq
    ... = card (range n) : card_attach
    ... = n : card_range n
end

lemma card_eq_succ [decidable_eq α] {s : finset α} {n : ℕ} :
  s.card = n + 1 ↔ (∃a t, a ∉ t ∧ insert a t = s ∧ card t = n) :=
iff.intro
  (assume eq,
    have 0 < card s, from eq.symm ▸ nat.zero_lt_succ _,
    let ⟨a, has⟩ := card_pos.mp this in
    ⟨a, s.erase a, s.not_mem_erase a, insert_erase has,
      by simp only [eq, card_erase_of_mem has, pred_succ]⟩)
  (assume ⟨a, t, hat, s_eq, n_eq⟩, s_eq ▸ n_eq ▸ card_insert_of_not_mem hat)

theorem card_le_of_subset {s t : finset α} : s ⊆ t → card s ≤ card t :=
multiset.card_le_of_le ∘ val_le_iff.mpr

theorem card_filter_le (s : finset α) (p : α → Prop) [decidable_pred p] :
  card (s.filter p) ≤ card s :=
card_le_of_subset $ filter_subset _ _

theorem eq_of_subset_of_card_le {s t : finset α} (h : s ⊆ t) (h₂ : card t ≤ card s) : s = t :=
eq_of_veq $ multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂

lemma card_lt_card {s t : finset α} (h : s ⊂ t) : s.card < t.card :=
card_lt_of_lt (val_lt_iff.2 h)

lemma card_le_card_of_inj_on {s : finset α} {t : finset β}
  (f : α → β) (hf : ∀a∈s, f a ∈ t) (f_inj : ∀a₁∈s, ∀a₂∈s, f a₁ = f a₂ → a₁ = a₂) :
  card s ≤ card t :=
begin
  classical,
  calc card s = card (s.image f) : by rw [card_image_of_inj_on f_inj]
    ... ≤ card t : card_le_of_subset $ image_subset_iff.2 hf
end

/--
If there are more pigeons than pigeonholes, then there are two pigeons
in the same pigeonhole.
-/
lemma exists_ne_map_eq_of_card_lt_of_maps_to {s : finset α} {t : finset β} (hc : t.card < s.card)
  {f : α → β} (hf : ∀ a ∈ s, f a ∈ t) :
  ∃ (x ∈ s) (y ∈ s), x ≠ y ∧ f x = f y :=
begin
  classical, by_contra hz, push_neg at hz,
  refine hc.not_le (card_le_card_of_inj_on f hf _),
  intros x hx y hy, contrapose, exact hz x hx y hy,
end

lemma le_card_of_inj_on_range {n} {s : finset α}
  (f : ℕ → α) (hf : ∀i<n, f i ∈ s) (f_inj : ∀ (i<n) (j<n), f i = f j → i = j) : n ≤ card s :=
calc n = card (range n) : (card_range n).symm
  ... ≤ card s : card_le_card_of_inj_on f (by simpa only [mem_range]) (by simpa only [mem_range])

/-- Suppose that, given objects defined on all strict subsets of any finset `s`, one knows how to
define an object on `s`. Then one can inductively define an object on all finsets, starting from
the empty set and iterating. This can be used either to define data, or to prove properties. -/
def strong_induction {p : finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s) :
  ∀ (s : finset α), p s
| s := H s (λ t h, have card t < card s, from card_lt_card h, strong_induction t)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf card⟩]}

lemma strong_induction_eq {p : finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s) (s : finset α) :
  strong_induction H s = H s (λ t h, strong_induction H t) :=
by rw strong_induction

/-- Analogue of `strong_induction` with order of arguments swapped. -/
@[elab_as_eliminator] def strong_induction_on {p : finset α → Sort*} :
  ∀ (s : finset α), (∀s, (∀ t ⊂ s, p t) → p s) → p s :=
λ s H, strong_induction H s

lemma strong_induction_on_eq {p : finset α → Sort*} (s : finset α) (H : ∀ s, (∀ t ⊂ s, p t) → p s) :
  s.strong_induction_on H = H s (λ t h, t.strong_induction_on H) :=
by { dunfold strong_induction_on, rw strong_induction }

@[elab_as_eliminator] lemma case_strong_induction_on [decidable_eq α] {p : finset α → Prop}
  (s : finset α) (h₀ : p ∅) (h₁ : ∀ a s, a ∉ s → (∀t ⊆ s, p t) → p (insert a s)) : p s :=
finset.strong_induction_on s $ λ s,
finset.induction_on s (λ _, h₀) $ λ a s n _ ih, h₁ a s n $
λ t ss, ih _ (lt_of_le_of_lt ss (ssubset_insert n) : t < _)

lemma card_congr {s : finset α} {t : finset β} (f : Π a ∈ s, β)
  (h₁ : ∀ a ha, f a ha ∈ t) (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b)
  (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b) : s.card = t.card :=
by haveI := classical.prop_decidable; exact
calc s.card = s.attach.card : card_attach.symm
... = (s.attach.image (λ (a : {a // a ∈ s}), f a.1 a.2)).card :
  eq.symm (card_image_of_injective _ (λ a b h, subtype.eq (h₂ _ _ _ _ h)))
... = t.card : congr_arg card (finset.ext $ λ b,
    ⟨λ h, let ⟨a, ha₁, ha₂⟩ := mem_image.1 h in ha₂ ▸ h₁ _ _,
      λ h, let ⟨a, ha₁, ha₂⟩ := h₃ b h in mem_image.2 ⟨⟨a, ha₁⟩, by simp [ha₂]⟩⟩)

lemma card_union_add_card_inter [decidable_eq α] (s t : finset α) :
  (s ∪ t).card + (s ∩ t).card = s.card + t.card :=
finset.induction_on t (by simp) $ λ a r har, by by_cases a ∈ s; simp *; cc

lemma card_union_le [decidable_eq α] (s t : finset α) :
  (s ∪ t).card ≤ s.card + t.card :=
card_union_add_card_inter s t ▸ le_add_right _ _

lemma card_union_eq [decidable_eq α] {s t : finset α} (h : disjoint s t) :
  (s ∪ t).card = s.card + t.card :=
begin
  rw [← card_union_add_card_inter],
  convert (add_zero _).symm, rw [card_eq_zero], rwa [disjoint_iff] at h
end

lemma surj_on_of_inj_on_of_card_le {s : finset α} {t : finset β}
  (f : Π a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
  (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂)
  (hst : card t ≤ card s) :
  (∀ b ∈ t, ∃ a ha, b = f a ha) :=
by haveI := classical.dec_eq β; exact
λ b hb,
  have h : card (image (λ (a : {a // a ∈ s}), f a a.prop) (attach s)) = card s,
    from @card_attach _ s ▸ card_image_of_injective _
      (λ ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ h, subtype.eq $ hinj _ _ _ _ h),
  have h₁ : image (λ a : {a // a ∈ s}, f a a.prop) s.attach = t :=
  eq_of_subset_of_card_le (λ b h, let ⟨a, ha₁, ha₂⟩ := mem_image.1 h in
    ha₂ ▸ hf _ _) (by simp [hst, h]),
begin
  rw ← h₁ at hb,
  rcases mem_image.1 hb with ⟨a, ha₁, ha₂⟩,
  exact ⟨a, a.2, ha₂.symm⟩,
end

open function

lemma inj_on_of_surj_on_of_card_le {s : finset α} {t : finset β}
  (f : Π a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
  (hsurj : ∀ b ∈ t, ∃ a ha, b = f a ha)
  (hst : card s ≤ card t)
  ⦃a₁ a₂⦄ (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s)
  (ha₁a₂: f a₁ ha₁ = f a₂ ha₂) : a₁ = a₂ :=
by haveI : inhabited {x // x ∈ s} := ⟨⟨a₁, ha₁⟩⟩; exact
let f' : {x // x ∈ s} → {x // x ∈ t} := λ x, ⟨f x.1 x.2, hf x.1 x.2⟩ in
let g : {x // x ∈ t} → {x // x ∈ s} :=
  @surj_inv _ _ f'
    (λ x, let ⟨y, hy₁, hy₂⟩ := hsurj x.1 x.2 in ⟨⟨y, hy₁⟩, subtype.eq hy₂.symm⟩) in
have hg : injective g, from injective_surj_inv _,
have hsg : surjective g, from λ x,
  let ⟨y, hy⟩ := surj_on_of_inj_on_of_card_le (λ (x : {x // x ∈ t}) (hx : x ∈ t.attach), g x)
    (λ x _, show (g x) ∈ s.attach, from mem_attach _ _)
    (λ x y _ _ hxy, hg hxy) (by simpa) x (mem_attach _ _) in
  ⟨y, hy.snd.symm⟩,
have hif : injective f',
  from (left_inverse_of_surjective_of_right_inverse hsg
      (right_inverse_surj_inv _)).injective,
subtype.ext_iff_val.1 (@hif ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ (subtype.eq ha₁a₂))

end card

section bUnion
/-!
### bUnion

This section is about the bounded union of an indexed family `t : α → finset β` of finite sets
over a finite set `s : finset α`.
-/

variables [decidable_eq β] {s : finset α} {t : α → finset β}

/-- `bUnion s t` is the union of `t x` over `x ∈ s`.
(This was formerly `bind` due to the monad structure on types with `decidable_eq`.) -/
protected def bUnion (s : finset α) (t : α → finset β) : finset β :=
(s.1.bind (λ a, (t a).1)).to_finset

@[simp] theorem bUnion_val (s : finset α) (t : α → finset β) :
  (s.bUnion t).1 = (s.1.bind (λ a, (t a).1)).erase_dup := rfl

@[simp] theorem bUnion_empty : finset.bUnion ∅ t = ∅ := rfl

@[simp] theorem mem_bUnion {b : β} : b ∈ s.bUnion t ↔ ∃a∈s, b ∈ t a :=
by simp only [mem_def, bUnion_val, mem_erase_dup, mem_bind, exists_prop]

@[simp] theorem bUnion_insert [decidable_eq α] {a : α} : (insert a s).bUnion t = t a ∪ s.bUnion t :=
ext $ λ x, by simp only [mem_bUnion, exists_prop, mem_union, mem_insert,
  or_and_distrib_right, exists_or_distrib, exists_eq_left]
-- ext $ λ x, by simp [or_and_distrib_right, exists_or_distrib]

theorem bUnion_subset {s' : finset β} : s.bUnion t ⊆ s' ↔ ∀ x ∈ s, t x ⊆ s' :=
by simp only [subset_iff, mem_bUnion]; exact
⟨λ H a ha b hb, H ⟨a, ha, hb⟩, λ H b ⟨a, ha, hb⟩, H a ha hb⟩

@[simp] lemma singleton_bUnion {a : α} : finset.bUnion {a} t = t a :=
begin
  classical,
  rw [← insert_emptyc_eq, bUnion_insert, bUnion_empty, union_empty]
end

theorem bUnion_inter (s : finset α) (f : α → finset β) (t : finset β) :
  s.bUnion f ∩ t = s.bUnion (λ x, f x ∩ t) :=
begin
  ext x,
  simp only [mem_bUnion, mem_inter],
  tauto
end

theorem inter_bUnion (t : finset β) (s : finset α) (f : α → finset β) :
  t ∩ s.bUnion f = s.bUnion (λ x, t ∩ f x) :=
by rw [inter_comm, bUnion_inter]; simp [inter_comm]

theorem image_bUnion [decidable_eq γ] {f : α → β} {s : finset α} {t : β → finset γ} :
  (s.image f).bUnion t = s.bUnion (λa, t (f a)) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s rfl (λ a s has ih,
  by simp only [image_insert, bUnion_insert, ih])

theorem bUnion_image [decidable_eq γ] {s : finset α} {t : α → finset β} {f : β → γ} :
  (s.bUnion t).image f = s.bUnion (λa, (t a).image f) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s rfl (λ a s has ih,
  by simp only [bUnion_insert, image_union, ih])

theorem bind_to_finset [decidable_eq α] (s : multiset α) (t : α → multiset β) :
  (s.bind t).to_finset = s.to_finset.bUnion (λa, (t a).to_finset) :=
ext $ λ x, by simp only [multiset.mem_to_finset, mem_bUnion, multiset.mem_bind, exists_prop]

lemma bUnion_mono {t₁ t₂ : α → finset β} (h : ∀a∈s, t₁ a ⊆ t₂ a) : s.bUnion t₁ ⊆ s.bUnion t₂ :=
have ∀b a, a ∈ s → b ∈ t₁ a → (∃ (a : α), a ∈ s ∧ b ∈ t₂ a),
  from assume b a ha hb, ⟨a, ha, finset.mem_of_subset (h a ha) hb⟩,
by simpa only [subset_iff, mem_bUnion, exists_imp_distrib, and_imp, exists_prop]

lemma bUnion_subset_bUnion_of_subset_left {α : Type*} {s₁ s₂ : finset α}
  (t : α → finset β) (h : s₁ ⊆ s₂) : s₁.bUnion t ⊆ s₂.bUnion t :=
begin
  intro x,
  simp only [and_imp, mem_bUnion, exists_prop],
  exact Exists.imp (λ a ha, ⟨h ha.1, ha.2⟩)
end

lemma subset_bUnion_of_mem {s : finset α}
  (u : α → finset β) {x : α} (xs : x ∈ s) :
  u x ⊆ s.bUnion u :=
begin
  apply subset.trans _ (bUnion_subset_bUnion_of_subset_left u (singleton_subset_iff.2 xs)),
  exact subset_of_eq singleton_bUnion.symm,
end

lemma bUnion_singleton {f : α → β} : s.bUnion (λa, {f a}) = s.image f :=
ext $ λ x, by simp only [mem_bUnion, mem_image, mem_singleton, eq_comm]

@[simp] lemma bUnion_singleton_eq_self [decidable_eq α] :
  s.bUnion (singleton : α → finset α) = s :=
by { rw bUnion_singleton, exact image_id }

lemma bUnion_filter_eq_of_maps_to [decidable_eq α] {s : finset α} {t : finset β} {f : α → β}
  (h : ∀ x ∈ s, f x ∈ t) :
  t.bUnion (λa, s.filter $ (λc, f c = a)) = s :=
ext $ λ b, by simpa using h b

lemma image_bUnion_filter_eq [decidable_eq α] (s : finset β) (g : β → α) :
  (s.image g).bUnion (λa, s.filter $ (λc, g c = a)) = s :=
bUnion_filter_eq_of_maps_to (λ x, mem_image_of_mem g)

lemma erase_bUnion (f : α → finset β) (s : finset α) (b : β) :
  (s.bUnion f).erase b = s.bUnion (λ x, (f x).erase b) :=
by { ext, simp only [finset.mem_bUnion, iff_self, exists_and_distrib_left, finset.mem_erase] }

end bUnion

/-! ### prod -/
section prod
variables {s : finset α} {t : finset β}

/-- `product s t` is the set of pairs `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
protected def product (s : finset α) (t : finset β) : finset (α × β) := ⟨_, nodup_product s.2 t.2⟩

@[simp] theorem product_val : (s.product t).1 = s.1.product t.1 := rfl

@[simp] theorem mem_product {p : α × β} : p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t := mem_product

theorem subset_product [decidable_eq α] [decidable_eq β] {s : finset (α × β)} :
  s ⊆ (s.image prod.fst).product (s.image prod.snd) :=
λ p hp, mem_product.2 ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩

theorem product_eq_bUnion [decidable_eq α] [decidable_eq β] (s : finset α) (t : finset β) :
 s.product t = s.bUnion (λa, t.image $ λb, (a, b)) :=
ext $ λ ⟨x, y⟩, by simp only [mem_product, mem_bUnion, mem_image, exists_prop, prod.mk.inj_iff,
  and.left_comm, exists_and_distrib_left, exists_eq_right, exists_eq_left]

@[simp] theorem card_product (s : finset α) (t : finset β) : card (s.product t) = card s * card t :=
multiset.card_product _ _

theorem filter_product (p : α → Prop) (q : β → Prop) [decidable_pred p] [decidable_pred q] :
  (s.product t).filter (λ (x : α × β), p x.1 ∧ q x.2) = (s.filter p).product (t.filter q) :=
by { ext ⟨a, b⟩, simp only [mem_filter, mem_product], finish, }

lemma filter_product_card (s : finset α) (t : finset β)
  (p : α → Prop) (q : β → Prop) [decidable_pred p] [decidable_pred q] :
  ((s.product t).filter (λ (x : α × β), p x.1 ↔ q x.2)).card =
  (s.filter p).card * (t.filter q).card + (s.filter (not ∘ p)).card * (t.filter (not ∘ q)).card :=
begin
  classical,
  rw [← card_product, ← card_product, ← filter_product, ← filter_product, ← card_union_eq],
  { apply congr_arg, ext ⟨a, b⟩, simp only [filter_union_right, mem_filter, mem_product],
    split; intros; finish, },
  { rw disjoint_iff, change _ ∩ _ = ∅, ext ⟨a, b⟩, rw mem_inter, finish, },
end

end prod

/-! ### sigma -/
section sigma
variables {σ : α → Type*} {s : finset α} {t : Πa, finset (σ a)}

/-- `sigma s t` is the set of dependent pairs `⟨a, b⟩` such that `a ∈ s` and `b ∈ t a`. -/
protected def sigma (s : finset α) (t : Πa, finset (σ a)) : finset (Σa, σ a) :=
⟨_, nodup_sigma s.2 (λ a, (t a).2)⟩

@[simp] theorem mem_sigma {p : sigma σ} : p ∈ s.sigma t ↔ p.1 ∈ s ∧ p.2 ∈ t (p.1) := mem_sigma

theorem sigma_mono {s₁ s₂ : finset α} {t₁ t₂ : Πa, finset (σ a)}
  (H1 : s₁ ⊆ s₂) (H2 : ∀a, t₁ a ⊆ t₂ a) : s₁.sigma t₁ ⊆ s₂.sigma t₂ :=
λ ⟨x, sx⟩ H, let ⟨H3, H4⟩ := mem_sigma.1 H in mem_sigma.2 ⟨H1 H3, H2 x H4⟩

theorem sigma_eq_bUnion [decidable_eq (Σ a, σ a)] (s : finset α)
  (t : Πa, finset (σ a)) :
  s.sigma t = s.bUnion (λa, (t a).map $ embedding.sigma_mk a) :=
by { ext ⟨x, y⟩, simp [and.left_comm] }

end sigma

/-! ### disjoint -/
section disjoint
variable [decidable_eq α]

theorem disjoint_left {s t : finset α} : disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t :=
by simp only [_root_.disjoint, inf_eq_inter, le_iff_subset, subset_iff, mem_inter, not_and,
  and_imp]; refl

theorem disjoint_val {s t : finset α} : disjoint s t ↔ s.1.disjoint t.1 :=
disjoint_left

theorem disjoint_iff_inter_eq_empty {s t : finset α} : disjoint s t ↔ s ∩ t = ∅ :=
disjoint_iff

instance decidable_disjoint (U V : finset α) : decidable (disjoint U V) :=
decidable_of_decidable_of_iff (by apply_instance) eq_bot_iff

theorem disjoint_right {s t : finset α} : disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
by rw [disjoint.comm, disjoint_left]

theorem disjoint_iff_ne {s t : finset α} : disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b :=
by simp only [disjoint_left, imp_not_comm, forall_eq']

theorem disjoint_of_subset_left {s t u : finset α} (h : s ⊆ u) (d : disjoint u t) : disjoint s t :=
disjoint_left.2 (λ x m₁, (disjoint_left.1 d) (h m₁))

theorem disjoint_of_subset_right {s t u : finset α} (h : t ⊆ u) (d : disjoint s u) : disjoint s t :=
disjoint_right.2 (λ x m₁, (disjoint_right.1 d) (h m₁))

@[simp] theorem disjoint_empty_left (s : finset α) : disjoint ∅ s := disjoint_bot_left

@[simp] theorem disjoint_empty_right (s : finset α) : disjoint s ∅ := disjoint_bot_right

@[simp] theorem singleton_disjoint {s : finset α} {a : α} : disjoint (singleton a) s ↔ a ∉ s :=
by simp only [disjoint_left, mem_singleton, forall_eq]

@[simp] theorem disjoint_singleton {s : finset α} {a : α} : disjoint s (singleton a) ↔ a ∉ s :=
disjoint.comm.trans singleton_disjoint

@[simp] theorem disjoint_insert_left {a : α} {s t : finset α} :
  disjoint (insert a s) t ↔ a ∉ t ∧ disjoint s t :=
by simp only [disjoint_left, mem_insert, or_imp_distrib, forall_and_distrib, forall_eq]

@[simp] theorem disjoint_insert_right {a : α} {s t : finset α} :
  disjoint s (insert a t) ↔ a ∉ s ∧ disjoint s t :=
disjoint.comm.trans $ by rw [disjoint_insert_left, disjoint.comm]

@[simp] theorem disjoint_union_left {s t u : finset α} :
  disjoint (s ∪ t) u ↔ disjoint s u ∧ disjoint t u :=
by simp only [disjoint_left, mem_union, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_union_right {s t u : finset α} :
  disjoint s (t ∪ u) ↔ disjoint s t ∧ disjoint s u :=
by simp only [disjoint_right, mem_union, or_imp_distrib, forall_and_distrib]

lemma sdiff_disjoint {s t : finset α} : disjoint (t \ s) s :=
disjoint_left.2 $ assume a ha, (mem_sdiff.1 ha).2

lemma disjoint_sdiff {s t : finset α} : disjoint s (t \ s) :=
sdiff_disjoint.symm

lemma disjoint_sdiff_inter (s t : finset α) : disjoint (s \ t) (s ∩ t) :=
disjoint_of_subset_right (inter_subset_right _ _) sdiff_disjoint

lemma sdiff_eq_self_iff_disjoint {s t : finset α} : s \ t = s ↔ disjoint s t :=
by rw [sdiff_eq_self, subset_empty, disjoint_iff_inter_eq_empty]

lemma sdiff_eq_self_of_disjoint {s t : finset α} (h : disjoint s t) : s \ t = s :=
sdiff_eq_self_iff_disjoint.2 h

lemma disjoint_self_iff_empty (s : finset α) : disjoint s s ↔ s = ∅ :=
disjoint_self

lemma disjoint_bUnion_left {ι : Type*}
  (s : finset ι) (f : ι → finset α) (t : finset α) :
  disjoint (s.bUnion f) t ↔ (∀i∈s, disjoint (f i) t) :=
begin
  classical,
  refine s.induction _ _,
  { simp only [forall_mem_empty_iff, bUnion_empty, disjoint_empty_left] },
  { assume i s his ih,
    simp only [disjoint_union_left, bUnion_insert, his, forall_mem_insert, ih] }
end

lemma disjoint_bUnion_right {ι : Type*}
  (s : finset α) (t : finset ι) (f : ι → finset α) :
  disjoint s (t.bUnion f) ↔ (∀i∈t, disjoint s (f i)) :=
by simpa only [disjoint.comm] using disjoint_bUnion_left t f s

@[simp] theorem card_disjoint_union {s t : finset α} (h : disjoint s t) :
  card (s ∪ t) = card s + card t :=
by rw [← card_union_add_card_inter, disjoint_iff_inter_eq_empty.1 h, card_empty, add_zero]

theorem card_sdiff {s t : finset α} (h : s ⊆ t) : card (t \ s) = card t - card s :=
suffices card (t \ s) = card ((t \ s) ∪ s) - card s, by rwa sdiff_union_of_subset h at this,
by rw [card_disjoint_union sdiff_disjoint, nat.add_sub_cancel]

lemma disjoint_filter {s : finset α} {p q : α → Prop} [decidable_pred p] [decidable_pred q] :
    disjoint (s.filter p) (s.filter q) ↔ (∀ x ∈ s, p x → ¬ q x) :=
by split; simp [disjoint_left] {contextual := tt}

lemma disjoint_filter_filter {s t : finset α} {p q : α → Prop} [decidable_pred p]
  [decidable_pred q] :
  (disjoint s t) → disjoint (s.filter p) (t.filter q) :=
disjoint.mono (filter_subset _ _) (filter_subset _ _)

lemma disjoint_iff_disjoint_coe {α : Type*} {a b : finset α} [decidable_eq α] :
  disjoint a b ↔ disjoint (↑a : set α) (↑b : set α) :=
by { rw [finset.disjoint_left, set.disjoint_left], refl }

lemma filter_card_add_filter_neg_card_eq_card {α : Type*} {s : finset α} (p : α → Prop)
  [decidable_pred p] :
  (s.filter p).card + (s.filter (not ∘ p)).card = s.card :=
by { classical, simp [← card_union_eq, filter_union_filter_neg_eq, disjoint_filter], }

end disjoint

section self_prod
variables (s : finset α) [decidable_eq α]

/-- Given a finite set `s`, the diagonal, `s.diag` is the set of pairs of the form `(a, a)` for
`a ∈ s`. -/
def diag := (s.product s).filter (λ (a : α × α), a.fst = a.snd)

/-- Given a finite set `s`, the off-diagonal, `s.off_diag` is the set of pairs `(a, b)` with `a ≠ b`
for `a, b ∈ s`. -/
def off_diag := (s.product s).filter (λ (a : α × α), a.fst ≠ a.snd)

@[simp] lemma mem_diag (x : α × α) : x ∈ s.diag ↔ x.1 ∈ s ∧ x.1 = x.2 :=
by { simp only [diag, mem_filter, mem_product], split; intros; finish, }

@[simp] lemma mem_off_diag (x : α × α) : x ∈ s.off_diag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 :=
by { simp only [off_diag, mem_filter, mem_product], split; intros; finish, }

@[simp] lemma diag_card : (diag s).card = s.card :=
begin
  suffices : diag s = s.image (λ a, (a, a)), { rw this, apply card_image_of_inj_on, finish, },
  ext ⟨a₁, a₂⟩, rw mem_diag, split; intros; finish,
end

@[simp] lemma off_diag_card : (off_diag s).card = s.card * s.card - s.card :=
begin
  suffices : (diag s).card + (off_diag s).card = s.card * s.card,
  { nth_rewrite 2 ← s.diag_card, finish, },
  rw ← card_product,
  apply filter_card_add_filter_neg_card_eq_card,
end

end self_prod

/--
Given a set A and a set B inside it, we can shrink A to any appropriate size, and keep B
inside it.
-/
lemma exists_intermediate_set {A B : finset α} (i : ℕ)
  (h₁ : i + card B ≤ card A) (h₂ : B ⊆ A) :
  ∃ (C : finset α), B ⊆ C ∧ C ⊆ A ∧ card C = i + card B :=
begin
  classical,
  rcases nat.le.dest h₁ with ⟨k, _⟩,
  clear h₁,
  induction k with k ih generalizing A,
  { exact ⟨A, h₂, subset.refl _, h.symm⟩ },
  { have : (A \ B).nonempty,
    { rw [← card_pos, card_sdiff h₂, ← h, nat.add_right_comm,
          nat.add_sub_cancel, nat.add_succ],
      apply nat.succ_pos },
    rcases this with ⟨a, ha⟩,
    have z : i + card B + k = card (erase A a),
    { rw [card_erase_of_mem, ← h, nat.add_succ, nat.pred_succ],
      rw mem_sdiff at ha,
      exact ha.1 },
    rcases ih _ z with ⟨B', hB', B'subA', cards⟩,
    { exact ⟨B', hB', trans B'subA' (erase_subset _ _), cards⟩ },
    { rintros t th,
      apply mem_erase_of_ne_of_mem _ (h₂ th),
      rintro rfl,
      exact not_mem_sdiff_of_mem_right th ha } }
end

/-- We can shrink A to any smaller size. -/
lemma exists_smaller_set (A : finset α) (i : ℕ) (h₁ : i ≤ card A) :
  ∃ (B : finset α), B ⊆ A ∧ card B = i :=
let ⟨B, _, x₁, x₂⟩ := exists_intermediate_set i (by simpa) (empty_subset A) in ⟨B, x₁, x₂⟩

/-- `finset.fin_range k` is the finset `{0, 1, ..., k-1}`, as a `finset (fin k)`. -/
def fin_range (k : ℕ) : finset (fin k) :=
⟨list.fin_range k, list.nodup_fin_range k⟩

@[simp]
lemma fin_range_card {k : ℕ} : (fin_range k).card = k :=
by simp [fin_range]

@[simp]
lemma mem_fin_range {k : ℕ} (m : fin k) : m ∈ fin_range k :=
list.mem_fin_range m

@[simp] lemma coe_fin_range (k : ℕ) : (fin_range k : set (fin k)) = set.univ :=
set.eq_univ_of_forall mem_fin_range

/-- Given a finset `s` of `ℕ` contained in `{0,..., n-1}`, the corresponding finset in `fin n`
is `s.attach_fin h` where `h` is a proof that all elements of `s` are less than `n`. -/
def attach_fin (s : finset ℕ) {n : ℕ} (h : ∀ m ∈ s, m < n) : finset (fin n) :=
⟨s.1.pmap (λ a ha, ⟨a, ha⟩) h, multiset.nodup_pmap (λ _ _ _ _, fin.veq_of_eq) s.2⟩

@[simp] lemma mem_attach_fin {n : ℕ} {s : finset ℕ} (h : ∀ m ∈ s, m < n) {a : fin n} :
  a ∈ s.attach_fin h ↔ (a : ℕ) ∈ s :=
⟨λ h, let ⟨b, hb₁, hb₂⟩ := multiset.mem_pmap.1 h in hb₂ ▸ hb₁,
λ h, multiset.mem_pmap.2 ⟨a, h, fin.eta _ _⟩⟩

@[simp] lemma card_attach_fin {n : ℕ} (s : finset ℕ) (h : ∀ m ∈ s, m < n) :
  (s.attach_fin h).card = s.card := multiset.card_pmap _ _ _

/-! ### choose -/
section choose
variables (p : α → Prop) [decidable_pred p] (l : finset α)

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def choose_x (hp : (∃! a, a ∈ l ∧ p a)) : { a // a ∈ l ∧ p a } :=
multiset.choose_x p l.val hp

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the ambient type. -/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α := choose_x p l hp

lemma choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
(choose_x p l hp).property

lemma choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l := (choose_spec _ _ _).1

lemma choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) := (choose_spec _ _ _).2

end choose

theorem lt_wf {α} : well_founded (@has_lt.lt (finset α) _) :=
have H : subrelation (@has_lt.lt (finset α) _)
    (inv_image (<) card),
  from λ x y hxy, card_lt_card hxy,
subrelation.wf H $ inv_image.wf _ $ nat.lt_wf

end finset

namespace equiv

/-- Given an equivalence `α` to `β`, produce an equivalence between `finset α` and `finset β`. -/
protected def finset_congr (e : α ≃ β) : finset α ≃ finset β :=
{ to_fun := λ s, s.map e.to_embedding,
  inv_fun := λ s, s.map e.symm.to_embedding,
  left_inv := λ s, by simp [finset.map_map],
  right_inv := λ s, by simp [finset.map_map] }

@[simp] lemma finset_congr_apply (e : α ≃ β) (s : finset α) :
  e.finset_congr s = s.map e.to_embedding :=
rfl

@[simp] lemma finset_congr_refl :
  (equiv.refl α).finset_congr = equiv.refl _ :=
by { ext, simp }

@[simp] lemma finset_congr_symm (e : α ≃ β) :
  e.finset_congr.symm = e.symm.finset_congr :=
rfl

@[simp] lemma finset_congr_trans (e : α ≃ β) (e' : β ≃ γ) :
  e.finset_congr.trans (e'.finset_congr) = (e.trans e').finset_congr :=
by { ext, simp [-finset.mem_map, -equiv.trans_to_embedding] }

end equiv

namespace list
variable [decidable_eq α]

theorem to_finset_card_of_nodup {l : list α} (h : l.nodup) : l.to_finset.card = l.length :=
congr_arg card $ (@multiset.erase_dup_eq_self α _ l).2 h

end list

namespace multiset
variable [decidable_eq α]

theorem to_finset_card_of_nodup {l : multiset α} (h : l.nodup) : l.to_finset.card = l.card :=
congr_arg card $ (@multiset.erase_dup_eq_self α _ l).2 h

lemma disjoint_to_finset (m1 m2 : multiset α) :
  _root_.disjoint m1.to_finset m2.to_finset ↔ m1.disjoint m2 :=
begin
  rw finset.disjoint_iff_ne,
  split,
  { intro h,
    intros a ha1 ha2,
    rw ← multiset.mem_to_finset at ha1 ha2,
    exact h _ ha1 _ ha2 rfl },
  { rintros h a ha b hb rfl,
    rw multiset.mem_to_finset at ha hb,
    exact h ha hb }
end

end multiset
