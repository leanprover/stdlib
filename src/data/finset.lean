/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import data.multiset
import tactic.monotonicity
import tactic.apply

/-!
# Finite sets
-/

open multiset subtype nat

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

/- membership -/

instance : has_mem α (finset α) := ⟨λ a s, a ∈ s.1⟩

theorem mem_def {a : α} {s : finset α} : a ∈ s ↔ a ∈ s.1 := iff.rfl

@[simp] theorem mem_mk {a : α} {s nd} : a ∈ @finset.mk α s nd ↔ a ∈ s := iff.rfl

instance decidable_mem [h : decidable_eq α] (a : α) (s : finset α) : decidable (a ∈ s) :=
multiset.decidable_mem _ _

/-! ### set coercion -/

/-- Convert a finset to a set in the natural way. -/
instance : has_lift (finset α) (set α) := ⟨λ s, {x | x ∈ s}⟩

@[simp, norm_cast] lemma mem_coe {a : α} {s : finset α} : a ∈ (↑s : set α) ↔ a ∈ s := iff.rfl

@[simp] lemma set_of_mem {α} {s : finset α} : {a | a ∈ s} = ↑s := rfl

@[simp] lemma coe_mem {s : finset α} (x : (↑s : set α)) : ↑x ∈ s := x.2

@[simp] lemma mk_coe {s : finset α} (x : (↑s : set α)) {h} :
  (⟨↑x, h⟩ : (↑s : set α)) = x :=
by { apply subtype.eq, refl, }

instance decidable_mem' [decidable_eq α] (a : α) (s : finset α) :
  decidable (a ∈ (↑s : set α)) := s.decidable_mem _

/-! ### extensionality -/
theorem ext_iff {s₁ s₂ : finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
val_inj.symm.trans $ nodup_ext s₁.2 s₂.2

@[ext]
theorem ext {s₁ s₂ : finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
ext_iff.2

@[simp, norm_cast] theorem coe_inj {s₁ s₂ : finset α} : (↑s₁ : set α) = ↑s₂ ↔ s₁ = s₂ :=
set.ext_iff.trans ext_iff.symm

lemma coe_injective {α} : function.injective (coe : finset α → set α) :=
λ s t, coe_inj.1

/-!
### Partial order with bottom element structure
-/

instance : order_bot (finset α) :=
{ le := λ s t, ∀ ⦃a⦄, a ∈ s → a ∈ t,
  bot := ⟨0, nodup_zero⟩,
  bot_le := λ _, zero_subset _,
  .. partial_order.lift (coe : finset α → set α) coe_injective }

@[simp, norm_cast] lemma coe_subset {s t : finset α} : (↑s : set α) ⊆ ↑t ↔ s ≤ t := iff.rfl

@[simp, norm_cast] lemma coe_ssubset {s t : finset α} : (↑s : set α) ⊂ ↑t ↔ s < t := iff.rfl

@[simp] lemma val_subset_iff {s t : finset α} : s.1 ⊆ t.1 ↔ s ≤ t := iff.rfl

@[simp] lemma val_le_iff {s t : finset α} : s.1 ≤ t.1 ↔ s ≤ t := le_iff_subset s.2

@[simp] lemma val_lt_iff {s t : finset α} : s.1 < t.1 ↔ s < t :=
lt_iff_lt_of_le_iff_le' val_le_iff val_le_iff

theorem mem_of_le {s t : finset α} {a : α} : s ≤ t → a ∈ s → a ∈ t := mem_of_subset

theorem le_def {s t : finset α} : s ≤ t ↔ ∀ ⦃x⦄, x ∈ s → x ∈ t := iff.rfl

theorem lt_iff_of_le {s t : finset α} (h : s ≤ t) : s < t ↔ ∃ x ∈ t, x ∉ s :=
set.ssubset_iff_of_subset h

/-! ### Nonempty -/

/-- The property `s.nonempty` expresses the fact that the finset `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def nonempty (s : finset α) : Prop := ∃ x:α, x ∈ s

@[norm_cast] lemma coe_nonempty {s : finset α} : (↑s:set α).nonempty ↔ s.nonempty := iff.rfl

lemma nonempty.coe {s : finset α} (h : s.nonempty) : (↑s:set α).nonempty := h

lemma nonempty.bex {s : finset α} (h : s.nonempty) : ∃ x:α, x ∈ s := h

lemma nonempty.mono {s t : finset α} (hst : s ≤ t) (hs : s.nonempty) : t.nonempty :=
set.nonempty.mono hst hs

/-!
### empty set, denoted by `⊥`
-/

instance : inhabited (finset α) := ⟨⊥⟩

@[simp, norm_cast] lemma coe_bot : (↑(⊥ : finset α) : set α)  = ∅ := rfl

@[simp] lemma bot_val : (⊥ : finset α).1 = 0 := rfl

@[simp] theorem not_mem_bot (a : α) : a ∉ (⊥ : finset α) := id

@[simp] theorem ne_bot_of_mem {a : α} {s : finset α} (h : a ∈ s) : s ≠ ⊥ :=
λ e, not_mem_bot a $ e ▸ h

theorem nonempty.ne_bot {s : finset α} (h : s.nonempty) : s ≠ ⊥ :=
exists.elim h $ λ a, ne_bot_of_mem

theorem eq_bot_of_forall_not_mem {s : finset α} (H : ∀x, x ∉ s) : s = ⊥ :=
eq_of_veq (eq_zero_of_forall_not_mem H)

lemma eq_bot_iff_forall_not_mem {s : finset α} : s = ⊥ ↔ ∀ x, x ∉ s :=
⟨by rintro rfl x; exact id, λ h, eq_bot_of_forall_not_mem h⟩

@[simp] theorem val_eq_zero {s : finset α} : s.1 = 0 ↔ s = ⊥ := @val_inj _ s ⊥

theorem nonempty_of_ne_bot {s : finset α} (h : s ≠ ⊥) : s.nonempty :=
exists_mem_of_ne_zero (mt val_eq_zero.1 h)

theorem nonempty_iff_ne_bot {s : finset α} : s.nonempty ↔ s ≠ ⊥ :=
⟨nonempty.ne_bot, nonempty_of_ne_bot⟩

theorem eq_bot_or_nonempty (s : finset α) : s = ⊥ ∨ s.nonempty :=
classical.by_cases or.inl (λ h, or.inr (nonempty_of_ne_bot h))

/-! ### singleton -/
/--
`{a} : finset a` is the set `{a}` containing `a` and nothing else.

This differs from `insert a ∅` in that it does not require a `decidable_eq` instance for `α`.
-/
instance : has_singleton α (finset α) := ⟨λ a, ⟨{a}, nodup_singleton a⟩⟩

@[simp] theorem singleton_val (a : α) : ({a} : finset α).1 = a :: 0 := rfl

@[simp] theorem mem_singleton {a b : α} : b ∈ ({a} : finset α) ↔ b = a := mem_singleton

theorem not_mem_singleton {a b : α} : a ∉ ({b} : finset α) ↔ a ≠ b := not_congr mem_singleton

theorem mem_singleton_self (a : α) : a ∈ ({a} : finset α) := or.inl rfl

theorem singleton_inj {a b : α} : ({a} : finset α) = {b} ↔ a = b :=
⟨λ h, mem_singleton.1 (h ▸ mem_singleton_self _), congr_arg _⟩

theorem singleton_nonempty (a : α) : ({a} : finset α).nonempty := ⟨a, mem_singleton_self a⟩

@[simp] theorem singleton_ne_bot (a : α) : ({a} : finset α) ≠ ⊥ := (singleton_nonempty a).ne_bot

@[simp] lemma coe_singleton (a : α) : ↑({a} : finset α) = ({a} : set α) := by { ext, simp }

lemma eq_singleton_iff_unique_mem {s : finset α} {a : α} :
  s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
begin
  split; intro t,
    rw t,
    refine ⟨finset.mem_singleton_self _, λ _, finset.mem_singleton.1⟩,
  ext, rw finset.mem_singleton,
  refine ⟨t.right _, λ r, r.symm ▸ t.left⟩
end

lemma singleton_iff_unique_mem (s : finset α) : (∃ a, s = {a}) ↔ ∃! a, a ∈ s :=
by simp only [eq_singleton_iff_unique_mem, exists_unique]

lemma singleton_subset_set_iff {s : set α} {a : α} :
  ↑({a} : finset α) ⊆ s ↔ a ∈ s :=
by rw [coe_singleton, set.singleton_subset_iff]

@[simp] lemma singleton_le_iff {s : finset α} {a : α} :
  {a} ≤ s ↔ a ∈ s :=
singleton_subset_set_iff

/-!
### Lattice structure

In this section we define the following structures on `finset α` assuming `[decidable_eq α]`:

* `distrib_lattice`;
* `semilattice_sup_bot`;
* `semilattice_inf_bot`.

-/

section lattice

variable [decidable_eq α]

instance : lattice (finset α) :=
{ sup := λ s t, ⟨s.1.ndunion t.1, s.1.nodup_ndunion t.2⟩,
  sup_le := λ s₁ s₂ t h₁ h₂, val_le_iff.1 $ ndunion_le.2 $ ⟨h₁, val_le_iff.2 h₂⟩,
  le_sup_left := λ s t, subset_ndunion_left s.1 t.1,
  le_sup_right := λ s t, subset_ndunion_right s.1 t.1,
  inf := λ s t, ⟨_, t.1.nodup_ndinter s.2⟩,
  le_inf := λ s t₁ t₂ h₁ h₂, subset_of_le $ le_ndinter.2 ⟨val_le_iff.2 h₁, h₂⟩,
  inf_le_left := λ s t, ndinter_subset_left s.1 t.1,
  inf_le_right := λ s t, ndinter_subset_right _ _,
 .. finset.order_bot }

instance : semilattice_sup_bot (finset α) :=
{ .. finset.lattice, .. finset.order_bot }

instance : semilattice_inf_bot (finset α) :=
{ .. finset.lattice, .. finset.order_bot }

@[simp, norm_cast] lemma coe_sup {s t : finset α} : ↑(s ⊔ t : finset α) = (↑s ∪ ↑t : set α) :=
set.ext $ λ x, mem_ndunion

@[simp] lemma mem_sup {s t : finset α} {a : α} : a ∈ (s ⊔ t) ↔ a ∈ s ∨ a ∈ t := mem_ndunion

theorem mem_sup_left {a : α} {s : finset α} (h : a ∈ s) (t : finset α) : a ∈ s ⊔ t :=
mem_of_le le_sup_left h

theorem mem_sup_right {a : α} (s : finset α) {t : finset α} (h : a ∈ t) : a ∈ s ⊔ t :=
mem_of_le le_sup_right h

theorem not_mem_sup {a : α} {s t : finset α} : a ∉ s ⊔ t ↔ a ∉ s ∧ a ∉ t :=
by rw [mem_sup, not_or_distrib]

lemma sup_val_nd {s t : finset α} : (s ⊔ t).1 = s.1.ndunion t.1 := rfl

@[simp] lemma sup_val {s t : finset α} : (s ⊔ t).1 = s.1 ∪ t.1 := ndunion_eq_union s.2

@[simp, norm_cast] lemma coe_inf {s t : finset α} : ↑(s ⊓ t : finset α) = (↑s ∩ ↑t : set α) :=
set.ext $ λ x, mem_ndinter

@[simp] theorem sup_singleton_of_mem {a : α} {s : finset α} (h : a ∈ s) : s ⊔ {a} = s :=
sup_eq_left.2 $ singleton_le_iff.2 h

@[simp] theorem singleton_sup_of_mem {a : α} {s : finset α} (h : a ∈ s) : {a} ⊔ s = s :=
sup_eq_right.2 $ singleton_le_iff.2 h

@[simp] lemma mem_inf {s t : finset α} {a : α} : a ∈ s ⊓ t ↔ a ∈ s ∧ a ∈ t := mem_ndinter

lemma inf_val_nd {s t : finset α} : (s ⊓ t).1 = s.1.ndinter t.1 := rfl

@[simp] lemma inf_val {s t : finset α} : (s ⊓ t).1 = s.1 ∩ t.1 := ndinter_eq_inter s.2

theorem mem_of_mem_inf_left {a : α} {s t : finset α} (h : a ∈ s ⊓ t) : a ∈ s := (mem_inf.1 h).1

theorem mem_of_mem_inf_right {a : α} {s t : finset α} (h : a ∈ s ⊓ t) : a ∈ t := (mem_inf.1 h).2

theorem mem_inf_of_mem {a : α} {s t : finset α} : a ∈ s → a ∈ t → a ∈ s ⊓ t := and_imp.1 mem_inf.2

instance : distrib_lattice (finset α) :=
{ le_sup_inf := λ s t₁ t₂, coe_subset.1 $ by simp only [coe_sup, coe_inf, set.union_distrib_left],
  .. finset.lattice }

@[simp] theorem singleton_inf_of_mem {a : α} {s : finset α} (H : a ∈ s) : {a} ⊓ s = {a} :=
inf_eq_left.2 $ singleton_le_iff.2 H

@[simp] theorem singleton_inf_of_not_mem {a : α} {s : finset α} (H : a ∉ s) : {a} ⊓ s = ⊥ :=
eq_bot_of_forall_not_mem $ by simp only [mem_inf, mem_singleton]; rintro x ⟨rfl, h⟩; exact H h

@[simp] theorem inf_singleton_of_mem {a : α} {s : finset α} (h : a ∈ s) : s ⊓ {a} = {a} :=
by rw [inf_comm, singleton_inf_of_mem h]

@[simp] theorem inf_singleton_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : s ⊓ {a} = ⊥ :=
by rw [inf_comm, singleton_inf_of_not_mem h]

end lattice

/-! ### insert -/
section decidable_eq
variables [decidable_eq α]

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
instance : has_insert α (finset α) := ⟨λ a s, ⟨_, nodup_ndinsert a s.2⟩⟩

theorem insert_def (a : α) (s : finset α) : insert a s = ⟨_, nodup_ndinsert a s.2⟩ := rfl

@[simp] theorem insert_val (a : α) (s : finset α) : (insert a s).1 = ndinsert a s.1 := rfl

@[simp] theorem mem_insert {a b : α} {s : finset α} : a ∈ insert b s ↔ a = b ∨ a ∈ s := mem_ndinsert

theorem insert_eq (a : α) (s : finset α) : insert a s = {a} ⊔ s := rfl

@[simp, norm_cast] lemma coe_insert (a : α) (s : finset α) :
  ↑(insert a s) = (insert a ↑s : set α) :=
by simp [insert_eq]

@[simp] lemma insert_bot (a : α) : insert a (⊥ : finset α) = {a} := by simp [insert_eq]

theorem insert_val' (a : α) (s : finset α) : (insert a s).1 = erase_dup (a :: s.1) :=
by rw [erase_dup_cons, erase_dup_eq_self]; refl

theorem insert_val_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : (insert a s).1 = a :: s.1 :=
by rw [insert_val, ndinsert_of_not_mem h]

theorem mem_insert_self (a : α) (s : finset α) : a ∈ insert a s := mem_ndinsert_self a s.1
theorem mem_insert_of_mem {a b : α} {s : finset α} (h : a ∈ s) : a ∈ insert b s :=
mem_ndinsert_of_mem h
theorem mem_of_mem_insert_of_ne {a b : α} {s : finset α} (h : b ∈ insert a s) : b ≠ a → b ∈ s :=
(mem_insert.1 h).resolve_left

@[simp] theorem insert_eq_of_mem {a : α} {s : finset α} (h : a ∈ s) : insert a s = s :=
eq_of_veq $ ndinsert_of_mem h

@[simp] theorem insert_singleton_self_eq (a : α) : ({a, a} : finset α) = {a} :=
insert_eq_of_mem $ mem_singleton_self _

theorem insert.comm (a b : α) (s : finset α) : insert a (insert b s) = insert b (insert a s) :=
by simp only [insert_eq, sup_left_comm]

@[simp] theorem insert_idem (a : α) (s : finset α) : insert a (insert a s) = insert a s :=
by simp only [insert_eq, sup_left_idem]

theorem insert_nonempty (a : α) (s : finset α) : (insert a s).nonempty := ⟨a, mem_insert_self a s⟩

@[simp] theorem insert_ne_bot (a : α) (s : finset α) : insert a s ≠ ⊥ :=
(insert_nonempty a s).ne_bot

lemma ne_insert_of_not_mem (s t : finset α) {a : α} (h : a ∉ s) :
  s ≠ insert a t :=
flip mt h $ λ h, h.symm ▸ mem_insert_self a t

theorem insert_le {a : α} {s t : finset α} : insert a s ≤ t ↔ a ∈ t ∧ s ≤ t :=
by simp only [insert_eq, sup_le_iff, singleton_le_iff]

theorem le_insert (a : α) (s : finset α) : s ≤ insert a s := λ b, mem_insert_of_mem

@[mono] theorem insert_mono (a : α) {s t : finset α} (h : s ≤ t) : insert a s ≤ insert a t :=
by simp only [insert_eq, sup_le_sup, h]

lemma lt_iff {s t : finset α} : s < t ↔ (∃a ∉ s, insert a s ≤ t) :=
by simpa only [← coe_insert] using (@set.ssubset_iff_insert α ↑s ↑t)

lemma lt_insert {s : finset α} {a : α} (h : a ∉ s) : s < insert a s :=
lt_iff.mpr ⟨a, h, subset.refl _⟩

@[simp] theorem insert_sup (a : α) (s t : finset α) : insert a s ⊔ t = insert a (s ⊔ t) :=
by simp only [insert_eq, sup_assoc]

@[simp] theorem sup_insert (a : α) (s t : finset α) : s ⊔ insert a t = insert a (s ⊔ t) :=
by simp only [insert_eq, sup_left_comm]

theorem insert_sup_distrib (a : α) (s t : finset α) :
  insert a (s ⊔ t) = insert a s ⊔ insert a t :=
by simp only [insert_sup, sup_insert, insert_idem]

theorem insert_inf_insert (a : α) (s t : finset α) :
  insert a s ⊓ insert a t = insert a (s ⊓ t) :=
by simp only [insert_eq, sup_inf_left]

@[simp] theorem insert_inf_of_mem (s : finset α) {t : finset α} {a : α} (h : a ∈ t) :
  insert a s ⊓ t = insert a (s ⊓ t) :=
by simp only [← insert_inf_insert, insert_eq_of_mem h]

@[simp] theorem inf_insert_of_mem {s : finset α} {a : α} (h : a ∈ s) (t : finset α) :
  s ⊓ insert a t = insert a (s ⊓ t) :=
by rw [inf_comm, insert_inf_of_mem t h, inf_comm]

@[simp] theorem insert_inf_of_not_mem (s : finset α) {t : finset α} {a : α} (h : a ∉ t) :
  insert a s ⊓ t = s ⊓ t :=
by simp [insert_eq, inf_sup_right, h]

@[simp] theorem inf_insert_of_not_mem {s : finset α} {a : α} (h : a ∉ s) (t : finset α) :
  s ⊓ insert a t = s ⊓ t :=
by rw [inf_comm, insert_inf_of_not_mem t h, inf_comm]

/-!
### Induction principle
-/

protected theorem induction {α : Type*} {p : finset α → Prop} [decidable_eq α]
  (h₁ : p ⊥) (h₂ : ∀ ⦃a : α⦄ {s : finset α}, a ∉ s → p s → p (insert a s)) : ∀ s, p s
| ⟨s, nd⟩ := multiset.induction_on s (λ _, h₁) (λ a s IH nd, begin
    cases nodup_cons.1 nd with m nd',
    rw [← (eq_of_veq _ : insert a (finset.mk s _) = ⟨a::s, nd⟩)],
    { exact h₂ (by exact m) (IH nd') },
    { rw [insert_val, ndinsert_of_not_mem m] }
  end) nd

/--
To prove a proposition about an arbitrary `finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α`,
then it holds for the `finset` obtained by inserting a new element.
-/
@[elab_as_eliminator]
protected theorem induction_on {α : Type*} {p : finset α → Prop} [decidable_eq α]
  (s : finset α) (h₁ : p ⊥) (h₂ : ∀ ⦃a : α⦄ {s : finset α}, a ∉ s → p s → p (insert a s)) : p s :=
finset.induction h₁ h₂ s

/-! ### erase -/

/-- `erase s a` is the set `s - {a}`, that is, the elements of `s` which are
  not equal to `a`. -/
def erase (s : finset α) (a : α) : finset α := ⟨_, nodup_erase_of_nodup a s.2⟩

@[simp] theorem erase_val (s : finset α) (a : α) : (erase s a).1 = s.1.erase a := rfl

@[simp] theorem mem_erase {a b : α} {s : finset α} : a ∈ erase s b ↔ a ≠ b ∧ a ∈ s :=
mem_erase_iff_of_nodup s.2

theorem not_mem_erase (a : α) (s : finset α) : a ∉ erase s a := mem_erase_of_nodup s.2

@[simp] theorem erase_bot (a : α) : erase ⊥ a = ⊥ := rfl

theorem ne_of_mem_erase {a b : α} {s : finset α} : b ∈ erase s a → b ≠ a :=
by simp only [mem_erase]; exact and.left

theorem mem_of_mem_erase {a b : α} {s : finset α} : b ∈ erase s a → b ∈ s := mem_of_mem_erase

theorem mem_erase_of_ne_of_mem {a b : α} {s : finset α} : a ≠ b → a ∈ s → a ∈ erase s b :=
by simp only [mem_erase]; exact and.intro

theorem erase_insert {a : α} {s : finset α} (h : a ∉ s) : erase (insert a s) a = s :=
ext $ assume x, by simp only [mem_erase, mem_insert, and_or_distrib_left, not_and_self, false_or];
apply and_iff_right_of_imp; rintro H rfl; exact h H

theorem insert_erase {a : α} {s : finset α} (h : a ∈ s) : insert a (erase s a) = s :=
ext $ assume x, by simp only [mem_insert, mem_erase, or_and_distrib_left, dec_em, true_and];
apply or_iff_right_of_imp; rintro rfl; exact h

@[mono] theorem erase_mono (a : α) {s t : finset α} (h : s ≤ t) : erase s a ≤ erase t a :=
val_le_iff.1 $ erase_le_erase _ $ val_le_iff.2 h

theorem erase_le (a : α) (s : finset α) : erase s a ≤ s := erase_subset _ _

@[simp, norm_cast] lemma coe_erase (a : α) (s : finset α) : ↑(erase s a) = (↑s \ {a} : set α) :=
set.ext $ λ _, mem_erase.trans $ by rw [and_comm, set.mem_diff, set.mem_singleton_iff, mem_coe]

lemma erase_lt {a : α} {s : finset α} (h : a ∈ s) : s.erase a < s :=
calc s.erase a < insert a (s.erase a) : lt_insert $ not_mem_erase _ _
           ... = s                    : insert_erase h

theorem erase_eq_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : erase s a = s :=
eq_of_veq $ erase_of_not_mem h

theorem le_insert_iff {a : α} {s t : finset α} : s ≤ insert a t ↔ erase s a ≤ t :=
by simp only [le_def, or_iff_not_imp_left, mem_erase, mem_insert, and_imp];
exact forall_congr (λ x, forall_swap)

theorem erase_insert_le (a : α) (s : finset α) : erase (insert a s) a ≤ s :=
le_insert_iff.1 $ subset.refl _

theorem insert_erase_le (a : α) (s : finset α) : s ≤ insert a (erase s a) :=
le_insert_iff.2 $ subset.refl _

/-! ### sdiff -/

/-- `s \ t` is the set consisting of the elements of `s` that are not in `t`. -/
instance : has_sdiff (finset α) := ⟨λs₁ s₂, ⟨s₁.1 - s₂.1, nodup_of_le (sub_le_self _ _) s₁.2⟩⟩

@[simp] theorem mem_sdiff {a : α} {s₁ s₂ : finset α} :
  a ∈ s₁ \ s₂ ↔ a ∈ s₁ ∧ a ∉ s₂ := mem_sub_of_nodup s₁.2

@[simp, norm_cast] lemma coe_sdiff (s₁ s₂ : finset α) : ↑(s₁ \ s₂) = (↑s₁ \ ↑s₂ : set α) :=
set.ext $ λ _, mem_sdiff

lemma not_mem_sdiff_of_mem_right {a : α} {s t : finset α} (h : a ∈ t) : a ∉ s \ t :=
by simp only [mem_sdiff, h, not_true, not_false_iff, and_false]

theorem sdiff_sup_of_le {s₁ s₂ : finset α} (h : s₁ ≤ s₂) : (s₂ \ s₁) ⊔ s₁ = s₂ :=
ext $ λ a, by simpa only [mem_sdiff, mem_sup, or_comm,
  or_and_distrib_left, dec_em, and_true] using or_iff_right_of_imp (@h a)

theorem sup_sdiff_of_le {s₁ s₂ : finset α} (h : s₁ ≤ s₂) : s₁ ⊔ (s₂ \ s₁) = s₂ :=
sup_comm.trans (sdiff_sup_of_le h)

theorem inf_sdiff (s t u : finset α) : s ⊓ (t \ u) = s ⊓ t \ u :=
by { ext x, simp [and_assoc] }

theorem sdiff_disjoint (s t : finset α) : disjoint (s \ t) t :=
λ x, by simp [mem_inf, mem_sdiff]

theorem disjoint_sdiff (s t : finset α) : disjoint t (s \ t) :=
(sdiff_disjoint s t).symm

@[simp] theorem inf_sdiff_self (s₁ s₂ : finset α) : s₁ ⊓ (s₂ \ s₁) = ⊥ :=
(disjoint_sdiff s₂ s₁).eq_bot

@[simp] theorem sdiff_inf_self (s₁ s₂ : finset α) : (s₂ \ s₁) ⊓ s₁ = ⊥ :=
(sdiff_disjoint s₂ s₁).eq_bot

@[simp] theorem sdiff_self (s₁ : finset α) : s₁ \ s₁ = ⊥ :=
by ext; simp

theorem sdiff_inf_distrib_right (s₁ s₂ s₃ : finset α) : s₁ \ (s₂ ⊓ s₃) = (s₁ \ s₂) ⊔ (s₁ \ s₃) :=
by ext; simp only [and_or_distrib_left, mem_sup, classical.not_and_distrib, mem_sdiff, mem_inf]

@[simp] theorem sdiff_inf_self_left (s₁ s₂ : finset α) : s₁ \ (s₁ ⊓ s₂) = s₁ \ s₂ :=
by simp only [sdiff_inf_distrib_right, sdiff_self, bot_sup_eq]

@[simp] theorem sdiff_inf_self_right (s₁ s₂ : finset α) : s₁ \ (s₂ ⊓ s₁) = s₁ \ s₂ :=
by simp only [sdiff_inf_distrib_right, sdiff_self, sup_bot_eq]

@[simp] theorem sdiff_bot {s₁ : finset α} : s₁ \ ⊥ = s₁ :=
ext (by simp)

@[mono] theorem sdiff_mono {s₁ s₂ t₁ t₂ : finset α} (h₁ : t₁ ≤ t₂) (h₂ : s₂ ≤ s₁) :
  t₁ \ s₁ ≤ t₂ \ s₂ :=
by simpa only [le_def, mem_sdiff, and_imp] using λ a m₁ m₂, and.intro (h₁ m₁) (mt (@h₂ _) m₂)

@[simp] theorem sdiff_le_self (s t : finset α) : s \ t ≤ s :=
by exact_mod_cast set.diff_subset (↑s : set α) ↑t

@[simp] theorem sup_sdiff_self (s t : finset α) : s ⊔ (t \ s) = s ⊔ t :=
by exact_mod_cast @set.union_diff_self α ↑s ↑t

@[simp] theorem sdiff_sup_self (s t : finset α) : (s \ t) ⊔ t = s ⊔ t :=
by exact_mod_cast @set.diff_union_self α ↑s ↑t

lemma sup_sdiff_symm (s t : finset α) : s ⊔ (t \ s) = t ⊔ (s \ t) :=
by rw [sup_sdiff_self, sup_sdiff_self, sup_comm]

lemma sdiff_sup_inf (s t : finset α) : (s \ t) ⊔ (s ⊓ t) = s :=
by { simp only [ext_iff, mem_sup, mem_sdiff, mem_inf], tauto }

@[simp] lemma sdiff_idem (s t : finset α) : s \ t \ t = s \ t :=
by { simp only [ext_iff, mem_sdiff], tauto }

lemma sdiff_eq_bot_iff_le {s t : finset α} : s \ t = ⊥ ↔ s ≤ t :=
by { rw [le_def, ext_iff], simp }

@[simp] lemma bot_sdiff (s : finset α) : ⊥ \ s = ⊥ :=
bot_unique $ sdiff_le_self _ _

lemma insert_sdiff_of_not_mem (s : finset α) {t : finset α} {x : α} (h : x ∉ t) :
  (insert x s) \ t = insert x (s \ t) :=
begin
  rw [← coe_inj, coe_insert, coe_sdiff, coe_sdiff, coe_insert],
  exact set.insert_diff_of_not_mem ↑s h
end

lemma insert_sdiff_of_mem (s : finset α) {t : finset α} {x : α} (h : x ∈ t) :
  (insert x s) \ t = s \ t :=
begin
  rw [← coe_inj, coe_sdiff, coe_sdiff, coe_insert],
  exact set.insert_diff_of_mem ↑s h
end

lemma sup_sdiff_distrib (s₁ s₂ t : finset α) : (s₁ ⊔ s₂) \ t = s₁ \ t ⊔ s₂ \ t :=
by { simp only [ext_iff, mem_sdiff, mem_sup], tauto }

lemma sdiff_sup_distrib (s t₁ t₂ : finset α) : s \ (t₁ ⊔ t₂) = (s \ t₁) ⊓ (s \ t₂) :=
by { simp only [ext_iff, mem_sup, mem_sdiff, mem_inf], tauto }

lemma sdiff_singleton_eq_erase (a : α) (s : finset α) : s \ {a} = erase s a :=
by { ext, rw [mem_erase, mem_sdiff, mem_singleton], tauto }

lemma sdiff_sdiff_self_left (s t : finset α) : s \ (s \ t) = s ⊓ t :=
by { simp only [ext_iff, mem_sdiff, mem_inf], tauto }

lemma inter_eq_inter_of_sdiff_eq_sdiff {s t₁ t₂ : finset α} : s \ t₁ = s \ t₂ → s ⊓ t₁ = s ⊓ t₂ :=
by { simp only [ext_iff, mem_sdiff, mem_inf], intros b c, replace b := b c, split; tauto }

end decidable_eq

/-! ### attach -/

/-- `attach s` takes the elements of `s` and forms a new set of elements of the
  subtype `{x // x ∈ s}`. -/
def attach (s : finset α) : finset {x // x ∈ s} := ⟨attach s.1, nodup_attach.2 s.2⟩

@[simp] theorem attach_val (s : finset α) : s.attach.1 = s.1.attach := rfl

@[simp] theorem mem_attach (s : finset α) : ∀ x, x ∈ s.attach := mem_attach _

@[simp] theorem attach_bot : attach (⊥ : finset α) = ⊥ := rfl

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

@[simp] lemma piecewise_bot [∀i : α, decidable (i ∈ (⊥ : finset α))] : piecewise ⊥ f g = g :=
by { ext i, simp [piecewise] }

variable [∀j, decidable (j ∈ s)]

@[norm_cast] lemma piecewise_coe [∀j, decidable (j ∈ (↑s : set α))] :
  (↑s : set α).piecewise f g = s.piecewise f g :=
by { ext, congr }

@[simp, priority 980]
lemma piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i :=
by simp [piecewise, hi]

@[simp, priority 980]
lemma piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i :=
by simp [piecewise, hi]

@[simp, priority 990]
lemma piecewise_insert_of_ne [decidable_eq α] {i j : α} [∀i, decidable (i ∈ insert j s)]
  (h : i ≠ j) : (insert j s).piecewise f g i = s.piecewise f g i :=
by simp [piecewise, h]

lemma piecewise_insert [decidable_eq α] (j : α) [∀i, decidable (i ∈ insert j s)] :
  (insert j s).piecewise f g = function.update (s.piecewise f g) j (f j) :=
begin
  classical,
  rw [← piecewise_coe, ← piecewise_coe, ← set.piecewise_insert, ← coe_insert j s],
  congr
end

lemma update_eq_piecewise {β : Type*} [decidable_eq α] (f : α → β) (i : α) (v : β) :
  function.update f i v = piecewise (singleton i) (λj, v) f :=
begin
  ext j,
  by_cases h : j = i,
  { rw [h], simp },
  { simp [h] }
end

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
variables {p q : α → Prop} [decidable_pred p] [decidable_pred q]

/-- `filter p s` is the set of elements of `s` that satisfy `p`. -/
def filter (p : α → Prop) [decidable_pred p] (s : finset α) : finset α :=
⟨_, nodup_filter p s.2⟩

@[simp] theorem filter_val (s : finset α) : (filter p s).1 = s.1.filter p := rfl

@[simp] theorem mem_filter {s : finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a := mem_filter

@[simp] theorem filter_le (s : finset α) : s.filter p ≤ s := filter_subset _

theorem filter_lt {s : finset α} : s.filter p < s ↔ ∃ x ∈ s, ¬ p x :=
⟨λ h, let ⟨x, hs, hp⟩ := set.exists_of_ssubset h in ⟨x, hs, mt (λ hp, mem_filter.2 ⟨hs, hp⟩) hp⟩,
  λ ⟨x, hs, hp⟩, ⟨s.filter_le, λ h, hp (mem_filter.1 (h hs)).2⟩⟩

theorem filter_filter (s : finset α) :
  (s.filter p).filter q = s.filter (λa, p a ∧ q a) :=
ext $ assume a, by simp only [mem_filter, and_comm, and.left_comm]

@[simp] lemma filter_true {s : finset α} [h : decidable_pred (λ _, true)] :
  @finset.filter α (λ _, true) h s = s :=
by ext; simp

@[simp] theorem filter_false {h} (s : finset α) : @filter α (λa, false) h s = ⊥ :=
ext $ assume a, by simp only [mem_filter, and_false]; refl

lemma filter_congr {s : finset α} (H : ∀ x ∈ s, p x ↔ q x) : filter p s = filter q s :=
eq_of_veq $ filter_congr H

lemma filter_bot : filter p ⊥ = ⊥ := bot_unique $ filter_le _

@[mono] lemma filter_mono {s t : finset α} (h : s ≤ t) : s.filter p ≤ t.filter p :=
assume a ha, mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩

@[simp] lemma coe_filter (s : finset α) : ↑(s.filter p) = ({x ∈ ↑s | p x} : set α) :=
set.ext $ λ _, mem_filter

theorem filter_singleton (a : α) : filter p {a} = if p a then {a} else ⊥ :=
by { classical, ext x, simp, split_ifs with h; by_cases h' : x = a; simp [h, h'] }

variable [decidable_eq α]

theorem filter_sup (s₁ s₂ : finset α) :
  (s₁ ⊔ s₂).filter p = s₁.filter p ⊔ s₂.filter p :=
ext $ λ _, by simp only [mem_filter, mem_sup, or_and_distrib_right]

theorem filter_sup_right (p q : α → Prop) [decidable_pred p] [decidable_pred q]
  [decidable_pred (λ a, p a ∨ q a)](s : finset α) :
  s.filter p ⊔ s.filter q = s.filter (λx, p x ∨ q x) :=
ext $ λ x, by simp only [mem_filter, mem_sup, and_or_distrib_left.symm]

lemma filter_mem_eq_inf {s t : finset α} : s.filter (λ i, i ∈ t) = s ⊓ t :=
ext $ λ i, by rw [mem_filter, mem_inf]

theorem filter_inf {s t : finset α} : filter p s ⊓ t = filter p (s ⊓ t) :=
by { ext, simp only [mem_inf, mem_filter, and.right_comm] }

theorem inf_filter {s t : finset α} : s ⊓ filter p t = filter p (s ⊓ t) :=
by rw [inf_comm, filter_inf, inf_comm]

theorem filter_insert (a : α) (s : finset α) :
  filter p (insert a s) = if p a then insert a (filter p s) else (filter p s) :=
by { ext x, simp, split_ifs with h; by_cases h' : x = a; simp [h, h'] }

theorem filter_or [decidable_pred (λ a, p a ∨ q a)] (s : finset α) :
  s.filter (λ a, p a ∨ q a) = s.filter p ⊔ s.filter q :=
(filter_sup_right _ _ _).symm

theorem filter_and [decidable_pred (λ a, p a ∧ q a)] (s : finset α) :
  s.filter (λ a, p a ∧ q a) = s.filter p ⊓ s.filter q :=
ext $ λ _, by simp only [mem_filter, mem_inf, and_comm, and.left_comm, and_self]

theorem filter_not [decidable_pred (λ a, ¬ p a)] (s : finset α) :
  s.filter (λ a, ¬ p a) = s \ s.filter p :=
ext $ by simpa only [mem_filter, mem_sdiff, and_comm, not_and] using λ a, and_congr_right $
  λ h : a ∈ s, (imp_iff_right h).symm.trans imp_not_comm

theorem sdiff_eq_filter (s₁ s₂ : finset α) :
  s₁ \ s₂ = filter (∉ s₂) s₁ := ext $ λ _, by simp only [mem_sdiff, mem_filter]

theorem sdiff_eq_self {s₁ s₂ : finset α} :
  s₁ \ s₂ = s₁ ↔ disjoint s₁ s₂ :=
begin
  simp only [_root_.disjoint, ext_iff, mem_sdiff, le_def, mem_inf, not_mem_bot],
  refine forall_congr (λ a, _),
  tauto
end

theorem filter_sup_filter_neg_eq [decidable_pred (λ a, ¬ p a)]
  (s : finset α) : s.filter p ⊔ s.filter (λa, ¬ p a) = s :=
by simp only [filter_not, sup_sdiff_of_le (filter_le s)]

theorem filter_inf_filter_neg_eq (s : finset α) : s.filter p ⊓ s.filter (λa, ¬ p a) = ⊥ :=
by simp only [filter_not, inf_sdiff_self]

lemma le_sup_elim {s : finset α} {t₁ t₂ : set α} (h : ↑s ⊆ t₁ ∪ t₂) :
  ∃s₁ s₂ : finset α, s₁ ⊔ s₂ = s ∧ ↑s₁ ⊆ t₁ ∧ ↑s₂ ⊆ t₂ \ t₁ :=
begin
  classical,
  refine ⟨s.filter (∈ t₁), s.filter (∉ t₁), _, _ , _⟩,
  { simp [filter_sup_right, classical.or_not] },
  { intro x, simp },
  { intro x, simp, intros hx hx₂, refine ⟨or.resolve_left (h hx) hx₂, hx₂⟩ }
end

/- We can simplify an application of filter where the decidability is inferred in "the wrong way" -/
@[simp] lemma filter_congr_decidable {α} (s : finset α) (p : α → Prop) (h : decidable_pred p)
  [decidable_pred p] : @filter α p h s = s.filter p :=
by congr

section classical
open_locale classical
/-- The following instance allows us to write `{ x ∈ s | p x }` for `finset.filter s p`.
  Since the former notation requires us to define this for all propositions `p`, and `finset.filter`
  only works for decidable propositions, the notation `{ x ∈ s | p x }` is only compatible with
  classical logic because it uses `classical.prop_decidable`.
  We don't want to redo all lemmas of `finset.filter` for `has_sep.sep`, so we make sure that `simp`
  unfolds the notation `{ x ∈ s | p x }` to `finset.filter s p`. If `p` happens to be decidable, the
  simp-lemma `filter_congr_decidable` will make sure that `finset.filter` uses the right instance
  for decidability.
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
  s.filter(eq b) = ite (b ∈ s) {b} ⊥ :=
begin
  split_ifs,
  { ext,
    simp only [mem_filter, mem_singleton],
    exact ⟨λ h, h.2.symm, by { rintro ⟨h⟩, exact ⟨h, rfl⟩, }⟩ },
  { ext,
    simp only [mem_filter, not_and, iff_false, not_mem_bot],
    rintros m ⟨e⟩, exact h m, }
end

/--
  After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq` with the equality the other way.
-/
lemma filter_eq' [decidable_eq β] (s : finset β) (b : β) :
  s.filter (λ a, a = b) = ite (b ∈ s) {b} ⊥ :=
trans (filter_congr (λ _ _, ⟨eq.symm, eq.symm⟩)) (filter_eq s b)

lemma filter_ne [decidable_eq β] (s : finset β) (b : β) :
  s.filter (λ a, b ≠ a) = s.erase b :=
by { ext, simp only [mem_filter, mem_erase, ne.def], cc, }

lemma filter_ne' [decidable_eq β] (s : finset β) (b : β) :
  s.filter (λ a, a ≠ b) = s.erase b :=
trans (filter_congr (λ _ _, ⟨ne.symm, ne.symm⟩)) (filter_ne s b)

end filter

/-! ### range -/
section range
variables {n m l : ℕ}

/-- `range n` is the set of natural numbers less than `n`. -/
def range (n : ℕ) : finset ℕ := ⟨_, nodup_range n⟩

@[simp] theorem range_val (n : ℕ) : (range n).1 = multiset.range n := rfl

@[simp] theorem mem_range : m ∈ range n ↔ m < n := mem_range

@[simp] theorem range_zero : range 0 = ⊥ := rfl

@[simp] theorem range_one : range 1 = {0} := rfl

theorem range_succ : range (succ n) = insert n (range n) :=
eq_of_veq $ (range_succ n).trans $ (ndinsert_of_not_mem not_mem_range_self).symm

theorem range_add_one : range (n + 1) = insert n (range n) :=
range_succ

@[simp] theorem not_mem_range_self : n ∉ range n := not_mem_range_self

@[simp] theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) := multiset.self_mem_range_succ n

@[simp] theorem range_le {n m} : range n ≤ range m ↔ n ≤ m := range_subset

theorem range_mono : monotone range := λ _ _, range_subset.2

end range

/- useful rules for calculations with quantifiers -/
theorem exists_mem_bot_iff (p : α → Prop) : (∃ x, x ∈ (⊥ : finset α) ∧ p x) ↔ false :=
by simp only [not_mem_bot, false_and, exists_false]

theorem exists_mem_insert [d : decidable_eq α]
    (a : α) (s : finset α) (p : α → Prop) :
  (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ (∃ x, x ∈ s ∧ p x) :=
by simp only [mem_insert, or_and_distrib_right, exists_or_distrib, exists_eq_left]

theorem forall_mem_bot_iff (p : α → Prop) : (∀ x, x ∈ (⊥ : finset α) → p x) ↔ true :=
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
    rw subtype.ext,
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
| none   := ⊥
| some a := {a}
end

@[simp] theorem to_finset_none : none.to_finset = (⊥ : finset α) := rfl

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

@[simp] lemma to_finset_zero : to_finset (0 : multiset α) = ⊥ := rfl

@[simp] lemma to_finset_cons (a : α) (s : multiset α) :
  to_finset (a :: s) = insert a (to_finset s) :=
finset.eq_of_veq erase_dup_cons

@[simp] lemma to_finset_add (s t : multiset α) :
  to_finset (s + t) = to_finset s ⊔ to_finset t :=
finset.ext $ by simp

@[simp] lemma to_finset_nsmul (s : multiset α) :
  ∀(n : ℕ) (hn : n ≠ 0), (n •ℕ s).to_finset = s.to_finset
| 0     h := by contradiction
| (n+1) h :=
  begin
    by_cases n = 0,
    { rw [h, zero_add, one_nsmul] },
    { rw [add_nsmul, to_finset_add, one_nsmul, to_finset_nsmul n h, sup_idem] }
  end

@[simp] lemma to_finset_inter (s t : multiset α) :
  to_finset (s ∩ t) = to_finset s ⊓ to_finset t :=
finset.ext $ by simp

theorem to_finset_eq_bot {m : multiset α} : m.to_finset = ⊥ ↔ m = 0 :=
finset.val_inj.symm.trans multiset.erase_dup_eq_zero

end multiset

namespace list
variable [decidable_eq α]

/-- `to_finset l` removes duplicates from the list `l` to produce a finset. -/
def to_finset (l : list α) : finset α := multiset.to_finset l

@[simp] theorem to_finset_val (l : list α) : l.to_finset.1 = (l.erase_dup : multiset α) := rfl

theorem to_finset_eq {l : list α} (n : nodup l) : @finset.mk α l n = l.to_finset :=
multiset.to_finset_eq n

@[simp] theorem mem_to_finset {a : α} {l : list α} : a ∈ l.to_finset ↔ a ∈ l :=
mem_erase_dup

@[simp] theorem to_finset_nil : to_finset (@nil α) = ⊥ := rfl

@[simp] theorem to_finset_cons {a : α} {l : list α} : to_finset (a :: l) = insert a (to_finset l) :=
finset.eq_of_veq $ by by_cases h : a ∈ l; simp [finset.insert_val', multiset.erase_dup_cons, h]

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

@[simp] theorem map_bot (f : α ↪ β) : (⊥ : finset α).map f = ⊥ := rfl

variables {f : α ↪ β} {s : finset α}

@[simp] theorem mem_map {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
mem_map.trans $ by simp only [exists_prop]; refl

theorem mem_map' (f : α ↪ β) {a} {s : finset α} : f a ∈ s.map f ↔ a ∈ s :=
mem_map_of_inj f.2

theorem mem_map_of_mem (f : α ↪ β) {a} {s : finset α} : a ∈ s → f a ∈ s.map f :=
(mem_map' _).2

@[simp] theorem coe_map (f : α ↪ β) (s : finset α) : (↑(s.map f) : set β) = f '' ↑s :=
set.ext $ λ x, mem_map.trans set.mem_image_iff_bex.symm

theorem coe_map_subset_range (f : α ↪ β) (s : finset α) : (↑(s.map f) : set β) ⊆ set.range f :=
calc ↑(s.map f) = f '' ↑s     : coe_map f s
            ... ⊆ set.range f : set.image_subset_range f ↑s

theorem map_to_finset [decidable_eq α] [decidable_eq β] {s : multiset α} :
  s.to_finset.map f = (s.map f).to_finset :=
ext $ λ _, by simp only [mem_map, multiset.mem_map, exists_prop, multiset.mem_to_finset]

@[simp] theorem map_refl : s.map (embedding.refl _) = s :=
ext $ λ _, by simpa only [mem_map, exists_prop] using exists_eq_right

theorem map_map {g : β ↪ γ} : (s.map f).map g = s.map (f.trans g) :=
eq_of_veq $ by simp only [map_val, multiset.map_map]; refl

theorem map_subset_map {s₁ s₂ : finset α} : s₁.map f ≤ s₂.map f ↔ s₁ ≤ s₂ :=
⟨λ h x xs, (mem_map' _).1 $ h $ (mem_map' f).2 xs,
 λ h, by simp [← val_subset_iff, map_subset_map h]⟩

theorem map_inj {s₁ s₂ : finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂ :=
by simp only [le_antisymm_iff, map_subset_map]

/-- Associate to an embedding `f` from `α` to `β` the embedding that maps a finset to its image
under `f`. -/
def map_embedding (f : α ↪ β) : finset α ↪ finset β := ⟨map f, λ s₁ s₂, map_inj.1⟩

@[simp] theorem map_embedding_apply : map_embedding f s = map f s := rfl

theorem map_filter {p : β → Prop} [decidable_pred p] :
  (s.map f).filter p = (s.filter (p ∘ f)).map f :=
ext $ λ b, by simp only [mem_filter, mem_map, exists_prop, and_assoc]; exact
⟨by rintro ⟨⟨x, h1, rfl⟩, h2⟩; exact ⟨x, h1, h2, rfl⟩,
by rintro ⟨x, h1, h2, rfl⟩; exact ⟨⟨x, h1, rfl⟩, h2⟩⟩

theorem map_sup [decidable_eq α] [decidable_eq β]
  {f : α ↪ β} (s₁ s₂ : finset α) : (s₁ ⊔ s₂).map f = s₁.map f ⊔ s₂.map f :=
ext $ λ _, by simp only [mem_map, mem_sup, exists_prop, or_and_distrib_right, exists_or_distrib]

theorem map_inter [decidable_eq α] [decidable_eq β]
  {f : α ↪ β} (s₁ s₂ : finset α) : (s₁ ⊓ s₂).map f = s₁.map f ⊓ s₂.map f :=
ext $ λ b, by simp only [mem_map, mem_inf, exists_prop]; exact
⟨by rintro ⟨a, ⟨m₁, m₂⟩, rfl⟩; exact ⟨⟨a, m₁, rfl⟩, ⟨a, m₂, rfl⟩⟩,
by rintro ⟨⟨a, m₁, e⟩, ⟨a', m₂, rfl⟩⟩; cases f.2 e; exact ⟨_, ⟨m₁, m₂⟩, rfl⟩⟩

@[simp] theorem map_singleton (f : α ↪ β) (a : α) : map f {a} = {f a} :=
ext $ λ _, by simp only [mem_map, mem_singleton, exists_prop, exists_eq_left]; exact eq_comm

@[simp] theorem map_insert [decidable_eq α] [decidable_eq β]
  (f : α ↪ β) (a : α) (s : finset α) :
  (insert a s).map f = insert (f a) (s.map f) :=
by simp only [insert_eq, map_sup, map_singleton]

@[simp] theorem map_eq_bot : s.map f = ⊥ ↔ s = ⊥ :=
⟨λ h, eq_bot_of_forall_not_mem $
 λ a m, ne_bot_of_mem (mem_map_of_mem _ m) h, λ e, e.symm ▸ rfl⟩

lemma attach_map_val {s : finset α} : s.attach.map (embedding.subtype _) = s :=
eq_of_veq $ by rw [map_val, attach_val]; exact attach_map_val _

end map

lemma range_add_one' (n : ℕ) :
  range (n + 1) = insert 0 ((range n).map ⟨λi, i + 1, assume i j, nat.succ_inj⟩) :=
by ext (⟨⟩ | ⟨n⟩); simp [nat.succ_eq_add_one, nat.zero_lt_succ n]

/-! ### image -/
section image
variables [decidable_eq β]

/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : finset α) : finset β := (s.1.map f).to_finset

@[simp] theorem image_val (f : α → β) (s : finset α) : (image f s).1 = (s.1.map f).erase_dup := rfl

@[simp] theorem image_bot (f : α → β) : (⊥ : finset α).image f = ⊥ := rfl

variables {f : α → β} {s : finset α}

@[simp] theorem mem_image {b : β} : b ∈ s.image f ↔ ∃ a ∈ s, f a = b :=
by simp only [mem_def, image_val, mem_erase_dup, multiset.mem_map, exists_prop]

theorem mem_image_of_mem (f : α → β) {a} {s : finset α} (h : a ∈ s) : f a ∈ s.image f :=
mem_image.2 ⟨_, h, rfl⟩

@[simp] lemma coe_image {f : α → β} : ↑(s.image f) = f '' ↑s :=
set.ext $ λ _, mem_image.trans set.mem_image_iff_bex.symm

lemma nonempty.image (h : s.nonempty) (f : α → β) : (s.image f).nonempty :=
let ⟨a, ha⟩ := h in ⟨f a, mem_image_of_mem f ha⟩

theorem image_to_finset [decidable_eq α] {s : multiset α} :
  s.to_finset.image f = (s.map f).to_finset :=
ext $ λ _, by simp only [mem_image, multiset.mem_to_finset, exists_prop, multiset.mem_map]

theorem image_val_of_inj_on (H : ∀x∈s, ∀y∈s, f x = f y → x = y) : (image f s).1 = s.1.map f :=
multiset.erase_dup_eq_self.2 (nodup_map_on H s.2)

theorem image_id [decidable_eq α] : s.image id = s :=
ext $ λ _, by simp only [mem_image, exists_prop, id, exists_eq_right]

theorem image_image [decidable_eq γ] {g : β → γ} : (s.image f).image g = s.image (g ∘ f) :=
eq_of_veq $ by simp only [image_val, erase_dup_map_erase_dup_eq, multiset.map_map]

@[mono] theorem image_le_image {s₁ s₂ : finset α} (h : s₁ ≤ s₂) : s₁.image f ≤ s₂.image f :=
by simp only [← val_subset_iff, image_val, subset_erase_dup', erase_dup_subset',
  multiset.map_subset_map h]

theorem image_mono (f : α → β) : monotone (finset.image f) := λ _ _, image_le_image

theorem coe_image_subset_range : ↑(s.image f) ⊆ set.range f :=
calc ↑(s.image f) = f '' ↑s     : coe_image
              ... ⊆ set.range f : set.image_subset_range f ↑s

theorem image_filter {p : β → Prop} [decidable_pred p] :
  (s.image f).filter p = (s.filter (p ∘ f)).image f :=
ext $ λ b, by simp only [mem_filter, mem_image, exists_prop]; exact
⟨by rintro ⟨⟨x, h1, rfl⟩, h2⟩; exact ⟨x, ⟨h1, h2⟩, rfl⟩,
 by rintro ⟨x, ⟨h1, h2⟩, rfl⟩; exact ⟨⟨x, h1, rfl⟩, h2⟩⟩

theorem image_sup [decidable_eq α] {f : α → β} (s₁ s₂ : finset α) :
  (s₁ ⊔ s₂).image f = s₁.image f ⊔ s₂.image f :=
ext $ λ _, by simp only [mem_image, mem_sup, exists_prop, or_and_distrib_right, exists_or_distrib]

theorem image_inf [decidable_eq α] (s₁ s₂ : finset α) (hf : function.injective f) :
  (s₁ ⊓ s₂).image f = s₁.image f ⊓ s₂.image f :=
coe_inj.1 $ by simp [set.image_inter hf]

@[simp] theorem image_singleton (f : α → β) (a : α) : image f {a} = {f a} := by simp [← coe_inj]

@[simp] theorem image_insert [decidable_eq α] (f : α → β) (a : α) (s : finset α) :
  (insert a s).image f = insert (f a) (s.image f) :=
by simp only [insert_eq, image_singleton, image_sup]

@[simp] theorem image_eq_bot : s.image f = ⊥ ↔ s = ⊥ := by simp [← coe_inj]

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

lemma image_const {s : finset α} (h : s.nonempty) (b : β) : s.image (λa, b) = {b} :=
by simp [← coe_inj, h.coe.image_const]

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
  ∀{a : subtype p}, a ∈ s.subtype p ↔ a.val ∈ s
| ⟨a, ha⟩ := by simp [finset.subtype, ha]

lemma subset_image_iff {f : α → β}
  {s : finset β} {t : set α} : ↑s ⊆ f '' t ↔ ∃s' : finset α, ↑s' ⊆ t ∧ s'.image f = s :=
begin
  classical,
  split, swap,
  { rintro ⟨s, hs, rfl⟩, rw [coe_image], exact set.image_subset f hs },
  intro h, induction s using finset.induction with a s has ih h,
  { refine ⟨⊥, set.empty_subset _, _⟩,
    convert finset.image_bot _ },
  rw [finset.coe_insert, set.insert_subset] at h,
  rcases ih h.2 with ⟨s', hst, hsi⟩,
  rcases h.1 with ⟨x, hxt, rfl⟩,
  refine ⟨insert x s', _, _⟩,
  { rw [finset.coe_insert, set.insert_subset], exact ⟨hxt, hst⟩ },
  rw [finset.image_insert, hsi],
  congr
end

end image

/-! ### card -/
section card

/-- `card s` is the cardinality (number of elements) of `s`. -/
def card (s : finset α) : nat := s.1.card

theorem card_def (s : finset α) : s.card = s.1.card := rfl

@[simp] theorem card_bot : card (⊥ : finset α) = 0 := rfl

@[simp] theorem card_eq_zero {s : finset α} : card s = 0 ↔ s = ⊥ :=
card_eq_zero.trans val_eq_zero

theorem card_pos {s : finset α} : 0 < card s ↔ s.nonempty :=
pos_iff_ne_zero.trans $ (not_congr card_eq_zero).trans nonempty_iff_ne_bot.symm

theorem card_ne_zero_of_mem {s : finset α} {a : α} (h : a ∈ s) : card s ≠ 0 :=
(not_congr card_eq_zero).2 (ne_bot_of_mem h)

theorem card_eq_one {s : finset α} : s.card = 1 ↔ ∃ a, s = {a} :=
by cases s; simp only [multiset.card_eq_one, finset.card, ← val_inj, singleton_val]

@[simp] theorem card_insert_of_not_mem [decidable_eq α]
  {a : α} {s : finset α} (h : a ∉ s) : card (insert a s) = card s + 1 :=
by simpa only [card_cons, card, insert_val] using
congr_arg multiset.card (ndinsert_of_not_mem h)

theorem card_insert_le [decidable_eq α] (a : α) (s : finset α) : card (insert a s) ≤ card s + 1 :=
by by_cases a ∈ s; [{rw [insert_eq_of_mem h], apply nat.le_add_right},
rw [card_insert_of_not_mem h]]

@[simp] theorem card_singleton (a : α) : card ({a} : finset α) = 1 := card_singleton _

theorem card_erase_of_mem [decidable_eq α] {a : α} {s : finset α} :
  a ∈ s → card (erase s a) = pred (card s) := card_erase_of_mem

theorem card_erase_lt_of_mem [decidable_eq α] {a : α} {s : finset α} :
  a ∈ s → card (erase s a) < card s := card_erase_lt_of_mem

theorem card_erase_le [decidable_eq α] {a : α} {s : finset α} :
  card (erase s a) ≤ card s := card_erase_le

@[simp] theorem card_range (n : ℕ) : card (range n) = n := card_range n

@[simp] theorem card_attach {s : finset α} : card (attach s) = card s := multiset.card_attach

end card
end finset

theorem multiset.to_finset_card_le [decidable_eq α] (m : multiset α) : m.to_finset.card ≤ m.card :=
card_le_of_le (erase_dup_le _)

theorem list.to_finset_card_le [decidable_eq α] (l : list α) : l.to_finset.card ≤ l.length :=
multiset.to_finset_card_le ⟦l⟧

namespace finset
section card

theorem card_image_le [decidable_eq β] {f : α → β} {s : finset α} : card (image f s) ≤ card s :=
by simpa only [card_map] using (s.1.map f).to_finset_card_le

theorem card_image_of_inj_on [decidable_eq β] {f : α → β} {s : finset α}
  (H : ∀x∈s, ∀y∈s, f x = f y → x = y) : card (image f s) = card s :=
by simp only [card, image_val_of_inj_on H, card_map]

theorem card_image_of_injective [decidable_eq β] {f : α → β} (s : finset α)
  (H : function.injective f) : card (image f s) = card s :=
card_image_of_inj_on $ λ x _ y _ h, H h

@[simp] lemma card_map {α β} (f : α ↪ β) {s : finset α} : (s.map f).card = s.card :=
multiset.card_map _ _

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

@[mono] theorem card_mono {s t : finset α} : s ≤ t → card s ≤ card t :=
multiset.card_le_of_le ∘ val_le_iff.mpr

theorem eq_of_le_of_card_le {s t : finset α} (h : s ≤ t) (h₂ : card t ≤ card s) : s = t :=
eq_of_veq $ multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂

lemma card_lt_card {s t : finset α} (h : s < t) : s.card < t.card :=
card_lt_of_lt (val_lt_iff.2 h)

lemma card_le_card_of_inj_on {s : finset α} {t : finset β}
  (f : α → β) (hf : ∀a∈s, f a ∈ t) (f_inj : ∀a₁∈s, ∀a₂∈s, f a₁ = f a₂ → a₁ = a₂) :
  card s ≤ card t :=
begin
  classical,
  calc card s = card (s.image f) : by rw [card_image_of_inj_on f_inj]
    ... ≤ card t : card_mono $
      assume x hx, match x, finset.mem_image.1 hx with _, ⟨a, ha, rfl⟩ := hf a ha end
end

lemma card_le_of_inj_on {n} {s : finset α}
  (f : ℕ → α) (hf : ∀i<n, f i ∈ s) (f_inj : ∀i j, i<n → j<n → f i = f j → i = j) : n ≤ card s :=
calc n = card (range n) : (card_range n).symm
  ... ≤ card s : card_le_card_of_inj_on f
    (by simpa only [mem_range])
    (by simp only [mem_range]; exact assume a₁ h₁ a₂ h₂, f_inj a₁ a₂ h₁ h₂)

/-- Suppose that, given objects defined on all strict subsets of any finset `s`, one knows how to
define an object on `s`. Then one can inductively define an object on all finsets, starting from
the empty set and iterating. This can be used either to define data, or to prove properties. -/
@[elab_as_eliminator] def strong_induction_on {p : finset α → Sort*} :
  ∀ (s : finset α), (∀s, (∀t < s, p t) → p s) → p s
| ⟨s, nd⟩ ih := multiset.strong_induction_on s
  (λ s IH nd, ih ⟨s, nd⟩ (λ ⟨t, nd'⟩ ss, IH t (val_lt_iff.2 ss) nd')) nd

@[elab_as_eliminator] lemma case_strong_induction_on [decidable_eq α] {p : finset α → Prop}
  (s : finset α) (h₀ : p ⊥) (h₁ : ∀ a s, a ∉ s → (∀t ≤ s, p t) → p (insert a s)) : p s :=
finset.strong_induction_on s $ λ s,
finset.induction_on s (λ _, h₀) $ λ a s n _ ih, h₁ a s n $
λ t ss, ih _ (lt_of_le_of_lt ss (lt_insert n) : t < _)

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

lemma card_sup_add_card_inf [decidable_eq α] (s t : finset α) :
  (s ⊔ t).card + (s ⊓ t).card = s.card + t.card :=
finset.induction_on t (by simp) $ λ a r har, by by_cases a ∈ s; simp *; cc

lemma card_sup_le [decidable_eq α] (s t : finset α) :
  (s ⊔ t).card ≤ s.card + t.card :=
card_sup_add_card_inf s t ▸ le_add_right _ _

lemma surj_on_of_inj_on_of_card_le {s : finset α} {t : finset β}
  (f : Π a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
  (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂)
  (hst : card t ≤ card s) :
  (∀ b ∈ t, ∃ a ha, b = f a ha) :=
by haveI := classical.dec_eq β; exact
λ b hb,
  have h : card (image (λ (a : {a // a ∈ s}), f (a.val) a.2) (attach s)) = card s,
    from @card_attach _ s ▸ card_image_of_injective _
      (λ ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ h, subtype.eq $ hinj _ _ _ _ h),
  have h₁ : image (λ a : {a // a ∈ s}, f a.1 a.2) s.attach = t :=
  eq_of_le_of_card_le (λ b h, let ⟨a, ha₁, ha₂⟩ := mem_image.1 h in
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
have hg : injective g, from function.injective_surj_inv _,
have hsg : surjective g, from λ x,
  let ⟨y, hy⟩ := surj_on_of_inj_on_of_card_le (λ (x : {x // x ∈ t}) (hx : x ∈ t.attach), g x)
    (λ x _, show (g x) ∈ s.attach, from mem_attach _ _)
    (λ x y _ _ hxy, hg hxy) (by simpa) x (mem_attach _ _) in
  ⟨y, hy.snd.symm⟩,
have hif : injective f',
  from (left_inverse_of_surjective_of_right_inverse hsg
      (right_inverse_surj_inv _)).injective,
subtype.ext.1 (@hif ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ (subtype.eq ha₁a₂))

end card

/-! ### bind -/
section bind
variables [decidable_eq β] {s : finset α} {t : α → finset β}

/-- `bind s t` is the union of `t x` over `x ∈ s` -/
protected def bind (s : finset α) (t : α → finset β) : finset β :=
(s.1.bind (λ a, (t a).1)).to_finset

@[simp] theorem bind_val (s : finset α) (t : α → finset β) :
  (s.bind t).1 = (s.1.bind (λ a, (t a).1)).erase_dup := rfl

@[simp] theorem bind_bot : finset.bind ⊥ t = ⊥ := rfl

@[simp] theorem mem_bind {b : β} : b ∈ s.bind t ↔ ∃a∈s, b ∈ t a :=
by simp only [mem_def, bind_val, mem_erase_dup, mem_bind, exists_prop]

@[simp, norm_cast] theorem coe_bind : ↑(s.bind t) = ⋃ i ∈ s, (↑(t i) : set β) :=
set.ext $ by simp

@[simp] theorem bind_insert [decidable_eq α] {a : α} : (insert a s).bind t = t a ⊔ s.bind t :=
ext $ λ x, by simp only [mem_bind, exists_prop, mem_sup, mem_insert,
  or_and_distrib_right, exists_or_distrib, exists_eq_left]
-- ext $ λ x, by simp [or_and_distrib_right, exists_or_distrib]

@[simp] lemma singleton_bind {a : α} : finset.bind {a} t = t a :=
ext $ by simp

theorem bind_inf (s : finset α) (f : α → finset β) (t : finset β) :
  s.bind f ⊓ t = s.bind (λ x, f x ⊓ t) :=
ext $ λ x, by simp only [mem_bind, mem_inf, exists_and_distrib_right]

theorem inf_bind (t : finset β) (s : finset α) (f : α → finset β) :
  t ⊓ s.bind f = s.bind (λ x, t ⊓ f x) :=
by rw [inf_comm, bind_inf]; simp [inf_comm]

theorem image_bind [decidable_eq γ] {f : α → β} {s : finset α} {t : β → finset γ} :
  (s.image f).bind t = s.bind (λa, t (f a)) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s rfl (λ a s has ih,
  by simp only [image_insert, bind_insert, ih])

theorem bind_image [decidable_eq γ] {s : finset α} {t : α → finset β} {f : β → γ} :
  (s.bind t).image f = s.bind (λa, (t a).image f) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s rfl (λ a s has ih,
  by simp only [bind_insert, image_sup, ih])

theorem bind_to_finset [decidable_eq α] (s : multiset α) (t : α → multiset β) :
  (s.bind t).to_finset = s.to_finset.bind (λa, (t a).to_finset) :=
ext $ λ x, by simp only [multiset.mem_to_finset, mem_bind, multiset.mem_bind, exists_prop]

@[mono] lemma bind_mono {s₁ s₂ : finset α} {t₁ t₂ : α → finset β} (hs : s₁ ≤ s₂)
  (ht : ∀ a ∈ s₁, t₁ a ≤ t₂ a) :
  s₁.bind t₁ ≤ s₂.bind t₂ :=
λ x hx, let ⟨i, hi, hx⟩ := mem_bind.1 hx in mem_bind.2 ⟨i, hs hi, ht i hi hx⟩

lemma bind_mono_right {t₁ t₂ : α → finset β} (h : ∀a∈s, t₁ a ≤ t₂ a) : s.bind t₁ ≤ s.bind t₂ :=
bind_mono (le_refl _) h

lemma bind_mono_left {s₁ s₂ : finset α} (t : α → finset β) (h : s₁ ≤ s₂) : s₁.bind t ≤ s₂.bind t :=
bind_mono h (λ _ _, le_refl _)

@[simp] lemma bind_singleton {f : α → β} : s.bind (λa, {f a}) = s.image f :=
ext $ λ x, by simp only [mem_bind, mem_image, mem_singleton, eq_comm]

lemma image_bind_filter_eq [decidable_eq α] (s : finset β) (g : β → α) :
  (s.image g).bind (λa, s.filter $ (λc, g c = a)) = s :=
begin
  ext b,
  suffices : (∃ a, a ∈ s ∧ b ∈ s ∧ g b = g a) ↔ b ∈ s, by simpa,
  exact ⟨λ ⟨a, ha, hb, hab⟩, hb, λ hb, ⟨b, hb, hb, rfl⟩⟩
end

end bind

/-! ### prod-/
section prod
variables {s : finset α} {t : finset β}

/-- `product s t` is the set of pairs `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
protected def product (s : finset α) (t : finset β) : finset (α × β) := ⟨_, nodup_product s.2 t.2⟩

@[simp] theorem product_val : (s.product t).1 = s.1.product t.1 := rfl

@[simp] theorem mem_product {p : α × β} : p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t := mem_product

theorem product_eq_bind [decidable_eq α] [decidable_eq β] (s : finset α) (t : finset β) :
 s.product t = s.bind (λa, t.image $ λb, (a, b)) :=
ext $ λ ⟨x, y⟩, by simp only [mem_product, mem_bind, mem_image, exists_prop, prod.mk.inj_iff,
  and.left_comm, exists_and_distrib_left, exists_eq_right, exists_eq_left]

@[simp] theorem card_product (s : finset α) (t : finset β) : card (s.product t) = card s * card t :=
multiset.card_product _ _

end prod

/-! ### sigma -/
section sigma
variables {σ : α → Type*} {s : finset α} {t : Πa, finset (σ a)}

/-- `sigma s t` is the set of dependent pairs `⟨a, b⟩` such that `a ∈ s` and `b ∈ t a`. -/
protected def sigma (s : finset α) (t : Πa, finset (σ a)) : finset (Σa, σ a) :=
⟨_, nodup_sigma s.2 (λ a, (t a).2)⟩

@[simp] theorem mem_sigma {p : sigma σ} : p ∈ s.sigma t ↔ p.1 ∈ s ∧ p.2 ∈ t (p.1) := mem_sigma

@[mono] theorem sigma_mono {s₁ s₂ : finset α} {t₁ t₂ : Πa, finset (σ a)}
  (H1 : s₁ ≤ s₂) (H2 : ∀a, t₁ a ≤ t₂ a) : s₁.sigma t₁ ≤ s₂.sigma t₂ :=
λ ⟨x, sx⟩ H, let ⟨H3, H4⟩ := mem_sigma.1 H in mem_sigma.2 ⟨H1 H3, H2 x H4⟩

theorem sigma_eq_bind [decidable_eq α] [∀a, decidable_eq (σ a)] (s : finset α)
  (t : Πa, finset (σ a)) :
  s.sigma t = s.bind (λa, (t a).image $ λb, ⟨a, b⟩) :=
ext $ λ ⟨x, y⟩, by simp only [mem_sigma, mem_bind, mem_image, exists_prop,
  and.left_comm, exists_and_distrib_left, exists_eq_left, heq_iff_eq, exists_eq_right]

end sigma

/-! ### pi -/
section pi
variables {δ : α → Type*} [decidable_eq α]

/-- Given a finset `s` of `α` and for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `s.pi t` of all functions defined on elements of `s` taking values in `t a` for `a ∈ s`.
Note that the elements of `s.pi t` are only partially defined, on `s`. -/
def pi (s : finset α) (t : Πa, finset (δ a)) : finset (Πa∈s, δ a) :=
⟨s.1.pi (λ a, (t a).1), nodup_pi s.2 (λ a _, (t a).2)⟩

@[simp] lemma pi_val (s : finset α) (t : Πa, finset (δ a)) :
  (s.pi t).1 = s.1.pi (λ a, (t a).1) := rfl

@[simp] lemma mem_pi {s : finset α} {t : Πa, finset (δ a)} {f : Πa∈s, δ a} :
  f ∈ s.pi t ↔ (∀a (h : a ∈ s), f a h ∈ t a) :=
mem_pi _ _ _

/-- The empty dependent product function, defined on the emptyset. The assumption `a ∈ ⊥` is never
satisfied. -/
def pi.empty (β : α → Sort*) (a : α) (h : a ∈ (⊥ : finset α)) : β a :=
multiset.pi.empty β a h

/-- Given a function `f` defined on a finset `s`, define a new function on the finset `s ∪ {a}`,
equal to `f` on `s` and sending `a` to a given value `b`. This function is denoted
`s.pi.cons a b f`. If `a` already belongs to `s`, the new function takes the value `b` at `a`
anyway. -/
def pi.cons (s : finset α) (a : α) (b : δ a) (f : Πa, a ∈ s → δ a) (a' : α) (h : a' ∈ insert a s) :
  δ a' :=
multiset.pi.cons s.1 a b f _ (multiset.mem_cons.2 $ mem_insert.symm.2 h)

@[simp]
lemma pi.cons_same (s : finset α) (a : α) (b : δ a) (f : Πa, a ∈ s → δ a) (h : a ∈ insert a s) :
  pi.cons s a b f a h = b :=
multiset.pi.cons_same _

lemma pi.cons_ne {s : finset α} {a a' : α} {b : δ a} {f : Πa, a ∈ s → δ a} {h : a' ∈ insert a s}
  (ha : a ≠ a') :
  pi.cons s a b f a' h = f a' ((mem_insert.1 h).resolve_left ha.symm) :=
multiset.pi.cons_ne _ _

lemma injective_pi_cons  {a : α} {b : δ a} {s : finset α} (hs : a ∉ s) :
  function.injective (pi.cons s a b) :=
assume e₁ e₂ eq,
@multiset.injective_pi_cons α _ δ a b s.1 hs _ _ $
  funext $ assume e, funext $ assume h,
  have pi.cons s a b e₁ e (by simpa only [mem_cons, mem_insert] using h) =
    pi.cons s a b e₂ e (by simpa only [mem_cons, mem_insert] using h),
  { rw [eq] },
  this

@[simp] lemma pi_bot {t : Πa:α, finset (δ a)} :
  pi (⊥ : finset α) t = singleton (pi.empty δ) := rfl

@[simp] lemma pi_insert [∀a, decidable_eq (δ a)]
  {s : finset α} {t : Πa:α, finset (δ a)} {a : α} (ha : a ∉ s) :
  pi (insert a s) t = (t a).bind (λb, (pi s t).image (pi.cons s a b)) :=
begin
  apply eq_of_veq,
  rw ← multiset.erase_dup_eq_self.2 (pi (insert a s) t).2,
  refine (λ s' (h : s' = a :: s.1), (_ : erase_dup (multiset.pi s' (λ a, (t a).1)) =
    erase_dup ((t a).1.bind $ λ b,
    erase_dup $ (multiset.pi s.1 (λ (a : α), (t a).val)).map $
      λ f a' h', multiset.pi.cons s.1 a b f a' (h ▸ h')))) _ (insert_val_of_not_mem ha),
  subst s', rw pi_cons,
  congr, funext b,
  rw multiset.erase_dup_eq_self.2,
  exact multiset.nodup_map (multiset.injective_pi_cons ha) (pi s t).2,
end

@[mono] lemma pi_mono {s : finset α} (t₁ t₂ : Πa, finset (δ a)) (h : ∀ a ∈ s, t₁ a ≤ t₂ a) :
  s.pi t₁ ≤ s.pi t₂ :=
λ g hg, mem_pi.2 $ λ a ha, h a ha (mem_pi.mp hg a ha)

end pi

/-! ### powerset -/
section powerset

/-- When `s` is a finset, `s.powerset` is the finset of all subsets of `s` (seen as finsets). -/
def powerset (s : finset α) : finset (finset α) :=
⟨s.1.powerset.pmap finset.mk
  (λ t h, nodup_of_le (mem_powerset.1 h) s.2),
 nodup_pmap (λ a ha b hb, congr_arg finset.val)
   (nodup_powerset.2 s.2)⟩

@[simp] theorem mem_powerset {s t : finset α} : s ∈ powerset t ↔ s ≤ t :=
by cases s; simp only [powerset, mem_mk, mem_pmap, mem_powerset, exists_prop, exists_eq_right];
  rw ← val_le_iff

@[simp] theorem bot_mem_powerset (s : finset α) : ⊥ ∈ powerset s :=
mem_powerset.2 bot_le

@[simp] theorem mem_powerset_self (s : finset α) : s ∈ powerset s :=
mem_powerset.2 (le_refl _)

@[simp] lemma powerset_bot : finset.powerset (⊥ : finset α) = {⊥} := rfl

@[simp] theorem powerset_le_iff {s t : finset α} : powerset s ≤ powerset t ↔ s ≤ t :=
⟨λ h, (mem_powerset.1 $ h $ mem_powerset_self _),
 λ st u h, mem_powerset.2 $ subset.trans (mem_powerset.1 h) st⟩

@[mono] theorem powerset_mono {s t : finset α} (h : s ≤ t) : powerset s ≤ powerset t :=
powerset_le_iff.2 h

@[simp] theorem card_powerset (s : finset α) :
  card (powerset s) = 2 ^ card s :=
(card_pmap _ _ _).trans (card_powerset s.1)

lemma not_mem_of_mem_powerset_of_not_mem {s t : finset α} {a : α}
  (ht : t ∈ s.powerset) (h : a ∉ s) : a ∉ t :=
by { apply mt _ h, apply mem_powerset.1 ht }

lemma powerset_insert [decidable_eq α] (s : finset α) (a : α) :
  powerset (insert a s) = s.powerset ⊔ s.powerset.image (insert a) :=
begin
  ext t,
  simp only [exists_prop, mem_powerset, mem_image, mem_sup, le_insert_iff],
  by_cases h : a ∈ t,
  { split,
    { exact λH, or.inr ⟨_, H, insert_erase h⟩ },
    { intros H,
      cases H,
      { exact subset.trans (erase_le a t) H },
      { rcases H with ⟨u, hu⟩,
        rw ← hu.2,
        exact subset.trans (erase_insert_le a u) hu.1 } } },
  { have : ¬ ∃ (u : finset α), u ≤ s ∧ insert a u = t,
      by simp [ne.symm (ne_insert_of_not_mem _ _ h)],
    simp [finset.erase_eq_of_not_mem h, this] }
end

end powerset

section powerset_len

/-- Given an integer `n` and a finset `s`, then `powerset_len n s` is the finset of subsets of `s`
of cardinality `n`.-/
def powerset_len (n : ℕ) (s : finset α) : finset (finset α) :=
⟨(s.1.powerset_len n).pmap finset.mk
  (λ t h, nodup_of_le (mem_powerset_len.1 h).1 s.2),
 nodup_pmap (λ a ha b hb, congr_arg finset.val)
   (nodup_powerset_len s.2)⟩

theorem mem_powerset_len {n} {s t : finset α} :
  s ∈ powerset_len n t ↔ s ≤ t ∧ card s = n :=
by cases s; simp [powerset_len, val_le_iff.symm]; refl

@[simp, mono] theorem powerset_len_mono {n} {s t : finset α} (h : s ≤ t) :
  powerset_len n s ≤ powerset_len n t :=
λ u h', mem_powerset_len.2 $
  and.imp (λ h₂, subset.trans h₂ h) id (mem_powerset_len.1 h')

@[simp] theorem card_powerset_len (n : ℕ) (s : finset α) :
  card (powerset_len n s) = nat.choose (card s) n :=
(card_pmap _ _ _).trans (card_powerset_len n s.1)

end powerset_len

/-! ### fold -/
section fold
variables (op : β → β → β) [hc : is_commutative β op] [ha : is_associative β op]
local notation a * b := op a b
include hc ha

/-- `fold op b f s` folds the commutative associative operation `op` over the
  `f`-image of `s`, i.e. `fold (+) b f {1,2,3} = `f 1 + f 2 + f 3 + b`. -/
def fold (b : β) (f : α → β) (s : finset α) : β := (s.1.map f).fold op b

variables {op} {f : α → β} {b : β} {s : finset α} {a : α}

@[simp] theorem fold_bot : (⊥ : finset α).fold op b f = b := rfl

@[simp] theorem fold_insert [decidable_eq α] (h : a ∉ s) :
  (insert a s).fold op b f = f a * s.fold op b f :=
by unfold fold; rw [insert_val, ndinsert_of_not_mem h, map_cons, fold_cons_left]

@[simp] theorem fold_singleton : ({a} : finset α).fold op b f = f a * b := rfl

@[simp] theorem fold_map {g : γ ↪ α} {s : finset γ} :
  (s.map g).fold op b f = s.fold op b (f ∘ g) :=
by simp only [fold, map, multiset.map_map]

@[simp] theorem fold_image [decidable_eq α] {g : γ → α} {s : finset γ}
  (H : ∀ (x ∈ s) (y ∈ s), g x = g y → x = y) : (s.image g).fold op b f = s.fold op b (f ∘ g) :=
by simp only [fold, image_val_of_inj_on H, multiset.map_map]

@[congr] theorem fold_congr {g : α → β} (H : ∀ x ∈ s, f x = g x) : s.fold op b f = s.fold op b g :=
by rw [fold, fold, map_congr H]

theorem fold_op_distrib {f g : α → β} {b₁ b₂ : β} :
  s.fold op (b₁ * b₂) (λx, f x * g x) = s.fold op b₁ f * s.fold op b₂ g :=
by simp only [fold, fold_distrib]

theorem fold_hom {op' : γ → γ → γ} [is_commutative γ op'] [is_associative γ op']
  {m : β → γ} (hm : ∀x y, m (op x y) = op' (m x) (m y)) :
  s.fold op' (m b) (λx, m (f x)) = m (s.fold op b f) :=
by rw [fold, fold, ← fold_hom op hm, multiset.map_map]

theorem fold_union_inter [decidable_eq α] {s₁ s₂ : finset α} {b₁ b₂ : β} :
  (s₁ ⊔ s₂).fold op b₁ f * (s₁ ⊓ s₂).fold op b₂ f = s₁.fold op b₂ f * s₂.fold op b₁ f :=
by unfold fold; rw [← fold_add op, ← map_add, sup_val,
     inf_val, union_add_inter, map_add, hc.comm, fold_add]

@[simp] theorem fold_insert_idem [decidable_eq α] [hi : is_idempotent β op] :
  (insert a s).fold op b f = f a * s.fold op b f :=
begin
  by_cases (a ∈ s),
  { rw [← insert_erase h], simp [← ha.assoc, hi.idempotent] },
  { apply fold_insert h },
end

lemma fold_op_rel_iff_and
  {r : β → β → Prop} (hr : ∀ {x y z}, r x (op y z) ↔ (r x y ∧ r x z)) {c : β} :
  r c (s.fold op b f) ↔ (r c b ∧ ∀ x∈s, r c (f x)) :=
begin
  classical,
  apply finset.induction_on s, { simp },
  clear s, intros a s ha IH,
  rw [finset.fold_insert ha, hr, IH, ← and_assoc, and_comm (r c (f a)), and_assoc],
  apply and_congr iff.rfl,
  split,
  { rintro ⟨h₁, h₂⟩, intros b hb, rw finset.mem_insert at hb,
    rcases hb with rfl|hb; solve_by_elim },
  { intro h, split,
    { exact h a (finset.mem_insert_self _ _), },
    { intros b hb, apply h b, rw finset.mem_insert, right, exact hb } }
end

lemma fold_op_rel_iff_or
  {r : β → β → Prop} (hr : ∀ {x y z}, r x (op y z) ↔ (r x y ∨ r x z)) {c : β} :
  r c (s.fold op b f) ↔ (r c b ∨ ∃ x∈s, r c (f x)) :=
begin
  classical,
  apply finset.induction_on s, { simp },
  clear s, intros a s ha IH,
  rw [finset.fold_insert ha, hr, IH, ← or_assoc, or_comm (r c (f a)), or_assoc],
  apply or_congr iff.rfl,
  split,
  { rintro (h₁|⟨x, hx, h₂⟩),
    { use a, simp [h₁] },
    { refine ⟨x, by simp [hx], h₂⟩ } },
  { rintro ⟨x, hx, h⟩,
    rw mem_insert at hx, cases hx,
    { left, rwa hx at h },
    { right, exact ⟨x, hx, h⟩ } }
end

omit hc ha

section order
variables [decidable_linear_order β] (c : β)

lemma le_fold_min : c ≤ s.fold min b f ↔ (c ≤ b ∧ ∀ x∈s, c ≤ f x) :=
fold_op_rel_iff_and $ λ x y z, le_min_iff

lemma fold_min_le : s.fold min b f ≤ c ↔ (b ≤ c ∨ ∃ x∈s, f x ≤ c) :=
begin
  show _ ≥ _ ↔ _,
  apply fold_op_rel_iff_or,
  intros x y z,
  show _ ≤ _ ↔ _,
  exact min_le_iff
end

lemma lt_fold_min : c < s.fold min b f ↔ (c < b ∧ ∀ x∈s, c < f x) :=
fold_op_rel_iff_and $ λ x y z, lt_min_iff

lemma fold_min_lt : s.fold min b f < c ↔ (b < c ∨ ∃ x∈s, f x < c) :=
begin
  show _ > _ ↔ _,
  apply fold_op_rel_iff_or,
  intros x y z,
  show _ < _ ↔ _,
  exact min_lt_iff
end

lemma fold_max_le : s.fold max b f ≤ c ↔ (b ≤ c ∧ ∀ x∈s, f x ≤ c) :=
begin
  show _ ≥ _ ↔ _,
  apply fold_op_rel_iff_and,
  intros x y z,
  show _ ≤ _ ↔ _,
  exact max_le_iff
end

lemma le_fold_max : c ≤ s.fold max b f ↔ (c ≤ b ∨ ∃ x∈s, c ≤ f x) :=
fold_op_rel_iff_or $ λ x y z, le_max_iff

lemma fold_max_lt : s.fold max b f < c ↔ (b < c ∧ ∀ x∈s, f x < c) :=
begin
  show _ > _ ↔ _,
  apply fold_op_rel_iff_and,
  intros x y z,
  show _ < _ ↔ _,
  exact max_lt_iff
end

lemma lt_fold_max : c < s.fold max b f ↔ (c < b ∨ ∃ x∈s, c < f x) :=
fold_op_rel_iff_or $ λ x y z, lt_max_iff

end order

end fold

/-! ### supr -/
section supr
variables [semilattice_sup_bot α]

/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
def supr (s : finset β) (f : β → α) : α := s.fold (⊔) ⊥ f

variables {s s₁ s₂ : finset β} {f : β → α}

lemma supr_val : s.supr f = (s.1.map f).sup := rfl

@[simp] lemma supr_bot : (⊥ : finset β).supr f = ⊥ :=
fold_bot

@[simp] lemma supr_insert [decidable_eq β] {b : β} :
  (insert b s : finset β).supr f = f b ⊔ s.supr f :=
fold_insert_idem

@[simp] lemma supr_singleton {b : β} : ({b} : finset β).supr f = f b :=
sup_singleton

lemma supr_sup [decidable_eq β] : (s₁ ⊔ s₂).supr f = s₁.supr f ⊔ s₂.supr f :=
finset.induction_on s₁ (by rw [bot_sup_eq, supr_bot, bot_sup_eq]) $ λ a s has ih,
by rw [insert_sup, supr_insert, supr_insert, ih, sup_assoc]

@[congr] theorem supr_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀a∈s₂, f a = g a) :
  s₁.supr f = s₂.supr g :=
by subst hs; exact finset.fold_congr hfg

@[simp] lemma supr_le_iff {a : α} : s.supr f ≤ a ↔ (∀b ∈ s, f b ≤ a) :=
begin
  apply iff.trans multiset.sup_le,
  simp only [multiset.mem_map, and_imp, exists_imp_distrib],
  exact ⟨λ k b hb, k _ _ hb rfl, λ k a' b hb h, h ▸ k _ hb⟩,
end

lemma supr_le {a : α} : (∀b ∈ s, f b ≤ a) → s.supr f ≤ a :=
supr_le_iff.2

lemma le_supr {b : β} (hb : b ∈ s) : f b ≤ s.supr f :=
supr_le_iff.1 (le_refl _) _ hb

lemma is_lub_supr (s : finset β) (f : β → α) : is_lub (f '' ↑s) (s.supr f) :=
⟨λ x hx, let ⟨a, ha, hx⟩ := hx in hx ▸ le_supr ha,
  λ b hb, supr_le $ λ x hx, hb ⟨x, hx, rfl⟩⟩

@[mono] lemma supr_mono {g : β → α} (hs : s₁ ≤ s₂) (hf : ∀ b ∈ s₁, f b ≤ g b) :
  s₁.supr f ≤ s₂.supr g :=
supr_le $ λ b hb, le_trans (hf b hb) (le_supr $ hs hb)

lemma supr_mono_fun {g : β → α} (h : ∀b∈s, f b ≤ g b) : s.supr f ≤ s.supr g :=
supr_mono (le_refl s) h

lemma supr_mono_set (h : s₁ ≤ s₂) : s₁.supr f ≤ s₂.supr f :=
supr_mono h (λ _ _, le_refl _)

@[simp] lemma supr_lt_iff [is_total α (≤)] {a : α} (ha : ⊥ < a) :
  s.supr f < a ↔ (∀b ∈ s, f b < a) :=
by letI := classical.dec_eq β; from
⟨ λh b hb, lt_of_le_of_lt (le_supr hb) h,
  finset.induction_on s (by simp [ha]) (by simp {contextual := tt}) ⟩

lemma comp_supr_eq_supr_comp [is_total α (≤)] {γ : Type} [semilattice_sup_bot γ]
  (g : α → γ) (mono_g : monotone g) (bot : g ⊥ = ⊥) :
  g (s.supr f) = s.supr (g ∘ f) :=
by letI := classical.dec_eq β; from
finset.induction_on s (by simp [bot]) (by simp [mono_g.map_sup] {contextual := tt})

theorem le_range_supr_succ (s : finset ℕ) : s ≤ range (s.supr id).succ :=
λ n hn, mem_range.2 $ nat.lt_succ_of_le $ le_supr hn

theorem exists_nat_le_range (s : finset ℕ) : ∃n : ℕ, s ≤ range n :=
⟨_, s.le_range_supr_succ⟩

end supr

lemma supr_eq_bsupr [complete_lattice β] (s : finset α) (f : α → β) : s.supr f = (⨆a∈s, f a) :=
(is_lub_supr s f).unique is_lub_bsupr

/-! ### infi -/
section infi
variables [semilattice_inf_top α]

/-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/
def infi (s : finset β) (f : β → α) : α := s.fold (⊓) ⊤ f

variables {s s₁ s₂ : finset β} {f : β → α}

lemma infi_val : s.infi f = (s.1.map f).inf := rfl

@[simp] lemma infi_bot : (⊥ : finset β).infi f = ⊤ := fold_bot

lemma le_infi_iff {a : α} : a ≤ s.infi f ↔ ∀b ∈ s, a ≤ f b :=
@supr_le_iff (order_dual α) β _ _ _ _

@[simp] lemma infi_insert [decidable_eq β] {b : β} :
  (insert b s : finset β).infi f = f b ⊓ s.infi f :=
fold_insert_idem

@[simp] lemma infi_singleton {b : β} : ({b} : finset β).infi f = f b :=
inf_singleton

lemma infi_sup [decidable_eq β] : (s₁ ⊔ s₂).infi f = s₁.infi f ⊓ s₂.infi f :=
@supr_sup (order_dual α) _ _ _ _ _ _

theorem infi_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀a∈s₂, f a = g a) : s₁.infi f = s₂.infi g :=
@supr_congr (order_dual α) _ _ _ _ _ _ hs hfg

lemma infi_le {b : β} (hb : b ∈ s) : s.infi f ≤ f b :=
le_infi_iff.1 (le_refl _) _ hb

lemma le_infi {a : α} : (∀b ∈ s, a ≤ f b) → a ≤ s.infi f :=
le_infi_iff.2

lemma is_glb_infi (s : finset β) (f : β → α) : is_glb (f '' ↑s) (s.infi f) :=
@is_lub_supr (order_dual α) _ _ s f

@[mono] lemma infi_mono {g : β → α} (hs : s₁ ≤ s₂) (hf : ∀ b ∈ s₁, f b ≤ g b) :
  s₂.infi f ≤ s₁.infi g :=
@supr_mono (order_dual α) β _ _ _ _ _ hs hf

lemma infi_mono_fun {g : β → α} (h : ∀b∈s, f b ≤ g b) : s.infi f ≤ s.infi g :=
infi_mono (le_refl s) h

lemma infi_mono_set (h : s₁ ≤ s₂) : s₂.infi f ≤ s₁.infi f := infi_mono h (λ _ _, le_refl _)

lemma lt_infi_iff [h : is_total α (≤)] {a : α} (ha : a < ⊤) : a < s.infi f ↔ (∀b ∈ s, a < f b) :=
@supr_lt_iff (order_dual α) β _ _ _ (@is_total.swap _ _ h) _ ha

lemma comp_infi_eq_infi_comp [h : is_total α (≤)] {γ : Type} [semilattice_inf_top γ]
  (g : α → γ) (mono_g : monotone g) (top : g ⊤ = ⊤) :
  g (s.infi f) = s.infi (g ∘ f) :=
@comp_supr_eq_supr_comp (order_dual α) _ _ _ _ (@is_total.swap _ _ h)
  (order_dual γ) _ g mono_g.order_dual top

end infi

lemma infi_eq_binfi [complete_lattice β] (s : finset α) (f : α → β) : s.infi f = (⨅a∈s, f a) :=
@supr_eq_bsupr α (order_dual β) _ s f

/-! ### max and min of finite sets -/
section max_min
variables [decidable_linear_order α]

/-- Let `s` be a finset in a linear order. Then `s.max` is the maximum of `s` if `s` is not empty,
and `none` otherwise. It belongs to `option α`. If you want to get an element of `α`, see
`s.max'`. -/
protected def max : finset α → option α :=
fold (option.lift_or_get max) none some

theorem max_eq_supr_with_bot (s : finset α) :
  s.max = @supr (with_bot α) α _ s some := rfl

@[simp] theorem max_bot : (⊥ : finset α).max = none := rfl

@[simp] theorem max_insert {a : α} {s : finset α} :
  (insert a s).max = option.lift_or_get max (some a) s.max := fold_insert_idem

@[simp] theorem max_singleton {a : α} : finset.max {a} = some a :=
by { rw [← insert_bot], exact max_insert }

theorem max_of_mem {s : finset α} {a : α} (h : a ∈ s) : ∃ b, b ∈ s.max :=
(@le_supr (with_bot α) _ _ _ _ _ h _ rfl).imp $ λ b, Exists.fst

theorem max_of_nonempty {s : finset α} (h : s.nonempty) : ∃ a, a ∈ s.max :=
let ⟨a, ha⟩ := h in max_of_mem ha

theorem max_eq_none {s : finset α} : s.max = none ↔ s = ⊥ :=
⟨λ h, s.eq_bot_or_nonempty.elim id
  (λ H, let ⟨a, ha⟩ := max_of_nonempty H in by rw h at ha; cases ha),
  λ h, h.symm ▸ max_bot⟩

theorem mem_of_max {s : finset α} : ∀ {a : α}, a ∈ s.max → a ∈ s :=
finset.induction_on s (λ _ H, by cases H)
  (λ b s _ (ih : ∀ {a}, a ∈ s.max → a ∈ s) a (h : a ∈ (insert b s).max),
  begin
    by_cases p : b = a,
    { induction p, exact mem_insert_self b s },
    { cases option.lift_or_get_choice max_choice (some b) s.max with q q;
      rw [max_insert, q] at h,
      { cases h, cases p rfl },
      { exact mem_insert_of_mem (ih h) } }
  end)

theorem le_max_of_mem {s : finset α} {a b : α} (h₁ : a ∈ s) (h₂ : b ∈ s.max) : a ≤ b :=
by rcases @le_supr (with_bot α) _ _ _ _ _ h₁ _ rfl with ⟨b', hb, ab⟩;
   cases h₂.symm.trans hb; assumption

/-- Let `s` be a finset in a linear order. Then `s.min` is the minimum of `s` if `s` is not empty,
and `none` otherwise. It belongs to `option α`. If you want to get an element of `α`, see
`s.min'`. -/
protected def min : finset α → option α :=
fold (option.lift_or_get min) none some

theorem min_eq_infi_with_top (s : finset α) :
  s.min = @infi (with_top α) α _ s some := rfl

@[simp] theorem min_bot : (⊥ : finset α).min = none := rfl

@[simp] theorem min_insert {a : α} {s : finset α} :
  (insert a s).min = option.lift_or_get min (some a) s.min :=
fold_insert_idem

@[simp] theorem min_singleton {a : α} : finset.min {a} = some a :=
by { rw ← insert_bot, exact min_insert }

theorem min_of_mem {s : finset α} {a : α} (h : a ∈ s) : ∃ b, b ∈ s.min :=
(@infi_le (with_top α) _ _ _ _ _ h _ rfl).imp $ λ b, Exists.fst

theorem min_of_nonempty {s : finset α} (h : s.nonempty) : ∃ a, a ∈ s.min :=
let ⟨a, ha⟩ := h in min_of_mem ha

theorem min_eq_none {s : finset α} : s.min = none ↔ s = ⊥ :=
⟨λ h, s.eq_bot_or_nonempty.elim id
  (λ H, let ⟨a, ha⟩ := min_of_nonempty H in by rw h at ha; cases ha),
  λ h, h.symm ▸ min_bot⟩

theorem mem_of_min {s : finset α} : ∀ {a : α}, a ∈ s.min → a ∈ s :=
finset.induction_on s (λ _ H, by cases H) $
  λ b s _ (ih : ∀ {a}, a ∈ s.min → a ∈ s) a (h : a ∈ (insert b s).min),
  begin
    by_cases p : b = a,
    { induction p, exact mem_insert_self b s },
    { cases option.lift_or_get_choice min_choice (some b) s.min with q q;
      rw [min_insert, q] at h,
      { cases h, cases p rfl },
      { exact mem_insert_of_mem (ih h) } }
  end

theorem min_le_of_mem {s : finset α} {a b : α} (h₁ : b ∈ s) (h₂ : a ∈ s.min) : a ≤ b :=
by rcases @infi_le (with_top α) _ _ _ _ _ h₁ _ rfl with ⟨b', hb, ab⟩;
   cases h₂.symm.trans hb; assumption

/-- Given a nonempty finset `s` in a linear order `α `, then `s.min' h` is its minimum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.min`,
taking values in `option α`. -/
def min' (s : finset α) (H : s.nonempty) : α :=
@option.get _ s.min $
  let ⟨k, hk⟩ := H in
  let ⟨b, hb⟩ := min_of_mem hk in by simp at hb; simp [hb]

/-- Given a nonempty finset `s` in a linear order `α `, then `s.max' h` is its maximum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `option α`. -/
def max' (s : finset α) (H : s.nonempty) : α :=
@option.get _ s.max $
  let ⟨k, hk⟩ := H in
  let ⟨b, hb⟩ := max_of_mem hk in by simp at hb; simp [hb]

variables (s : finset α) (H : s.nonempty)

theorem min'_mem : s.min' H ∈ s := mem_of_min $ by simp [min']

theorem min'_le (x) (H2 : x ∈ s) : s.min' H ≤ x := min_le_of_mem H2 $ option.get_mem _

theorem le_min' (x) (H2 : ∀ y ∈ s, x ≤ y) : x ≤ s.min' H := H2 _ $ min'_mem _ _

theorem max'_mem : s.max' H ∈ s := mem_of_max $ by simp [max']

theorem le_max' (x) (H2 : x ∈ s) : x ≤ s.max' H := le_max_of_mem H2 $ option.get_mem _

theorem max'_le (x) (H2 : ∀ y ∈ s, y ≤ x) : s.max' H ≤ x := H2 _ $ max'_mem _ _

theorem min'_lt_max' {i j} (H1 : i ∈ s) (H2 : j ∈ s) (H3 : i ≠ j) : s.min' H < s.max' H :=
begin
  rcases lt_trichotomy i j with H4 | H4 | H4,
  { have H5 := min'_le s H i H1,
    have H6 := le_max' s H j H2,
    apply lt_of_le_of_lt H5,
    apply lt_of_lt_of_le H4 H6 },
  { cc },
  { have H5 := min'_le s H j H2,
    have H6 := le_max' s H i H1,
    apply lt_of_le_of_lt H5,
    apply lt_of_lt_of_le H4 H6 }
end

/--
If there's more than 1 element, the min' is less than the max'. An alternate version of
`min'_lt_max'` which is sometimes more convenient.
-/
lemma min'_lt_max'_of_card (h₂ : 1 < card s) : s.min' H < s.max' H :=
begin
  apply lt_of_not_ge,
  intro a,
  apply not_le_of_lt h₂ (le_of_eq _),
  rw card_eq_one,
  use max' s H,
  rw eq_singleton_iff_unique_mem,
  refine ⟨max'_mem _ _, λ t Ht, le_antisymm (le_max' s H t Ht) (le_trans a (min'_le s H t Ht))⟩,
end

end max_min

section exists_max_min

variables [linear_order α]
lemma exists_max_image (s : finset β) (f : β → α) (h : s.nonempty) :
  ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x :=
begin
  letI := classical.DLO α,
  cases max_of_nonempty (h.image f) with y hy,
  rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩,
  exact ⟨x, hx, λ x' hx', le_max_of_mem (mem_image_of_mem f hx') hy⟩,
end

lemma exists_min_image (s : finset β) (f : β → α) (h : s.nonempty) :
  ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x' :=
begin
  letI := classical.DLO α,
  cases min_of_nonempty (h.image f) with y hy,
  rcases mem_image.mp (mem_of_min hy) with ⟨x, hx, rfl⟩,
  exact ⟨x, hx, λ x' hx', min_le_of_mem (mem_image_of_mem f hx') hy⟩
end

end exists_max_min

/-! ### sort -/
section sort
variables (r : α → α → Prop) [decidable_rel r]
  [is_trans α r] [is_antisymm α r] [is_total α r]

/-- `sort s` constructs a sorted list from the unordered set `s`.
  (Uses merge sort algorithm.) -/
def sort (s : finset α) : list α := sort r s.1

@[simp] theorem sort_sorted (s : finset α) : list.sorted r (sort r s) :=
sort_sorted _ _

@[simp] theorem sort_eq (s : finset α) : ↑(sort r s) = s.1 :=
sort_eq _ _

@[simp] theorem sort_nodup (s : finset α) : (sort r s).nodup :=
(by rw sort_eq; exact s.2 : @multiset.nodup α (sort r s))

@[simp] theorem sort_to_finset [decidable_eq α] (s : finset α) : (sort r s).to_finset = s :=
list.to_finset_eq (sort_nodup r s) ▸ eq_of_veq (sort_eq r s)

@[simp] theorem mem_sort {s : finset α} {a : α} : a ∈ sort r s ↔ a ∈ s :=
multiset.mem_sort _

@[simp] theorem length_sort {s : finset α} : (sort r s).length = s.card :=
multiset.length_sort _

end sort

section sort_linear_order

variables [decidable_linear_order α]

theorem sort_sorted_lt (s : finset α) :
  list.sorted (<) (sort (≤) s) :=
(sort_sorted _ _).imp₂ (@lt_of_le_of_ne _ _) (sort_nodup _ _)

lemma sorted_zero_eq_min' (s : finset α) (h : 0 < (s.sort (≤)).length) (H : s.nonempty) :
  (s.sort (≤)).nth_le 0 h = s.min' H :=
begin
  let l := s.sort (≤),
  apply le_antisymm,
  { have : s.min' H ∈ l := (finset.mem_sort (≤)).mpr (s.min'_mem H),
    obtain ⟨i, i_lt, hi⟩ : ∃ i (hi : i < l.length), l.nth_le i hi = s.min' H :=
      list.mem_iff_nth_le.1 this,
    rw ← hi,
    exact list.nth_le_of_sorted_of_le (s.sort_sorted (≤)) (nat.zero_le i) },
  { have : l.nth_le 0 h ∈ s := (finset.mem_sort (≤)).1 (list.nth_le_mem l 0 h),
    exact s.min'_le H _ this }
end

lemma sorted_last_eq_max' (s : finset α) (h : (s.sort (≤)).length - 1 < (s.sort (≤)).length)
  (H : s.nonempty) : (s.sort (≤)).nth_le ((s.sort (≤)).length - 1) h = s.max' H :=
begin
  let l := s.sort (≤),
  apply le_antisymm,
  { have : l.nth_le ((s.sort (≤)).length - 1) h ∈ s :=
      (finset.mem_sort (≤)).1 (list.nth_le_mem l _ h),
    exact s.le_max' H _ this },
  { have : s.max' H ∈ l := (finset.mem_sort (≤)).mpr (s.max'_mem H),
    obtain ⟨i, i_lt, hi⟩ : ∃ i (hi : i < l.length), l.nth_le i hi = s.max' H :=
      list.mem_iff_nth_le.1 this,
    rw ← hi,
    have : i ≤ l.length - 1 := nat.le_pred_of_lt i_lt,
    exact list.nth_le_of_sorted_of_le (s.sort_sorted (≤)) (nat.le_pred_of_lt i_lt) },
end

/-- Given a finset `s` of cardinal `k` in a linear order `α`, the map `mono_of_fin s h`
is the increasing bijection between `fin k` and `s` as an `α`-valued map. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of a map `fin s.card → α` to avoid
casting issues in further uses of this function. -/
def mono_of_fin (s : finset α) {k : ℕ} (h : s.card = k) (i : fin k) : α :=
have A : (i : ℕ) < (s.sort (≤)).length, by simpa [h] using i.2,
(s.sort (≤)).nth_le i A

lemma mono_of_fin_strict_mono (s : finset α) {k : ℕ} (h : s.card = k) :
  strict_mono (s.mono_of_fin h) :=
begin
  assume i j hij,
  exact list.pairwise_iff_nth_le.1 s.sort_sorted_lt _ _ _ hij
end

lemma mono_of_fin_bij_on (s : finset α) {k : ℕ} (h : s.card = k) :
  set.bij_on (s.mono_of_fin h) set.univ ↑s :=
begin
  have A : ∀ j, j ∈ s ↔ j ∈ (s.sort (≤)) := λ j, by simp,
  apply set.bij_on.mk,
  { assume i hi,
    simp only [mono_of_fin, set.mem_preimage, mem_coe, list.nth_le, A],
    exact list.nth_le_mem _ _ _ },
  { exact ((mono_of_fin_strict_mono s h).injective).inj_on _ },
  { assume x hx,
    simp only [mem_coe, A] at hx,
    obtain ⟨i, il, hi⟩ : ∃ (i : ℕ) (h : i < (s.sort (≤)).length), (s.sort (≤)).nth_le i h = x :=
      list.nth_le_of_mem hx,
    simp [h] at il,
    exact ⟨⟨i, il⟩, set.mem_univ _, hi⟩ }
end

lemma mono_of_fin_injective (s : finset α) {k : ℕ} (h : s.card = k) :
  function.injective (s.mono_of_fin h) :=
set.injective_iff_inj_on_univ.mpr (s.mono_of_fin_bij_on h).inj_on

/-- The bijection `mono_of_fin s h` sends `0` to the minimum of `s`. -/
lemma mono_of_fin_zero {s : finset α} {k : ℕ} (h : s.card = k) (hs : s.nonempty) (hz : 0 < k) :
  mono_of_fin s h ⟨0, hz⟩ = s.min' hs :=
begin
  apply le_antisymm,
  { have : min' s hs ∈ s := min'_mem s hs,
    rcases (mono_of_fin_bij_on s h).surj_on this with ⟨a, _, ha⟩,
    rw ← ha,
    apply (mono_of_fin_strict_mono s h).monotone,
    exact zero_le a.val },
  { have : mono_of_fin s h ⟨0, hz⟩ ∈ s := (mono_of_fin_bij_on s h).maps_to (set.mem_univ _),
    exact min'_le s hs _ this }
end

/-- The bijection `mono_of_fin s h` sends `k-1` to the maximum of `s`. -/
lemma mono_of_fin_last {s : finset α} {k : ℕ} (h : s.card = k) (hs : s.nonempty) (hz : 0 < k) :
  mono_of_fin s h ⟨k-1, buffer.lt_aux_2 hz⟩ = s.max' hs :=
begin
  have h'' : k - 1 < k := buffer.lt_aux_2 hz,
  apply le_antisymm,
  { have : mono_of_fin s h ⟨k-1, h''⟩ ∈ s := (mono_of_fin_bij_on s h).maps_to (set.mem_univ _),
    exact le_max' s hs _ this },
  { have : max' s hs ∈ s := max'_mem s hs,
    rcases (mono_of_fin_bij_on s h).surj_on this with ⟨a, _, ha⟩,
    rw ← ha,
    apply (mono_of_fin_strict_mono s h).monotone,
    exact le_pred_of_lt a.2},
end

/-- Any increasing bijection between `fin k` and a finset of cardinality `k` has to coincide with
the increasing bijection `mono_of_fin s h`. For a statement assuming only that `f` maps `univ` to
`s`, see `mono_of_fin_unique'`.-/
lemma mono_of_fin_unique {s : finset α} {k : ℕ} (h : s.card = k) {f : fin k → α}
  (hbij : set.bij_on f set.univ ↑s) (hmono : strict_mono f) : f = s.mono_of_fin h :=
begin
  ext ⟨i, hi⟩,
  induction i using nat.strong_induction_on with i IH,
  rcases lt_trichotomy (f ⟨i, hi⟩) (mono_of_fin s h ⟨i, hi⟩) with H|H|H,
  { have A : f ⟨i, hi⟩ ∈ ↑s := hbij.maps_to (set.mem_univ _),
    rcases (mono_of_fin_bij_on s h).surj_on A with ⟨j, _, hj⟩,
    rw ← hj at H,
    have ji : j < ⟨i, hi⟩ := (mono_of_fin_strict_mono s h).lt_iff_lt.1 H,
    have : f j = mono_of_fin s h j,
      by { convert IH j.1 ji (lt_trans ji hi), rw fin.ext_iff },
    rw ← this at hj,
    exact (ne_of_lt (hmono ji) hj).elim },
  { exact H },
  { have A : mono_of_fin s h ⟨i, hi⟩ ∈ ↑s := (mono_of_fin_bij_on s h).maps_to (set.mem_univ _),
    rcases hbij.surj_on A with ⟨j, _, hj⟩,
    rw ← hj at H,
    have ji : j < ⟨i, hi⟩ := hmono.lt_iff_lt.1 H,
    have : f j = mono_of_fin s h j,
      by { convert IH j.1 ji (lt_trans ji hi), rw fin.ext_iff },
    rw this at hj,
    exact (ne_of_lt (mono_of_fin_strict_mono s h ji) hj).elim }
end

/-- Two parametrizations `mono_of_fin` of the same set take the same value on `i` and `j` if and
only if `i = j`. Since they can be defined on a priori not defeq types `fin k` and `fin l` (although
necessarily `k = l`), the conclusion is rather written `i.val = j.val`. -/
@[simp] lemma mono_of_fin_eq_mono_of_fin_iff
  {k l : ℕ} {s : finset α} {i : fin k} {j : fin l} {h : s.card = k} {h' : s.card = l} :
  s.mono_of_fin h i = s.mono_of_fin h' j ↔ i.val = j.val :=
begin
  have A : k = l, by rw [← h', ← h],
  have : s.mono_of_fin h = (s.mono_of_fin h') ∘ (λ j : (fin k), ⟨j.1, A ▸ j.2⟩) := rfl,
  rw [this, function.comp_app, (s.mono_of_fin_injective h').eq_iff, fin.ext_iff]
end

/-- Given a finset `s` of cardinal `k` in a linear order `α`, the equiv `mono_equiv_of_fin s h`
is the increasing bijection between `fin k` and `s` as an `s`-valued map. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of a map `fin s.card → α` to avoid
casting issues in further uses of this function. -/
noncomputable def mono_equiv_of_fin (s : finset α) {k : ℕ} (h : s.card = k) :
  fin k ≃ {x // x ∈ s} :=
(s.mono_of_fin_bij_on h).equiv _

end sort_linear_order

/-! ### disjoint -/
section disjoint
variable [decidable_eq α]

@[simp, norm_cast] lemma disjoint_coe {s t : finset α} :
  disjoint (↑s : set α) ↑t ↔ disjoint s t :=
by { simp only [disjoint_iff, set.bot_eq_empty, set.inf_eq_inter, ← coe_bot, ← coe_inf, coe_inj] }

theorem disjoint_left {s t : finset α} : disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t :=
by exact_mod_cast @set.disjoint_left α ↑s ↑t

theorem disjoint_val {s t : finset α} : disjoint s t ↔ s.1.disjoint t.1 :=
disjoint_left

instance decidable_disjoint (U V : finset α) : decidable (disjoint U V) :=
decidable_of_decidable_of_iff (by apply_instance) eq_bot_iff

theorem disjoint_right {s t : finset α} : disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
by rw [disjoint.comm, disjoint_left]

theorem disjoint_iff_ne {s t : finset α} : disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b :=
by simp only [disjoint_left, imp_not_comm, forall_eq']

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

@[simp] theorem disjoint_sup_left {s t u : finset α} :
  disjoint (s ⊔ t) u ↔ disjoint s u ∧ disjoint t u :=
by simp only [disjoint_left, mem_sup, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_sup_right {s t u : finset α} :
  disjoint s (t ⊔ u) ↔ disjoint s t ∧ disjoint s u :=
by simp only [disjoint_right, mem_sup, or_imp_distrib, forall_and_distrib]

lemma disjoint_sdiff_inf (s t : finset α) : disjoint (s \ t) (s ⊓ t) :=
(sdiff_disjoint s t).mono_right inf_le_right

lemma sdiff_eq_self_of_disjoint {s t : finset α} (h : disjoint s t) : s \ t = s :=
sdiff_eq_self.2 h

lemma disjoint_self_iff_bot (s : finset α) : disjoint s s ↔ s = ⊥ :=
disjoint_self

lemma disjoint_bind_left {ι : Type*}
  (s : finset ι) (f : ι → finset α) (t : finset α) :
  disjoint (s.bind f) t ↔ (∀i∈s, disjoint (f i) t) :=
begin
  classical,
  refine s.induction _ _,
  { simp only [forall_mem_bot_iff, bind_bot, disjoint_bot_left] },
  { assume i s his ih,
    simp only [disjoint_sup_left, bind_insert, his, forall_mem_insert, ih] }
end

lemma disjoint_bind_right {ι : Type*}
  (s : finset α) (t : finset ι) (f : ι → finset α) :
  disjoint s (t.bind f) ↔ (∀i∈t, disjoint s (f i)) :=
by simpa only [disjoint.comm] using disjoint_bind_left t f s

@[simp] theorem card_disjoint_sup {s t : finset α} (h : disjoint s t) :
  card (s ⊔ t) = card s + card t :=
by rw [← card_sup_add_card_inf, h.eq_bot, card_bot, add_zero]

theorem card_sdiff {s t : finset α} (h : s ≤ t) : card (t \ s) = card t - card s :=
suffices card (t \ s) = card ((t \ s) ⊔ s) - card s, by rwa sdiff_sup_of_le h at this,
by rw [card_disjoint_sup (sdiff_disjoint _ _), nat.add_sub_cancel]

lemma disjoint_filter {s : finset α} {p q : α → Prop} [decidable_pred p] [decidable_pred q] :
    disjoint (s.filter p) (s.filter q) ↔ (∀ x ∈ s, p x → ¬ q x) :=
by split; simp [disjoint_left] {contextual := tt}

lemma disjoint_filter_filter {s t : finset α} {p q : α → Prop} [decidable_pred p]
  [decidable_pred q] :
  (disjoint s t) → disjoint (s.filter p) (t.filter q) :=
disjoint.mono (filter_subset _) (filter_subset _)

lemma pi_disjoint_of_disjoint {δ : α → Type*} [∀a, decidable_eq (δ a)]
  {s : finset α} [decidable_eq (Πa∈s, δ a)]
  (t₁ t₂ : Πa, finset (δ a)) {a : α} (ha : a ∈ s) (h : disjoint (t₁ a) (t₂ a)) :
  disjoint (s.pi t₁) (s.pi t₂) :=
disjoint_iff_ne.2 $ λ f₁ hf₁ f₂ hf₂ eq₁₂,
  disjoint_iff_ne.1 h (f₁ a ha) (mem_pi.mp hf₁ a ha) (f₂ a ha) (mem_pi.mp hf₂ a ha)
  $ congr_fun (congr_fun eq₁₂ a) ha

lemma disjoint_iff_disjoint_coe {α : Type*} {a b : finset α} [decidable_eq α] :
  disjoint a b ↔ disjoint (↑a : set α) (↑b : set α) :=
by { rw [finset.disjoint_left, set.disjoint_left], refl }

end disjoint

/--
Given a set A and a set B inside it, we can shrink A to any appropriate size, and keep B
inside it.
-/
lemma exists_intermediate_set {A B : finset α} (i : ℕ)
  (h₁ : i + card B ≤ card A) (h₂ : B ≤ A) :
  ∃ (C : finset α), B ≤ C ∧ C ≤ A ∧ card C = i + card B :=
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
  ∃ (B : finset α), B ≤ A ∧ card B = i :=
let ⟨B, _, x₁, x₂⟩ := exists_intermediate_set i (by simpa) bot_le in ⟨B, x₁, x₂⟩

instance [has_repr α] : has_repr (finset α) := ⟨λ s, repr s.1⟩

/-- Given a finset `s` of `ℕ` contained in `{0,..., n-1}`, the corresponding finset in `fin n`
is `s.attach_fin h` where `h` is a proof that all elements of `s` are less than `n`. -/
def attach_fin (s : finset ℕ) {n : ℕ} (h : ∀ m ∈ s, m < n) : finset (fin n) :=
⟨s.1.pmap (λ a ha, ⟨a, ha⟩) h, multiset.nodup_pmap (λ _ _ _ _, fin.mk.inj) s.2⟩

@[simp] lemma mem_attach_fin {n : ℕ} {s : finset ℕ} (h : ∀ m ∈ s, m < n) {a : fin n} :
  a ∈ s.attach_fin h ↔ a.1 ∈ s :=
⟨λ h, let ⟨b, hb₁, hb₂⟩ := multiset.mem_pmap.1 h in hb₂ ▸ hb₁,
λ h, multiset.mem_pmap.2 ⟨a.1, h, fin.eta _ _⟩⟩

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

/-! ### intervals -/
/- Ico (a closed open interval) -/
variables {n m l : ℕ}

/-- `Ico n m` is the set of natural numbers `n ≤ k < m`. -/
def Ico (n m : ℕ) : finset ℕ := ⟨_, Ico.nodup n m⟩

namespace Ico

@[simp] theorem val (n m : ℕ) : (Ico n m).1 = multiset.Ico n m := rfl

@[simp] theorem to_finset (n m : ℕ) : (multiset.Ico n m).to_finset = Ico n m :=
(multiset.to_finset_eq _).symm

theorem image_add (n m k : ℕ) : (Ico n m).image ((+) k) = Ico (n + k) (m + k) :=
by simp [image, multiset.Ico.map_add]

theorem image_sub (n m k : ℕ) (h : k ≤ n) : (Ico n m).image (λ x, x - k) = Ico (n - k) (m - k) :=
begin
  dsimp [image],
  rw [multiset.Ico.map_sub _ _ _ h, ←multiset.to_finset_eq],
  refl,
end

theorem zero_bot (n : ℕ) : Ico 0 n = range n :=
eq_of_veq $ multiset.Ico.zero_bot _

@[simp] theorem card (n m : ℕ) : (Ico n m).card = m - n :=
multiset.Ico.card _ _

@[simp] theorem mem {n m l : ℕ} : l ∈ Ico n m ↔ n ≤ l ∧ l < m :=
multiset.Ico.mem

theorem eq_bot_of_le {n m : ℕ} (h : m ≤ n) : Ico n m = ⊥ :=
eq_of_veq $ multiset.Ico.eq_zero_of_le h

@[simp] theorem self_eq_bot (n : ℕ) : Ico n n = ⊥ :=
eq_bot_of_le $ le_refl n

@[simp] theorem eq_bot_iff {n m : ℕ} : Ico n m = ⊥ ↔ m ≤ n :=
iff.trans val_eq_zero.symm multiset.Ico.eq_zero_iff

theorem le_iff {m₁ n₁ m₂ n₂ : ℕ} (hmn : m₁ < n₁) :
  Ico m₁ n₁ ≤ Ico m₂ n₂ ↔ (m₂ ≤ m₁ ∧ n₁ ≤ n₂) :=
begin
  simp only [le_def, mem],
  refine ⟨λ h, ⟨_, _⟩, _⟩,
  { exact (h ⟨le_refl _, hmn⟩).1 },
  { refine le_of_pred_lt (@h (pred n₁) ⟨le_pred_of_lt hmn, pred_lt _⟩).2,
    exact ne_of_gt (lt_of_le_of_lt (nat.zero_le m₁) hmn) },
  { rintros ⟨hm, hn⟩ k ⟨hmk, hkn⟩,
    exact ⟨le_trans hm hmk, lt_of_lt_of_le hkn hn⟩ }
end

protected theorem le {m₁ n₁ m₂ n₂ : ℕ} (hmm : m₂ ≤ m₁) (hnn : n₁ ≤ n₂) :
  Ico m₁ n₁ ≤ Ico m₂ n₂ :=
begin
  simp only [le_def, Ico.mem],
  assume x hx,
  exact ⟨le_trans hmm hx.1, lt_of_lt_of_le hx.2 hnn⟩
end

lemma sup_consecutive {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
  Ico n m ⊔ Ico m l = Ico n l :=
by rw [← to_finset, ← to_finset, ← multiset.to_finset_add,
  multiset.Ico.add_consecutive hnm hml, to_finset]

@[simp] lemma inter_consecutive (n m l : ℕ) : Ico n m ⊓ Ico m l = ⊥ :=
begin
  rw [← to_finset, ← to_finset, ← multiset.to_finset_inter, multiset.Ico.inter_consecutive],
  simp,
end

lemma disjoint_consecutive (n m l : ℕ) : disjoint (Ico n m) (Ico m l) :=
le_of_eq $ inter_consecutive n m l

@[simp] theorem succ_singleton (n : ℕ) : Ico n (n+1) = {n} :=
eq_of_veq $ multiset.Ico.succ_singleton

theorem succ_top {n m : ℕ} (h : n ≤ m) : Ico n (m + 1) = insert m (Ico n m) :=
by rw [← to_finset, multiset.Ico.succ_top h, multiset.to_finset_cons, to_finset]

theorem succ_top' {n m : ℕ} (h : n < m) : Ico n m = insert (m - 1) (Ico n (m - 1)) :=
begin
  have w : m = m - 1 + 1 := (nat.sub_add_cancel (nat.one_le_of_lt h)).symm,
  conv { to_lhs, rw w },
  rw succ_top,
  exact nat.le_pred_of_lt h
end

theorem insert_succ_bot {n m : ℕ} (h : n < m) : insert n (Ico (n + 1) m) = Ico n m :=
by rw [eq_comm, ← to_finset, multiset.Ico.eq_cons h, multiset.to_finset_cons, to_finset]

@[simp] theorem pred_singleton {m : ℕ} (h : 0 < m) : Ico (m - 1) m = {m - 1} :=
eq_of_veq $ multiset.Ico.pred_singleton h

@[simp] theorem not_mem_top {n m : ℕ} : m ∉ Ico n m :=
multiset.Ico.not_mem_top

lemma filter_lt_of_top_le {n m l : ℕ} (hml : m ≤ l) : (Ico n m).filter (λ x, x < l) = Ico n m :=
eq_of_veq $ multiset.Ico.filter_lt_of_top_le hml

lemma filter_lt_of_le_bot {n m l : ℕ} (hln : l ≤ n) : (Ico n m).filter (λ x, x < l) = ⊥ :=
eq_of_veq $ multiset.Ico.filter_lt_of_le_bot hln

lemma filter_lt_of_ge {n m l : ℕ} (hlm : l ≤ m) : (Ico n m).filter (λ x, x < l) = Ico n l :=
eq_of_veq $ multiset.Ico.filter_lt_of_ge hlm

@[simp] lemma filter_lt (n m l : ℕ) : (Ico n m).filter (λ x, x < l) = Ico n (min m l) :=
eq_of_veq $ multiset.Ico.filter_lt n m l

lemma filter_le_of_le_bot {n m l : ℕ} (hln : l ≤ n) : (Ico n m).filter (λ x, l ≤ x) = Ico n m :=
eq_of_veq $ multiset.Ico.filter_le_of_le_bot hln

lemma filter_le_of_top_le {n m l : ℕ} (hml : m ≤ l) : (Ico n m).filter (λ x, l ≤ x) = ⊥ :=
eq_of_veq $ multiset.Ico.filter_le_of_top_le hml

lemma filter_le_of_le {n m l : ℕ} (hnl : n ≤ l) : (Ico n m).filter (λ x, l ≤ x) = Ico l m :=
eq_of_veq $ multiset.Ico.filter_le_of_le hnl

@[simp] lemma filter_le (n m l : ℕ) : (Ico n m).filter (λ x, l ≤ x) = Ico (max n l) m :=
eq_of_veq $ multiset.Ico.filter_le n m l

@[simp] lemma diff_left (l n m : ℕ) : (Ico n m) \ (Ico n l) = Ico (max n l) m :=
by ext k; by_cases n ≤ k; simp [h, and_comm]

@[simp] lemma diff_right (l n m : ℕ) : (Ico n m) \ (Ico l m) = Ico n (min m l) :=
have ∀k, (k < m ∧ (l ≤ k → m ≤ k)) ↔ (k < m ∧ k < l) :=
  assume k, and_congr_right $ assume hk, by rw [← not_imp_not]; simp [hk],
by ext k; by_cases n ≤ k; simp [h, this]

lemma image_const_sub {k m n : ℕ} (hkn : k ≤ n) :
  (Ico k m).image (λ j, n - j) = Ico (n + 1 - m) (n + 1 - k) :=
begin
  rw [nat.sub_add_comm hkn],
  ext j,
  simp only [mem, mem_image, exists_prop, nat.lt_iff_add_one_le, add_le_add_iff_right],
  split,
  { rintros ⟨j, ⟨hjk, hjm⟩, rfl⟩,
    split,
    { simp only [← nat.add_sub_add_right n 1 j, nat.sub_le_sub_left, hjm] },
    { exact nat.sub_le_sub_left _ hjk } },
  { rintros ⟨hm, hk⟩,
    have hj : j ≤ n := le_trans hk (nat.sub_le_self _ _),
    refine ⟨n - j, ⟨_, _⟩, _⟩,
    { apply nat.le_sub_right_of_add_le,
      rwa nat.le_sub_left_iff_add_le hkn at hk },
    { rwa [← nat.sub_add_comm hj, nat.sub_le_iff] },
    { exact nat.sub_sub_self hj } }
end

end Ico

lemma range_eq_Ico (n : ℕ) : finset.range n = finset.Ico 0 n :=
by { ext i, simp }

lemma range_image_pred_top_sub (n : ℕ) :
  (finset.range n).image (λ j, n - 1 - j) = finset.range n :=
begin
  cases n,
  { simp },
  { simp [range_eq_Ico, Ico.image_const_sub] }
end

-- TODO We don't yet attempt to reproduce the entire interface for `Ico` for `Ico_ℤ`.

/-- `Ico_ℤ l u` is the set of integers `l ≤ k < u`. -/
def Ico_ℤ (l u : ℤ) : finset ℤ :=
(finset.range (u - l).to_nat).map
  { to_fun := λ n, n + l,
    inj' := λ n m h, by simpa using h }

@[simp] lemma Ico_ℤ.mem {n m l : ℤ} : l ∈ Ico_ℤ n m ↔ n ≤ l ∧ l < m :=
begin
  dsimp [Ico_ℤ],
  simp only [int.lt_to_nat, exists_prop, mem_range, add_comm, function.embedding.coe_fn_mk,
    mem_map],
  split,
  { rintro ⟨a, ⟨h, rfl⟩⟩,
    exact ⟨int.le.intro rfl, lt_sub_iff_add_lt'.mp h⟩ },
  { rintro ⟨h₁, h₂⟩,
    use (l - n).to_nat,
    split; simp [h₁, h₂], }
end

@[simp] lemma Ico_ℤ.card (l u : ℤ) : (Ico_ℤ l u).card = (u - l).to_nat := by simp [Ico_ℤ]

lemma supr_coe [has_Sup β] (f : α → β) (s : finset α) :
  (⨆ x ∈ (↑s : set α), f x) = ⨆ x ∈ s, f x :=
rfl

lemma infi_coe [has_Inf β] (f : α → β) (s : finset α) :
  (⨅ x ∈ (↑s : set α), f x) = ⨅ x ∈ s, f x :=
rfl

end finset

namespace multiset

lemma count_sup [decidable_eq β] (s : finset α) (f : α → multiset β) (b : β) :
  count b (s.supr f) = s.supr (λa, count b (f a)) :=
begin
  letI := classical.dec_eq α,
  refine s.induction _ _,
  { exact count_zero _ },
  { assume i s his ih,
    rw [finset.supr_insert, sup_eq_union, count_union, finset.supr_insert, ih],
    refl }
end

end multiset

namespace list
variable [decidable_eq α]

theorem to_finset_card_of_nodup {l : list α} (h : l.nodup) : l.to_finset.card = l.length :=
congr_arg card $ (@multiset.erase_dup_eq_self α _ l).2 h

end list

section lattice
variables {ι : Sort*} [complete_lattice α]

lemma supr_eq_supr_finset (s : ι → α) :
  (⨆i, s i) = (⨆t:finset (plift ι), ⨆i∈t, s (plift.down i)) :=
begin
  classical,
  exact le_antisymm
    (supr_le $ assume b, le_supr_of_le {plift.up b} $ le_supr_of_le (plift.up b) $ le_supr_of_le
      (by simp) $ le_refl _)
    (supr_le $ assume t, supr_le $ assume b, supr_le $ assume hb, le_supr _ _)
end

lemma infi_eq_infi_finset (s : ι → α) :
  (⨅i, s i) = (⨅t:finset (plift ι), ⨅i∈t, s (plift.down i)) :=
begin
  classical,
  exact le_antisymm
    (le_infi $ assume t, le_infi $ assume b, le_infi $ assume hb, infi_le _ _)
    (le_infi $ assume b, infi_le_of_le {plift.up b} $ infi_le_of_le (plift.up b) $ infi_le_of_le
      (by simp) $ le_refl _)
end

end lattice

namespace set
variables {ι : Sort*}

lemma Union_eq_Union_finset (s : ι → set α) :
  (⋃i, s i) = (⋃t:finset (plift ι), ⋃i∈t, s (plift.down i)) :=
supr_eq_supr_finset s

lemma Inter_eq_Inter_finset (s : ι → set α) :
  (⋂i, s i) = (⋂t:finset (plift ι), ⋂i∈t, s (plift.down i)) :=
infi_eq_infi_finset s

end set

namespace finset

namespace nat

/-- The antidiagonal of a natural number `n` is
    the finset of pairs `(i,j)` such that `i+j = n`. -/
def antidiagonal (n : ℕ) : finset (ℕ × ℕ) :=
(multiset.nat.antidiagonal n).to_finset

/-- A pair (i,j) is contained in the antidiagonal of `n` if and only if `i+j=n`. -/
@[simp] lemma mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} :
  x ∈ antidiagonal n ↔ x.1 + x.2 = n :=
by rw [antidiagonal, multiset.mem_to_finset, multiset.nat.mem_antidiagonal]

/-- The cardinality of the antidiagonal of `n` is `n+1`. -/
@[simp] lemma card_antidiagonal (n : ℕ) : (antidiagonal n).card = n+1 :=
by simpa using list.to_finset_card_of_nodup (list.nat.nodup_antidiagonal n)

/-- The antidiagonal of `0` is the list `[(0,0)]` -/
@[simp] lemma antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
by { rw [antidiagonal, multiset.nat.antidiagonal_zero], refl }

end nat

end finset

namespace finset

/-! ### bUnion -/

@[simp] theorem bUnion_singleton (a : α) (s : α → set β) : (⋃ x ∈ ({a} : finset α), s x) = s a :=
by { simp only [set.Union, ← supr_coe], rw coe_singleton, exact _root_.supr_singleton }

variables [decidable_eq α]

theorem bsupr_sup {α} [complete_lattice α] {β} [decidable_eq β] {f : β → α} {s t : finset β} :
  (⨆ x ∈ s ⊔ t, f x) = (⨆x∈s, f x) ⊔ (⨆x∈t, f x) :=
calc (⨆ x ∈ s ⊔ t, f x) = (⨆ x, (⨆h : x∈s, f x) ⊔ (⨆h : x∈t, f x)) :
  congr_arg _ $ funext $ λ x, by { convert supr_or, rw finset.mem_sup, rw finset.mem_sup, refl,
    refl }
                    ... = (⨆x∈s, f x) ⊔ (⨆x∈t, f x) : supr_sup_eq

lemma bUnion_sup (s t : finset α) (u : α → set β) :
  (⋃ x ∈ s ⊔ t, u x) = (⋃ x ∈ s, u x) ∪ (⋃ x ∈ t, u x) :=
bsupr_sup

@[simp] lemma bUnion_insert (a : α) (s : finset α) (t : α → set β) :
  (⋃ x ∈ insert a s, t x) = t a ∪ (⋃ x ∈ s, t x) :=
begin rw insert_eq, simp only [bUnion_sup, finset.bUnion_singleton] end

end finset
